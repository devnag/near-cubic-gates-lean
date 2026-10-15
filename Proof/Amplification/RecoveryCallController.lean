import Proof.Amplification.RecoveryTimedExecution

/-! A finite call graph for the fixed arithmetic routine. Every return and
branch is one actual local transition. The node family is a finite static
rule table; this construction does not interpret an encoded program. -/
namespace NearCubicWires.RepairOrdinary.RecoveryCalls
open LocalBitMultitape RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev Control {k : Nat} (sizes : Fin k → Nat) := Option ((j : Fin k) × Fin (sizes j))
noncomputable def controlCode {k : Nat} (sizes : Fin k → Nat) :
    Control sizes ≃ Fin (Fintype.card (Control sizes)) := Fintype.equivFin _

noncomputable def code {k : Nat} (sizes : Fin k → Nat) (j : Fin k) (q : Fin (sizes j)) :=
  controlCode sizes (some ⟨j, q⟩)

noncomputable def mapAction {t k : Nat} (sizes : Fin k → Nat) (j : Fin k)
    (a : Action t (sizes j)) : Action t (Fintype.card (Control sizes)) :=
  ⟨code sizes j a.nextControl, a.write, a.move⟩

noncomputable def machine {t k : Nat} (sizes : Fin k → Nat)
    (programs : (j : Fin k) → Machine t (sizes j)) (entry : Fin k)
    (next : (j : Fin k) → Fin (sizes j) → (Fin t → Bool) → Option (Fin k)) :
    Machine t (Fintype.card (Control sizes)) where
  descriptionBits := 0
  start := code sizes entry (programs entry).start
  halted := fun q => ((controlCode sizes).symm q).isNone
  rule := fun q bits => match (controlCode sizes).symm q with
    | none => none
    | some ⟨j, state⟩ =>
      if (programs j).halted state then
        some ⟨controlCode sizes ((next j state bits).map (fun l => ⟨l, (programs l).start⟩)),
          fun _ => none, fun _ => .stay⟩
      else ((programs j).rule state bits).map (mapAction sizes j)

theorem action_config {t k : Nat} (sizes : Fin k → Nat) (j : Fin k)
    (c : Configuration t (sizes j)) (a : Action t (sizes j)) :
    applyAction (controlConfig (code sizes j) c) (mapAction sizes j a) =
      controlConfig (code sizes j) (applyAction c a) := by rfl

theorem body_step {t k : Nat} (sizes : Fin k → Nat)
    (programs : (j : Fin k) → Machine t (sizes j)) (entry : Fin k)
    (next : (j : Fin k) → Fin (sizes j) → (Fin t → Bool) → Option (Fin k))
    (j : Fin k) (c d : Configuration t (sizes j))
    (hn : (programs j).halted c.control = false) (hs : step (programs j) c = some d) :
    step (machine sizes programs entry next) (controlConfig (code sizes j) c) =
      some (controlConfig (code sizes j) d) := by
  unfold step at hs ⊢
  simp only [machine, controlConfig, code, Equiv.symm_apply_apply, hn, Bool.false_eq_true,
    ↓reduceIte, Option.map_map]
  change ((programs j).rule c.control c.scanned).map
    (fun a => controlConfig (code sizes j) (applyAction c a)) = _
  simpa only [Option.map_map, Function.comp_def, Option.map_some, controlConfig, code] using
    congrArg (Option.map (controlConfig (code sizes j))) hs

theorem body_timed {t k n : Nat} (sizes : Fin k → Nat)
    (programs : (j : Fin k) → Machine t (sizes j)) (entry : Fin k)
    (next : (j : Fin k) → Fin (sizes j) → (Fin t → Bool) → Option (Fin k))
    (j : Fin k) {c d : Configuration t (sizes j)} (h : Timed (programs j) n c d) :
    Timed (machine sizes programs entry next) n
      (controlConfig (code sizes j) c) (controlConfig (code sizes j) d) := by
  obtain ⟨space, hp⟩ := h
  refine ⟨space, hp.mapControl (code sizes j) ?_ ?_⟩
  · intro x _
    simp [machine, code]
  · exact body_step sizes programs entry next j

def restarted {t s : Nat} (p : Machine t s) (heads : Fin t → Nat)
    (tapes : Fin t → List Bool) : Configuration t s := ⟨p.start, heads, tapes⟩

noncomputable def stopped {t k : Nat} (sizes : Fin k → Nat)
    (heads : Fin t → Nat) (tapes : Fin t → List Bool) :
    Configuration t (Fintype.card (Control sizes)) := ⟨controlCode sizes none, heads, tapes⟩

theorem return_step {t k : Nat} (sizes : Fin k → Nat)
    (programs : (j : Fin k) → Machine t (sizes j)) (entry : Fin k)
    (next : (j : Fin k) → Fin (sizes j) → (Fin t → Bool) → Option (Fin k))
    (j l : Fin k) (c : Configuration t (sizes j))
    (hh : (programs j).halted c.control = true) (hn : next j c.control c.scanned = some l) :
    step (machine sizes programs entry next) (controlConfig (code sizes j) c) =
      some (controlConfig (code sizes l) (restarted (programs l) c.heads c.tapes)) := by
  change ((machine sizes programs entry next).rule (code sizes j c.control) c.scanned).map _ = _
  simp only [machine, code, Equiv.symm_apply_apply, hh, ↓reduceIte, hn, Option.map_some]
  rfl

theorem stop_step {t k : Nat} (sizes : Fin k → Nat)
    (programs : (j : Fin k) → Machine t (sizes j)) (entry : Fin k)
    (next : (j : Fin k) → Fin (sizes j) → (Fin t → Bool) → Option (Fin k))
    (j : Fin k) (c : Configuration t (sizes j))
    (hh : (programs j).halted c.control = true) (hn : next j c.control c.scanned = none) :
    step (machine sizes programs entry next) (controlConfig (code sizes j) c) =
      some (stopped sizes c.heads c.tapes) := by
  change ((machine sizes programs entry next).rule (code sizes j c.control) c.scanned).map _ = _
  simp only [machine, code, Equiv.symm_apply_apply, hh, ↓reduceIte, hn, Option.map_none, Option.map_some]
  rfl

end NearCubicWires.RepairOrdinary.RecoveryCalls
