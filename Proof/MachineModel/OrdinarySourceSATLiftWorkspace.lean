import Proof.MachineModel.OrdinarySourceSATLiftGraph

/-! The retained finite workspace invariant used by every query replacement. -/
namespace NearCubicWires.RepairSource.OrdinarySourceSATLift
open LocalBitMultitape RepairOrdinary RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure Workspace {p : OrdinaryOracleProgram} {t : ℕ} (w : Wiring p t) (b : ℕ)
    (heads : Fin t → ℕ) (tapes : Fin t → List Bool) : Prop where
  heads_zero : ∀ j,j≠0 → heads (w.kernel j)=0
  driver : tapes (w.kernel 1)=List.replicate (capacity b) true
  log : ∃ n ≤ capacity b+1,tapes (w.kernel 2)=List.replicate n false
  bounded : Kernel.Bounded (capacity b) (tapes ∘ w.kernel)

theorem Wiring.core_pick_none {p : OrdinaryOracleProgram} {t : ℕ} (w : Wiring p t)
    (j : Fin 156) (hj : j≠0) : RecoveryFocus.pick w.core (w.kernel j)=none := by
  classical
  unfold RecoveryFocus.pick
  exact dif_neg (by rintro ⟨i,he⟩; exact w.disjoint i j hj he)

theorem Wiring.focus_head_other {p : OrdinaryOracleProgram} {t : ℕ} (w : Wiring p t)
    (heads : Fin t → ℕ) (tapes : Fin t → List Bool) (c : p.Config) (j : Fin 156) (hj : j≠0) :
    (RecoveryFocus.config w.core heads tapes c).heads (w.kernel j)=heads (w.kernel j) := by
  simp [RecoveryFocus.config,w.core_pick_none j hj]
theorem Wiring.focus_tape_other {p : OrdinaryOracleProgram} {t : ℕ} (w : Wiring p t)
    (heads : Fin t → ℕ) (tapes : Fin t → List Bool) (c : p.Config) (j : Fin 156) (hj : j≠0) :
    (RecoveryFocus.config w.core heads tapes c).tapes (w.kernel j)=tapes (w.kernel j) := by
  simp [RecoveryFocus.config,w.core_pick_none j hj]

theorem Workspace.focus {p : OrdinaryOracleProgram} {t : ℕ} {w : Wiring p t} {b : ℕ}
    {heads : Fin t → ℕ} {tapes : Fin t → List Bool} (h : Workspace w b heads tapes) (c : p.Config) :
    Workspace w b (RecoveryFocus.config w.core heads tapes c).heads
      (RecoveryFocus.config w.core heads tapes c).tapes := by
  refine ⟨?_,?_,?_,?_⟩
  · intro j hj
    rw [w.focus_head_other heads tapes c j hj]
    exact h.heads_zero j hj
  · rw [w.focus_tape_other heads tapes c 1 (by decide)]
    exact h.driver
  · obtain ⟨n,hn,hl⟩ := h.log
    exact ⟨n,hn,(w.focus_tape_other heads tapes c 2 (by decide)).trans hl⟩
  · intro j hj
    have hz : j≠0 := by intro he; subst j; simp at hj
    simpa only [Function.comp_apply,w.focus_tape_other heads tapes c j hz] using h.bounded j hj

theorem Workspace.install {p : OrdinaryOracleProgram} {t : ℕ} {w : Wiring p t} {b : ℕ}
    {heads : Fin t → ℕ} {tapes : Fin t → List Bool} (h : Workspace w b heads tapes)
    (out : Fin 156 → List Bool) (hd : out 1=List.replicate (capacity b) true)
    (hl : out 2=List.replicate (capacity b+1) false) (hb : Kernel.Bounded (capacity b) out) :
    Workspace w b heads (install w.kernel tapes out) := by
  refine ⟨h.heads_zero,?_,?_,?_⟩
  · rw [install_slot _ w.kernel_injective]
    exact hd
  · exact ⟨capacity b+1,le_rfl,(install_slot _ w.kernel_injective tapes out 2).trans hl⟩
  · intro j hj
    simpa only [Function.comp_apply,install_slot _ w.kernel_injective] using hb j hj

theorem Wiring.focus_existing {p : OrdinaryOracleProgram} {t : ℕ} (w : Wiring p t)
    (heads : Fin t → ℕ) (tapes : Fin t → List Bool) (c : p.Config)
    (hh : ∀ i,heads (w.core i)=c.heads i) (ht : ∀ i,tapes (w.core i)=c.tapes i) :
    RecoveryFocus.config w.core heads tapes c=⟨c.control,heads,tapes⟩ := by
  apply configuration_ext
  · rfl
  · funext i
    cases hp : RecoveryFocus.pick w.core i with
    | none => simp [RecoveryFocus.config,hp]
    | some j =>
      have he := RecoveryFocus.slot_of_pick w.core hp
      simpa only [RecoveryFocus.config,hp] using (hh j).symm.trans (congrArg heads he)
  · exact install_existing w.core tapes c.tapes ht

def Retained {p : OrdinaryOracleProgram} {t : ℕ} (w : Wiring p t)
    (beforeHeads afterHeads : Fin t → ℕ) (beforeTapes afterTapes : Fin t → List Bool) : Prop :=
  ∀ i,(∀ j,w.core j≠i) → (∀ j,w.kernel j≠i) →
    afterHeads i=beforeHeads i ∧ afterTapes i=beforeTapes i

theorem Retained.refl {p : OrdinaryOracleProgram} {t : ℕ} (w : Wiring p t)
    (heads : Fin t → ℕ) (tapes : Fin t → List Bool) : Retained w heads heads tapes tapes :=
  fun _ _ _ => ⟨rfl,rfl⟩

theorem Retained.trans {p : OrdinaryOracleProgram} {t : ℕ} {w : Wiring p t}
    {h0 h1 h2 : Fin t → ℕ} {t0 t1 t2 : Fin t → List Bool}
    (ha : Retained w h0 h1 t0 t1) (hb : Retained w h1 h2 t1 t2) :
    Retained w h0 h2 t0 t2 := by
  intro i hi hk
  exact ⟨(hb i hi hk).1.trans (ha i hi hk).1,(hb i hi hk).2.trans (ha i hi hk).2⟩

theorem retained_query {p : OrdinaryOracleProgram} {t : ℕ} (w : Wiring p t)
    (heads : Fin t → ℕ) (tapes : Fin t → List Bool) (c : p.Config) (out : Fin 156 → List Bool) :
    Retained w heads (RecoveryFocus.config w.core heads tapes c).heads tapes
      (install w.kernel (RecoveryFocus.config w.core heads tapes c).tapes out) := by
  classical
  intro i hc hk
  have hp : RecoveryFocus.pick w.core i=none := by
    unfold RecoveryFocus.pick
    exact dif_neg (by rintro ⟨j,he⟩; exact hc j he)
  constructor
  · simp [RecoveryFocus.config,hp]
  · rw [install_other w.kernel _ _ i hk]
    simp [RecoveryFocus.config,hp]

end NearCubicWires.RepairSource.OrdinarySourceSATLift
