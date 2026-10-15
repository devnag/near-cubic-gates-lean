import Proof.SourceAssembly.MaskLoad

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace SLoad
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
noncomputable section

/-- Dual of `RecoveryRootRound.install_existing` for head positions. -/
theorem dockH_existing {t u : Nat} (slot : Fin t → Fin u) (ambient : Fin u → Nat)
    (heads : Fin t → Nat) (h : ∀ j, ambient (slot j) = heads j) :
    dockH slot ambient heads = ambient := by
  funext i
  cases hp : RecoveryFocus.pick slot i with
  | none => simp [dockH, hp]
  | some j =>
    have he := RecoveryFocus.slot_of_pick slot hp
    simp only [dockH, hp]
    exact (h j).symm.trans (congrArg ambient he)

/-- A local run that changes only coordinate `j` installs as a single update. -/
theorem install_update {t u : Nat} (slot : Fin t → Fin u) (hi : Function.Injective slot)
    (ambient : Fin u → List Bool) (tin tout : Fin t → List Bool) (j : Fin t)
    (hkeep : ∀ i, i ≠ j → tout i = tin i) (hit : ∀ i, ambient (slot i) = tin i) :
    install slot ambient tout = Function.update ambient (slot j) (tout j) := by
  classical
  funext i
  by_cases hij : i = slot j
  · subst hij
    rw [install_slot slot hi, Function.update_self]
  · rw [Function.update_of_ne hij]
    by_cases hp : ∃ k, slot k = i
    · obtain ⟨k, rfl⟩ := hp
      have hkj : k ≠ j := by
        intro h
        exact hij (congrArg slot h)
      rw [install_slot slot hi, hkeep k hkj, hit k]
    · exact install_other slot ambient tout i (by intro k hk; exact hp ⟨k, hk⟩)

/-- One focused call of a head-restoring local machine that rewrites a single
local tape: the ambient bank changes at exactly one slot and no ambient head
moves. -/
theorem step_update {t u s : Nat} {p : Machine t s} {n : Nat} {tin tout : Fin t → List Bool}
    (h : Step p n (fun _ => 0) tin (fun _ => 0) tout) (j : Fin t)
    (hkeep : ∀ i, i ≠ j → tout i = tin i)
    (slot : Fin t → Fin u) (hi : Function.Injective slot)
    (heads : Fin u → Nat) (tapes : Fin u → List Bool)
    (ih : ∀ i, heads (slot i) = 0) (it : ∀ i, tapes (slot i) = tin i) :
    Step (RecoveryFocus.machine slot p) n heads tapes heads
      (Function.update tapes (slot j) (tout j)) := by
  have hf := h.focus slot hi heads tapes
  rw [dockH_existing slot heads (fun _ => 0) ih, install_existing slot tapes tin it,
    install_update slot hi tapes tin tout j hkeep it] at hf
  exact hf

/-- An exact receipt is a `Step` receipt. -/
theorem step_of_exact {t s : Nat} {p : Machine t s} {n : Nat} {h h' : Fin t → Nat}
    {d d' : Fin t → List Bool} (e : PCPOuter.Exact p n h d h' d') : Step p n h d h' d' := by
  obtain ⟨r, hr, rh, rt, rs⟩ := e
  exact Step.of_run hr rh rt

/-- The three-slot maps used by both loaders are injective exactly when the
three chosen ambient tapes are distinct. -/
theorem triple_injective {u : Nat} (a b c : Fin u) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Function.Injective (![a, b, c] : Fin 3 → Fin u) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    first
      | rfl
      | (exact absurd hij hab) | (exact absurd hij.symm hab)
      | (exact absurd hij hac) | (exact absurd hij.symm hac)
      | (exact absurd hij hbc) | (exact absurd hij.symm hbc)

end
end SLoad
