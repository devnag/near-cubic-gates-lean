import SourceAdapters.Routing.PairDecomposition
import SourceAdapters.Routing.LanePair

/-!
# Recursive Beneš configurations and completeness

There is one switch at width one. A larger network has input and output
pair switches around two smaller networks running in parallel. The
semantics uses the low-bit lane split, and its depth is exactly `2*k-1`.
This implements the all-size completeness induction of the proof of `lem:routing`
without importing a routing contract or assuming a routing theorem.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Routing.BenesRecursive

/-- Switch settings of a positive-width recursive Beneš network. -/
inductive Config : ℕ → Type
  | base (setting : Bool) : Config 1
  | step {k : ℕ} (input output : BitVec (k + 1) → Bool)
      (lo hi : Config (k + 1)) : Config (k + 2)

/-- The two inner networks run in parallel, so their depths are maximized. -/
def Config.depth : {k : ℕ} → Config k → ℕ
  | _, .base _ => 1
  | _, .step _ _ lo hi => 1 + max lo.depth hi.depth + 1

/-- Exact permutation semantics. A base configuration is one switch. -/
def Config.perm : {k : ℕ} → Config k → Equiv.Perm (BitVec k)
  | _, .base setting =>
      (LanePair.equiv 0).symm.permCongr (pairSwitch (fun _ => setting))
  | _, @Config.step k input output lo hi =>
      (LanePair.equiv (k + 1)).symm.permCongr
        (((pairSwitch input).trans (pairMiddle lo.perm hi.perm)).trans (pairSwitch output))

theorem Config.positive {k : ℕ} (C : Config k) : 1 ≤ k := by
  cases C <;> omega

/-- The depth includes precisely one first and one last stage at each
recursive step; the base contributes only one stage. -/
theorem Config.depth_eq {k : ℕ} (C : Config k) : C.depth = 2 * k - 1 := by
  induction C with
  | base setting => rfl
  | @step k input output lo hi hlo hhi =>
      simp only [Config.depth, hlo, hhi, max_self]
      omega

@[simp] theorem Config.perm_base (setting : Bool) :
    (Config.base setting).perm =
      (LanePair.equiv 0).symm.permCongr (pairSwitch (fun _ => setting)) := rfl

@[simp] theorem Config.perm_step {k : ℕ} (input output : BitVec (k + 1) → Bool)
    (lo hi : Config (k + 1)) :
    (Config.step input output lo hi).perm =
      (LanePair.equiv (k + 1)).symm.permCongr
        (((pairSwitch input).trans (pairMiddle lo.perm hi.perm)).trans (pairSwitch output)) := rfl

/-- The exact recursive equation, ready to flatten into a stage schedule. -/
theorem Config.perm_step_apply {k : ℕ} (input output : BitVec (k + 1) → Bool)
    (lo hi : Config (k + 1)) (x : BitVec (k + 2)) :
    (Config.step input output lo hi).perm x =
      LanePair.join (pairSwitch output
        (pairMiddle lo.perm hi.perm (pairSwitch input (LanePair.split x)))) := rfl

theorem Config.perm_step_split {k : ℕ} (input output : BitVec (k + 1) → Bool)
    (lo hi : Config (k + 1)) (x : BitVec (k + 2)) :
    LanePair.split ((Config.step input output lo hi).perm x) =
      pairSwitch output (pairMiddle lo.perm hi.perm (pairSwitch input (LanePair.split x))) := by
  rw [Config.perm_step_apply, LanePair.split_join]

/-- At width one the two pair-switch factors combine into ONE XOR switch,
because the remaining lane type has one element. -/
theorem single_switch_complete (π : Equiv.Perm (BitVec 1)) :
    ∃ setting : Bool, (Config.base setting).perm = π := by
  classical
  let e := LanePair.equiv 0
  obtain ⟨input, output, π0, π1, hπ⟩ := pair_decomposition (e.permCongr π)
  let setting : Bool := Bool.xor (input 0) (output 0)
  have combined :
      ((pairSwitch input).trans (pairMiddle π0 π1)).trans (pairSwitch output) =
        pairSwitch (fun _ : BitVec 0 => setting) := by
    apply Equiv.ext
    rintro ⟨a, t⟩
    have ha : a = 0 := Subsingleton.elim _ _
    subst a
    change pairSwitch output (pairMiddle π0 π1 (pairSwitch input (0, t))) =
      pairSwitch (fun _ : BitVec 0 => setting) (0, t)
    rw [pairSwitch_apply, pairMiddle_apply, pairSwitch_apply, pairSwitch_apply]
    have hz : (if Bool.xor t (input 0) then π1 else π0) 0 = 0 := Subsingleton.elim _ _
    rw [hz]
    change (0, Bool.xor (Bool.xor t (input 0)) (output 0)) =
      (0, Bool.xor t (Bool.xor (input 0) (output 0)))
    rw [Bool.xor_assoc]
  refine ⟨setting, ?_⟩
  change e.symm.permCongr (pairSwitch (fun _ => setting)) = π
  rw [← combined, ← hπ]
  exact e.permCongr.symm_apply_apply π

/-- Every permutation of `k+1` lane bits is realized by the actual
recursive switch configuration. -/
theorem complete_succ (k : ℕ) (π : Equiv.Perm (BitVec (k + 1))) :
    ∃ C : Config (k + 1), C.perm = π := by
  induction k with
  | zero =>
      obtain ⟨setting, h⟩ := single_switch_complete π
      exact ⟨Config.base setting, h⟩
  | succ k ih =>
      letI : Finite (BitVec (k + 1)) := Finite.of_injective BitVec.toFin BitVec.toFin_injective
      let e := LanePair.equiv (k + 1)
      obtain ⟨input, output, π0, π1, hπ⟩ := pair_decomposition (e.permCongr π)
      obtain ⟨lo, hlo⟩ := ih π0
      obtain ⟨hi, hhi⟩ := ih π1
      refine ⟨Config.step input output lo hi, ?_⟩
      change e.symm.permCongr
        (((pairSwitch input).trans (pairMiddle lo.perm hi.perm)).trans (pairSwitch output)) = π
      rw [hlo, hhi, ← hπ]
      exact e.permCongr.symm_apply_apply π

/-- All positive sizes, with the exact `2*k-1` stage depth. -/
theorem complete (k : ℕ) (hk : 1 ≤ k) (π : Equiv.Perm (BitVec k)) :
    ∃ C : Config k, C.perm = π ∧ C.depth = 2 * k - 1 := by
  cases k with
  | zero => omega
  | succ k =>
      obtain ⟨C, hC⟩ := complete_succ k π
      exact ⟨C, hC, C.depth_eq⟩

end NearCubicGates.Adapters.Routing.BenesRecursive
