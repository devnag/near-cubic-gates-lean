import SourceAdapters.Routing.BenesSchedule

/-! Actual stage settings and low-bit transport for one recursive Beneš step. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Routing.BenesRecursive

/-- Input stage, parallel smaller stages, then output stage. -/
def combine {k : ℕ} (input output : BitVec (k + 1) → Bool)
    (lo hi : Settings (k + 1)) : Settings (k + 2)
  | 0, x => input (LanePair.split x).1
  | j + 1, x =>
      if j < switchCount (k + 1) then
        if (LanePair.split x).2 then hi j (LanePair.split x).1 else lo j (LanePair.split x).1
      else output (LanePair.split x).1

theorem split_partner_inner {k : ℕ} (j : ℕ) (hj : j < switchCount (k + 1))
    (x : BitVec (k + 2)) :
    LanePair.split (partner (k + 2) (dimension (k + 2) (j + 1)) x) =
      (partner (k + 1) (dimension (k + 1) j) (LanePair.split x).1, (LanePair.split x).2) := by
  rw [dimension_inner k j hj]
  exact LanePair.split_flip_succ (dimension_lt (by omega)) x

theorem combine_first {k : ℕ} (input output : BitVec (k + 1) → Bool)
    (lo hi : Settings (k + 1)) (x : BitVec (k + 2)) :
    LanePair.split (stageMap (k + 2) (combine input output lo hi) 0 x) =
      pairSwitch input (LanePair.split x) :=
  split_pair_stage _ 0 input (dimension_first _) (fun _ => rfl) x

theorem combine_last {k : ℕ} (input output : BitVec (k + 1) → Bool)
    (lo hi : Settings (k + 1)) (x : BitVec (k + 2)) :
    LanePair.split
      (stageMap (k + 2) (combine input output lo hi) (switchCount (k + 1) + 1) x) =
      pairSwitch output (LanePair.split x) := by
  apply split_pair_stage _ _ output (dimension_last k) _ x
  intro y
  simp only [combine, lt_self_iff_false, ↓reduceIte]

theorem combine_inner {k : ℕ} (input output : BitVec (k + 1) → Bool)
    (lo hi : Settings (k + 1)) (j : ℕ) (hj : j < switchCount (k + 1))
    (x : BitVec (k + 2)) :
    LanePair.split (stageMap (k + 2) (combine input output lo hi) (j + 1) x) =
      ((if (LanePair.split x).2 then stageMap (k + 1) hi j else stageMap (k + 1) lo j)
        (LanePair.split x).1, (LanePair.split x).2) := by
  unfold stageMap
  rw [combine, if_pos hj]
  cases hb : (LanePair.split x).2 <;> simp only [Bool.false_eq_true, ↓reduceIte]
  all_goals split_ifs
  · simpa only [hb] using split_partner_inner j hj x
  · exact Prod.ext rfl hb
  · simpa only [hb] using split_partner_inner j hj x
  · exact Prod.ext rfl hb

/-- Every combined stage uses the same setting on its two partner lanes. -/
theorem combine_coherent {k : ℕ} (input output : BitVec (k + 1) → Bool)
    (lo hi : Settings (k + 1)) (hlo : Coherent (k + 1) lo) (hhi : Coherent (k + 1) hi) :
    Coherent (k + 2) (combine input output lo hi) := by
  intro j hj x
  cases j with
  | zero =>
      simp only [combine, dimension_first]
      change input (LanePair.split (x ^^^ BitVec.ofNat (k + 2) 1)).1 = input (LanePair.split x).1
      rw [LanePair.split_flip_zero]
  | succ j =>
      by_cases hmid : j < switchCount (k + 1)
      · simp only [combine, if_pos hmid, split_partner_inner j hmid x]
        cases (LanePair.split x).2 <;> simp only [Bool.false_eq_true, ↓reduceIte]
        · exact hlo j hmid (LanePair.split x).1
        · exact hhi j hmid (LanePair.split x).1
      · have hjlast : j = switchCount (k + 1) := by rw [switchCount_step] at hj; omega
        subst j
        simp only [combine, lt_self_iff_false, ↓reduceIte, dimension_last]
        change output (LanePair.split (x ^^^ BitVec.ofNat (k + 2) 1)).1 = output (LanePair.split x).1
        rw [LanePair.split_flip_zero]

end NearCubicGates.Adapters.Routing.BenesRecursive
