import Proof.Wire_3_5.SelectionMachineSortPlan

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.SelectionMachine.Sort
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey NearCubicWires.RepairOrdinary.RadixSemantics
open NearCubicWires.WireExponent3_5.SelectionMachine.Math

/-! ## The sweep -/

/-- The sweep's step. -/
def scanStep (p : ℕ × ℕ) (x : ℕ) : ℕ × ℕ := if x % 2 = 1 then (p.1 + 1, p.2) else (p.1, p.2 + p.1)

theorem scanRef_eq (l : List ℕ) : scanRef l = l.foldl scanStep (0, 0) := rfl

/-- `joinLt` depends only on the multisets. -/
theorem joinLt_perm {A A' B B' : List ℕ} (hA : A.Perm A') (hB : B.Perm B') : joinLt A B = joinLt A' B' := by
  unfold joinLt
  rw [(hB.map _).sum_eq]
  congr 1
  apply List.map_congr_left
  intro b _
  exact hA.countP_eq _

/-- **The sweep of a sorted list**: from `(c, t)`, the total adds, at each even `x`, `c` plus the odd keys below `x`. -/
theorem scan_fold : ∀ (l : List ℕ) (c t : ℕ), l.Pairwise (· ≤ ·) →
    (l.foldl scanStep (c, t)).2 =
      t + ((l.filter fun x => x % 2 = 0).map fun x => c + (l.filter fun y => y % 2 = 1).countP (· < x)).sum
  | [], c, t, _ => by simp
  | x :: rest, c, t, hs => by
    have hx : ∀ y ∈ rest, x ≤ y := fun y hy => List.rel_of_pairwise_cons hs hy
    have hr : rest.Pairwise (· ≤ ·) := hs.of_cons
    rw [List.foldl_cons]
    by_cases hodd : x % 2 = 1
    · have e : scanStep (c, t) x = (c + 1, t) := by simp [scanStep, hodd]
      rw [e, scan_fold rest (c + 1) t hr]
      have hf0 : (x :: rest).filter (fun x => x % 2 = 0) = rest.filter (fun x => x % 2 = 0) := by
        rw [List.filter_cons_of_neg (by simp; omega)]
      have hf1 : (x :: rest).filter (fun y => y % 2 = 1) = x :: rest.filter (fun y => y % 2 = 1) := by
        rw [List.filter_cons_of_pos (by simpa using hodd)]
      rw [hf0, hf1]
      congr 1
      congr 1
      apply List.map_congr_left
      intro x' hx'
      rw [List.mem_filter] at hx'
      have hxx : x < x' := by
        have h1 := hx x' hx'.1
        have h2 : x' % 2 = 0 := by simpa using hx'.2
        rcases Nat.lt_or_eq_of_le h1 with h | h
        · exact h
        · subst h; omega
      rw [List.countP_cons, if_pos (by simpa using hxx)]
      omega
    · have heven : x % 2 = 0 := by omega
      have e : scanStep (c, t) x = (c, t + c) := by simp [scanStep, hodd]
      rw [e, scan_fold rest c (t + c) hr]
      have hf0 : (x :: rest).filter (fun x => x % 2 = 0) = x :: rest.filter (fun x => x % 2 = 0) := by
        rw [List.filter_cons_of_pos (by simpa using heven)]
      have hf1 : (x :: rest).filter (fun y => y % 2 = 1) = rest.filter (fun y => y % 2 = 1) := by
        rw [List.filter_cons_of_neg (by simpa using hodd)]
      rw [hf0, hf1, List.map_cons, List.sum_cons]
      have hzero : (rest.filter fun y => y % 2 = 1).countP (· < x) = 0 := by
        rw [List.countP_eq_zero]
        intro y hy
        have := hx y (List.mem_filter.mp hy).1
        simp only [decide_eq_true_eq]
        omega
      rw [hzero]
      omega

/-- The sweep of a sorted list is the `<`-join of its odd keys against its even keys. -/
theorem scanRef_sorted (l : List ℕ) (hs : l.Pairwise (· ≤ ·)) :
    (scanRef l).2 = joinLt (l.filter fun y => y % 2 = 1) (l.filter fun x => x % 2 = 0) := by
  rw [scanRef_eq, scan_fold l 0 0 hs]
  unfold joinLt
  simp

theorem filter_odd_tagged (A B : List ℕ) :
    (A.map tagA ++ B.map tagB).filter (fun y => y % 2 = 1) = A.map tagA := by
  rw [List.filter_append, List.filter_eq_self.mpr, List.filter_eq_nil_iff.mpr, List.append_nil]
  · intro y hy
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp hy
    simp [tagB]
  · intro y hy
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hy
    simp [tagA, Nat.add_mod]

theorem filter_even_tagged (A B : List ℕ) :
    (A.map tagA ++ B.map tagB).filter (fun x => x % 2 = 0) = B.map tagB := by
  rw [List.filter_append, List.filter_eq_nil_iff.mpr, List.filter_eq_self.mpr, List.nil_append]
  · intro y hy
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp hy
    simp [tagB]
  · intro y hy
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hy
    simp [tagA, Nat.add_mod]

theorem joinLt_tagged (A B : List ℕ) : joinLt (A.map tagA) (B.map tagB) = joinLt A B := by
  unfold joinLt
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro b _
  rw [Function.comp_apply, List.countP_map]
  apply List.countP_congr
  intro a _
  simp only [Function.comp_apply, tagA, tagB, decide_eq_true_eq]
  omega

/-- **`ScanJoin`**. -/
theorem scanJoin : ScanJoin := by
  intro A B l hp hs
  rw [scanRef_sorted l hs, joinLt_perm ((hp.filter _).trans (by rw [filter_odd_tagged]))
    ((hp.filter _).trans (by rw [filter_even_tagged])), joinLt_tagged]

/-! ## The radix rounds -/

theorem records_add (a : ℕ) : ∀ (b : ℕ) (rs : List StablePartition.Record),
    RadixIteration.records (a + b) rs = RadixIteration.records a (RadixIteration.records b rs)
  | 0, rs => rfl
  | b + 1, rs => by
    rw [← Nat.add_assoc]
    exact records_add a b (RadixRound.records rs)

theorem word_keyRec (W x : ℕ) (hW : 1 ≤ W) : word (keyRec W x) = binary W x := by
  unfold keyRec
  apply word_record
  intro h
  have := congrArg List.length h
  simp at this
  omega

theorem value_keyRec (W x : ℕ) (hW : 1 ≤ W) (hx : x < 2 ^ W) : value (word (keyRec W x)) = x := by
  rw [word_keyRec W x hW, binary_value W x hx]

/-- **`2W` radix rounds sort the width-`W` records of `l`.** -/
theorem radix_sorted (W : ℕ) (hW : 1 ≤ W) (l : List ℕ) (hl : ∀ x ∈ l, x < 2 ^ W) :
    RadixIteration.records (2 * W) (l.map (keyRec W)) = (sorted l).map (keyRec W) := by
  set rs := l.map (keyRec W) with hrs
  have hw : ∀ r ∈ rs, (word r).length = W := by
    intro r hr
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp hr
    rw [word_keyRec W x hW, binary_length]
  obtain ⟨p1, _⟩ := sorted_permutation W rs hw
  have hw1 : ∀ r ∈ RadixIteration.records W rs, (word r).length = W := fun r hr => hw r (p1.subset hr)
  obtain ⟨p2, s2⟩ := sorted_permutation W (RadixIteration.records W rs) hw1
  rw [Nat.two_mul, records_add]
  apply List.Perm.eq_of_pairwise _ s2
  · rw [List.pairwise_map]
    apply (sorted_pairwise l).imp_of_mem
    intro a b ha hb hab
    rw [value_keyRec W a hW (hl a ((sorted_perm l).subset ha)),
      value_keyRec W b hW (hl b ((sorted_perm l).subset hb))]
    exact hab
  · exact (p2.trans p1).trans ((sorted_perm l).map (keyRec W)).symm
  · intro a b ha hb h1 h2
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (((p2.trans p1)).subset ha)
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hb
    rw [value_keyRec W x hW (hl x hx), value_keyRec W y hW (hl y ((sorted_perm l).subset hy))] at h1 h2
    rw [show x = y by omega]

end NearCubicWires.WireExponent3_5.SelectionMachine.Sort
