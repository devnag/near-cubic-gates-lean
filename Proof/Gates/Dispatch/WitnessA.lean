import Proof.Gates.Dispatch.WitDock

/-!
# Fragment (W), part A: the witness codec, value level (paper v2 lines 1642–1654)

Bit windows (`bitsValue` of `take`/`drop`), the field readers `readBlock`/`readSegments` field by field, the
coordinate bitmask (a Boolean list of length `n` read as a number), and the call word around the coefficient lists.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.Dispatch

open NearCubicGates NearCubicGates.Close.Counter NearCubicWires NearCubicWires.RepairRepresentation
  NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats

/-! ## Bit windows -/

theorem bitsValue_append (l m : List Bool) : bitsValue (l ++ m) = bitsValue l + 2 ^ l.length * bitsValue m := by
  induction l with
  | nil => simp [bitsValue]
  | cons b l ih => simp only [List.cons_append, bitsValue, ih, List.length_cons, pow_succ]; ring

theorem bitsValue_lt (l : List Bool) : bitsValue l < 2 ^ l.length := by
  induction l with
  | nil => simp [bitsValue]
  | cons b l ih => simp only [bitsValue, List.length_cons, pow_succ]; cases b <;> simp <;> omega

theorem bitsValue_split (l : List Bool) (m : ℕ) :
    bitsValue l = bitsValue (l.take m) + 2 ^ m * bitsValue (l.drop m) := by
  by_cases h : m ≤ l.length
  · conv_lhs => rw [← List.take_append_drop m l]
    rw [bitsValue_append, List.length_take, Nat.min_eq_left h]
  · rw [List.take_of_length_le (by omega), List.drop_of_length_le (by omega)]; simp [bitsValue]

theorem bitsValue_mod (l : List Bool) (m : ℕ) : bitsValue l % 2 ^ m = bitsValue (l.take m) := by
  rw [bitsValue_split l m, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt]
  exact lt_of_lt_of_le (bitsValue_lt _) (Nat.pow_le_pow_right (by norm_num) (by simp))

theorem bitsValue_div (l : List Bool) (m : ℕ) : bitsValue l / 2 ^ m = bitsValue (l.drop m) := by
  rw [bitsValue_split l m, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt, Nat.zero_add]
  exact lt_of_lt_of_le (bitsValue_lt _) (Nat.pow_le_pow_right (by norm_num) (by simp))

/-- The bit `c` of a list as `0/1`. -/
theorem bitsValue_drop_succ (l : List Bool) (c : ℕ) :
    bitsValue (l.drop c) = (l.getD c false).toNat + 2 * bitsValue (l.drop (c + 1)) := by
  induction l generalizing c with
  | nil => simp [bitsValue]
  | cons b l ih =>
    cases c with
    | zero => simp [bitsValue]
    | succ c => simpa using ih c

theorem bitsValue_take_succ (l : List Bool) (c : ℕ) :
    bitsValue (l.take (c + 1)) = bitsValue (l.take c) + (l.getD c false).toNat * 2 ^ c := by
  induction l generalizing c with
  | nil => simp [bitsValue]
  | cons b l ih =>
    cases c with
    | zero => simp [bitsValue]
    | succ c => simp only [List.take_succ_cons, bitsValue, ih c, List.getD_cons_succ, pow_succ]; ring

theorem bitsValue_div_mod (l : List Bool) (x : ℕ) : bitsValue l / 2 ^ x % 2 = (l.getD x false).toNat := by
  rw [bitsValue_div, bitsValue_drop_succ, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt]
  cases l.getD x false <;> simp

theorem getD_drop (l : List Bool) (p j : ℕ) : (l.drop p).getD j false = l.getD (p + j) false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem bitOf_eq (l : List Bool) (i : ℕ) : bitOf l i = (l.getD i false).toNat := rfl

/-! ## Field readers, field by field -/

theorem readBlock_cons (l : List Bool) (m : ℕ) (ws : List ℕ) :
    readBlock l (m :: ws) = (bitsValue (l.take m) :: (readBlock (l.drop m) ws).1, (readBlock (l.drop m) ws).2) := rfl

theorem readBlock_snd (l : List Bool) (ws : List ℕ) : (readBlock l ws).2 = l.drop ws.sum := by
  induction ws generalizing l with
  | nil => simp [readBlock]
  | cons m ws ih => simp [readBlock_cons, ih, List.drop_drop, Nat.add_comm]

theorem readBlock_fst_length (l : List Bool) (ws : List ℕ) : (readBlock l ws).1.length = ws.length := by
  induction ws generalizing l with
  | nil => simp [readBlock]
  | cons m ws ih => simp [readBlock_cons, ih]

/-- The coordinate block, one coordinate at a time. -/
theorem readBlock_rep_succ (l : List Bool) (m : ℕ) :
    ∀ i, (readBlock l (List.replicate (i + 1) m)).1 =
      (readBlock l (List.replicate i m)).1 ++ [bitsValue ((l.drop (i * m)).take m)] := by
  intro i
  induction i generalizing l with
  | zero => simp [readBlock]
  | succ i ih =>
    have e1 : List.replicate (i + 1 + 1) m = m :: List.replicate (i + 1) m := rfl
    have e2 : List.replicate (i + 1) m = m :: List.replicate i m := rfl
    rw [e1, readBlock_cons, ih (l.drop m), e2, readBlock_cons]
    simp only [List.drop_drop, List.cons_append]
    congr 4; ring

theorem readBlock_rep_take (l : List Bool) (m k i : ℕ) (hi : i ≤ k) :
    ((readBlock l (List.replicate k m)).1).take i = (readBlock l (List.replicate i m)).1 := by
  induction k generalizing i with
  | zero => have : i = 0 := by omega
            subst this; simp [readBlock]
  | succ k ih =>
    rcases Nat.lt_or_ge i (k + 1) with h | h
    · rw [readBlock_rep_succ, List.take_append_of_le_length (by rw [readBlock_fst_length]; simp; omega), ih i (by omega)]
    · have : i = k + 1 := by omega
      subst this; rw [List.take_of_length_le (by rw [readBlock_fst_length]; simp)]

/-- Reading segments only looks at the first `total` bits. -/
theorem readBlock_take (l : List Bool) (ws : List ℕ) (T : ℕ) :
    (readBlock (l.take (ws.sum + T)) ws).1 = (readBlock l ws).1 ∧
      (readBlock (l.take (ws.sum + T)) ws).2 = ((readBlock l ws).2).take T := by
  rw [readBlock_snd, readBlock_snd]
  refine ⟨?_, by rw [List.drop_take]; congr 1; omega⟩
  induction ws generalizing l with
  | nil => simp [readBlock]
  | cons m ws ih =>
    rw [readBlock_cons, readBlock_cons]
    simp only [Prod.mk.injEq]
    have h1 : (l.take ((m :: ws).sum + T)).take m = l.take m := by
      rw [List.take_take]; congr 1; simp; omega
    have h2 : (l.take ((m :: ws).sum + T)).drop m = (l.drop m).take (ws.sum + T) := by
      rw [List.drop_take]; congr 1; simp; omega
    rw [h1, h2, ih]

theorem readSegments_take (l : List Bool) (segs : List (List ℕ)) :
    (readSegments (l.take (segs.map List.sum).sum) segs).1 = (readSegments l segs).1 := by
  suffices h : ∀ T, (readSegments (l.take ((segs.map List.sum).sum + T)) segs).1 = (readSegments l segs).1 by
    simpa using h 0
  induction segs generalizing l with
  | nil => intro T; simp [readSegments]
  | cons seg segs ih =>
    intro T
    simp only [readSegments, List.map_cons, List.sum_cons]
    have hb := readBlock_take l seg ((segs.map List.sum).sum + T)
    rw [← Nat.add_assoc] at hb
    rw [hb.1, hb.2, ih]

theorem readSegments_cons (l : List Bool) (seg : List ℕ) (segs : List (List ℕ)) :
    (readSegments l (seg :: segs)).1 = (readBlock l seg).1 :: (readSegments (readBlock l seg).2 segs).1 := rfl

/-! ## The coordinate bitmask -/

theorem bitsValue_set_true (l : List Bool) (x : ℕ) (hx : x < l.length) (h0 : l.getD x false = false) :
    bitsValue (l.set x true) = bitsValue l + 2 ^ x := by
  induction l generalizing x with
  | nil => simp at hx
  | cons b l ih =>
    cases x with
    | zero => simp at h0; simp [bitsValue, h0]; omega
    | succ x =>
      simp only [List.set_cons_succ, bitsValue, List.length_cons] at hx ⊢
      simp only [List.getD_cons_succ] at h0
      rw [ih x (by omega) h0, pow_succ]; ring

/-- The mask of a coordinate list: bit `y` set iff `y` occurs. -/
def maskOf (n : ℕ) (xs : List ℕ) : List Bool := (List.range n).map fun y => decide (y ∈ xs)

theorem maskOf_length (n : ℕ) (xs : List ℕ) : (maskOf n xs).length = n := by simp [maskOf]

theorem maskOf_getD (n : ℕ) (xs : List ℕ) (y : ℕ) : (maskOf n xs).getD y false = decide (y < n ∧ y ∈ xs) := by
  unfold maskOf
  rw [List.getD_eq_getElem?_getD]
  by_cases hy : y < n
  · simp [hy]
  · rw [List.getElem?_eq_none (by simp; omega)]; simp [hy]

theorem maskOf_snoc (n : ℕ) (xs : List ℕ) (x : ℕ) :
    maskOf n (xs ++ [x]) = (maskOf n xs).set x true := by
  apply List.ext_getElem (by simp [maskOf])
  intro i h1 h2
  simp only [maskOf, List.getElem_map, List.getElem_range, List.getElem_set]
  by_cases hi : x = i
  · subst hi; simp
  · simp [hi, Ne.symm hi]

/-- The sorted coordinate list is the mask's set bits, in order. -/
theorem coordsOf_eq_filter (n : ℕ) (I : Finset (Fin n)) :
    coordsOf I = (List.range n).filter fun y => decide (∃ h : y < n, (⟨y, h⟩ : Fin n) ∈ I) := by
  unfold coordsOf
  refine List.Pairwise.eq_of_mem_iff (r := (· < ·)) ?_ ?_ ?_
  · exact List.Pairwise.map _ (fun a b h => h) (Finset.sortedLT_sort I).pairwise
  · exact List.pairwise_lt_range.filter _
  · intro y
    simp only [List.mem_map, Finset.mem_sort, List.mem_filter, List.mem_range, decide_eq_true_eq]
    constructor
    · rintro ⟨i, hi, rfl⟩; exact ⟨i.isLt, i.isLt, hi⟩
    · rintro ⟨hy, h, hm⟩; exact ⟨⟨y, h⟩, hm, rfl⟩

end NearCubicGates.Close.Dispatch
