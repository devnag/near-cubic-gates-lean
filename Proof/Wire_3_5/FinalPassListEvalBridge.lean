import Proof.Wire_3_5.FinalPassList
import Proof.Wire_3_5.FinalPassListEvalRef

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.ListEval
open NearCubicWires.WireExponent3_5.Lists NearCubicWires.WireExponent3_5.Filters Finset

/-- The table rows of a list: `row_j = [i ∈ 𝓛_j]_{i<L}`. -/
def rowsOf (D : ListData) (L : ℕ) (j : ℕ) : List Bool := (List.range L).map (D.inLevel j)

/-! ## Counts -/

theorem hits_eq_sum : ∀ (l1 l2 : List Bool),
    hits l1 l2 = ∑ i ∈ range (min l1.length l2.length), if l1.getD i false && l2.getD i false then 1 else 0
  | [], _ => by simp [hits]
  | _ :: _, [] => by simp [hits]
  | a :: as, b :: bs => by
    rw [hits, hits_eq_sum as bs]
    simp only [List.length_cons, Nat.add_min_add_right, sum_range_succ', List.getD_cons_succ, List.getD_cons_zero]
    ring

theorem and_indicator (a b : Bool) : (if (a && b) = true then 1 else 0) = if b = true ∧ a = true then (1 : ℕ) else 0 := by
  cases a <;> cases b <;> decide

theorem hits_rows (D : ListData) (L j : ℕ) (Z : List Bool) (hZ : Z.length = L) :
    hits (rowsOf D L j) Z = D.levelCount j Z := by
  rw [hits_eq_sum]
  unfold ListData.levelCount rowsOf
  rw [card_filter]
  simp only [List.length_map, List.length_range, hZ, min_self]
  refine sum_congr rfl fun i hi => ?_
  have hi' : i < L := mem_range.mp hi
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi']
  simp only [Option.map_some, Option.getD_some]
  exact and_indicator (D.inLevel j i) (Z.getD i false)

/-! ## The decoder's value -/

theorem bitF2_val (b : Bool) : (bitF2 b).val = if b then 1 else 0 := by cases b <;> rfl

theorem emod_two_mul (x : ℤ) (m : ℕ) (hm : 0 < m) :
    x % (2 * m : ℕ) = x % 2 + 2 * ((x / 2) % (m : ℕ)) := by
  have h2 := Int.emod_add_ediv_mul x 2
  have hq := Int.emod_add_ediv_mul (x / 2) (m : ℤ)
  have hr0 : 0 ≤ x % 2 := Int.emod_nonneg _ (by norm_num)
  have hr1 : x % 2 < 2 := Int.emod_lt_of_pos _ (by norm_num)
  have hs0 : 0 ≤ (x / 2) % (m : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hm.ne')
  have hs1 : (x / 2) % (m : ℤ) < m := Int.emod_lt_of_pos _ (by exact_mod_cast hm)
  have hx : x = (x % 2 + 2 * ((x / 2) % (m : ℕ))) + ((2 * m : ℕ) : ℤ) * ((x / 2) / m) := by
    push_cast; linear_combination -h2 - 2 * hq
  conv_lhs => rw [hx, Int.add_mul_emod_self_left]
  apply Int.emod_eq_of_lt
  · linarith
  · push_cast; linarith

theorem testBit_zero_int (x : ℤ) : x.testBit 0 = decide (x % 2 = 1) := by
  conv_lhs => rw [← Int.bit_decomp x]
  rw [Int.testBit_bit_zero]
  have h := Int.bodd_add_div2 x
  rw [Int.div2_val] at h
  cases hb : Int.bodd x <;> rw [hb] at h <;> simp only [cond_false, cond_true] at h
  · simp only [false_eq_decide_iff]; omega
  · simp only [true_eq_decide_iff]; omega

theorem testBit_succ_int (x : ℤ) (n : ℕ) : x.testBit (n + 1) = (x / 2).testBit n := by
  conv_lhs => rw [← Int.bit_decomp x]
  rw [Int.testBit_bit_succ, Int.div2_val]

/-- The value of `ℓ` low bits of an integer is its residue mod `2^ℓ` (two's complement). -/
theorem decodeVal_testBit : ∀ (ℓ : ℕ) (x : ℤ), decodeVal ℓ (fun h => bitF2 (x.testBit h)) = (x % (2 ^ ℓ : ℕ)).toNat
  | 0, x => by simp [decodeVal]
  | ℓ + 1, x => by
    simp only [decodeVal, Fin.val_zero, Fin.val_succ]
    have ih := decodeVal_testBit ℓ (x / 2)
    have e : (fun h : Fin ℓ => bitF2 (x.testBit (h.val + 1))) = fun h : Fin ℓ => bitF2 ((x / 2).testBit h) := by
      funext h; rw [testBit_succ_int]
    rw [e, ih, bitF2_val, testBit_zero_int, show 2 ^ (ℓ + 1) = 2 * 2 ^ ℓ by ring,
      emod_two_mul x (2 ^ ℓ) (by positivity)]
    have hr0 : 0 ≤ x % 2 := Int.emod_nonneg _ (by norm_num)
    have hr1 : x % 2 < 2 := Int.emod_lt_of_pos _ (by norm_num)
    have hs0 : 0 ≤ (x / 2) % ((2 ^ ℓ : ℕ) : ℤ) := Int.emod_nonneg _ (by positivity)
    by_cases h1 : x % 2 = 1
    · rw [if_pos (by simpa using h1)]; omega
    · rw [if_neg (by simpa using h1)]; omega

theorem decoded_eq (D : ListData) (j : ℕ) (Z : List Bool) :
    ListFast.decoded D j Z =
      (cyc (pow (D.W j)) ((D.levelCount j Z : ℤ) + D.W j - 2 * D.levelCount (j + 1) Z) : ℤ) - D.W j := by
  unfold ListFast.decoded ListData.decoderBits cyc pow
  rw [decodeVal_testBit]
  unfold ListData.levelDelta ListData.ell
  congr 3
  push_cast
  ring_nf

/-! ## One level -/

theorem levelStep_eq (M W cp c : ℕ) (d : ℤ) (hd : d = (cyc (pow W) ((c : ℤ) + W - 2 * cp) : ℤ) - W)
    (o : Option ℕ) : levelStep M W cp c o = followStep M d o := by
  cases o with
  | none => rfl
  | some t =>
    simp only [levelStep, followStep]
    by_cases h : t ≤ M ∧ W ≤ 2 * t + cyc (pow W) ((c : ℤ) + W - 2 * cp)
    · rw [if_pos h, if_pos ⟨h.1, by rw [hd]; omega⟩]
      congr 1
      rw [hd]
      omega
    · rw [if_neg h, if_neg (fun h' => h ⟨h'.1, by rw [hd] at h'; omega⟩)]

theorem levelStep_top (M c : ℕ) : levelStep M 0 0 c (some 0) = some 0 := by
  have hp : pow 0 = 1 := by simp [pow]
  simp [levelStep, hp, cyc]

/-! ## The fold -/

theorem fold_range' (D : ListData) (L : ℕ) (Z : List Bool) (hZ : Z.length = L) :
    ∀ n k, k + n = D.J →
      (List.range' k n).foldr (fun j acc => (levelStep D.M (topW D.J D.W j) acc.2 (hits (rowsOf D L j) Z) acc.1,
          hits (rowsOf D L j) Z)) (some 0, hits (rowsOf D L D.J) Z) =
        (followAll D.M ((List.range' k n).map fun j => ListFast.decoded D j Z), D.levelCount k Z)
  | 0, k, hk => by
    simp only [List.range'_zero, List.foldr_nil, List.map_nil, followAll, Prod.mk.injEq, true_and]
    rw [hits_rows D L _ Z hZ, ← hk, Nat.add_zero]
  | n + 1, k, hk => by
    rw [List.range'_succ, List.foldr_cons, fold_range' D L Z hZ n (k + 1) (by omega), List.map_cons,
      followAll]
    simp only [Prod.mk.injEq]
    have htop : topW D.J D.W k = D.W k := by simp [topW]; omega
    refine ⟨?_, hits_rows D L k Z hZ⟩
    rw [htop, hits_rows D L k Z hZ]
    exact levelStep_eq _ _ _ _ _ (decoded_eq D k Z) _

theorem reportRef_eq_fast (D : ListData) (L : ℕ) (Z : List Bool) (hZ : Z.length = L) :
    reportRef D.M D.J D.W (rowsOf D L) Z = ListFast.listReportFast D Z := by
  have hfold : (levelFold D.M D.J D.W (rowsOf D L) Z (some 0, 0) (levels D.J)).1 = ListFast.followed D Z := by
    unfold levelFold levels ListFast.followed
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append, List.foldl_cons,
      List.foldl_reverse]
    have htop : topW D.J D.W D.J = 0 := by simp [topW]
    simp only [htop, levelStep_top]
    have h := fold_range' D L Z hZ D.J 0 (by omega)
    rw [List.range_eq_range'] at *
    exact congrArg Prod.fst h
  unfold reportRef ListFast.listReportFast
  rw [hfold]
  cases ListFast.followed D Z <;> rfl

/-! ## Executable twin -/

/-- The tiny table of `ListEvalRef` as list data. -/
def tinyData (M : ℕ) : ListData := ⟨M, 2, tinyW, fun j i => (tinyRow j).getD i false⟩

theorem tiny_rows (j : ℕ) : rowsOf (tinyData 5) 3 j = tinyRow j := by
  rcases j with _ | _ | j <;> rfl

theorem tiny_twin :
    allZ.map (fun Z => ListFast.listReportFast (tinyData 5) Z) = [0, 1, 1, 2, 1, 2, 2, 3] ∧
      allZ.map (fun Z => ListFast.listReportFast (tinyData 1) Z) = [0, 1, 1, 0, 1, 0, 0, 0] := by decide

end NearCubicWires.WireExponent3_5.FinalPass.ListEval
