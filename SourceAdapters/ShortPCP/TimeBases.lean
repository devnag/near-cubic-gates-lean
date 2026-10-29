import SourceAdapters.ShortPCP.TimeSubspace

/-!
# Single-run time, reference layer 2: the bases of the dimension recursion stay independent

The recursion of `V_{RS,=}` (BCGT13 §12.3.1 `Translate`, `D_{RS,=}`; Algorithm 16) passes from the domain `L` with
basis `B` (dimension `κ`, `k = ⌊κ/2⌋ − γ`) to
* the row domain `L_β` with basis `B_{L00} ++ [a_{k+μ+1}]` if `β ∈ L00`, else `B_{L00} ++ [β + O]`, and
* the column domain `Z_{L0}(L1)` with basis `[Z_{L0}(a) + Z_{L0}(0) | a ∈ B_{L1}]` and offset `Z_{L0}(O)`.
proof of `thm:short-pcp-ours` ("Its recursion roughly halves the dimension of the current affine subspace at each level and does
poly(f) field operations per level") needs these sub-bases to be bases again, so that the poly-time forms of
GetIndexOfElt, membership and `Z` (`TimeSubspace.lean`) apply at every level. Here `γ = 0`, `μ = 1` (the tuple
`(2, 4, 0, 1)` of the join), so `B_{L0} = B.take k`, `B_{L00} = B.take (k + 1)`, `B_{L1} = B.drop k`.

Results (all for an independent `B`):
* membership `β ∈ L00` for `β = sel B_{L1} rv + O` is the coin test `rv < 2` (`mem_span_take_iff`);
* both row bases and the column basis are independent (`indep_take`, `indep_rowNew`, `indep_zMulti`);
* the column basis is `zMulti B_{L0} B_{L1}` and its offset is `0` (`colBasis_eq`, `zEval_offset`);
* the index in `L` of the row domain's `ι`-th element is `rowIdx k rv ι` (`rowIdx_spec`).
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.ShortPCP.Time

open Finset NearCubicGates.Published.BCGT13 NearCubicWires.CanonicalBinary

variable {F : Type} [Field F]

theorem bitsValue_lt : ∀ l : List Bool, bitsValue l < 2 ^ l.length
  | [] => by simp [bitsValue]
  | b :: l => by
    rw [bitsValue_cons, List.length_cons, pow_succ]
    have := bitsValue_lt l
    cases b <;> simp <;> omega

theorem sel_drop (B : List F) (k v : ℕ) (hk : k ≤ B.length) : sel (B.drop k) v = sel B (2 ^ k * v) := by
  have h := sel_lt_add (B.take k) 0 v (by positivity) (B.drop k)
  rw [List.take_append_drop, List.length_take, min_eq_left hk, zero_add, sel_zero, zero_add] at h
  exact h.symm

theorem indep_take {B : List F} (hB : Indep B) (m : ℕ) : Indep (B.take m) := by
  intro v hv h0
  rw [sel_take] at h0
  have hv' : v < 2 ^ m := lt_of_lt_of_le hv (Nat.pow_le_pow_right (by norm_num) (by simp))
  have hm : v % 2 ^ m < 2 ^ B.length := by
    rw [Nat.mod_eq_of_lt hv']
    exact lt_of_lt_of_le hv (Nat.pow_le_pow_right (by norm_num) (by simp))
  have := hB _ hm h0
  rwa [Nat.mod_eq_of_lt hv'] at this

theorem indep_drop {B : List F} (hB : Indep B) (k : ℕ) (hk : k ≤ B.length) : Indep (B.drop k) := by
  intro v hv h0
  rw [sel_drop B k v hk] at h0
  rw [List.length_drop] at hv
  have hlt : 2 ^ k * v < 2 ^ B.length := by
    calc 2 ^ k * v < 2 ^ k * 2 ^ (B.length - k) := by
          exact Nat.mul_lt_mul_of_pos_left hv (by positivity)
      _ = 2 ^ B.length := by rw [← pow_add, Nat.add_sub_cancel' hk]
  have := hB _ hlt h0
  rcases Nat.mul_eq_zero.mp this with h | h
  · exact absurd h (by positivity)
  · exact h

omit [Field F] in
theorem sel_drop_lt {B : List F} (k : ℕ) (hk : k ≤ B.length) {rv : ℕ} (hrv : rv < 2 ^ (B.drop k).length) :
    2 ^ k * rv < 2 ^ B.length := by
  rw [List.length_drop] at hrv
  calc 2 ^ k * rv < 2 ^ k * 2 ^ (B.length - k) := Nat.mul_lt_mul_of_pos_left hrv (by positivity)
    _ = 2 ^ B.length := by rw [← pow_add, Nat.add_sub_cancel' hk]

section Two

variable [CharP F 2]

/-- **Membership is a coin test** (`μ = 1`): `sel B_{L1} rv + O ∈ span B_{L00} O ↔ rv < 2`. -/
theorem mem_span_take_iff [DecidableEq F] {B : List F} (hB : Indep B) (O : F) (k : ℕ) (hk : k + 1 ≤ B.length)
    {rv : ℕ} (hrv : rv < 2 ^ (B.drop k).length) :
    sel (B.drop k) rv + O ∈ span (B.take (k + 1)) O ↔ rv < 2 := by
  rw [mem_span, sel_drop B k rv (by omega), List.length_take, min_eq_left hk]
  have hlt := sel_drop_lt k (by omega) hrv
  constructor
  · rintro ⟨w, hw, hsel⟩
    rw [sel_take, Nat.mod_eq_of_lt hw] at hsel
    have hw' : w < 2 ^ B.length := lt_of_lt_of_le hw (Nat.pow_le_pow_right (by norm_num) hk)
    have := hB.injOn hw' hlt (add_right_cancel hsel)
    subst this
    rw [pow_succ] at hw
    by_contra hc
    push Not at hc
    have : 2 ^ k * 2 ≤ 2 ^ k * rv := Nat.mul_le_mul_left _ hc
    omega
  · intro h
    refine ⟨2 ^ k * rv, ?_, ?_⟩
    · rw [pow_succ]; exact Nat.mul_lt_mul_of_pos_left h (by positivity)
    · rw [sel_take, Nat.mod_eq_of_lt (by rw [pow_succ]; exact Nat.mul_lt_mul_of_pos_left h (by positivity))]

omit [CharP F 2] in
/-- The row basis when `β ∈ L00`: `B_{L00} ++ [a_{k+2}] = B.take (k + 2)`. -/
theorem rowMem_eq (B : List F) (k : ℕ) (hk : k + 1 < B.length) :
    B.take (k + 1) ++ [B.getD (k + 1) 0] = B.take (k + 1 + 1) := by
  rw [List.take_add_one (i := k + 1), List.getElem?_eq_getElem hk, Option.toList_some, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hk, Option.getD_some]

omit [CharP F 2] in
theorem sel_rowNew (B : List F) (k : ℕ) (hk : k + 1 ≤ B.length) (x : F) (c : ℕ) (hc : c < 2 ^ (k + 1 + 1)) :
    sel (B.take (k + 1) ++ [x]) c = sel B (c % 2 ^ (k + 1)) + (if c.testBit (k + 1) then x else 0) := by
  rw [sel_append, sel_take, List.length_take, min_eq_left hk, sel_cons, sel_nil, add_zero]
  congr 1
  have h2 : c / 2 ^ (k + 1) < 2 := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]; rw [pow_succ] at hc; omega
  have hb : c.testBit (k + 1) = decide (c / 2 ^ (k + 1) % 2 = 1) := by
    rw [Nat.testBit, Nat.shiftRight_eq_div_pow]
    rcases Nat.mod_two_eq_zero_or_one (c / 2 ^ (k + 1)) with h | h <;> simp [h, Nat.one_and_eq_mod_two]
  rw [hb]
  split_ifs with h <;> simp_all

theorem indep_rowNew {B : List F} (hB : Indep B) (k : ℕ) (hk : k + 1 < B.length) {rv : ℕ}
    (hrv2 : 2 ≤ rv) (hrv : rv < 2 ^ (B.drop k).length) :
    Indep (B.take (k + 1) ++ [sel B (2 ^ k * rv)]) := by
  intro v hv h0
  rw [List.length_append, List.length_take, min_eq_left hk.le, List.length_singleton] at hv
  rw [sel_rowNew B k hk.le _ v hv] at h0
  have hlt := sel_drop_lt (B := B) k (by omega) hrv
  have hm : v % 2 ^ (k + 1) < 2 ^ B.length :=
    lt_of_lt_of_le (Nat.mod_lt _ (by positivity)) (Nat.pow_le_pow_right (by norm_num) hk.le)
  split_ifs at h0 with hb
  · -- `sel B (v mod 2^{k+1}) = sel B (2^k rv)`: impossible since `2^k·rv ≥ 2^{k+1}`
    have h1 : sel B (v % 2 ^ (k + 1)) = sel B (2 ^ k * rv) := by
      have := CharTwo.add_eq_zero.mp h0; exact this
    have e := hB.injOn hm hlt h1
    have h3 : v % 2 ^ (k + 1) < 2 ^ k * 2 := by rw [← pow_succ]; exact Nat.mod_lt _ (by positivity)
    have h4 : 2 ^ k * 2 ≤ 2 ^ k * rv := Nat.mul_le_mul_left _ hrv2
    omega
  · rw [add_zero] at h0
    have h1 := hB _ hm h0
    have h2 : v / 2 ^ (k + 1) = 0 := by
      have hlt2 : v / 2 ^ (k + 1) < 2 := by
        rw [Nat.div_lt_iff_lt_mul (by positivity)]; rw [pow_succ] at hv; omega
      have hbit : ¬ v / 2 ^ (k + 1) % 2 = 1 := by
        intro h; apply hb; rw [Nat.testBit_eq_decide_div_mod_eq]; simp [h]
      generalize v / 2 ^ (k + 1) = x at hlt2 hbit ⊢
      omega
    have := Nat.div_add_mod v (2 ^ (k + 1))
    rw [h1, h2] at this; omega

/-- The index in `L` of the `ι`-th element of the row domain `L_β` (`μ = 1`; `rv` the coins of `β`). -/
def rowIdx (k rv ι : ℕ) : ℕ :=
  if rv < 2 then 1 + (ι - 1) % 2 ^ (k + 1 + 1)
  else 1 + ((ι - 1) % 2 ^ (k + 1 + 1) % 2 ^ (k + 1) ^^^
    (if ((ι - 1) % 2 ^ (k + 1 + 1)).testBit (k + 1) then 2 ^ k * rv else 0))

theorem rowIdx_bounds (k rv ι n : ℕ) (hk : k + 1 + 1 ≤ n) (hrv : 2 ^ k * rv < 2 ^ n) :
    1 ≤ rowIdx k rv ι ∧ rowIdx k rv ι ≤ 2 ^ n := by
  have hkk : 2 ^ (k + 1 + 1) ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hk
  have hc : (ι - 1) % 2 ^ (k + 1 + 1) < 2 ^ (k + 1 + 1) := Nat.mod_lt _ (by positivity)
  have hm : (ι - 1) % 2 ^ (k + 1 + 1) % 2 ^ (k + 1) < 2 ^ n :=
    lt_of_lt_of_le (Nat.mod_lt _ (by positivity)) (Nat.pow_le_pow_right (by norm_num) (by omega))
  unfold rowIdx
  split_ifs with hr hb
  · omega
  · have := Nat.xor_lt_two_pow hm hrv; omega
  · rw [Nat.xor_zero]; omega

theorem rowIdx_spec {B : List F} (O : F) (k : ℕ) (hk : k + 1 < B.length) {rv : ℕ}
    (hrv : rv < 2 ^ (B.drop k).length) (ι : ℕ) :
    let BLb := if rv < 2 then B.take (k + 1) ++ [B.getD (k + 1) 0]
      else B.take (k + 1) ++ [sel (B.drop k) rv + O + O]
    eltWithIndex BLb O ι = eltWithIndex B O (rowIdx k rv ι) ∧ 1 ≤ rowIdx k rv ι ∧
      rowIdx k rv ι ≤ 2 ^ B.length := by
  intro BLb
  have hlt := sel_drop_lt (B := B) k (by omega) hrv
  have hkk : 2 ^ (k + 1 + 1) ≤ 2 ^ B.length := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hc : (ι - 1) % 2 ^ (k + 1 + 1) < 2 ^ (k + 1 + 1) := Nat.mod_lt _ (by positivity)
  have hb := rowIdx_bounds k rv ι B.length (by omega) hlt
  simp only [BLb]
  by_cases hr : rv < 2
  · rw [if_pos hr]
    unfold rowIdx at hb ⊢
    rw [if_pos hr] at hb ⊢
    rw [rowMem_eq B k hk, eltWithIndex_eq, eltWithIndex_eq, sel_take, Nat.add_sub_cancel_left]
    exact ⟨rfl, hb⟩
  · rw [if_neg hr]
    unfold rowIdx at hb ⊢
    rw [if_neg hr] at hb ⊢
    have hO : sel (B.drop k) rv + O + O = sel B (2 ^ k * rv) := by
      rw [add_assoc, CharTwo.add_self_eq_zero, add_zero, sel_drop B k rv (by omega)]
    rw [hO, eltWithIndex_eq, eltWithIndex_eq, Nat.add_sub_cancel_left]
    have hlen : (B.take (k + 1) ++ [sel B (2 ^ k * rv)]).length = k + 1 + 1 := by
      simp; omega
    rw [← sel_mod _ (ι - 1), hlen, sel_rowNew B k hk.le _ _ hc]
    refine ⟨?_, hb⟩
    rw [sel_xor]
    congr 1
    split_ifs <;> simp

/-! ## The column domain -/

/-- `Z_{L0}(O) = 0`: the offset lies in its own subspace. -/
theorem zEval_offset [DecidableEq F] {B : List F} (hB : Indep B) (O : F) : zEval B O O = 0 := by
  rw [zEval_eq hB, CharTwo.add_self_eq_zero, zProd_zero]

theorem colBasis_eq [DecidableEq F] {B0 : List F} (hB : Indep B0) (O : F) (B1 : List F) :
    B1.map (fun a => zEval B0 O a + zEval B0 O 0) = zMulti B0 B1 := by
  rw [zMulti_eq]
  apply List.map_congr_left
  intro a _
  rw [zEval_eq hB, zEval_eq hB, zero_add, zProd_add, add_assoc, CharTwo.add_self_eq_zero, add_zero]

theorem indep_zMulti {B : List F} (hB : Indep B) (k : ℕ) (hk : k ≤ B.length) :
    Indep (zMulti (B.take k) (B.drop k)) := by
  intro v hv h0
  rw [zMulti_eq, List.length_map] at hv
  rw [zMulti_eq, ← zProd_sel, zProd_eq_zero_iff] at h0
  obtain ⟨w, hw, hsel⟩ := h0
  rw [List.length_take, min_eq_left hk] at hw
  have h := sel_lt_add (B.take k) w v (by rw [List.length_take, min_eq_left hk]; exact hw) (B.drop k)
  rw [List.take_append_drop, hsel, List.length_take, min_eq_left hk, CharTwo.add_self_eq_zero] at h
  have hlt : w + 2 ^ k * v < 2 ^ B.length := by
    rw [List.length_drop] at hv
    calc w + 2 ^ k * v < 2 ^ k + 2 ^ k * v := by omega
      _ = 2 ^ k * (v + 1) := by ring
      _ ≤ 2 ^ k * 2 ^ (B.length - k) := Nat.mul_le_mul_left _ hv
      _ = 2 ^ B.length := by rw [← pow_add, Nat.add_sub_cancel' hk]
  have := hB _ hlt h
  have hpos : 0 < 2 ^ k := by positivity
  rcases Nat.eq_zero_or_pos v with h' | h'
  · exact h'
  · have : 2 ^ k * v ≥ 1 := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by positivity) (by omega))
    omega

end Two

end NearCubicGates.Adapters.ShortPCP.Time
