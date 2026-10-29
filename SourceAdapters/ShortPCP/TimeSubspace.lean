import NineInputs

/-!
# Single-run time, reference layer 1: affine subspaces by basis and offset, efficiently

proof of `thm:short-pcp-ours` ("A single run of V_RS or V_VRS takes poly(f) field operations … [BCGT13, Algorithms 12–16]") rests
on four primitives of the transcribed verifiers (`PublishedStatements/BCGT13.lean`) whose leaf definitions are
searches or products over the `2^κ` points of a subspace: GetIndexOfElt (`indexOfElt`), membership in `span`, the
vanishing polynomial `zEval` (Algorithm 21), and GetEltWithIndex / GetRandElt (Algorithms 19–20). This module gives
their poly(κ)-field-operation forms, each proved equal to the leaf definition when the basis is independent
(`Indep`, equivalent to the leaf's `IsBasis` in characteristic two, `isBasis_iff`):

* `sel B v = Σ_j (bit j of v)·B_j`; `getRandElt B O r = sel B (bitsValue r) + O`, `eltWithIndex B O i =
  sel B (i − 1) + O` (`getRandElt_eq`, `eltWithIndex_eq`);
* `indexOfElt B O (eltWithIndex B O i) = i` for `1 ≤ i ≤ 2^κ` (`indexOfElt_eltWithIndex`), hence the index of a
  random element is its coin value plus one (`indexOfElt_getRandElt`);
* the subspace polynomial `zProd B y = ∏_{v < 2^κ} (y − sel B v)` satisfies `Z_{a::B}(y) = Z_B(y)·(Z_B(y)+Z_B(a))`
  and is additive (`zProd_cons`, `zProd_add`); `zEval B O x = zProd B (x + O)` (`zEval_eq`); `zMulti` evaluates it at
  a list of points with `|B|·(|ys| + |B|)` multiplications (`zMulti_eq`) — FindSubspPoly (Alg. 21) as a recursion.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.ShortPCP.Time

open Finset NearCubicGates.Published.BCGT13 NearCubicWires.CanonicalBinary

variable {F : Type} [Field F]

/-! ## Selection by the bits of a number -/

/-- `Σ_j (bit j of v)·B_j` (bits beyond `|B|` ignored). -/
def sel : List F → ℕ → F
  | [], _ => 0
  | a :: B, v => (if v % 2 = 1 then a else 0) + sel B (v / 2)

@[simp] theorem sel_nil (v : ℕ) : sel ([] : List F) v = 0 := rfl

theorem sel_cons (a : F) (B : List F) (v : ℕ) :
    sel (a :: B) v = (if v % 2 = 1 then a else 0) + sel B (v / 2) := rfl

@[simp] theorem sel_zero : ∀ B : List F, sel B 0 = 0
  | [] => rfl
  | a :: B => by simp [sel_cons, sel_zero B]

theorem sel_mod : ∀ (B : List F) (v : ℕ), sel B (v % 2 ^ B.length) = sel B v
  | [], _ => rfl
  | a :: B, v => by
    rw [sel_cons, sel_cons, List.length_cons, pow_succ]
    have h1 : v % (2 ^ B.length * 2) % 2 = v % 2 := by
      rw [Nat.mod_mul_left_mod]
    have h2 : v % (2 ^ B.length * 2) / 2 = v / 2 % 2 ^ B.length := by
      rw [mul_comm, Nat.mod_mul_right_div_self]
    rw [h1, h2, sel_mod B]

theorem sel_append : ∀ (B C : List F) (v : ℕ), sel (B ++ C) v = sel B v + sel C (v / 2 ^ B.length)
  | [], C, v => by simp
  | a :: B, C, v => by
    rw [List.cons_append, sel_cons, sel_cons, sel_append B C, List.length_cons, pow_succ, mul_comm,
      ← Nat.div_div_eq_div_mul]
    ring

theorem sel_take (B : List F) (m v : ℕ) : sel (B.take m) v = sel B (v % 2 ^ m) := by
  by_cases hm : m ≤ B.length
  · conv_rhs => rw [← List.take_append_drop m B]
    rw [sel_append, List.length_take, min_eq_left hm, Nat.mod_div_self, sel_zero, add_zero]
    rw [← sel_mod (B.take m) v, List.length_take, min_eq_left hm]
  · push Not at hm
    rw [List.take_of_length_le hm.le, ← sel_mod B (v % 2 ^ m), ← sel_mod B v,
      Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hm.le)]

theorem sel_lt_add (B : List F) (v w : ℕ) (hv : v < 2 ^ B.length) (C : List F) :
    sel (B ++ C) (v + 2 ^ B.length * w) = sel B v + sel C w := by
  rw [sel_append, ← sel_mod B (v + 2 ^ B.length * w), Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hv,
    Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hv, zero_add]

section Two

variable [CharP F 2]

theorem sel_xor : ∀ (B : List F) (v w : ℕ), sel B (v ^^^ w) = sel B v + sel B w
  | [], _, _ => by simp
  | a :: B, v, w => by
    rw [sel_cons, sel_cons, sel_cons, Nat.xor_div_two, sel_xor B]
    have ha : a + a = 0 := CharTwo.add_self_eq_zero a
    have hx : (v ^^^ w) % 2 = (v + w) % 2 := Nat.xor_mod_two_eq
    rcases Nat.mod_two_eq_zero_or_one v with hv | hv <;>
      rcases Nat.mod_two_eq_zero_or_one w with hw | hw
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]; ring
    · rw [if_pos (by omega), if_neg (by omega), if_pos (by omega)]; ring
    · rw [if_pos (by omega), if_pos (by omega), if_neg (by omega)]; ring
    · rw [if_neg (by omega), if_pos (by omega), if_pos (by omega)]; linear_combination (-1 : F) * ha

theorem sel_inj_iff_indep_aux (B : List F) (v w : ℕ) : sel B v = sel B w ↔ sel B (v ^^^ w) = 0 := by
  rw [sel_xor, CharTwo.add_eq_zero]

end Two

/-! ## Bits and the leaf's element functions -/

section Dec

variable [DecidableEq F]

theorem bitsValue_cons (b : Bool) (r : List Bool) : bitsValue (b :: r) = b.toNat + 2 * bitsValue r := rfl

omit [DecidableEq F] in
theorem getRandElt_eq (B : List F) (O : F) (r : List Bool) : getRandElt B O r = sel B (bitsValue r) + O := by
  unfold getRandElt
  congr 1
  induction B generalizing r with
  | nil => simp
  | cons a B ih =>
    cases r with
    | nil => simp [bitsValue]
    | cons b r =>
      rw [List.zipWith_cons_cons, List.sum_cons, ih, sel_cons, bitsValue_cons]
      cases b <;> simp [Nat.add_mul_div_left]

theorem bitsValue_map_testBit (v : ℕ) : ∀ n : ℕ, bitsValue ((List.range n).map fun j => v.testBit j) = v % 2 ^ n
  | 0 => by simp [bitsValue, Nat.mod_one]
  | n + 1 => by
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, bitsValue_cons]
    have ih := bitsValue_map_testBit (v / 2) n
    have e : ((List.range n).map ((fun j => v.testBit j) ∘ Nat.succ)) =
        (List.range n).map fun j => (v / 2).testBit j := by
      apply List.map_congr_left; intro j _; simp [Nat.testBit_div_two]
    have h0 : (v.testBit 0).toNat = v % 2 := by
      rw [Nat.testBit_zero]; rcases Nat.mod_two_eq_zero_or_one v with h | h <;> simp [h]
    rw [e, ih, h0, pow_succ, mul_comm (2 ^ n) 2, Nat.mod_mul]

omit [DecidableEq F] in
theorem eltWithIndex_eq (B : List F) (O : F) (i : ℕ) : eltWithIndex B O i = sel B (i - 1) + O := by
  unfold eltWithIndex
  rw [getRandElt_eq, bitsValue_map_testBit, sel_mod]

/-- The points of `span B O`, as an image of `range (2^κ)`. -/
theorem span_eq (B : List F) (O : F) :
    span B O = (Finset.range (2 ^ B.length)).image fun v => sel B v + O := by
  unfold span
  ext x
  simp only [List.mem_toFinset, List.mem_map, List.mem_range, Finset.mem_image, Finset.mem_range,
    eltWithIndex_eq, Nat.add_sub_cancel]

theorem mem_span (B : List F) (O x : F) : x ∈ span B O ↔ ∃ v < 2 ^ B.length, sel B v + O = x := by
  rw [span_eq]; simp

end Dec

/-- Independence of the basis list over `𝔽₂`. -/
def Indep (B : List F) : Prop := ∀ v < 2 ^ B.length, sel B v = 0 → v = 0

theorem Indep.injOn [CharP F 2] {B : List F} (hB : Indep B) {v w : ℕ} (hv : v < 2 ^ B.length)
    (hw : w < 2 ^ B.length) (h : sel B v = sel B w) : v = w := by
  rw [sel_inj_iff_indep_aux] at h
  have h0 := hB _ (Nat.xor_lt_two_pow hv hw) h
  have h1 := Nat.xor_xor_cancel_left v w
  rw [h0, Nat.xor_zero] at h1
  exact h1

theorem isBasis_iff [DecidableEq F] [CharP F 2] (B : List F) (O : F) : IsBasis B O ↔ Indep B := by
  unfold IsBasis
  have hc : ((Finset.range (2 ^ B.length)).image fun v => sel B v + O).card = 2 ^ B.length ↔
      ((Finset.range (2 ^ B.length)).image fun v => sel B v + O).card = (Finset.range (2 ^ B.length)).card := by
    rw [Finset.card_range]
  rw [span_eq, hc, Finset.card_image_iff]
  constructor
  · intro h v hv h0
    have := h (Finset.mem_coe.mpr (Finset.mem_range.mpr hv))
      (Finset.mem_coe.mpr (Finset.mem_range.mpr (Nat.two_pow_pos B.length))) (by simp [h0])
    exact this
  · intro hB v hv w hw h
    simp only [Finset.coe_range, Set.mem_Iio] at hv hw
    exact hB.injOn hv hw (add_right_cancel h)

/-! ## GetIndexOfElt -/

theorem find_range_eq (p : ℕ → Bool) (i : ℕ) (hi : p i = true) (hlt : ∀ j < i, p j = false) :
    ∀ n, i < n → (List.range n).find? p = some i := by
  intro n hn
  induction n with
  | zero => omega
  | succ n ih =>
    rw [List.range_succ, List.find?_append]
    rcases Nat.lt_or_ge i n with h | h
    · rw [ih h]; rfl
    · have hin : i = n := by omega
      subst hin
      have hnone : (List.range i).find? p = none := by
        rw [List.find?_eq_none]
        intro j hj
        rw [List.mem_range] at hj
        simp [hlt j hj]
      rw [hnone]
      simp [hi]

theorem indexOfElt_eltWithIndex [DecidableEq F] [CharP F 2] {B : List F} (hB : Indep B) (O : F) (i : ℕ) (hi : 1 ≤ i)
    (hi' : i ≤ 2 ^ B.length) : indexOfElt B O (eltWithIndex B O i) = i := by
  unfold indexOfElt
  rw [find_range_eq _ (i - 1) _ _ (2 ^ B.length) (by omega)]
  · simp; omega
  · simp [Nat.sub_add_cancel hi]
  · intro j hj
    simp only [decide_eq_false_iff_not]
    intro h
    rw [eltWithIndex_eq, eltWithIndex_eq, Nat.add_sub_cancel] at h
    have := hB.injOn (by omega) (by omega) (add_right_cancel h)
    omega

theorem getRandElt_eq_eltWithIndex (B : List F) (O : F) (r : List Bool) :
    getRandElt B O r = eltWithIndex B O (1 + bitsValue r % 2 ^ B.length) := by
  rw [getRandElt_eq, eltWithIndex_eq, Nat.add_sub_cancel_left, sel_mod]

/-- The index of a random element is its coin value plus one (BCGT13 Alg. 19–20 with GetIndexOfElt). -/
theorem indexOfElt_getRandElt [DecidableEq F] [CharP F 2] {B : List F} (hB : Indep B) (O : F) (r : List Bool) :
    indexOfElt B O (getRandElt B O r) = 1 + bitsValue r % 2 ^ B.length := by
  rw [getRandElt_eq_eltWithIndex, indexOfElt_eltWithIndex hB]
  · omega
  · have := Nat.mod_lt (bitsValue r) (Nat.two_pow_pos B.length); omega

/-! ## The subspace polynomial (FindSubspPoly, Algorithm 21) -/

/-- `Z_B(y) = ∏_{v < 2^κ} (y − sel B v)`: the vanishing polynomial of the linear span (with multiplicity). -/
def zProd (B : List F) (y : F) : F := ∏ v ∈ Finset.range (2 ^ B.length), (y - sel B v)

theorem prod_range_two_mul {M : Type} [CommMonoid M] (g : ℕ → M) :
    ∀ m : ℕ, ∏ v ∈ Finset.range (2 * m), g v = ∏ w ∈ Finset.range m, (g (2 * w) * g (2 * w + 1))
  | 0 => by simp
  | m + 1 => by
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.prod_range_succ, Finset.prod_range_succ,
      prod_range_two_mul g m, Finset.prod_range_succ, mul_assoc]

section Two

variable [CharP F 2]

omit [CharP F 2] in
@[simp] theorem zProd_nil (y : F) : zProd [] y = y := by simp [zProd]

theorem zProd_cons_mul (a : F) (B : List F) (y : F) : zProd (a :: B) y = zProd B y * zProd B (y + a) := by
  unfold zProd
  rw [List.length_cons, pow_succ, mul_comm, prod_range_two_mul, Finset.prod_mul_distrib]
  congr 1
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [sel_cons]; simp
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [sel_cons]
    have h1 : (2 * w + 1) % 2 = 1 := by omega
    have h2 : (2 * w + 1) / 2 = w := by omega
    rw [if_pos h1, h2, CharTwo.sub_eq_add, CharTwo.sub_eq_add]
    ring

theorem zProd_add : ∀ (B : List F) (y y' : F), zProd B (y + y') = zProd B y + zProd B y'
  | [], y, y' => by simp
  | a :: B, y, y' => by
    rw [zProd_cons_mul, zProd_cons_mul, zProd_cons_mul, zProd_add B, zProd_add B, zProd_add B, zProd_add B,
      zProd_add B]
    have h2 : ∀ u v : F, (u + v) ^ 2 = u ^ 2 + v ^ 2 := CharTwo.add_sq
    linear_combination h2 (zProd B y) (zProd B y')

theorem zProd_cons (a : F) (B : List F) (y : F) :
    zProd (a :: B) y = zProd B y * (zProd B y + zProd B a) := by
  rw [zProd_cons_mul, zProd_add]

@[simp] theorem zProd_zero (B : List F) : zProd B 0 = 0 := by
  have h := zProd_add B 0 0
  rw [add_zero] at h
  have h2 : zProd B 0 + zProd B 0 = 0 := CharTwo.add_self_eq_zero _
  rw [← h] at h2
  exact h2

theorem zProd_sel (B : List F) : ∀ (C : List F) (v : ℕ), zProd B (sel C v) = sel (C.map (zProd B)) v
  | [], v => by simp
  | c :: C, v => by
    rw [sel_cons, List.map_cons, sel_cons, zProd_add, zProd_sel B C]
    split_ifs <;> simp

omit [CharP F 2] in
theorem zProd_eq_zero_iff (B : List F) (y : F) : zProd B y = 0 ↔ ∃ v < 2 ^ B.length, y = sel B v := by
  unfold zProd
  rw [Finset.prod_eq_zero_iff]
  simp [sub_eq_zero]

/-- **Algorithm 21 as a value.** `zEval B O x = Z_B(x + O)` for an independent basis. -/
theorem zEval_eq [DecidableEq F] {B : List F} (hB : Indep B) (O x : F) : zEval B O x = zProd B (x + O) := by
  unfold zEval zProd
  rw [span_eq, Finset.prod_image]
  · refine Finset.prod_congr rfl fun v _ => ?_
    simp only [CharTwo.sub_eq_add]; ring
  · intro v hv w hw h
    simp only [Finset.coe_range, Set.mem_Iio] at hv hw
    exact hB.injOn hv hw (add_right_cancel h)

end Two

/-- The recursion of Algorithm 21 on a list of points: `|B|` levels, each squaring-and-multiplying every point. -/
def zMulti : List F → List F → List F
  | [], ys => ys
  | a :: B, ys =>
    let v := zMulti B (a :: ys)
    v.tail.map fun z => z * (z + v.headD 0)

theorem zMulti_eq [CharP F 2] : ∀ (B ys : List F), zMulti B ys = ys.map (zProd B)
  | [], ys => by
    have h : zProd ([] : List F) = id := funext zProd_nil
    simp [zMulti, h]
  | a :: B, ys => by
    simp only [zMulti, zMulti_eq B, List.map_cons, List.tail_cons, List.headD_cons, List.map_map]
    apply List.map_congr_left
    intro y _
    simp [zProd_cons]

end NearCubicGates.Adapters.ShortPCP.Time
