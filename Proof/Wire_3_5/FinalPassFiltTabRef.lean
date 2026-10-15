import Proof.Wire_3_5.FinalPassFiltRef

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Filt
open NearCubicWires NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.SupplierWalk NearCubicWires.SupplierToeplitzCore NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey NearCubicWires.WireExponent3_5.GF2 NearCubicWires.SourceInterfaces

/-! ## Binary words -/

theorem binary_add : ∀ (a b x : ℕ), binary (a + b) x = binary a x ++ binary b (x / 2 ^ a)
  | 0, b, x => by simp [binary]
  | a + 1, b, x => by
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [binary, List.cons_append]
    rw [binary_add a b (x / 2), Nat.div_div_eq_div_mul, ← pow_succ']

theorem binary_getD' : ∀ (n x i : ℕ), i < n → (binary n x).getD i false = x.testBit i
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, x, 0, _ => by by_cases h : x % 2 = 1 <;> simp [binary, h]
  | n + 1, x, i + 1, h => by
    simp only [binary, List.getD_cons_succ]
    rw [binary_getD' n (x / 2) i (by omega), Nat.testBit_succ]

theorem binary_congr : ∀ (n x y : ℕ), (∀ i < n, x.testBit i = y.testBit i) → binary n x = binary n y
  | 0, _, _, _ => rfl
  | n + 1, x, y, h => by
    simp only [binary]
    have h0 := h 0 (by omega)
    simp only [Nat.testBit_zero, decide_eq_decide] at h0
    have e0 : (x % 2 == 1) = (y % 2 == 1) := by
      by_cases hx : x % 2 = 1
      · have hy : y % 2 = 1 := h0.1 hx
        simp [hx, hy]
      · have hy : ¬ y % 2 = 1 := fun hy => hx (h0.2 hy)
        simp [hx, hy]
    rw [e0, binary_congr n (x / 2) (y / 2) (fun i hi => by
      have := h (i + 1) (by omega); rwa [Nat.testBit_succ, Nat.testBit_succ] at this)]

/-! ## The decoding of a vertex -/

/-- The bit width of one copy seed. -/
def seedW (P : GapParams) : ℕ := P.labelBits + (P.labelBits - 1) + P.labelBits + 2 * P.fieldBits

theorem copySize_eq (P : GapParams) : P.copySize = 2 ^ seedW P := by
  unfold GapParams.copySize seedW
  rw [← pow_add, ← pow_add, ← pow_add, ← pow_add]
  congr 1
  omega

theorem finEquiv_symm_val (N : ℕ) [NeZero N] (z : ZMod N) : (((ZMod.finEquiv N).symm z : Fin N) : ℕ) = z.val := by
  cases N with
  | zero => exact absurd rfl (NeZero.ne 0)
  | succ n => rfl

/-- Digit `j` of the vertex's base seed. -/
def seedDigit (P : GapParams) (x j : ℕ) : ℕ := x / 2 ^ (seedW P * j) % 2 ^ seedW P

theorem vertexSeed_digit (P : GapParams) (v : MargulisVertex P.baseSize) (j : Fin 128) :
    vertexSeed P (Equiv.refl _) v j = copyEquiv P (Equiv.refl _) ⟨seedDigit P v.1.val j, by
      rw [copySize_eq]; exact Nat.mod_lt _ (by positivity)⟩ := by
  show copyEquiv P (Equiv.refl _) (finFunctionFinEquiv.symm ((ZMod.finEquiv P.baseSize).symm v.1) j) = _
  congr 1
  apply Fin.ext
  show ((ZMod.finEquiv P.baseSize).symm v.1 : ℕ) / P.copySize ^ (j : ℕ) % P.copySize = seedDigit P v.1.val j
  rw [finEquiv_symm_val, copySize_eq, seedDigit, ← pow_mul]

/-- Field `v` of digit `j` (its low `m` bits). -/
def fieldV (P : GapParams) (x j : ℕ) : ℕ := x / 2 ^ (seedW P * j) % 2 ^ P.fieldBits
/-- Field `u` of digit `j` (the next `m` bits). -/
def fieldU (P : GapParams) (x j : ℕ) : ℕ := x / 2 ^ (seedW P * j + P.fieldBits) % 2 ^ P.fieldBits
/-- Bit `i` of the Toeplitz translation of digit `j`. -/
def transBit (P : GapParams) (x j i : ℕ) : Bool := x.testBit (seedW P * j + 2 * P.fieldBits + i)
/-- Bit `i` of the strict upper diagonals of digit `j`. -/
def upBit (P : GapParams) (x j i : ℕ) : Bool := x.testBit (seedW P * j + 2 * P.fieldBits + P.labelBits + i)
/-- Bit `i` of the main and lower diagonals of digit `j`. -/
def lowBit (P : GapParams) (x j i : ℕ) : Bool :=
  x.testBit (seedW P * j + 2 * P.fieldBits + P.labelBits + (P.labelBits - 1) + i)

theorem testBit_digit (P : GapParams) (x j i : ℕ) (hi : i < seedW P) :
    (seedDigit P x j).testBit i = x.testBit (seedW P * j + i) := by
  unfold seedDigit
  rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, decide_eq_true hi, Bool.true_and, Nat.add_comm]

theorem bit_val (y i : ℕ) : y / 2 ^ i % 2 = (y.testBit i).toNat := (Nat.toNat_testBit y i).symm

theorem pow_mul_pow (a b : ℕ) : (2 : ℕ) ^ a * 2 ^ b = 2 ^ (a + b) := (pow_add 2 a b).symm

section Decode
variable (P : GapParams) (v : MargulisVertex P.baseSize) (j : Fin 128)

theorem vertexSeed_v : ((vertexSeed P (Equiv.refl _) v j).2.2 : ℕ) = fieldV P v.1.val j := by
  rw [vertexSeed_digit]
  show seedDigit P v.1.val j % (2 ^ P.fieldBits * 2 ^ P.fieldBits) % 2 ^ P.fieldBits = _
  apply Nat.eq_of_testBit_eq
  intro i
  unfold fieldV
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, pow_mul_pow]
  by_cases hi : i < P.fieldBits
  · simp only [decide_eq_true hi, decide_eq_true (by omega : i < P.fieldBits + P.fieldBits), Bool.true_and]
    rw [testBit_digit P _ _ _ (by unfold seedW; omega)]
    congr 1; omega
  · simp only [decide_eq_false hi, Bool.false_and]

theorem vertexSeed_u : ((vertexSeed P (Equiv.refl _) v j).2.1 : ℕ) = fieldU P v.1.val j := by
  rw [vertexSeed_digit]
  show seedDigit P v.1.val j % (2 ^ P.fieldBits * 2 ^ P.fieldBits) / 2 ^ P.fieldBits = _
  apply Nat.eq_of_testBit_eq
  intro i
  unfold fieldU
  simp only [Nat.testBit_div_two_pow, pow_mul_pow, Nat.testBit_mod_two_pow]
  by_cases hi : i < P.fieldBits
  · simp only [decide_eq_true hi, decide_eq_true (by omega : i + P.fieldBits < P.fieldBits + P.fieldBits),
      Bool.true_and]
    rw [testBit_digit P _ _ _ (by unfold seedW; omega)]
    congr 1; omega
  · simp only [decide_eq_false hi, decide_eq_false (by omega : ¬ i + P.fieldBits < P.fieldBits + P.fieldBits),
      Bool.false_and]

theorem vertexSeed_trans (i : Fin P.labelBits) :
    ((vertexSeed P (Equiv.refl _) v j).1.2 i).val = (transBit P v.1.val j i).toNat := by
  rw [vertexSeed_digit]
  show seedDigit P v.1.val j / (2 ^ P.fieldBits * 2 ^ P.fieldBits) % 2 ^ P.labelBits / 2 ^ (i : ℕ) % 2 = _
  rw [bit_val]
  simp only [Nat.testBit_div_two_pow, pow_mul_pow, Nat.testBit_mod_two_pow, decide_eq_true i.isLt, Bool.true_and]
  rw [testBit_digit P _ _ _ (by unfold seedW; have := i.isLt; omega)]
  unfold transBit
  congr 2; omega

theorem vertexSeed_up (i : Fin (P.labelBits - 1)) :
    ((vertexSeed P (Equiv.refl _) v j).1.1.2 i).val = (upBit P v.1.val j i).toNat := by
  rw [vertexSeed_digit]
  show seedDigit P v.1.val j / (2 ^ P.fieldBits * 2 ^ P.fieldBits) / 2 ^ P.labelBits % 2 ^ (P.labelBits - 1) /
    2 ^ (i : ℕ) % 2 = _
  rw [bit_val]
  simp only [Nat.testBit_div_two_pow, pow_mul_pow, Nat.testBit_mod_two_pow, decide_eq_true i.isLt, Bool.true_and]
  rw [testBit_digit P _ _ _ (by unfold seedW; have := i.isLt; omega)]
  unfold upBit
  congr 2; omega

theorem vertexSeed_low (i : Fin P.labelBits) :
    ((vertexSeed P (Equiv.refl _) v j).1.1.1 i).val = (lowBit P v.1.val j i).toNat := by
  rw [vertexSeed_digit]
  show seedDigit P v.1.val j / (2 ^ P.fieldBits * 2 ^ P.fieldBits) / 2 ^ P.labelBits / 2 ^ (P.labelBits - 1) /
    2 ^ (i : ℕ) % 2 = _
  rw [bit_val]
  simp only [Nat.testBit_div_two_pow, pow_mul_pow]
  rw [testBit_digit P _ _ _ (by unfold seedW; have := i.isLt; omega)]
  unfold lowBit
  congr 2; omega

end Decode

/-! ## The inclusion bit from the bits -/

/-- `EP = reverse (main and lower diagonals) ++ (strict upper diagonals)` of digit `j`: row `i` of the Toeplitz
matrix is its window of `ℓ` bits at `ℓ − 1 − i`. -/
def epWord (P : GapParams) (x j : ℕ) : List Bool :=
  ((List.range P.labelBits).map (lowBit P x j)).reverse ++ (List.range (P.labelBits - 1)).map (upBit P x j)

/-- Row `i` of the Toeplitz matrix of digit `j`. -/
def rowWin (P : GapParams) (x j i : ℕ) : List Bool := ((epWord P x j).drop (P.labelBits - 1 - i)).take P.labelBits

/-- **The inclusion bit `H_k` from the bits**: every prefix bit of the hash is zero. -/
def selB (P : GapParams) (x j k : ℕ) : Bool :=
  (List.range P.prefixBits).all fun i =>
    !(xor (transBit P x j i) (parityDot (rowWin P x j i) (binary P.labelBits k)))

theorem rowWin_length (P : GapParams) (x j i : ℕ) (hi : i < P.labelBits) :
    (rowWin P x j i).length = P.labelBits := by
  unfold rowWin epWord
  simp only [List.length_take, List.length_drop, List.length_append, List.length_reverse, List.length_map,
    List.length_range]
  omega

theorem rowWin_getD (P : GapParams) (x j i c : ℕ) (hi : i < P.labelBits) (hc : c < P.labelBits) :
    (rowWin P x j i).getD c false = if c ≤ i then lowBit P x j (i - c) else upBit P x j (c - i - 1) := by
  have hlen := rowWin_length P x j i hi
  rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact hc)]
  simp only [rowWin, epWord, List.getElem_take, List.getElem_drop, List.getElem_append]
  by_cases hci : c ≤ i
  · rw [dif_pos (by simp; omega), if_pos hci]
    simp only [List.getElem_reverse, List.getElem_map, List.getElem_range, List.length_map, List.length_range]
    congr 1; omega
  · rw [dif_neg (by simp; omega), if_neg hci]
    simp only [List.getElem_map, List.getElem_range, List.length_reverse, List.length_map, List.length_range]
    congr 1; omega

theorem toNat_and (a b : Bool) : (a && b).toNat = a.toNat * b.toNat := by cases a <;> cases b <;> rfl

theorem zmod2_eq_val (z : ZMod 2) : z = ((z.val : ℕ) : ZMod 2) := (ZMod.natCast_zmod_val z).symm

theorem dotCnt_eq_sum (cs zs : List Bool) :
    dotCnt cs zs = ∑ i ∈ Finset.range cs.length, (cs.getD i false && zs.getD i false).toNat := by
  unfold dotCnt
  apply Finset.sum_congr rfl
  intro i _
  cases cs.getD i false && zs.getD i false <;> rfl

theorem toeplitzApply_bits (P : GapParams) (v : MargulisVertex P.baseSize) (j : Fin 128) (k : ℕ)
    (i : Fin P.labelBits) :
    toeplitzApply (vertexSeed P (Equiv.refl _) v j).1.1 (coordLabel P.labelBits k) i =
      ((dotCnt (rowWin P v.1.val j i) (binary P.labelBits k) : ℕ) : ZMod 2) := by
  unfold toeplitzApply
  rw [dotCnt_eq_sum, rowWin_length P _ _ _ i.isLt, Nat.cast_sum, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro c _
  rw [zmod2_eq_val (toeplitzEntry _ _ _ * _), ZMod.val_mul, toNat_and]
  congr 1
  have hc := c.isLt
  have hlab : (coordLabel P.labelBits k c).val = ((binary P.labelBits k).getD c false).toNat := by
    rw [binary_getD' _ _ _ hc]
    unfold coordLabel
    cases k.testBit c <;> rfl
  have hent : (toeplitzEntry (vertexSeed P (Equiv.refl _) v j).1.1 i c).val =
      ((rowWin P v.1.val j i).getD c false).toNat := by
    rw [rowWin_getD P _ _ _ _ i.isLt hc]
    unfold toeplitzEntry
    by_cases hci : (c : ℕ) ≤ i
    · rw [dif_pos hci, if_pos hci, vertexSeed_low]
    · rw [dif_neg hci, if_neg hci, vertexSeed_up]
  rw [hent, hlab]
  have h2 : ((rowWin P v.1.val j i).getD c false).toNat * ((binary P.labelBits k).getD c false).toNat < 2 := by
    cases (rowWin P v.1.val j i).getD c false <;> cases (binary P.labelBits k).getD c false <;> decide
  exact Nat.mod_eq_of_lt h2

theorem hash_zero_iff (P : GapParams) (v : MargulisVertex P.baseSize) (j : Fin 128) (k : ℕ) (i : Fin P.labelBits) :
    toeplitzHash (coordLabel P.labelBits k) (vertexSeed P (Equiv.refl _) v j).1 i = 0 ↔
      (!(xor (transBit P v.1.val j i) (parityDot (rowWin P v.1.val j i) (binary P.labelBits k)))) = true := by
  rw [toeplitzHash_apply, toeplitzApply_bits, zmod2_eq_val ((vertexSeed P (Equiv.refl _) v j).1.2 i),
    vertexSeed_trans, ← Nat.cast_add, ZMod.natCast_eq_zero_iff_even, parityDot_eq_odd]
  cases transBit P v.1.val j i
  · simp [Nat.not_odd_iff_even]
  · simp only [Bool.toNat_true, Nat.even_add_one, Bool.true_xor, Bool.not_not, decide_eq_true_eq]
    exact Nat.not_even_iff_odd

theorem prefixBits_le (P : GapParams) : P.prefixBits ≤ P.labelBits := le_max_left _ _

/-- **The inclusion bit from the bits**. -/
theorem selected_eq_selB (P : GapParams) (v : MargulisVertex P.baseSize) (j : Fin 128) (k : ℕ) :
    selected P (vertexSeed P (Equiv.refl _) v j).1 k = selB P v.1.val j k := by
  have hle := prefixBits_le P
  unfold selected selB
  rw [Bool.eq_iff_iff, decide_eq_true_iff, List.all_eq_true]
  constructor
  · intro h i hi
    rw [List.mem_range] at hi
    exact (hash_zero_iff P v j k ⟨i, by omega⟩).1 (h ⟨i, by omega⟩ hi)
  · intro h i hi
    exact (hash_zero_iff P v j k i).2 (h i (List.mem_range.2 hi))

/-! ## The small-bias bit from the bits -/

/-- `v^k` by the shift-and-xor product. -/
def powN (p m v : ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => fmulShift p m (powN p m v k) v

/-- **The small-bias bit `Tr(u v^{k+1})` from the bits**: the parity of `τ` against the product. -/
def trB (P : GapParams) (x j k : ℕ) : Bool :=
  parityDot (binary P.fieldBits (tau (GF.firstPrimitive P.fieldBits) P.fieldBits))
    (binary P.fieldBits (fmulShift (GF.firstPrimitive P.fieldBits) P.fieldBits (fieldU P x j)
      (powN (GF.firstPrimitive P.fieldBits) P.fieldBits (fieldV P x j) (k + 1))))

theorem pow_val (P : GapParams) (w : Fin (2 ^ P.fieldBits)) :
    ∀ k, ((filtOps P).pow w k : ℕ) = powN (GF.firstPrimitive P.fieldBits) P.fieldBits w k
  | 0 => rfl
  | k + 1 => by
    show fmulShift _ _ ((filtOps P).pow w k : ℕ) w = _
    rw [pow_val P w k]; rfl

theorem count_range_filter (f : ℕ → Bool) :
    ∀ n, ((List.range n).filter f).length = ∑ i ∈ Finset.range n, (f i).toNat
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.filter_append, List.length_append, count_range_filter f n, Finset.sum_range_succ]
    cases h : f n <;> simp [h]

theorem parityMasked_eq (mask a m : ℕ) :
    decide (parityMasked mask a m = 1) = parityDot (binary m mask) (binary m a) := by
  rw [parityDot_eq_odd, dotCnt_eq_sum, binary_length]
  unfold parityMasked
  rw [count_range_filter]
  have e : ∑ i ∈ Finset.range m, (mask.testBit i && a.testBit i).toNat =
      ∑ i ∈ Finset.range m, ((binary m mask).getD i false && (binary m a).getD i false).toNat := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    rw [binary_getD' _ _ _ hi, binary_getD' _ _ _ hi]
  rw [e]
  simp only [Nat.odd_iff]

/-- **The small-bias bit from the bits**. -/
theorem biasBit_eq_trB (P : GapParams) (v : MargulisVertex P.baseSize) (j : Fin 128) (k : ℕ) :
    biasBit (filtOps P) (vertexSeed P (Equiv.refl _) v j).2.1 (vertexSeed P (Equiv.refl _) v j).2.2 k =
      trB P v.1.val j k := by
  unfold biasBit trB
  show decide (parityMasked _ (fmulShift _ _ ((vertexSeed P (Equiv.refl _) v j).2.1 : ℕ)
    ((filtOps P).pow (vertexSeed P (Equiv.refl _) v j).2.2 (k + 1) : ℕ)) _ = 1) = _
  rw [pow_val, vertexSeed_u, vertexSeed_v, parityMasked_eq]

/-! ## The table from the bits -/

/-- **The coefficient word of copy `j` from the bits of the vertex `x`.** -/
def coefBits (P : GapParams) (x j L : ℕ) : List Bool := (List.range L).map fun k => selB P x j k && trB P x j k

theorem coefWord_vertex (P : GapParams) (v : MargulisVertex P.baseSize) (j : Fin 128) (L : ℕ) :
    coefWord P (filtOps P) (vertexSeed P (Equiv.refl _) v j) L = coefBits P v.1.val j L := by
  unfold coefWord coefBits
  apply List.map_congr_left
  intro k _
  rw [selected_eq_selB, biasBit_eq_trB]

/-- **The seed's table from the bits of the visited vertices.** -/
theorem filterTable_bits (P : GapParams) (e : GapSeed P) (L : ℕ) :
    filterTable P e L = (List.finRange P.walkLen).map fun i =>
      (List.finRange 128).map fun (j : Fin 128) => coefBits P (e.vertex i).1.val (j : ℕ) L := by
  unfold filterTable
  apply List.map_congr_left
  intro i _
  apply List.map_congr_left
  intro j _
  exact coefWord_vertex P _ j L

end NearCubicWires.WireExponent3_5.FinalPass.Filt
