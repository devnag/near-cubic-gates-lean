import Proof.Wire_3_5.FinalPassFiltTabSel
import Proof.Wire_3_5.FinalPassListEvalBridge
import Proof.Wire_3_5.FinalPassSym

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Flat
open NearCubicWires NearCubicWires.SupplierToeplitzCore NearCubicWires.SupplierToeplitz NearCubicWires.SupplierWalk
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.WireExponent3_5.FinalPass NearCubicWires.WireExponent3_5.FinalPass.Filt
open NearCubicWires.WireExponent3_5.FinalPass.ListEval NearCubicWires.SourceInterfaces

/-! ## The Toeplitz hash from bits -/

/-- The diagonal word: the main and lower diagonals reversed, then the upper diagonals. -/
def epL (rank : ℕ) (lowB upB : ℕ → Bool) : List Bool :=
  ((List.range rank).map lowB).reverse ++ (List.range (rank - 1)).map upB

theorem epL_length (rank : ℕ) (lowB upB : ℕ → Bool) : (epL rank lowB upB).length = rank + (rank - 1) := by
  simp [epL]

theorem winOf_length (rank : ℕ) (lowB upB : ℕ → Bool) (i : ℕ) (hi : i < rank) :
    (winOf (epL rank lowB upB) rank i).length = rank := by
  unfold winOf
  simp only [List.length_take, List.length_drop, epL_length]
  omega

theorem winOf_getD (rank : ℕ) (lowB upB : ℕ → Bool) (i c : ℕ) (hi : i < rank) (hc : c < rank) :
    (winOf (epL rank lowB upB) rank i).getD c false = if c ≤ i then lowB (i - c) else upB (c - i - 1) := by
  have hlen := winOf_length rank lowB upB i hi
  rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact hc)]
  simp only [winOf, epL, List.getElem_take, List.getElem_drop, List.getElem_append]
  by_cases hci : c ≤ i
  · rw [dif_pos (by simp; omega), if_pos hci]
    simp only [List.getElem_reverse, List.getElem_map, List.getElem_range, List.length_map, List.length_range]
    congr 1; omega
  · rw [dif_neg (by simp; omega), if_neg hci]
    simp only [List.getElem_map, List.getElem_range, List.length_reverse, List.length_map, List.length_range]
    congr 1; omega

/-- A bit of `𝔽₂` from a Boolean. -/
def f2 (b : Bool) : ZMod 2 := if b then 1 else 0

theorem f2_val (b : Bool) : (f2 b).val = b.toNat := by cases b <;> rfl

theorem toeplitzApply_bits' (rank : ℕ) (h : ToeplitzSeed rank) (lowB upB : ℕ → Bool)
    (hl : ∀ c : Fin rank, h.1.1 c = f2 (lowB c)) (hu : ∀ c : Fin (rank - 1), h.1.2 c = f2 (upB c)) (k : ℕ)
    (i : Fin rank) :
    toeplitzApply h.1 (coordLabel rank k) i =
      ((dotCnt (winOf (epL rank lowB upB) rank i) (binary rank k) : ℕ) : ZMod 2) := by
  unfold toeplitzApply
  rw [dotCnt_eq_sum, winOf_length rank lowB upB i i.isLt, Nat.cast_sum, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro c _
  rw [zmod2_eq_val (toeplitzEntry _ _ _ * _), ZMod.val_mul, toNat_and]
  congr 1
  have hc := c.isLt
  have hlab : (coordLabel rank k c).val = ((binary rank k).getD c false).toNat := by
    rw [binary_getD' _ _ _ hc]
    unfold coordLabel
    cases k.testBit c <;> rfl
  have hent : (toeplitzEntry h.1 i c).val = ((winOf (epL rank lowB upB) rank i).getD c false).toNat := by
    rw [winOf_getD rank lowB upB _ _ i.isLt hc]
    unfold toeplitzEntry
    by_cases hci : (c : ℕ) ≤ i
    · rw [dif_pos hci, if_pos hci, hl, f2_val]
    · rw [dif_neg hci, if_neg hci, hu, f2_val]
  rw [hent, hlab]
  have h2 : ((winOf (epL rank lowB upB) rank i).getD c false).toNat * ((binary rank k).getD c false).toNat < 2 := by
    cases (winOf (epL rank lowB upB) rank i).getD c false <;> cases (binary rank k).getD c false <;> decide
  exact Nat.mod_eq_of_lt h2

/-- **A Toeplitz hash bit from bits**: zero iff the translation bit equals the row parity of the label. -/
theorem toeplitz_zero_iff (rank : ℕ) (h : ToeplitzSeed rank) (lowB upB trB : ℕ → Bool)
    (hl : ∀ c : Fin rank, h.1.1 c = f2 (lowB c)) (hu : ∀ c : Fin (rank - 1), h.1.2 c = f2 (upB c))
    (ht : ∀ c : Fin rank, h.2 c = f2 (trB c)) (k : ℕ) (i : Fin rank) :
    toeplitzHash (coordLabel rank k) h i = 0 ↔
      xor (trB i) (parityDot (winOf (epL rank lowB upB) rank i) (binary rank k)) = false := by
  rw [toeplitzHash_apply, toeplitzApply_bits' rank h lowB upB hl hu, ht, zmod2_eq_val (f2 (trB i)), f2_val,
    ← Nat.cast_add, ZMod.natCast_eq_zero_iff_even, parityDot_eq_odd]
  cases trB i
  · simp [Nat.not_odd_iff_even]
  · simp only [Bool.toNat_true, Nat.even_add_one, Bool.true_xor, Bool.not_eq_false',
      decide_eq_true_eq]
    exact Nat.not_even_iff_odd

/-- The translation word. -/
def trL (rank : ℕ) (trB : ℕ → Bool) : List Bool := (List.range rank).map trB

/-- **The level bit is stage 6's prefix test**: `i ∈ 𝓛_j` iff no hash bit below `j` mismatches. -/
theorem inLevel_eq_mism (P : BaseListParams) (h : P.Seed) (lowB upB trB : ℕ → Bool)
    (hl : ∀ c : Fin P.rank, h.1.1 c = f2 (lowB c)) (hu : ∀ c : Fin (P.rank - 1), h.1.2 c = f2 (upB c))
    (ht : ∀ c : Fin P.rank, h.2 c = f2 (trB c)) (j i : ℕ) (hj : j ≤ P.rank) :
    P.inLevel h j i = !mism (binary P.rank i) (epL P.rank lowB upB) (trL P.rank trB) P.rank 0 j := by
  unfold BaseListParams.inLevel mism
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_iff, mem_zeroPrefixCell, Bool.not_eq_true', List.any_eq_false, List.mem_range'_1,
    Nat.zero_add]
  constructor
  · intro H c hc
    have hz := (toeplitz_zero_iff P.rank h lowB upB trB hl hu ht i ⟨c, by omega⟩).1 (H ⟨c, by omega⟩ hc.2)
    rw [parW_eq, parityDot_comm]
    have e : (trL P.rank trB).getD c false = trB c := by
      unfold trL; rw [List.getD_eq_getElem _ _ (by simp; omega)]; simp
    rw [e]
    simpa using hz
  · intro H c hc
    have hz := H c ⟨Nat.zero_le _, hc⟩
    rw [parW_eq, parityDot_comm] at hz
    have e : (trL P.rank trB).getD c false = trB c := by
      unfold trL; rw [List.getD_eq_getElem _ _ (by simp)]; simp
    rw [e] at hz
    exact (toeplitz_zero_iff P.rank h lowB upB trB hl hu ht i c).2 (by simpa using hz)

/-! ## The walk vertex's Toeplitz seed -/

theorem zval_symm (d : Fin 2) : ZMod.val ((((ZMod.finEquiv 2).symm : ZMod 2 ≃+* Fin 2) : ZMod 2 ≃ Fin 2).symm d) = d :=
  rfl

/-- The side bits `s`, the seed bits `3·rank − 1`, the padding `2s − (3·rank − 1)` and the vertex number
`N = y + 2^s·x`. -/
abbrev sideB (rank : ℕ) : ℕ := SupplierWalkBridge.toeplitzWalkSideBits rank
abbrev padB (rank : ℕ) : ℕ := 2 * sideB rank - SupplierWalkBridge.toeplitzSeedBits rank
def vnum {rank : ℕ} (v : MargulisVertex (2 ^ sideB rank)) : ℕ := v.2.val + 2 ^ sideB rank * v.1.val

/-- A seed coordinate is the bit of the vertex number after the padding. -/
theorem f2_of_val (z : ZMod 2) (N k : ℕ) (h : z.val = N / 2 ^ k % 2) : z = f2 (N.testBit k) := by
  rw [bit_val] at h
  rw [zmod2_eq_val z, h]
  cases N.testBit k <;> rfl

theorem teq {m : ℕ} [NeZero m] (z : ZMod m) : ((ZMod.finEquiv m).symm.toEquiv z : ℕ) = z.val :=
  finEquiv_symm_val m z

theorem decode_main (rank : ℕ) (v : MargulisVertex (2 ^ sideB rank)) (c : Fin rank) :
    (SupplierWalkBridge.toeplitzWalkEncoding rank v).1.1.1 c = f2 ((vnum v).testBit (padB rank + c)) := by
  apply f2_of_val
  unfold SupplierWalkBridge.toeplitzWalkEncoding SupplierWalkBridge.toeplitzSeedBitEquiv
    SupplierWalkBridge.binaryFunctionFinEquiv
  simp only [Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map_fst, Equiv.coe_fn_mk,
    Equiv.symm_trans_apply, finProdFinEquiv_symm_apply, Equiv.piCongrRight_symm_apply, Pi.map_apply]
  rw [zval_symm, finFunctionFinEquiv_symm_apply_val, Fin.coe_divNat]
  simp only [finCongr_apply, Fin.val_cast, finCongr_symm]
  rw [finProdFinEquiv_apply_val]
  simp only [Prod.map_fst, Prod.map_snd]
  rw [teq, teq, Nat.div_div_eq_div_mul, ← pow_add]
  rfl

theorem decode_up (rank : ℕ) (v : MargulisVertex (2 ^ sideB rank)) (c : Fin (rank - 1)) :
    (SupplierWalkBridge.toeplitzWalkEncoding rank v).1.1.2 c = f2 ((vnum v).testBit (padB rank + (rank + c))) := by
  apply f2_of_val
  unfold SupplierWalkBridge.toeplitzWalkEncoding SupplierWalkBridge.toeplitzSeedBitEquiv
    SupplierWalkBridge.binaryFunctionFinEquiv
  simp only [Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map_fst, Equiv.coe_fn_mk,
    Equiv.symm_trans_apply, finProdFinEquiv_symm_apply, Equiv.piCongrRight_symm_apply, Pi.map_apply]
  rw [zval_symm, finFunctionFinEquiv_symm_apply_val, Fin.coe_divNat]
  simp only [finCongr_apply, Fin.val_cast, finCongr_symm]
  rw [finProdFinEquiv_apply_val]
  simp only [Prod.map_fst, Prod.map_snd]
  rw [teq, teq, Nat.div_div_eq_div_mul, ← pow_add]
  rfl

theorem decode_tr (rank : ℕ) (v : MargulisVertex (2 ^ sideB rank)) (c : Fin rank) :
    (SupplierWalkBridge.toeplitzWalkEncoding rank v).1.2 c =
      f2 ((vnum v).testBit (padB rank + (rank + (rank - 1) + c))) := by
  apply f2_of_val
  unfold SupplierWalkBridge.toeplitzWalkEncoding SupplierWalkBridge.toeplitzSeedBitEquiv
    SupplierWalkBridge.binaryFunctionFinEquiv
  simp only [Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map_fst, Equiv.coe_fn_mk,
    Equiv.symm_trans_apply, finProdFinEquiv_symm_apply, Equiv.piCongrRight_symm_apply, Pi.map_apply]
  rw [zval_symm, finFunctionFinEquiv_symm_apply_val, Fin.coe_divNat]
  simp only [finCongr_apply, Fin.val_cast, finCongr_symm]
  rw [finProdFinEquiv_apply_val]
  simp only [Prod.map_fst, Prod.map_snd]
  rw [teq, teq, Nat.div_div_eq_div_mul, ← pow_add]
  rfl

/-! ## The level table of a visited vertex -/

/-- The main/lower, upper and translation bits of the vertex's seed. -/
def lowV {rank : ℕ} (v : MargulisVertex (2 ^ sideB rank)) (c : ℕ) : Bool := (vnum v).testBit (padB rank + c)
def upV {rank : ℕ} (v : MargulisVertex (2 ^ sideB rank)) (c : ℕ) : Bool := (vnum v).testBit (padB rank + (rank + c))
def trV {rank : ℕ} (v : MargulisVertex (2 ^ sideB rank)) (c : ℕ) : Bool :=
  (vnum v).testBit (padB rank + (rank + (rank - 1) + c))

/-- The diagonal word and the translation word of the vertex's seed. -/
def epV {rank : ℕ} (v : MargulisVertex (2 ^ sideB rank)) : List Bool := epL rank (lowV v) (upV v)
def trLV {rank : ℕ} (v : MargulisVertex (2 ^ sideB rank)) : List Bool := trL rank (trV v)

/-- **The level bits of a visited vertex** (`list:base` at the walk's seed) from the vertex's bits. -/
theorem inLevel_decode (P : FlatListParams) (v : MargulisVertex P.side) (j i : ℕ) (hj : j ≤ P.base.rank) :
    P.base.inLevel (P.decode v) j i =
      !mism (binary P.base.rank i) (epV (rank := P.base.rank) v) (trLV (rank := P.base.rank) v) P.base.rank 0 j :=
  inLevel_eq_mism P.base (P.decode v) (lowV (rank := P.base.rank) v) (upV (rank := P.base.rank) v)
    (trV (rank := P.base.rank) v) (fun c => decode_main P.base.rank v c) (fun c => decode_up P.base.rank v c)
    (fun c => decode_tr P.base.rank v c) j i hj

/-- The rows of the visited vertex's level table. -/
theorem rowsOf_decode (P : FlatListParams) (v : MargulisVertex P.side) (L j : ℕ) (hj : j ≤ P.base.rank) :
    rowsOf (P.base.data (P.decode v)) L j =
      (List.range L).map fun i =>
        !mism (binary P.base.rank i) (epV (rank := P.base.rank) v) (trLV (rank := P.base.rank) v) P.base.rank 0 j := by
  unfold rowsOf
  apply List.map_congr_left
  intro i _
  exact inLevel_decode P v j i hj

theorem J_le_rank (P : BaseListParams) : P.J ≤ P.rank := le_max_left _ _

end NearCubicWires.WireExponent3_5.FinalPass.Flat
