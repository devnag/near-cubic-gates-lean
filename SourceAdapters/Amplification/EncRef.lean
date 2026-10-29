import SourceAdapters.Amplification.EncField
import SourceAdapters.Joins.STVEncoderTable

/-!
# The truth table of the rounded STV code, as a recursion on numbers (X9, the reference computation)

`app:sources`, "Full-range amplification interface" ("… the evaluation domain is then `F^m`; concatenation with a Hadamard block indexes the binary
codeword by a product of binary cubes … its entire truth table is computable in `2^{O(n)}` time"). The encoder
machine of X9 computes the table position by position; this module states that computation as plain recursions on
numbers and proves it is the truth table of `stvEncode` (`Amplification/GateA.lean`), i.e. the output word of the
join `Joins/STVEncoderTable.lean`.

For the table code `c < 2^ℓ`, `ℓ = (m+1)t` (`layoutEquiv`): the Hadamard position is the low `t` bits of `c` and the
point of `F^m` has coordinates `zc t c j = ⌊c / 2^((j+1)t)⌋ mod 2^t`. The inner value at that point is
`valAt = Σ_{i < 2^n, msg(i)} ∏_{j < m} L_{blk h i j}(zc t c j)` (STV Lemma 25: the low-degree extension with value
`msg(i)` at the grid point of `i`, `blk h i j = ⌊i / 2^(jh)⌋ mod 2^h` the `j`-th block of `h` bits of `i`), with the
Lagrange basis `lag` of `H = {0,…,2^h−1}` (as field elements) computed by `prodFold` and `finv`. The bit is the
parity of the common bits of the value and the position (`hadBit`). Main result: `encoderOutput_eq`.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Amplification.Enc

open Polynomial Finset NearCubicWires NearCubicWires.WireExponent3_5 NearCubicGates.Published.STV
open NearCubicGates.Adapters.Amplification NearCubicWires.ExecutableInterfaces

/-! ## Words and numbers -/

/-- The number whose bit `s < h` is `V s`. -/
def wnum {h : ℕ} (V : Fin h → Bool) : ℕ :=
  Finset.equivBitIndices.symm ((univ.filter fun s => V s = true).map Fin.valEmbedding)

theorem testBit_wnum {h : ℕ} (V : Fin h → Bool) (i : ℕ) :
    (wnum V).testBit i = if hi : i < h then V ⟨i, hi⟩ else false := by
  unfold wnum
  rw [GF.testBit_equivBitIndices_symm]
  split_ifs with hi
  · simp only [mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply]
    cases hv : V ⟨i, hi⟩
    · simp only [decide_eq_false_iff_not, not_exists, not_and]
      intro x hx hxi
      have : x = ⟨i, hi⟩ := Fin.ext hxi
      rw [this, hv] at hx; exact Bool.false_ne_true hx
    · simp only [decide_eq_true_eq]; exact ⟨⟨i, hi⟩, hv, rfl⟩
  · simp only [mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply, decide_eq_false_iff_not,
      not_exists, not_and]
    intro x _ hxi; have := x.isLt; omega

theorem wnum_lt {h : ℕ} (V : Fin h → Bool) : wnum V < 2 ^ h := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [testBit_wnum, dif_neg (by omega)]

theorem wnum_bits {h : ℕ} (w : ℕ) (hw : w < 2 ^ h) : wnum (fun s : Fin h => w.testBit s) = w := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_wnum]
  split_ifs with hi
  · rfl
  · exact (Nat.testBit_lt_two_pow (lt_of_lt_of_le hw (Nat.pow_le_pow_right (by norm_num) (by omega)))).symm

theorem bits_wnum {h : ℕ} (V : Fin h → Bool) : (fun s : Fin h => (wnum V).testBit s) = V := by
  funext s; rw [testBit_wnum, dif_pos s.isLt]

theorem wordPoly_eq_toPoly {t : ℕ} (w : Fin t → Bool) : wordPoly w = GF.toPoly (wnum w) := by
  ext i
  rw [GF.coeff_toPoly, testBit_wnum, Amplification.coeff_wordPoly]
  by_cases hi : i < t
  · rw [dif_pos hi, dif_pos hi]
    cases w ⟨i, hi⟩ <;> rfl
  · rw [dif_neg hi, dif_neg hi]; rfl

theorem fieldElt_eq_rep (p : ℕ) {t : ℕ} (w : Fin t → Bool) : fieldElt (GF.toPoly p) w = GF.rep p (wnum w) := by
  unfold fieldElt GF.rep; rw [wordPoly_eq_toPoly]

theorem wnum_hWord {h t : ℕ} (hht : h ≤ t) (V : Fin h → Bool) : wnum (hWord (t := t) V) = wnum V := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_wnum, testBit_wnum]
  by_cases hi : i < h
  · have hit : i < t := by omega
    simp [hWord, hit, hi]
  · by_cases hit : i < t <;> simp [hWord, hit, hi]

theorem node_eq_rep (p : ℕ) {h t : ℕ} (hht : h ≤ t) (V : Fin h → Bool) :
    node (GF.toPoly p) (t := t) V = GF.rep p (wnum V) := by
  unfold node; rw [fieldElt_eq_rep, wnum_hWord hht]

/-! ## Characteristic two -/

theorem two_eq_zero (q : (ZMod 2)[X]) : (2 : AdjoinRoot q) = 0 := by
  have h : (AdjoinRoot.of q) (2 : ZMod 2) = 2 := map_ofNat _ 2
  rw [← h, show (2 : ZMod 2) = 0 from rfl, map_zero]

theorem sub_eq_add' (q : (ZMod 2)[X]) (a b : AdjoinRoot q) : a - b = a + b := by
  have : b + b = 0 := by rw [← two_mul, two_eq_zero, zero_mul]
  rw [sub_eq_iff_eq_add, add_assoc, this, add_zero]

/-! ## The Lagrange basis of `H` -/

/-- `L_v(x) = ∏_{w < 2^h, w ≠ v} (x + w) / (v + w)`. -/
def lag (p t h v x : ℕ) : ℕ :=
  fmul p t (prodFold p t (fun w => x ^^^ w) v (2 ^ h) 1) (finv p t (prodFold p t (fun w => v ^^^ w) v (2 ^ h) 1))

theorem lt_of_lt_h {h t w : ℕ} (hht : h ≤ t) (hw : w < 2 ^ h) : w < 2 ^ t :=
  lt_of_lt_of_le hw (Nat.pow_le_pow_right (by norm_num) hht)

theorem lag_spec (p t h : ℕ) (hc : GF.PrimitiveCert p t) (hht : h ≤ t) (v x : ℕ) (hv : v < 2 ^ h) (hx : x < 2 ^ t) :
    letI : Fact (Irreducible (GF.toPoly p)) := ⟨GF.irreducible_ref p t hc⟩
    lag p t h v x < 2 ^ t ∧
      GF.rep p (lag p t h v x) =
        eval (GF.rep p x) (Lagrange.basis univ (node (GF.toPoly p) (h := h) (t := t)) (fun s : Fin h => v.testBit s)) := by
  letI : Fact (Irreducible (GF.toPoly p)) := ⟨GF.irreducible_ref p t hc⟩
  have hp := hc.2.1
  have hvt := lt_of_lt_h hht hv
  have hone : 1 < 2 ^ t := Nat.one_lt_two_pow (by have := hc.1; omega)
  have hf1 : ∀ w < 2 ^ h, (fun w => x ^^^ w) w < 2 ^ t := fun w hw => Nat.xor_lt_two_pow hx (lt_of_lt_h hht hw)
  have hf2 : ∀ w < 2 ^ h, (fun w => v ^^^ w) w < 2 ^ t := fun w hw => Nat.xor_lt_two_pow hvt (lt_of_lt_h hht hw)
  obtain ⟨hn1, hn2⟩ := prodFold_spec p t hp (fun w => x ^^^ w) v (2 ^ h) 1 hf1 hone
  obtain ⟨hd1, hd2⟩ := prodFold_spec p t hp (fun w => v ^^^ w) v (2 ^ h) 1 hf2 hone
  set D := prodFold p t (fun w => v ^^^ w) v (2 ^ h) 1 with hD
  set Nm := prodFold p t (fun w => x ^^^ w) v (2 ^ h) 1 with hNm
  have hfac : ∀ w ∈ (range (2 ^ h)).erase v, GF.rep p v + GF.rep p w ≠ 0 := by
    intro w hw h0
    rw [mem_erase, mem_range] at hw
    have : GF.rep p v = GF.rep p w := by
      have e := sub_eq_add' (GF.toPoly p) (GF.rep p v) (GF.rep p w)
      rw [← e] at h0; exact sub_eq_zero.mp h0
    exact hw.1 (GF.rep_injOn p t w v hp (lt_of_lt_h hht hw.2) hvt this.symm)
  have hD0 : GF.rep p D ≠ 0 := by
    rw [hd2, GF.rep, GF.toPoly_one, map_one, one_mul, prod_ne_zero_iff]
    intro w hw
    simp only [GF.rep_xor]
    exact hfac w hw
  obtain ⟨hi1, hi2⟩ := finv_spec p t hc D hd1 hD0
  obtain ⟨hm1, hm2⟩ := fmul_spec p t Nm (finv p t D) hp hn1 hi1
  refine ⟨hm1, ?_⟩
  unfold lag
  rw [← hNm, ← hD, hm2, hi2, hn2, hd2]
  have hr1 : GF.rep p 1 = 1 := by simp [GF.rep, GF.toPoly_one]
  rw [hr1, one_mul, one_mul]
  simp only [GF.rep_xor]
  unfold Lagrange.basis
  rw [eval_prod]
  have hbd : ∀ a b z : AdjoinRoot (GF.toPoly p), eval z (Lagrange.basisDivisor a b) = (a - b)⁻¹ * (z - b) := by
    intro a b z; unfold Lagrange.basisDivisor; simp
  simp only [hbd]
  set Vv : Fin h → Bool := fun s => v.testBit s with hVv
  have hnV : node (GF.toPoly p) (t := t) Vv = GF.rep p v := by rw [node_eq_rep p hht, hVv, wnum_bits v hv]
  have hre : ∏ W ∈ univ.erase Vv, (node (GF.toPoly p) (t := t) Vv - node (GF.toPoly p) (t := t) W)⁻¹ *
      (GF.rep p x - node (GF.toPoly p) (t := t) W) =
      ∏ w ∈ (range (2 ^ h)).erase v, (GF.rep p v + GF.rep p w)⁻¹ * (GF.rep p x + GF.rep p w) := by
    apply prod_nbij' (fun W => wnum W) (fun w => fun s : Fin h => w.testBit s)
    · intro W hW
      rw [mem_erase] at hW ⊢
      refine ⟨fun e => hW.1 ?_, mem_range.mpr (wnum_lt W)⟩
      rw [← bits_wnum W, e]
    · intro w hw
      rw [mem_erase, mem_range] at hw
      refine mem_erase.mpr ⟨fun e => hw.1 ?_, mem_univ _⟩
      have := congrArg wnum e
      rwa [wnum_bits w hw.2, hVv, wnum_bits v hv] at this
    · intro W _; exact bits_wnum W
    · intro w hw
      rw [mem_erase, mem_range] at hw
      exact wnum_bits w hw.2
    · intro W _
      rw [hnV, node_eq_rep p hht, sub_eq_add', sub_eq_add']
  rw [hre, prod_mul_distrib, prod_inv_distrib, mul_comm]

/-! ## The value at a point -/

/-- The `j`-th block of `h` bits of `i` (STV's grid point of the message position `i`). -/
def blk (h i j : ℕ) : ℕ := i / 2 ^ (j * h) % 2 ^ h

/-- The `j`-th coordinate of the point of the table code `c` (`layoutEquiv`). -/
def zc (t c j : ℕ) : ℕ := c / 2 ^ ((j + 1) * t) % 2 ^ t

/-- `∏_{j < m} L_{blk h i j}(zc t c j)`. -/
def prodAt (p t h m i c : ℕ) : ℕ := prodFold p t (fun j => lag p t h (blk h i j) (zc t c j)) m m 1

/-- The inner value at the point of `c`: `Σ_{i < 2^n, T i} prodAt i c`. -/
def valAt (p t h m n : ℕ) (T : ℕ → Bool) (c : ℕ) : ℕ :=
  (List.range (2 ^ n)).foldl (fun Y i => if T i then Y ^^^ prodAt p t h m i c else Y) 0

/-- The Hadamard bit: the parity of the common low `t` bits of `Y` and `c`. -/
def hadBit (t Y c : ℕ) : Bool := decide (((range t).filter fun s => Y.testBit s && c.testBit s).card % 2 = 1)

theorem blk_lt (h i j : ℕ) : blk h i j < 2 ^ h := Nat.mod_lt _ (Nat.two_pow_pos h)

theorem zc_lt (t c j : ℕ) : zc t c j < 2 ^ t := Nat.mod_lt _ (Nat.two_pow_pos t)

theorem prodAt_spec (p t h m : ℕ) (hc : GF.PrimitiveCert p t) (hht : h ≤ t) (i c : ℕ) :
    prodAt p t h m i c < 2 ^ t ∧
      GF.rep p (prodAt p t h m i c) = ∏ j ∈ range m, GF.rep p (lag p t h (blk h i j) (zc t c j)) := by
  have hone : 1 < 2 ^ t := Nat.one_lt_two_pow (by have := hc.1; omega)
  obtain ⟨h1, h2⟩ := prodFold_spec p t hc.2.1 (fun j => lag p t h (blk h i j) (zc t c j)) m m 1
    (fun j _ => (lag_spec p t h hc hht _ _ (blk_lt h i j) (zc_lt t c j)).1) hone
  refine ⟨h1, ?_⟩
  unfold prodAt
  rw [h2, erase_eq_of_notMem (by simp)]
  simp [GF.rep, GF.toPoly_one]

theorem valFold_spec (p t : ℕ) (T : ℕ → Bool) (g : ℕ → ℕ) (hg : ∀ i, g i < 2 ^ t) :
    ∀ N : ℕ, (List.range N).foldl (fun Y i => if T i then Y ^^^ g i else Y) 0 < 2 ^ t ∧
      GF.rep p ((List.range N).foldl (fun Y i => if T i then Y ^^^ g i else Y) 0) =
        ∑ i ∈ range N, if T i then GF.rep p (g i) else 0 := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.foldl_append, Finset.sum_range_succ]
    simp only [List.foldl_cons, List.foldl_nil]
    obtain ⟨h1, h2⟩ := ih
    by_cases hT : T N
    · simp only [hT, if_true]
      exact ⟨Nat.xor_lt_two_pow h1 (hg N), by rw [GF.rep_xor, h2]⟩
    · have hF : T N = false := by simpa using hT
      simp only [hF, Bool.false_eq_true, if_false, add_zero]
      exact ⟨h1, h2⟩

theorem valAt_spec (p t h m n : ℕ) (hc : GF.PrimitiveCert p t) (hht : h ≤ t) (T : ℕ → Bool) (c : ℕ) :
    valAt p t h m n T c < 2 ^ t ∧
      GF.rep p (valAt p t h m n T c) = ∑ i ∈ range (2 ^ n), if T i then GF.rep p (prodAt p t h m i c) else 0 :=
  valFold_spec p t T (fun i => prodAt p t h m i c) (fun i => (prodAt_spec p t h m hc hht i c).1) (2 ^ n)

/-! ## The glue to `stvEncode` -/

theorem layout_fst (m t : ℕ) (w : Fin ((m + 1) * t) → Bool) (j : Fin m) (s : Fin t) :
    ((layoutEquiv m t).symm w).1 j s =
      w ⟨s + t * (j.val + 1), by
        have := s.isLt; have := j.isLt
        calc s.val + t * (j.val + 1) < t + t * (j.val + 1) := by omega
          _ = t * (j.val + 2) := by ring
          _ ≤ t * (m + 1) := Nat.mul_le_mul_left _ (by omega)
          _ = (m + 1) * t := by ring⟩ := by
  simp [layoutEquiv, finProdFinEquiv]
  rfl

theorem layout_snd (m t : ℕ) (w : Fin ((m + 1) * t) → Bool) (s : Fin t) :
    ((layoutEquiv m t).symm w).2 s =
      w ⟨s, by have := s.isLt; nlinarith⟩ := by
  simp [layoutEquiv, finProdFinEquiv]

theorem wnum_zc (m t c : ℕ) (j : Fin m) :
    wnum (((layoutEquiv m t).symm (fun idx : Fin ((m + 1) * t) => c.testBit idx)).1 j) = zc t c j := by
  apply Nat.eq_of_testBit_eq
  intro s
  rw [testBit_wnum]
  unfold zc
  rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  split_ifs with hs
  · rw [layout_fst]; simp [hs]; ring_nf
  · simp [hs]

theorem grid_bits (n m h I : ℕ) (hI : I < 2 ^ n) (j : Fin m) :
    grid (n := n) (m := m) (h := h) (fun idx : Fin n => I.testBit idx) j = fun s : Fin h => (blk h I j).testBit s := by
  funext s
  unfold grid blk
  rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  simp only [s.isLt, decide_true, Bool.true_and]
  split_ifs with hp
  · congr 1; ring
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hI (Nat.pow_le_pow_right (by norm_num) (by omega)))]

/-- The truth table of the message as a predicate on numbers (`boolFunctionTable` order). -/
def msgT {n : ℕ} (msg : (Fin n → Bool) → Bool) (i : ℕ) : Bool := msg (fun idx => i.testBit idx)

theorem msgVal_zero_of_not_mem {n m h : ℕ} (q : (ZMod 2)[X]) (msg : (Fin n → Bool) → Bool)
    (V : Fin m → Fin h → Bool) (hV : V ∉ univ.image (grid (n := n) (m := m) (h := h))) : msgVal q msg V = 0 := by
  classical
  unfold msgVal
  rw [dif_neg]
  rintro ⟨i, hi⟩
  exact hV (mem_image.mpr ⟨i, mem_univ _, hi⟩)

theorem evalAt_eq (C n k p : ℕ) (hc : GF.PrimitiveCert p (tParam C n k)) (msg : (Fin n → Bool) → Bool) (c : ℕ) :
    letI : Fact (Irreducible (GF.toPoly p)) := ⟨GF.irreducible_ref p _ hc⟩
    evalAt (GF.toPoly p) (innerPoly C n k (GF.toPoly p) msg)
        ((layoutEquiv (mParam n k) (tParam C n k)).symm (fun idx => c.testBit idx)).1 =
      GF.rep p (valAt p (tParam C n k) (hParam n k) (mParam n k) n (msgT msg) c) := by
  letI : Fact (Irreducible (GF.toPoly p)) := ⟨GF.irreducible_ref p _ hc⟩
  have hht : hParam n k ≤ tParam C n k := hParam_le_tParam C n k
  have hnm : n ≤ mParam n k * hParam n k := le_mParam_mul n k
  unfold evalAt innerPoly lde
  rw [map_sum]
  simp_rw [map_mul, MvPolynomial.eval_C, map_prod, MvPolynomial.eval_toMvPolynomial]
  set t := tParam C n k
  set h := hParam n k
  set m := mParam n k
  set z := ((layoutEquiv m t).symm (fun idx => c.testBit idx)).1
  rw [(valAt_spec p t h m n hc hht (msgT msg) c).2]
  have hz : ∀ j : Fin m, fieldElt (GF.toPoly p) (z j) = GF.rep p (zc t c j) := by
    intro j; rw [fieldElt_eq_rep, wnum_zc]
  set F : (Fin m → Fin h → Bool) → AdjoinRoot (GF.toPoly p) :=
    fun V => ∏ j : Fin m, eval (GF.rep p (zc t c j)) (lagr (GF.toPoly p) h t (V j)) with hF
  have e1 : ∑ V : Fin m → Fin h → Bool, msgVal (GF.toPoly p) msg V *
      ∏ j, eval (fieldElt (GF.toPoly p) (z j)) (lagr (GF.toPoly p) h t (V j)) =
      ∑ V : Fin m → Fin h → Bool, msgVal (GF.toPoly p) msg V * F V := by
    refine sum_congr rfl fun V _ => ?_
    simp only [hF, hz]
  rw [e1]
  have e2 : ∑ V : Fin m → Fin h → Bool, msgVal (GF.toPoly p) msg V * F V =
      ∑ i : Fin n → Bool, (if msg i then 1 else 0) * F (grid i) := by
    rw [← sum_subset (subset_univ (univ.image (grid (n := n) (m := m) (h := h))))]
    · rw [sum_image (fun a _ b _ hab => grid_injective hnm hab)]
      refine sum_congr rfl fun i _ => ?_
      rw [msgVal_grid hnm]
    · intro V _ hV
      rw [msgVal_zero_of_not_mem _ msg V hV, zero_mul]
  rw [e2]
  have e3 : ∑ i : Fin n → Bool, (if msg i then (1 : AdjoinRoot (GF.toPoly p)) else 0) * F (grid i) =
      ∑ I ∈ range (2 ^ n), (if msg (fun idx => I.testBit idx) then (1 : AdjoinRoot (GF.toPoly p)) else 0) *
        F (grid (fun idx : Fin n => I.testBit idx)) := by
    apply sum_nbij' (fun i => wnum i) (fun I => fun idx : Fin n => I.testBit idx)
    · intro i _; exact mem_range.mpr (wnum_lt i)
    · intro I _; exact mem_univ _
    · intro i _; exact bits_wnum i
    · intro I hI; exact wnum_bits I (mem_range.mp hI)
    · intro i _; rw [bits_wnum]
  rw [e3]
  refine sum_congr rfl fun I hI => ?_
  have hIn : I < 2 ^ n := mem_range.mp hI
  have hprod : F (grid (fun idx : Fin n => I.testBit idx)) = GF.rep p (prodAt p t h m I c) := by
    rw [(prodAt_spec p t h m hc hht I c).2, hF]
    simp only [grid_bits n m h I hIn]
    rw [← Fin.prod_univ_eq_prod_range]
    refine prod_congr rfl fun j _ => ?_
    rw [(lag_spec p t h hc hht _ _ (blk_lt h I j) (zc_lt t c j)).2]
    rfl
  rw [hprod]
  unfold msgT
  split_ifs <;> simp

theorem eltWord_rep (p t : ℕ) (hq : (GF.toPoly p).Monic) (ht : (GF.toPoly p).natDegree = t) (Y : ℕ)
    (hY : Y < 2 ^ t) : eltWord hq ht (GF.rep p Y) = fun s : Fin t => Y.testBit s := by
  apply (fieldElt_bijective hq ht).1
  rw [fieldElt_eltWord, fieldElt_eq_rep, wnum_bits Y hY]

theorem card_filter_fin (t : ℕ) (P : ℕ → Bool) :
    (univ.filter fun s : Fin t => P s = true).card = ((range t).filter fun s => P s = true).card := by
  rw [← card_map Fin.valEmbedding]
  congr 1
  ext x
  simp only [mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply, mem_range]
  constructor
  · rintro ⟨s, hs, rfl⟩; exact ⟨s.isLt, hs⟩
  · rintro ⟨hx, hP⟩; exact ⟨⟨x, hx⟩, hP, rfl⟩

theorem stvEncode_eq (C n k p : ℕ) (hc : GF.PrimitiveCert p (tParam C n k)) (hq : (GF.toPoly p).Monic)
    (ht : (GF.toPoly p).natDegree = tParam C n k) (msg : (Fin n → Bool) → Bool) (c : ℕ) :
    letI : Fact (Irreducible (GF.toPoly p)) := ⟨GF.irreducible_ref p _ hc⟩
    stvEncode C n k hq ht msg (fun idx => c.testBit idx) =
      hadBit (tParam C n k) (valAt p (tParam C n k) (hParam n k) (mParam n k) n (msgT msg) c) c := by
  letI : Fact (Irreducible (GF.toPoly p)) := ⟨GF.irreducible_ref p _ hc⟩
  have hht : hParam n k ≤ tParam C n k := hParam_le_tParam C n k
  unfold stvEncode hadConcat innerWord
  rw [evalAt_eq C n k p hc msg c,
    eltWord_rep p _ hq ht _ (valAt_spec p _ _ (mParam n k) n hc hht (msgT msg) c).1]
  unfold had hadBit
  have hu : ((layoutEquiv (mParam n k) (tParam C n k)).symm (fun idx => c.testBit idx)).2 =
      fun s : Fin (tParam C n k) => c.testBit s := by
    funext s; rw [layout_snd]
  rw [hu]
  congr 2
  exact congrArg (· % 2) (card_filter_fin _ (fun s =>
    (valAt p (tParam C n k) (hParam n k) (mParam n k) n (msgT msg) c).testBit s && c.testBit s))

/-- The code bit at table position `c`, with the X3 modulus. -/
def codeBit (C n k : ℕ) (T : ℕ → Bool) (c : ℕ) : Bool :=
  hadBit (tParam C n k)
    (valAt (GF.firstPrimitive (tParam C n k)) (tParam C n k) (hParam n k) (mParam n k) n T c) c

/-- **The output word of X9 as a recursion on numbers.** -/
theorem encoderOutput_eq (C : ℕ) (r : Joins.EncoderRequest) :
    Joins.encoderOutput C r =
      RepairOrdinary.frame (arityParam C r.n r.k).bits ++
        (List.range (2 ^ arityParam C r.n r.k)).map (codeBit C r.n r.k (msgT r.msg)) := by
  have hcert := (Field.binaryFieldArithmetic.2.1 (tParam C r.n r.k) (one_le_tParam C r.n r.k)).1
  unfold Joins.encoderOutput Joins.stvOutput boolFunctionTable
  simp only
  congr 1
  refine List.map_congr_left fun c _ => ?_
  exact stvEncode_eq C r.n r.k _ hcert _ _ r.msg c

end NearCubicGates.Adapters.Amplification.Enc
