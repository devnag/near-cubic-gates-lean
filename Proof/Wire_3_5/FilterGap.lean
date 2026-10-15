import Proof.Wire_3_5.FilterGapCopies

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Filters
open NearCubicWires NearCubicWires.SupplierPipeline NearCubicWires.SupplierWalk NearCubicWires.SourceInterfaces
open Finset

noncomputable instance galoisFieldFintype (m : ℕ) : Fintype (GaloisField 2 m) := Fintype.ofFinite _

noncomputable instance galoisFieldDecEq (m : ℕ) : DecidableEq (GaloisField 2 m) := Classical.decEq _

noncomputable def galoisTrace (m : ℕ) : GaloisField 2 m →+ ZMod 2 :=
  (Algebra.trace (ZMod 2) (GaloisField 2 m)).toAddMonoidHom

theorem galoisOps_eq (m : ℕ) : galoisOps m = fieldOps (galoisTrace m) := rfl

/-- The trace is nontrivial (the trace form is nondegenerate). -/
theorem galoisTrace_nontrivial (m : ℕ) : ∃ b, galoisTrace m b ≠ 0 := by
  have hne := (traceForm_nondegenerate (ZMod 2) (GaloisField 2 m)).ne_zero
  by_contra hall
  simp only [not_exists, not_not] at hall
  apply hne
  ext a b
  simpa [Algebra.traceForm_apply, galoisTrace] using hall (a * b)

theorem card_galoisField (m : ℕ) (hm : m ≠ 0) : Fintype.card (GaloisField 2 m) = 2 ^ m := by
  rw [Fintype.card_eq_nat_card]; exact GaloisField.card 2 m hm

theorem sixteen_len_le_card (P : GapParams) : 16 * P.len ≤ Fintype.card (GaloisField 2 P.fieldBits) := by
  rw [card_galoisField _ P.fieldBits_ne_zero]
  unfold GapParams.fieldBits
  rw [pow_add]
  have := Nat.le_pow_clog (b := 2) (by norm_num) P.len
  norm_num
  omega

/-! ## The walk's vertices decode to uniform base seeds -/

theorem sum_vertexSeed (P : GapParams) {K : Type} [Fintype K] (kEq : Fin (2 ^ P.fieldBits) ≃ K)
    (f : BaseSeed P K → ℝ) :
    ∑ v : MargulisVertex P.baseSize, f (vertexSeed P kEq v) = P.baseSize * ∑ b, f b := by
  simp only [vertexSeed, Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  rw [← Finset.mul_sum]
  congr 1
  rw [← (baseEquiv P kEq).sum_comp f]
  exact Fintype.sum_equiv (ZMod.finEquiv P.baseSize).symm.toEquiv _ _ (fun _ => rfl)

theorem card_baseSeed (P : GapParams) {K : Type} [Fintype K] (kEq : Fin (2 ^ P.fieldBits) ≃ K) :
    Fintype.card (BaseSeed P K) = P.baseSize := by
  rw [← Fintype.card_congr (baseEquiv P kEq), Fintype.card_fin]

/-- The base seed at a uniform walk vertex is uniform. -/
theorem booleanMean_vertexSeed (P : GapParams) {K : Type} [Fintype K] (kEq : Fin (2 ^ P.fieldBits) ≃ K)
    (f : BaseSeed P K → Bool) :
    booleanMean (fun v : MargulisVertex P.baseSize => f (vertexSeed P kEq v)) = booleanMean f := by
  unfold booleanMean
  rw [sum_vertexSeed P kEq (fun b => bitAsReal (f b)), card_baseSeed P kEq]
  simp only [MargulisVertex, Fintype.card_prod, ZMod.card]
  have hN : (P.baseSize : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne _)
  push_cast
  field_simp

/-! ## Majority -/

/-- For an odd walk, a failed majority of `good` is a majority of `!good`. -/
theorem majority_complement {m t : ℕ} [NeZero m] (ht : Odd t) (good : MargulisVertex m → Bool)
    (e : MargulisWalkSample m t) (h : concreteMajorityFailure good e = false) :
    concreteMajorityFailure (fun v => !good v) e = true := by
  unfold concreteMajorityFailure concreteBadTimes concreteBadAt majorityThreshold at *
  simp only [decide_eq_false_iff_not, not_le, decide_eq_true_eq] at h ⊢
  have hsplit := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin t)))
    (fun time => good (e.vertex time) = true)
  have hneg : (univ.filter fun time => ¬ good (e.vertex time) = true) =
      univ.filter fun time => (!good (e.vertex time)) = true := by
    ext time; simp
  rw [hneg, Finset.card_univ, Fintype.card_fin] at hsplit
  obtain ⟨k, rfl⟩ := ht
  omega

/-! ## The guarantee -/

structure GapGuarantee (P : GapParams) (F : GapSeed P → List Bool → Bool) : Prop where
  complete : ∀ Z : List Bool, Z.length ≤ P.len → Z.count true ≤ P.cap →
    booleanMean (fun e : GapSeed P => !F e Z) ≤ 1 / 2 ^ P.errExp
  sound : ∀ Z : List Bool, Z.length ≤ P.len → 4096 * P.cap ≤ Z.count true →
    booleanMean (fun e : GapSeed P => F e Z) ≤ 1 / 2 ^ P.errExp

theorem walkLen_odd (P : GapParams) : Odd P.walkLen := ⟨P.errExp / 4, rfl⟩

theorem walk_error_le (P : GapParams) : 1 / (2 : ℝ) ^ (2 * P.walkLen + 4) ≤ 1 / 2 ^ P.errExp := by
  apply one_div_le_one_div_of_le (by positivity)
  apply pow_le_pow_right₀ (by norm_num)
  unfold GapParams.walkLen; omega

theorem gapFilter_guarantee (spectrum : ExpanderSpectrumContract) (P : GapParams) (hU : 1 ≤ P.cap) :
    GapGuarantee P (gapFilter P) := by
  set Tr := galoisTrace P.fieldBits
  set kEq := galoisEquiv P.fieldBits P.fieldBits_ne_zero
  have hTr := galoisTrace_nontrivial P.fieldBits
  have hK := sixteen_len_le_card P
  constructor
  · intro Z hZ hw
    set good : MargulisVertex P.baseSize → Bool := fun v => baseFilter P (fieldOps Tr) (vertexSeed P kEq v) Z
    have hrho : booleanMean (fun v => !good v) ≤ 1 / 128 := by
      rw [booleanMean_vertexSeed P kEq (fun s => !baseFilter P (fieldOps Tr) s Z)]
      exact baseFilter_reject_le P Tr hTr hK Z hZ hw
    have hmaj := concreteMajorityFailure_le spectrum (walkLen_odd P) (fun v => !good v) hrho
    refine le_trans ?_ (hmaj.trans (walk_error_le P))
    apply booleanMean_mono
    intro e he
    apply majority_complement (walkLen_odd P) good e
    simpa [gapFilter, gapFilterWith, galoisOps_eq] using he
  · intro Z hZ hw
    set good : MargulisVertex P.baseSize → Bool := fun v => baseFilter P (fieldOps Tr) (vertexSeed P kEq v) Z
    have hrho : booleanMean good ≤ 1 / 128 := by
      rw [booleanMean_vertexSeed P kEq (fun s => baseFilter P (fieldOps Tr) s Z)]
      exact baseFilter_accept_le P Tr hTr hK hU Z hZ hw
    have hmaj := concreteMajorityFailure_le spectrum (walkLen_odd P) good hrho
    exact hmaj.trans (walk_error_le P)

theorem gapFilter_spec (spectrum : ExpanderSpectrumContract) (P : GapParams) (hU : 1 ≤ P.cap) (Z : List Bool)
    (hZ : Z.length ≤ P.len) :
    (Z.count true ≤ P.cap → booleanMean (fun e : GapSeed P => !gapFilter P e Z) ≤ 1 / 2 ^ P.errExp) ∧
      (4096 * P.cap ≤ Z.count true → booleanMean (fun e : GapSeed P => gapFilter P e Z) ≤ 1 / 2 ^ P.errExp) :=
  ⟨(gapFilter_guarantee spectrum P hU).complete Z hZ, (gapFilter_guarantee spectrum P hU).sound Z hZ⟩

/-- The contract excludes a useless filter: the constant filter `F ≡ 1` fails soundness (at `M ≥ 4096U` and
`ε < 1`). -/
theorem not_gapGuarantee_const (P : GapParams) (hM : 4096 * P.cap ≤ P.len) (hε : 0 < P.errExp) :
    ¬ GapGuarantee P (fun _ _ => true) := by
  intro h
  have := h.sound (List.replicate (4096 * P.cap) true) (by simpa using hM) (by simp)
  have hone : booleanMean (fun _ : GapSeed P => true) = 1 := by
    unfold booleanMean; simp [bitAsReal]
  rw [hone] at this
  have hlt : (1 : ℝ) / 2 ^ P.errExp < 1 := by
    rw [div_lt_one (by positivity)]; exact one_lt_pow₀ (by norm_num) hε.ne'
  linarith

/-- The seed length in bits: the walk start (two base seeds' worth: the base seed and its padding) and `t − 1`
powered-walk labels of `160` bits. -/
def GapParams.seedBits (P : GapParams) : ℕ :=
  2 * (128 * (P.labelBits + (P.labelBits - 1) + P.labelBits + 2 * P.fieldBits)) + 160 * (P.walkLen - 1)

theorem copySize_eq (P : GapParams) :
    P.copySize = 2 ^ (P.labelBits + (P.labelBits - 1) + P.labelBits + 2 * P.fieldBits) := by
  unfold GapParams.copySize
  rw [← pow_add, ← pow_add, ← pow_add, ← pow_add]
  congr 1; omega

/-- **`|seeds| = 2^seedBits`.** -/
theorem card_gapSeed (P : GapParams) : Fintype.card (GapSeed P) = 2 ^ P.seedBits := by
  have he : GapSeed P ≃ MargulisVertex P.baseSize × (Fin (P.walkLen - 1) → PoweredMargulisLabel) :=
    { toFun := fun s => (s.start, s.transitions)
      invFun := fun p => ⟨p.1, p.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr he]
  simp only [Fintype.card_prod, MargulisVertex, ZMod.card, Fintype.card_fun, Fintype.card_fin,
    PoweredMargulisLabel]
  have hN : P.baseSize = 2 ^ (128 * (P.labelBits + (P.labelBits - 1) + P.labelBits + 2 * P.fieldBits)) := by
    unfold GapParams.baseSize; rw [copySize_eq, ← pow_mul, mul_comm]
  have h16 : (16 : ℕ) ^ 40 = 2 ^ 160 := by norm_num
  rw [hN, h16, ← pow_add, ← pow_mul, ← pow_add]
  unfold GapParams.seedBits
  exact congrArg (fun k => 2 ^ k) (by ring)

theorem seedBits_le (P : GapParams) :
    P.seedBits ≤ 6000 * (Nat.clog 2 (P.len + 1) + Nat.clog 2 (P.cap + 1) + P.errExp + 1) := by
  have hA : Nat.clog 2 (32 * P.cap) ≤ Nat.clog 2 (P.cap + 1) + 5 := by
    apply Nat.clog_le_of_le_pow
    rw [pow_add]
    have := Nat.le_pow_clog (b := 2) (by norm_num) (P.cap + 1)
    norm_num; omega
  have hB : Nat.clog 2 P.len ≤ Nat.clog 2 (P.len + 1) := Nat.clog_mono_right 2 (Nat.le_succ _)
  have hr : P.labelBits ≤ Nat.clog 2 (P.cap + 1) + 5 + Nat.clog 2 (P.len + 1) := by
    unfold GapParams.labelBits GapParams.prefixBits; omega
  have hm : P.fieldBits ≤ Nat.clog 2 (P.len + 1) + 4 := by unfold GapParams.fieldBits; omega
  have ht : P.walkLen - 1 ≤ P.errExp / 2 := by unfold GapParams.walkLen; omega
  unfold GapParams.seedBits
  omega

end NearCubicWires.WireExponent3_5.Filters
