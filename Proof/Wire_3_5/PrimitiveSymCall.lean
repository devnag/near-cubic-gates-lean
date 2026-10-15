import Proof.Wire_3_5.PrimitiveSym

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires NearCubicWires.SupplierPipeline NearCubicWires.SupplierWalk NearCubicWires.SourceInterfaces
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.Lists NearCubicWires.WireExponent3_5.Rows NearCubicWires.WireExponent3_5.Cost
open scoped Matrix.Norms.L2Operator

variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E}

/-- A symmetric-top call. -/
abbrev symReq (n a : ℕ) (ha : a ≤ 4) (Cs : Fin a → NormalizedSymmetricThresholdCircuit n) (carriers : List (Carrier n))
    (translation : List ℕ) : PrimRequest :=
  ⟨n, .sym, a, ha, Cs, carriers, translation⟩

def symListParams (I : PrimitiveInputs B) (n a : ℕ) (Cs : Fin a → NormalizedSymmetricThresholdCircuit n)
    (carriers : List (Carrier n)) : FlatListParams :=
  ⟨∑ i, (Cs i).bottomCount, carriers.length * (4096 * B.capOf .sym n), I.D * Nat.clog 2 (n + 2) + 5⟩

/-- The sampler's data at a call: an indexing of the live halves and the common sample `(U_ℓ,V_ℓ)_{ℓ≤Q}`. -/
structure CallSample (P : StarParams) where
  N : ℕ
  Q : ℕ
  eqv : P.Errors ≃ Fin N
  S : Fin Q → Fin N × Fin N

/-- **The printed estimate at a `SYM` call**. -/
noncomputable def symCallEstimate (I : PrimitiveInputs B) {n : ℕ} (hs : I.StarAt n) {a : ℕ}
    (Cs : Fin a → NormalizedSymmetricThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (smp : CallSample (I.starParams n hs)) : ℝ :=
  symEstimate (I.starParams n hs) ((I.starParams n hs).translationOfCodes translation) Cs carriers
    (I.filterParams .sym n) (symListParams I n a Cs carriers) smp.eqv smp.S

/-- The call's state matrices (row:matrix), the family the sampler must control. -/
noncomputable def symCallStates (I : PrimitiveInputs B) {n : ℕ} (hs : I.StarAt n) {a : ℕ}
    (Cs : Fin a → NormalizedSymmetricThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (smp : CallSample (I.starParams n hs))
    (c : {c // (I.starParams n hs).IsCenter ((I.starParams n hs).translationOfCodes translation) c})
    (s : GapSeed (I.filterParams .sym n) × (symListParams I n a Cs carriers).FlatSeed)
    (τ : SymState (symM (I.starParams n hs) Cs)) : Fin smp.N → Fin smp.N → ℂ :=
  symStateAt (I.starParams n hs) ((I.starParams n hs).translationOfCodes translation) Cs carriers
    (I.filterParams .sym n) (symListParams I n a Cs carriers) smp.eqv c s τ

/-! ## The error budget -/

theorem two_pow_clog_ge (D n : ℕ) : ((n : ℝ) + 2) ^ D ≤ 2 ^ (D * Nat.clog 2 (n + 2)) := by
  rw [mul_comm, pow_mul]
  apply pow_le_pow_left₀ (by positivity)
  have := Nat.le_pow_clog (b := 2) (by norm_num) (n + 2)
  exact_mod_cast this

theorem rpow_neg_eq (n D : ℕ) : (n : ℝ) ^ (-(D : ℝ)) = 1 / (n : ℝ) ^ D := by
  rw [Real.rpow_neg (Nat.cast_nonneg _), Real.rpow_natCast, one_div]

/-- The list term: `2a·2^{−(D·L(n)+5)} ≤ n^{−D}/4` for `a ≤ 4`. -/
theorem list_term_le (n D a : ℕ) (hn : 0 < n) (ha : a ≤ 4) :
    ((2 * a : ℕ) : ℝ) * (1 / 2 ^ (D * Nat.clog 2 (n + 2) + 5)) ≤ (n : ℝ) ^ (-(D : ℝ)) / 4 := by
  rw [rpow_neg_eq n D]
  have hnD : (0 : ℝ) < (n : ℝ) ^ D := by positivity
  have h1 : (n : ℝ) ^ D ≤ 2 ^ (D * Nat.clog 2 (n + 2)) :=
    le_trans (pow_le_pow_left₀ (Nat.cast_nonneg _) (by linarith) D) (two_pow_clog_ge D n)
  have ha' : ((2 * a : ℕ) : ℝ) ≤ 8 := by push_cast; exact_mod_cast (by omega : 2 * a ≤ 8)
  rw [pow_add]
  have h32 : (2 : ℝ) ^ 5 = 32 := by norm_num
  rw [h32]
  have hpos : (0 : ℝ) < 2 ^ (D * Nat.clog 2 (n + 2)) := by positivity
  rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
  calc ((2 * a : ℕ) : ℝ) * 4 ≤ 8 * 4 := by nlinarith
    _ = 1 * 32 := by norm_num
    _ ≤ 1 / (n : ℝ) ^ D * (2 ^ (D * Nat.clog 2 (n + 2)) * 32) := by
        rw [one_div, ← mul_assoc, inv_mul_eq_div]
        have : 1 ≤ 2 ^ (D * Nat.clog 2 (n + 2)) / (n : ℝ) ^ D := by rw [le_div_iff₀ hnD]; linarith
        nlinarith

/-- The filter term: `ξ = 2^{−fe·L(n)} ≤ n^{−D}/4` when `fe ≥ D + 2`. -/
theorem filter_term_le (n D fe : ℕ) (hn : 0 < n) (hfe : D + 2 ≤ fe) :
    (1 : ℝ) / 2 ^ (fe * Nat.clog 2 (n + 2)) ≤ (n : ℝ) ^ (-(D : ℝ)) / 4 := by
  rw [rpow_neg_eq n D]
  have hnD : (0 : ℝ) < (n : ℝ) ^ D := by positivity
  have h1 : ((n : ℝ) + 2) ^ fe ≤ 2 ^ (fe * Nat.clog 2 (n + 2)) := two_pow_clog_ge fe n
  have h2 : 4 * (n : ℝ) ^ D ≤ ((n : ℝ) + 2) ^ fe := by
    calc 4 * (n : ℝ) ^ D ≤ ((n : ℝ) + 2) ^ 2 * ((n : ℝ) + 2) ^ D := by
          have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
          apply mul_le_mul (by nlinarith) (pow_le_pow_left₀ (Nat.cast_nonneg _) (by linarith) D) hnD.le
            (by positivity)
      _ = ((n : ℝ) + 2) ^ (D + 2) := by ring
      _ ≤ ((n : ℝ) + 2) ^ fe := pow_le_pow_right₀ (by linarith) hfe
  rw [div_div, one_div_le_one_div (by positivity) (by positivity)]
  rw [mul_comm]
  exact h2.trans h1

/-! ## The error at a call -/

theorem sym_call_error (spectrum : ExpanderSpectrumContract) (I : PrimitiveInputs B) (hfe : I.D + 2 ≤ I.filterErrDeg)
    {n a : ℕ} (ha : a ≤ 4) (Cs : Fin a → NormalizedSymmetricThresholdCircuit n) (carriers : List (Carrier n))
    (translation : List ℕ) (h : I.Call (symReq n a ha Cs carriers translation)) (hs : I.StarAt n)
    (smp : CallSample (I.starParams n hs)) (hQ : 0 < smp.Q)
    (ηz : {c // (I.starParams n hs).IsCenter ((I.starParams n hs).translationOfCodes translation) c} → ℝ)
    (hηz : ∀ c s τ, ‖sampleError (symCallStates I hs Cs carriers translation smp c s τ) smp.S‖ /
      (smp.Q * smp.N) ≤ ηz c)
    (hη : uMean ηz ≤ (n : ℝ) ^ (-(I.D : ℝ)) / (2 * symMass (I.starParams n hs) Cs)) :
    |symCallEstimate I hs Cs carriers translation smp - I.truth (symReq n a ha Cs carriers translation)| ≤
      (n : ℝ) ^ (-(I.D : ℝ)) := by
  have hn : 0 < n := by
    have h2 : 4 * B.rOf n ≤ n := hs.2.2.1
    have h1 : 2 ≤ B.rOf n := hs.2.1
    omega
  have hN : 0 < smp.N := by
    rw [← Fintype.card_fin smp.N, ← Fintype.card_congr smp.eqv]
    exact Fintype.card_pos_iff.mpr ⟨fun _ => none⟩
  have hmask : I.mask (symReq n a ha Cs carriers translation) =
      symMask (I.starParams n hs) ((I.starParams n hs).translationOfCodes translation) carriers
        (I.filterParams .sym n) := by
    funext e x
    exact mask_of_call I hs e x
  have htruth : I.truth (symReq n a ha Cs carriers translation) =
      WireExponent3_5.maskedMean (symMask (I.starParams n hs) ((I.starParams n hs).translationOfCodes translation)
        carriers (I.filterParams .sym n)) (fun i => (Cs i).eval) := by
    unfold PrimitiveInputs.truth
    rw [hmask]
    rfl
  have hgates : GatesIn (fun i => symGates (Cs i)) carriers := h.1
  have hFlen : ∀ X ∈ carriers, 2 * X.length ≤ (I.filterParams .sym n).len :=
    fun X hX => Nat.mul_le_mul_left 2 (h.2.1 X hX).1
  have hM : ∀ i, (Cs i).bottomCount ≤ (symListParams I n a Cs carriers).M := fun i =>
    Finset.single_le_sum (f := fun i => (Cs i).bottomCount) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hmain := sym_primitive_error (I.starParams n hs) ((I.starParams n hs).translationOfCodes translation) Cs
    carriers (I.filterParams .sym n) (symListParams I n a Cs carriers) smp.eqv smp.S spectrum hgates hFlen
    (B.capOf_pos .sym n) hM le_rfl hN hQ ηz _ hηz hη
  rw [htruth]
  refine hmain.trans ?_
  have hmass : 0 < symMass (I.starParams n hs) Cs := by
    unfold symMass
    apply mul_pos
    · have : 0 < ∏ j, (symM (I.starParams n hs) Cs j + 1) ^ 2 := Finset.prod_pos fun j _ => by positivity
      exact_mod_cast this
    · exact Finset.prod_pos fun j _ => by unfold symModulus; positivity
  have h1 := list_term_le n I.D a hn ha
  have h2 := filter_term_le n I.D I.filterErrDeg hn hfe
  have h3 : symMass (I.starParams n hs) Cs * ((n : ℝ) ^ (-(I.D : ℝ)) / (2 * symMass (I.starParams n hs) Cs)) =
      (n : ℝ) ^ (-(I.D : ℝ)) / 2 := by
    field_simp
  have hPl : (symListParams I n a Cs carriers).errExp = I.D * Nat.clog 2 (n + 2) + 5 := rfl
  have hFP : (I.filterParams .sym n).errExp = I.filterErrDeg * Nat.clog 2 (n + 2) := rfl
  rw [hPl, hFP, h3]
  linarith

end NearCubicWires.WireExponent3_5.Primitive
