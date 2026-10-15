import Proof.Wire_3_5.PrimitiveThrCall

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires NearCubicWires.SupplierPipeline NearCubicWires.SupplierPrime NearCubicWires.SupplierEstimator
open NearCubicWires.ExecutableInterfaces NearCubicWires.SupplierWalk NearCubicWires.SourceInterfaces
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.Lists NearCubicWires.WireExponent3_5.Rows NearCubicWires.WireExponent3_5.Cost
open scoped Matrix.Norms.L2Operator

/-- A bit as a rational. -/
def bitQ (b : Bool) : ℚ := if b then 1 else 0

theorem bitQ_cast (b : Bool) : ((bitQ b : ℚ) : ℝ) = bitR b := by cases b <;> simp [bitQ, bitR]

/-- Nested column, seed and sample averages are one normalized sum. -/
theorem mean_mean_sample {A C : Type} [Fintype A] [Fintype C] {Q : ℕ} (F : A → C → Fin Q → ℝ) :
    uMean (fun a => uMean (fun c => (∑ l, F a c l) / Q)) =
      (∑ a, ∑ c, ∑ l, F a c l) / (Fintype.card A * Fintype.card C * Q) := by
  unfold uMean
  simp only [Finset.sum_div]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun l _ => ?_
  ring

/-! ## The printed rationals -/

section Values
variable (P : StarParams) (σ : P.Translation) {a : ℕ} {N Q : ℕ} (eqv : P.Errors ≃ Fin N) (S : Fin Q → Fin N × Fin N)

/-- **The SYM printed rational**: `(Σ_zΣ_{(e,e')}Σ_ℓ M·R̂)/(|Z|·|E|·Q)`. -/
noncomputable def symValue (Cs : Fin a → NormalizedSymmetricThresholdCircuit P.n) (carriers : List (Carrier P.n))
    (FP : GapParams) (Pl : FlatListParams) : ℚ :=
  (∑ c : {c // P.IsCenter σ c}, ∑ s : GapSeed FP × Pl.FlatSeed, ∑ l : Fin Q,
      bitQ (symMask P σ carriers FP s.1 (P.point c.1 (eqv.symm (S l).1) (eqv.symm (S l).2))) *
        bitQ (symRhat P Cs Pl s.2 c.1 (eqv.symm (S l).1) (eqv.symm (S l).2))) /
    (Fintype.card {c // P.IsCenter σ c} * Fintype.card (GapSeed FP × Pl.FlatSeed) * Q)

theorem symValue_cast (Cs : Fin a → NormalizedSymmetricThresholdCircuit P.n) (carriers : List (Carrier P.n))
    (FP : GapParams) (Pl : FlatListParams) :
    ((symValue P σ eqv S Cs carriers FP Pl : ℚ) : ℝ) = symEstimate P σ Cs carriers FP Pl eqv S := by
  unfold symEstimate sampleMean
  rw [mean_mean_sample (fun c s l => symCell P σ Cs carriers FP Pl eqv c s (S l).1 (S l).2)]
  unfold symValue symCell
  push_cast
  simp only [bitQ_cast]

/-- **The THR printed rational**: `(Σ_zΣ_eΣ_ℓΣ_{g,p}(1/|𝒫|)M·R̂_{g,p})/(|Z|·|E|·Q)`. -/
noncomputable def thrValue (Cs : Fin a → NormalizedThresholdThresholdCircuit P.n) (carriers : List (Carrier P.n))
    (FP : GapParams) (algorithm : RepairRepresentation.DecompositionAlgorithm) (den : ℕ) (report : List Bool → ℕ) : ℚ :=
  (∑ c : {c // P.IsCenter σ c}, ∑ e : GapSeed FP, ∑ l : Fin Q,
      ∑ gp : ThrEq P Cs algorithm × PrimeIndex (thrCutoff P Cs algorithm den),
        (1 / (Fintype.card (PrimeIndex (thrCutoff P Cs algorithm den)) : ℚ)) *
          (bitQ (symMask P σ carriers FP e (P.point c.1 (eqv.symm (S l).1) (eqv.symm (S l).2))) *
            bitQ (thrRhat P Cs algorithm den report gp.1 gp.2 c.1 (eqv.symm (S l).1) (eqv.symm (S l).2)))) /
    (Fintype.card {c // P.IsCenter σ c} * Fintype.card (GapSeed FP) * Q)

theorem thrValue_cast (Cs : Fin a → NormalizedThresholdThresholdCircuit P.n) (carriers : List (Carrier P.n))
    (FP : GapParams) (algorithm : RepairRepresentation.DecompositionAlgorithm) (den : ℕ) (report : List Bool → ℕ) :
    ((thrValue P σ eqv S Cs carriers FP algorithm den report : ℚ) : ℝ) =
      thrEstimate P σ Cs carriers FP algorithm den report eqv S := by
  unfold thrEstimate sampleMean
  rw [mean_mean_sample (fun c e l => thrCellObs P σ Cs carriers FP algorithm den report eqv c e (S l).1 (S l).2)]
  have hcell : ∀ c e (i j : Fin N), thrCellObs P σ Cs carriers FP algorithm den report eqv c e i j =
      ∑ gp : ThrEq P Cs algorithm × PrimeIndex (thrCutoff P Cs algorithm den),
        (1 / (Fintype.card (PrimeIndex (thrCutoff P Cs algorithm den)) : ℝ)) *
          (bitR (symMask P σ carriers FP e (P.point c.1 (eqv.symm i) (eqv.symm j))) *
            bitR (thrRhat P Cs algorithm den report gp.1 gp.2 c.1 (eqv.symm i) (eqv.symm j))) := by
    intro c e i j
    unfold thrCellObs thrObservable
    refine Finset.sum_congr rfl fun gp _ => ?_
    rw [thrRow_cell]
  simp only [hcell]
  unfold thrValue
  push_cast
  simp only [bitQ_cast]

end Values

/-! ## The call-level rationals -/

variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E}

/-- The printed rational at a `SYM` call. -/
noncomputable def symCallValue (I : PrimitiveInputs B) {n : ℕ} (hs : I.StarAt n) {a : ℕ}
    (Cs : Fin a → NormalizedSymmetricThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (smp : CallSample (I.starParams n hs)) : ℚ :=
  symValue (I.starParams n hs) ((I.starParams n hs).translationOfCodes translation) smp.eqv smp.S Cs carriers
    (I.filterParams .sym n) (symListParams I n a Cs carriers)

/-- The printed rational at a `THR` call. -/
noncomputable def thrCallValue (algorithm : RepairRepresentation.DecompositionAlgorithm) (I : PrimitiveInputs B) {n : ℕ}
    (hs : I.StarAt n) {a : ℕ} (Cs : Fin a → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n))
    (translation : List ℕ) (smp : CallSample (I.starParams n hs)) : ℚ :=
  thrValue (I.starParams n hs) ((I.starParams n hs).translationOfCodes translation) smp.eqv smp.S Cs carriers
    (I.filterParams .thr n) algorithm (thrCallDen algorithm I hs Cs) (thrCallReport algorithm I hs Cs carriers translation)

/-- **The sampler's samples at every call** (the output of `samp:printable`, B6): one indexing of the live halves and
one common sample per call, with the column-averaged maximum state error of `row:sampler-interface` below the call's
target (`n^{−D}/(2𝔐)` for SYM, `n^{−D}/(2|𝒢|·cutoff)` for THR). -/
structure CallSampler (I : PrimitiveInputs B) (algorithm : RepairRepresentation.DecompositionAlgorithm) where
  symS : ∀ {n a : ℕ} (_Cs : Fin a → NormalizedSymmetricThresholdCircuit n) (_carriers : List (Carrier n))
    (_translation : List ℕ) (hs : I.StarAt n), CallSample (I.starParams n hs)
  thrS : ∀ {n a : ℕ} (_Cs : Fin a → NormalizedThresholdThresholdCircuit n) (_carriers : List (Carrier n))
    (_translation : List ℕ) (hs : I.StarAt n), CallSample (I.starParams n hs)
  sym_good : ∀ {n a : ℕ} (Cs : Fin a → NormalizedSymmetricThresholdCircuit n) (carriers : List (Carrier n))
    (translation : List ℕ) (hs : I.StarAt n),
    0 < (symS Cs carriers translation hs).Q ∧
      ∃ ηz : {c // (I.starParams n hs).IsCenter ((I.starParams n hs).translationOfCodes translation) c} → ℝ,
        (∀ c s τ, ‖sampleError (symCallStates I hs Cs carriers translation (symS Cs carriers translation hs) c s τ)
          (symS Cs carriers translation hs).S‖ /
            ((symS Cs carriers translation hs).Q * (symS Cs carriers translation hs).N) ≤ ηz c) ∧
        uMean ηz ≤ (n : ℝ) ^ (-(I.D : ℝ)) / (2 * symMass (I.starParams n hs) Cs)
  thr_good : ∀ {n a : ℕ} (Cs : Fin a → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n))
    (translation : List ℕ) (hs : I.StarAt n),
    0 < (thrS Cs carriers translation hs).Q ∧
      ∃ ηz : {c // (I.starParams n hs).IsCenter ((I.starParams n hs).translationOfCodes translation) c} → ℝ,
        (∀ c e g pr s, ‖sampleError
          (thrCallStates algorithm I hs Cs carriers translation (thrS Cs carriers translation hs) c e g pr s)
          (thrS Cs carriers translation hs).S‖ /
            ((thrS Cs carriers translation hs).Q * (thrS Cs carriers translation hs).N) ≤ ηz c) ∧
        2 * (Fintype.card (ThrEq (I.starParams n hs) Cs algorithm) : ℝ) *
          (thrCutoff (I.starParams n hs) Cs algorithm (thrCallDen algorithm I hs Cs) : ℝ) * uMean ηz ≤
            (n : ℝ) ^ (-(I.D : ℝ))

/-- The star hypotheses are decidable (a machine tests them before a call). -/
instance instDecidableStarAt (I : PrimitiveInputs B) (n : ℕ) : Decidable (I.StarAt n) := by
  unfold PrimitiveInputs.StarAt; infer_instance

/-- **The printed value** of the primitive at a request (`FusedPrimitive.value`): the class mode's rational at the
request's star partition and the sampler's sample; `0` off the star hypotheses (no call there). -/
noncomputable def fusedValue (I : PrimitiveInputs B) (algorithm : RepairRepresentation.DecompositionAlgorithm)
    (smp : CallSampler I algorithm) : PrimRequest → ℚ
  | ⟨n, .sym, _, _, Cs, carriers, translation⟩ =>
      if hs : I.StarAt n then symCallValue I hs Cs carriers translation (smp.symS Cs carriers translation hs) else 0
  | ⟨n, .thr, _, _, Cs, carriers, translation⟩ =>
      if hs : I.StarAt n then
        thrCallValue algorithm I hs Cs carriers translation (smp.thrS Cs carriers translation hs)
      else 0

theorem fused_error (spectrum : ExpanderSpectrumContract) (theta : PrimeThetaBoundContract)
    (algorithm : RepairRepresentation.DecompositionAlgorithm) (I : PrimitiveInputs B) (smp : CallSampler I algorithm)
    (hfe : I.D + 2 ≤ I.filterErrDeg)
    (hG : ∀ {n a : ℕ} (ha : a ≤ 4) (Cs : Fin a → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n))
      (translation : List ℕ), I.Call (thrReq n a ha Cs carriers translation) → ∀ hs : I.StarAt n,
        (Fintype.card (ThrEq (I.starParams n hs) Cs algorithm) : ℝ) * (1 / 2 ^ (I.filterParams .thr n).errExp) ≤
          (n : ℝ) ^ (-(I.D : ℝ)) / 8)
    (req : PrimRequest) (h : I.Call req) :
    |((fusedValue I algorithm smp req : ℚ) : ℝ) - I.truth req| ≤ (req.n : ℝ) ^ (-(I.D : ℝ)) := by
  obtain ⟨n, mode, a, ha, Cs, carriers, translation⟩ := req
  have hs : I.StarAt n := h.2.2.2.2.2.1
  cases mode with
  | thr =>
    obtain ⟨hQ, ηz, hηz, hη⟩ := smp.thr_good Cs carriers translation hs
    have hmain := thr_call_error spectrum theta algorithm I ha Cs carriers translation h hs
      (smp.thrS Cs carriers translation hs) hQ (hG ha Cs carriers translation h hs) ηz hηz hη
    show |((fusedValue I algorithm smp (thrReq n a ha Cs carriers translation) : ℚ) : ℝ) -
      I.truth (thrReq n a ha Cs carriers translation)| ≤ (n : ℝ) ^ (-(I.D : ℝ))
    simp only [fusedValue, dif_pos hs]
    unfold thrCallValue
    rw [thrValue_cast]
    exact hmain
  | sym =>
    obtain ⟨hQ, ηz, hηz, hη⟩ := smp.sym_good Cs carriers translation hs
    have hmain := sym_call_error spectrum I hfe ha Cs carriers translation h hs
      (smp.symS Cs carriers translation hs) hQ ηz hηz hη
    show |((fusedValue I algorithm smp (symReq n a ha Cs carriers translation) : ℚ) : ℝ) -
      I.truth (symReq n a ha Cs carriers translation)| ≤ (n : ℝ) ^ (-(I.D : ℝ))
    simp only [fusedValue, dif_pos hs]
    unfold symCallValue
    rw [symValue_cast]
    exact hmain

/-! ## Non-vacuity: the exhaustive sample -/

/-- The exhaustive sample of a star: every live pair exactly once (`Q = N²`). It meets every call's target with
`η = 0`, so `CallSampler` is inhabited (running time is `samp:printable`'s concern, not this witness's). -/
noncomputable def exhaustiveSample (P : StarParams) : CallSample P :=
  ⟨Fintype.card P.Errors, Fintype.card P.Errors * Fintype.card P.Errors, Fintype.equivFin P.Errors,
    fun l => finProdFinEquiv.symm l⟩

theorem sampleError_exhaustive {N : ℕ} (D : Fin N → Fin N → ℂ) :
    sampleError D (fun l : Fin (N * N) => finProdFinEquiv.symm l) = 0 := by
  ext u v
  simp only [sampleError, Matrix.of_apply, Matrix.zero_apply]
  have hsum : (∑ l : Fin (N * N), if finProdFinEquiv.symm l = (u, v) then D u v else 0) = D u v := by
    rw [Equiv.sum_comp finProdFinEquiv.symm (fun p : Fin N × Fin N => if p = (u, v) then D u v else 0)]
    simp
  rw [hsum]
  push_cast
  ring

theorem exhaustive_pos (P : StarParams) : 0 < (exhaustiveSample P).Q := by
  have : 0 < Fintype.card P.Errors := Fintype.card_pos_iff.mpr ⟨fun _ => none⟩
  show 0 < Fintype.card P.Errors * Fintype.card P.Errors
  positivity

/-- **The exhaustive sampler**: at every call, the exhaustive sample with `η_z = 0`. -/
noncomputable def exhaustiveSampler (I : PrimitiveInputs B) (algorithm : RepairRepresentation.DecompositionAlgorithm) :
    CallSampler I algorithm where
  symS := fun _ _ _ hs => exhaustiveSample (I.starParams _ hs)
  thrS := fun _ _ _ hs => exhaustiveSample (I.starParams _ hs)
  sym_good := by
    intro n a Cs carriers translation hs
    refine ⟨exhaustive_pos _, fun _ => 0, fun c s τ => ?_, ?_⟩
    · show ‖sampleError _ (fun l => finProdFinEquiv.symm l)‖ / _ ≤ 0
      rw [sampleError_exhaustive, norm_zero, zero_div]
    · simp only [uMean, Finset.sum_const_zero, zero_div]
      have hm : 0 < symMass (I.starParams n hs) Cs := by
        unfold symMass
        apply mul_pos
        · have : 0 < ∏ j, (symM (I.starParams n hs) Cs j + 1) ^ 2 := Finset.prod_pos fun j _ => by positivity
          exact_mod_cast this
        · exact Finset.prod_pos fun j _ => by unfold symModulus; positivity
      exact div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (by positivity)
  thr_good := by
    intro n a Cs carriers translation hs
    refine ⟨exhaustive_pos _, fun _ => 0, fun c e g pr s => ?_, ?_⟩
    · show ‖sampleError _ (fun l => finProdFinEquiv.symm l)‖ / _ ≤ 0
      rw [sampleError_exhaustive, norm_zero, zero_div]
    · simp only [uMean, Finset.sum_const_zero, zero_div, mul_zero]
      exact Real.rpow_nonneg (Nat.cast_nonneg _) _

/-- **`lem:primitive`'s error with the exhaustive sampler**: the error field needs only the literals' contracts, the
decomposition algorithm and the caller's endpoint exponent. -/
theorem fused_error_exhaustive (spectrum : ExpanderSpectrumContract) (theta : PrimeThetaBoundContract)
    (algorithm : RepairRepresentation.DecompositionAlgorithm) (I : PrimitiveInputs B) (hfe : I.D + 2 ≤ I.filterErrDeg)
    (hG : ∀ {n a : ℕ} (ha : a ≤ 4) (Cs : Fin a → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n))
      (translation : List ℕ), I.Call (thrReq n a ha Cs carriers translation) → ∀ hs : I.StarAt n,
        (Fintype.card (ThrEq (I.starParams n hs) Cs algorithm) : ℝ) * (1 / 2 ^ (I.filterParams .thr n).errExp) ≤
          (n : ℝ) ^ (-(I.D : ℝ)) / 8)
    (req : PrimRequest) (h : I.Call req) :
    |((fusedValue I algorithm (exhaustiveSampler I algorithm) req : ℚ) : ℝ) - I.truth req| ≤
      (req.n : ℝ) ^ (-(I.D : ℝ)) :=
  fused_error spectrum theta algorithm I (exhaustiveSampler I algorithm) hfe hG req h

end NearCubicWires.WireExponent3_5.Primitive
