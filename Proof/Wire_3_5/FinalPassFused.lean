import Proof.Wire_3_5.FinalPassThr

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires NearCubicWires.SupplierPipeline NearCubicWires.SupplierPrime NearCubicWires.SupplierEstimator
open NearCubicWires.ExecutableInterfaces NearCubicWires.SourceInterfaces NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.WireExponent3_5.Primitive NearCubicWires.WireExponent3_5.Cost

variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E}

/-- The THR call's digit-list reporter, computable: the rational greedy's fixed hash, fast reports. -/
def thrCallReportBits (algorithm : RepairRepresentation.DecompositionAlgorithm) (I : PrimitiveInputs B) {n : ℕ}
    (hs : I.StarAt n) {a : ℕ} (Cs : Fin a → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n))
    (translation : List ℕ) : List Bool → ℕ :=
  thrReportBits (I.starParams n hs) ((I.starParams n hs).translationOfCodes translation) Cs carriers
    (I.filterParams .thr n) algorithm (thrCallDen algorithm I hs Cs) (thrCallE algorithm I hs Cs carriers)
    (thrCallT algorithm I hs Cs carriers) (thrCallJ algorithm I hs Cs carriers)

theorem thrCallReport_eq_bits (algorithm : RepairRepresentation.DecompositionAlgorithm) (I : PrimitiveInputs B) {n : ℕ}
    (hs : I.StarAt n) {a : ℕ} (Cs : Fin a → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n))
    (translation : List ℕ) :
    thrCallReport algorithm I hs Cs carriers translation = thrCallReportBits algorithm I hs Cs carriers translation :=
  thrReport_eq_bits _ _ _ _ _ _ _ _ _ _

/-- The SYM call's printed rational, computable. -/
def symCallValueBits (I : PrimitiveInputs B) {n : ℕ} (hs : I.StarAt n) {a : ℕ}
    (Cs : Fin a → NormalizedSymmetricThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (smp : CallSample (I.starParams n hs)) : ℚ :=
  symValueBits (I.starParams n hs) ((I.starParams n hs).translationOfCodes translation) smp.eqv smp.S Cs carriers
    (I.filterParams .sym n) (symListParams I n a Cs carriers)

/-- The THR call's printed rational, computable. -/
def thrCallValueBits (algorithm : RepairRepresentation.DecompositionAlgorithm) (I : PrimitiveInputs B) {n : ℕ}
    (hs : I.StarAt n) {a : ℕ} (Cs : Fin a → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n))
    (translation : List ℕ) (smp : CallSample (I.starParams n hs)) : ℚ :=
  thrValueBits (I.starParams n hs) ((I.starParams n hs).translationOfCodes translation) smp.eqv smp.S Cs carriers
    (I.filterParams .thr n) algorithm (thrCallDen algorithm I hs Cs) (thrCallReportBits algorithm I hs Cs carriers translation)

theorem symCallValue_eq_bits (I : PrimitiveInputs B) {n : ℕ} (hs : I.StarAt n) {a : ℕ}
    (Cs : Fin a → NormalizedSymmetricThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (smp : CallSample (I.starParams n hs)) :
    symCallValue I hs Cs carriers translation smp = symCallValueBits I hs Cs carriers translation smp :=
  (symValueBits_eq _ _ _ _ _ _ _ _).symm

theorem thrCallValue_eq_bits (algorithm : RepairRepresentation.DecompositionAlgorithm) (I : PrimitiveInputs B) {n : ℕ}
    (hs : I.StarAt n) {a : ℕ} (Cs : Fin a → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n))
    (translation : List ℕ) (smp : CallSample (I.starParams n hs)) :
    thrCallValue algorithm I hs Cs carriers translation smp =
      thrCallValueBits algorithm I hs Cs carriers translation smp := by
  unfold thrCallValue thrCallValueBits
  rw [thrCallReport_eq_bits]
  exact (thrValueBits_eq _ _ _ _ _ _ _ _ _ _).symm

/-- **The primitive's printed value, computable** (the ref of the final-pass machine C5): the class mode's rational at
the request's star partition and the sampler's sample; `0` off the star hypotheses. -/
def fusedValueBits (I : PrimitiveInputs B) (algorithm : RepairRepresentation.DecompositionAlgorithm)
    (smp : CallSampler I algorithm) : PrimRequest → ℚ
  | ⟨n, .sym, _, _, Cs, carriers, translation⟩ =>
      if hs : I.StarAt n then symCallValueBits I hs Cs carriers translation (smp.symS Cs carriers translation hs)
      else 0
  | ⟨n, .thr, _, _, Cs, carriers, translation⟩ =>
      if hs : I.StarAt n then
        thrCallValueBits algorithm I hs Cs carriers translation (smp.thrS Cs carriers translation hs)
      else 0

/-- **The computable value is the primitive's value** on every request. -/
theorem fusedValueBits_eq (I : PrimitiveInputs B) (algorithm : RepairRepresentation.DecompositionAlgorithm)
    (smp : CallSampler I algorithm) (req : PrimRequest) :
    fusedValueBits I algorithm smp req = fusedValue I algorithm smp req := by
  obtain ⟨n, mode, a, ha, Cs, carriers, translation⟩ := req
  cases mode with
  | thr =>
    simp only [fusedValueBits, fusedValue]
    split_ifs with hs
    · exact (thrCallValue_eq_bits algorithm I hs Cs carriers translation _).symm
    · rfl
  | sym =>
    simp only [fusedValueBits, fusedValue]
    split_ifs with hs
    · exact (symCallValue_eq_bits I hs Cs carriers translation _).symm
    · rfl

theorem fusedValueBits_error (spectrum : ExpanderSpectrumContract) (theta : PrimeThetaBoundContract)
    (algorithm : RepairRepresentation.DecompositionAlgorithm) (I : PrimitiveInputs B) (smp : CallSampler I algorithm)
    (hfe : I.D + 2 ≤ I.filterErrDeg)
    (hG : ∀ {n a : ℕ} (ha : a ≤ 4) (Cs : Fin a → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n))
      (translation : List ℕ), I.Call (thrReq n a ha Cs carriers translation) → ∀ hs : I.StarAt n,
        (Fintype.card (ThrEq (I.starParams n hs) Cs algorithm) : ℝ) * (1 / 2 ^ (I.filterParams .thr n).errExp) ≤
          (n : ℝ) ^ (-(I.D : ℝ)) / 8)
    (req : PrimRequest) (h : I.Call req) :
    |((fusedValueBits I algorithm smp req : ℚ) : ℝ) - I.truth req| ≤ (req.n : ℝ) ^ (-(I.D : ℝ)) := by
  rw [fusedValueBits_eq]
  exact fused_error spectrum theta algorithm I smp hfe hG req h

end NearCubicWires.WireExponent3_5.FinalPass
