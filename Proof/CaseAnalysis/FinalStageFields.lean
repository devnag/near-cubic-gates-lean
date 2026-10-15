import Proof.CaseAnalysis.FinalSumFamilyTransport
import Proof.CaseAnalysis.FinalUnionSupplier
import Proof.CaseAnalysis.FinalStageFuelBound
import Proof.CaseAnalysis.FinalCallCountCap
import Proof.CaseAnalysis.FinalExactFraction

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10StageFields

open NearCubicWires
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.CloseoutWitness
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule (Phase)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10Exactness (CoordinateExpands phasePolynomial)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10SupplierAccuracy
open NearCubicWires.RepairOrdinary.CloseoutFinalC10SupplierCalls (CoefficientsFit siteCalls)
open NearCubicWires.RepairRepresentation
open NearCubicWires.RepairSource
open NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairSource.CloseoutFinal.C10SumFamilyTransport
open NearCubicWires.RepairSource.CloseoutFinal.C10SupplierAccuracyChain
open NearCubicWires.RepairSource.CloseoutFinal.C10SupplierWidth
open NearCubicWires.RepairSource.CloseoutFinal.C10StageFuelBound
open NearCubicWires.RepairSource.CloseoutFinal.C10TailComposeUniform
open NearCubicWires.RepairSource.CloseoutFinal.C10ThresholdWidths (thresholdWidth)
open NearCubicWires.RepairSource.CloseoutFinal.C10UnionSupplier
open NearCubicWires.RepairSource.CloseoutLanguage (selectedPCPP)
open NearCubicWires.RepairSource.CompetitorRationalGap
open NearCubicWires.RepairSource.SelectedRecoveryIntegration (outer)
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPipeline

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (sources : EightSources) (k : ℕ) {gamma : ℝ} (p : Parameters sources gamma)

def stageArity (n : ℕ) : ℕ :=
  max ((outer sources k (PolynomialClock.ordinaryClock k)).result.pcp.nativeWidth n)
    (selectedPCPP sources).minimumArity

/-! ## §2 The frozen limits, and the two witnesses of the accuracy ledger -/

/-- **The decoded family's limits, frozen.**  `symLimits`
(`Proof/CaseAnalysis/FinalTotalDecode.lean`) is
`CloseoutSampledWitness.symmetricLimits` (`Proof/CaseAnalysis/SampledWitness.lean`),
whose `coefficientMassCap` field is `massCap delta copies`
(`Proof/CaseAnalysis/WitnessAverage.lean`) at `delta := zeta (constantsOf sources)`
and `copies := p.copies`.  Neither depends on the input length, the input, or
the guessed oracle, so evaluating `symLimits` at a canonical point names that
one cap -- `symLimits_coefficientMassCap` below is the `rfl` that proves it.
`paper.tex:1405-1408` is the sentence: coefficient masses "are frozen before the
weak machine". -/
def stageMassCap : ℚ :=
  CloseoutSampledWitness.massCap (zeta (constantsOf sources)) p.copies

/-- **The coefficient-mass cap is the same at every length, input and oracle**,
and it is `massCap` (`Proof/CaseAnalysis/SampledWitness.lean`) at the two frozen
constants.  The guessed oracle enters `symLimits` only through the REQUEST, and
the request reaches no field but `expectedArity`. -/
theorem symLimits_coefficientMassCap {n : ℕ} (x : BitInput n)
    (oracle : BooleanCircuit
      ((outer sources k (PolynomialClock.ordinaryClock k)).result.pcp.nativeWidth n)) :
    (C10TotalDecode.symLimits sources k (PolynomialClock.ordinaryClock k) p x
        oracle).coefficientMassCap
      = stageMassCap sources p := rfl

/-- The frozen limits: the one cap above, carried by a `LegalSumLimits` that
depends on nothing else. -/
def stageLimits : CanonicalWitnessCodec.LegalSumLimits where
  expectedArity := 0
  termCap := 0
  coefficientBitCap := 0
  coefficientMassCap := stageMassCap sources p
  wireCap := 0
  descriptionCap := 0

/-- SUMFAM's `stageMass` (`Proof/CaseAnalysis/FinalSumFamilyTransport.lean`) IS
`massOf` (`Proof/CaseAnalysis/FinalSupplierAccuracyChain.lean`) at the frozen
limits.  This is the rider SUMFAM recorded: `haccuracy` has to be discharged at
`massBound`, not at an arbitrary mass, and this equation is what lets the
accuracy chain reach SUMFAM's own witness. -/
theorem stageMass_eq_massOf (n : ℕ) (x : BitInput n) (bits : List Bool) (ph : Phase) :
    stageMass sources k p n x bits ph
      = massOf (fun _ => stageLimits sources p) n x bits ph := by
  unfold stageMass massOf C10FamilyMass.massBound
  rw [symLimits_coefficientMassCap sources k p x
    (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)]
  rfl

theorem stageMass_eq_siteMassBound (n : ℕ) (x : BitInput n) (bits : List Bool) (ph : Phase) :
    stageMass sources k p n x bits ph
      = ((C10FamilyMass.siteMassBound (stageLimits sources p).coefficientMassCap ph : ℚ) : ℝ) := by
  rw [stageMass_eq_massOf sources k p n x bits ph]
  rfl

/-- **`S.failure`'s requested reciprocal accuracy**, the canonical choice of
`accuracyTarget_le_all` (`Proof/CaseAnalysis/FinalSupplierAccuracyChain.lean`):
one number per input length, independent of the length because the limits are
frozen. -/
def stageTarget : ℕ → ℕ :=
  fun _ => accuracyTargetAll (constantsOf sources) (stageLimits sources p)

def stageScale : ℕ → ℕ :=
  fun _ => Nat.size (accuracyTargetAll (constantsOf sources) (stageLimits sources p))

/-- **`S.failure`.** -/
def stageFailure : (n : ℕ) → BitInput n → List Bool → Phase → ℝ :=
  failureOf (stageTarget sources p) (stageArity sources k) (stageScale sources p)

/-- **`S.entryWidth`**, at S-W's three floors. -/
def stageEntryWidth (coefficientFloor : ℕ → ℕ) : ℕ → ℕ :=
  entryWidth coefficientFloor (stageArity sources k) (stageScale sources p) (constantsOf sources)

/-! ## §3 The three record-shape-independent semantic fields

These are SUMFAM's, at the field's verbatim type.  They are restated here (as
terms, not reproofs) so the assembly has one module to `refine` from. -/

/-- **`StageBlock.hcoordinate`** (`Proof/CaseAnalysis/FinalStageContracts.lean`)
at `S.coordinate := stageCoordinate sources k p`. -/
theorem stage_field_hcoordinate :
    ∀ (n : ℕ) (x : BitInput n) (bits : List Bool),
      Soundness.cutoff (constantsOf sources) ≤ n →
      CoordinateExpands (pcppOf sources k p x bits) C10TotalDecode.evaluate
        (proofOf sources k p x bits) (stageCoordinate sources k p n x bits) :=
  stage_hcoordinate sources k p

theorem stage_field_hcoefficients (coefficientFloor : ℕ → ℕ)
    (hfloor : ∀ (n : ℕ) (x : BitInput n) (w : List Bool),
      C10SiteCoefficientsFit.coefficientBound
        (C10TotalDecode.symLimits sources k (PolynomialClock.ordinaryClock k) p x
          (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n w))
        (pcppOf sources k p x w) ≤ coefficientFloor n) :
    ∀ (n : ℕ) (x : BitInput n) (bits : List Bool),
      Soundness.cutoff (constantsOf sources) ≤ n →
      ∀ (ph : Phase) (address : Fin (2 ^ (pcppOf sources k p x bits).clauseBits)),
        CoefficientsFit (stageEntryWidth sources k p coefficientFloor n)
          (siteCalls ph (pcppOf sources k p x bits) (stageCoordinate sources k p n x bits)
            C10TotalDecode.Atom.systematic address) :=
  stage_hcoefficients sources k p (stageEntryWidth sources k p coefficientFloor)
    (fun n x w => (hfloor n x w).trans
      (le_trans (le_max_left _ _) (le_max_left _ _)))

/-- **`StageBlock.hmass`** (`Proof/CaseAnalysis/FinalStageContracts.lean`) at
`S.coordinate := stageCoordinate sources k p`, `S.mass := stageMass sources k p`. -/
theorem stage_field_hmass :
    ∀ (n : ℕ) (x : BitInput n) (bits : List Bool),
      Soundness.cutoff (constantsOf sources) ≤ n →
      ∀ ph : Phase,
        (((phasePolynomial ph (pcppOf sources k p x bits) (stageCoordinate sources k p n x bits)
            C10TotalDecode.Atom.systematic).coefficientMass : ℚ) : ℝ)
          ≤ stageMass sources k p n x bits ph :=
  stage_hmass sources k p

/-! ## §4 The width and accuracy fields -- all four unconditional -/

theorem stage_field_he (S : StageData sources k p) (extra : ℕ) (hextra : S.e = 60 + extra) :
    58 ≤ S.e := by omega

/-- **`StageBlock.hthreshold`** (`Proof/CaseAnalysis/FinalStageContracts.lean`).
S-W's second floor, read straight off the `max`; no hypothesis. -/
theorem stage_field_hthreshold (coefficientFloor : ℕ → ℕ) :
    ∀ n, thresholdWidth (constantsOf sources)
      ≤ stageEntryWidth sources k p coefficientFloor n :=
  fun _ => le_trans (le_max_right _ _) (le_max_left _ _)

/-- **`StageBlock.hfailure`** (`Proof/CaseAnalysis/FinalStageContracts.lean`).
The paper's per-call error is a sum of reciprocals; it is nonnegative because it
is one. -/
theorem stage_field_hfailure :
    ∀ (n : ℕ) (x : BitInput n) (bits : List Bool),
      Soundness.cutoff (constantsOf sources) ≤ n →
      ∀ ph : Phase, 0 ≤ stageFailure sources k p n x bits ph :=
  fun n x bits _ ph =>
    failureOf_nonneg (stageTarget sources p) (stageArity sources k) (stageScale sources p)
      n x bits ph

/-- **`StageBlock.haccuracy`** (`Proof/CaseAnalysis/FinalStageContracts.lean`),
UNCONDITIONAL at the frozen limits, i.e. `paper.tex:3555-3557`'s product landing
inside `estimationTolerance`.  Discharged AT `massBound`, per SUMFAM's rider,
through `stageMass_eq_massOf`. -/
theorem stage_field_haccuracy :
    ∀ (n : ℕ) (x : BitInput n) (bits : List Bool),
      Soundness.cutoff (constantsOf sources) ≤ n →
      ∀ ph : Phase,
        stageFailure sources k p n x bits ph * stageMass sources k p n x bits ph
          ≤ ((estimationTolerance (constantsOf sources) (zeta (constantsOf sources)) : ℚ) : ℝ) := by
  intro n x bits _ ph
  rw [stageMass_eq_massOf]
  exact haccuracy_at_frozen_limits (constantsOf sources) (stageLimits sources p)
    (stageArity sources k) n x bits ph

/-! ## §5 The SCALAR-denominator supplier fields -- `StageBlock` as it stands -/

/-- **`S.supplier`** at the decode-union rows and S-W's uniform denominator. -/
def stageSupplier (liveScale : ℕ) :
    (n : ℕ) → (x : BitInput n) → (bits : List Bool) → List (Atoms sources k p x bits) → ℚ :=
  fun n _ _ atoms =>
    unionSupplier (unionAtomRows sources liveScale (stageTarget sources p))
      (stageArity sources k n) (stageScale sources p n) atoms

/-- **`S.answer`** at the same rows. -/
def stageAnswer (liveScale : ℕ) :
    (n : ℕ) → (x : BitInput n) → (bits : List Bool) → List (Atoms sources k p x bits) → ℕ :=
  fun n _ _ atoms =>
    unionAnswer (unionAtomRows sources liveScale (stageTarget sources p))
      (stageArity sources k n) (stageScale sources p n) atoms

/-- **`S.denominator`**. -/
def stageDenominator : ℕ → ℕ :=
  fun n => denominator (stageArity sources k n) (stageScale sources p n)

/-- **`StageBlock.hsupplier`** (`Proof/CaseAnalysis/FinalStageContracts.lean`). -/
theorem stage_field_hsupplier (liveScale : ℕ) :
    ∀ (n : ℕ) (x : BitInput n) (bits : List Bool),
      Soundness.cutoff (constantsOf sources) ≤ n →
      ∀ atoms : List (Atoms sources k p x bits),
        (stageAnswer sources k p liveScale n x bits atoms : ℚ)
            / (stageDenominator sources k p n : ℚ)
          = stageSupplier sources k p liveScale n x bits atoms :=
  fun n _ _ _ atoms =>
    unionSupplier_eq (unionAtomRows sources liveScale (stageTarget sources p))
      (stageArity sources k n) (stageScale sources p n) atoms

/-- **`StageBlock.hcount`** (`Proof/CaseAnalysis/FinalStageContracts.lean`). -/
theorem stage_field_hcount (liveScale : ℕ) (coefficientFloor : ℕ → ℕ) :
    ∀ (n : ℕ) (x : BitInput n) (bits : List Bool),
      Soundness.cutoff (constantsOf sources) ≤ n →
      ∀ atoms : List (Atoms sources k p x bits),
        stageAnswer sources k p liveScale n x bits atoms
          < 2 ^ stageEntryWidth sources k p coefficientFloor n :=
  fun n _ _ _ atoms =>
    unionAnswer_lt (unionAtomRows sources liveScale (stageTarget sources p)) coefficientFloor
      (stageArity sources k) (stageScale sources p) (constantsOf sources) n atoms

/-- **`StageBlock.hdenominator`** (`Proof/CaseAnalysis/FinalStageContracts.lean`). -/
theorem stage_field_hdenominator (coefficientFloor : ℕ → ℕ) :
    ∀ n, Soundness.cutoff (constantsOf sources) ≤ n →
      stageDenominator sources k p n < 2 ^ stageEntryWidth sources k p coefficientFloor n :=
  fun n _ =>
    denominator_lt coefficientFloor (stageArity sources k) (stageScale sources p)
      (constantsOf sources) n

/-- **`StageBlock.hdenominatorPositive`**
(`Proof/CaseAnalysis/FinalStageContracts.lean`). -/
theorem stage_field_hdenominatorPositive :
    ∀ n, Soundness.cutoff (constantsOf sources) ≤ n → 0 < stageDenominator sources k p n :=
  fun n _ => denominator_pos (stageArity sources k n) (stageScale sources p n)

/-- **`StageBlock.hpoint`** (`Proof/CaseAnalysis/FinalStageContracts.lean`) at
the scalar supplier.  **CAPONE's rider is visible in the statement**: `atoms`
ranges over ALL lists of `Atoms sources k p x bits`, with no wire bound
anywhere, and `C10TotalDecode.Atom` (`Proof/CaseAnalysis/FinalTotalDecode.lean`)
carries whole competitor circuits, so this obligation is already strictly
stronger than any per-atom wire envelope and lowering `symCap` cannot relax it. -/
theorem stage_field_hpoint (liveScale : ℕ) :
    ∀ (n : ℕ) (x : BitInput n) (bits : List Bool),
      Soundness.cutoff (constantsOf sources) ≤ n →
      ∀ (ph : Phase) (atoms : List (Atoms sources k p x bits)),
        |((stageSupplier sources k p liveScale n x bits atoms : ℚ) : ℝ)
            - conjunctionProbability C10TotalDecode.evaluate atoms|
          ≤ stageFailure sources k p n x bits ph :=
  fun n x bits _ ph atoms =>
    hpoint_of_unionAtomRows sources liveScale (stageTarget sources p) (stageArity sources k)
      (stageScale sources p) n x bits ph atoms

/-! ## §6 The EXACT-FRACTION supplier fields -- the four shapes EXACTFRAC pinned -/

/-- **`num`** (EXACTFRAC's `hnum` slot): A.13.9's own numerator
`\sum_e\sum_z T_{e,F(z)}(z)`, per call, with no rescaling. -/
def stageNum (liveScale : ℕ) :
    (n : ℕ) → (x : BitInput n) → (bits : List Bool) →
      Fin (2 ^ (pcppOf sources k p x bits).clauseBits) →
      CircuitMonomial (Atoms sources k p x bits) 4 → ℕ :=
  fun n _ _ _ monomial =>
    rowAnswer (unionAtomRows sources liveScale (stageTarget sources p))
      (stageArity sources k n) (monomial.factors.map atomToUnion)

/-- **`den`**: A.13.9's own `|\mathcal E|2^q` (`paper.tex:3161`), per call. -/
def stageDen (liveScale : ℕ) :
    (n : ℕ) → (x : BitInput n) → (bits : List Bool) →
      Fin (2 ^ (pcppOf sources k p x bits).clauseBits) →
      CircuitMonomial (Atoms sources k p x bits) 4 → ℕ :=
  fun n _ _ _ monomial =>
    rowDenominator (unionAtomRows sources liveScale (stageTarget sources p))
      (stageArity sources k n) (monomial.factors.map atomToUnion)

/-- **`S.supplier` on the exact route**: the rows' own rational output, NOT the
rescaled `unionSupplier` of §5. -/
def stageRowSupplier (liveScale : ℕ) :
    (n : ℕ) → (x : BitInput n) → (bits : List Bool) → List (Atoms sources k p x bits) → ℚ :=
  fun n _ _ atoms =>
    rowSupplier (unionAtomRows sources liveScale (stageTarget sources p))
      (stageArity sources k n) (atoms.map atomToUnion)

/-- **`hratio`** (`Proof/CaseAnalysis/FinalExactFraction.lean`).
Unconditional: `rowSupplier_eq_ratio`
(`Proof/CaseAnalysis/FinalSupplierAccuracy.lean`) is an identity, not a bound.
No divisibility, no common scale, no rounding. -/
theorem stage_field_hratio (liveScale : ℕ) :
    ∀ (n : ℕ) (x : BitInput n) (bits : List Bool),
      Soundness.cutoff (constantsOf sources) ≤ n →
      ∀ (address : Fin (2 ^ (pcppOf sources k p x bits).clauseBits))
        (monomial : CircuitMonomial (Atoms sources k p x bits) 4),
        ((stageNum sources k p liveScale n x bits address monomial : ℚ)
            / (stageDen sources k p liveScale n x bits address monomial : ℚ))
          = stageRowSupplier sources k p liveScale n x bits monomial.factors :=
  fun n _ _ _ _ monomial =>
    rowSupplier_eq_ratio (unionAtomRows sources liveScale (stageTarget sources p))
      (stageArity sources k n) (monomial.factors.map atomToUnion)

/-- **`hdenPos`** (`Proof/CaseAnalysis/FinalExactFraction.lean`).
Unconditional: `rowCountPositive` times `2 ^ q`. -/
theorem stage_field_hdenPos (liveScale : ℕ) :
    ∀ (n : ℕ) (x : BitInput n) (bits : List Bool),
      Soundness.cutoff (constantsOf sources) ≤ n →
      ∀ (address : Fin (2 ^ (pcppOf sources k p x bits).clauseBits))
        (monomial : CircuitMonomial (Atoms sources k p x bits) 4),
        0 < stageDen sources k p liveScale n x bits address monomial :=
  fun n _ _ _ _ monomial =>
    rowDenominator_pos (unionAtomRows sources liveScale (stageTarget sources p))
      (stageArity sources k n) (monomial.factors.map atomToUnion)

theorem stage_field_hden (liveScale : ℕ) (coefficientFloor seedBound : ℕ → ℕ)
    (hseed : ∀ (n : ℕ) (circuits : List (DecodeUnion (stageArity sources k n))),
      (unionAtomRows sources liveScale (stageTarget sources p)).rowCount
          ⟨stageArity sources k n, circuits⟩ ≤ 2 ^ seedBound n)
    (hfloor : ∀ n, stageArity sources k n + seedBound n + 1
      ≤ stageEntryWidth sources k p coefficientFloor n) :
    ∀ (n : ℕ) (x : BitInput n) (bits : List Bool),
      Soundness.cutoff (constantsOf sources) ≤ n →
      ∀ (address : Fin (2 ^ (pcppOf sources k p x bits).clauseBits))
        (monomial : CircuitMonomial (Atoms sources k p x bits) 4),
        stageDen sources k p liveScale n x bits address monomial
          < 2 ^ stageEntryWidth sources k p coefficientFloor n := by
  intro n x bits _ address monomial
  have hrow := hseed n (monomial.factors.map atomToUnion)
  have hle : stageDen sources k p liveScale n x bits address monomial
      ≤ 2 ^ seedBound n * 2 ^ stageArity sources k n :=
    Nat.mul_le_mul_right _ hrow
  have hmul : 2 ^ seedBound n * 2 ^ stageArity sources k n
      = 2 ^ (stageArity sources k n + seedBound n) := by
    rw [pow_add, Nat.mul_comm]
  have hstep : 2 ^ seedBound n * 2 ^ stageArity sources k n
      < 2 ^ stageEntryWidth sources k p coefficientFloor n := by
    rw [hmul]
    exact Nat.pow_lt_pow_right (by norm_num)
      (lt_of_lt_of_le (Nat.lt_succ_self _) (hfloor n))
  exact lt_of_le_of_lt hle hstep

/-- **`hnum`** (`Proof/CaseAnalysis/FinalExactFraction.lean`) is FREE once
`hden` holds: the acceptance count never exceeds the sample count
(`rowAnswer_le_rowDenominator`,
`Proof/CaseAnalysis/FinalSupplierWidth.lean`).  So the exact route's four
premises reduce to ONE open quantity, `hden`. -/
theorem stage_field_hnum (liveScale : ℕ) (coefficientFloor : ℕ → ℕ)
    (hden : ∀ (n : ℕ) (x : BitInput n) (bits : List Bool),
      Soundness.cutoff (constantsOf sources) ≤ n →
      ∀ (address : Fin (2 ^ (pcppOf sources k p x bits).clauseBits))
        (monomial : CircuitMonomial (Atoms sources k p x bits) 4),
        stageDen sources k p liveScale n x bits address monomial
          < 2 ^ stageEntryWidth sources k p coefficientFloor n) :
    ∀ (n : ℕ) (x : BitInput n) (bits : List Bool),
      Soundness.cutoff (constantsOf sources) ≤ n →
      ∀ (address : Fin (2 ^ (pcppOf sources k p x bits).clauseBits))
        (monomial : CircuitMonomial (Atoms sources k p x bits) 4),
        stageNum sources k p liveScale n x bits address monomial
          < 2 ^ stageEntryWidth sources k p coefficientFloor n :=
  fun n x bits hn address monomial =>
    lt_of_le_of_lt
      (rowAnswer_le_rowDenominator (unionAtomRows sources liveScale (stageTarget sources p))
        (stageArity sources k n) (monomial.factors.map atomToUnion))
      (hden n x bits hn address monomial)

/-- **`StageBlock.hpoint` at the EXACT supplier**, which is a DIFFERENT
instantiation from §5: the landed producer `hpoint_of_unionAtomRows`
(`Proof/CaseAnalysis/FinalUnionSupplier.lean`) is stated at `unionSupplier`,
the rescaled scalar answer, so it does not serve the exact route.  Here the
error is paid at the rows' own failure with NO ulp term -- EXACTFRAC's point 4,
compiled. -/
theorem stage_field_hpoint_row (liveScale : ℕ) :
    ∀ (n : ℕ) (x : BitInput n) (bits : List Bool),
      Soundness.cutoff (constantsOf sources) ≤ n →
      ∀ atoms : List (Atoms sources k p x bits),
        |((stageRowSupplier sources k p liveScale n x bits atoms : ℚ) : ℝ)
            - conjunctionProbability C10TotalDecode.evaluate atoms|
          ≤ 1 / ((stageTarget sources p (stageArity sources k n) + 1 : ℕ) : ℝ) := by
  intro n x bits _ atoms
  rw [← conjunctionProbability_atomToUnion atoms]
  exact (rowSupplier_error_le (unionAtomRows sources liveScale (stageTarget sources p))
      (stageArity sources k n) (atoms.map atomToUnion)).trans
    (unionAtomRows_failure_le sources liveScale (stageTarget sources p)
      ⟨stageArity sources k n, atoms.map atomToUnion⟩)

/-- **`StageBlock.haccuracy` at the exact route's tighter failure.**  One term
has left the budget, so the product clears `estimationTolerance` with a factor
of two to spare. -/
theorem stage_field_haccuracy_row :
    ∀ (n : ℕ) (x : BitInput n) (bits : List Bool),
      Soundness.cutoff (constantsOf sources) ≤ n →
      ∀ ph : Phase,
        1 / ((stageTarget sources p (stageArity sources k n) + 1 : ℕ) : ℝ)
            * stageMass sources k p n x bits ph
          ≤ ((estimationTolerance (constantsOf sources) (zeta (constantsOf sources)) : ℚ) : ℝ) := by
  intro n x bits _ ph
  have hpos : (0 : ℝ)
      < ((estimationTolerance (constantsOf sources) (zeta (constantsOf sources)) : ℚ) : ℝ) := by
    exact_mod_cast (full_error_budget (constantsOf sources)).1
  have hspec := accuracyTarget_spec (constantsOf sources) (stageLimits sources p) ph
    (stageTarget sources p (stageArity sources k n) + 1)
    (le_trans (accuracyTarget_le_all (constantsOf sources) (stageLimits sources p) ph)
      (Nat.le_succ _))
  rw [stageMass_eq_siteMassBound]
  have hhalf := recip_mul_le_half hpos
    (by positivity : (0 : ℝ) ≤ ((stageTarget sources p (stageArity sources k n) + 1 : ℕ) : ℝ))
    hspec
  linarith

/-! ## §7 `hfuel` -- the criterion, and the call cap that feeds it -/

/-- **`StageBlock.hfuel`** (`Proof/CaseAnalysis/FinalStageContracts.lean`) from
a call-count cap.  `fuel_bounded_iff`
(`Proof/CaseAnalysis/FinalStageFuelBound.lean`) is an IFF at one length and one
input; this is its uniform half, at the shape the field asks for.  `hfuel` is
the one field with no `Soundness.cutoff` guard, and HFUEL's verdict stands:
nothing in `actualFuel` truncates, so the only obligation is the cap. -/
theorem stage_field_hfuel (S : StageData sources k p) (K : ℕ → ℕ)
    (hK : ∀ (n : ℕ) (x : BitInput n) (bits : List Bool) (ph : Phase),
      (records sources k p S x bits ph).length ≤ K n)
    (hbudget : ∀ n, fuelAt sources k p S n (fun _ => K n) ≤ S.budget n) :
    ∀ (n : ℕ) (x : BitInput n) (bits : List Bool),
      actualFuel sources k p S x bits ≤ S.budget n := by
  intro n x bits
  rw [actualFuel_eq sources k p S x bits]
  exact (fuelAt_mono sources k p S n (fun ph => hK n x bits ph)).trans (hbudget n)

/-- The cap `hK` asks for, from the coordinate degree alone.  `phaseRecords_length_le`
(`Proof/CaseAnalysis/FinalCallCountCap.lean`) is generic in the record
function, so it is blind to which of §5 / §6 supplies `S.answer`. -/
theorem stage_records_length_le (S : StageData sources k p) (L : ℕ → ℕ)
    (hL : ∀ (n : ℕ) (x : BitInput n) (bits : List Bool) j,
      ((S.coordinate n x bits) j).monomials.length ≤ L n)
    (n : ℕ) (x : BitInput n) (bits : List Bool) (ph : Phase) :
    (records sources k p S x bits ph).length
      ≤ 2 ^ (pcppOf sources k p x bits).clauseBits
        * CloseoutFinalC10CallCountCap.siteCap (L n) :=
  CloseoutFinalC10CallCountCap.phaseRecords_length_le (L n) _ (pcppOf sources k p x bits)
    (S.answer n x bits) (S.denominator n) ph (S.coordinate n x bits)
    C10TotalDecode.Atom.systematic (hL n x bits)

end

end NearCubicWires.RepairOrdinary.CloseoutFinalC10StageFields
