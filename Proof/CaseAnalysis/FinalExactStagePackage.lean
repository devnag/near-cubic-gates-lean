import Proof.CaseAnalysis.FinalCompletion
import Proof.CaseAnalysis.FinalStageFields

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10ExactStagePackage

open NearCubicWires
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.CloseoutWitness
open NearCubicWires.RepairOrdinary.CloseoutFinalC10Exactness
open NearCubicWires.RepairOrdinary.CloseoutFinalC10ExactFractionRecords
open NearCubicWires.RepairOrdinary.CloseoutFinalC10StageFields
open NearCubicWires.RepairSource.CloseoutFinal.C10StageFuelBound (fuelAt actualFuel_eq
  fuelAt_mono)
open NearCubicWires.RepairSource.CloseoutFinal.C10SumFamilyTransport (stageCoordinate
  stageMass)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10Realizes
open NearCubicWires.RepairOrdinary.CloseoutFinalC10StageSeam
open NearCubicWires.RepairOrdinary.CloseoutFinalC10SupplierCalls
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerChain
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDock
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDockSeam
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerEmitLoader
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerEmitShape
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerFold
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream (Entry contributions)
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule
open NearCubicWires.RepairRepresentation
open NearCubicWires.RepairSource.CloseoutFinal.C10BodyWidths
open NearCubicWires.RepairSource.CloseoutFinal.C10LengthGate
open NearCubicWires.RepairSource.CloseoutFinal.C10TailCompose
open NearCubicWires.RepairSource.CloseoutFinal.C10TailComposeUniform
open NearCubicWires.RepairSource.CloseoutFinal.C10TailComposeVerdict
open NearCubicWires.RepairSource.CloseoutFinal.C10TotalDecode
open NearCubicWires.RepairSource.CloseoutFinal.C10Verdict
open NearCubicWires.RepairSource.CompetitorRationalGap
open NearCubicWires.RepairSource
open NearCubicWires.RepairSource.CloseoutFinal (constantsOf Parameters Runtime Theorem25Target
  theorem25_of_leaves)
open NearCubicWires.RepairOrdinary.CompetitorSourceAverage
open NearCubicWires.RepairSource.CloseoutLanguage
open NearCubicWires.RepairSource.SelectedRecoveryIntegration
open NearCubicWires.RepairSource.CloseoutFinal.C10DecidesUniform
open NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.CircuitRestriction
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.AggregateSemanticStage
open NearCubicWires.RepairSource.CloseoutFinal.C10Fusion (Pipeline)
open NearCubicWires.RepairSource.CloseoutFinal.C10ComposeWidths
open NearCubicWires.RepairSource.CloseoutFinal.C10StageWidths
open NearCubicWires.RepairSource.CloseoutFinal.C10TailVerdictUniform (tbud tailWidths'_of)
open NearCubicWires.RepairSource.CloseoutFinal.C10ThresholdWidths (thresholdWidth)
open NearCubicWires.RepairSource.CloseoutFinal.C10SupplierWidth (rowAnswer_le_rowDenominator)
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierPipeline

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (sources : EightSources) (k : ℕ)

attribute [local irreducible] pcppOf Atoms

/-- **The stage's data at the paper's own per-call fraction.**  Field for field
`StageData` (`Proof/CaseAnalysis/FinalStageContracts.lean`), except that the pair
`answer : ... → List Atom → ℕ` (`:79`) and `denominator : ℕ → ℕ` (`:74`) is replaced
by the numerator/denominator pair `exactFractionRecord`
(`Proof/CaseAnalysis/FinalExactFraction.lean`) consumes: one pair per PCPP
clause address and monomial.  `den` is A.13.9's `|\mathcal E| 2 ^ q`
(`paper.tex:3161`), i.e. `rowDenominator`
(`Proof/CaseAnalysis/FinalSupplierAccuracy.lean`), which is a function of the
request and therefore cannot be a `ℕ → ℕ`. -/
structure StageData' {gamma : ℝ} (p : Parameters sources gamma) :
    Type 1 where
  e : ℕ
  st : Phase → ℕ
  stage : (ph : Phase) → LocalBitMultitape.Machine (218+e) (st ph)
  stageFuel : Phase → ℕ → ℕ
  entryWidth : ℕ → ℕ
  num : (n : ℕ) → (x : BitInput n) → (bits : List Bool) →
    Fin (2 ^ (pcppOf sources k p x bits).clauseBits) →
      CircuitMonomial (Atoms sources k p x bits) 4 → ℕ
  den : (n : ℕ) → (x : BitInput n) → (bits : List Bool) →
    Fin (2 ^ (pcppOf sources k p x bits).clauseBits) →
      CircuitMonomial (Atoms sources k p x bits) 4 → ℕ
  coordinate : (n : ℕ) → (x : BitInput n) → (bits : List Bool) →
    Fin ((pcppOf sources k p x bits).systematicBits+(pcppOf sources k p x bits).auxiliaryBits) →
      CircuitPolynomial (Atoms sources k p x bits) 1
  supplier : (n : ℕ) → (x : BitInput n) → (bits : List Bool) → List (Atoms sources k p x bits) → ℚ
  failure : (n : ℕ) → BitInput n → List Bool → Phase → ℝ
  mass : (n : ℕ) → BitInput n → List Bool → Phase → ℝ
  L : ℕ → ℕ
  budget : ℕ → ℕ

attribute [local semireducible] pcppOf Atoms

variable {gamma : ℝ} (p : Parameters sources gamma)
  (S : StageData' sources k p)

/-- The emitted record stream, at A.13.9's own fraction.  `records`
(`Proof/CaseAnalysis/FinalStageContracts.lean`) with `phaseRecords` replaced by
`phaseRecords'` (`Proof/CaseAnalysis/FinalExactFraction.lean`). -/
abbrev records' {n : ℕ} (x : BitInput n) (bits : List Bool) (ph : Phase) :=
  phaseRecords' ph (pcppOf sources k p x bits) (S.coordinate n x bits) Atom.systematic
    (exactFractionRecord (2 ^ (pcppOf sources k p x bits).clauseBits) (S.num n x bits)
      (S.den n x bits))

/-- `widthOf` (`Proof/CaseAnalysis/FinalStageContracts.lean`) at `records'`. -/
def widthOf' {n : ℕ} (x : BitInput n) (bits : List Bool) (ph : Phase) :=
  foldWidth (CompetitorRationalDecision.width (S.entryWidth n))
    (records' sources k p S x bits ph)

/-- `emissionFuel` (`Proof/CaseAnalysis/FinalStageContracts.lean`) at `records'`. -/
def emissionFuel' {n : ℕ} (x : BitInput n) (bits : List Bool) (ph : Phase) : ℕ → ℕ :=
  fun _ => emitFuel (joinScalarWidth (S.entryWidth n) (records' sources k p S x bits ph).length)

/-- `body` (`Proof/CaseAnalysis/FinalStageContracts.lean`), unchanged in kind. -/
def body' (ph : Phase) := stagedBody (S.stage ph) emitLoader

/-- `phaseFuel` (`Proof/CaseAnalysis/FinalStageContracts.lean`) at `records'`. -/
def phaseFuel' {n : ℕ} (x : BitInput n) (bits : List Bool) (ph : Phase) : ℕ :=
  stagedFuel (S.stageFuel ph) (emissionFuel' sources k p S x bits ph) (S.entryWidth n)
    (records' sources k p S x bits ph).length n

/-- `actualFuel` (`Proof/CaseAnalysis/FinalStageContracts.lean`) at `records'`. -/
def actualFuel' {n : ℕ} (x : BitInput n) (bits : List Bool) : ℕ :=
  workerBudget (Soundness.cutoff (constantsOf sources))
    (fun _ => innerFuel (phaseFuel' sources k p S x bits)
      (widthOf' sources k p S x bits) tbud) n

structure StageReady' (he : 58 ≤ S.e) {n : ℕ} (x : BitInput n) (bits : List Bool) (ph : Phase)
    (bank : Fin 218 → List Bool) (scratch : Fin S.e → List Bool) : Prop where
  hstage : Step (S.stage ph) (S.stageFuel ph n) (fun _ => 0)
    (exitTapes (Fin.castAdd S.e flag)
      ((UAcceptanceCarrier.verifier
        (worker (Soundness.cutoff (constantsOf sources)) (Fin.castAdd S.e inputTape)
          (Fin.castAdd S.e flag) (Fin.castAdd S.e result) (body' sources k p S ph))
        (by omega) (Fin.castAdd S.e result)).inputTapes (List.ofFn x) bits) 0 true)
    (fun _ => 0) (Fin.addCases bank scratch)
  hready : DockReady (S.entryWidth n) (records' sources k p S x bits ph) bank
  hentry : EmitEntry (joinScalarWidth (S.entryWidth n)
    (records' sources k p S x bits ph).length) bank
  h0 : bank 0 = frame (List.ofFn x)
  h1 : bank 1 = frame bits
  hemit : emissionFuel' sources k p S x bits ph =
    fun _ => emitFuel (joinScalarWidth (S.entryWidth n) (records' sources k p S x bits ph).length)
  hwidth : ∀ j, Fin.addCases bank scratch (retained S.e he j) =
    widthWord (widthOf' sources k p S x bits ph) j

structure StageBlock' : Prop where
  he : 58 ≤ S.e
  hstage : ∀ (n : ℕ) (x : BitInput n) (bits : List Bool),
    Soundness.cutoff (constantsOf sources) ≤ n →
    ∀ ph, ∃ bank scratch, StageReady' sources k p S he x bits ph bank scratch
  hcoordinate : ∀ (n : ℕ) (x : BitInput n) (bits : List Bool),
    Soundness.cutoff (constantsOf sources) ≤ n →
    CoordinateExpands (pcppOf sources k p x bits) evaluate (proofOf sources k p x bits)
      (S.coordinate n x bits)
  hratio : ∀ (n : ℕ) (x : BitInput n) (bits : List Bool),
    Soundness.cutoff (constantsOf sources) ≤ n →
    ∀ address monomial, ((S.num n x bits address monomial : ℚ) /
      (S.den n x bits address monomial : ℚ)) = S.supplier n x bits monomial.factors
  hnum : ∀ (n : ℕ) (x : BitInput n) (bits : List Bool),
    Soundness.cutoff (constantsOf sources) ≤ n →
    ∀ ph address monomial,
      monomial ∈ (siteCalls ph (pcppOf sources k p x bits)
        (S.coordinate n x bits) Atom.systematic address).monomials →
      S.num n x bits address monomial < 2^(S.entryWidth n)
  hden : ∀ (n : ℕ) (x : BitInput n) (bits : List Bool),
    Soundness.cutoff (constantsOf sources) ≤ n →
    ∀ ph address monomial,
      monomial ∈ (siteCalls ph (pcppOf sources k p x bits)
        (S.coordinate n x bits) Atom.systematic address).monomials →
      S.den n x bits address monomial < 2^(S.entryWidth n)
  hdenPos : ∀ (n : ℕ) (x : BitInput n) (bits : List Bool),
    Soundness.cutoff (constantsOf sources) ≤ n →
    ∀ address monomial, 0 < S.den n x bits address monomial
  hcoefficients : ∀ (n : ℕ) (x : BitInput n) (bits : List Bool),
    Soundness.cutoff (constantsOf sources) ≤ n →
    ∀ ph address, CoefficientsFit (S.entryWidth n)
      (siteCalls ph (pcppOf sources k p x bits) (S.coordinate n x bits) Atom.systematic address)
  hfailure : ∀ (n : ℕ) (x : BitInput n) (bits : List Bool),
    Soundness.cutoff (constantsOf sources) ≤ n → ∀ ph, 0 ≤ S.failure n x bits ph
  hpoint : ∀ (n : ℕ) (x : BitInput n) (bits : List Bool),
    Soundness.cutoff (constantsOf sources) ≤ n →
    ∀ ph circuits, |((S.supplier n x bits circuits : ℚ) : ℝ) -
      conjunctionProbability evaluate circuits| ≤ S.failure n x bits ph
  hmass : ∀ (n : ℕ) (x : BitInput n) (bits : List Bool),
    Soundness.cutoff (constantsOf sources) ≤ n →
    ∀ ph, (((phasePolynomial ph (pcppOf sources k p x bits) (S.coordinate n x bits)
      Atom.systematic).coefficientMass : ℚ) : ℝ) ≤ S.mass n x bits ph
  haccuracy : ∀ (n : ℕ) (x : BitInput n) (bits : List Bool),
    Soundness.cutoff (constantsOf sources) ≤ n →
    ∀ ph, S.failure n x bits ph * S.mass n x bits ph ≤
      ((estimationTolerance (constantsOf sources) (zeta (constantsOf sources)) : ℚ) : ℝ)
  hthreshold : ∀ n, thresholdWidth (constantsOf sources) ≤ S.entryWidth n
  hfuel : ∀ (n : ℕ) (x : BitInput n) (bits : List Bool),
    actualFuel' sources k p S x bits ≤ S.budget n

def ofScalar (T : StageData sources k p) : StageData' sources k p where
  e := T.e
  st := T.st
  stage := T.stage
  stageFuel := T.stageFuel
  entryWidth := T.entryWidth
  num := fun n x bits _ monomial => T.answer n x bits monomial.factors
  den := fun n _ _ _ _ => T.denominator n
  coordinate := T.coordinate
  supplier := T.supplier
  failure := T.failure
  mass := T.mass
  L := T.L
  budget := T.budget

theorem records'_ofScalar (T : StageData sources k p) {n : ℕ} (x : BitInput n)
    (bits : List Bool) (ph : Phase) :
    records' sources k p (ofScalar sources k p T) x bits ph
      = records sources k p T x bits ph := rfl

/-- `widthOf` (`Proof/CaseAnalysis/FinalStageContracts.lean`) is `widthOf'` there. -/
theorem widthOf'_ofScalar (T : StageData sources k p) {n : ℕ} (x : BitInput n)
    (bits : List Bool) (ph : Phase) :
    widthOf' sources k p (ofScalar sources k p T) x bits ph
      = widthOf sources k p T x bits ph := rfl

/-- `emissionFuel` (`Proof/CaseAnalysis/FinalStageContracts.lean`) is `emissionFuel'`. -/
theorem emissionFuel'_ofScalar (T : StageData sources k p) {n : ℕ} (x : BitInput n)
    (bits : List Bool) (ph : Phase) :
    emissionFuel' sources k p (ofScalar sources k p T) x bits ph
      = emissionFuel sources k p T x bits ph := rfl

/-- `body` (`Proof/CaseAnalysis/FinalStageContracts.lean`) is `body'`. -/
theorem body'_ofScalar (T : StageData sources k p) (ph : Phase) :
    body' sources k p (ofScalar sources k p T) ph = body sources k p T ph := rfl

/-- `phaseFuel` (`Proof/CaseAnalysis/FinalStageContracts.lean`) is `phaseFuel'`. -/
theorem phaseFuel'_ofScalar (T : StageData sources k p) {n : ℕ} (x : BitInput n)
    (bits : List Bool) (ph : Phase) :
    phaseFuel' sources k p (ofScalar sources k p T) x bits ph
      = phaseFuel sources k p T x bits ph := rfl

theorem actualFuel'_ofScalar (T : StageData sources k p) {n : ℕ} (x : BitInput n)
    (bits : List Bool) :
    actualFuel' sources k p (ofScalar sources k p T) x bits
      = actualFuel sources k p T x bits := rfl

/-- **`StageReady` (`Proof/CaseAnalysis/FinalStageContracts.lean`) IS `StageReady'`
at `ofScalar`**, field for field: every component is `rfl`-equal by the six identities
above, so both directions are the anonymous constructor. -/
theorem stageReady'_iff (T : StageData sources k p) (he : 58 ≤ T.e) {n : ℕ}
    (x : BitInput n) (bits : List Bool) (ph : Phase) (bank : Fin 218 → List Bool)
    (scratch : Fin T.e → List Bool) :
    StageReady' sources k p (ofScalar sources k p T) he x bits ph bank scratch
      ↔ StageReady sources k p T he x bits ph bank scratch :=
  ⟨fun h => ⟨h.hstage, h.hready, h.hentry, h.h0, h.h1, h.hemit, h.hwidth⟩,
    fun h => ⟨h.hstage, h.hready, h.hentry, h.h0, h.h1, h.hemit, h.hwidth⟩⟩

theorem stageBlock'_of_stageBlock (T : StageData sources k p)
    (hb : StageBlock sources k p T) : StageBlock' sources k p (ofScalar sources k p T) where
  he := hb.he
  hstage := fun n x bits hc ph => by
    obtain ⟨bank, scratch, hr⟩ := hb.hstage n x bits hc ph
    exact ⟨bank, scratch, (stageReady'_iff sources k p T hb.he x bits ph bank scratch).mpr hr⟩
  hcoordinate := hb.hcoordinate
  hratio := fun n x bits hc _ monomial => hb.hsupplier n x bits hc monomial.factors
  hnum := fun n x bits hc _ _ monomial _ => hb.hcount n x bits hc monomial.factors
  hden := fun n _ _ hc _ _ _ _ => hb.hdenominator n hc
  hdenPos := fun n _ _ hc _ _ => hb.hdenominatorPositive n hc
  hcoefficients := hb.hcoefficients
  hfailure := hb.hfailure
  hpoint := hb.hpoint
  hmass := hb.hmass
  haccuracy := hb.haccuracy
  hthreshold := hb.hthreshold
  hfuel := hb.hfuel

variable (hs : StageBlock' sources k p S)

/-- `workerOf` (`Proof/CaseAnalysis/FinalTailComposeUniform.lean`) at `body'`. -/
def workerOf' := composedWorker' S.e hs.he (Soundness.cutoff (constantsOf sources))
  (body' sources k p S) (tailMachine sources)

/-- `phaseBank` (`Proof/CaseAnalysis/FinalTailComposeUniform.lean`). -/
def phaseBank' {n : ℕ} (x : BitInput n) (bits : List Bool)
    (hc : Soundness.cutoff (constantsOf sources) ≤ n) (ph : Phase) :=
  (hs.hstage n x bits hc ph).choose

/-- `phaseScratch` (`Proof/CaseAnalysis/FinalTailComposeUniform.lean`). -/
def phaseScratch' {n : ℕ} (x : BitInput n) (bits : List Bool)
    (hc : Soundness.cutoff (constantsOf sources) ≤ n) (ph : Phase) :=
  (hs.hstage n x bits hc ph).choose_spec.choose

/-- `phaseReady` (`Proof/CaseAnalysis/FinalTailComposeUniform.lean`). -/
theorem phaseReady' {n : ℕ} (x : BitInput n) (bits : List Bool)
    (hc : Soundness.cutoff (constantsOf sources) ≤ n) (ph : Phase) :
    StageReady' sources k p S hs.he x bits ph
      (phaseBank' sources k p S hs x bits hc ph) (phaseScratch' sources k p S hs x bits hc ph) :=
  (hs.hstage n x bits hc ph).choose_spec.choose_spec

/-- `foldedOf` (`Proof/CaseAnalysis/FinalTailComposeUniform.lean`) at `records'`. -/
def foldedOf' {n : ℕ} (x : BitInput n) (bits : List Bool) (ph : Phase) :=
  CompetitorSumFold.folded CompetitorSumWidth.zero
    (contributions (records' sources k p S x bits ph))

/-- **`Realizes` at A.13.9's own fraction**, in the position `rawRealizes`
(`Proof/CaseAnalysis/FinalTailComposeUniform.lean`) holds: `exactFraction_realizes`
(`Proof/CaseAnalysis/FinalExactFraction.lean`) applied to the four fields that
replaced the scalar denominator, with `hratio` carrying the paper's own
`num/den = supplier` (`paper.tex:3161`). -/
def rawRealizes' {n : ℕ} (x : BitInput n) (bits : List Bool)
    (hc : Soundness.cutoff (constantsOf sources) ≤ n) (ph : Phase) :=
  exactFraction_realizes ph (constantsOf sources) (pcppOf sources k p x bits)
    evaluate (proofOf sources k p x bits) (S.coordinate n x bits)
    (hs.hcoordinate n x bits hc) Atom.systematic
    (hsystematic_rfl (pcppOf sources k p x bits))
    (S.supplier n x bits) (S.entryWidth n) (S.num n x bits) (S.den n x bits)
    (hs.hratio n x bits hc) (hs.hnum n x bits hc ph) (hs.hden n x bits hc ph)
    (hs.hdenPos n x bits hc) (hs.hcoefficients n x bits hc ph)
    (S.failure n x bits ph) (hs.hfailure n x bits hc ph) (hs.hpoint n x bits hc ph)
    (S.mass n x bits ph) (hs.hmass n x bits hc ph) (hs.haccuracy n x bits hc ph)
    (Soundness.cutoff (constantsOf sources)) (S.stage ph) (S.stageFuel ph)
    (emissionFuel' sources k p S x bits ph) n x bits hc
    (phaseBank' sources k p S hs x bits hc ph) (phaseScratch' sources k p S hs x bits hc ph)
    (phaseReady' sources k p S hs x bits hc ph).hready
    (phaseReady' sources k p S hs x bits hc ph).hentry
    (phaseReady' sources k p S hs x bits hc ph).hemit
    (phaseReady' sources k p S hs x bits hc ph).hstage

/-- `rawRealizes_result` (`Proof/CaseAnalysis/FinalTailComposeUniform.lean`). -/
theorem rawRealizes'_result {n : ℕ} (x : BitInput n) (bits : List Bool)
    (hc : Soundness.cutoff (constantsOf sources) ≤ n) (ph : Phase) :
    (rawRealizes' sources k p S hs x bits hc ph).result = foldedOf' sources k p S x bits ph :=
  rfl

theorem blocks_run' {n : ℕ} (x : BitInput n) (bits : List Bool)
    (hc : Soundness.cutoff (constantsOf sources) ≤ n) (ph : Phase) :
    BlockRunsWidths S.e hs.he (body' sources k p S ph) (phaseFuel' sources k p S x bits ph)
      (List.ofFn x) bits
      (CloseoutRowsEstimatorCoefficients.Stream.recordWord (widthOf' sources k p S x bits ph)
        (foldedOf' sources k p S x bits ph) 1 1) (widthOf' sources k p S x bits ph) :=
  exactFraction_widths hs.he ph (pcppOf sources k p x bits) (S.coordinate n x bits)
    Atom.systematic (S.entryWidth n) (S.num n x bits) (S.den n x bits)
    (hs.hnum n x bits hc ph) (hs.hden n x bits hc ph) (hs.hdenPos n x bits hc)
    (hs.hcoefficients n x bits hc ph)
    (Soundness.cutoff (constantsOf sources)) (S.stage ph) (S.stageFuel ph)
    (emissionFuel' sources k p S x bits ph) n x bits
    (phaseBank' sources k p S hs x bits hc ph) (phaseScratch' sources k p S hs x bits hc ph)
    (phaseReady' sources k p S hs x bits hc ph).hready
    (phaseReady' sources k p S hs x bits hc ph).hentry
    (phaseReady' sources k p S hs x bits hc ph).h0
    (phaseReady' sources k p S hs x bits hc ph).h1
    (phaseReady' sources k p S hs x bits hc ph).hemit
    (phaseReady' sources k p S hs x bits hc ph).hstage
    (phaseReady' sources k p S hs x bits hc ph).hwidth

include hs in
/-- `threshold_le_width` (`Proof/CaseAnalysis/FinalTailComposeUniform.lean`). -/
theorem threshold_le_width' {n : ℕ} (x : BitInput n) (bits : List Bool) (ph : Phase) :
    thresholdWidth (constantsOf sources) ≤ widthOf' sources k p S x bits ph := by
  apply (hs.hthreshold n).trans
  unfold widthOf'
  rw [foldWidth_eq_joinScalarWidth]
  unfold joinScalarWidth CompetitorSumWidth.width CompetitorRationalDecision.width
  nlinarith [Nat.zero_le ((records' sources k p S x bits ph).length * (2*S.entryWidth n+3))]

/-- `above_run` (`Proof/CaseAnalysis/FinalTailComposeUniform.lean`). -/
theorem above_run' {n : ℕ} (x : BitInput n) (bits : List Bool)
    (hc : Soundness.cutoff (constantsOf sources) ≤ n) :
    ∃ A, Step (workerOf' sources k p S hs) (S.budget n) (fun _ => 0)
      ((UAcceptanceCarrier.verifier (workerOf' sources k p S hs) (bigTwo S.e)
        (gResult S.e)).inputTapes (List.ofFn x) bits) (fun _ => 0) A ∧
      (readTapeBit (A (gResult S.e)) 0 = true ↔
        ((((foldedOf' sources k p S x bits .penalty).value : ℚ) : ℝ) ≤
            bound (constantsOf sources) .penalty ∧
         (((foldedOf' sources k p S x bits .moment).value : ℚ) : ℝ) ≤
            bound (constantsOf sources) .moment ∧
         bound (constantsOf sources) .clause ≤
            (((foldedOf' sources k p S x bits .clause).value : ℚ) : ℝ))) ∧
      (∀ ph, A (scr S.e ph) = CloseoutRowsEstimatorCoefficients.Stream.recordWord
        (widthOf' sources k p S x bits ph) (foldedOf' sources k p S x bits ph) 1 1) := by
  have hv (ph : Phase) :
      (foldedOf' sources k p S x bits ph).Valid (widthOf' sources k p S x bits ph) :=
    (rawRealizes' sources k p S hs x bits hc ph).hvalid
  obtain ⟨A, hrun, hbit, hrec⟩ := verdict_run_uniform' S.e hs.he
    (body' sources k p S) (phaseFuel' sources k p S x bits) (widthOf' sources k p S x bits)
    (tailMachine sources) tbud (constantsOf sources) (tail_spec sources)
    (foldedOf' sources k p S x bits) hv
    (tailWidths'_of (constantsOf sources)
      (threshold_le_width' sources k p S hs x bits .penalty)
      (threshold_le_width' sources k p S hs x bits .moment)
      (threshold_le_width' sources k p S hs x bits .clause))
    (Soundness.cutoff (constantsOf sources)) n x bits hc (blocks_run' sources k p S hs x bits hc)
  refine ⟨A, hrun.enlarge (hs.hfuel n x bits), ?_, hrec⟩
  exact hbit.trans (and_congr (bound_penalty _ _) (and_congr (bound_moment _ _) (bound_clause _ _)))

/-- `below_run` (`Proof/CaseAnalysis/FinalTailComposeUniform.lean`). -/
theorem below_run' {n : ℕ} (x : BitInput n) (bits : List Bool)
    (hc : n < Soundness.cutoff (constantsOf sources)) :
    ∃ H A, Step (workerOf' sources k p S hs) (S.budget n) (fun _ => 0)
      ((UAcceptanceCarrier.verifier (workerOf' sources k p S hs) (bigTwo S.e)
        (gResult S.e)).inputTapes (List.ofFn x) bits) H A ∧
      readTapeBit (A (gResult S.e)) (H (gResult S.e)) = false := by
  obtain ⟨H, A, hrun, hbit⟩ := gated_below S.e (Soundness.cutoff (constantsOf sources))
    (innerOf' S.e hs.he (body' sources k p S) (tailMachine sources)) n x bits hc
  have hle : 2*n+3 ≤ actualFuel' sources k p S x bits := by
    unfold actualFuel' workerBudget
    omega
  exact ⟨H, A, hrun.enlarge (hle.trans (hs.hfuel n x bits)), hbit⟩

/-- **The paper's verdict at A.13.9's own fraction**, at the same fixed machine and
budget for every witness: `verdict_of_stage`
(`Proof/CaseAnalysis/FinalTailComposeUniform.lean`) with the per-call denominator.
`paper.tex:4292-4302` fixes the rejection rule as SYNTACTIC, so nothing here decides
`0 ≤ P(x) ≤ 1` and no evaluator or clamp is carried. -/
def verdict_of_stage' (n : ℕ) (x : BitInput n) (bits : List Bool) :
    Verdict (constantsOf sources) (pcppOf sources k p x bits) (proofOf sources k p x bits)
      (evaluate (pcpp := pcppOf sources k p x bits)) (workerOf' sources k p S hs) (bigTwo S.e)
      S.budget n x bits (gResult S.e) (scr S.e) (widthOf' sources k p S x bits) := by
  classical
  have hgate : LengthGate (constantsOf sources) (workerOf' sources k p S hs) (bigTwo S.e)
      (gResult S.e) S.budget :=
    gate_of_compose S.e (constantsOf sources)
      (innerOf' S.e hs.he (body' sources k p S) (tailMachine sources)) S.budget
  by_cases hc : Soundness.cutoff (constantsOf sources) ≤ n
  · let hrun := above_run' sources k p S hs x bits hc
    let A := hrun.choose
    have hstep := hrun.choose_spec.1
    have hbit := hrun.choose_spec.2.1
    have hrec := hrun.choose_spec.2.2
    refine {
      gate := hgate
      heads := fun _ => 0
      exit := A
      run := hstep
      realizes := fun _ ph => transport (rawRealizes' sources k p S hs x bits hc ph)
        (fun _ => 0) A hstep (hrec ph)
      hshared := fun _ _ => rfl
      estimate := fun ph => (((foldedOf' sources k p S x bits ph).value : ℚ) : ℝ)
      hestimate := fun _ _ => rfl
      accepts_iff := ?_ }
    exact hbit.trans ⟨fun h => ⟨hc, h⟩, fun h => h.2⟩
  · let hrun := below_run' sources k p S hs x bits (by omega)
    let H := hrun.choose
    let A := hrun.choose_spec.choose
    have hstep := hrun.choose_spec.choose_spec.1
    have hbit := hrun.choose_spec.choose_spec.2
    refine {
      gate := hgate
      heads := H
      exit := A
      run := hstep
      realizes := fun h => (hc h).elim
      hshared := fun h => (hc h).elim
      estimate := fun _ => 0
      hestimate := fun h => (hc h).elim
      accepts_iff := ?_ }
    constructor
    · intro h
      have habs : (false : Bool) = true := hbit.symm.trans h
      cases habs
    · intro h
      exact (hc h.1).elim

/-- `pipeline_of_stage` (`Proof/CaseAnalysis/FinalPipelineOfStage.lean`). -/
def pipeline_of_stage' : Pipeline sources k (PolynomialClock.ordinaryClock k)
    (constantsOf sources) (workerOf' sources k p S hs) (bigTwo S.e) (gResult S.e) S.budget :=
  fun n x bits =>
    PSum.inr ⟨oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits,
     Atoms sources k p x bits, proofOf sources k p x bits,
     evaluate (pcpp := pcppOf sources k p x bits), scr S.e,
     widthOf' sources k p S x bits, verdict_of_stage' sources k p S hs n x bits⟩

/-- `pinnedSym_of_stage` (`Proof/CaseAnalysis/FinalPipelineOfStage.lean`). -/
def pinnedSym_of_stage' (s : ℕ) (_hs : Soundness.cutoff (constantsOf sources) ≤ s)
    (input : BitInput (2^s))
    (oracle : BooleanCircuit
      ((outer sources k (PolynomialClock.ordinaryClock k)).result.pcp.nativeWidth (2^s)))
    (family : SymFamily sources k (PolynomialClock.ordinaryClock k) p input oracle)
    (guess : BitInput (2^s/16))
    (_hlen : 16*(List.ofFn guess).length ≤ 2^s)
    (_hheader : CompetitorWitnessTriple.headerValid (List.ofFn guess))
    (horacle : decodeBooleanCircuit
      ((outer sources k (PolynomialClock.ordinaryClock k)).result.pcp.nativeWidth (2^s))
      (RadixSemantics.value (BoundedFields.oracle (List.ofFn guess))) = some oracle)
    (hsize : oracle.size ≤ oracleSizeBound p.degree
      ((outer sources k (PolynomialClock.ordinaryClock k)).result.pcp.nativeWidth (2^s)))
    (hfamily : SumFamily.decode symmetricCircuitCodec NormalizedSymmetricThresholdCircuit.wireCount
      NormalizedSymmetricThresholdCircuit.descriptionBits
      (symLimits sources k (PolynomialClock.ordinaryClock k) p input oracle)
      (CloseoutWitnessPolicy.variableCount sources k (PolynomialClock.ordinaryClock k) input oracle)
      (RadixSemantics.value (BoundedFields.family (List.ofFn guess))) = some family)
    (hmode : BoundedFields.symmetric (List.ofFn guess) = true) :
    PinnedSym' sources k (PolynomialClock.ordinaryClock k) (constantsOf sources)
      (workerOf' sources k p S hs) (bigTwo S.e) (gResult S.e) S.budget p.clauseDegree p.copies
      (zeta (constantsOf sources)) 1 s input oracle family guess := by
  have ho := oracleOf_pin sources k (PolynomialClock.ordinaryClock k) p.degree (2^s)
    (List.ofFn guess) oracle horacle hsize
  subst oracle
  have hp : proofOf sources k p input (List.ofFn guess) =
      SumFamily.value NormalizedSymmetricThresholdCircuit.eval family :=
    proofValueOf_sym sources k (PolynomialClock.ordinaryClock k) p input _ (List.ofFn guess)
      family hmode hfamily
  refine ⟨Atoms sources k p input (List.ofFn guess),
    evaluate (pcpp := pcppOf sources k p input (List.ofFn guess)), scr S.e,
    widthOf' sources k p S input (List.ofFn guess), ?_⟩
  rw [← hp]
  exact verdict_of_stage' sources k p S hs (2^s) input (List.ofFn guess)

/-- `pinnedThr_of_stage` (`Proof/CaseAnalysis/FinalPipelineOfStage.lean`). -/
def pinnedThr_of_stage' (s : ℕ) (_hs : Soundness.cutoff (constantsOf sources) ≤ s)
    (input : BitInput (2^s))
    (oracle : BooleanCircuit
      ((outer sources k (PolynomialClock.ordinaryClock k)).result.pcp.nativeWidth (2^s)))
    (family : ThrFamily sources k (PolynomialClock.ordinaryClock k) p input oracle)
    (guess : BitInput (2^s/16))
    (_hlen : 16*(List.ofFn guess).length ≤ 2^s)
    (_hheader : CompetitorWitnessTriple.headerValid (List.ofFn guess))
    (horacle : decodeBooleanCircuit
      ((outer sources k (PolynomialClock.ordinaryClock k)).result.pcp.nativeWidth (2^s))
      (RadixSemantics.value (BoundedFields.oracle (List.ofFn guess))) = some oracle)
    (hsize : oracle.size ≤ oracleSizeBound p.degree
      ((outer sources k (PolynomialClock.ordinaryClock k)).result.pcp.nativeWidth (2^s)))
    (hfamily : SumFamily.decode thresholdCircuitCodec NormalizedThresholdThresholdCircuit.wireCount
      NormalizedThresholdThresholdCircuit.descriptionBits
      (thrLimits sources k (PolynomialClock.ordinaryClock k) p input oracle)
      (CloseoutWitnessPolicy.variableCount sources k (PolynomialClock.ordinaryClock k) input oracle)
      (RadixSemantics.value (BoundedFields.family (List.ofFn guess))) = some family)
    (hmode : BoundedFields.symmetric (List.ofFn guess) = false) :
    PinnedThr' sources k (PolynomialClock.ordinaryClock k) (constantsOf sources)
      (workerOf' sources k p S hs) (bigTwo S.e) (gResult S.e) S.budget p.clauseDegree p.copies
      (zeta (constantsOf sources)) 1 s input oracle family guess := by
  have ho := oracleOf_pin sources k (PolynomialClock.ordinaryClock k) p.degree (2^s)
    (List.ofFn guess) oracle horacle hsize
  subst oracle
  have hp : proofOf sources k p input (List.ofFn guess) =
      SumFamily.value NormalizedThresholdThresholdCircuit.eval family :=
    proofValueOf_thr sources k (PolynomialClock.ordinaryClock k) p input _ (List.ofFn guess)
      family hmode hfamily
  refine ⟨Atoms sources k p input (List.ofFn guess),
    evaluate (pcpp := pcppOf sources k p input (List.ofFn guess)), scr S.e,
    widthOf' sources k p S input (List.ofFn guess), ?_⟩
  rw [← hp]
  exact verdict_of_stage' sources k p S hs (2^s) input (List.ofFn guess)

def machine_of_stage' :
    RepairSource.CloseoutFinal.Machine sources p.degree p.clauseDegree p.copies where
  k := k
  clock := PolynomialClock.ordinaryClock k
  tapes := bigOf S.e
  states := _
  worker := workerOf' sources k p S hs
  htapes := bigTwo S.e
  result := gResult S.e
  fuel := S.budget
  pipeline := pipeline_of_stage' sources k p S hs
  gateOnset := Soundness.cutoff (constantsOf sources)
  symCap := 1
  thrCap := 1
  hsym := by norm_num
  hthr := by norm_num
  symDecides := symDecides_of_pinned' sources k (PolynomialClock.ordinaryClock k)
    (constantsOf sources) (workerOf' sources k p S hs) (bigTwo S.e) (gResult S.e) S.budget
    p.degree p.clauseDegree p.copies 1 (Soundness.cutoff (constantsOf sources))
    (fun s h => h.trans (Nat.lt_two_pow_self).le) (pinnedSym_of_stage' sources k p S hs)
  thrDecides := thrDecides_of_pinned' sources k (PolynomialClock.ordinaryClock k)
    (constantsOf sources) (workerOf' sources k p S hs) (bigTwo S.e) (gResult S.e) S.budget
    p.degree p.clauseDegree p.copies 1 (Soundness.cutoff (constantsOf sources))
    (fun s h => h.trans (Nat.lt_two_pow_self).le) (pinnedThr_of_stage' sources k p S hs)

end

/-- `StageChoice` (`Proof/CaseAnalysis/FinalCompletion.lean`) at `StageData'`. -/
abbrev StageChoice' (src : EightSources) {g : ℝ} (par : Parameters src g) : Type 1 :=
  Σ' (j : ℕ) (T : StageData' src j par), StageBlock' src j par T

/-- `machineOf` (`Proof/CaseAnalysis/FinalCompletion.lean`) at `StageData'`. -/
noncomputable def machineOf'
    (stage : (src : EightSources) → ∀ g : ℝ, 0 < g → g < 1/2 →
      (par : Parameters src g) → StageChoice' src par)
    (src : EightSources) (g : ℝ) (hg : 0 < g) (hh : g < 1/2) (par : Parameters src g) :
    RepairSource.CloseoutFinal.Machine src par.degree par.clauseDegree par.copies :=
  machine_of_stage' src (stage src g hg hh par).1 par (stage src g hg hh par).2.1
    (stage src g hg hh par).2.2

/-- **THEOREM 2.5, conditional on the supplier stage at A.13.9's OWN fraction and on
its fuel ledger.**  `theorem25_of_stageBlock`
(`Proof/CaseAnalysis/FinalCompletion.lean`) with `StageChoice` replaced by
`StageChoice'`: the record stream the machine emits carries the paper's own
`|\mathcal E| 2 ^ q` per call (`paper.tex:3161`) rather than a common dyadic scale,
and no other premise changes. -/
theorem theorem25_of_stageBlock'
    (stage : (src : EightSources) → ∀ g : ℝ, 0 < g → g < 1/2 →
      (par : Parameters src g) → StageChoice' src par)
    (ledger : (src : EightSources) → ∀ (g : ℝ) (hg : 0 < g) (hh : g < 1/2)
      (par : Parameters src g),
      Runtime src (stage src g hg hh par).1
        (PolynomialClock.ordinaryClock (stage src g hg hh par).1)
        (stage src g hg hh par).2.1.budget) :
    Theorem25Target :=
  theorem25_of_leaves (machineOf' stage) ledger

noncomputable section
variable (sources : EightSources) (k : ℕ) {gamma : ℝ} (p : Parameters sources gamma)
  (S : StageData' sources k p)

/-! ## §6 The capstone anti-fork receipt -/

theorem workerOf'_ofScalar (T : StageData sources k p) (hb : StageBlock sources k p T) :
    workerOf' sources k p (ofScalar sources k p T)
        (stageBlock'_of_stageBlock sources k p T hb)
      = workerOf sources k p T hb := rfl

theorem foldedOf'_ofScalar (T : StageData sources k p) {n : ℕ} (x : BitInput n)
    (bits : List Bool) (ph : Phase) :
    foldedOf' sources k p (ofScalar sources k p T) x bits ph
      = foldedOf sources k p T x bits ph := rfl

def shell : StageData sources k p where
  e := S.e
  st := S.st
  stage := S.stage
  stageFuel := S.stageFuel
  entryWidth := S.entryWidth
  denominator := fun _ => 1
  coordinate := S.coordinate
  supplier := S.supplier
  answer := fun _ _ _ _ => 0
  failure := S.failure
  mass := S.mass
  L := S.L
  budget := S.budget

/-- **The record COUNT is blind to the record function.** -/
theorem records'_length_shell {n : ℕ} (x : BitInput n) (bits : List Bool) (ph : Phase) :
    (records' sources k p S x bits ph).length
      = (records sources k p (shell sources k p S) x bits ph).length := by
  simp [phaseRecords', phaseRecords, siteRecords, callRecords, shell]

/-- The call cap of `phaseRecords_length_le`
(`Proof/CaseAnalysis/FinalCallCountCap.lean`), at the exact record stream. -/
theorem records'_length_le (L : ℕ) {n : ℕ} (x : BitInput n) (bits : List Bool) (ph : Phase)
    (hL : ∀ i, ((S.coordinate n x bits) i).monomials.length ≤ L) :
    (records' sources k p S x bits ph).length
      ≤ 2 ^ (pcppOf sources k p x bits).clauseBits * CloseoutFinalC10CallCountCap.siteCap L := by
  rw [records'_length_shell sources k p S x bits ph]
  exact CloseoutFinalC10CallCountCap.phaseRecords_length_le L _ (pcppOf sources k p x bits)
    (fun _ => 0) 1 ph (S.coordinate n x bits) Atom.systematic hL

/-- The fold width agrees with the shell's. -/
theorem widthOf'_shell {n : ℕ} (x : BitInput n) (bits : List Bool) (ph : Phase) :
    widthOf' sources k p S x bits ph = widthOf sources k p (shell sources k p S) x bits ph := by
  unfold widthOf' widthOf
  rw [foldWidth_eq_joinScalarWidth, foldWidth_eq_joinScalarWidth,
    records'_length_shell sources k p S x bits ph]
  rfl

/-- The phase fuel agrees with the shell's. -/
theorem phaseFuel'_shell {n : ℕ} (x : BitInput n) (bits : List Bool) (ph : Phase) :
    phaseFuel' sources k p S x bits ph = phaseFuel sources k p (shell sources k p S) x bits ph := by
  unfold phaseFuel' phaseFuel emissionFuel' emissionFuel
  rw [records'_length_shell sources k p S x bits ph]
  rfl

theorem actualFuel'_shell {n : ℕ} (x : BitInput n) (bits : List Bool) :
    actualFuel' sources k p S x bits = actualFuel sources k p (shell sources k p S) x bits := by
  have hF : phaseFuel' sources k p S x bits = phaseFuel sources k p (shell sources k p S) x bits :=
    funext (fun ph => phaseFuel'_shell sources k p S x bits ph)
  have hW : widthOf' sources k p S x bits = widthOf sources k p (shell sources k p S) x bits :=
    funext (fun ph => widthOf'_shell sources k p S x bits ph)
  unfold actualFuel' actualFuel
  rw [hF, hW]

/-- **`StageBlock'.hfuel` from a call-count cap**, the exact-route form of
`stage_field_hfuel` (`Proof/CaseAnalysis/FinalStageFields.lean`). -/
theorem hfuel'_of_cap (K : ℕ → ℕ)
    (hK : ∀ (n : ℕ) (x : BitInput n) (bits : List Bool) (ph : Phase),
      (records' sources k p S x bits ph).length ≤ K n)
    (hbudget : ∀ n, fuelAt sources k p (shell sources k p S) n (fun _ => K n) ≤ S.budget n) :
    ∀ (n : ℕ) (x : BitInput n) (bits : List Bool),
      actualFuel' sources k p S x bits ≤ S.budget n := by
  intro n x bits
  rw [actualFuel'_shell sources k p S x bits,
    actualFuel_eq sources k p (shell sources k p S) x bits]
  refine (fuelAt_mono sources k p (shell sources k p S) n ?_).trans (hbudget n)
  intro ph
  rw [← records'_length_shell sources k p S x bits ph]
  exact hK n x bits ph

attribute [local irreducible] stageNum stageDen stageRowSupplier stageMass stageCoordinate
  stageEntryWidth stageArity stageTarget stageFailure

/-- **The exact-fraction stage data**: A.13.9's own numerator over its own
`|\mathcal E| 2 ^ q` (`paper.tex:3161`), per call, at STAGEFIELDS' witnesses. -/
def exactStageData (liveScale : ℕ) (coefficientFloor : ℕ → ℕ) (extra : ℕ) (st : Phase → ℕ)
    (stage : (ph : Phase) → LocalBitMultitape.Machine (218 + (60 + extra)) (st ph))
    (stageFuel : Phase → ℕ → ℕ) (L budget : ℕ → ℕ) : StageData' sources k p where
  e := 60 + extra
  st := st
  stage := stage
  stageFuel := stageFuel
  entryWidth := stageEntryWidth sources k p coefficientFloor
  num := stageNum sources k p liveScale
  den := stageDen sources k p liveScale
  coordinate := stageCoordinate sources k p
  supplier := stageRowSupplier sources k p liveScale
  failure := fun n _ _ _ =>
    1 / ((stageTarget sources p (stageArity sources k n) + 1 : ℕ) : ℝ)
  mass := stageMass sources k p
  L := L
  budget := budget

theorem stageBlock'_of_stageFields (liveScale : ℕ) (coefficientFloor : ℕ → ℕ)
    (enum : S.num = stageNum sources k p liveScale)
    (eden : S.den = stageDen sources k p liveScale)
    (esup : S.supplier = stageRowSupplier sources k p liveScale)
    (ewidth : S.entryWidth = stageEntryWidth sources k p coefficientFloor)
    (ecoord : S.coordinate = stageCoordinate sources k p)
    (emass : S.mass = stageMass sources k p)
    (efail : S.failure = fun n _ _ _ =>
      1 / ((stageTarget sources p (stageArity sources k n) + 1 : ℕ) : ℝ))
    (he : 58 ≤ S.e)
    (ebound : ∀ (n : ℕ) (x : BitInput n) (bits : List Bool),
      Soundness.cutoff (constantsOf sources) ≤ n →
      ∀ (ph : Phase) (address : Fin (2 ^ (pcppOf sources k p x bits).clauseBits))
        (monomial : CircuitMonomial (Atoms sources k p x bits) 4),
        monomial ∈ (siteCalls ph (pcppOf sources k p x bits)
          (stageCoordinate sources k p n x bits) Atom.systematic address).monomials →
        stageDen sources k p liveScale n x bits address monomial
          < 2 ^ stageEntryWidth sources k p coefficientFloor n)
    (ecoef : ∀ (n : ℕ) (x : BitInput n) (bits : List Bool),
      Soundness.cutoff (constantsOf sources) ≤ n →
      ∀ (ph : Phase) (address : Fin (2 ^ (pcppOf sources k p x bits).clauseBits)),
        CoefficientsFit (stageEntryWidth sources k p coefficientFloor n)
          (siteCalls ph (pcppOf sources k p x bits) (stageCoordinate sources k p n x bits)
            Atom.systematic address))
    (hstage : ∀ (n : ℕ) (x : BitInput n) (bits : List Bool),
      Soundness.cutoff (constantsOf sources) ≤ n →
      ∀ ph, ∃ bank scratch, StageReady' sources k p S he x bits ph bank scratch)
    (hfuel : ∀ (n : ℕ) (x : BitInput n) (bits : List Bool),
      actualFuel' sources k p S x bits ≤ S.budget n) :
    StageBlock' sources k p S where
  he := he
  hstage := hstage
  hcoordinate := by rw [ecoord]; exact stage_field_hcoordinate sources k p
  hratio := by rw [enum, eden, esup]; exact stage_field_hratio sources k p liveScale
  hnum := by
    rw [enum, ewidth, ecoord]
    intro n x bits hn ph address monomial hmem
    apply lt_of_le_of_lt ?_ (ebound n x bits hn ph address monomial hmem)
    unfold stageNum stageDen
    exact rowAnswer_le_rowDenominator _ _ _
  hden := by rw [eden, ewidth, ecoord]; exact ebound
  hdenPos := by rw [eden]; exact stage_field_hdenPos sources k p liveScale
  hcoefficients := by rw [ewidth, ecoord]; exact ecoef
  hfailure := by
    rw [efail]
    intro n _ _ _ _
    positivity
  hpoint := by
    rw [esup, efail]
    exact fun n x bits hc _ circuits =>
      stage_field_hpoint_row sources k p liveScale n x bits hc circuits
  hmass := by rw [ecoord, emass]; exact stage_field_hmass sources k p
  haccuracy := by
    rw [efail, emass]
    exact fun n x bits hc ph => stage_field_haccuracy_row sources k p n x bits hc ph
  hthreshold := by rw [ewidth]; exact stage_field_hthreshold sources k p coefficientFloor
  hfuel := hfuel

theorem exactStageBlock (liveScale : ℕ) (coefficientFloor : ℕ → ℕ) (extra : ℕ)
    (st : Phase → ℕ)
    (stage : (ph : Phase) → LocalBitMultitape.Machine (218 + (60 + extra)) (st ph))
    (stageFuel : Phase → ℕ → ℕ) (L budget K : ℕ → ℕ) (he : 58 ≤ 60 + extra)
    (ebound : ∀ (n : ℕ) (x : BitInput n) (bits : List Bool),
      Soundness.cutoff (constantsOf sources) ≤ n →
      ∀ (ph : Phase) (address : Fin (2 ^ (pcppOf sources k p x bits).clauseBits))
        (monomial : CircuitMonomial (Atoms sources k p x bits) 4),
        monomial ∈ (siteCalls ph (pcppOf sources k p x bits)
          (stageCoordinate sources k p n x bits) Atom.systematic address).monomials →
        stageDen sources k p liveScale n x bits address monomial
          < 2 ^ stageEntryWidth sources k p coefficientFloor n)
    (ecoef : ∀ (n : ℕ) (x : BitInput n) (bits : List Bool),
      Soundness.cutoff (constantsOf sources) ≤ n →
      ∀ (ph : Phase) (address : Fin (2 ^ (pcppOf sources k p x bits).clauseBits)),
        CoefficientsFit (stageEntryWidth sources k p coefficientFloor n)
          (siteCalls ph (pcppOf sources k p x bits) (stageCoordinate sources k p n x bits)
            Atom.systematic address))
    (hstage : ∀ (n : ℕ) (x : BitInput n) (bits : List Bool),
      Soundness.cutoff (constantsOf sources) ≤ n →
      ∀ ph, ∃ bank scratch,
        StageReady' sources k p (exactStageData sources k p liveScale coefficientFloor extra st stage stageFuel L budget) he x bits ph bank scratch)
    (hK : ∀ (n : ℕ) (x : BitInput n) (bits : List Bool) (ph : Phase),
      (records' sources k p (exactStageData sources k p liveScale coefficientFloor extra st stage stageFuel L budget) x bits ph).length ≤ K n)
    (hbudget : ∀ n, fuelAt sources k p (shell sources k p (exactStageData sources k p liveScale coefficientFloor extra st stage stageFuel L budget)) n (fun _ => K n) ≤ budget n) :
    StageBlock' sources k p (exactStageData sources k p liveScale coefficientFloor extra st stage stageFuel L budget) :=
  stageBlock'_of_stageFields sources k p (exactStageData sources k p liveScale coefficientFloor extra st stage stageFuel L budget) liveScale coefficientFloor
    rfl rfl rfl rfl rfl rfl rfl he ebound ecoef hstage
    (hfuel'_of_cap sources k p (exactStageData sources k p liveScale coefficientFloor extra st stage stageFuel L budget) K hK hbudget)

end
end NearCubicWires.RepairOrdinary.CloseoutFinalC10ExactStagePackage
