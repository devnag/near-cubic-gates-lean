import Proof.CaseAnalysis.FinalExactStagePackage
import Proof.CaseAnalysis.FinalExactRecordLoop
import Proof.CaseAnalysis.FinalRecordPadding
import Proof.CaseAnalysis.FinalClauseBitsUniform

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10StageJoin

open NearCubicWires
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary.CloseoutWitness
open NearCubicWires.RepairOrdinary.CloseoutFinalC10ExactStagePackage
open NearCubicWires.RepairOrdinary.CloseoutFinalC10StageFields
open NearCubicWires.RepairOrdinary.CloseoutFinalC10ExactRecordLoop (exactRecord_stageReady
  foldWidth_eq_joinScalarWidth')
open NearCubicWires.RepairOrdinary.CloseoutFinalC10SupplierCalls (CoefficientsFit siteCalls)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDock (joinScalarWidth)
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule (Phase)
open NearCubicWires.RepairRepresentation
open NearCubicWires.RepairSource (EightSources)
open NearCubicWires.RepairSource.CloseoutFinal (Parameters constantsOf)
open NearCubicWires.RepairSource.CloseoutFinal.C10RecordPadding (stageFuel_mono)
open NearCubicWires.RepairSource.CloseoutFinal.C10StageFuelBound (fuelAt)
open NearCubicWires.RepairSource.CloseoutFinal.C10SumFamilyTransport (stageCoordinate stageMass)
open NearCubicWires.RepairSource.CloseoutFinal.C10SupplierStage (CallsReady stage stageFuel
  stageStates)
open NearCubicWires.RepairSource.CloseoutFinal.C10TailComposeUniform (pcppOf Atoms)
open NearCubicWires.RepairSource.CloseoutFinal.C10TotalDecode (Atom)
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierPipeline

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

attribute [local irreducible] stageNum stageDen stageRowSupplier stageMass stageCoordinate
  stageEntryWidth stageArity stageTarget stageFailure

variable (sources : EightSources) (k : ℕ) {gamma : ℝ} (p : Parameters sources gamma)

/-! ## §1 The one width identity the join needs -/

theorem widthOf'_eq_joinScalarWidth (S : StageData' sources k p) {n : ℕ} (x : BitInput n)
    (bits : List Bool) (ph : Phase) :
    widthOf' sources k p S x bits ph
      = joinScalarWidth (S.entryWidth n) (records' sources k p S x bits ph).length := by
  unfold widthOf'
  exact foldWidth_eq_joinScalarWidth' (S.entryWidth n) (records' sources k p S x bits ph)

/-! ## §2 `StageReady'` at the exact-fraction stage data, from `CallsReady` -/

/-- **The join.**  `exactRecord_stageReady`
(`Proof/CaseAnalysis/FinalExactRecordLoop.lean`) delivers exactly `StageReady'`'s
(`Proof/CaseAnalysis/FinalExactStagePackage.lean`) seven fields at the stage data
`exactStageData` (`Proof/CaseAnalysis/FinalExactStagePackage.lean`) names, once the run is
taken at the branch's own record count and enlarged to the declared `callCount` with
`stageFuel_mono` (`Proof/CaseAnalysis/FinalRecordPadding.lean`).  `hemit` is definitional
-- `emissionFuel'` (`Proof/CaseAnalysis/FinalExactStagePackage.lean`) is literally that
function -- and `hwidth` is §1. -/
theorem exactStage_stageReady (liveScale : ℕ) (coefficientFloor : ℕ → ℕ) (extra : ℕ)
    {cs : Phase → ℕ}
    (calls : (ph : Phase) → Machine (218 + (60 + extra)) (cs ph))
    (callFuel : Phase → ℕ → ℕ) (callCount L budget : ℕ → ℕ)
    (he : 58 ≤ 60 + extra)
    {n : ℕ} (x : BitInput n) (bits : List Bool) (ph : Phase)
    (hcap : (records' sources k p
        (exactStageData sources k p liveScale coefficientFloor extra (stageStates extra calls)
          (stage extra calls)
          (stageFuel callFuel (stageEntryWidth sources k p coefficientFloor) callCount)
          L budget) x bits ph).length ≤ callCount n)
    (hcalls : CallsReady extra (calls ph) (callFuel ph n)
      (stageEntryWidth sources k p coefficientFloor n)
      (records' sources k p
        (exactStageData sources k p liveScale coefficientFloor extra (stageStates extra calls)
          (stage extra calls)
          (stageFuel callFuel (stageEntryWidth sources k p coefficientFloor) callCount)
          L budget) x bits ph).length
      (CloseoutRowsEstimatorCoefficients.Stream.words
        (stageEntryWidth sources k p coefficientFloor n)
        (records' sources k p
          (exactStageData sources k p liveScale coefficientFloor extra (stageStates extra calls)
            (stage extra calls)
            (stageFuel callFuel (stageEntryWidth sources k p coefficientFloor) callCount)
            L budget) x bits ph))
      (List.ofFn x) bits) :
    ∃ bank scratch,
      StageReady' sources k p
        (exactStageData sources k p liveScale coefficientFloor extra (stageStates extra calls)
          (stage extra calls)
          (stageFuel callFuel (stageEntryWidth sources k p coefficientFloor) callCount)
          L budget) he x bits ph bank scratch := by
  obtain ⟨bank, scratch, hstep, hready, hentry, h0, h1, hwidth⟩ :=
    exactRecord_stageReady (Atom := Atoms sources k p x bits) extra he calls callFuel
      (stageEntryWidth sources k p coefficientFloor)
      (fun _ => (records' sources k p
        (exactStageData sources k p liveScale coefficientFloor extra (stageStates extra calls)
          (stage extra calls)
          (stageFuel callFuel (stageEntryWidth sources k p coefficientFloor) callCount)
          L budget) x bits ph).length)
      ph (pcppOf sources k p x bits) (stageCoordinate sources k p n x bits) Atom.systematic
      (stageNum sources k p liveScale n x bits) (stageDen sources k p liveScale n x bits)
      (records' sources k p
        (exactStageData sources k p liveScale coefficientFloor extra (stageStates extra calls)
          (stage extra calls)
          (stageFuel callFuel (stageEntryWidth sources k p coefficientFloor) callCount)
          L budget) x bits ph) rfl
      (Soundness.cutoff (constantsOf sources)) n x bits rfl hcalls
  refine ⟨bank, scratch,
    hstep.enlarge (stageFuel_mono callFuel (stageEntryWidth sources k p coefficientFloor)
      _ callCount ph n hcap),
    hready, hentry, h0, h1, rfl, ?_⟩
  intro j
  refine (hwidth j).trans ?_
  rw [widthOf'_eq_joinScalarWidth sources k p
    (exactStageData sources k p liveScale coefficientFloor extra (stageStates extra calls)
      (stage extra calls)
      (stageFuel callFuel (stageEntryWidth sources k p coefficientFloor) callCount)
      L budget) x bits ph]
  rfl

/-! ## §3 `StageBlock'` at A.13.9's own fraction, open in `CallsReady` alone -/

theorem exactStageBlock_of_callsReady (liveScale : ℕ) (coefficientFloor : ℕ → ℕ) (extra : ℕ)
    {cs : Phase → ℕ}
    (calls : (ph : Phase) → Machine (218 + (60 + extra)) (cs ph))
    (callFuel : Phase → ℕ → ℕ) (callCount L budget : ℕ → ℕ)
    (he : 58 ≤ 60 + extra)
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
    (hcap : ∀ (n : ℕ) (x : BitInput n) (bits : List Bool) (ph : Phase),
      (records' sources k p
        (exactStageData sources k p liveScale coefficientFloor extra (stageStates extra calls)
          (stage extra calls)
          (stageFuel callFuel (stageEntryWidth sources k p coefficientFloor) callCount)
          L budget) x bits ph).length ≤ callCount n)
    (hbudget : ∀ n, fuelAt sources k p (shell sources k p
        (exactStageData sources k p liveScale coefficientFloor extra (stageStates extra calls)
          (stage extra calls)
          (stageFuel callFuel (stageEntryWidth sources k p coefficientFloor) callCount)
          L budget)) n (fun _ => callCount n) ≤ budget n)
    (hcalls : ∀ (n : ℕ) (x : BitInput n) (bits : List Bool),
      Soundness.cutoff (constantsOf sources) ≤ n → ∀ ph,
        CallsReady extra (calls ph) (callFuel ph n)
          (stageEntryWidth sources k p coefficientFloor n)
          (records' sources k p
            (exactStageData sources k p liveScale coefficientFloor extra
              (stageStates extra calls) (stage extra calls)
              (stageFuel callFuel (stageEntryWidth sources k p coefficientFloor) callCount)
              L budget) x bits ph).length
          (CloseoutRowsEstimatorCoefficients.Stream.words
            (stageEntryWidth sources k p coefficientFloor n)
            (records' sources k p
              (exactStageData sources k p liveScale coefficientFloor extra
                (stageStates extra calls) (stage extra calls)
                (stageFuel callFuel (stageEntryWidth sources k p coefficientFloor) callCount)
                L budget) x bits ph))
          (List.ofFn x) bits) :
    StageBlock' sources k p
      (exactStageData sources k p liveScale coefficientFloor extra (stageStates extra calls)
        (stage extra calls)
        (stageFuel callFuel (stageEntryWidth sources k p coefficientFloor) callCount)
        L budget) :=
  exactStageBlock sources k p liveScale coefficientFloor extra (stageStates extra calls)
    (stage extra calls)
    (stageFuel callFuel (stageEntryWidth sources k p coefficientFloor) callCount)
    L budget callCount he ebound ecoef
    (fun n x bits hn ph =>
      exactStage_stageReady sources k p liveScale coefficientFloor extra calls callFuel
        callCount L budget he x bits ph (hcap n x bits ph) (hcalls n x bits hn ph))
    hcap hbudget

theorem records'_length_le_callCap (S : StageData' sources k p) (Lcap : ℕ → ℕ)
    (hL : ∀ (n : ℕ) (x : BitInput n) (bits : List Bool) j,
      ((S.coordinate n x bits) j).monomials.length ≤ Lcap n)
    (n : ℕ) (x : BitInput n) (bits : List Bool) (ph : Phase) :
    (records' sources k p S x bits ph).length
      ≤ CloseoutFinalC10ClauseBitsUniform.callCap sources k p Lcap n := by
  rw [records'_length_shell sources k p S x bits ph]
  exact CloseoutFinalC10ClauseBitsUniform.stage_records_length_le_uniform sources k p
    (shell sources k p S) Lcap hL n x bits ph

theorem exactStageBlock_at_uniform_caps (liveScale : ℕ) (extra : ℕ) {cs : Phase → ℕ}
    (calls : (ph : Phase) → Machine (218 + (60 + extra)) (cs ph))
    (callFuel : Phase → ℕ → ℕ) (L budget : ℕ → ℕ)
    (he : 58 ≤ 60 + extra)
    (ebound : ∀ (n : ℕ) (x : BitInput n) (bits : List Bool),
      Soundness.cutoff (constantsOf sources) ≤ n →
      ∀ (ph : Phase) (address : Fin (2 ^ (pcppOf sources k p x bits).clauseBits))
        (monomial : CircuitMonomial (Atoms sources k p x bits) 4),
        monomial ∈ (siteCalls ph (pcppOf sources k p x bits)
          (stageCoordinate sources k p n x bits) Atom.systematic address).monomials →
        stageDen sources k p liveScale n x bits address monomial
          < 2 ^ stageEntryWidth sources k p
            (CloseoutFinalC10ClauseBitsUniform.coefficientFloor sources k p) n)
    (hbudget : ∀ n, fuelAt sources k p (shell sources k p
        (exactStageData sources k p liveScale
        (CloseoutFinalC10ClauseBitsUniform.coefficientFloor sources k p) extra
        (stageStates extra calls) (stage extra calls)
        (stageFuel callFuel
          (stageEntryWidth sources k p
            (CloseoutFinalC10ClauseBitsUniform.coefficientFloor sources k p))
          (CloseoutFinalC10ClauseBitsUniform.callCap sources k p
            (CloseoutFinalC10ClauseBitsUniform.termFloor sources k p)))
        L budget)) n
      (fun _ => CloseoutFinalC10ClauseBitsUniform.callCap sources k p
        (CloseoutFinalC10ClauseBitsUniform.termFloor sources k p) n) ≤ budget n)
    (hcalls : ∀ (n : ℕ) (x : BitInput n) (bits : List Bool),
      Soundness.cutoff (constantsOf sources) ≤ n → ∀ ph,
        CallsReady extra (calls ph) (callFuel ph n)
          (stageEntryWidth sources k p
            (CloseoutFinalC10ClauseBitsUniform.coefficientFloor sources k p) n)
          (records' sources k p (exactStageData sources k p liveScale
        (CloseoutFinalC10ClauseBitsUniform.coefficientFloor sources k p) extra
        (stageStates extra calls) (stage extra calls)
        (stageFuel callFuel
          (stageEntryWidth sources k p
            (CloseoutFinalC10ClauseBitsUniform.coefficientFloor sources k p))
          (CloseoutFinalC10ClauseBitsUniform.callCap sources k p
            (CloseoutFinalC10ClauseBitsUniform.termFloor sources k p)))
        L budget) x bits ph).length
          (CloseoutRowsEstimatorCoefficients.Stream.words
            (stageEntryWidth sources k p
              (CloseoutFinalC10ClauseBitsUniform.coefficientFloor sources k p) n)
            (records' sources k p (exactStageData sources k p liveScale
        (CloseoutFinalC10ClauseBitsUniform.coefficientFloor sources k p) extra
        (stageStates extra calls) (stage extra calls)
        (stageFuel callFuel
          (stageEntryWidth sources k p
            (CloseoutFinalC10ClauseBitsUniform.coefficientFloor sources k p))
          (CloseoutFinalC10ClauseBitsUniform.callCap sources k p
            (CloseoutFinalC10ClauseBitsUniform.termFloor sources k p)))
        L budget) x bits ph))
          (List.ofFn x) bits) :
    StageBlock' sources k p (exactStageData sources k p liveScale
        (CloseoutFinalC10ClauseBitsUniform.coefficientFloor sources k p) extra
        (stageStates extra calls) (stage extra calls)
        (stageFuel callFuel
          (stageEntryWidth sources k p
            (CloseoutFinalC10ClauseBitsUniform.coefficientFloor sources k p))
          (CloseoutFinalC10ClauseBitsUniform.callCap sources k p
            (CloseoutFinalC10ClauseBitsUniform.termFloor sources k p)))
        L budget) :=
  exactStageBlock_of_callsReady sources k p liveScale
    (CloseoutFinalC10ClauseBitsUniform.coefficientFloor sources k p) extra calls callFuel
    (CloseoutFinalC10ClauseBitsUniform.callCap sources k p
      (CloseoutFinalC10ClauseBitsUniform.termFloor sources k p))
    L budget he ebound
    (CloseoutFinalC10ClauseBitsUniform.stage_field_hcoefficients_uniform sources k p)
    (fun n x bits ph =>
      records'_length_le_callCap sources k p (exactStageData sources k p liveScale
        (CloseoutFinalC10ClauseBitsUniform.coefficientFloor sources k p) extra
        (stageStates extra calls) (stage extra calls)
        (stageFuel callFuel
          (stageEntryWidth sources k p
            (CloseoutFinalC10ClauseBitsUniform.coefficientFloor sources k p))
          (CloseoutFinalC10ClauseBitsUniform.callCap sources k p
            (CloseoutFinalC10ClauseBitsUniform.termFloor sources k p)))
        L budget)
        (CloseoutFinalC10ClauseBitsUniform.termFloor sources k p)
        (CloseoutFinalC10ClauseBitsUniform.stage_hL_at_stageCoordinate sources k p)
        n x bits ph)
    hbudget hcalls

end
end NearCubicWires.RepairOrdinary.CloseoutFinalC10StageJoin
