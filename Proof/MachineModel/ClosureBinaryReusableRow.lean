import Proof.MachineModel.ClosureScannedRowState
import Proof.MachineModel.ClosureBinaryRequest

/-! The physical binary-order row is consumed by the scanner/printer and
selected-count payload transaction. The complete bank returns in its reusable
state, and the value is the original C.10 table count. The produced header,
selection mask and paid workspace remain the explicit input boundary. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.P1Closure.BinaryReusableRow
open LocalBitMultitape ExtDecompositionBatch RepairRepresentation RepairOrdinary
open SupplierPipeline SupplierEstimator CanonicalFourfoldRowProgram ThresholdCompiler
open SourceInterfaces RepairSource RepairSource.CloseoutFinal RecoveryRootRound
open CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients
open CompetitorSelectedCount CompetitorCountMask C10SupplierRowInput
open CompetitorCrossScheduler (producer)

attribute [local irreducible] pool BinaryPool.pool bank CloseoutRowsCacheInput.family CompactBounds.radix

theorem run {q : Nat} (a : DecompositionAlgorithm) (printer : WilliamsAlgorithm)
    (live : Finset (Fin q)) (occ : List (SupportedNormalizedGate q)) (s : Nat)
    (harity : (s+1)/2+s/2 = liveᶜ.card) (P : StructuralGF2Polynomial) (w degree : Nat)
    (hs : 67 ≤ s) (hmon : (CloseoutRowsUniversal.lower a live occ P).length < 2^w)
    (hpos : 1 ≤ w) (hload : 200*(live.card+w*(live.card+2)) ≤ s)
    (hdegree : CloseoutRawRows.RawMonomialDegreeAtMost degree P)
    (C D B R : Nat) (est : CompetitorValidity.Estimate) (den : Nat)
    (select :
      Fin (2^((s+1)/2)) →
      Fin (2^((s+1)/2)) → Bool)
    (old : Fin (WholePrefix.tapes (producer printer)) → List Bool) (out : List Bool)
    (hcapacity : old (Retained.capacity (producer printer)) = List.replicate C true)
    (hC : (Header.stream (BinaryRequest.input a live occ s harity P w degree hs hmon hpos hload hdegree)).length ≤ C)
    (hCD : C ≤ D)
    (hd : (BinaryRequest.input a live occ s harity P w degree hs hmon hpos hload hdegree).d ≤ D)
    (hp : (BinaryRequest.input a live occ s harity P w degree hs hmon hpos hload hdegree).p ≤ D)
    (hDpos : 1 ≤ D)
    (hD : Driver.value printer
      (BinaryRequest.input a live occ s harity P w degree hs hmon hpos hload hdegree).d
      (BinaryRequest.input a live occ s harity P w degree hs hmon hpos hload hdegree).p
      (BinaryRequest.input a live occ s harity P w degree hs hmon hpos hload hdegree).cuts.length C ≤ D)
    (hB : RowPayload.budget (scalarWidth
      (EquationRow.request (BinaryRequest.input a live occ s harity P w degree hs hmon hpos hload hdegree)) (live.card+1)) ≤ B)
    (hR : ScannedRow.budget printer (BinaryRequest.input a live occ s harity P w degree hs hmon hpos hload hdegree)
      D (live.card+1) ≤ R) (hBR : B+1 ≤ R) :
    let row := BinaryRequest.input a live occ s harity P w degree hs hmon hpos hload hdegree
    let p := producer printer
    let b := scalarWidth (EquationRow.request row) (live.card+1)
    let count := (selected (CompetitorSelectedCells.cells row.odd
      (C10SupplierTable.table a live occ s harity P w hs hmon hpos hload) select)).sum
    Step (ScannedRawRow.machine printer)
      (RawRowJoin.budget (ScannedRow.budget printer row D (live.card+1)) b B)
      (RawRowJoin.heads (ScannedRow.tapes p) out)
      (RawRowJoin.bank (RawRowJoin.padded (ScannedRawRow.port p) B
        (ScannedRow.input p row C D (live.card+1) est den select old [])) R B out)
      (RawRowJoin.heads (ScannedRow.tapes p) (out++SignedSortKey.binary b count))
      (RawRowJoin.bank (RawRowJoin.padded (ScannedRawRow.port p) B
        (ScannedRow.input p row C D (live.card+1) est den select
          (Warm.input p row C (live.card+1) est den select) [])) R B
        (out++SignedSortKey.binary b count)) ∧
    RawRowJoin.budget (ScannedRow.budget printer row D (live.card+1)) b B ≤ 22*D+4*B+170 := by
  dsimp only
  have hQ : live.card+1 ≤ (EquationRow.request
      (BinaryRequest.input a live occ s harity P w degree hs hmon hpos hload hdegree)).p := by
    change live.card+1 ≤ CompactBounds.radix a live occ*
      ((min degree (BinaryPool.pool a live occ s harity).length)*(live.card+1))+(live.card+1)+1
    omega
  obtain ⟨step,bound⟩ := ScannedRawRow.run printer
    (BinaryRequest.input a live occ s harity P w degree hs hmon hpos hload hdegree)
    C D (live.card+1) B R est den
    (C10SupplierTable.table a live occ s harity P w hs hmon hpos hload) select old out
    hcapacity hCD hd hp hDpos hC hQ
    (C10SupplierTable.table_lt a live occ s harity P w hs hmon hpos hload)
    (fun i => BinaryRequest.table_modEq a live occ s harity P w degree hs hmon hpos hload hdegree
      i.divNat i.modNat) hD hB hR hBR
  refine ⟨?_,bound⟩
  rw [RawRowState.exit_heads,RawRowState.exit_tapes,ScannedRowState.reset_to_input] at step
  exact step

end NearCubicWires.P1Closure.BinaryReusableRow
