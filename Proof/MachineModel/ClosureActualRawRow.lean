import Proof.MachineModel.ClosureScannedRawRow

/-! The actual C10 table instantiates the raw-output transaction. All table
correctness and value bounds are discharged here, as they were for the framed
printer. Only request legality, physical input preparation and capacities remain.
-/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.P1Closure.ActualRawRow
open LocalBitMultitape ExtDecompositionBatch RepairRepresentation RepairOrdinary
open SupplierPipeline SupplierEstimator CanonicalFourfoldRowProgram ThresholdCompiler
open SourceInterfaces RepairSource RepairSource.CloseoutFinal RecoveryRootRound
open CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients
open CompetitorSelectedCount CompetitorCountMask C10SupplierRowInput
open CompetitorCrossScheduler (producer)

theorem run {q : Nat} (a : DecompositionAlgorithm) (printer : WilliamsAlgorithm)
    (live : Finset (Fin q)) (occ : List (SupportedNormalizedGate q)) (s : Nat)
    (harity : (s+1)/2+s/2 = liveᶜ.card) (P : StructuralGF2Polynomial) (w : Nat)
    (hs : 67 ≤ s) (hmon : (CloseoutRowsUniversal.lower a live occ P).length < 2^w)
    (hpos : 1 ≤ w) (hload : 200*(live.card+w*(live.card+2)) ≤ s)
    (C D B R : Nat) (est : CompetitorValidity.Estimate) (den : Nat)
    (select :
      Fin (EquationRow.request (rowInput a live occ s harity P w hs hmon hpos hload)).U →
      Fin (EquationRow.request (rowInput a live occ s harity P w hs hmon hpos hload)).U → Bool)
    (old : Fin (WholePrefix.tapes (producer printer)) → List Bool) (out : List Bool)
    (hcapacity : old (Retained.capacity (producer printer)) = List.replicate C true)
    (hC : (Header.stream (rowInput a live occ s harity P w hs hmon hpos hload)).length ≤ C)
    (hCD : C ≤ D)
    (hd : (rowInput a live occ s harity P w hs hmon hpos hload).d ≤ D)
    (hp : (rowInput a live occ s harity P w hs hmon hpos hload).p ≤ D)
    (hDpos : 1 ≤ D)
    (hD : Driver.value printer
      (rowInput a live occ s harity P w hs hmon hpos hload).d
      (rowInput a live occ s harity P w hs hmon hpos hload).p
      (rowInput a live occ s harity P w hs hmon hpos hload).cuts.length C ≤ D)
    (hB : RowPayload.budget (scalarWidth
      (EquationRow.request (rowInput a live occ s harity P w hs hmon hpos hload)) (live.card+1)) ≤ B)
    (hR : ScannedRow.budget printer (rowInput a live occ s harity P w hs hmon hpos hload)
      D (live.card+1) ≤ R) (hBR : B+1 ≤ R) :
    let row := rowInput a live occ s harity P w hs hmon hpos hload
    let p := producer printer
    let b := scalarWidth (EquationRow.request row) (live.card+1)
    let count := (selected (CompetitorSelectedCells.cells row.odd
      (C10SupplierTable.table a live occ s harity P w hs hmon hpos hload) select)).sum
    let Z := ScannedRow.output p row C D (live.card+1) est den select
      (Stream.recordWord b est count den)
    Step (ScannedRawRow.machine printer)
      (RawRowJoin.budget (ScannedRow.budget printer row D (live.card+1)) b B)
      (RawRowJoin.heads (ScannedRow.tapes p) out)
      (RawRowJoin.bank (RawRowJoin.padded (ScannedRawRow.port p) B
        (ScannedRow.input p row C D (live.card+1) est den select old [])) R B out)
      (dockH (RawRowJoin.slots (ScannedRawRow.port p)) (RawRowJoin.heads (ScannedRow.tapes p) out)
        (RowPayloadReusable.heads (out++SignedSortKey.binary b count)))
      (install (RawRowJoin.slots (ScannedRawRow.port p))
        (RawRowJoin.bank (RawRowJoin.padded (ScannedRawRow.port p) B Z) R B out)
        (RowPayloadReusable.input [] (out++SignedSortKey.binary b count) B R)) ∧
    RawRowJoin.budget (ScannedRow.budget printer row D (live.card+1)) b B ≤ 22*D+4*B+170 := by
  dsimp only
  exact ScannedRawRow.run printer _ C D (live.card+1) B R est den
    (C10SupplierTable.table a live occ s harity P w hs hmon hpos hload) select old out
    hcapacity hCD hd hp hDpos hC
    (rowInput_p a live occ s harity P w hs hmon hpos hload)
    (C10SupplierTable.table_lt a live occ s harity P w hs hmon hpos hload)
    (fun i => C10SupplierTable.table_modEq a live occ s harity P w hs hmon hpos hload
      i.divNat i.modNat) hD hB hR hBR

end NearCubicWires.P1Closure.ActualRawRow
