import Proof.MachineModel.ClosureHeaderHandoff
import Proof.MachineModel.ClosureBinaryPreparedWriter
import Proof.MachineModel.ClosureBinaryReusableRow

/-! Actual cold native writer → paid header rewind/copy → actual C.10
selected count and binary payload, on one bank. The consumer header starts
blank. Source cache, lowered stream, metadata/mask and allocation inputs
remain explicit; no header or table answer is supplied to the entry. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.BinaryPreparedPayload
open LocalBitMultitape ExtDecompositionBatch RepairRepresentation RepairOrdinary RecoveryRootRound
open SupplierPipeline SupplierEstimator CanonicalFourfoldRowProgram ThresholdCompiler
open SourceInterfaces RepairSource CloseoutFinal RecoveryRootRound
open CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients
open CompetitorSelectedCount CompetitorCountMask C10SupplierRowInput C10RowFrameJoin
open CompetitorCrossScheduler (producer)
attribute [local irreducible] pool BinaryPool.pool bank CloseoutRowsCacheInput.family CompactBounds.radix
  CompetitorCrossScheduler.producer Warm.input BinaryPreparedWriter.machine ScannedRawRow.machine

def localNative (p : Program) : Fin (ScannedRow.tapes p) :=
  ((Reuse.native p).castAdd 7).castAdd 3
def native (p : Program) : Fin (ScannedRow.tapes p+1+2) :=
  ((localNative p).castAdd 1).castAdd 2
noncomputable def rowData (p : Program) (row : EquationRow.Input) (C D Q B R : Nat)
    (est : CompetitorValidity.Estimate) (den : Nat)
    (select : Fin (EquationRow.request row).U→Fin (EquationRow.request row).U→Bool)
    (old : Fin (WholePrefix.tapes p)→List Bool) (out : List Bool) :=
  RawRowJoin.bank (RawRowJoin.padded (ScannedRawRow.port p) B
    (ScannedRow.input p row C D Q est den select old [])) R B out

set_option maxHeartbeats 800000 in
theorem native_word (p : Program) (row : EquationRow.Input) (C D Q B R : Nat)
    (est : CompetitorValidity.Estimate) (den : Nat)
    (select : Fin (EquationRow.request row).U→Fin (EquationRow.request row).U→Bool)
    (old : Fin (WholePrefix.tapes p)→List Bool) (out : List Bool) :
    rowData p row C D Q B R est den select old out (native p)=ZeroPadding.pad C (Header.stream row) := by
  have hn : localNative p≠ScannedRawRow.port p := by
    intro h
    have h:=congrArg Fin.val h
    simp only [localNative,Fin.val_castAdd,ScannedRawRow.port,native_val,output_val] at h
    have := tapes_ge p
    omega
  change ZeroPadding.pad (RawRowJoin.caps (ScannedRawRow.port p) B (localNative p))
    (ScannedRow.input p row C D Q est den select old [] (localNative p))=_
  rw [RawRowJoin.caps,if_neg hn,ZeroPadding.pad_zero]
  change (Function.update (exitTapes p D old []) (Reuse.native p)
    (ZeroPadding.pad C (Header.stream row))) (Reuse.native p)=_
  exact Function.update_self _ _ _

noncomputable def machine (printer : WilliamsAlgorithm) := HeaderHandoff.machine
  BinaryPreparedWriter.machine (ScannedRawRow.machine printer) (180 : Fin 448) (native (producer printer))

set_option maxHeartbeats 800000 in
theorem run {q : Nat} (a : DecompositionAlgorithm) (printer : WilliamsAlgorithm)
    (live : Finset (Fin q)) (occ : List (SupportedNormalizedGate q)) (s : Nat)
    (harity : (s+1)/2+s/2 = liveᶜ.card) (P : StructuralGF2Polynomial) (w degree : Nat)
    (hs : 67 ≤ s) (hmon : (CloseoutRowsUniversal.lower a live occ P).length < 2^w)
    (hpos : 1 ≤ w) (hload : 200*(live.card+w*(live.card+2)) ≤ s)
    (hdegree : CloseoutRawRows.RawMonomialDegreeAtMost degree P)
    (C D B R S : Nat) (est : CompetitorValidity.Estimate) (den : Nat)
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
      D (live.card+1) ≤ R) (hBR : B+1 ≤ R)
    (hS : (ExtIncidence.stream (CloseoutRowsUniversal.lower a live occ P)).length≤S) :
    let row := BinaryRequest.input a live occ s harity P w degree hs hmon hpos hload hdegree
    let p := producer printer
    let b := scalarWidth (EquationRow.request row) (live.card+1)
    let count := (selected (CompetitorSelectedCells.cells row.odd
      (C10SupplierTable.table a live occ s harity P w hs hmon hpos hload) select)).sum
    let np := BinaryPreparedWriter.budget a live occ s harity P w degree S
    let nq := RawRowJoin.budget (ScannedRow.budget printer row D (live.card+1)) b B
    let A := rowData p row C D (live.card+1) B R est den select old out
    let next := out++SignedSortKey.binary b count
    let Z := rowData p row C D (live.card+1) B R est den select
      (Warm.input p row C (live.card+1) est den select) next
    Step (machine printer) (2*np+2*C+nq+8)
      (HeaderHandoff.pack (BinaryPreparedWriter.heads []) 0
        (RawRowJoin.heads (ScannedRow.tapes p) out) (fun _=>0))
      (HeaderHandoff.pack (BinaryPreparedWriter.entry a live occ s harity P w degree S [] [])
        (List.replicate np false) (Function.update A (native p) (List.replicate C false)) (HeaderHandoff.extra C))
      (dockH HeaderHandoff.target (HeaderHandoff.pack
        (HeaderHandoff.resetHeads (BinaryPreparedWriter.finalHeads a live occ s harity P w degree []) 180) 0
        (RawRowJoin.heads (ScannedRow.tapes p) out) (fun _=>0))
        (RawRowJoin.heads (ScannedRow.tapes p) next))
      (install HeaderHandoff.target (HeaderHandoff.pack
        (BinaryPreparedWriter.finalTapes a live occ s harity P w degree S [] [])
        (List.replicate np false) A (HeaderHandoff.extra C)) Z) := by
  dsimp only
  obtain ⟨written,hword⟩ := BinaryPreparedWriter.run a live occ s harity P w degree S [] []
    hs hmon hpos hload hdegree hS
  simp only [List.nil_append] at hword
  obtain ⟨consumed,_⟩ := BinaryReusableRow.run a printer live occ s harity P w degree
    hs hmon hpos hload hdegree C D B R est den select old out
    hcapacity hC hCD hd hp hDpos hD hB hR hBR
  exact HeaderHandoff.run BinaryPreparedWriter.machine (ScannedRawRow.machine printer)
    180 (native (producer printer)) _ _ C _ _ _ _ _ _ _ _ _ _ written consumed
    rfl rfl hword (native_word _ _ _ _ _ _ _ _ _ _ _ _) hC le_rfl

end NearCubicWires.P1Closure.BinaryPreparedPayload
