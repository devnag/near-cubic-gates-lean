import Proof.MachineModel.ClosureRadixNative
import Proof.MachineModel.ClosureCompactSharedInput
import Proof.MachineModel.ClosureActualMaskDegree
import Proof.CaseAnalysis.FinalSupplierTable

/-! The literal C.10 request in the compact raw-stream writer's order.
This joins A.12's semantic count and its actual emitted header. The retained
metadata and raw source are still physical input obligations. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.CompactNativeRequest
open LocalBitMultitape RepairRepresentation RepairOrdinary
open SupplierPipeline SupplierEstimator ThresholdCompiler CanonicalFourfoldRowProgram
open RepairSource CloseoutFinal C10SupplierRowInput
open ExtIncidence RepairSource.VerifierDecoding

attribute [local irreducible] pool bank childList CompactBounds.radix
  CloseoutRowsUniversal.pool ExtDecompositionBatch.GS

theorem family_eq {l r : Nat} (gs : List (ExactThresholdGate (l+r))) [P1Radix gs]
    (rows : List (List (List Bool))) :
    P1CompactCloseoutRowsCacheInput.family gs rows = CloseoutRowsCacheInput.family gs rows := rfl

variable {q : Nat} (a : DecompositionAlgorithm) (live : Finset (Fin q))
  (occ : List (SupportedNormalizedGate q)) (s : Nat)
  (harity : (s+1)/2+s/2 = liveᶜ.card) (P : StructuralGF2Polynomial) (w degree : Nat)
  (hs : 67 ≤ s) (hmon : (CloseoutRowsUniversal.lower a live occ P).length < 2^w)
  (hpos : 1 ≤ w) (hload : 200*(live.card+w*(live.card+2)) ≤ s)
  (hdegree : CloseoutRawRows.RawMonomialDegreeAtMost degree P)

noncomputable def input : EquationRow.Input := by
  letI := p1ActualRadix a live occ s harity degree
  letI := p1ActualMaskDegree a live occ s harity P degree hdegree
  exact P1CompactInput.input s (live.card+1) w (pool a live occ s harity)
    (bank a live occ s harity P) hs (gate a live occ s harity P w hmon hpos hload)
    (bank_rows_le a live occ s harity P w hmon)

theorem stream_eq :
    letI := p1ActualRadix a live occ s harity degree
    CloseoutRowsEstimator.Header.stream (input a live occ s harity P w degree hs hmon hpos hload hdegree) =
      (ps a live occ s harity P).flatMap
        (P1CompactNativeFamily.emit (pool a live occ s harity) (live.card+1) w) := by
  letI := p1ActualRadix a live occ s harity degree
  simp only [input,P1CompactInput.input,CloseoutRowsEstimator.Header.stream,
    bank,NativeRowInput.bank,List.flatMap_map,List.flatMap_assoc,
    CloseoutRows.commonInput,CloseoutRows.commonWidth]
  rfl

theorem table_modEq
    (i j : Fin (2^((s+1)/2))) :
    let row := input a live occ s harity P w degree hs hmon hpos hload hdegree
    Int.ModEq ((2 : Int)^(live.card+1))
      (SupplierPrinter.weightedDominance
        (MatrixScoreBatch.leftScore (EquationRow.request row))
        (MatrixScoreBatch.rightScore (EquationRow.request row))
        (MatrixScoreBatch.weight (EquationRow.request row)) i j)
      (C10SupplierTable.table a live occ s harity P w hs hmon hpos hload i j) := by
  letI := p1ActualRadix a live occ s harity degree
  letI := p1ActualMaskDegree a live occ s harity P degree hdegree
  have h := P1CompactInput.count_modEq s (live.card+1) w (pool a live occ s harity)
    (bank a live occ s harity P) hs (gate a live occ s harity P w hmon hpos hload)
    (bank_rows_le a live occ s harity P w hmon) i j
  simp only [CompetitorCountTable.rowValues,family_eq] at h
  exact h

theorem writer_run :
    letI := p1ActualRadix a live occ s harity degree
    ∀ (out pre tail : List Bool) (H : Fin 277 → Nat) (A : Fin 277 → List Bool),
    (∀ j,H (NativeFanoutLayout.sources j)=0) →
    (∀ j,A (NativeFanoutLayout.sources j)=
      P1CompactNativeMaster.words (pool a live occ s harity) (live.card+1) w j) →
    ∃ actual,runFrom P1CompactNativeFamily.machine
      (P1CompactNativeFamily.budget (pool a live occ s harity) (live.card+1) w (ps a live occ s harity P))
      (RepeatMachine.cfg 0
        (P1CompactNativeFamily.entry (pool a live occ s harity) (live.card+1) w
          (ps a live occ s harity P) pre tail H A 0 out) (ps a live occ s harity P).length 1)=some actual ∧
      actual.final=RepeatMachine.cfg 3
        (P1CompactNativeFamily.entry (pool a live occ s harity) (live.card+1) w
          (ps a live occ s harity P) pre tail H A (ps a live occ s harity P).length
          (out++CloseoutRowsEstimator.Header.stream (input a live occ s harity P w degree hs hmon hpos hload hdegree)))
        (ps a live occ s harity P).length 1 ∧
      actual.steps ≤ P1CompactNativeFamily.budget (pool a live occ s harity) (live.card+1) w
        (ps a live occ s harity P) := by
  letI := p1ActualRadix a live occ s harity degree
  letI := p1ActualMaskDegree a live occ s harity P degree hdegree
  intro out pre tail H A mh ma
  rw [stream_eq]
  exact P1CompactNativeFamily.family_run (pool a live occ s harity) (live.card+1) w
    (ps a live occ s harity P)
    (fun ms hm => P1BankDegree.bound (gs := pool a live occ s harity)
      (bank := bank a live occ s harity P) (rawRows ms)
      (by unfold bank NativeRowInput.bank; exact List.mem_map.mpr ⟨ms,hm,rfl⟩))
    out pre tail (ps_rows_lt a live occ s harity P w hmon) (by omega) H A mh ma

end NearCubicWires.P1Closure.CompactNativeRequest
