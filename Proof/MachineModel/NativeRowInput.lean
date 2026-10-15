import Proof.MachineModel.NativeOutputBound
import Proof.CaseAnalysis.RowsSharedInput
import Proof.CaseAnalysis.RowsEstimatorHeader

/-! The actual raw family has the literal row type consumed by the estimator.
The occurrence list and shared digit width are unchanged. -/
namespace NearCubicWires.ExtIncidence.NativeRowInput
open RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def bank {N : ℕ} (ps : List (List (List (Fin N)))):=ps.map rawRows

theorem bank_width {N : ℕ} (ps : List (List (List (Fin N)))) (w : ℕ)
    (hw : ∀ ms∈ps,ms.length<2^w) : ∀ rows∈bank ps,rows.length≤2^w:=by
  intro rows hr
  obtain ⟨ms,hm,rfl⟩:=List.mem_map.mp hr
  simpa only [rawRows,List.length_map] using (hw ms hm).le

def input (s Q w : ℕ) (gs : List (ExactThresholdGate ((s+1)/2+s/2)))
    (ps : List (List (List (Fin gs.length)))) (hs : 67 ≤ s)
    (hg : (RowBinLift.batch Q (CloseoutRowsCacheInput.family gs (bank ps))).length^100≤2^s)
    (hw : ∀ ms∈ps,ms.length<2^w) : EquationRow.Input:=
  CloseoutRowsSharedInput.input s Q w gs (bank ps) hs hg (bank_width ps w hw)

theorem stream_eq (s Q w : ℕ) (gs : List (ExactThresholdGate ((s+1)/2+s/2)))
    (ps : List (List (List (Fin gs.length)))) (hs : 67 ≤ s)
    (hg : (RowBinLift.batch Q (CloseoutRowsCacheInput.family gs (bank ps))).length^100≤2^s)
    (hw : ∀ ms∈ps,ms.length<2^w) :
    CloseoutRowsEstimator.Header.stream (input s Q w gs ps hs hg hw)=
      ps.flatMap (NativeFamily.emit gs Q w):=by
  simp only [CloseoutRowsEstimator.Header.stream,input,CloseoutRowsSharedInput.input,
    CloseoutRowsCacheInput.input,CloseoutRows.commonInput,CloseoutRows.commonWidth,
    bank,List.flatMap_map,List.flatMap_assoc]
  rfl

theorem stream_fits (s Q w : ℕ) (gs : List (ExactThresholdGate ((s+1)/2+s/2)))
    (ps : List (List (List (Fin gs.length)))) (hs : 67 ≤ s)
    (hg : (RowBinLift.batch Q (CloseoutRowsCacheInput.family gs (bank ps))).length^100≤2^s)
    (hw : ∀ ms∈ps,ms.length<2^w) (hQ : 1 ≤ Q) :
    (CloseoutRowsEstimator.Header.stream (input s Q w gs ps hs hg hw)).length≤
      NativeOutputBound.allowance (NativeMeasured.capacity gs Q w) Q ps.length:=by
  rw [stream_eq]
  exact NativeOutputBound.family_length gs Q w ps hw hQ

end NearCubicWires.ExtIncidence.NativeRowInput
