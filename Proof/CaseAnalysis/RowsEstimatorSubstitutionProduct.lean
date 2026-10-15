import Proof.CaseAnalysis.RowsEstimatorSubstitutionEraseReset
import Proof.CaseAnalysis.RowsRawProductLoop

/-! Raw multiplication returns both live polynomial heads. Its row capacity
is a proof bound on false logs, independent of the left table length. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.SubstitutionProduct
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine:=MaskedReset.machine CloseoutRowsRawProductLoop.machine (fun i=>decide (i=0 ∨ i=2))
def data (C : ℕ) (left right : List (List ℕ)) (out : List Bool) : Fin 6 → List Bool:=
  ![ZeroPadding.pad C (ExtIncidence.stream left),ZeroPadding.pad C (ExtIncidence.stream right),
    ZeroPadding.pad C out,List.replicate C false,List.replicate C false,List.replicate C false]
def budget (R count : ℕ):=2*CloseoutRowsRawProductLoop.budget R count+2

theorem run (C R : ℕ) (left right : List (List ℕ)) (hR : R ≤ C)
    (hl : ∀ l∈left,(l.flatMap ExtIncidence.block).length+1 ≤ R)
    (hc : ∀ l∈left,CloseoutRowsRawProductRow.budget l right ≤ R)
    (hb : CloseoutRowsRawProductLoop.budget R left.length ≤ C) :
    Step machine (budget R left.length) (fun _=>0) (data C left right []) (fun _=>0)
      (data C left right (ExtIncidence.stream (CloseoutRowsRawProductLoop.product left right))) := by
  have raw:=CloseoutRowsRawProductLoop.product_run R left right [] hl hc
  simp only [List.nil_append] at raw
  have padded:=raw.pad (fun _=>C)
  have masked:=padded.mask (cap:=C) (fun i=>decide (i=0 ∨ i=2)) (by
    intro i hi
    have he : i=0 ∨ i=2:=of_decide_eq_true hi
    rcases he with rfl | rfl <;>rfl) hb
  apply (masked.congr_in ?_ ?_).congr ?_ ?_
  all_goals funext i;fin_cases i
  all_goals simp [data,CloseoutRowsRawProductBody.heads,CloseoutRowsRawProductBody.data,
    Fin.addCases,SubstitutionErase.false_pad R C hR]

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.SubstitutionProduct
