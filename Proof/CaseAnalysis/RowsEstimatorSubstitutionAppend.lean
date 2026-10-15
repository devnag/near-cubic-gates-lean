import Proof.CaseAnalysis.RowsEstimatorSubstitutionEraseReset
import Proof.Hierarchy.HierarchyFixedWord

/-! Append one substituted monomial's raw body and initialize its next unit. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.SubstitutionAppend
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine:=MaskedReset.machine CloseoutRowsRawProductRow.machine (fun i=>decide (i=1))
def heads (out : List Bool) : Fin 5 → ℕ:=![0,0,out.length,0,0]
def data (C : ℕ) (p : List (List ℕ)) (out : List Bool) : Fin 5 → List Bool:=
  ![[false],ZeroPadding.pad C (ExtIncidence.stream p),out,List.replicate C false,List.replicate C false]
def budget (p : List (List ℕ)):=2*CloseoutRowsRawProductRow.budget [] p+2

theorem run (C : ℕ) (p : List (List ℕ)) (out : List Bool)
    (hb : CloseoutRowsRawProductRow.budget [] p ≤ C) :
    Step machine (budget p) (heads out) (data C p out)
      (heads (out++p.flatMap ExtIncidence.monomialWord)) (data C p (out++p.flatMap ExtIncidence.monomialWord)) := by
  have hC : 1 ≤ C:=by unfold CloseoutRowsRawProductRow.budget at hb;omega
  have raw:=CloseoutRowsRawPolynomialAdd.empty_row C p out hC
  have padded:=raw.pad (fun i=>if i=1 then C else 0)
  have masked:=padded.mask (cap:=C) (fun i=>decide (i=1)) (by
    intro i hi
    have he : i=1:=of_decide_eq_true hi
    subst i;rfl) hb
  apply (masked.congr_in ?_ ?_).congr ?_ ?_
  all_goals funext i;fin_cases i
  all_goals simp [heads,data,CloseoutRowsRawProductFields.heads,CloseoutRowsRawProductFields.data,
    CloseoutRowsRawPolynomialAdd.body,Fin.addCases,ZeroPadding.pad_zero]

def unitMachine:=HierarchyFixedWord.machine [true,false,false]
theorem unit_run (C : ℕ) (hC : 3 ≤ C) :
    Step unitMachine 8 (fun _=>0) (fun _=>List.replicate C false) (fun _=>0)
      (![ZeroPadding.pad C (ExtIncidence.stream [[]]),List.replicate C false] : Fin 2 → List Bool) := by
  have raw:=(Step.of_ready (HierarchyFixedWord.word_ready [true,false,false])).pad (fun _=>C)
  apply (raw.congr_in rfl ?_).congr rfl ?_
  · funext i;fin_cases i <;>rfl
  · funext i;fin_cases i
    · rfl
    · exact SubstitutionErase.false_pad 3 C hC

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.SubstitutionAppend
