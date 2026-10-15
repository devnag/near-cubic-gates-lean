import Proof.CaseAnalysis.RowsEstimatorSubstitutionErase

/-! Return the logical eraser to its reusable zero backing, at logical cost. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.SubstitutionErase
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def reset:=MaskedReset.machine machine (fun _=>true)
def bank (C : ℕ) (p : List (List ℕ)) : Fin 2 → List Bool:=
  ![ZeroPadding.pad C (ExtIncidence.stream p),List.replicate C false]

theorem false_pad (n C : ℕ) (h : n ≤ C) : ZeroPadding.pad C (List.replicate n false)=List.replicate C false := by
  simp only [ZeroPadding.pad,List.length_replicate,←List.replicate_add,Nat.add_sub_of_le h]

theorem reset_run (C : ℕ) (p : List (List ℕ)) (hc : (ExtIncidence.stream p).length ≤ C) :
    Step reset (2*(ExtIncidence.stream p).length+2) (fun _=>0) (bank C p)
      (fun _=>0) (fun _=>List.replicate C false) := by
  have raw:=(run p).pad (fun _=>C)
  have masked:=raw.mask (cap:=C) (fun _=>true) (by intro i _;rfl) hc
  apply (masked.congr_in ?_ ?_).congr ?_ ?_
  · funext i;fin_cases i <;>rfl
  · funext i;fin_cases i <;>rfl
  · funext i;fin_cases i <;>rfl
  · funext i;fin_cases i
    · exact false_pad _ C hc
    · rfl

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.SubstitutionErase
