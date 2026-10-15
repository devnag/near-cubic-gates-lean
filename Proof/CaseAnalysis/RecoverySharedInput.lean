import Proof.CaseAnalysis.CommonPortBank
import Proof.CaseAnalysis.RecoveryQuery

/-! Exact three-port cold recovery input for the common dispatcher: retained
hierarchy request, paid W, and the existing shared oracle's false padding. -/
namespace NearCubicWires.RepairSource.RecoveryBoundedCold
open LocalBitMultitape RepairOrdinary SourceInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section
variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)

def sharedLocal (k d : ℕ) : Fin 3→Fin (tapes source k d):=
  ![(RecoveryBoundedColdSourceGraph.hierarchyPort source k d).castAdd 790,
    (RecoveryBoundedColdSourceGraph.wPort source k d).castAdd 790,queryPort source k d]
def sharedWords (word : List Bool) (W padding : ℕ) : Fin 3→List Bool:=
  ![word,List.replicate W true,List.replicate padding false]

theorem sharedLocal_injective (k d : ℕ) : Function.Injective (sharedLocal source k d):=by
  have hne:=RecoveryBoundedColdSourceGraph.inputs_distinct source k d
  have hn:(RecoveryBoundedColdSourceGraph.hierarchyPort source k d).val≠
      (RecoveryBoundedColdSourceGraph.wPort source k d).val:=fun he=>hne (Fin.ext he)
  have hh:(RecoveryBoundedColdSourceGraph.hierarchyPort source k d).val<oldTapes source k d:=
    (RecoveryBoundedColdSourceGraph.hierarchyPort source k d).isLt
  have hw:(RecoveryBoundedColdSourceGraph.wPort source k d).val<oldTapes source k d:=
    (RecoveryBoundedColdSourceGraph.wPort source k d).isLt
  intro i j he
  fin_cases i <;>fin_cases j <;>try rfl
  all_goals
    have hv:=congrArg Fin.val he
    simp [sharedLocal,queryPort] at hv
    omega

theorem shared_input_old (k d : ℕ) (word : List Bool) (W padding : ℕ)
    (i : Fin (oldTapes source k d)) :
    queryInput source k d word W padding (i.castAdd 790)=
      RecoveryBoundedColdSourceGraph.input source k d word W i:=by
  have hi:i.castAdd 790≠queryPort source k d:=by
    intro he
    have hv:=congrArg Fin.val he
    have hb:=i.isLt
    change i.val=oldTapes source k d+356 at hv
    omega
  simp only [queryInput,Function.update_of_ne hi,input,Fin.addCases_left]

theorem shared_input_port (k d : ℕ) (word : List Bool) (W padding : ℕ) (j : Fin 3) :
    queryInput source k d word W padding (sharedLocal source k d j)=sharedWords word W padding j:=by
  fin_cases j
  · change queryInput source k d word W padding
      ((RecoveryBoundedColdSourceGraph.hierarchyPort source k d).castAdd 790)=word
    rw [shared_input_old]
    simp only [RecoveryBoundedColdSourceGraph.input,if_true]
  · change queryInput source k d word W padding
      ((RecoveryBoundedColdSourceGraph.wPort source k d).castAdd 790)=List.replicate W true
    rw [shared_input_old]
    simp only [RecoveryBoundedColdSourceGraph.input,
      if_neg (Ne.symm (RecoveryBoundedColdSourceGraph.inputs_distinct source k d)),if_true]
  · exact Function.update_self _ _ _

theorem shared_input_empty (k d : ℕ) (word : List Bool) (W padding : ℕ)
    (i : Fin (tapes source k d)) (hi : ∀ j,sharedLocal source k d j≠i) :
    queryInput source k d word W padding i=[]:=by
  have hq:i≠queryPort source k d:=(hi 2).symm
  rw [queryInput,Function.update_of_ne hq]
  revert hi
  refine Fin.addCases (m:=oldTapes source k d) (n:=790) (fun j=>?_) (fun j=>?_) i
  · intro hj
    have hh:j≠RecoveryBoundedColdSourceGraph.hierarchyPort source k d:=by
      intro he
      exact hj 0 (congrArg (fun z : Fin (oldTapes source k d)=>z.castAdd 790) he.symm)
    have hw:j≠RecoveryBoundedColdSourceGraph.wPort source k d:=by
      intro he
      exact hj 1 (congrArg (fun z : Fin (oldTapes source k d)=>z.castAdd 790) he.symm)
    simp only [input,Fin.addCases_left,RecoveryBoundedColdSourceGraph.input,if_neg hh,if_neg hw]
  · intro _
    exact Fin.addCases_right _

end
end NearCubicWires.RepairSource.RecoveryBoundedCold
