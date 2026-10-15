import Proof.CaseAnalysis.CaseTwoAssignmentMeaning
import Proof.CaseAnalysis.CaseTwoClauseVariable
import Proof.Circuits.OccurrenceSliceTransport

/-! The actual native clause query feeds the original unsigned assignment
worker. The request and actual input/scalar tapes are retained outside the
clause worker, and the assignment's remaining bank is initially empty. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.OccurrenceBit
open LocalBitMultitape SourceInterfaces RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def tapes (a : PointwisePCPPAlgorithm):=84+Assignment.tapes a
def old (a : PointwisePCPPAlgorithm) (j : Fin 84) : Fin (tapes a):=j.castAdd (Assignment.tapes a)
def base (a : PointwisePCPPAlgorithm) (j : Fin 25):=old a (j.castAdd 59)
def variableMap (j : Fin 59) : Fin 84:=
  if h : j.val<19 then ⟨j.val,by omega⟩ else if j.val=56 then 24 else ⟨25+j.val,by omega⟩
def variableSlots (a : PointwisePCPPAlgorithm) (j : Fin 59):=old a (variableMap j)
def assignmentMap : Fin 15 → Fin 84:=![0,1,2,13,15,14,16,17,18,19,20,22,21,82,23]
def assignmentSlots (a : PointwisePCPPAlgorithm) (j : Fin (Assignment.tapes a)) : Fin (tapes a):=
  if h : j.val<15 then old a (assignmentMap ⟨j.val,h⟩) else j.natAdd 84
def queryVariable (a : PointwisePCPPAlgorithm):=RecoveryFocus.machine (variableSlots a) ClauseVariable.machine
def assignment (a : PointwisePCPPAlgorithm):=RecoveryFocus.machine (assignmentSlots a) (Assignment.machine a)
def machine (a : PointwisePCPPAlgorithm):=Composition.machine (queryVariable a) (assignment a)
def named (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (index : Fin (2^(a.output r).clauseBits)) (position : Bool):=
  OccurrenceSliceTransport.occurrenceVariable (a.output r) (index,position)
def cache (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity) (index : ℕ):=
  PCPPQueryClauseReuse.data (pcppOutput r (a.output r)) r.arity index
    (PCPPQueryCachedBounds.capacity a (r.circuit.size+r.arity)) []
def input (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity) (u : BitInput r.arity)
    (index : ℕ) (position : Bool) (j : Fin (tapes a)) : List Bool:=
  if h : j.val<19 then cache a r index ⟨j.val,h⟩
  else if j.val=19 then frame (pcppInput r) else if j.val=20 then frame (List.ofFn u)
  else if j.val=21 then List.ofFn u else if j.val=22 then List.replicate r.arity true
  else if j.val=23 then UnaryTemplate.tape (a.output r).systematicBits
  else if j.val=24 then [position] else []
def heads (a : PointwisePCPPAlgorithm) (j : Fin (tapes a)):=if j.val=13 ∨ j.val=14 then 1 else 0
def outputSlot (a : PointwisePCPPAlgorithm):=assignmentSlots a (Assignment.low a 25)
def budget (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity) (u : BitInput r.arity)
    (index : Fin (2^(a.output r).clauseBits)) (position : Bool):=
  ClauseVariable.budget a r index position+1+Assignment.budget a r u (named a r index position).val

theorem old_injective (a : PointwisePCPPAlgorithm) : Function.Injective (old a):=by
  intro i j he;apply Fin.ext;exact congrArg (fun k : Fin (tapes a)=>k.val) he
theorem variable_val (j : Fin 59) : (variableMap j).val=
    if j.val<19 then j.val else if j.val=56 then 24 else 25+j.val:=by
  unfold variableMap
  split_ifs <;>rfl
theorem variable_map_injective : Function.Injective variableMap:=by
  intro i j he
  have h:=congrArg Fin.val he
  apply Fin.ext
  simp only [variable_val] at h
  split_ifs at h <;>omega
theorem variable_injective (a : PointwisePCPPAlgorithm) : Function.Injective (variableSlots a):=
  (old_injective a).comp variable_map_injective
theorem assignment_injective (a : PointwisePCPPAlgorithm) : Function.Injective (assignmentSlots a):=by
  intro i j he
  have h:=congrArg Fin.val he
  by_cases hi : i.val<15 <;>by_cases hj : j.val<15
  · have hm : assignmentMap ⟨i.val,hi⟩=assignmentMap ⟨j.val,hj⟩:=
      old_injective a (by simpa only [assignmentSlots,dif_pos hi,dif_pos hj] using he)
    have hinj : Function.Injective assignmentMap:=by decide
    apply Fin.ext
    exact congrArg (fun k : Fin 15=>k.val) (hinj hm)
  · have bound:=(assignmentMap ⟨i.val,hi⟩).isLt
    simp only [assignmentSlots,dif_pos hi,dif_neg hj,old,Fin.val_castAdd,Fin.val_natAdd] at h
    omega
  · have bound:=(assignmentMap ⟨j.val,hj⟩).isLt
    simp only [assignmentSlots,dif_neg hi,dif_pos hj,old,Fin.val_castAdd,Fin.val_natAdd] at h
    omega
  · apply Fin.ext
    simp only [assignmentSlots,dif_neg hi,dif_neg hj,Fin.val_natAdd] at h
    omega

theorem literal_index {n : ℕ} (l : Literal n) :
    LiteralFields.index l=(ComponentwiseBranchExtraction.literalIndex l).val:=by
  cases l <;>rfl
theorem selected_named (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (index : Fin (2^(a.output r).clauseBits)) (position : Bool) :
    LiteralIndices.selected ((a.output r).clauses index).left ((a.output r).clauses index).right position=
      (named a r index position).val:=by
  cases position <;>simp [LiteralIndices.selected,named,OccurrenceSliceTransport.occurrenceVariable,
    OccurrenceSliceTransport.occurrenceLiteral,literal_index]

end
end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.OccurrenceBit
