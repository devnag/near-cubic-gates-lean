import Proof.CaseAnalysis.CaseTwoOccurrenceAddressLayout

/-! The occurrence address front consumes the literal original cache bank.
The two retained frames and every fresh work tape have explicit entry ports. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.OccurrenceAddress
open LocalBitMultitape SourceInterfaces RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def cache (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity):=
  PCPPQueryIndexPadding.clauseData (pcppOutput r (a.output r)) r.arity 0
    (PCPPQueryCachedBounds.capacity a (r.circuit.size+r.arity)) []

theorem metadata_input (D : ℕ) (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (address : List Bool) (j : Fin 56) :
    input D a r address (metadataSlots D j)=Metadata.input (cache a r) j:=by
  refine Fin.addCases (m:=19) (n:=37) (fun k=>?_) (fun k=>?_) j
  · simp only [metadataSlots,base,input,Fin.val_castAdd,dif_pos k.isLt,
      Metadata.input,Fin.addCases_left,cache]
  · have h19 : ¬19+k.val<19:=by omega
    have h56 : 19+k.val≠56:=by have h:=k.isLt;omega
    have h57 : 19+k.val≠57:=by have h:=k.isLt;omega
    simp only [metadataSlots,base,input,Fin.val_castAdd,Fin.val_natAdd,dif_neg h19,
      h56,h57,if_false,Metadata.input,Fin.addCases_right]

theorem metadata_heads (D : ℕ) (j : Fin 56) :
    heads D (metadataSlots D j)=Metadata.heads PCPPQueryClauseReuse.heads j:=by
  refine Fin.addCases (m:=19) (n:=37) (fun k=>?_) (fun k=>?_) j
  · simp [heads,metadataSlots,base,Metadata.heads,PCPPQueryClauseReuse.heads,Fin.ext_iff]
  · have h13 : 19+k.val≠13:=by omega
    have h14 : 19+k.val≠14:=by omega
    simp only [heads,metadataSlots,base,Fin.val_castAdd,Fin.val_natAdd,h13,h14,
      or_self,if_false,Metadata.heads,Fin.addCases_right]

theorem new_input (D : ℕ) (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (address : List Bool) (i : Fin (tapes D)) (hi : 58 ≤ i.val) : input D a r address i=[]:=by
  simp only [input,dif_neg (show ¬i.val<19 by omega),show i.val≠56 by omega,
    show i.val≠57 by omega,if_false]
theorem new_head (D : ℕ) (i : Fin (tapes D)) (hi : 58 ≤ i.val) : heads D i=0:=by
  simp only [heads,show i.val≠13 by omega,show i.val≠14 by omega,or_self,if_false]
theorem metadata_outside (D : ℕ) (i : Fin (tapes D)) (hi : 56 ≤ i.val) :
    ∀ j,metadataSlots D j≠i:=by
  intro j he
  have h:=congrArg Fin.val he
  have hj:=j.isLt
  simp only [metadataSlots,base,Fin.val_castAdd] at h
  omega
theorem width_outside (D : ℕ) (i : Fin (tapes D))
    (hi : (i.val<58 ∧ i.val≠52 ∧ i.val≠48) ∨ 58+Widths.tapes D ≤ i.val) :
    ∀ j,widthSlots D j≠i:=by
  intro j he
  have h:=congrArg Fin.val he
  have hj:=j.isLt
  dsimp only [widthSlots,base] at h
  split_ifs at h <;>(try simp only [Fin.val_castAdd] at h) <;>omega

end
end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.OccurrenceAddress
