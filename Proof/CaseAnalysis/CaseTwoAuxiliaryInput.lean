import Proof.CaseAnalysis.CaseTwoAuxiliaryBit

/-! Literal port projections of the checked honest-call entry. This only
unpacks its existing nested tape bank; it changes no input representation. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.AuxiliaryBit
open LocalBitMultitape SourceInterfaces RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem honest_input (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (u : BitInput r.arity) (j : Fin (HonestCall.tapes a)) :
    HonestCall.input a r u j=
      if j.val=0 then frame (pcppInput r) else if j.val=1 then frame (List.ofFn u) else []:=by
  refine Fin.addCases (m:=7) (n:=(HonestCall.program a).tapeCount) (fun k=>?_) (fun k=>?_) j
  · fin_cases k <;>rfl
  · simp only [HonestCall.input,Fin.addCases_right,Fin.val_natAdd]
    simp only [show 7+k.val≠0 by omega,show 7+k.val≠1 by omega,if_false]

theorem input_flat (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (u : BitInput r.arity) (index : ℕ) (j : Fin (tapes a)) : input a r u index j=
      if j.val=0 then frame (pcppInput r) else if j.val=1 then frame (List.ofFn u)
      else if j.val=HonestCall.tapes a then List.replicate index true else []:=by
  have hh : 7 ≤ HonestCall.tapes a:=by unfold HonestCall.tapes;omega
  refine Fin.addCases (m:=HonestCall.tapes a) (n:=3) (fun k=>?_) (fun k=>?_) j
  · have hk : k.val≠HonestCall.tapes a:=Nat.ne_of_lt k.isLt
    simp only [input,Fin.addCases_left,honest_input,Fin.val_castAdd,hk,if_false]
  · simp only [input,Fin.addCases_right,Fin.val_natAdd]
    have h0 : HonestCall.tapes a+k.val≠0:=by omega
    have h1 : HonestCall.tapes a+k.val≠1:=by omega
    simp only [h0,h1,if_false]
    fin_cases k <;>simp

end
end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.AuxiliaryBit
