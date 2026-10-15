import Proof.CaseAnalysis.WitnessFamilyCapacityCall

/-! Any preceding original-input run that retained N attaches the paid
capacity producer directly. Every old tape/head is preserved by the call. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyCapacity.Call
open LocalBitMultitape
open private joined from Proof.CaseAnalysis.RowsCircuitBottomReturned
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def after (E K : ℕ) {t s : ℕ} (p : Machine t s) (source : Fin t):=
  Composition.machine (TapeEmbedding.machine (extra E) p) (machine E K source)

theorem after_run (E K N : ℕ) (hK : 0<K) {t s : ℕ} (p : Machine t s) (source : Fin t)
    (fuel : ℕ) (data : Fin t→List Bool) (cursor : Fin t→ℕ) (prior : ExecutionReceipt t s)
    (hp : runFrom p fuel ⟨p.start,cursor,data⟩=some prior) (hs : prior.steps≤fuel)
    (hd : prior.final.tapes source=List.replicate N true) (hh : prior.final.heads source=0) :
    ∃ actual,runFrom (after E K p source) (fuel+1+FamilyCapacity.budget E K N)
      ⟨(after E K p source).start,heads E cursor,input E data⟩=some actual ∧
      actual.steps≤fuel+1+FamilyCapacity.budget E K N ∧
      (∀ i,actual.final.heads (slots E source i)=0) ∧
      actual.final.tapes (slots E source (FamilyCapacity.pSlot E))=
        List.replicate (FamilyCapacity.value E K N) true ∧
      actual.final.tapes (slots E source (FamilyCapacity.hSlot E))=
        List.replicate (FamilyCapacity.value E K N+1) true ∧
      (∀ i,actual.final.heads (old E i)=prior.final.heads i ∧ actual.final.tapes (old E i)=prior.final.tapes i):=by
  let lifted:=TapeEmbedding.receipt (fun _ : Fin (extra E)=>0) (fun _=>[]) prior
  have first:=TapeEmbedding.run_embed p (fun _ : Fin (extra E)=>0) (fun _=>[]) _ _ prior hp
  obtain ⟨last,lr,ls,lh,lP,lH,keep⟩:=call_run E K N hK source prior.final.tapes prior.final.heads hd hh
  obtain ⟨actual,run,steps,ah,atapes⟩:=joined (TapeEmbedding.machine (extra E) p) (machine E K source)
    fuel (FamilyCapacity.budget E K N) (heads E cursor) (input E data) lifted last first lr hs ls
  refine ⟨actual,run,steps,fun i=>(congrFun ah _).trans (lh i),
    (congrFun atapes _).trans lP,(congrFun atapes _).trans lH,?_⟩
  intro i
  exact ⟨(congrFun ah _).trans (keep i).1,(congrFun atapes _).trans (keep i).2⟩

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyCapacity.Call
