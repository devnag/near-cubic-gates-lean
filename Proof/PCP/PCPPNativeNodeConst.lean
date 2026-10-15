import Proof.PCP.PCPPNativeNodeDock

/-! The complete constant-node path in the fixed 119-tape controller:
original three native fields, real tag/Boolean dispatch, exact two-node
output, and the controller's actual halted state. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeNodeMachine
open LocalBitMultitape RepairRepresentation RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def constBudget (b : Bool) := PCPPNativeNodeClassify.budget 0 b.toNat 0+(b.toNat+1)+(constBits false b).length+3

theorem const_run (pre tail queries : List Bool) (b : Bool) (base position C : ℕ) (out : List Bool) :
    ∃ r,runFrom machine (constBudget b)
      (entry (PCPPNativeNodeRead.source pre tail 0 b.toNat 0) queries pre.length base position C out)=some r ∧
      r.steps ≤ constBudget b ∧
      r.final.tapes 0=PCPPNativeNodeRead.source pre tail 0 b.toNat 0 ∧
      r.final.heads 0=pre.length+(natWord 0).length+(natWord b.toNat).length+(natWord 0).length ∧
      r.final.tapes 5=out++constBits false b ∧ r.final.heads 5=(out++constBits false b).length ∧
      (∀ i,(∀ j,readSlots j≠i) → i≠5 →
        r.final.heads i=initialHeads pre.length out i ∧
        r.final.tapes i=initialData (PCPPNativeNodeRead.source pre tail 0 b.toNat 0) queries base position C out i) := by
  obtain ⟨a,ha,as,ac,a0,ah0,_,_,a7,ah7,_,_,akeep⟩ := reader_run pre tail queries 0 b.toNat 0 base position C out
  let tag : Fin 5 := ⟨b.toNat,by cases b <;> decide⟩
  obtain ⟨br,hbr,bs,bc,bkeep⟩ := tag_run 7 tag a.final.heads a.final.tapes ah7 a7
  have outHead : br.final.heads 5=out.length := by
    rw [(bkeep 5 (by decide)).1,(akeep 5 (by decide)).1]
    rfl
  have outTape : br.final.tapes 5=out := by
    rw [(bkeep 5 (by decide)).2,(akeep 5 (by decide)).2]
    rfl
  obtain ⟨c,hc,cs,ch,ct,ckeep⟩ := literal_run (constBits false b) out br.final.heads br.final.tapes outHead outTape
  have firstCall : Timed machine (a.steps+1)
      (entry (PCPPNativeNodeRead.source pre tail 0 b.toNat 0) queries pre.length base position C out)
      (boundary 1 a.final.heads a.final.tapes) :=
    call_run 0 1 _ _ _ a ha (parsed_next 0 a.final.control a.final.scanned ac)
  have full : Timed machine ((a.steps+1)+(br.steps+1)+(c.steps+1))
      (entry (PCPPNativeNodeRead.source pre tail 0 b.toNat 0) queries pre.length base position C out)
      (RecoveryCalls.stopped sizes c.final.heads c.final.tapes) := by
    cases b
    · have middleCall := call_run 1 2 _ _ _ br hbr (by
        change next 1 br.final.control br.final.scanned=some 2
        simp only [next,bc,tag,Bool.toNat_false,Nat.zero_add,ite_true]
        rfl)
      have finalCall := stop_run 2 _ _ _ c hc (by rfl)
      exact (firstCall.trans middleCall).trans finalCall
    · have middleCall := call_run 1 3 _ _ _ br hbr (by
        change next 1 br.final.control br.final.scanned=some 3
        simp only [next,bc,tag,Bool.toNat_true,show 1+5=6 by omega,show ¬(6:ℕ)=5 by omega,ite_false,ite_true]
        rfl)
      have finalCall := stop_run 3 _ _ _ c hc (by rfl)
      exact (firstCall.trans middleCall).trans finalCall
  obtain ⟨result,hresult,rf,rs⟩ := full.run (by simp [machine,RecoveryCalls.machine,RecoveryCalls.stopped])
  have timeBound : (a.steps+1)+(br.steps+1)+(c.steps+1) ≤ constBudget b := by
    unfold constBudget
    change br.steps=b.toNat+1 at bs
    omega
  have more := runFrom_moreFuel machine _
    (constBudget b-((a.steps+1)+(br.steps+1)+(c.steps+1))) _ result hresult
  rw [Nat.add_sub_of_le timeBound] at more
  refine ⟨result,more,by omega,?_,?_,?_,?_,?_⟩
  · rw [rf]
    change c.final.tapes 0=_
    rw [(ckeep 0 (by decide)).2,(bkeep 0 (by decide)).2]
    exact a0
  · rw [rf]
    change c.final.heads 0=_
    rw [(ckeep 0 (by decide)).1,(bkeep 0 (by decide)).1]
    exact ah0
  · rw [rf]; exact ct
  · rw [rf]; exact ch
  · intro i hi h5
    have h7 : i≠7 := by intro he; subst i; exact hi 20 rfl
    rw [rf]
    change c.final.heads i=_ ∧ c.final.tapes i=_
    exact ⟨(ckeep i h5).1.trans ((bkeep i h7).1.trans (akeep i hi).1),
      (ckeep i h5).2.trans ((bkeep i h7).2.trans (akeep i hi).2)⟩

end NearCubicWires.RepairOrdinary.PCPPNativeNodeMachine
