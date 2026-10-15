import Proof.PCP.PCPPNativeNodeProjectedInput

/-! The same executed NOT path exposes its complete retained scalar frame
for the enclosing node loop. The machine and its execution budget are the
already checked controller and notBudget. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeNodeMachine
open LocalBitMultitape RepairRepresentation RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem not_retained_run (pre tail queries : List Bool) (index base position C : ℕ) (out : List Bool)
    (hC : PCPPNativeAddressAppend.budget base index+1 ≤ C) :
    ∃ r,runFrom machine (notBudget index base C)
      (entry (PCPPNativeNodeRead.source pre tail 2 index 0) queries pre.length base position C out)=some r ∧
      r.steps ≤ notBudget index base C ∧
      r.final.tapes 0=PCPPNativeNodeRead.source pre tail 2 index 0 ∧
      r.final.heads 0=pre.length+(natWord 2).length+(natWord index).length+(natWord 0).length ∧
      r.final.tapes 5=out++PCPPNativeNotNode.emitted base index ∧
      r.final.heads 5=(out++PCPPNativeNotNode.emitted base index).length ∧
      (∀ i,r.final.heads (fieldSlots false i)=PCPPNativeAddressReusable.heads (out++PCPPNativeNotNode.emitted base index) i ∧
        r.final.tapes (fieldSlots false i)=PCPPNativeAddressReusable.data base index C (out++PCPPNativeNotNode.emitted base index) i) ∧
      (∀ i,(∀ j,readSlots j≠i) → (∀ j,argSlots false j≠i) → (∀ j,fieldSlots false j≠i) →
        r.final.heads i=initialHeads pre.length out i ∧
        r.final.tapes i=initialData (PCPPNativeNodeRead.source pre tail 2 index 0) queries base position C out i) := by
  obtain ⟨a,ha,as,ac,a0,ah0,_,_,a7,ah7,_,_,akeep⟩ := reader_run pre tail queries 2 index 0 base position C out
  have awork (i : Fin 5) (hi : i≠0) : a.final.heads (argSlots false i)=0 ∧ a.final.tapes (argSlots false i)=[] := by
    have k := akeep (argSlots false i) (arg_work_away false i hi).1
    have z := arg_work_initial false i hi (PCPPNativeNodeRead.source pre tail 2 index 0) queries pre.length base position C out
    exact ⟨k.1.trans z.1,k.2.trans z.2⟩
  have ready := argument_input false index a.final.heads a.final.tapes ah7 a7 awork
  obtain ⟨b,hb,bs,bh,_,bt,bkeep⟩ := arg_run false index a.final.heads a.final.tapes ready.1 ready.2
  have fieldReady (i : Fin 24) :
      b.final.heads (fieldSlots false i)=PCPPNativeAddressReusable.heads out i ∧
      b.final.tapes (fieldSlots false i)=PCPPNativeAddressReusable.data base index C out i := by
    by_cases hi : i=1
    · subst i
      exact ⟨bh 1,bt⟩
    · have k := bkeep (fieldSlots false i) (field_arg_away i hi)
      have ar := akeep (fieldSlots false i) (field_read_away false i)
      have ini := initial_field false i hi (PCPPNativeNodeRead.source pre tail 2 index 0) queries pre.length base position index C out
      exact ⟨k.1.trans (ar.1.trans ini.1),k.2.trans (ar.2.trans ini.2)⟩
  obtain ⟨raw,hraw,raws,rawh,rawt⟩ := PCPPNativeNotNode.node_run base index C out hC
  obtain ⟨c,hc,_,cs,ch,ct,ckeep⟩ := RecoveryFocus.dock (fieldSlots false) (field_injective false)
    PCPPNativeNotNode.machine _ b.final.heads b.final.tapes (PCPPNativeNotNode.entry base index C out)
    (fun i => (fieldReady i).1) (fun i => (fieldReady i).2) raw hraw
  have firstCall := call_run 0 4 _ _ _ a ha (parsed_next 2 a.final.control a.final.scanned ac)
  have middleCall := call_run 4 5 _ _ _ b hb (by rfl)
  have finalCall := stop_run 5 _ _ _ c hc (by rfl)
  have full := (firstCall.trans middleCall).trans finalCall
  obtain ⟨result,hresult,rf,rs⟩ := full.run (by simp [machine,RecoveryCalls.machine,RecoveryCalls.stopped])
  have timeBound : (a.steps+1)+(b.steps+1)+(c.steps+1) ≤ notBudget index base C := by
    unfold notBudget
    omega
  have more := runFrom_moreFuel machine _ (notBudget index base C-((a.steps+1)+(b.steps+1)+(c.steps+1))) _ result hresult
  rw [Nat.add_sub_of_le timeBound] at more
  have c0 := ckeep 0 (by decide)
  have b0 := bkeep 0 (by decide)
  refine ⟨result,more,by omega,?_,?_,?_,?_,?_,?_⟩
  · rw [rf]
    exact c0.2.trans (b0.2.trans a0)
  · rw [rf]
    exact c0.1.trans (b0.1.trans ah0)
  · rw [rf]
    exact (ct 20).trans (congrFun rawt 20)
  · rw [rf]
    exact (ch 20).trans (congrFun rawh 20)
  · intro i
    rw [rf]
    exact ⟨(ch i).trans (congrFun rawh i),(ct i).trans (congrFun rawt i)⟩
  · intro i hir hia hif
    rw [rf]
    exact ⟨(ckeep i hif).1.trans ((bkeep i hia).1.trans (akeep i hir).1),
      (ckeep i hif).2.trans ((bkeep i hia).2.trans (akeep i hir).2)⟩

end NearCubicWires.RepairOrdinary.PCPPNativeNodeMachine
