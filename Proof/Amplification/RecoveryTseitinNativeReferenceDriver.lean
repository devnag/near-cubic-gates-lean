import Proof.Amplification.RecoveryTseitinNativeReference
import Proof.Amplification.RecoveryTseitinReferenceDriverCold

/-! Native node preparation retains the actual target-reference capacity
and cleared log for the following ordinary clause-kernel allocation. -/
namespace NearCubicWires.RepairSource.RecoveryTseitinNative
open LocalBitMultitape RepairOrdinary RepairRepresentation RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

private theorem join_all {s t : Nat} (p : Machine 1099 s) (q : Machine 1062 t)
    (fp fq : Nat) (initial : Configuration 1099 s) (data : Fin 1062→List Bool)
    (first : ExecutionReceipt 1099 s) (hf : runFrom p fp initial=some first) (fs : first.steps≤fp)
    (ft : ∀ i,first.final.tapes (referenceSlots i)=data i) (fh : ∀ i,first.final.heads (referenceSlots i)=0)
    (second : ExecutionReceipt 1062 t) (hs : run q fq data=some second) (ss : second.steps≤fq) :
    ∃ r,runFrom (Composition.machine p (RecoveryFocus.machine referenceSlots q)) (fp+1+fq)
      (Composition.leftConfig t initial)=some r ∧ r.steps≤fp+1+fq ∧
      (∀ i,r.final.tapes (referenceSlots i)=second.final.tapes i ∧ r.final.heads (referenceSlots i)=second.final.heads i) ∧
      (∀ i,1062 ≤ i.val → r.final.tapes i=first.final.tapes i ∧ r.final.heads i=first.final.heads i) := by
  obtain ⟨last,hl,_lc,ls,lh,lt,lo⟩:=RecoveryFocus.dock referenceSlots reference_injective q fq
    first.final.heads first.final.tapes _ fh ft second hs
  refine ⟨_,Composition.run_join p (RecoveryFocus.machine referenceSlots q) fp fq initial first last hf hl,
    Nat.add_le_add (Nat.add_le_add_right fs 1) (ls.le.trans ss),fun i=>⟨lt i,lh i⟩,?_⟩
  intro i hi
  have h:=lo i (by
    intro j he
    have hv:=congrArg Fin.val he
    have hj:=j.isLt
    change j.val=i.val at hv
    omega)
  exact ⟨h.2,h.1⟩

theorem references_driver_run (arity index : Nat) (pre tail : List Bool) (tag a b : Nat) :
    ∃ r,runFrom referencesMachine (referencesBudget arity index tag a b)
      ⟨referencesMachine.start,heads pre.length,input arity index (PCPPNativeNodeRead.source pre tail tag a b)⟩=some r ∧
      r.steps≤referencesBudget arity index tag a b ∧
      (∀ k,r.final.tapes (referenceSlots (RecoveryTseitinReferences.referenceSlot k))=
        RecoveryTseitinReferences.fields arity index a b k ∧
        r.final.heads (referenceSlots (RecoveryTseitinReferences.referenceSlot k))=0) ∧
      r.final.tapes 17=List.replicate (RecoveryTseitinTautology.Cold.driverCapacity (arity+index)) true ∧
      r.final.tapes 18=List.replicate (RecoveryTseitinTautology.Cold.driverCapacity (arity+index)+1) false ∧
      r.final.heads 17=0 ∧ r.final.heads 18=0 ∧
      r.final.tapes 1062=PCPPNativeNodeRead.source pre tail tag a b ∧
      r.final.heads 1062=pre.length+(natWord tag).length+(natWord a).length+(natWord b).length ∧
      r.final.tapes 1072=UnaryTemplate.tape tag ∧ r.final.heads 1072=1 ∧
      r.final.tapes 1082=UnaryTemplate.tape a ∧ r.final.heads 1082=1 := by
  obtain ⟨first,hf,fs,fields,f0,fh,ftag,htag,fa,ha⟩:=operands_run arity index pre tail tag a b
  obtain ⟨second,hs,so,sd,sl,sdh,slh,ss⟩:=RecoveryTseitinReferences.cold_driver_run arity index a b
  obtain ⟨r,hr,rs,ro,rkeep⟩:=join_all operandsMachine RecoveryTseitinReferences.coldMachine
    (operandsBudget tag a b) (RecoveryTseitinReferences.coldBudget arity index a b) _
    (RecoveryTseitinReferences.coldInput arity index a b)
    first hf fs (fun i=>(fields i).1) (fun i=>(fields i).2) second hs ss
  exact ⟨r,hr,rs,(fun k=>⟨(ro _).1.trans (so k).1,(ro _).2.trans (so k).2⟩),
    (ro 17).1.trans sd,(ro 18).1.trans sl,(ro 17).2.trans sdh,(ro 18).2.trans slh,
    (rkeep 1062 (by decide)).1.trans f0,(rkeep 1062 (by decide)).2.trans fh,
    (rkeep 1072 (by decide)).1.trans ftag,(rkeep 1072 (by decide)).2.trans htag,
    (rkeep 1082 (by decide)).1.trans fa,(rkeep 1082 (by decide)).2.trans ha⟩

end NearCubicWires.RepairSource.RecoveryTseitinNative
