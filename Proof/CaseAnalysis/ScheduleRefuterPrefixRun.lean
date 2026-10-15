import Proof.CaseAnalysis.ScheduleRefuterPrefixLayout

/-! Entire finite-branch schedule/refuter continuation. A short input pays
only its actual schedule and canonical false output; the selected refuter is
called only under the computed onset flag, retaining the original address. -/
namespace NearCubicWires.RepairSource.CloseoutSchedule.RefuterPrefix
open LocalBitMultitape RepairOrdinary OrdinaryOracleCompose RecoveryRootRound RecoveryExecution
open CloseoutRetainedRefuter
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem prefix_run {t s fuel refuterBudget : Nat} {o : Nat→Bool}
    (p : Machine t s) (r : OrdinaryOracleProgram) (source flag : Fin t)
    (a b : Fin t→List Bool) (word output : List Bool) (go : Bool)
    (hp : ClockJoin.ReadyRun p fuel a b) (hflag : b flag=[go]) (hword : b source=frame word)
    (hr : go=true → OrdinaryOracleRuns o r word output refuterBudget) :
    ∃ cost≤fuel+16*(refuterBudget+1)+4,∃ out,
      Ready o (program p r source flag) cost (input r a) out ∧
      (∀ i : Fin t,i≠source → out (old r i)=b i) ∧
      out (fresh t r 0)=frame (if go then output else []) ∧
      (go=true → ∃ n≤refuterBudget,
        out (bank r source (clocked r).queryTape)=List.replicate n false):=by
  obtain ⟨c0,hc0,h0⟩:=first_ready (o:=o) p r source a b hp
  cases go
  · obtain ⟨out,ho,hret,hout⟩:=reject_ready (o:=o) r source flag b hflag
    have hnext : ∀ q,next p r source flag 0 q
        (fun i=>readTapeBit (input r b i) 0)=some 2:=by
      intro q
      simp only [next,input_old,hflag]
      rfl
    have ta:=h0.call (ports r source) (pieces p r source flag) 0 (next p r source flag) 0 2 hnext
    have tb:=ho.stop (ports r source) (pieces p r source flag) 0 (next p r source flag) 2
      (by intro q; rfl)
    have ht:=trans ta tb
    have hi : controlConfig (RecoveryCalls.code (fun j=>(pieces p r source flag j).states) 0)
        (initialConfiguration (pieces p r source flag 0).machine (input r a))=
        initialConfiguration (program p r source flag).base.machine (input r a):=rfl
    rw [hi] at ht
    refine ⟨(c0+1)+(1+1),by omega,out,⟨_,ht,?_,fun _=>rfl,rfl⟩,
      fun i _=>hret i,hout,?_⟩
    · simp [program,Ports.program,graph,RecoveryCalls.machine,RecoveryCalls.stopped]
    · intro h
      cases h
  · obtain ⟨c1,hc1,n,hn,out,ho,hret,hout,hquery⟩:=
      retained_run source b word output hword (hr rfl)
    have hnext : ∀ q,next p r source flag 0 q
        (fun i=>readTapeBit (input r b i) 0)=some 1:=by
      intro q
      simp only [next,input_old,hflag]
      rfl
    have ta:=h0.call (ports r source) (pieces p r source flag) 0 (next p r source flag) 0 1 hnext
    have tb:=ho.stop (ports r source) (pieces p r source flag) 0 (next p r source flag) 1
      (by intro q; rfl)
    have ht:=trans ta tb
    have hi : controlConfig (RecoveryCalls.code (fun j=>(pieces p r source flag j).states) 0)
        (initialConfiguration (pieces p r source flag 0).machine (input r a))=
        initialConfiguration (program p r source flag).base.machine (input r a):=rfl
    rw [hi] at ht
    refine ⟨(c0+1)+(c1+1),by omega,out,⟨_,ht,?_,fun _=>rfl,rfl⟩,hret,hout,
      fun _=>⟨n,hn,hquery⟩⟩
    simp [program,Ports.program,graph,RecoveryCalls.machine,RecoveryCalls.stopped]

end
end NearCubicWires.RepairSource.CloseoutSchedule.RefuterPrefix
