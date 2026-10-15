import Proof.CaseAnalysis.RetainedRefuterLayout

/-! A whole paid refuter call on the schedule's already-framed request,
preserving every other old tape and restoring the shared query to false.
This is the strong endpoint needed by the two-case common-language program. -/
namespace NearCubicWires.RepairSource.CloseoutRetainedRefuter
open LocalBitMultitape RepairOrdinary OrdinaryOracleCompose RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem retained_run {t budget : Nat} {o : Nat→Bool} {p : OrdinaryOracleProgram}
    (source : Fin t) (ambient : Fin t→List Bool) (word output : List Bool)
    (hs : ambient source=frame word) (hr : OrdinaryOracleRuns o p word output budget) :
    ∃ cost≤16*(budget+1),∃ n≤budget,∃ out,
      Ready o (program p source) cost (input p ambient) out ∧
      (∀ i : Fin t,i≠source → out (old p i)=ambient i) ∧
      out (fresh t p 0)=frame output ∧
      out (bank p source (clocked p).queryTape)=List.replicate n false := by
  obtain ⟨cost,n,final,hcost,hn,htrace,hhalt,hout,hheads,hclock,_,hquery,hwidth⟩:=clocked_runs hr
  let start:=input p ambient
  let a:=install (bank p source) start final.tapes
  have hin (j : Fin (clocked p).base.tapeCount) :
      start (bank p source j)=(clocked p).base.inputTapes word j:=by
    by_cases hz:j.val=0
    · simpa [start,input,bank,hz,old,source.isLt,Program.inputTapes] using hs
    · simp [start,input,bank,hz,Program.inputTapes,show ¬t+j.val<t by omega]
  have ra : Ready o ((ports p source).program (pieces p source 0)) (cost+n+2) start a:=
    Ready.focus ⟨final,htrace,hhalt,hheads,rfl⟩ (ports p source) (bank p source)
      (bank_injective p source) rfl start hin
  have abank (j : Fin (clocked p).base.tapeCount) : a (bank p source j)=final.tapes j:=
    install_slot _ (bank_injective p source) _ _ j
  have afresh (j : Fin 3) : a (fresh t p j)=[]:=by
    rw [show a (fresh t p j)=start (fresh t p j) from
      install_other _ _ _ _ (fun i=>bank_fresh p source i j)]
    simp [start,input,fresh,show ¬t+(clocked p).base.tapeCount+j.val<t by omega]
  have aold (i : Fin t) (hi : i≠source) : a (old p i)=ambient i:=by
    rw [show a (old p i)=start (old p i) from
      install_other _ _ _ _ (fun j=>bank_old p source i hi j)]
    simp [start,input,old,i.isLt]
  let b:=Function.update (Function.update a (fresh t p 0) (frame output))
    (fresh t p 1) (List.replicate (2*output.length+1) false)
  have rb : Ready o ((ports p source).program (pieces p source 1)) (4*output.length+4) a b:=by
    apply Ready.ordinary (ports p source)
    exact OrdinaryOracleCompose.copy_ready (copySlots p source) (copy_injective p source) a output []
      (by simpa [copySlots] using (abank (clocked p).base.outputTape).trans hout)
      (afresh 0) (afresh 1)
  have bbank (j : Fin (clocked p).base.tapeCount) : b (bank p source j)=final.tapes j:=by
    simp only [b,Function.update_apply,bank_fresh,if_false]
    exact abank j
  have bfresh : b (fresh t p 2)=[]:=by
    have h20 : fresh t p 2≠fresh t p 0:=fun h=>(by decide : (2 : Fin 3)≠0) (fresh_injective t p h)
    have h21 : fresh t p 2≠fresh t p 1:=fun h=>(by decide : (2 : Fin 3)≠1) (fresh_injective t p h)
    simp only [b,Function.update_apply,h20,h21,if_false]
    exact afresh 2
  let c:=Function.update (Function.update b (bank p source (clocked p).queryTape)
    (List.replicate n false)) (fresh t p 2) (List.replicate (n+1) false)
  have rc : Ready o ((ports p source).program (pieces p source 2)) (2*n+4) b c:=by
    apply Ready.ordinary (ports p source)
    exact OrdinaryOracleCompose.clear_ready (clearSlots p source) (clear_injective p source) b n
      (by simpa [clearSlots,bbank] using hquery)
      ((bbank (clockTape p)).trans hclock) bfresh
  have ta:=ra.call (ports p source) (pieces p source) 0 (next p source) 0 1 (by intro q; rfl)
  have tb:=rb.call (ports p source) (pieces p source) 0 (next p source) 1 2 (by intro q; rfl)
  have tc:=rc.stop (ports p source) (pieces p source) 0 (next p source) 2 (by intro q; rfl)
  have ht:=trans ta (trans tb tc)
  have hstart : controlConfig (RecoveryCalls.code (fun j=>(pieces p source j).states) 0)
      (initialConfiguration (pieces p source 0).machine start)=
      initialConfiguration (program p source).base.machine start:=rfl
  rw [hstart] at ht
  refine ⟨(cost+n+2+1)+((4*output.length+4+1)+(2*n+4+1)),?_,n,hn.trans hcost,c,
    ⟨_,ht,?_,fun _=>rfl,rfl⟩,?_,?_,?_⟩
  · simp only [frame_length] at hwidth
    omega
  · simp [program,Ports.program,graph,RecoveryCalls.machine,RecoveryCalls.stopped]
  · intro i hi
    have hq : old p i≠bank p source (clocked p).queryTape:=(bank_old p source i hi _).symm
    simp only [c,b,Function.update_apply,old_fresh,hq,if_false]
    exact aold i hi
  · have h02 : fresh t p 0≠fresh t p 2:=fun h=>(by decide : (0 : Fin 3)≠2) (fresh_injective t p h)
    have h01 : fresh t p 0≠fresh t p 1:=fun h=>(by decide : (0 : Fin 3)≠1) (fresh_injective t p h)
    have hq : fresh t p 0≠bank p source (clocked p).queryTape:=(bank_fresh p source _ 0).symm
    simp [c,b,h02,h01,hq]
  · simp [c,bank_fresh]

end
end NearCubicWires.RepairSource.CloseoutRetainedRefuter
