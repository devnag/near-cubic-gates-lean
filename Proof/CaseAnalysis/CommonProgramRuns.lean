import Proof.CaseAnalysis.CommonProgramSuppliers
import Proof.CaseAnalysis.CommonProgramInactive

/-! All three paths of the same ordinary oracle program, including every
input length and the paid common query reset. -/
namespace NearCubicWires.RepairSource.CloseoutCommonProgram
open LocalBitMultitape RepairOrdinary SourceInterfaces CloseoutLanguage OrdinaryOracleCompose
open RecoveryRootRound RecoveryChoice
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem runs (p : Parameters) (M : OrdinaryWeakMachine) (c : Constants) (sup : Suppliers p M c)
    (n : ℕ) (point : BitInput n) :
    OrdinaryOracleRuns RecoveryOracle.correctedSat (program p) (List.ofFn point)
      (target p M n point).toNat.bits (runBudget p c (List.ofFn point)):=by
  classical
  obtain ⟨fuel,hfuel,out,prefixRun,address,flag,fields⟩:=sup.prefixRuns (List.ofFn point)
  simp only [List.length_ofFn] at hfuel flag fields
  by_cases live:p.onset ≤ length p n
  · let r:=selectedRequest p M n
    have hs:=((active_iff p n sup.onset).mp live).1
    have hN:=((active_iff p n sup.onset).mp live).2
    have fit:=case_one_live_fits p.sources p.k p.clock p.degree p.copies p.D n
      sup.copies r.2 hs
    have good: Fits p r (CloseoutCapacity.capacity p.Aw p.Bw n):=sup.fits n r fit.2.1 fit.2.2.1
    obtain ⟨padding,hpadding,inputFields⟩:=fields live
    obtain ⟨cost,hcost,final,cold,halt,caseFlag,caseHead,queryBound,queryHead,got,heads⟩:=
      source_recovery p r (CloseoutCapacity.capacity p.Aw p.Bw n) good
    have hcost':cost ≤ c.recoveryC*(CloseoutCapacity.capacity p.Aw p.Bw n+1)^c.recoveryE:=
      hcost.trans (sup.budget r _ good)
    have first:=live_recovery_trace p (List.ofFn point) (hierarchyWord p r)
      (CloseoutCapacity.capacity p.Aw p.Bw n) padding fuel cost out prefixRun
      (flag.trans (decide_eq_true live)) inputFields final cold queryBound
    have htarget:=active_target p M n point sup.onset live
    by_cases small:SmallOracle (globalPCP p) p.degree r.2
    · obtain ⟨answer,actual,answerBit⟩:=sup.two n point r.2 hN small
      have hf:=caseFlag.trans ((caseTwo_true _ _ _).mpr small)
      obtain ⟨lastCost,hlast,result,lastRun,lastHalt,lastOutput⟩:=two_branch p (List.ofFn point)
        (hierarchyWord p r) (recoveryDescription p r) (R p r) (B p r) padding
        (c.twoC*(2^n+1)^c.twoE) out final halt hf caseHead address got heads answer actual
      refine ⟨fuel+1+cost+lastCost,result,?_,trans first lastRun,lastHalt,?_⟩
      · dsimp only [runBudget]
        simp only [List.length_ofFn]
        omega
      · exact (lastOutput.trans answerBit).trans
          (congrArg (fun b : Bool=>frame b.toNat.bits) htarget.symm)
    · have hquery : ((recovered p (List.ofFn point) out padding final).tapes (ports p).queryTape).length ≤
          CloseoutCapacity.capacity p.Aq p.Bq (List.ofFn point).length:=by
        rw [recovered_query_length,List.length_ofFn]
        exact (max_le_max hpadding (queryBound.trans hcost')).trans (sup.query n)
      obtain ⟨oneCost,hone,answer,actual,answerBit⟩:=selected_case_one_header_live
        p.sources p.k p.clock p.degree p.copies p.D sup.copies point r.2 hs small
      have hf:readTapeBit (final.tapes (recoveryFlagLocal p)) 0=false:=
        caseFlag.trans (by simp only [caseTwo,decide_eq_false small])
      obtain ⟨lastCost,hlast,result,lastRun,lastHalt,lastOutput⟩:=one_branch p (List.ofFn point)
        (hierarchyWord p r) padding oneCost out final halt hf caseHead address (got 0) (heads 0)
        queryHead hquery answer actual
      refine ⟨fuel+1+cost+lastCost,result,?_,trans first lastRun,lastHalt,?_⟩
      · change oneCost ≤ oneCoefficient p*(2^n+1)^oneExponent p at hone
        dsimp only [runBudget]
        simp only [List.length_ofFn] at hlast ⊢
        omega
      · exact (lastOutput.trans answerBit).trans
          (congrArg (fun b : Bool=>frame b.toNat.bits) htarget.symm)
  · obtain ⟨answer,actual,hout⟩:=inactive_ready p (List.ofFn point) fuel out prefixRun
      (flag.trans (decide_eq_false live))
    obtain ⟨final,trace,halt,_heads,tapes⟩:=actual
    refine ⟨fuel+6,final,?_,trace,halt,?_⟩
    · dsimp only [runBudget]
      simp only [List.length_ofFn]
      omega
    · exact ((congrFun tapes _).trans hout).trans
        (congrArg (fun b : Bool=>frame b.toNat.bits) (inactive_target p M n point sup.onset live).symm)

end
end NearCubicWires.RepairSource.CloseoutCommonProgram
