import Proof.CaseAnalysis.CommonProgramSuppliers
import Proof.CaseAnalysis.CaseTwoSelectedOutput

/-! Choose and discharge every local supplier from the eight sources and
the actual weak-machine/refuter theorem. The common onset is chosen once. -/
namespace NearCubicWires.RepairSource.CloseoutCommonProgram
open LocalBitMultitape RepairOrdinary SourceInterfaces CloseoutLanguage OrdinaryOracleCompose
open ProjectionNormalization SelectedRecoveryIntegration RecoveryScheduleEnvelope
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem choose (sources : EightSources) (k : ℕ) (clock : OrdinaryClock (fun n=>n^(k+2)))
    (degree D copies cutoff : ℕ) (hD : 1 ≤ D) (clauses : ClauseReady sources degree D)
    (hcopies : (selectedAmplifier sources.amplification degree).arityCoefficient ≤ copies)
    (M : OrdinaryWeakMachine) (littleO : OrdinaryLittleO M (fun n=>n^(k+2))) :
    ∃ onset,cutoff ≤ onset ∧ ∃ As Bs Aw Bw Aq Bq refuter c,
      Suppliers ⟨sources,k,degree,D,copies,As,Bs,onset,Aw,Bw,Aq,Bq,clock,refuter⟩ M c:=by
  obtain ⟨caseCut,_caseCutPositive,caseRuns⟩:=
    CloseoutCaseTwo.SelectedOutput.selected_polynomial_run sources degree D hD clauses
  have hcopies1:1 ≤ copies:=
    (selectedAmplifier sources.amplification degree).arityCoefficientPositive.trans hcopies
  obtain ⟨twoC,twoE,_twoCPositive,caseRun⟩:=caseRuns k clock copies hcopies1
  let src:=fixedProjection sources
  let H:=(sources.hierarchy (fun n=>n^(k+2)) clock).hierarchy
  let Cpad:=padding sources k clock
  have hc:H.coefficient ≤ Cpad:=Nat.le_max_left _ _
  have hp:k+3 ≤ Cpad:=Nat.le_max_right _ _
  obtain ⟨Aw,Bw,capacity⟩:=CloseoutRecoveryCapacity.actual_capacity_with_source src H Cpad degree hc hp
  obtain ⟨recoveryC,recoveryE,_recoveryPositive,recoveryBound⟩:=
    RecoveryBoundedCold.polynomial_budget src H Cpad degree hc hp
  obtain ⟨onset,honset,hcut,refuter,As,Bs,prefixC,prefixE,prefixRun⟩:=
    CloseoutCommonPrefix.exists_selected sources k D copies (max cutoff caseCut) Aw Bw clock hD M littleO
  obtain ⟨Aq,Bq,query⟩:=CloseoutCommonQueryClear.exists_capacity prefixC prefixE recoveryC recoveryE Aw Bw
  let p : Parameters:=⟨sources,k,degree,D,copies,As,Bs,onset,Aw,Bw,Aq,Bq,clock,refuter⟩
  let c : Constants:=⟨prefixC,prefixE,recoveryC,recoveryE,twoC,twoE⟩
  refine ⟨onset,(Nat.le_max_left cutoff caseCut).trans hcut,As,Bs,Aw,Bw,Aq,Bq,refuter,c,?_⟩
  change Suppliers p M c
  refine ⟨honset,hcopies,?_,?_,?_,?_,query⟩
  · intro bits
    obtain ⟨fuel,hfuel,out,actual,address,flag,rawCapacity,word,liveFields⟩:=prefixRun bits
    refine ⟨fuel,hfuel,out,actual,address,congrArg (fun w=>readTapeBit w 0) flag,?_⟩
    intro live
    obtain ⟨_conflict,padding,hpadding,rawQuery⟩:=liveFields live
    have hlen:=active_length p bits.length honset live
    have hresult : (if onset ≤ length p bits.length then
        List.ofFn ((sources.hierarchy (fun n=>n^(k+2)) clock).output M (length p bits.length)) else [])=
        List.ofFn (selectedWord p M bits.length):=by
      rw [if_pos live,hlen]
      rfl
    change out (prefixRecoveryFields p 0)=
      frame (if onset ≤ length p bits.length then
        List.ofFn ((sources.hierarchy (fun n=>n^(k+2)) clock).output M (length p bits.length)) else [])++
      frame (H.time (if onset ≤ length p bits.length then
        List.ofFn ((sources.hierarchy (fun n=>n^(k+2)) clock).output M (length p bits.length)) else []).length).bits at word
    rw [hresult,List.length_ofFn] at word
    refine ⟨padding,hpadding,?_⟩
    intro j
    fin_cases j
    · exact word
    · exact rawCapacity
    · exact rawQuery
  · intro n point x hN small
    have hcase:caseCut ≤ 2^index p n:=((Nat.le_max_right cutoff caseCut).trans hcut).trans hN
    obtain ⟨answer,actual,value,_word,_desc,_address⟩:=caseRun n point x hcase small
    refine ⟨answer,?_,value⟩
    have hd:=recovery_description p ⟨2^index p n,x⟩ small
    rw [hd]
    exact actual
  · intro n r hn hr
    obtain ⟨hN,hW,_hR,_hQ,_hB,hbytes,htwo⟩:=capacity n r hn hr
    exact ⟨hN,hW,hbytes,htwo⟩
  · intro r W fits
    have hR:=native_width p r
    have hQ:=native_queries p r
    have hP:=native_source p r
    change PCPPNativeHierarchyNodes.width src k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2=R p r at hR
    change PCPPNativeHierarchyNodes.queries src k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2=Q p r at hQ
    change PCPPNativeHierarchyNodes.pcp src k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2=sourcePCP p r at hP
    apply recoveryBound r W fits.length
    · rw [hR,hQ,hP]
      exact fits.workspace
    · rw [hR]
      exact fits.two

end
end NearCubicWires.RepairSource.CloseoutCommonProgram
