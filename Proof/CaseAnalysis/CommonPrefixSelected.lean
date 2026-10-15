import Proof.CaseAnalysis.CommonPrefixRun

/-! One fixed common prefix on every final input length. Its parameters are
chosen once from the actual weak machine and the selected refuter. All costs
use the existing C.12 table-length envelope, including finite rejected lengths. -/
namespace NearCubicWires.RepairSource.CloseoutCommonPrefix
open LocalBitMultitape RepairOrdinary CloseoutSchedule CloseoutRetainedRefuter
open OrdinaryOracleCompose
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem exists_selected (sources : EightSources) (k D copies cutoff Aw Bw : ℕ)
    (clock : OrdinaryClock (fun n=>n^(k+2))) (hD : 1≤D)
    (M : OrdinaryWeakMachine) (hM : OrdinaryLittleO M (fun n=>n^(k+2))) :
    ∃ onset : ℕ,1≤onset ∧ cutoff≤onset ∧ ∃ (r : OrdinaryOracleProgram) (As Bs C E : ℕ),
      ∀ bits : List Bool,
        let w:=Step.workTapes sources k D
        let H:=sources.hierarchy (fun n=>n^(k+2)) clock
        let N:=Framed.selectedLength (CloseoutLanguage.widthAt sources k clock copies D) bits.length
        let result:=if onset≤N then List.ofFn (H.output M N) else []
        ∃ cost≤C*(2^bits.length+1)^E,∃ out,
          Ready RecoveryOracle.correctedSat (program sources k D copies As Bs onset Aw Bw clock r)
            cost (input w r k bits) out ∧
          out (0 : Fin (tapes w r k))=frame bits ∧
          out (firstSlots w r k (old r (RefuterPrefix.flagPort w)))=[decide (onset≤N)] ∧
          out (prepareSlots w r k (CloseoutCommonPrepare.capacitySlot k))=
            List.replicate (CloseoutCapacity.capacity Aw Bw bits.length) true ∧
          out (prepareSlots w r k (CloseoutCommonPrepare.hierarchySlot k))=
            frame result++frame (H.hierarchy.time result.length).bits ∧
          (onset≤N →
            (M.accepts N (H.output M N) ↔ H.hierarchy.timedView.accepts N (H.output M N)=false) ∧
            ∃ qlen≤C*(2^bits.length+1)^E,
              out (firstSlots w r k (query w r))=List.replicate qlen false):=by
  obtain ⟨onset,honset,hcut,r,As,Bs,C,E,hprefix⟩:=
    RefuterPrefix.exists_selected sources k D copies cutoff clock hD M hM
  let H:=sources.hierarchy (fun n=>n^(k+2)) clock
  let cp:=CloseoutCommonPrepare.coefficient k H.hierarchy.coefficient Aw Bw
  let ep:=CloseoutCommonPrepare.degree Aw
  refine ⟨onset,honset,hcut,r,As,Bs,32*(C+cp*2^ep+1),E+ep+1,?_⟩
  intro bits
  let w:=Step.workTapes sources k D
  let N:=Framed.selectedLength (CloseoutLanguage.widthAt sources k clock copies D) bits.length
  let result:=if onset≤N then List.ofFn (H.output M N) else []
  have hN : N≤2^bits.length:=Framed.selectedLength_bound _ _
  have hlength : result.length≤2^bits.length:=by
    dsimp only [result]
    split_ifs
    · simpa only [List.length_ofFn] using hN
    · simp
  obtain ⟨fuel,hfuel,a,hpre,ha,hflag,hanswer,hquery⟩:=hprefix bits
  obtain ⟨cost,hcost,out,hr,haddress,hW,hword,hkeep⟩:=
    prefix_run sources k D copies As Bs onset Aw Bw clock r bits result fuel a hpre ha hanswer
  have hprep:=CloseoutCommonPrepare.budget_bound k H.hierarchy.coefficient Aw Bw bits result hlength
  have hpower : cp*(2^bits.length+1)^ep≤cp*(2^bits.length+2)^ep:=
    Nat.mul_le_mul_left cp (Nat.pow_le_pow_left (by omega) ep)
  have hbound:=RefuterPrefix.budget_bound C E cp ep bits.length (2^bits.length) (Nat.le_refl _)
  have hsmall : C*(2^bits.length+1)^E≤
      32*(C+cp*2^ep+1)*(2^bits.length+1)^(E+ep+1):=by
    have hnonneg : 0≤16*(cp*(2^bits.length+2)^ep+1)+4:=Nat.zero_le _
    omega
  have htotal : cost≤32*(C+cp*2^ep+1)*(2^bits.length+1)^(E+ep+1):=by
    change CloseoutCommonPrepare.budget k H.hierarchy.coefficient Aw Bw bits result≤
      cp*(2^bits.length+1)^ep at hprep
    change cost≤fuel+CloseoutCommonPrepare.budget k H.hierarchy.coefficient Aw Bw bits result+2 at hcost
    omega
  have hfaddr : old r (RefuterPrefix.flagPort w)≠address w r:=by
    intro he
    exact (Guarded.old_fresh w (Cold.extra w 0) 4) ((old_injective r he).symm)
  have hfanswer:=old_fresh r (RefuterPrefix.flagPort w) 0
  refine ⟨cost,htotal,out,hr,?_,(hkeep _ hfaddr hfanswer).trans hflag,hW,hword,?_⟩
  · simpa only [first_address] using haddress
  · intro hn
    obtain ⟨hconflict,qlen,hqlen,hqt⟩:=hquery hn
    refine ⟨hconflict,qlen,hqlen.trans hsmall,?_⟩
    exact (hkeep (query w r) (query_ne_address w r)
      (bank_fresh r (RefuterPrefix.sourcePort w) (clocked r).queryTape 0)).trans hqt

end
end NearCubicWires.RepairSource.CloseoutCommonPrefix
