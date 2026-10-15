import Proof.CaseAnalysis.WitnessMassCapacity
import Proof.CaseAnalysis.RowsGateSourceCalls

/-! The combined term verdict is folded before either exit. True commits
the same coefficient; false only clears the parser. No rejected term reaches
mass arithmetic or retained-record emission. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.TermExit
open LocalBitMultitape RecoveryRootRound RecoveryExecution SignedSortKey CompetitorSumFold
open CompetitorValidity (Estimate)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def flagSlots : Fin 2→Fin 827:=![719,724]
noncomputable def foldFlag:=RecoveryFocus.machine flagSlots CloseoutRowsIntegerRound.flagMachine
private def stateCount {s : ℕ} (_ : Machine 827 s):=s
noncomputable def sizes : Fin 3→ℕ:=![2,stateCount TermCommit.machine,stateCount TermCommit.erase]
noncomputable def programs : (j : Fin 3)→Machine 827 (sizes j)
  | 0=>foldFlag
  | 1=>TermCommit.machine
  | 2=>TermCommit.erase
def next (j : Fin 3) (_ : Fin (sizes j)) (bits : Fin 827→Bool) : Option (Fin 3):=
  if j.val=0 then if bits 719 then some 1 else some 2 else none
noncomputable def machine:=RecoveryCalls.machine sizes programs 0 next

theorem flag_run (P position : ℕ) (out : List Bool) (flag : Bool)
    (terms : Fin 725→List Bool) (ambient : Fin 94→List Bool) (hf : terms 724=[flag]) :
    CloseoutRowsGatePairHeads.ReadyAt foldFlag 1 (TermCommit.heads position out)
      (TermCommit.data P terms ambient out)
      (TermCommit.data P (Function.update terms 724 [flag && readTapeBit (terms 719) 0]) ambient out):=by
  let tapes:=TermCommit.data P terms ambient out
  obtain ⟨r,hr,rh,rt,rs⟩:=(CloseoutRowsIntegerRound.flag_ready (terms 719) flag).focus_at
    flagSlots (by decide) (TermCommit.heads position out) tapes
    (by intro i;fin_cases i
        · exact TermCommit.data_core P terms ambient out 719
        · exact (TermCommit.data_core P terms ambient out 724).trans hf)
    (by intro i;fin_cases i <;> rfl)
  refine ⟨r,hr,?_,rh,rs.le⟩
  rw [rt,←SumFinish.data_update]
  funext i
  by_cases h724:i=724
  · subst i
    rw [Function.update_self]
    exact install_slot flagSlots (by decide) tapes _ 1
  rw [Function.update_of_ne h724]
  by_cases h719:i=719
  · subst i
    exact (install_slot flagSlots (by decide) tapes _ 0).trans
      (TermCommit.data_core P terms ambient out 719).symm
  · exact install_other flagSlots tapes _ i (by
      intro j;fin_cases j
      · exact Ne.symm h719
      · exact Ne.symm h724)

theorem branch_run (takeCommit : Bool) (fuel : ℕ) (heads : Fin 827→ℕ)
    (input middle : Fin 827→List Bool)
    (first : CloseoutRowsGatePairHeads.ReadyAt foldFlag 1 heads input middle)
    (hbit : readTapeBit (middle 719) (heads 719)=takeCommit)
    (last : ExecutionReceipt 827 (sizes (if takeCommit then 1 else 2)))
    (hrun : runFrom (programs (if takeCommit then 1 else 2)) fuel
      (RecoveryCalls.restarted (programs (if takeCommit then 1 else 2)) heads middle)=some last) :
    ∃ result,runFrom machine (fuel+3) (RecoveryCalls.restarted machine heads input)=some result ∧
      result.final.heads=last.final.heads ∧ result.final.tapes=last.final.tapes ∧ result.steps≤fuel+3:=by
  obtain ⟨base,hb,bt,bh,_bs⟩:=first
  have scan:base.final.scanned 719=takeCommit:=by
    change readTapeBit (base.final.tapes 719) (base.final.heads 719)=_
    rw [bt,bh]
    exact hbit
  obtain ⟨u,hu,ht⟩:=call_receipt sizes programs 0 next 0 (if takeCommit then 1 else 2) 1 _ base hb (by
    change (if base.final.scanned 719 then some (1 : Fin 3) else some 2)=some (if takeCommit then 1 else 2)
    rw [scan]
    cases takeCommit <;> rfl)
  rw [bh,bt] at ht
  obtain ⟨v,hv,tail⟩:=stop_receipt sizes programs 0 next (if takeCommit then 1 else 2) fuel _ last hrun
    (by cases takeCommit <;> rfl)
  obtain ⟨r,hr,rf,rs⟩:=(ht.trans tail).run (by simp [RecoveryCalls.machine,RecoveryCalls.stopped])
  have hbound:u+v≤fuel+3:=by omega
  have more:=runFrom_moreFuel machine (u+v) (fuel+3-(u+v)) _ r hr
  rw [Nat.add_sub_of_le hbound] at more
  exact ⟨r,more,by rw [rf];rfl,by rw [rf];rfl,rs.le.trans hbound⟩

theorem changed_extra (P : ℕ) (source : List Bool) (old flag : Bool)
    (terms : Fin 725→List Bool)
    (h : ∀ i,terms (i.natAdd 720)=TermRead.extra P source old i) (i : Fin 5) :
    Function.update terms 724 [flag] (i.natAdd 720)=TermRead.extra P source flag i:=by
  fin_cases i
  · change Function.update terms 724 [flag] 720=_
    rw [Function.update_of_ne (by decide)];exact h 0
  · change Function.update terms 724 [flag] 721=_
    rw [Function.update_of_ne (by decide)];exact h 1
  · change Function.update terms 724 [flag] 722=_
    rw [Function.update_of_ne (by decide)];exact h 2
  · change Function.update terms 724 [flag] 723=_
    rw [Function.update_of_ne (by decide)];exact h 3
  · change Function.update terms 724 [flag] 724=[flag]
    exact Function.update_self _ _ _

theorem reject_run (P b position : ℕ) (source out : List Bool) (flag : Bool)
    (terms : Fin 725→List Bool) (ambient : Fin 94→List Bool) (hP : 1≤P)
    (hfalse : readTapeBit (terms 719) 0=false)
    (hbound : ∀ i : Fin 719,(terms (TermRead.scratchSlots i)).length≤P)
    (hwidth : terms 149=ZeroPadding.pad P (List.replicate b true))
    (hextra : ∀ i,terms (i.natAdd 720)=TermRead.extra P source flag i) : ∃ result,
    runFrom machine (2*P+7)
      ⟨machine.start,TermCommit.heads position out,TermCommit.data P terms ambient out⟩=some result ∧
      result.steps≤2*P+7 ∧ result.final.heads=TermCommit.heads position out ∧
      result.final.tapes=TermCommit.data P (TermRead.data P b [] source false) ambient out:=by
  let changed:=Function.update terms 724 [false]
  have first:=flag_run P position out flag terms ambient (hextra 4)
  rw [hfalse,Bool.and_false] at first
  obtain ⟨last,hl,ls,lh,lt⟩:=TermCommit.erase_run P b position source out false changed ambient hP
    (by intro i
        have hv:=TermRead.scratch_small i
        rw [show changed=Function.update terms 724 [false] by rfl,
          Function.update_of_ne (by apply Fin.ne_of_val_ne;omega)]
        exact hbound i)
    (by rw [show changed=Function.update terms 724 [false] by rfl,Function.update_of_ne (by decide)];exact hwidth)
    (changed_extra P source flag false terms hextra)
  have bit:readTapeBit (TermCommit.data P changed ambient out 719) (TermCommit.heads position out 719)=false:=by
    change readTapeBit (TermCommit.data P changed ambient out (TermCommit.eraseSlots 719)) 0=false
    rw [TermCommit.data_core,show changed=Function.update terms 724 [false] by rfl,
      Function.update_of_ne (by decide)]
    exact hfalse
  obtain ⟨r,hr,rh,rt,rs⟩:=branch_run false (2*P+4) (TermCommit.heads position out)
    (TermCommit.data P terms ambient out) (TermCommit.data P changed ambient out) first bit last hl
  have ht:2*P+4+3=2*P+7:=by omega
  rw [ht] at hr rs
  exact ⟨r,hr,rs,rh.trans lh,rt.trans lt⟩

theorem accept_run (P B b position : ℕ) (q : ℚ) (a : Estimate)
    (bits source out : List Bool) (flag : Bool) (terms : Fin 725→List Bool) (ambient : Fin 94→List Bool)
    (htrue : readTapeBit (terms 719) 0=true) (hstore : Store B a [] ambient) (ha : a.Valid B)
    (hb : b≤B) (hn : q.num.natAbs<2^b) (hd : q.den<2^b)
    (hdecode : CanonicalWitnessCodec.decodeCanonicalRational (RadixSemantics.value bits)=some q)
    (hnum : terms 690=ZeroPadding.pad P (frame (binary b q.num.natAbs)))
    (hden : terms 693=ZeroPadding.pad P (frame (binary b q.den)))
    (hsign : terms 316=ZeroPadding.pad P (frame (RecoveryFixedUnpair.leftWord (RationalCold.numeratorWord bits))))
    (hwidth : terms 149=ZeroPadding.pad P (List.replicate b true))
    (hextra : ∀ i,terms (i.natAdd 720)=TermRead.extra P source flag i)
    (hbound : ∀ i : Fin 719,(terms (TermRead.scratchSlots i)).length≤P)
    (hcap : MassStep.budget B+1≤P) (hbits : 2*b+1≤P) (hnative : CompetitorReusableDecision.capacity B+1≤P) :
    ∃ next result,runFrom machine (TermCommit.budget P B b+3)
      ⟨machine.start,TermCommit.heads position out,TermCommit.data P terms ambient out⟩=some result ∧
      result.steps≤TermCommit.budget P B b+3 ∧
      result.final.heads=TermCommit.heads position (out++TermRecord.word b q) ∧
      result.final.tapes=TermCommit.data P (TermRead.data P b [] source flag) next (out++TermRecord.word b q) ∧
      Store B (CompetitorRationalNumerators.add a (Mass.magnitude q)) [] next:=by
  have first:=flag_run P position out flag terms ambient (hextra 4)
  rw [htrue,Bool.and_true] at first
  have unchanged:Function.update terms 724 [flag]=terms:=by
    have h:=hextra 4
    change terms 724=[flag] at h
    rw [←h]
    exact Function.update_eq_self _ _
  rw [unchanged] at first
  obtain ⟨next,last,hl,ls,lh,lt,store⟩:=TermCommit.commit_run P B b position q a bits source out flag terms ambient
    hstore ha hb hn hd hdecode hnum hden hsign hwidth hextra hbound hcap hbits
    (MassCapacity.prepare_length P B b q.num.natAbs q.den a ambient hstore hnative hbits)
  have bit:readTapeBit (TermCommit.data P terms ambient out 719) (TermCommit.heads position out 719)=true:=by
    change readTapeBit (TermCommit.data P terms ambient out (TermCommit.eraseSlots 719)) 0=true
    rw [TermCommit.data_core]
    exact htrue
  obtain ⟨r,hr,rh,rt,rs⟩:=branch_run true (TermCommit.budget P B b) (TermCommit.heads position out)
    (TermCommit.data P terms ambient out) (TermCommit.data P terms ambient out) first bit last hl
  exact ⟨next,r,hr,rs,rh.trans lh,rt.trans lt,store⟩

end NearCubicWires.RepairOrdinary.CloseoutWitness.TermExit
