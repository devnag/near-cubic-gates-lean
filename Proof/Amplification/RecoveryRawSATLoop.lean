import Proof.Amplification.RecoveryRawSATSemantics

/-! The physical outer-count driver repeats the actual clause body. Each
successful return retains one common valuation and the decoded code tail. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRawSATLoop
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRawSAT
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable abbrev bodySize := Fintype.card (RecoveryCalls.Control RecoveryRawSAT.sizes)
def accepted (_ : Fin bodySize) (scanned : Fin 70→Bool) := scanned 27
noncomputable def source (x : State) := x.cfg RecoveryRawSAT.machine.start
noncomputable def machine := RepeatMachine.machine RecoveryRawSAT.machine accepted
def budget (width total : Nat) := total*(RecoveryRawSAT.budget width+3)+3

open private successful_cfg_eq from Proof.PCP.VerifierDecodingRejectingRepeat

theorem driver_run (width cap committed count : Nat) (word : List Bool)
    (n total pos : Nat) (x : State) (hx : Inv width cap committed count word x)
    (hn : pos+n=total) :
    ∃ r,runFrom machine (n*(RecoveryRawSAT.budget width+2)+total+3)
        (RepeatMachine.cfg 0 (source x) total (pos+1))=some r ∧
      r.steps ≤ n*(RecoveryRawSAT.budget width+2)+total+3 ∧
      r.final.control=RepeatMachine.phaseCode bodySize
        (if prefixCheck (clauseCheck width cap committed count word) n x.code then 3 else 4) ∧
      r.final.heads 27=0 ∧ (∃ bit,r.final.tapes 27=[bit]) ∧
      (prefixCheck (clauseCheck width cap committed count word) n x.code=true → ∃ out : State,
        r.final=RepeatMachine.cfg 3 (source out) total 1 ∧ Inv width cap committed count word out ∧
        out.code=tailCode n x.code) := by
  induction n generalizing pos x with
  | zero=>
    have hpos : pos=total := by omega
    subst pos
    obtain ⟨r,hr,hf,hs⟩ := (RepeatMachine.exhaust RecoveryRawSAT.machine accepted (source x) total).run
      (by simp [RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])
    refine ⟨r,by simpa only [machine,Nat.zero_mul,Nat.zero_add] using hr,by simpa using hs.le,?_,?_,?_,?_⟩
    · rw [hf]; rfl
    · rw [hf]; rfl
    · exact ⟨x.clause.result,by rw [hf]; rfl⟩
    · intro _
      exact ⟨x,hf,hx,rfl⟩
  | succ n ih=>
    have hrun := RecoveryRawSAT.body_run x word hx.valid
    obtain ⟨r,hr,hrb,hrh,hrt,hgood⟩ := hrun
    rw [hx.width_eq] at hr hrb
    have ha : accepted r.final.control r.final.scanned=answer x word := by
      simp only [accepted,Configuration.scanned,hrh,hrt,readTapeBit]
      rfl
    have hstep := RepeatMachine.iteration RecoveryRawSAT.machine accepted (source x) total pos r rfl (by omega) hr
    rw [ha] at hstep
    cases hanswer : answer x word
    · have hcheck : prefixCheck (clauseCheck width cap committed count word) (n+1) x.code=false := by
        rw [prefixCheck,←answer_inv width cap committed count word x hx,hanswer]
        rfl
      simp only [hanswer,Bool.false_eq_true,if_false] at hstep
      obtain ⟨result,hrun,hfinal,hsteps⟩ := hstep.run
        (by simp [RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])
      have htime : r.steps+2 ≤ (n+1)*(RecoveryRawSAT.budget width+2)+total+3 := by nlinarith only [hrb]
      have hm := runFrom_moreFuel machine (r.steps+2)
        ((n+1)*(RecoveryRawSAT.budget width+2)+total+3-(r.steps+2)) _ result hrun
      rw [Nat.add_sub_of_le htime] at hm
      refine ⟨result,hm,hsteps.le.trans htime,?_,?_,?_,?_⟩
      · rw [hfinal,hcheck]; rfl
      · rw [hfinal]
        change r.final.heads 27=0
        exact hrh 27
      · refine ⟨answer x word,?_⟩
        rw [hfinal]
        exact hrt
      · simp only [hcheck,Bool.false_eq_true,IsEmpty.forall_iff]
    · obtain ⟨out,hout⟩ := hgood hanswer
      have hy := accepted_inv width cap committed count word x hx out
      have hcode := accepted_code x word out hanswer
      have hcheck : prefixCheck (clauseCheck width cap committed count word) (n+1) x.code=
          prefixCheck (clauseCheck width cap committed count word) n out.data.code := by
        rw [prefixCheck,←answer_inv width cap committed count word x hx,hanswer,Bool.true_and,hcode]
      simp only [hanswer,if_true] at hstep
      have hh : r.final.heads=(source out.data).heads := funext hrh
      have ht : r.final.tapes=(source out.data).tapes := hout
      have he := successful_cfg_eq r.final (source out.data) total (pos+2) hh ht
      rw [he] at hstep
      obtain ⟨tail,htail,htb,htphase,hth,htt,htout⟩ := ih (pos+1) out.data hy (by omega)
      rcases hstep with ⟨space,hstep⟩
      obtain ⟨result,hrun,hfinal,hsteps,_⟩ := hstep.followedBy tail htail
      have htime : (r.steps+2)+(n*(RecoveryRawSAT.budget width+2)+total+3) ≤
          (n+1)*(RecoveryRawSAT.budget width+2)+total+3 := by nlinarith only [hrb]
      have hm := runFrom_moreFuel machine _
        ((n+1)*(RecoveryRawSAT.budget width+2)+total+3-((r.steps+2)+(n*(RecoveryRawSAT.budget width+2)+total+3))) _ result hrun
      rw [Nat.add_sub_of_le htime] at hm
      refine ⟨result,hm,?_,?_,?_,?_,?_⟩
      · rw [hsteps]; nlinarith only [hrb,htb]
      · rw [hfinal,hcheck]; exact htphase
      · rw [hfinal]; exact hth
      · rw [hfinal]; exact htt
      · intro hall
        rw [hcheck] at hall
        obtain ⟨last,hf,hv,ht⟩ := htout hall
        refine ⟨last,hfinal.trans hf,hv,?_⟩
        rw [ht,hcode]
        rfl

theorem loop_run (width cap committed count total : Nat) (word : List Bool)
    (x : State) (hx : Inv width cap committed count word x) :
    ∃ r,runFrom machine (budget width total) (RepeatMachine.cfg 0 (source x) total 1)=some r ∧
      r.steps ≤ budget width total ∧
      r.final.control=RepeatMachine.phaseCode bodySize
        (if prefixCheck (clauseCheck width cap committed count word) total x.code then 3 else 4) ∧
      r.final.heads 27=0 ∧ (∃ bit,r.final.tapes 27=[bit]) ∧
      (prefixCheck (clauseCheck width cap committed count word) total x.code=true → ∃ out : State,
        r.final=RepeatMachine.cfg 3 (source out) total 1 ∧ Inv width cap committed count word out ∧
        out.code=tailCode total x.code) := by
  have h := driver_run width cap committed count word total total 0 x hx (by omega)
  have he : total*(RecoveryRawSAT.budget width+2)+total+3=budget width total := by unfold budget; ring
  simpa only [he,Nat.zero_add] using h

end NearCubicWires.RepairOrdinary.RecoveryRawSATLoop
