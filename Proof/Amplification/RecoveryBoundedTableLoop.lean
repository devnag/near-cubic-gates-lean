import Proof.Amplification.RecoveryOuterTableSemantics

/-! A bounded rejecting table induction over an abstract finite machine.
Its actual body supplier is consumed at each physical driver iteration. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedTableLoop
open LocalBitMultitape RecoveryExecution
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def accepted {t s : Nat} (bit : Fin t) (_ : Fin s) (scanned : Fin t → Bool) := scanned bit
noncomputable def machine {t s : Nat} (p : Machine t s) (bit : Fin t) := RepeatMachine.machine p (accepted bit)
open private successful_cfg_eq from Proof.PCP.VerifierDecodingRejectingRepeat

theorem driver_run {α : Type} {t s : Nat} (p : Machine t s) (bit : Fin t)
    (source : α → Configuration t s) (next : α → α) (answer : α → Bool) (grade : α → Nat) (Inv : α → Prop)
    (check : Nat → α → Bool) (cost limit : Nat)
    (hstart : ∀ x,Inv x → (source x).control=p.start)
    (hhead : ∀ x,Inv x → (source x).heads bit=0)
    (htape : ∀ x,Inv x → ∃ b,(source x).tapes bit=[b])
    (hzero : ∀ x,check 0 x=true)
    (hsucc : ∀ n x,Inv x → grade x<limit → check (n+1) x=(answer x && check n (next x)))
    (supplier : ∀ x,Inv x → grade x<limit → ∃ r,runFrom p cost (source x)=some r ∧ r.steps ≤ cost ∧
      r.final.heads bit=0 ∧ r.final.tapes bit=[answer x] ∧
      (answer x=true → r.final.heads=(source (next x)).heads ∧ r.final.tapes=(source (next x)).tapes ∧
        Inv (next x) ∧ grade (next x)=grade x+1))
    (n total pos : Nat) (x : α) (hx : Inv x) (hn : pos+n=total) (hbound : grade x+n ≤ limit) :
    ∃ r,runFrom (machine p bit) (n*(cost+2)+total+3) (RepeatMachine.cfg 0 (source x) total (pos+1))=some r ∧
      r.steps ≤ n*(cost+2)+total+3 ∧
      r.final.control=RepeatMachine.phaseCode s (if check n x then 3 else 4) ∧
      r.final.heads (bit.castAdd 1)=0 ∧ (∃ b,r.final.tapes (bit.castAdd 1)=[b]) ∧
      (check n x=true → ∃ out,r.final=RepeatMachine.cfg 3 (source out) total 1 ∧ Inv out ∧ grade out=grade x+n) := by
  induction n generalizing pos x with
  | zero=>
    have hpos : pos=total := by omega
    subst pos
    obtain ⟨r,hr,hf,hs⟩ := (RepeatMachine.exhaust p (accepted bit) (source x) total).run
      (by simp [RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])
    refine ⟨r,by simpa only [machine,Nat.zero_mul,Nat.zero_add] using hr,by simpa using hs.le,?_,?_,?_,?_⟩
    · rw [hf,hzero]; rfl
    · rw [hf]
      simpa only [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,Fin.addCases_left] using hhead x hx
    · obtain ⟨b,hb⟩ := htape x hx
      refine ⟨b,?_⟩
      rw [hf]
      simpa only [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,Fin.addCases_left] using hb
    · intro _
      exact ⟨x,hf,hx,by omega⟩
  | succ n ih=>
    have hj : grade x<limit := by omega
    obtain ⟨r,hr,hrb,hrh,hrt,hgood⟩ := supplier x hx hj
    have ha : accepted bit r.final.control r.final.scanned=answer x := by
      simp only [accepted,Configuration.scanned,hrh,hrt,readTapeBit]
      rfl
    have hstep := RepeatMachine.iteration p (accepted bit) (source x) total pos r (hstart x hx) (by omega) hr
    rw [ha] at hstep
    have hc := hsucc n x hx hj
    cases hans : answer x
    · have hcheck : check (n+1) x=false := by rw [hc,hans]; rfl
      simp only [hans,Bool.false_eq_true,if_false] at hstep
      obtain ⟨result,hrun,hfinal,hsteps⟩ := hstep.run
        (by simp [RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])
      have htime : r.steps+2 ≤ (n+1)*(cost+2)+total+3 := by nlinarith
      have hm := runFrom_moreFuel (machine p bit) (r.steps+2)
        ((n+1)*(cost+2)+total+3-(r.steps+2)) _ result hrun
      rw [Nat.add_sub_of_le htime] at hm
      refine ⟨result,hm,hsteps.le.trans htime,?_,?_,?_,?_⟩
      · rw [hfinal,hcheck]; rfl
      · rw [hfinal]
        simpa only [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,Fin.addCases_left] using hrh
      · refine ⟨answer x,?_⟩
        rw [hfinal]
        simpa only [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,Fin.addCases_left] using hrt
      · simp only [hcheck,Bool.false_eq_true,IsEmpty.forall_iff]
    · obtain ⟨hh,ht,hnext,hgrade⟩ := hgood hans
      have hcheck : check (n+1) x=check n (next x) := by rw [hc,hans]; rfl
      simp only [hans,if_true] at hstep
      have he := successful_cfg_eq r.final (source (next x)) total (pos+2) hh ht
      rw [he] at hstep
      obtain ⟨tail,htail,htb,htphase,hth,htt,htout⟩ := ih (pos+1) (next x) hnext (by omega) (by rw [hgrade]; omega)
      rcases hstep with ⟨space,hstep⟩
      obtain ⟨result,hrun,hfinal,hsteps,_⟩ := hstep.followedBy tail htail
      have htime : (r.steps+2)+(n*(cost+2)+total+3) ≤ (n+1)*(cost+2)+total+3 := by nlinarith
      have hm := runFrom_moreFuel (machine p bit) _
        ((n+1)*(cost+2)+total+3-((r.steps+2)+(n*(cost+2)+total+3))) _ result hrun
      rw [Nat.add_sub_of_le htime] at hm
      refine ⟨result,hm,?_,?_,?_,?_,?_⟩
      · rw [hsteps]; nlinarith
      · rw [hfinal,hcheck]; exact htphase
      · rw [hfinal]; exact hth
      · rw [hfinal]; exact htt
      · intro hall
        rw [hcheck] at hall
        obtain ⟨last,hf,hv,hg⟩ := htout hall
        exact ⟨last,hfinal.trans hf,hv,by rw [hg,hgrade]; omega⟩

end NearCubicWires.RepairOrdinary.RecoveryBoundedTableLoop
