import Proof.Amplification.RecoveryRowTableSemantics

/-! Whole bounded ordinary table loop. The external unary driver controls
iteration; each accepted body updates its separate prior-row driver. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRowTable
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRowStream RecoveryRowStructure
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RepairSource.RecoveryOracle.BalancedCertificate RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable abbrev bodySize := Fintype.card (RecoveryCalls.Control tableBodySizes)
def accepted (_ : Fin bodySize) (scanned : Fin 68→Bool) := scanned 50
noncomputable def source (x : Cursor) := x.data.cfg tableBodyMachine.start
noncomputable def machine := RepeatMachine.machine tableBodyMachine accepted

open private successful_cfg_eq from Proof.PCP.VerifierDecodingRejectingRepeat

theorem table_driver_run (width limit : Nat) (word bits : List Bool) (P : Nat→Bool)
    (n total pos : Nat) (x : Cursor) (hx : Inv width limit word bits P x)
    (hn : pos+n=total) (hbound : x.data.total+n ≤ limit) :
    ∃ r,runFrom machine (n*(tableRowBudget width limit+2)+total+3)
        (RepeatMachine.cfg 0 (source x) total (pos+1))=some r ∧
      r.steps ≤ n*(tableRowBudget width limit+2)+total+3 ∧
      r.final.control=RepeatMachine.phaseCode bodySize (if tableCheck width P n x.prior x.input then 3 else 4) ∧
      r.final.heads 50=0 ∧ (∃ bit,r.final.tapes 50=[bit]) ∧
      (tableCheck width P n x.prior x.input=true → ∃ out : Cursor,
        r.final=RepeatMachine.cfg 3 (source out) total 1 ∧ Inv width limit word bits P out ∧
        out.data.total=x.data.total+n) := by
  induction n generalizing pos x with
  | zero=>
    have hpos : pos=total := by omega
    subst pos
    obtain ⟨r,hr,hf,hs⟩ := (RepeatMachine.exhaust tableBodyMachine accepted (source x) total).run
      (by simp [RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])
    refine ⟨r,by simpa only [machine,Nat.zero_mul,Nat.zero_add] using hr,by simpa using hs.le,?_,?_,?_,?_⟩
    · rw [hf]; rfl
    · rw [hf]; rfl
    · exact ⟨x.data.base.valid,by rw [hf]; rfl⟩
    · intro _
      exact ⟨x,hf,hx,by omega⟩
  | succ n ih=>
    have hb : x.data.bank.row.width=width := hx.ready.2.1.2.1.trans hx.sameWidth
    have hp : readMany (readRow x.data.bank.row.width) x.data.total bits=some (x.prior,x.input) := by
      rw [hb]; exact hx.parsed
    have hcapacity : (x.data.total+1)*(RecoveryRowLookupStream.budget x.data.bank.row.width+3)+5 ≤ x.data.lookupCapacity := by
      rw [hb]
      calc
        _ ≤ limit*(RecoveryRowLookupStream.budget width+3)+5 := by gcongr; omega
        _ ≤ _ := hx.capacity
    obtain ⟨r,hr,hrb,hrh,hrt,hgood⟩ := table_body_run x.data word bits x.pre x.input x.prior x.input
      limit hx.ready hx.source hx.sourcePos hp hx.bounded hcapacity
    rw [hx.sameWidth] at hr hrb
    have ha : accepted r.final.control r.final.scanned=readWholeAnswer x.data word bits x.input := by
      simp only [accepted,Configuration.scanned,hrh,hrt,readTapeBit]
      rfl
    have hstep := RepeatMachine.iteration tableBodyMachine accepted (source x) total pos r rfl (by omega) hr
    rw [ha] at hstep
    cases hanswer : readWholeAnswer x.data word bits x.input
    · have hcheck : tableCheck width P (n+1) x.prior x.input=false :=
        table_check_reject width P n x.prior x.input ((body_answer width limit word bits P x hx).symm.trans hanswer)
      simp only [hanswer,Bool.false_eq_true,if_false] at hstep
      obtain ⟨result,hrun,hfinal,hsteps⟩ := hstep.run
        (by simp [RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])
      have htime : r.steps+2 ≤ (n+1)*(tableRowBudget width limit+2)+total+3 := by nlinarith
      have hm := runFrom_moreFuel machine (r.steps+2)
        ((n+1)*(tableRowBudget width limit+2)+total+3-(r.steps+2)) _ result hrun
      rw [Nat.add_sub_of_le htime] at hm
      refine ⟨result,hm,hsteps.le.trans htime,?_,?_,?_,?_⟩
      · rw [hfinal,hcheck]; rfl
      · rw [hfinal]
        change r.final.heads 50=0
        exact hrh
      · refine ⟨readWholeAnswer x.data word bits x.input,?_⟩
        rw [hfinal]
        change r.final.tapes 50=[readWholeAnswer x.data word bits x.input]
        exact hrt
      · simp only [hcheck,Bool.false_eq_true,IsEmpty.forall_iff]
    · obtain ⟨out,hout,hready⟩ := hgood hanswer
      have hy := advance_inv width limit word bits P x hx out hready (by omega) hanswer
      have hi : 4*x.data.base.state.bits.length ≤ x.input.length := by
        simp only [readWholeAnswer,Bool.and_eq_true,RecoveryCertificateRow.row_isSome,decide_eq_true_eq] at hanswer
        exact hanswer.1
      have htotal : (advance x word bits out).data.total=x.data.total+1 := by
        change (readFinished x.data word bits x.input out).total+1=x.data.total+1
        rw [(read_finished_retained x.data word bits x.input out hi).2.2.1]
      have hcheck := table_check_advance width P n x word bits out hx.sameWidth
        ((body_answer width limit word bits P x hx).symm.trans hanswer)
      simp only [hanswer,if_true] at hstep
      have hh : r.final.heads=(source (advance x word bits out)).heads := by rw [hout]; rfl
      have ht : r.final.tapes=(source (advance x word bits out)).tapes := by rw [hout]; rfl
      have he := successful_cfg_eq r.final (source (advance x word bits out)) total (pos+2) hh ht
      rw [he] at hstep
      obtain ⟨tail,htail,htb,htphase,hth,htt,htout⟩ := ih (pos+1) (advance x word bits out) hy (by omega) (by rw [htotal]; omega)
      rcases hstep with ⟨space,hstep⟩
      obtain ⟨result,hrun,hfinal,hsteps,_⟩ := hstep.followedBy tail htail
      have htime : (r.steps+2)+(n*(tableRowBudget width limit+2)+total+3) ≤
          (n+1)*(tableRowBudget width limit+2)+total+3 := by nlinarith
      have hm := runFrom_moreFuel machine _
        ((n+1)*(tableRowBudget width limit+2)+total+3-((r.steps+2)+(n*(tableRowBudget width limit+2)+total+3))) _ result hrun
      rw [Nat.add_sub_of_le htime] at hm
      refine ⟨result,hm,?_,?_,?_,?_,?_⟩
      · rw [hsteps]; nlinarith
      · rw [hfinal,hcheck]
        exact htphase
      · rw [hfinal]; exact hth
      · rw [hfinal]; exact htt
      · intro hall
        rw [hcheck] at hall
        obtain ⟨last,hf,hv,ht⟩ := htout hall
        refine ⟨last,hfinal.trans hf,hv,?_⟩
        rw [ht,htotal]
        omega

theorem table_run (width limit total : Nat) (word bits : List Bool) (P : Nat→Bool)
    (x : Cursor) (hx : Inv width limit word bits P x) (hbound : x.data.total+total ≤ limit) :
    ∃ r,runFrom machine (total*(tableRowBudget width limit+3)+3)
        (RepeatMachine.cfg 0 (source x) total 1)=some r ∧
      r.steps ≤ total*(tableRowBudget width limit+3)+3 ∧
      r.final.control=RepeatMachine.phaseCode bodySize (if tableCheck width P total x.prior x.input then 3 else 4) ∧
      r.final.heads 50=0 ∧ (∃ bit,r.final.tapes 50=[bit]) ∧
      (tableCheck width P total x.prior x.input=true → ∃ out : Cursor,
        r.final=RepeatMachine.cfg 3 (source out) total 1 ∧ Inv width limit word bits P out ∧
        out.data.total=x.data.total+total) := by
  have h := table_driver_run width limit word bits P total total 0 x hx (by omega) hbound
  have he : total*(tableRowBudget width limit+2)+total+3=total*(tableRowBudget width limit+3)+3 := by ring
  simpa only [he,Nat.zero_add] using h

end NearCubicWires.RepairOrdinary.RecoveryRowTable
