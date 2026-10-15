import Proof.Amplification.RecoveryRowRootFront

namespace NearCubicWires.RepairOrdinary.RecoveryRowRoot
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRowStream RecoveryRowStructure
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RepairSource.RecoveryOracle.BalancedCertificate
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def wholeMachine := RecoveryGatedSequence.machine tableMachine checkMachine 50
def rootBudget (width total : Nat) := 8*width+23+2*total*(32*width+53)
def wholeBudget (width limit total : Nat) := RecoveryRowTable.returnBudget width limit total+rootBudget width total+2
def wholeAnswer (x : State) (word bits : List Bool) :=
  (readMany (readRow x.data.base.state.bits.length) x.total bits).any
    (fun pair=>rootCheck (tableLeafPredicate x.data word) pair.1 (RadixSemantics.value x.key))

theorem root_time (x : State) (word bits : List Bool) (hx : x.Valid word bits) :
    checkTime x=rootBudget x.key.length x.data.total := by
  have hb : x.data.bank.row.width=x.key.length := hx.1.2.1.2.1.trans hx.2.symm
  simp only [checkTime,time,bankTime,RecoveryRowLookupStream.budget,hb,rootBudget]
  ring

theorem rootAnswer_eq (x : State) (word bits : List Bool) (rows : List Row) (rest : List Bool)
    (hp : readMany (readRow x.data.base.state.bits.length) x.total bits=some (rows,rest)) :
    wholeAnswer x word bits=(RecoveryRowTable.tableCheck x.data.base.state.bits.length
      (tableLeafPredicate x.data word) x.total [] bits && rows.any (fun row=>decide (RadixSemantics.value x.key=row.code))) := by
  unfold wholeAnswer
  rw [hp,RecoveryRowTable.table_check_parser,hp]
  simp only [Option.any_some,rootCheck]
  congr 1
  apply congrArg (fun f : Row→Bool=>rows.any f)
  funext row
  apply Bool.eq_iff_iff.mpr
  rw [beq_iff_eq,decide_eq_true_eq]
  exact eq_comm

theorem whole_root_run (limit : Nat) (word bits pre : List Bool) (x : State)
    (hx : x.Valid word bits) (hj : x.data.total=0) (hn : x.total ≤ limit)
    (hs : x.data.base.source=pre++frame bits) (hp : x.data.base.pos=pre.length)
    (hcap : limit*(RecoveryRowLookupStream.budget x.data.base.state.bits.length+3)+5 ≤ x.data.lookupCapacity) :
    ∃ r,runFrom wholeMachine (wholeBudget x.data.base.state.bits.length limit x.total)
        (x.cfg wholeMachine.start)=some r ∧
      r.steps ≤ wholeBudget x.data.base.state.bits.length limit x.total ∧
      r.final.heads 50=0 ∧ r.final.tapes 50=[wholeAnswer x word bits] ∧
      (wholeAnswer x word bits=true →
        ∃ values,CanonicalBinary.decodeBalancedList (RadixSemantics.value x.key)=some values ∧
          values.all (tableLeafPredicate x.data word)=true) := by
  obtain ⟨first,hr0,hb0,hh0,ht0,hout⟩ := table_front_run limit word bits pre x hx hj hn hs hp hcap
  have sound : wholeAnswer x word bits=true →
      ∃ values,CanonicalBinary.decodeBalancedList (RadixSemantics.value x.key)=some values ∧
        values.all (tableLeafPredicate x.data word)=true := by
    intro ha
    simp only [wholeAnswer,Option.any_eq_true] at ha
    obtain ⟨pair,_,hroot⟩ := ha
    exact rootCheck_sound _ _ _ hroot
  cases ha : RecoveryRowTable.tableCheck x.data.base.state.bits.length (tableLeafPredicate x.data word) x.total [] bits
  · have hfalse : wholeAnswer x word bits=false := by
      rw [RecoveryRowTable.table_check_parser] at ha
      unfold wholeAnswer
      cases he : readMany (readRow x.data.base.state.bits.length) x.total bits with
      | none => rfl
      | some pair =>
        rw [he] at ha
        change (checkFrom [] pair.1 && pair.1.all (leafCheck (tableLeafPredicate x.data word)))=false at ha
        change rootCheck _ pair.1 _=false
        simp only [rootCheck,ha,Bool.false_and]
    rw [ha] at ht0
    obtain ⟨r,hr,hb,hf⟩ := RecoveryGatedSequence.reject_run tableMachine checkMachine 50
      (RecoveryRowTable.returnBudget x.data.base.state.bits.length limit x.total) _ first hr0 hh0 ht0
    have hl : RecoveryRowTable.returnBudget x.data.base.state.bits.length limit x.total+1 ≤
        wholeBudget x.data.base.state.bits.length limit x.total := by unfold wholeBudget; omega
    have hm := runFrom_moreFuel wholeMachine _ (wholeBudget x.data.base.state.bits.length limit x.total-
      (RecoveryRowTable.returnBudget x.data.base.state.bits.length limit x.total+1)) _ r hr
    rw [Nat.add_sub_of_le hl] at hm
    refine ⟨r,hm,hb.trans hl,?_,?_,sound⟩
    · rw [hf]; exact hh0
    · rw [hf]; change first.final.tapes 50=_; rw [ht0,hfalse]
  · obtain ⟨out,hf0,hi,hjout⟩ := hout ha
    let y : State := ⟨out.data,x.total,x.key⟩
    have hy : y.Valid word bits := ⟨hi.ready,hx.2.trans hi.sameWidth.symm⟩
    have hw : y.data.bank.row.width=x.data.base.state.bits.length := hi.ready.2.1.2.1.trans hi.sameWidth
    have hparsed : readMany (readRow y.data.bank.row.width) y.data.total bits=some (out.prior,out.input) := by
      rw [hw]; exact hi.parsed
    obtain ⟨last,hr1,hf1,hb1,_,ht1⟩ := root_check_run y word bits out.prior out.input hy hparsed
    have hrootTime : checkTime y=rootBudget x.data.base.state.bits.length x.total := by
      rw [root_time y word bits hy]
      change rootBudget x.key.length out.data.total=_
      rw [hx.2,hjout]
    rw [hrootTime] at hr1 hb1
    have hnext : RecoveryCalls.restarted checkMachine first.final.heads first.final.tapes=y.cfg checkMachine.start := by
      rw [hf0]; rfl
    rw [←hnext] at hr1
    rw [ha] at ht0
    obtain ⟨r,hr,hb,hf⟩ := RecoveryGatedSequence.accept_run tableMachine checkMachine 50
      (RecoveryRowTable.returnBudget x.data.base.state.bits.length limit x.total)
      (rootBudget x.data.base.state.bits.length x.total) _ first last hr0 hh0 ht0 hr1
    have hparse0 : readMany (readRow x.data.base.state.bits.length) x.total bits=some (out.prior,out.input) := by
      rw [←hjout]; exact hi.parsed
    have he : wholeAnswer x word bits=out.prior.any (fun row=>decide (RadixSemantics.value x.key=row.code)) := by
      rw [rootAnswer_eq x word bits out.prior out.input hparse0,ha,Bool.true_and]
    refine ⟨r,hr,hb,?_,?_,sound⟩
    · rw [hf,hf1]; rfl
    · rw [hf,hf1]
      change [(checked y bits).data.base.valid]=[wholeAnswer x word bits]
      rw [ht1,he]

end NearCubicWires.RepairOrdinary.RecoveryRowRoot
