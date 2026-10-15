import Proof.Amplification.RecoveryGatedBoolean

namespace NearCubicWires.RepairOrdinary.RecoveryOuterRoot
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRowStream RecoveryRowStructure
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RepairSource.RecoveryOracle.BalancedCertificate
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def wholeMachine := RecoveryGatedSequence.machine tableMachine rootMachine 50
def rootBudget (width total : Nat) := 8*width+23+2*total*(32*width+53)
def wholeBudget (width limit total : Nat) := RecoveryOuterTable.returnBudget width limit total+rootBudget width total+2
def wholeAnswer (x : State) (innerRows : List Row) (bits : List Bool) :=
  (readMany (readRow x.data.outer.base.state.bits.length) x.total bits).any
    (fun pair=>rootCheck (RecoveryOuterLeaf.predicate innerRows) pair.1 (RadixSemantics.value x.key))

theorem rootAnswer_eq (x : State) (innerRows : List Row) (bits : List Bool) (rows : List Row) (rest : List Bool)
    (hp : readMany (readRow x.data.outer.base.state.bits.length) x.total bits=some (rows,rest)) :
    wholeAnswer x innerRows bits=(RecoveryRowTable.tableCheck x.data.outer.base.state.bits.length
      (RecoveryOuterLeaf.predicate innerRows) x.total [] bits && rows.any (fun row=>decide (RadixSemantics.value x.key=row.code))) := by
  unfold wholeAnswer
  rw [hp,RecoveryRowTable.table_check_parser,hp]
  simp only [Option.any_some,rootCheck]
  congr 1
  apply congrArg (fun f : Row→Bool=>rows.any f)
  funext row
  apply Bool.eq_iff_iff.mpr
  rw [beq_iff_eq,decide_eq_true_eq]
  exact eq_comm

theorem answer_sound (x : State) (innerRows : List Row) (bits : List Bool)
    (ha : wholeAnswer x innerRows bits=true) :
    ∃ values,CanonicalBinary.decodeBalancedList (RadixSemantics.value x.key)=some values ∧
      values.all (RecoveryOuterLeaf.predicate innerRows)=true := by
  simp only [wholeAnswer,Option.any_eq_true] at ha
  obtain ⟨pair,_,hroot⟩ := ha
  exact rootCheck_sound _ _ _ hroot

theorem answer_reject (x : State) (innerRows : List Row) (bits : List Bool)
    (ha : RecoveryRowTable.tableCheck x.data.outer.base.state.bits.length
      (RecoveryOuterLeaf.predicate innerRows) x.total [] bits=false) :
    wholeAnswer x innerRows bits=false := by
  rw [RecoveryRowTable.table_check_parser] at ha
  unfold wholeAnswer
  cases he : readMany (readRow x.data.outer.base.state.bits.length) x.total bits with
  | none => rfl
  | some pair =>
    rw [he] at ha
    change (checkFrom [] pair.1 && pair.1.all (leafCheck (RecoveryOuterLeaf.predicate innerRows)))=false at ha
    change rootCheck _ pair.1 _=false
    simp only [rootCheck,ha,Bool.false_and]

theorem root_tail_run (limit : Nat) (word bits innerBits : List Bool) (innerRows : List Row) (innerRest : List Bool)
    (x : State) (out : RecoveryOuterTable.Cursor) (hx : x.Valid word bits innerBits)
    (hi : RecoveryOuterTable.Inv x.data.outer.base.state.bits.length limit word bits innerBits innerRows innerRest out)
    (hjout : out.data.outer.total=x.total)
    (ha : RecoveryRowTable.tableCheck x.data.outer.base.state.bits.length (RecoveryOuterLeaf.predicate innerRows) x.total [] bits=true) :
    ∃ r,runFrom rootMachine (rootBudget x.data.outer.base.state.bits.length x.total)
        ((⟨out.data,x.total,x.key⟩ : State).cfg rootMachine.start)=some r ∧
      r.final.heads 50=0 ∧ r.final.tapes 50=[wholeAnswer x innerRows bits] := by
  let y : State := ⟨out.data,x.total,x.key⟩
  have hy : y.Valid word bits innerBits := ⟨hi.ready,hx.2.trans hi.sameWidth.symm⟩
  have hw : y.data.outer.bank.row.width=x.data.outer.base.state.bits.length := hi.ready.1.2.1.2.1.trans hi.sameWidth
  have hparsed : readMany (readRow y.data.outer.bank.row.width) y.data.outer.total bits=some (out.prior,out.input) := by
    rw [hw]; exact hi.parsed
  obtain ⟨r,hr,hf,_,_,ht⟩ := root_run y word bits innerBits out.prior out.input hy hparsed
  have hrootTime : RecoveryRowRoot.checkTime y.root=rootBudget x.data.outer.base.state.bits.length x.total := by
    rw [RecoveryRowRoot.root_time y.root word bits ⟨hy.1.1,hy.2⟩]
    change rootBudget x.key.length out.data.outer.total=_
    rw [hx.2,hjout]
  rw [hrootTime] at hr
  have hparse0 : readMany (readRow x.data.outer.base.state.bits.length) x.total bits=some (out.prior,out.input) := by
    rw [←hjout]; exact hi.parsed
  have he : wholeAnswer x innerRows bits=out.prior.any (fun row=>decide (RadixSemantics.value x.key=row.code)) := by
    rw [rootAnswer_eq x innerRows bits out.prior out.input hparse0,ha,Bool.true_and]
  refine ⟨r,hr,?_,?_⟩
  · rw [hf]; rfl
  · rw [hf]
    change [(output y bits).data.outer.base.valid]=[wholeAnswer x innerRows bits]
    rw [ht,he]

end NearCubicWires.RepairOrdinary.RecoveryOuterRoot
