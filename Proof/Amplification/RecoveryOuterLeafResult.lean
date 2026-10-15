import Proof.Amplification.RecoveryOuterLeafCopy

/-! The independent inner lookup returns its found bit to the shared row
result. The whole call retains both row streams and all bounded drivers. -/
namespace NearCubicWires.RepairOrdinary.RecoveryOuterLeaf
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRowStream RecoveryRowStructure
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RepairSource.RecoveryOracle.BalancedCertificate
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def setResult (x : State) (bit : Bool) : State := {x with outer:={x.outer with base:=setValid x.outer.base bit}}
def flagMachine : Machine 84 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==1
  rule := fun q scanned=>if q.val=0 then some ⟨1,fun i=>if i=50 then some (scanned 77) else none,fun _=>.stay⟩ else none

theorem setResult_tapes (x : State) (bit : Bool) :
    (setResult x bit).tapes=Function.update x.tapes 50 [bit] := by
  have he : (setResult x bit).outer.tapes=Function.update x.outer.tapes 50 [bit] := by
    change Fin.addCases (m:=52) (n:=16) (motive:=fun _=>List Bool)
      (cfg (setValid x.outer.base bit) x.outer.copyCapacity (0 : Fin 1)).tapes
      (RecoveryRowLookupTable.readyTapes x.outer.bank x.outer.total x.outer.lookupCapacity)=_
    rw [cfg_valid,bank_update_left]
    rfl
  unfold State.tapes
  rw [he,bank_update_left]
  rfl

theorem flag_run (x : State) :
    ∃ r,runFrom flagMachine 1 (x.cfg flagMachine.start)=some r ∧
      r.final=(setResult x x.inner.found).cfg r.final.control ∧ r.steps=1 := by
  have h : step flagMachine (x.cfg flagMachine.start)=
      some (⟨1,x.heads,Function.update x.tapes 50 [x.inner.found]⟩ : Configuration 84 2) := by
    apply congrArg some
    apply configuration_ext
    · rfl
    · rfl
    · funext i
      by_cases hi : i=50
      · subst i
        change writeTapeBit (x.tapes 50) 0 (readTapeBit (x.tapes 77) 0)=_
        change writeTapeBit [x.outer.base.valid] 0 (readTapeBit [x.inner.found] 0)=_
        simp [readTapeBit,writeTapeBit]
      · simp [applyAction,hi]
        rfl
  obtain ⟨r,hr,hf,hs⟩ := (Timed.single (by rfl) h).run (by rfl)
  refine ⟨r,hr,?_,hs⟩
  apply configuration_ext
  · rfl
  · rw [hf]; rfl
  · rw [hf]; exact (setResult_tapes x x.inner.found).symm

noncomputable def checkedMachine := Composition.machine machine flagMachine
def checkedCost (x : State) := cost x+2
def checked (x : State) (bits : List Bool) := setResult (result x bits) (result x bits).inner.found

theorem checked_run (x : State) (word outerBits innerBits : List Bool) (rows : List Row) (rest : List Bool)
    (hx : x.Valid word outerBits innerBits)
    (hp : readMany (readRow x.inner.row.width) x.total innerBits=some (rows,rest)) :
    ∃ r,runFrom checkedMachine (checkedCost x) (x.cfg checkedMachine.start)=some r ∧
      r.final=(checked x innerBits).cfg r.final.control ∧ r.steps ≤ checkedCost x ∧
      (checked x innerBits).Valid word outerBits innerBits ∧
      (checked x innerBits).outer.base.valid=rows.any (fun row=>decide (RadixSemantics.value x.outer.base.state.bits=row.code)) := by
  obtain ⟨first,hr0,hf0,hs0,hv0,ha⟩ := member_run x word outerBits innerBits rows rest hx hp
  obtain ⟨last,hr1,hf1,hs1⟩ := flag_run (result x innerBits)
  have hnext : Composition.restart first.final flagMachine.start=(result x innerBits).cfg flagMachine.start := by
    rw [hf0]; rfl
  rw [←hnext] at hr1
  have hall := Composition.run_join machine flagMachine (cost x) 1 _ first last hr0 hr1
  refine ⟨Composition.joinedReceipt first last,hall,?_,?_,hv0,ha⟩
  · apply configuration_ext
    · rfl
    · change last.final.heads=(checked x innerBits).heads
      rw [hf1]; rfl
    · change last.final.tapes=(checked x innerBits).tapes
      rw [hf1]; rfl
  · change first.steps+1+last.steps ≤ checkedCost x
    rw [hs1]
    unfold checkedCost
    omega

end NearCubicWires.RepairOrdinary.RecoveryOuterLeaf
