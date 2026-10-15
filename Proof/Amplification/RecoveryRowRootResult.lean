import Proof.Amplification.RecoveryRowRootLookup

namespace NearCubicWires.RepairOrdinary.RecoveryRowRoot
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRowStream RecoveryRowStructure
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RepairSource.RecoveryOracle.BalancedCertificate
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def setFound (x : State) : State := {x with data:={x.data with base:=setValid x.data.base x.data.bank.found}}
def flagMachine : Machine 70 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==1
  rule := fun q scanned=>if q.val=0 then some ⟨1,fun i=>if i=50 then some (scanned 61) else none,fun _=>.stay⟩ else none

theorem flag_step (heads : Fin 70→Nat) (tapes : Fin 70→List Bool) (old bit : Bool)
    (h50 : heads 50=0) (h61 : heads 61=0) (t50 : tapes 50=[old]) (t61 : tapes 61=[bit]) :
    step flagMachine (⟨0,heads,tapes⟩ : Configuration 70 2)=
      some (⟨1,heads,Function.update tapes 50 [bit]⟩ : Configuration 70 2) := by
  apply congrArg some
  apply configuration_ext
  · rfl
  · rfl
  · funext i
    by_cases hi : i=50
    · subst i
      simp [applyAction,Configuration.scanned,h50,h61,t50,t61,readTapeBit,writeTapeBit]
    · simp [applyAction,hi]

theorem setFound_tapes (x : State) : (setFound x).tapes=Function.update x.tapes 50 [x.data.bank.found] := by
  have h : (setFound x).data.tapes=Function.update x.data.tapes 50 [x.data.bank.found] := by
    change Fin.addCases (m:=52) (n:=16) (motive:=fun _=>List Bool)
      (cfg (setValid x.data.base x.data.bank.found) x.data.copyCapacity (0 : Fin 1)).tapes
      (RecoveryRowLookupTable.readyTapes x.data.bank x.data.total x.data.lookupCapacity)=_
    rw [cfg_valid,bank_update_left]
    rfl
  unfold State.tapes
  rw [h,bank_update_left]
  rfl

theorem flag_run (x : State) :
    ∃ r,runFrom flagMachine 1 (x.cfg flagMachine.start)=some r ∧
      r.final=(setFound x).cfg r.final.control ∧ r.steps=1 := by
  have h := flag_step x.heads x.tapes x.data.base.valid x.data.bank.found rfl rfl rfl rfl
  obtain ⟨r,hr,hf,hs⟩ := (Timed.single (by rfl) h).run (by rfl)
  refine ⟨r,hr,?_,hs⟩
  apply configuration_ext
  · rfl
  · rw [hf]; rfl
  · rw [hf]
    exact (setFound_tapes x).symm

noncomputable def checkMachine := Composition.machine machine flagMachine
def checkTime (x : State) := time x+2
def checked (x : State) (bits : List Bool) := setFound (output x bits)

theorem root_check_run (x : State) (word bits : List Bool) (rows : List Row) (rest : List Bool)
    (hx : x.Valid word bits)
    (hp : readMany (readRow x.data.bank.row.width) x.data.total bits=some (rows,rest)) :
    ∃ r,runFrom checkMachine (checkTime x) (x.cfg checkMachine.start)=some r ∧
      r.final=(checked x bits).cfg r.final.control ∧ r.steps ≤ checkTime x ∧
      (checked x bits).Valid word bits ∧
      (checked x bits).data.base.valid=rows.any (fun row=>decide (RadixSemantics.value x.key=row.code)) := by
  obtain ⟨first,hr0,hf0,hs0,hv,ha⟩ := root_lookup_run x word bits rows rest hx hp
  obtain ⟨last,hr1,hf1,hs1⟩ := flag_run (output x bits)
  have hnext : Composition.restart first.final flagMachine.start=(output x bits).cfg flagMachine.start := by
    rw [hf0]; rfl
  rw [←hnext] at hr1
  have hall := Composition.run_join machine flagMachine (time x) 1 _ first last hr0 hr1
  refine ⟨Composition.joinedReceipt first last,hall,?_,?_,hv,ha⟩
  · apply configuration_ext
    · rfl
    · change last.final.heads=(checked x bits).heads
      rw [hf1]; rfl
    · change last.final.tapes=(checked x bits).tapes
      rw [hf1]; rfl
  · change first.steps+1+last.steps ≤ checkTime x
    rw [hs1]
    unfold checkTime
    omega

theorem root_found_sound (P : Nat→Bool) (rows : List Row) (code : Nat)
    (hc : checkFrom [] rows=true) (hl : rows.all (leafCheck P)=true)
    (hr : rows.any (fun row=>decide (code=row.code))=true) :
    ∃ values,CanonicalBinary.decodeBalancedList code=some values ∧ values.all P=true := by
  apply rootCheck_sound P rows code
  simp only [rootCheck,Bool.and_eq_true]
  refine ⟨⟨hc,hl⟩,?_⟩
  simp only [List.any_eq_true,decide_eq_true_eq] at hr
  obtain ⟨row,hm,he⟩ := hr
  simp only [List.any_eq_true,beq_iff_eq]
  exact ⟨row,hm,he.symm⟩

end NearCubicWires.RepairOrdinary.RecoveryRowRoot
