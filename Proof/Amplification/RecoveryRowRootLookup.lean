import Proof.Amplification.RecoveryRowTableWhole

namespace NearCubicWires.RepairOrdinary.RecoveryRowRoot
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRowStream RecoveryRowStructure
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RepairSource.RecoveryOracle.BalancedCertificate RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure State where
  data : Children
  total : Nat
  key : List Bool
def State.extra (x : State) : Fin 2→List Bool := ![CompareMachine.word x.total,frame x.key]
def State.extraHeads : Fin 2→Nat := ![1,0]
noncomputable def State.tapes (x : State) : Fin 70→List Bool :=
  Fin.addCases (m:=68) (n:=2) (motive:=fun _=>List Bool) x.data.tapes x.extra
def State.heads (x : State) : Fin 70→Nat :=
  Fin.addCases (m:=68) (n:=2) (motive:=fun _=>Nat) x.data.heads State.extraHeads
noncomputable def State.cfg {s : Nat} (x : State) (q : Fin s) : Configuration 70 s := ⟨q,x.heads,x.tapes⟩
def State.Valid (x : State) (word bits : List Bool) : Prop := x.data.Valid word bits ∧ x.key.length=x.data.base.state.bits.length
def keyed (x : State) : State := {x with data:=bankKey x.data x.key}
def output (x : State) (bits : List Bool) : State := {x with data:=bankOutput (keyed x).data bits}
def copySlots : Fin 4→Fin 70 := ![69,59,51,22]
theorem copySlots_injective : Function.Injective copySlots := by decide
noncomputable def copyMachine := RecoveryFocus.machine copySlots RecoveryRootRound.copyMachine
noncomputable def lookupMachine := TapeEmbedding.machine 2 bankMachine
noncomputable def machine := Composition.machine copyMachine lookupMachine
def time (x : State) := (8*x.key.length+8)+1+bankTime x.data

theorem keyed_tapes (x : State) : (keyed x).tapes=Function.update x.tapes 59 (frame x.key) := by
  unfold State.tapes keyed
  rw [bankKey_tapes,bank_update_left]
  rfl

open private install_eq from Proof.Amplification.RecoveryRowLookupCell

theorem copy_run (x : State) (word bits : List Bool) (hx : x.Valid word bits) :
    ∃ r,runFrom copyMachine (8*x.key.length+8) (x.cfg copyMachine.start)=some r ∧
      r.final=(keyed x).cfg r.final.control ∧ r.steps=8*x.key.length+8 ∧ (keyed x).Valid word bits := by
  have hw : x.data.bank.key.length=x.key.length := hx.1.2.1.1.2.1.trans (hx.1.2.1.2.1.trans hx.2.symm)
  have hc : 2*x.key.length+1 ≤ x.data.copyCapacity := by rw [hx.2]; exact hx.1.2.2.2.2.1
  have hr : 4*x.key.length+3 ≤ x.data.base.state.capacity := by
    have h := hx.1.1.2.1.reset
    change 8192*(x.data.base.state.bits.length+1)^2+1 ≤ x.data.base.state.capacity at h
    rw [hx.2]
    nlinarith
  have h := RecoveryRootRound.copy_ready x.key (frame x.data.bank.key) x.data.copyCapacity x.data.base.state.capacity
    (by rw [frame_length,hw])
  rw [Nat.max_eq_left hc,Nat.max_eq_left hr] at h
  obtain ⟨r,hrun,hheads,htapes,hsteps⟩ := h.focus_at copySlots copySlots_injective x.heads x.tapes
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  have he : install copySlots x.tapes
      ![frame x.key,frame x.key,List.replicate x.data.copyCapacity false,List.replicate x.data.base.state.capacity false]=
      Function.update x.tapes 59 (frame x.key) := by
    apply install_eq copySlots copySlots_injective
    · intro j
      fin_cases j
      · rfl
      · simp [copySlots]
      · rfl
      · rfl
    · intro i hi
      have hn : i≠59 := by intro he; exact hi 1 he.symm
      simp only [Function.update_of_ne hn]
  refine ⟨r,hrun,?_,hsteps,bankKey_valid x.data x.key word bits hx.1 hx.2,hx.2⟩
  apply configuration_ext
  · rfl
  · exact hheads
  · exact htapes.trans (he.trans (keyed_tapes x).symm)

theorem lookup_run (x : State) (word bits : List Bool) (rows : List Row) (rest : List Bool)
    (hx : (keyed x).Valid word bits)
    (hp : readMany (readRow x.data.bank.row.width) x.data.total bits=some (rows,rest)) :
    ∃ r,runFrom lookupMachine (bankTime x.data) ((keyed x).cfg lookupMachine.start)=some r ∧
      r.final=(output x bits).cfg r.final.control ∧ r.steps ≤ bankTime x.data ∧
      (output x bits).Valid word bits ∧
      (output x bits).data.bank.found=rows.any (fun row=>decide (RadixSemantics.value x.key=row.code)) := by
  obtain ⟨base,hr,hf,hb,hv,ha,_⟩ := bank_run (keyed x).data word bits rows rest hx.1 hp
  let r := TapeEmbedding.receipt State.extraHeads x.extra base
  have h := TapeEmbedding.run_embed bankMachine State.extraHeads x.extra (bankTime x.data) _ base hr
  refine ⟨r,h,?_,hb,⟨hv,hx.2⟩,ha⟩
  change TapeEmbedding.config State.extraHeads x.extra base.final=(output x bits).cfg _
  rw [hf]
  rfl

theorem root_lookup_run (x : State) (word bits : List Bool) (rows : List Row) (rest : List Bool)
    (hx : x.Valid word bits)
    (hp : readMany (readRow x.data.bank.row.width) x.data.total bits=some (rows,rest)) :
    ∃ r,runFrom machine (time x) (x.cfg machine.start)=some r ∧
      r.final=(output x bits).cfg r.final.control ∧ r.steps ≤ time x ∧
      (output x bits).Valid word bits ∧
      (output x bits).data.bank.found=rows.any (fun row=>decide (RadixSemantics.value x.key=row.code)) := by
  obtain ⟨first,hr0,hf0,hs0,hv0⟩ := copy_run x word bits hx
  obtain ⟨last,hr1,hf1,hs1,hv1,ha⟩ := lookup_run x word bits rows rest hv0 hp
  have hnext : Composition.restart first.final lookupMachine.start=(keyed x).cfg lookupMachine.start := by
    rw [hf0]; rfl
  rw [←hnext] at hr1
  have hall := Composition.run_join copyMachine lookupMachine (8*x.key.length+8) (bankTime x.data) _ first last hr0 hr1
  refine ⟨Composition.joinedReceipt first last,hall,?_,?_,hv1,ha⟩
  · apply configuration_ext
    · rfl
    · change last.final.heads=(output x bits).heads
      rw [hf1]
      rfl
    · change last.final.tapes=(output x bits).tapes
      rw [hf1]
      rfl
  · change first.steps+1+last.steps ≤ time x
    rw [hs0]
    unfold time
    omega

end NearCubicWires.RepairOrdinary.RecoveryRowRoot
