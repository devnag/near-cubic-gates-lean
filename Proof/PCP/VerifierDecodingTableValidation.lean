import Proof.PCP.VerifierDecodingRecordsDriver
import Proof.PCP.VerifierDecodingDelimiter
import Proof.MachineModel.OrdinaryMemoryEffect

/-! Finite controller for the counted table and exact final delimiter.
Both rejection and success physically overwrite the result bit, including
the zero-record case. All call returns and final writes are paid. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.TableValidation
open LocalBitMultitape RepairOrdinary RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev recordStates := Fintype.card (RecoveryCalls.Control RecordMachine.sizes)
abbrev loopStates := Fintype.card (RepeatMachine.Control recordStates)
abbrev driverStates := 3+loopStates

def flagProgram (value : Bool) : Machine 9 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun q _ => if q.val=0 then
    some ⟨1,(fun i => if i=7 then some value else none),fun _ => .stay⟩ else none
def flagOutput (value : Bool) (heads : Fin 9 → ℕ) (tapes : Fin 9 → List Bool) : Configuration 9 2 :=
  ⟨1,heads,fun i => if i=7 then writeTapeBit (tapes i) (heads i) value else tapes i⟩

theorem flag_run (value : Bool) (heads : Fin 9 → ℕ) (tapes : Fin 9 → List Bool) :
    ∃ r, runFrom (flagProgram value) 1 ⟨0,heads,tapes⟩=some r ∧
      r.final=flagOutput value heads tapes ∧ r.steps=1 := by
  have he : step (flagProgram value) ⟨0,heads,tapes⟩=some (flagOutput value heads tapes) := by
    simp [step,flagProgram]
    apply configuration_ext
    · rfl
    · funext i; simp [applyAction,HeadMove.apply,flagOutput]
    · funext i; by_cases h : i=7 <;> simp [applyAction,flagOutput,h]
  exact (Timed.single (by rfl : (flagProgram value).halted (0 : Fin 2)=false) he).run (by rfl)

noncomputable def delimiterProgram := TapeEmbedding.machine 8 DelimiterMachine.machine
def sizes : Fin 4 → ℕ := ![driverStates,3,2,2]
noncomputable def programs : (j : Fin 4) → Machine 9 (sizes j)
  | ⟨0,_⟩ => RecordsDriver.machine
  | ⟨1,_⟩ => delimiterProgram
  | ⟨2,_⟩ => flagProgram true
  | ⟨3,_⟩ => flagProgram false
  | ⟨n+4,h⟩ => False.elim (by omega)
noncomputable def next : (j : Fin 4) → Fin (sizes j) → (Fin 9 → Bool) → Option (Fin 4)
  | ⟨0,_⟩,q,_ => if q=(RepeatMachine.phaseCode recordStates 3).natAdd 3 then some 1 else some 3
  | ⟨1,_⟩,q,_ => if q.val=1 then some 2 else some 3
  | ⟨2,_⟩,_,_ => none
  | ⟨3,_⟩,_,_ => none
  | ⟨n+4,h⟩,_,_ => False.elim (by omega)
noncomputable def machine := RecoveryCalls.machine sizes programs 0 next

theorem call_prefix (node dest : Fin 4) (fuel : ℕ)
    (input : Configuration 9 (sizes node)) (r : ExecutionReceipt 9 (sizes node))
    (hr : runFrom (programs node) fuel input=some r)
    (hn : next node r.final.control r.final.scanned=some dest) :
    Timed machine (r.steps+1) (controlConfig (RecoveryCalls.code sizes node) input)
      (controlConfig (RecoveryCalls.code sizes dest)
        (RecoveryCalls.restarted (programs dest) r.final.heads r.final.tapes)) := by
  obtain ⟨hp,hh⟩ := prefix_of_run (programs node) fuel input r hr
  have hb := RecoveryCalls.body_timed sizes programs 0 next node ⟨r.peakTapeCells,hp⟩
  have he := RecoveryCalls.return_step sizes programs 0 next node dest r.final hh hn
  exact hb.trans (Timed.single (by simp [RecoveryCalls.machine,controlConfig,RecoveryCalls.code]) he)

theorem stop_prefix (node : Fin 4) (fuel : ℕ)
    (input : Configuration 9 (sizes node)) (r : ExecutionReceipt 9 (sizes node))
    (hr : runFrom (programs node) fuel input=some r)
    (hn : next node r.final.control r.final.scanned=none) :
    Timed machine (r.steps+1) (controlConfig (RecoveryCalls.code sizes node) input)
      (RecoveryCalls.stopped sizes r.final.heads r.final.tapes) := by
  obtain ⟨hp,hh⟩ := prefix_of_run (programs node) fuel input r hr
  have hb := RecoveryCalls.body_timed sizes programs 0 next node ⟨r.peakTapeCells,hp⟩
  have he := RecoveryCalls.stop_step sizes programs 0 next node r.final hh hn
  exact hb.trans (Timed.single (by simp [RecoveryCalls.machine,controlConfig,RecoveryCalls.code]) he)

noncomputable def finished (value : Bool) (heads : Fin 9 → ℕ) (tapes : Fin 9 → List Bool) :=
  RecoveryCalls.stopped sizes (flagOutput value heads tapes).heads (flagOutput value heads tapes).tapes

theorem finished_scanned (value : Bool) (heads : Fin 9 → ℕ) (tapes : Fin 9 → List Bool) :
    (finished value heads tapes).scanned 7=value := by
  simp [finished,RecoveryCalls.stopped,flagOutput,Configuration.scanned,MemoryTransition.read_write]

theorem flag_tail (value : Bool) (heads : Fin 9 → ℕ) (tapes : Fin 9 → List Bool) :
    Timed machine 2
      (controlConfig (RecoveryCalls.code sizes (if value then 2 else 3))
        ⟨(programs (if value then 2 else 3)).start,heads,tapes⟩)
      (finished value heads tapes) := by
  obtain ⟨r,hr,hf,hs⟩ := flag_run value heads tapes
  cases value with
  | false =>
    have ht := stop_prefix 3 1 _ r hr (by rfl)
    rw [hf,hs] at ht
    exact ht
  | true =>
    have ht := stop_prefix 2 1 _ r hr (by rfl)
    rw [hf,hs] at ht
    exact ht

theorem reject_ne_success :
    (RepeatMachine.phaseCode recordStates 4).natAdd 3 ≠ (RepeatMachine.phaseCode recordStates 3).natAdd 3 := by
  intro h
  have he : RepeatMachine.phaseCode recordStates 4=RepeatMachine.phaseCode recordStates 3 := by
    apply Fin.ext
    have hv := congrArg Fin.val h
    simp only [Fin.val_natAdd] at hv
    omega
  have hi := (RepeatMachine.code recordStates).injective he
  exact (by decide : (4 : Fin 5)≠3) (Sum.inr.inj hi)

end NearCubicWires.RepairSource.VerifierDecoding.TableValidation
