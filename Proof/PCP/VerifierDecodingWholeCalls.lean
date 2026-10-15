import Proof.PCP.VerifierDecodingFrontTableLayout

/-! One fixed twenty-tape decoder controller. Every rejected front/guard
physically writes false; table acceptance is the table's own final bit. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.Whole
open LocalBitMultitape RepairOrdinary RecoveryExecution RecordsMachine
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def rejectProgram : Machine 20 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val=1
  rule := fun q _ => if q.val=0 then
    some ⟨1,(fun i => if i=19 then some false else none),fun _ => .stay⟩ else none
def sizes : Fin 5 → ℕ :=
  ![Fintype.card (RecoveryCalls.Control Front.sizes),TableGuardLayout.states,3,TableLayout.states,2]
noncomputable def programs : (j : Fin 5) → Machine 20 (sizes j)
  | ⟨0,_⟩ => TapeEmbedding.machine 6 Front.machine
  | ⟨1,_⟩ => TableGuardLayout.machine
  | ⟨2,_⟩ => CounterReset.program (1 : Fin 20)
  | ⟨3,_⟩ => TableLayout.machine
  | ⟨4,_⟩ => rejectProgram
  | ⟨n+5,h⟩ => False.elim (by omega)
def next : (j : Fin 5) → Fin (sizes j) → (Fin 20 → Bool) → Option (Fin 5)
  | ⟨0,_⟩,_,bits => if bits 12 then some 1 else some 4
  | ⟨1,_⟩,_,bits => if bits 17 then some 2 else some 4
  | ⟨2,_⟩,_,_ => some 3
  | ⟨3,_⟩,_,_ => none
  | ⟨4,_⟩,_,_ => none
  | ⟨n+5,h⟩,_,_ => False.elim (by omega)
noncomputable def machine := RecoveryCalls.machine sizes programs 0 next
def tableValid (word fields : List Bool) (t s : ℕ) :=
  decide (2^t*s ≤ word.length) &&
    TableValidation.valid (Front.bound s) t (2^t*s) (FrontTable.tableState fields t s).bits
def valid (word : List Bool) (limit : ℕ) :=
  Front.valid word limit && match HeaderMachine.parts word with
    | none => false
    | some (t,s,fields) => tableValid word fields t s
def budget (c : ℕ) := 96*(c+1)^2
noncomputable def initial (word : List Bool) (limit : ℕ) :=
  controlConfig (RecoveryCalls.code sizes 0)
    (TapeEmbedding.config (fun _ : Fin 6 => 0) (FrontTable.extras word.length) (Front.initial word limit))
noncomputable def endpoint (word fields : List Bool) (limit t s x y : ℕ) (out : State) :=
  let last := TableLayout.output (FrontTable.reset word fields limit t s x y)
    (Front.bound s) t word.length (2^t*s) out
  RecoveryCalls.stopped sizes last.heads last.tapes
def Success (word fields : List Bool) (limit t s x y : ℕ)
    (final : Configuration 20 (Fintype.card (RecoveryCalls.Control sizes))) : Prop :=
  ∃ out : State, final=endpoint word fields limit t s x y out ∧
    out.pre++frame out.bits=(FrontTable.tableState fields t s).pre++frame (FrontTable.tableState fields t s).bits ∧
    out.bits=[] ∧ Inv (Front.bound s) out

theorem call_prefix (node dest : Fin 5) (fuel : ℕ)
    (input : Configuration 20 (sizes node)) (r : ExecutionReceipt 20 (sizes node))
    (hr : runFrom (programs node) fuel input=some r)
    (hn : next node r.final.control r.final.scanned=some dest) :
    Timed machine (r.steps+1) (controlConfig (RecoveryCalls.code sizes node) input)
      (controlConfig (RecoveryCalls.code sizes dest)
        (RecoveryCalls.restarted (programs dest) r.final.heads r.final.tapes)) := by
  obtain ⟨hp,hh⟩ := prefix_of_run (programs node) fuel input r hr
  have hb := RecoveryCalls.body_timed sizes programs 0 next node ⟨r.peakTapeCells,hp⟩
  have he := RecoveryCalls.return_step sizes programs 0 next node dest r.final hh hn
  exact hb.trans (Timed.single (by simp [RecoveryCalls.machine,controlConfig,RecoveryCalls.code]) he)

theorem stop_prefix (node : Fin 5) (fuel : ℕ)
    (input : Configuration 20 (sizes node)) (r : ExecutionReceipt 20 (sizes node))
    (hr : runFrom (programs node) fuel input=some r)
    (hn : next node r.final.control r.final.scanned=none) :
    Timed machine (r.steps+1) (controlConfig (RecoveryCalls.code sizes node) input)
      (RecoveryCalls.stopped sizes r.final.heads r.final.tapes) := by
  obtain ⟨hp,hh⟩ := prefix_of_run (programs node) fuel input r hr
  have hb := RecoveryCalls.body_timed sizes programs 0 next node ⟨r.peakTapeCells,hp⟩
  have he := RecoveryCalls.stop_step sizes programs 0 next node r.final hh hn
  exact hb.trans (Timed.single (by simp [RecoveryCalls.machine,controlConfig,RecoveryCalls.code]) he)

noncomputable def rejected (heads : Fin 20 → ℕ) (tapes : Fin 20 → List Bool) :=
  RecoveryCalls.stopped sizes heads (fun i => if i=19 then writeTapeBit (tapes i) (heads i) false else tapes i)
theorem reject_tail (heads : Fin 20 → ℕ) (tapes : Fin 20 → List Bool) :
    Timed machine 2 (controlConfig (RecoveryCalls.code sizes 4) ⟨(0 : Fin 2),heads,tapes⟩) (rejected heads tapes) := by
  let out : Configuration 20 2 :=
    ⟨1,heads,fun i => if i=19 then writeTapeBit (tapes i) (heads i) false else tapes i⟩
  have he : step rejectProgram ⟨0,heads,tapes⟩=some out := by
    simp [step,rejectProgram]
    apply configuration_ext
    · rfl
    · funext i; simp [applyAction,HeadMove.apply,out]
    · funext i; by_cases h : i=19 <;> simp [applyAction,out,h]
  obtain ⟨r,hr,hf,hs⟩ := (Timed.single (by rfl : rejectProgram.halted (0 : Fin 2)=false) he).run (by rfl)
  have hp := stop_prefix 4 1 _ r hr (by rfl)
  rw [hf,hs] at hp
  change Timed machine 2 (controlConfig (RecoveryCalls.code sizes 4)
    ⟨(0 : Fin 2),heads,tapes⟩) (rejected heads tapes) at hp
  exact hp
theorem rejected_bit (heads : Fin 20 → ℕ) (tapes : Fin 20 → List Bool) :
    (rejected heads tapes).scanned 19=false := by
  simp [rejected,RecoveryCalls.stopped,Configuration.scanned,MemoryTransition.read_write]

end NearCubicWires.RepairSource.VerifierDecoding.Whole
