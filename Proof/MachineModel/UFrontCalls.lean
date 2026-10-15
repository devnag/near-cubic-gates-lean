import Proof.MachineModel.UFrontWitnessLayout

/-! One actual controller for ordinary input, canonical decoder and the
guarded witness prefix, retaining all successful physical endpoints. -/
namespace NearCubicWires.RepairOrdinary.UFront
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def rejectProgram : Machine 81 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val=1
  rule := fun q _ => if q.val=0 then
    some ⟨1,(fun i => if i=79 then some false else none),fun _ => .stay⟩ else none
def sizes : Fin 3 → ℕ := ![decoderStates,witnessStates,2]
noncomputable def programs : (j : Fin 3) → Machine 81 (sizes j)
  | ⟨0,_⟩ => TapeEmbedding.machine 12 UDecoder.machine
  | ⟨1,_⟩ => UWitnessOrdinary.machine
  | ⟨2,_⟩ => rejectProgram
  | ⟨n+3,h⟩ => False.elim (by omega)
def next : (j : Fin 3) → Fin (sizes j) → (Fin 81 → Bool) → Option (Fin 3)
  | ⟨0,_⟩,_,bits => if bits 67 then some 1 else some 2
  | ⟨1,_⟩,_,_ => none
  | ⟨2,_⟩,_,_ => none
  | ⟨n+3,h⟩,_,_ => False.elim (by omega)
noncomputable def machine := RecoveryCalls.machine sizes programs 0 next
def input (raw witness : List Bool) : Fin 81 → List Bool :=
  fun i => Fin.addCases (UDecoder.input raw witness) (fun _ : Fin 12 => []) i
def budget (raw : List Bool) := UDecoder.budget raw+
  UWitness.budget (ClockDyadicLedger.width raw.length) (ClockDyadicLedger.limit raw.length)+3

noncomputable def rejected (heads : Fin 81 → ℕ) (tapes : Fin 81 → List Bool) :=
  RecoveryCalls.stopped sizes heads (fun i => if i=79 then writeTapeBit (tapes i) (heads i) false else tapes i)

theorem reject_tail (heads : Fin 81 → ℕ) (tapes : Fin 81 → List Bool) :
    ∃ n, n≤2 ∧ Timed machine n
      (controlConfig (RecoveryCalls.code sizes 2) ⟨(0 : Fin 2),heads,tapes⟩) (rejected heads tapes) := by
  let out : Configuration 81 2 :=
    ⟨1,heads,fun i => if i=79 then writeTapeBit (tapes i) (heads i) false else tapes i⟩
  have he : step rejectProgram ⟨0,heads,tapes⟩=some out := by
    simp [step,rejectProgram]
    apply configuration_ext
    · rfl
    · funext i; simp [applyAction,HeadMove.apply,out]
    · funext i; by_cases h : i=79 <;> simp [applyAction,out,h]
  obtain ⟨r,hr,hf,hs⟩ := (Timed.single (by rfl : rejectProgram.halted (0 : Fin 2)=false) he).run (by rfl)
  obtain ⟨n,hn,hp⟩ := stop_receipt sizes programs 0 next 2 1 _ r hr (by rfl)
  rw [hf] at hp
  exact ⟨n,hn,hp⟩

theorem rejected_bit (heads : Fin 81 → ℕ) (tapes : Fin 81 → List Bool) :
    (rejected heads tapes).scanned 79=false := by
  simp [rejected,RecoveryCalls.stopped,Configuration.scanned,MemoryTransition.read_write]

def Successful {s : ℕ} (raw witness : List Bool) (final : Configuration 81 s) : Prop :=
  ∃ code x bound padding, ∃ base : Configuration 69 decoderStates,
    ∃ last : Configuration 81 witnessStates,
    raw=VerifierInputFields.source code x bound padding ∧ UInputScalars.Guards raw x bound ∧
    UDecoder.Accepted raw ∧ UDecoder.Successful raw witness base ∧
    final.heads=last.heads ∧ final.tapes=last.tapes ∧
    UWitness.Outcome (ClockDyadicLedger.width raw.length) (RadixSemantics.value bound) witness
      (UWitnessOrdinary.project last) ∧
    UWitnessOrdinary.Preserved (extended base).heads (extended base).tapes last

end NearCubicWires.RepairOrdinary.UFront
