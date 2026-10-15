import Proof.MachineModel.UDecoderLayout

/-! One actual U front controller: input syntax/scalars, guarded decoder,
and a physical rejecting result for a failed input guard. -/
namespace NearCubicWires.RepairOrdinary.UDecoder
open LocalBitMultitape RecoveryExecution RecoveryRootRound RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def rejectProgram : Machine 69 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val=1
  rule := fun q _ => if q.val=0 then
    some ⟨1,(fun i => if i=67 then some false else none),fun _ => .stay⟩ else none
abbrev inputStates := Fintype.card (RecoveryCalls.Control UInputEntry.sizes)
def sizes : Fin 3 → ℕ := ![inputStates,states,2]
noncomputable def programs : (j : Fin 3) → Machine 69 (sizes j)
  | ⟨0,_⟩ => TapeEmbedding.machine 19 UInputOrdinary.machine
  | ⟨1,_⟩ => decoder
  | ⟨2,_⟩ => rejectProgram
  | ⟨n+3,h⟩ => False.elim (by omega)
def next : (j : Fin 3) → Fin (sizes j) → (Fin 69 → Bool) → Option (Fin 3)
  | ⟨0,_⟩,_,bits => if bits 47 then some 1 else some 2
  | ⟨1,_⟩,_,_ => none
  | ⟨2,_⟩,_,_ => none
  | ⟨n+3,h⟩,_,_ => False.elim (by omega)
noncomputable def machine := RecoveryCalls.machine sizes programs 0 next
def input (raw witness : List Bool) : Fin 69 → List Bool :=
  fun i => Fin.addCases (UInputOrdinary.input raw witness) (fun _ : Fin 19 => []) i

def Accepted (raw : List Bool) : Prop := ∃ code x bound padding,
  raw=VerifierInputFields.source code x bound padding ∧ UInputScalars.Guards raw x bound ∧
    ∃ v,decode raw.length code=some v

theorem accepted_valid (raw : List Bool) : Accepted raw → UInputEntry.Valid raw := by
  rintro ⟨code,x,bound,padding,he,hg,_⟩
  exact ⟨code,x,bound,padding,he,hg⟩

theorem accepted_iff (raw code x bound padding : List Bool)
    (he : raw=VerifierInputFields.source code x bound padding)
    (hg : UInputScalars.Guards raw x bound) :
    Accepted raw ↔ ∃ v,decode raw.length code=some v := by
  constructor
  · rintro ⟨code',x',bound',padding',he',_,hd⟩
    have hu := UInputEntry.source_unique code x bound padding code' x' bound' padding' (he.symm.trans he')
    simpa only [hu.1] using hd
  · exact fun h => ⟨code,x,bound,padding,he,hg,h⟩

def budget (raw : List Bool) := UInputEntry.budget raw+
  Ready.limitedBudget raw.length (Nat.log 2 raw.length)+3

noncomputable def rejected (heads : Fin 69 → ℕ) (tapes : Fin 69 → List Bool) :=
  RecoveryCalls.stopped sizes heads (fun i => if i=67 then writeTapeBit (tapes i) (heads i) false else tapes i)

theorem reject_tail (heads : Fin 69 → ℕ) (tapes : Fin 69 → List Bool) :
    ∃ n, n≤2 ∧ Timed machine n
      (controlConfig (RecoveryCalls.code sizes 2) ⟨(0 : Fin 2),heads,tapes⟩) (rejected heads tapes) := by
  let out : Configuration 69 2 :=
    ⟨1,heads,fun i => if i=67 then writeTapeBit (tapes i) (heads i) false else tapes i⟩
  have he : step rejectProgram ⟨0,heads,tapes⟩=some out := by
    simp [step,rejectProgram]
    apply configuration_ext
    · rfl
    · funext i; simp [applyAction,HeadMove.apply,out]
    · funext i; by_cases h : i=67 <;> simp [applyAction,out,h]
  obtain ⟨r,hr,hf,hs⟩ := (Timed.single (by rfl : rejectProgram.halted (0 : Fin 2)=false) he).run (by rfl)
  obtain ⟨n,hn,hp⟩ := stop_receipt sizes programs 0 next 2 1 _ r hr (by rfl)
  rw [hf] at hp
  exact ⟨n,hn,hp⟩

theorem rejected_bit (heads : Fin 69 → ℕ) (tapes : Fin 69 → List Bool) :
    (rejected heads tapes).scanned 67=false := by
  simp [rejected,RecoveryCalls.stopped,Configuration.scanned,MemoryTransition.read_write]

def Successful (raw witness : List Bool)
    (final : Configuration 69 (Fintype.card (RecoveryCalls.Control sizes))) : Prop :=
  ∃ code x bound padding, ∃ base : Configuration 50 inputStates, ∃ small : Configuration 21 states,
    raw=VerifierInputFields.source code x bound padding ∧ UInputScalars.Guards raw x bound ∧
    UInputOrdinary.Prepared raw base.tapes ∧ base.heads=UInputOrdinary.heads ∧
    base.tapes 1=frame witness ∧ base.heads 1=0 ∧
    final.heads=(RecoveryFocus.config slots (extended base).heads (extended base).tapes small).heads ∧
    final.tapes=(RecoveryFocus.config slots (extended base).heads (extended base).tapes small).tapes ∧
    Ready.Outcome code (Nat.log 2 raw.length) (ZeroPadding.config (Ready.inputCapacity code) small)

end NearCubicWires.RepairOrdinary.UDecoder
