import Proof.Amplification.RecoveryStoredListCell

/-! Persistent three-literal storage around the one reusable raw-cell
decoder. The next cursor is the literal output of the actual controller. -/
namespace NearCubicWires.RepairOrdinary.RecoveryClauseState
open LocalBitMultitape RecoveryExecution RecoveryRootRound RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure State where
  bits : List Bool
  capacity : Nat
  backing : Fin 20 → List Bool
  fields : Fin 3 → List Bool
  flag : Bool
  result : Bool

def State.core (s : State) := RecoveryRawListStep.input s.bits s.capacity s.backing s.flag
def State.tapes (s : State) : Fin 28 → List Bool :=
  Fin.addCases (m := 24) (n := 4) (motive := fun _ => List Bool) s.core
    (Fin.addCases (m := 3) (n := 1) (motive := fun _ => List Bool) s.fields (fun _ => [s.result]))
def State.Valid (s : State) : Prop :=
  (∀ i,(s.backing i).length≤RecoveryReusableUnpair.capacity s.bits) ∧
    ∀ i,(s.fields i).length≤2*s.bits.length+1
def tailWord (bits : List Bool) := RecoveryChildSelection.word false (RecoveryRawListStep.reduced bits)
def nextCapacity (s : State) := max (RecoveryRawListStep.reset1 s.bits s.capacity)
  (RecoveryReusableUnpair.capacity (RecoveryRawListStep.reduced s.bits)+1)
def State.after (s : State) (which : Fin 3) : State :=
  if value s.bits=0 then
    { s with
      bits := RecoveryRawListStep.reduced s.bits
      capacity := RecoveryRawListStep.reset1 s.bits s.capacity
      flag := false }
  else
    { s with
      bits := tailWord s.bits
      capacity := nextCapacity s
      backing := RecoveryChildSelection.backing (RecoveryRawListStep.reduced s.bits)
        (RecoveryRawListStep.reset1 s.bits s.capacity)
      fields := Function.update s.fields which (frame (RecoveryCellStore.headWord s.bits))
      flag := true }

theorem after_length (s : State) (which : Fin 3) : (s.after which).bits.length=s.bits.length := by
  by_cases hz : value s.bits=0 <;> simp [State.after,hz,tailWord,RecoveryChildSelection.word_length]

theorem after_valid (s : State) (which : Fin 3) (h : s.Valid) : (s.after which).Valid := by
  unfold State.after
  split
  next hz =>
    simp only [State.Valid,RecoveryRawListStep.reduced_length]
    constructor
    · intro i
      rw [RecoveryRawListStep.reduced_capacity]
      exact h.1 i
    · exact h.2
  next hz =>
    constructor
    · intro i
      exact RecoveryDecodeStep.next_backing_bound false (RecoveryRawListStep.reduced s.bits)
        (RecoveryRawListStep.reset1 s.bits s.capacity) i
    · intro i
      by_cases hi : i=which
      · subst i
        simp [Function.update,tailWord,RecoveryChildSelection.word_length,RecoveryCellStore.headWord_length]
      · simpa [Function.update,hi,tailWord,RecoveryChildSelection.word_length] using h.2 i

def savedSlot (which : Fin 3) : Fin 28 := ⟨24+which.val,by omega⟩
def slots (which : Fin 3) (i : Fin 25) : Fin 28 :=
  if i.val<24 then ⟨i.val,by omega⟩ else savedSlot which

theorem slots_injective (which : Fin 3) : Function.Injective (slots which) := by
  intro i j he
  have hv := congrArg (fun k : Fin 28 => k.val) he
  simp only [slots,savedSlot] at hv
  split at hv <;> split at hv <;> apply Fin.ext <;> dsimp at hv <;> omega

@[simp] theorem slot_core (which : Fin 3) (i : Fin 24) : slots which (i.castAdd 1)=i.castAdd 4 := by
  apply Fin.ext
  simp [slots]
@[simp] theorem slot_saved (which : Fin 3) : slots which 24=savedSlot which := by simp [slots]

@[simp] theorem tapes_core (s : State) (i : Fin 24) : s.tapes (i.castAdd 4)=s.core i := by
  simp [State.tapes]
@[simp] theorem tapes_saved (s : State) (which : Fin 3) : s.tapes (savedSlot which)=s.fields which := by
  change s.tapes ((which.castAdd 1).natAdd 24)=s.fields which
  simp [State.tapes]
@[simp] theorem tapes_result (s : State) : s.tapes 27=[s.result] := rfl

theorem after_core (s : State) (which : Fin 3) :
    (s.after which).core=RecoveryRawListStep.output false s.bits s.capacity s.backing := by
  by_cases hz : value s.bits=0
  · simp [State.after,State.core,RecoveryRawListStep.output,hz,RecoveryRawListStep.predOutput]
  · simp [State.after,State.core,RecoveryRawListStep.output,hz,RecoveryRawListStep.decodeOutput,
      RecoveryRawListStep.input,tailWord,nextCapacity]

theorem output_layout (s : State) (which : Fin 3) (i : Fin 25) :
    RecoveryStoredListCell.output s.bits (s.fields which) s.capacity s.backing i=
      (s.after which).tapes (slots which i) := by
  refine Fin.addCases (m := 24) (n := 1) (motive := fun j : Fin 25 =>
    RecoveryStoredListCell.output s.bits (s.fields which) s.capacity s.backing j=
      (s.after which).tapes (slots which j)) ?_ ?_ i
  · intro j
    rw [slot_core,tapes_core,after_core]
    by_cases hz : value s.bits=0 <;>
      simp [RecoveryStoredListCell.output,RecoveryStoredListCell.middle,RecoveryCellStore.tapes,
        RecoveryRawListStep.output,RecoveryCellStore.base,hz]
  · intro j
    fin_cases j
    change RecoveryStoredListCell.output s.bits (s.fields which) s.capacity s.backing 24=
      (s.after which).tapes (slots which 24)
    rw [slot_saved,tapes_saved]
    by_cases hz : value s.bits=0 <;>
      simp [RecoveryStoredListCell.output,RecoveryStoredListCell.middle,RecoveryCellStore.tapes,State.after,hz,Fin.addCases]

noncomputable def machine (which : Fin 3) := RecoveryFocus.machine (slots which) RecoveryStoredListCell.machine

theorem cell_ready (s : State) (which : Fin 3) (hv : s.Valid) :
    ReadyRun (machine which) (RecoveryStoredListCell.time s.bits) s.tapes (s.after which).tapes := by
  have h := (RecoveryStoredListCell.stored_cell_ready s.bits (s.fields which) s.capacity s.backing s.flag
    hv.1 (hv.2 which)).focus (slots which) (slots_injective which) s.tapes (by
      intro j
      refine Fin.addCases (m := 24) (n := 1) (motive := fun i : Fin 25 =>
        s.tapes (slots which i)=RecoveryStoredListCell.input s.bits (s.fields which) s.capacity s.backing s.flag i) ?_ ?_ j
      · intro i; simp [RecoveryStoredListCell.input,RecoveryCellStore.tapes,State.core]
      · intro i; fin_cases i
        change s.tapes (slots which 24)=s.fields which
        rw [slot_saved,tapes_saved])
  have he : install (slots which) s.tapes
      (RecoveryStoredListCell.output s.bits (s.fields which) s.capacity s.backing)=(s.after which).tapes := by
    funext i
    by_cases hi : ∃ j,slots which j=i
    · obtain ⟨j,rfl⟩ := hi
      exact (install_slot (slots which) (slots_injective which) _ _ j).trans (output_layout s which j)
    · rw [install_other (slots which) _ _ _ (by intro j hj; exact hi ⟨j,hj⟩)]
      have hlarge : 24 ≤ i.val := by
        by_contra hn
        exact hi ⟨⟨i.val,by omega⟩,by simp [slots,show i.val<24 by omega]⟩
      have hneq : i≠savedSlot which := by intro he; exact hi ⟨24,(slot_saved which).trans he.symm⟩
      refine Fin.addCases (m := 24) (n := 4) (motive := fun j : Fin 28 =>
        24 ≤ j.val → j≠savedSlot which → s.tapes j=(s.after which).tapes j) ?_ ?_ i hlarge hneq
      · intro j hj; simp only [Fin.val_castAdd] at hj; omega
      · intro j _ hj
        refine Fin.addCases (m := 3) (n := 1) (motive := fun k : Fin 4 =>
          k.natAdd 24≠savedSlot which → s.tapes (k.natAdd 24)=(s.after which).tapes (k.natAdd 24)) ?_ ?_ j hj
        · intro k hk
          have hkw : k≠which := by intro he; subst k; exact hk rfl
          by_cases hz : value s.bits=0 <;> simp [State.tapes,State.after,hz,hkw]
        · intro k _
          fin_cases k
          change [s.result]=[(s.after which).result]
          by_cases hz : value s.bits=0 <;> simp [State.after,hz]
  rw [he] at h
  exact h

end NearCubicWires.RepairOrdinary.RecoveryClauseState
