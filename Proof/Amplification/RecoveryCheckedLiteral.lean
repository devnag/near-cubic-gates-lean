import Proof.Amplification.RecoveryLiteralTag

/-! Enclosing ordinary literal decoding and natural Boolean-tag checking.
The tag checker consumes the retained padded left output of the real unpair,
and the checked variable stays in its selected persistent literal field. -/
namespace NearCubicWires.RepairOrdinary.RecoveryCheckedLiteral
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryClauseState RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tagSlots : Fin 4→Fin 28 := ![17,23,27,22]
noncomputable def tagMachine := RecoveryFocus.machine tagSlots RecoveryLiteralTag.machine

def resetCapacity (s : State) (word : List Bool) := max s.capacity (RecoveryReusableUnpair.capacity word+1)
def tagWord (word : List Bool) := RecoveryFixedUnpair.leftWord word
def tagInput (s : State) (word : List Bool) (i : Fin 4) :=
  ZeroPadding.pad (![RecoveryReusableUnpair.capacity word,0,0,0] i)
    (RecoveryLiteralTag.tapes (tagWord word) s.flag s.result (resetCapacity s word) i)
def tagOutput (s : State) (word : List Bool) (i : Fin 4) :=
  ZeroPadding.pad (![RecoveryReusableUnpair.capacity word,0,0,0] i)
    (RecoveryLiteralTag.tapes (RecoveryLiteralTag.predWord (RecoveryLiteralTag.predWord (tagWord word)))
      (RecoveryLiteralTag.nonzero (tagWord word)) (decide (value (tagWord word)≤1))
      (max (resetCapacity s word) (2*(tagWord word).length+1)) i)
noncomputable def output (s : State) (which : Fin 3) (word : List Bool) :=
  install tagSlots (RecoveryLiteralDecode.output s which word) (tagOutput s word)

theorem decoded_layout (s : State) (which : Fin 3) (word : List Bool) (i : Fin 4) :
    RecoveryLiteralDecode.output s which word (tagSlots i)=tagInput s word i := by
  fin_cases i
  · exact RecoveryLiteralDecode.output_tag s which word
  · exact (RecoveryLiteralDecode.output_other s which word 23 (Or.inr (by decide))
      (by intro h; have hv:=congrArg (fun k : Fin 28=>k.val) h; simp only [savedSlot] at hv; omega)).trans rfl
  · exact (RecoveryLiteralDecode.output_other s which word 27 (Or.inr (by decide))
      (by intro h; have hv:=congrArg (fun k : Fin 28=>k.val) h; simp only [savedSlot] at hv; omega)).trans rfl
  · change RecoveryLiteralDecode.output s which word 22=
      ZeroPadding.pad 0 (List.replicate (resetCapacity s word) false)
    rw [ZeroPadding.pad_zero]
    exact install_slot (RecoveryLiteralDecode.slots which) (RecoveryLiteralDecode.slots_injective which) _ _ 22

theorem tag_ready (s : State) (which : Fin 3) (word : List Bool) :
    ReadyRun tagMachine (RecoveryLiteralTag.time (tagWord word))
      (RecoveryLiteralDecode.output s which word) (output s which word) :=
  (RecoveryLiteralTag.padded_tag_ready (tagWord word) s.flag s.result
    (resetCapacity s word) (RecoveryReusableUnpair.capacity word)).focus
      tagSlots (by decide) _ (decoded_layout s which word)

abbrev decodeStates := Fintype.card (RecoveryCalls.Control RecoveryDecodeStep.sizes)
abbrev tagStates := Fintype.card (RecoveryCalls.Control RecoveryLiteralTag.sizes)
def sizes : Fin 2→Nat := ![decodeStates,tagStates]
noncomputable def programs (which : Fin 3) : (j : Fin 2)→Machine 28 (sizes j)
  | ⟨0,_⟩ => RecoveryLiteralDecode.machine which
  | ⟨1,_⟩ => tagMachine
  | ⟨n+2,h⟩ => False.elim (by omega)
def next (j : Fin 2) (_ : Fin (sizes j)) (_ : Fin 28→Bool) : Option (Fin 2) :=
  if j.val=0 then some 1 else none
noncomputable def machine (which : Fin 3) := RecoveryCalls.machine sizes (programs which) 0 next

def time (word : List Bool) := (RecoveryDecodeStep.time word+1)+(RecoveryLiteralTag.time (tagWord word)+1)
def budget (word : List Bool) := 131072*(word.length+1)^2

theorem literal_ready (s : State) (which : Fin 3) (word : List Bool)
    (hv : s.Valid) (hw : word.length=s.bits.length) (hf : s.fields which=frame word) :
    ReadyRun (machine which) (time word) s.tapes (output s which word) := by
  have hd := (RecoveryLiteralDecode.literal_ready s which word hv hw hf).call
    sizes (programs which) 0 next 0 1 (by intro q; rfl)
  have ht := (tag_ready s which word).stop sizes (programs which) 0 next 1 (by intro q; rfl)
  have h := hd.trans ht
  have hi : controlConfig (RecoveryCalls.code sizes 0)
      (initialConfiguration (programs which 0) s.tapes)=initialConfiguration (machine which) s.tapes := rfl
  rw [hi] at h
  obtain ⟨r,hr,hf,hs⟩ := h.run (by simp [RecoveryCalls.machine,RecoveryCalls.stopped])
  exact ⟨r,hr,by simp [hf,RecoveryCalls.stopped],by intro i; simp [hf,RecoveryCalls.stopped],hs⟩

theorem time_bound (word : List Bool) : time word≤budget word := by
  have hd := RecoveryDecodeStep.time_bound word
  unfold time budget RecoveryDecodeStep.budget at *
  rw [RecoveryLiteralTag.time_eq]
  simp only [tagWord,RecoveryFixedUnpair.word_lengths]
  nlinarith

theorem output_variable (s : State) (which : Fin 3) (word : List Bool) :
    output s which word (savedSlot which)=frame (RecoveryChildSelection.word false word) := by
  rw [output,install_other tagSlots _ _ _ (by
    intro j h
    have hv:=congrArg (fun k : Fin 28=>k.val) h
    fin_cases j <;> simp only [tagSlots,savedSlot] at hv <;> dsimp at hv <;> omega)]
  exact RecoveryLiteralDecode.output_variable s which word

theorem output_sign (s : State) (which : Fin 3) (word : List Bool) :
    output s which word 23=[decide ((Nat.unpair (value word)).1≠0)] := by
  have h := install_slot tagSlots (by decide) (RecoveryLiteralDecode.output s which word) (tagOutput s word) 1
  change output s which word 23=[RecoveryLiteralTag.nonzero (tagWord word)] at h
  rw [h]
  have hv : value (tagWord word)=(Nat.unpair (value word)).1 := (RecoveryFixedUnpair.word_values word).1
  unfold RecoveryLiteralTag.nonzero
  simp only [hv]

theorem output_valid (s : State) (which : Fin 3) (word : List Bool) :
    output s which word 27=[decide ((Nat.unpair (value word)).1≤1)] := by
  have h := install_slot tagSlots (by decide) (RecoveryLiteralDecode.output s which word) (tagOutput s word) 2
  change output s which word 27=[decide (value (tagWord word)≤1)] at h
  rw [h]
  have hv : value (tagWord word)=(Nat.unpair (value word)).1 := (RecoveryFixedUnpair.word_values word).1
  simp only [hv]

end NearCubicWires.RepairOrdinary.RecoveryCheckedLiteral
