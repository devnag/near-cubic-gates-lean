import Proof.PCP.PCPPNativeCanonicalTreeWeight

/-! The next actual tree consumer reads the physical branch flag. A branch
executes the second reusable unpair, leaving its left child at0 and its right
child at18; every other tag retains the first payload. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeCanonicalTree
open LocalBitMultitape RecoveryExecution RecoveryRootRound RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev headStates := Fintype.card (RecoveryCalls.Control RecoveryDecodeStep.sizes)+
  Fintype.card (RecoveryCalls.Control RecoveryRowKind.sizes)
abbrev decodeStates := Fintype.card (RecoveryCalls.Control RecoveryDecodeStep.sizes)
def stepSizes : Fin 2→ℕ := ![headStates,decodeStates]
noncomputable def stepPrograms : (j : Fin 2)→Machine 26 (stepSizes j)
  | ⟨0,_⟩=>head
  | ⟨1,_⟩=>decode true
  | ⟨n+2,h⟩=>False.elim (by omega)
def stepNext (j : Fin 2) (_ : Fin (stepSizes j)) (scanned : Fin 26→Bool) : Option (Fin 2) :=
  if j.val=0 && scanned 25 then some 1 else none
noncomputable def stepMachine := RecoveryCalls.machine stepSizes stepPrograms 0 stepNext
def branch (d : Data) : Prop := (Nat.unpair (value d.bits)).1=2
instance (d : Data) : Decidable (branch d) := inferInstanceAs (Decidable ((Nat.unpair (value d.bits)).1=2))
def stepped (d : Data) := if branch d then decoded true (classified d) else classified d
def stepTime (d : Data) := if branch d then headTime d+1+(RecoveryDecodeStep.time (classified d).bits+1) else headTime d+1

theorem classified_flag_tape (d : Data) : (classified d).tapes 25=[decide (branch d)] := by
  change [(classified d).flags 2]=_
  rw [classified_flag]
  rfl

theorem step_ready (d : Data) (hd : d.Valid) :
    ReadyRun stepMachine (stepTime d) d.tapes (stepped d).tapes := by
  have hin:controlConfig (RecoveryCalls.code stepSizes 0)
      (initialConfiguration (stepPrograms 0) d.tapes)=initialConfiguration stepMachine d.tapes:=rfl
  by_cases hb:branch d
  · have hp:=(head_ready d hd).call stepSizes stepPrograms 0 stepNext 0 1 (by
      intro q
      simp [stepNext,classified_flag_tape,hb,readTapeBit])
    have hc:=(decode_ready true (classified d) (classified_valid d)).stop stepSizes stepPrograms 0 stepNext 1 (by intro q;rfl)
    have h:=hp.trans hc
    rw [hin] at h
    obtain ⟨r,hr,hf,hs⟩:=h.run (by simp [RecoveryCalls.machine,RecoveryCalls.stopped])
    exact ⟨r,by simpa only [stepTime,if_pos hb,run,stepMachine] using hr,
      by simp [hf,RecoveryCalls.stopped,stepped,hb],by intro i;simp [hf,RecoveryCalls.stopped],
      by simpa only [stepTime,if_pos hb] using hs⟩
  · have h:=(head_ready d hd).stop stepSizes stepPrograms 0 stepNext 0 (by
      intro q
      simp [stepNext,classified_flag_tape,hb,readTapeBit])
    rw [hin] at h
    obtain ⟨r,hr,hf,hs⟩:=h.run (by simp [RecoveryCalls.machine,RecoveryCalls.stopped])
    exact ⟨r,by simpa only [stepTime,if_neg hb,run,stepMachine] using hr,
      by simp [hf,RecoveryCalls.stopped,stepped,hb],by intro i;simp [hf,RecoveryCalls.stopped],
      by simpa only [stepTime,if_neg hb] using hs⟩

theorem stepped_valid (d : Data) : (stepped d).Valid := by
  unfold stepped
  split
  · exact decoded_valid true (classified d)
  · exact classified_valid d

theorem stepped_width (d : Data) : (stepped d).bits.length=d.bits.length := by
  unfold stepped
  split <;> simp [decoded,classified,RecoveryChildSelection.word_length]

theorem step_bound (d : Data) : stepTime d≤262144*(d.bits.length+1)^2 := by
  have hh:=head_bound d
  have hd:=RecoveryDecodeStep.time_bound (classified d).bits
  have hw:(classified d).bits.length=d.bits.length:=RecoveryChildSelection.word_length false d.bits
  simp only [RecoveryDecodeStep.budget,hw] at hd
  unfold stepTime
  split <;> nlinarith

def rightChild (d : Data) := RecoveryFixedUnpair.rightWord (classified d).bits

theorem branch_values (d : Data) (hb:branch d) :
    value (stepped d).bits=(Nat.unpair (Nat.unpair (value d.bits)).2).1 ∧
      value (rightChild d)=(Nat.unpair (Nat.unpair (value d.bits)).2).2 := by
  have h0:=classified_payload d
  constructor
  · rw [stepped,if_pos hb]
    exact (RecoveryDecodeStep.child_value true (classified d).bits).trans (by simp only [h0,↓reduceIte])
  · exact (RecoveryFixedUnpair.word_values (classified d).bits).2.trans (by rw [h0])

theorem branch_right (d : Data) (hb:branch d) :
    (stepped d).tapes 18=ZeroPadding.pad (RecoveryReusableUnpair.capacity d.bits) (frame (rightChild d)) := by
  rw [stepped,if_pos hb]
  change ZeroPadding.pad (RecoveryReusableUnpair.capacity (classified d).bits) (frame (rightChild d))=_
  have hw:(classified d).bits.length=d.bits.length:=RecoveryChildSelection.word_length false d.bits
  simp only [RecoveryReusableUnpair.capacity,RecoveryTapeSupport.capacity,hw]

theorem stepped_flags (d : Data) : (stepped d).flags=(classified d).flags := by
  unfold stepped
  split <;> rfl

end NearCubicWires.RepairOrdinary.PCPPNativeCanonicalTree
