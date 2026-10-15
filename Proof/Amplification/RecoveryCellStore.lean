import Proof.Amplification.RecoveryClausePredicate
import Proof.Amplification.RecoveryRawListStep

/-! Preserve a raw list cell's head before the next reusable unpair erases
scratch. The actual tail remains on input0 and the head is copied to a fresh
external framed field. The reusable original-width driver is retained. -/
namespace NearCubicWires.RepairOrdinary.RecoveryCellStore
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tapes (base : Fin 24 → List Bool) (saved : List Bool) : Fin 25 → List Bool :=
  Fin.addCases (m := 24) (n := 1) (motive := fun _ => List Bool) base (fun _ => saved)
def headWord (bits : List Bool) := RecoveryChildSelection.word true (RecoveryRawListStep.reduced bits)
def base (bits : List Bool) (resetCapacity : Nat) := RecoveryRawListStep.decodeOutput false bits resetCapacity
def slots : Fin 4 → Fin 25 := ![17,24,16,22]
theorem slots_injective : Function.Injective slots := by decide
noncomputable def machine := RecoveryFocus.machine slots RecoveryFieldCopy.machine

theorem headWord_length (bits : List Bool) : (headWord bits).length=bits.length := by
  simp [headWord,RecoveryChildSelection.word_length]

theorem copy_ready (bits saved : List Bool) (resetCapacity : Nat)
    (hs : saved.length≤2*bits.length+1) :
    ReadyRun machine (8*bits.length+10)
      (tapes (base bits resetCapacity) saved) (tapes (base bits resetCapacity) (frame (headWord bits))) := by
  let reduced := RecoveryRawListStep.reduced bits
  let S := RecoveryReusableUnpair.capacity reduced
  let R := max (RecoveryRawListStep.reset1 bits resetCapacity) (S+1)
  have hlen : (headWord bits).length=bits.length := headWord_length bits
  have hcap : 4*bits.length+4≤R := by
    have h : 4*bits.length+4≤S+1 := by
      dsimp [S,reduced,RecoveryReusableUnpair.capacity,RecoveryTapeSupport.capacity]
      simp only [RecoveryRawListStep.reduced_length]
      nlinarith
    exact h.trans (Nat.le_max_right _ _)
  have hc := RecoveryChildSelection.ReadyRun.pad
    (RecoveryFieldCopy.copy_ready (headWord bits) [false] saved R (by rw [hlen]; exact hs)) ![S,0,S,0]
  have hsource : Streaming.marks (headWord bits)++[false]=frame (headWord bits) := by
    simpa [frame] using (Streaming.frame_append (headWord bits) []).symm
  simp only [hsource,hlen,Nat.max_eq_left hcap] at hc
  have hin : (fun i : Fin 4 => ZeroPadding.pad (![S,0,S,0] i)
      (![frame (headWord bits),saved,CompareMachine.word bits.length,List.replicate R false] i)) =
      ![ZeroPadding.pad S (frame (headWord bits)),saved,
        ZeroPadding.pad S (CompareMachine.word bits.length),List.replicate R false] := by
    funext i; fin_cases i <;> simp
  have hout : (fun i : Fin 4 => ZeroPadding.pad (![S,0,S,0] i)
      (![frame (headWord bits),frame (headWord bits),CompareMachine.word bits.length,List.replicate R false] i)) =
      ![ZeroPadding.pad S (frame (headWord bits)),frame (headWord bits),
        ZeroPadding.pad S (CompareMachine.word bits.length),List.replicate R false] := by
    funext i; fin_cases i <;> simp
  rw [hin,hout] at hc
  have h := hc.focus slots slots_injective (tapes (base bits resetCapacity) saved) (by
    intro j; fin_cases j
    all_goals first
      | rfl
      | (change ZeroPadding.pad S (CompareMachine.word (RecoveryRawListStep.reduced bits).length)=
          ZeroPadding.pad S (CompareMachine.word bits.length)
         rw [RecoveryRawListStep.reduced_length]))
  have he : install slots (tapes (base bits resetCapacity) saved)
      ![ZeroPadding.pad S (frame (headWord bits)),frame (headWord bits),
        ZeroPadding.pad S (CompareMachine.word bits.length),List.replicate R false] =
      tapes (base bits resetCapacity) (frame (headWord bits)) := by
    funext i
    fin_cases i
    case «17» => exact install_slot slots slots_injective _ _ 0
    case «24» => exact install_slot slots slots_injective _ _ 1
    case «16» =>
      apply (install_slot slots slots_injective _ _ 2).trans
      change ZeroPadding.pad S (CompareMachine.word bits.length)=
        ZeroPadding.pad S (CompareMachine.word (RecoveryRawListStep.reduced bits).length)
      rw [RecoveryRawListStep.reduced_length]
    case «22» => exact install_slot slots slots_injective _ _ 3
    all_goals exact install_other slots _ _ _ (by intro j; fin_cases j <;> decide)
  rw [he] at h
  exact h

theorem head_value (bits : List Bool) (hz : RadixSemantics.value bits≠0) :
    RadixSemantics.value (headWord bits)=(Nat.unpair (RadixSemantics.value bits-1)).1 :=
  RecoveryRawListStep.list_component true bits hz

end NearCubicWires.RepairOrdinary.RecoveryCellStore
