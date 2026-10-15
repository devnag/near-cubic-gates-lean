import Proof.Amplification.RecoveryProjectionInitializeBank
import Proof.Amplification.RecoveryPaddedCopyWhole

/-! The actual fixed-width copy writes the initial all-false randomness
from the allocated empty field. Its source and scratch are reused in place. -/
namespace NearCubicWires.RepairSource.RecoveryProjectionInitialize
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def copySlots : Fin 4→Fin 36 := ![0,29,34,1]
theorem copy_injective : Function.Injective copySlots := by decide
noncomputable def randomMachine := RecoveryFocus.machine copySlots RecoveryColdPaddedCopy.machine
def randomized (cap R Q : Nat) (source : List Bool) :=
  Function.update (erased cap R Q source) 29 (RepairOrdinary.frame (List.replicate R false))

private theorem pad_false (cap n : Nat) (hn : n≤cap) :
    ZeroPadding.pad cap (List.replicate n false)=List.replicate cap false := by
  simp only [ZeroPadding.pad,List.length_replicate,←List.replicate_add,Nat.add_sub_of_le hn]

private theorem zero_data (R : Nat) : RecoveryColdPaddedCopy.data [] R=List.replicate R false := by
  have hz : readTapeBit ([] : List Bool)=(fun _=>false) := by funext i; rfl
  have hm (xs : List Nat) : xs.map (fun _=>false)=List.replicate xs.length false := by
    induction xs with
    | nil=>rfl
    | cons x xs ih=>simp only [List.map_cons,List.length_cons,List.replicate_succ,ih]
  simpa only [RecoveryColdPaddedCopy.data,hz,List.length_range] using hm (List.range R)

theorem random_ready (cap R Q : Nat) (source : List Bool) (hc : 2*R+3≤cap) :
    ClockJoin.ReadyRun randomMachine (4*R+8) (erased cap R Q source) (randomized cap R Q source) := by
  classical
  obtain ⟨r,hr,ht,hh,hs⟩ := RecoveryColdPaddedCopy.copy_ready [] R
  have base : ClockJoin.ReadyRun RecoveryColdPaddedCopy.machine (4*R+8)
      ![RepairOrdinary.frame [],[],VerifierDecoding.CompareMachine.word R,[]]
      ![RepairOrdinary.frame [],RepairOrdinary.frame (RecoveryColdPaddedCopy.data [] R),
        VerifierDecoding.CompareMachine.word R,List.replicate (2*R+3) false] := ⟨r,hr,ht,hh,hs.le⟩
  have hp := PCPPairReusable.padded_ready _ _ _ base ![cap,0,0,cap]
  have hi : ∀ i,erased cap R Q source (copySlots i)=
      ZeroPadding.pad (![cap,0,0,cap] i)
        (![RepairOrdinary.frame [],[],VerifierDecoding.CompareMachine.word R,[]] i) := by
    intro i; fin_cases i
    · change List.replicate cap false=ZeroPadding.pad cap (List.replicate 1 false)
      exact (pad_false cap 1 (by omega)).symm
    · exact (ZeroPadding.pad_zero []).symm
    · exact (ZeroPadding.pad_zero _).symm
    · rfl
  have focused := hp.focus copySlots copy_injective (erased cap R Q source) hi
  have he : install copySlots (erased cap R Q source)
      (fun i=>ZeroPadding.pad (![cap,0,0,cap] i)
        (![RepairOrdinary.frame [],RepairOrdinary.frame (RecoveryColdPaddedCopy.data [] R),
          VerifierDecoding.CompareMachine.word R,List.replicate (2*R+3) false] i))=
        randomized cap R Q source := by
    funext i
    by_cases h0 : i=0
    · subst i
      change install copySlots _ _ (copySlots 0)=_
      rw [install_slot _ copy_injective]
      change ZeroPadding.pad cap (List.replicate 1 false)=List.replicate cap false
      exact pad_false cap 1 (by omega)
    by_cases h29 : i=29
    · subst i
      change install copySlots _ _ (copySlots 1)=_
      rw [install_slot _ copy_injective]
      change ZeroPadding.pad 0 (RepairOrdinary.frame (RecoveryColdPaddedCopy.data [] R))=_
      rw [ZeroPadding.pad_zero,zero_data]
      simp only [randomized,Function.update_self]
    by_cases h34 : i=34
    · subst i
      change install copySlots _ _ (copySlots 2)=_
      rw [install_slot _ copy_injective]
      exact ZeroPadding.pad_zero _
    by_cases h1 : i=1
    · subst i
      change install copySlots _ _ (copySlots 3)=_
      rw [install_slot _ copy_injective]
      exact pad_false cap (2*R+3) hc
    have hn : ∀ j,copySlots j≠i := by
      intro j; fin_cases j <;> simpa only [copySlots,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
        Matrix.cons_val_three] using (Ne.symm (by assumption))
    rw [install_other _ _ _ _ hn]
    exact (Function.update_of_ne h29 _ _).symm
  rw [he] at focused
  exact focused

end NearCubicWires.RepairSource.RecoveryProjectionInitialize
