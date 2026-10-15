import Proof.Amplification.RecoveryHeaderLayout

/-! All three padded fields and the erase driver are executed from the
same cold header bank. Each copy retains the shared actual width driver. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdHeader
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem install_pair {t : Nat} (slots : Fin 4→Fin t) (hi : Function.Injective slots)
    (ambient : Fin t→List Bool) (replacement : Fin 4→List Bool)
    (h0 : replacement 0=ambient (slots 0)) (h2 : replacement 2=ambient (slots 2)) :
    install slots ambient replacement=
      Function.update (Function.update ambient (slots 1) (replacement 1)) (slots 3) (replacement 3) := by
  classical
  funext i
  cases hp : RecoveryFocus.pick slots i with
  | none=>
    have hn (j : Fin 4) : slots j ≠ i := by
      intro he
      rw [←he,RecoveryFocus.pick_slot slots hi] at hp
      cases hp
    simp [install,hp,Function.update,Ne.symm (hn 1),Ne.symm (hn 3)]
  | some j=>
    have he := RecoveryFocus.slot_of_pick slots hp
    subst i
    rw [install_slot slots hi]
    fin_cases j <;> simp [Function.update,hi.eq_iff,h0,h2]

theorem code_install (bits : List Bool) (cap scratch : Nat) : install (copySlots 0) (base bits cap scratch fields0)
    ![frame bits,frame (RecoveryColdPaddedCopy.data bits (width bits)),CompareMachine.word (width bits),copyReset bits]=
    base bits cap scratch (fields1 bits) := by
  rw [install_pair (copySlots 0) (copySlots_injective 0) _ _ (by rfl) (by rfl)]
  funext i
  fin_cases i <;> rfl

theorem code_ready (bits : List Bool) (cap scratch : Nat) :
    ReadyRun (copyMachine 0) (4*width bits+8) (base bits cap scratch fields0) (base bits cap scratch (fields1 bits)) := by
  have h := (RecoveryColdPaddedCopy.copy_ready bits (width bits)).focus (copySlots 0) (copySlots_injective 0)
    (base bits cap scratch fields0) (by intro j; fin_cases j <;> rfl)
  have he := code_install bits cap scratch
  unfold copyReset at he
  rw [he] at h
  exact h

theorem bound_install (bits : List Bool) (cap scratch : Nat) : install (copySlots 1) (base bits cap scratch (fields1 bits))
    ![frame (bound bits),frame (RecoveryColdPaddedCopy.data (bound bits) (width bits)),CompareMachine.word (width bits),copyReset bits]=
    base bits cap scratch (fields2 bits) := by
  rw [install_pair (copySlots 1) (copySlots_injective 1) _ _ (by rfl) (by rfl)]
  funext i
  fin_cases i <;> rfl

theorem bound_ready (bits : List Bool) (cap scratch : Nat) :
    ReadyRun (copyMachine 1) (4*width bits+8) (base bits cap scratch (fields1 bits)) (base bits cap scratch (fields2 bits)) := by
  have h := (RecoveryColdPaddedCopy.copy_ready (bound bits) (width bits)).focus (copySlots 1) (copySlots_injective 1)
    (base bits cap scratch (fields1 bits)) (by intro j; fin_cases j <;> rfl)
  have he := bound_install bits cap scratch
  unfold copyReset at he
  rw [he] at h
  exact h

theorem zero_install (bits : List Bool) (cap scratch : Nat) : install (copySlots 2) (base bits cap scratch (fields2 bits))
    ![frame [],frame (RecoveryColdPaddedCopy.data [] (width bits)),CompareMachine.word (width bits),copyReset bits]=
    base bits cap scratch (fields3 bits) := by
  rw [install_pair (copySlots 2) (copySlots_injective 2) _ _ (by rfl) (by rfl)]
  funext i
  fin_cases i <;> rfl

theorem zero_ready (bits : List Bool) (cap scratch : Nat) :
    ReadyRun (copyMachine 2) (4*width bits+8) (base bits cap scratch (fields2 bits)) (base bits cap scratch (fields3 bits)) := by
  have h := (RecoveryColdPaddedCopy.copy_ready [] (width bits)).focus (copySlots 2) (copySlots_injective 2)
    (base bits cap scratch (fields2 bits)) (by intro j; fin_cases j <;> rfl)
  have he := zero_install bits cap scratch
  unfold copyReset at he
  rw [he] at h
  exact h

theorem driver_ready (bits : List Bool) (cap scratch : Nat) :
    ReadyRun driverMachine (RecoveryEraseDriver.time (codeWord bits))
      (base bits cap scratch (fields3 bits)) (output bits cap scratch) :=
  (RecoveryEraseDriver.driver_ready (codeWord bits)).focus driverSlots driverSlots_injective
    (base bits cap scratch (fields3 bits)) (by intro j; fin_cases j <;> rfl)

end NearCubicWires.RepairOrdinary.RecoveryColdHeader
