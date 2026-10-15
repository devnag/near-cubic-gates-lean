import Proof.Amplification.RecoverySourceLiteralDriver
import Proof.Amplification.RecoveryAddressFieldLookup

/-! A complete actual source-literal/address lookup. Only the original
literal's binary field and actual address field stream are inputs. Its
source sign and selected address are retained at the original code boundary. -/
namespace NearCubicWires.RepairSource.RecoverySourceLiteralAddress
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
open VerifierDecoding ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def nativeSlots (i : Fin 11) : Fin 16 := i.castAdd 5
def lookupSlots : Fin 6→Fin 16 := ![11,12,9,13,14,15]
theorem native_injective : Function.Injective nativeSlots := by
  intro a b h; exact Fin.ext (congrArg (fun i : Fin 16=>i.val) h)
theorem lookup_injective : Function.Injective lookupSlots := by decide
noncomputable def nativeMachine := RecoveryFocus.machine nativeSlots RecoverySourceLiteral.driverMachine
noncomputable def lookupMachine := RecoveryFocus.machine lookupSlots RecoveryAddressFieldLookup.machine
noncomputable def machine := Composition.machine nativeMachine lookupMachine
def input (code source : List Bool) (i : Fin 16) :=
  if i=0 then RepairOrdinary.frame code else if i=11 then source else []
noncomputable def middle (code source : List Bool) (data : Fin 11→List Bool) := install nativeSlots (input code source) data
def budget (negative : Bool) (skipped : List (List Bool)) (bits : List Bool) :=
  RecoverySourceLiteral.driverBudget skipped.length negative+1+RecoveryAddressFieldLookup.budget skipped bits

theorem address_run (negative : Bool) (skipped : List (List Bool)) (bits suffix : List Bool) : ∃ out,
    ClockJoin.ReadyRun machine (budget negative skipped bits)
      (input (2*skipped.length+negative.toNat).bits (FieldList.stream skipped++RepairOrdinary.frame bits++suffix)) out ∧
      out 6=[negative] ∧ out 13=RepairOrdinary.frame bits ∧
      out 11=FieldList.stream skipped++RepairOrdinary.frame bits++suffix := by
  let code := (2*skipped.length+negative.toNat).bits
  let source := FieldList.stream skipped++RepairOrdinary.frame bits++suffix
  obtain ⟨native,hNative,hSign,hIndex⟩ := RecoverySourceLiteral.driver_run skipped.length negative
  have first := hNative.focus nativeSlots native_injective (input code source) (by intro i; fin_cases i <;> rfl)
  obtain ⟨look,hLook,hSource,_hCount,hAddress⟩ := RecoveryAddressFieldLookup.lookup_ready skipped bits suffix
  have second := hLook.focus lookupSlots lookup_injective (middle code source native) (by
    intro i; fin_cases i
    · rw [middle,install_other _ _ _ _ (by intro j; fin_cases j <;> decide)]
      rfl
    · rw [middle,install_other _ _ _ _ (by intro j; fin_cases j <;> decide)]
      rfl
    · change install nativeSlots _ _ (nativeSlots 9)=_
      rw [install_slot _ native_injective]
      exact hIndex
    all_goals
      rw [middle,install_other _ _ _ _ (by intro j; fin_cases j <;> decide)]
      rfl)
  have hall := ClockJoin.join _ _ _ _ _ _ _ first second
  refine ⟨_,hall,?_,?_,?_⟩
  · rw [install_other _ _ _ _ (by intro i; fin_cases i <;> decide)]
    change install nativeSlots _ _ (nativeSlots 6)=_
    rw [install_slot _ native_injective]
    exact hSign
  · change install lookupSlots _ _ (lookupSlots 3)=_
    rw [install_slot _ lookup_injective]
    exact hAddress
  · change install lookupSlots _ _ (lookupSlots 0)=_
    rw [install_slot _ lookup_injective]
    exact hSource

end NearCubicWires.RepairSource.RecoverySourceLiteralAddress
