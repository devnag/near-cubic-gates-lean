import Proof.Amplification.RecoverySourceLiteralSplit

/-! The original source literal produces its physical field-lookup driver.
The sign remains the source's negative flag; the later CNF literal encoding
uses its complement for the original Bool×Nat positive convention. -/
namespace NearCubicWires.RepairSource.RecoverySourceLiteral
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound RadixSemantics
open VerifierDecoding ProjectionNormalization SourceInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def nativeSlots (i : Fin 8) : Fin 11 := i.castAdd 3
def countSlots : Fin 4→Fin 11 := ![5,8,9,10]
theorem native_injective : Function.Injective nativeSlots := by
  intro a b h; exact Fin.ext (congrArg (fun i : Fin 11=>i.val) h)
theorem count_injective : Function.Injective countSlots := by decide
noncomputable def nativeMachine := RecoveryFocus.machine nativeSlots machine
noncomputable def countMachine := RecoveryFocus.machine countSlots Counter.machine
noncomputable def driverMachine := Composition.machine nativeMachine countMachine
def driverInput (bits : List Bool) (i : Fin 11) := if i=0 then RepairOrdinary.frame bits else []
noncomputable def driverMiddle (bits : List Bool) (out : Fin 8→List Bool) := install nativeSlots (driverInput bits) out
def driverBudget (index : Nat) (negative : Bool) := budget index negative+1+Counter.budget index

theorem driver_run (index : Nat) (negative : Bool) : ∃ out,
    ClockJoin.ReadyRun driverMachine (driverBudget index negative)
      (driverInput (2*index+negative.toNat).bits) out ∧
      out 6=[negative] ∧ out 9=CompareMachine.word index := by
  obtain ⟨parsed,hparsed,hIndex,hNegative⟩ := split_run index negative
  have first := hparsed.focus nativeSlots native_injective (driverInput (2*index+negative.toNat).bits)
    (by intro i; fin_cases i <;> rfl)
  obtain ⟨count,hcount,_hraw,hCounter⟩ := DriverAtoms.counter_run index
  have second := hcount.focus countSlots count_injective (driverMiddle (2*index+negative.toNat).bits parsed) (by
    intro i; fin_cases i
    · change install nativeSlots _ _ (nativeSlots 5)=_
      rw [install_slot _ native_injective]
      exact hIndex
    all_goals
      rw [driverMiddle,install_other _ _ _ _ (by intro j; fin_cases j <;> decide)]
      rfl)
  have hall := ClockJoin.join _ _ _ _ _ _ _ first second
  refine ⟨_,hall,?_,?_⟩
  · rw [install_other _ _ _ _ (by intro i; fin_cases i <;> decide)]
    change install nativeSlots _ _ (nativeSlots 6)=_
    rw [install_slot _ native_injective]
    exact hNegative
  · change install countSlots _ _ (countSlots 2)=_
    rw [install_slot _ count_injective]
    exact hCounter

def index {q : Nat} : Literal q→Nat
  | .positive j=>j.val
  | .negative j=>j.val
def negative {q : Nat} : Literal q→Bool
  | .positive _=>false
  | .negative _=>true

theorem literal_code {q : Nat} (literal : Literal q) :
    literalCode literal=2*index literal+(negative literal).toNat := by
  cases literal <;> rfl

theorem literal_run {q : Nat} (literal : Literal q) : ∃ out,
    ClockJoin.ReadyRun driverMachine (driverBudget (index literal) (negative literal))
      (driverInput (literalCode literal).bits) out ∧
      out 6=[negative literal] ∧ out 9=CompareMachine.word (index literal) := by
  rw [literal_code]
  exact driver_run (index literal) (negative literal)

end NearCubicWires.RepairSource.RecoverySourceLiteral
