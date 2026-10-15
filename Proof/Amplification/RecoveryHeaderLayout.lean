import Proof.Amplification.RecoveryPaddedCopyMeaning

/-! Fixed twenty-tape cold header layout. The produced unary width drives
three actual padded copies; the already checked erase producer then derives
its exact quadratic driver from the padded original code. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdHeader
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def width (bits : List Bool) := RecoveryColdWidth.width bits.length
def bound (bits : List Bool) := ClockBinary.word (max 1 bits.length)
def codeWord (bits : List Bool) := RecoveryColdPaddedCopy.data bits (width bits)
def boundWord (bits : List Bool) := RecoveryColdPaddedCopy.data (bound bits) (width bits)
def zeroWord (bits : List Bool) := RecoveryColdPaddedCopy.data [] (width bits)
def copyReset (bits : List Bool) := List.replicate (2*width bits+3) false

def fields0 : Fin 6→List Bool := fun _=>[]
def fields1 (bits : List Bool) : Fin 6→List Bool := ![frame (codeWord bits),copyReset bits,[],[],[],[]]
def fields2 (bits : List Bool) : Fin 6→List Bool :=
  ![frame (codeWord bits),copyReset bits,frame (boundWord bits),copyReset bits,[],[]]
def fields3 (bits : List Bool) : Fin 6→List Bool :=
  ![frame (codeWord bits),copyReset bits,frame (boundWord bits),copyReset bits,frame (zeroWord bits),copyReset bits]
def base (bits : List Bool) (cap scratch : Nat) (fields : Fin 6→List Bool) : Fin 20→List Bool :=
  ![frame bits,RecoveryColdWidth.word (width bits),frame (bound bits),List.replicate cap false,List.replicate scratch false,
    fields 0,fields 1,fields 2,fields 3,fields 4,fields 5,[false],[],[],[],[],[],[],[],[]]
def copySlots (which : Fin 3) : Fin 4→Fin 20 :=
  ![![0,5,1,6],![2,7,1,8],![11,9,1,10]] which

def driverSlots : Fin 9→Fin 20 := ![5,12,13,14,15,16,17,18,19]
theorem copySlots_injective (which : Fin 3) : Function.Injective (copySlots which) := by fin_cases which <;> decide
theorem driverSlots_injective : Function.Injective driverSlots := by decide
noncomputable def copyMachine (which : Fin 3) := RecoveryFocus.machine (copySlots which) RecoveryColdPaddedCopy.machine
noncomputable def driverMachine := RecoveryFocus.machine driverSlots RecoveryEraseDriver.machine
noncomputable def output (bits : List Bool) (cap scratch : Nat) :=
  install driverSlots (base bits cap scratch (fields3 bits)) (RecoveryEraseDriver.output3 (codeWord bits))

end NearCubicWires.RepairOrdinary.RecoveryColdHeader
