import Proof.Foundations.RecoverySourceContracts
import Proof.Amplification.RecoveryCommittedBitLookup

/-! The complete supplied table is in increasing integer address order.
Address bits are little endian, including the unique empty address at arity0. -/
namespace NearCubicWires.RepairOrdinary.GeneratedAmplifier
open SourceInterfaces ExecutableInterfaces RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem bitAt_eq_getD (bits : List Bool) (i : ℕ) :
    RecoveryCommittedBit.bitAt bits i=bits.getD i false := by
  induction bits generalizing i with
  | nil => simp [RecoveryCommittedBit.bitAt,List.getD]
  | cons b bs ih => cases i <;> simp [RecoveryCommittedBit.bitAt,List.getD,ih]

theorem value_bit (bits : List Bool) (i : ℕ) : (value bits).testBit i=bits.getD i false :=
  (RecoveryCommittedBit.bitAt_testBit bits i).symm.trans (bitAt_eq_getD bits i)

theorem address_lt {n : ℕ} (address : BitInput n) : value (List.ofFn address)<2^n := by
  simpa using value_lt (List.ofFn address)

theorem address_bit {n : ℕ} (address : BitInput n) (i : Fin n) :
    (value (List.ofFn address)).testBit i.val=address i := by
  rw [value_bit]
  simp [List.getD]

@[simp] theorem table_length {n : ℕ} (f : BoolFunction n) : (boolFunctionTable f).length=2^n := by
  simp [boolFunctionTable]

theorem table_lookup {n : ℕ} (f : BoolFunction n) (address : BitInput n) :
    (boolFunctionTable f)[value (List.ofFn address)]'(by simpa using address_lt address)=f address := by
  simp only [boolFunctionTable,List.getElem_map,List.getElem_range]
  congr 1
  funext i
  exact address_bit address i

def payload {n : ℕ} (f : BoolFunction n) (address : BitInput n) : List Bool :=
  frame n.bits++boolFunctionTable f++frame (List.ofFn address)

@[simp] theorem payload_length {n : ℕ} (f : BoolFunction n) (address : BitInput n) :
    (payload f address).length=2*n.bits.length+2^n+2*n+2 := by
  simp [payload]
  omega

theorem generated_input {c d : ℕ} {a : RepairSource.ScheduleAmplifier c d}
    (r : RepairSource.GeneratedAmplifierRequest a) : RepairSource.generatedAmplifierInput r=
      payload (a.output r.sourceArity r.sourceFunction).function r.address := rfl

end NearCubicWires.RepairOrdinary.GeneratedAmplifier
