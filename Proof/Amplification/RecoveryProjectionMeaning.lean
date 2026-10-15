import Proof.Amplification.RecoveryProjectionSelect
import Proof.MachineModel.GeneratedAmplifierSemantics

/-! The selector's two physical tag bits implement precisely the original
normalized PCP projection encoding, including constants and width zero. -/
namespace NearCubicWires.RepairSource.RecoveryProjectionSelect
open LocalBitMultitape RepairOrdinary SourceInterfaces RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem read_value (bits : List Bool) (k : Nat) : readTapeBit bits k=(value bits).testBit k :=
  (GeneratedAmplifier.value_bit bits k).symm

theorem result_value (tag code : List Bool) (picked : Bool) :
    result tag code picked=
      if (value tag).testBit 1 then (value code).testBit 0
      else if (value tag).testBit 0 then !picked else picked := by
  simp only [result,read_value]

theorem result_decoded (code : Nat) (picked : Bool) :
    result (RecoveryFixedUnpair.leftWord code.bits) code.bits picked=
      if (Nat.unpair code).1.testBit 1 then code.testBit 0
      else if (Nat.unpair code).1.testBit 0 then !picked else picked := by
  rw [result_value,(RecoveryFixedUnpair.word_values code.bits).1,CanonicalPositiveOutput.nat_bits_value]

theorem projection_meaning {n : Nat} (p : ProjectedRandomBit n) (randomness : BitInput n) :
    result (RecoveryFixedUnpair.leftWord (projectionCode p).bits) (projectionCode p).bits
      ((value (List.ofFn randomness)).testBit (Nat.unpair (projectionCode p)).2)=p.eval randomness := by
  rw [result_decoded]
  cases p with
  | bit i =>
    simp only [projectionCode,Nat.unpair_pair,show (0 : Nat).testBit 1=false by decide,
      show (0 : Nat).testBit 0=false by decide,Bool.false_eq_true,if_false,ProjectedRandomBit.eval]
    exact GeneratedAmplifier.address_bit randomness i
  | negatedBit i =>
    simp only [projectionCode,Nat.unpair_pair,show (1 : Nat).testBit 1=false by decide,
      show (1 : Nat).testBit 0=true by decide,Bool.false_eq_true,if_false,if_true,ProjectedRandomBit.eval]
    exact congrArg Bool.not (GeneratedAmplifier.address_bit randomness i)
  | constant b =>
    simp only [projectionCode,Nat.unpair_pair,show (2 : Nat).testBit 1=true by decide,
      if_true,ProjectedRandomBit.eval]
    cases b <;> decide

end NearCubicWires.RepairSource.RecoveryProjectionSelect
