import Proof.Amplification.RecoveryQueryStep
import Proof.Amplification.RecoveryCommittedBitGraph

/-! A high true bit outside the committed count keeps every physical query
operand canonical, without changing any constrained assignment position. -/
namespace NearCubicWires.RepairSource.RecoveryPrefix
open RepairOrdinary RadixSemantics RecoveryOracle RecoveryQuery TseitinCNF
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def commitment (xs : List Bool) : Nat := value (xs++[false,true])
def queryCount (xs : List Bool) : Nat := xs.length+1

theorem suffix_positive (xs : List Bool) : 0<value (xs++[true]) := by
  induction xs with
  | nil => decide
  | cons b xs ih => simp only [List.cons_append,value]; omega

theorem suffix_canonical (xs : List Bool) : (value (xs++[true])).bits=xs++[true] := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    have he : value ((b::xs)++[true])=Nat.bit b (value (xs++[true])) := by
      cases b <;> simp [value,Nat.bit]
      omega
    rw [he,Nat.bits_append_bit _ _ (by intro hz; have hp:=suffix_positive xs; omega),ih]
    rfl

@[simp] theorem commitment_bits (xs : List Bool) : (commitment xs).bits=xs++[false,true] := by
  simpa [commitment,List.append_assoc] using suffix_canonical (xs++[false])
@[simp] theorem commitment_length (xs : List Bool) : (commitment xs).bits.length=xs.length+2 := by
  simp

theorem bitAt_getD (bits : List Bool) (i : Nat) : RecoveryCommittedBit.bitAt bits i=bits.getD i false := by
  induction bits generalizing i with
  | nil => simp [RecoveryCommittedBit.bitAt,List.getD]
  | cons b bs ih => cases i <;> simp [RecoveryCommittedBit.bitAt,List.getD,ih]

theorem commitment_bit (xs : List Bool) (i : Nat) (hi : i<queryCount xs) :
    (commitment xs).testBit i=(xs++[false]).getD i false := by
  unfold commitment
  rw [←RecoveryCommittedBit.bitAt_testBit,bitAt_getD]
  have hil : i<(xs++[false]).length := by simp only [List.length_append,List.length_singleton]; exact hi
  have he : xs++[false,true]=(xs++[false])++[true] := by simp
  rw [he]
  exact List.getD_append _ _ _ _ hil

theorem query_iff (flat : Bool) (payload : Nat) (formula : EncodedCNF) (xs : List Bool)
    (hdecode : PayloadDecodes flat payload formula) :
    correctedSat (code flat payload (commitment xs) (queryCount xs))=true ↔
      formula.all (fun clause => clause.length=3)=true ∧
        ∃ assignment : Nat→Bool,
          (∀ i<xs.length+1,assignment i=(xs++[false]).getD i false) ∧
          formulaEval assignment formula=true := by
  rw [query_meaning flat payload (commitment xs) (queryCount xs) formula hdecode]
  unfold compactMeaning
  apply and_congr_right
  intro _
  apply exists_congr
  intro assignment
  apply and_congr_left
  intro _
  apply forall_congr'
  intro i
  apply imp_congr_right
  intro hi
  rw [commitment_bit xs i hi]

end NearCubicWires.RepairSource.RecoveryPrefix
