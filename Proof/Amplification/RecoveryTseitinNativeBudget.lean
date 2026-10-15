import Proof.Amplification.RecoveryTseitinNativeMasked
import Proof.PCP.PCPPNativeNodeReadBounds
import Proof.Amplification.RecoveryTseitinReferenceBound

/-! One paid cubic capacity works for every original well-formed node in
the retained verifier graph; no per-node canonical reference is an input. -/
namespace NearCubicWires.RepairSource.RecoveryTseitinNative.Reuse
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def capacity (n count : Nat) := 2199023255552*(n+count+1)^3
theorem operand_bound {n : Nat} (index : Nat) (node : BooleanNode n) (hw : node.WellFormedAt index)
    (j : Fin 2) : PCPPRequestNodeSchema.fields node (![1,2] j) ≤ n+index+1 := by
  cases node with
  | const b => cases b <;> fin_cases j <;> dsimp [PCPPRequestNodeSchema.fields] <;> omega
  | input v => have hv:=v.isLt; fin_cases j <;> dsimp [PCPPRequestNodeSchema.fields] <;> omega
  | not v => change v < index at hw; fin_cases j <;> dsimp [PCPPRequestNodeSchema.fields] <;> omega
  | and v w => rcases hw with ⟨hv,hw⟩; fin_cases j <;> dsimp [PCPPRequestNodeSchema.fields] <;> omega
  | or v w => rcases hw with ⟨hv,hw⟩; fin_cases j <;> dsimp [PCPPRequestNodeSchema.fields] <;> omega

theorem node_budget_bound {n : Nat} (count index : Nat) (hi : index ≤ count) (node : BooleanNode n)
    (hw : node.WellFormedAt index) : coldNodeBudget index node ≤ capacity n count := by
  let R:=n+count+1
  let a:=PCPPRequestNodeSchema.fields node 1
  let b:=PCPPRequestNodeSchema.fields node 2
  let tag:=(PCPPRequestNodeSchema.tag node).val
  have hr : 1 ≤ R := by dsimp [R]; omega
  have ha : a ≤ R := (operand_bound index node hw 0).trans (by dsimp [R]; omega)
  have hb : b ≤ R := (operand_bound index node hw 1).trans (by dsimp [R]; omega)
  have ht : tag < 5 := (PCPPRequestNodeSchema.tag node).isLt
  have hread:= (PCPPNativeNodeRead.budget_bound tag a b).trans
    (Nat.mul_le_mul_left 256 (Nat.pow_le_pow_left (by omega : tag+a+b+1 ≤ 7*R) 2))
  have href:=(RecoveryTseitinReferences.cold_budget_bound n index a b).trans
    (Nat.mul_le_mul_left 34359738368 (Nat.pow_le_pow_left (by dsimp [R] at *; omega : n+index+a+b+1 ≤ 3*R) 3))
  have hd : RecoveryTseitinTautology.Cold.driverCapacity (n+index) ≤ 33554432*R^2 :=
    Nat.mul_le_mul_left 33554432 (Nat.pow_le_pow_left (by dsimp [R]; omega) 2)
  have hr2 : R ≤ R^2 := by nlinarith
  have hr3 : R^2 ≤ R^3 := by nlinarith [Nat.mul_le_mul_left (R^2) hr]
  have he : coldNodeBudget index node=PCPPNativeNodeRead.budget tag a b+4*a+4*b+
      RecoveryTseitinReferences.coldBudget n index a b+62*RecoveryTseitinTautology.Cold.driverCapacity (n+index)+63 := by
    unfold coldNodeBudget referencesBudget operandsBudget
    dsimp only [a,b,tag]
    omega
  rw [he]
  change _ ≤ 2199023255552*R^3
  nlinarith

end NearCubicWires.RepairSource.RecoveryTseitinNative.Reuse
