import Proof.CaseAnalysis.RecoveryLiteralMeaning
import Proof.Amplification.RecoverySourceLiteralDriver
import Proof.Amplification.RecoveryProjectionWidthBudget

namespace NearCubicWires.RepairOrdinary.RecoveryBoundedLiteralDriver
open LocalBitMultitape RepairRepresentation RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def code (index : ℕ) (negative : Bool):=(2*index+negative.toNat).bits
def input (index C : ℕ) (negative : Bool) (i : Fin 11):=
  ZeroPadding.pad C (RepairSource.RecoverySourceLiteral.driverInput (code index negative) i)

theorem driver_capacity (index W C : ℕ) (negative : Bool) (hi : index ≤ W)
    (hC : 16384*(W+1)^2 ≤ C) :
    RepairSource.RecoverySourceLiteral.driverBudget index negative+1 ≤ C ∧
      (frame (code index negative)).length ≤ C := by
  have hn : negative.toNat ≤ 1 := by cases negative <;> decide
  have hb:=RepairSource.RecoveryProjectionRows.bits_le_value (2*index+negative.toNat)
  have hp : Unary.budget (code index negative) ≤ 24*(2*W+2)^2 := by
    unfold Unary.budget code
    rw [DimensionProducer.bits_value]
    calc
      24*(2*index+negative.toNat+1)*((2*index+negative.toNat).bits.length+1) ≤
          24*(2*W+2)*(2*W+2) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 24 (by omega)) (by omega)
      _=24*(2*W+2)^2 := by ring
  constructor
  · unfold RepairSource.RecoverySourceLiteral.driverBudget RepairSource.RecoverySourceLiteral.budget Counter.budget
    change Unary.budget (code index negative)+4*index+2*negative.toNat+9+1+(10*index+13)+1 ≤ C
    nlinarith [Nat.zero_le (W^2)]
  · rw [frame_length]
    change 2*(2*index+negative.toNat).bits.length+1 ≤ C
    nlinarith [Nat.zero_le (W^2)]

theorem driver_run (index W C : ℕ) (negative : Bool) (hi : index ≤ W)
    (hC : 16384*(W+1)^2 ≤ C) : ∃ out,
    ClockJoin.ReadyRun RepairSource.RecoverySourceLiteral.driverMachine
      (RepairSource.RecoverySourceLiteral.driverBudget index negative) (input index C negative) out ∧
      out 6=ZeroPadding.pad C [negative] ∧ out 9=ZeroPadding.pad C (RepairSource.VerifierDecoding.CompareMachine.word index) ∧
      (∀ i,(out i).length ≤ C) := by
  obtain ⟨out,hr,hflag,hindex⟩:=RepairSource.RecoverySourceLiteral.driver_run index negative
  have padded:=PCPPairReusable.padded_ready _ _ _ hr (fun _=>C)
  obtain ⟨p,pr,pt,ph,ps⟩:=padded
  obtain ⟨htime,hfield⟩:=driver_capacity index W C negative hi hC
  have hinput (i : Fin 11) : (RepairSource.RecoverySourceLiteral.driverInput (code index negative) i).length ≤ C := by
    unfold RepairSource.RecoverySourceLiteral.driverInput
    split_ifs
    · exact hfield
    · exact Nat.zero_le _
  have hsupport:=RecoveryTapeSupport.run_support RepairSource.RecoverySourceLiteral.driverMachine _ _ p pr C 0
    (by intro i;exact Nat.zero_le _) (by
      intro i
      change (ZeroPadding.pad C (RepairSource.RecoverySourceLiteral.driverInput (code index negative) i)).length ≤ max C (0+1)
      rw [ZeroPadding.pad_length,max_eq_left (hinput i)]
      exact Nat.le_max_left _ _)
  refine ⟨_,⟨p,pr,pt,ph,ps⟩,congrArg (ZeroPadding.pad C) hflag,congrArg (ZeroPadding.pad C) hindex,?_⟩
  intro i
  have h:=hsupport i
  rw [pt] at h
  exact h.trans (max_le le_rfl (by omega))

end NearCubicWires.RepairOrdinary.RecoveryBoundedLiteralDriver
