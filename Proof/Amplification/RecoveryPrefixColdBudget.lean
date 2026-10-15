import Proof.Amplification.RecoveryPrefixSearch

/-! Cubic bound for the whole cold search, measured in binary payload width
and the actual requested prefix length. Constants include every local call. -/
namespace NearCubicWires.RepairSource.RecoveryPrefixCold
open RepairOrdinary ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def radius (payload total : Nat) := payload.bits.length+2*total+5

theorem budget_expansion (C payload total : Nat) : budget C payload total=
    20*total*C*(radius payload total)^2+6*C*(radius payload total)^2+
    10*C*radius payload total+8*C+2*RecoveryPrefixMeasure.mass payload total+
    12*payload.bits.length+31*total+132 := by
  simp only [budget,RecoveryPrefixColdPrepare.budget,RecoveryPrefixMeasure.budget,
    PCPSerializerCapacity.Power.budget,RecoveryPrefixSearch.budget,RecoveryPrefixOutput.budget,
    RecoveryPrefixColdPrepare.capacity,RecoveryPrefixMeasure.mass,RecoveryPrefixMeasure.request,
    List.length_append,frame_length,List.length_replicate,DimensionPower.cost,
    Nat.pow_zero,Nat.pow_one,WilliamsUnaryProduct.budget,radius]
  ring

theorem budget_bound (C payload total : Nat) :
    budget C payload total  ≤  (40*C+200)*(radius payload total)^3 := by
  let m := radius payload total
  let X := m^3
  have hm : 1 ≤ m := by dsimp [m,radius]; omega
  have hX : 1 ≤ X := Nat.one_le_pow _ _ hm
  have hmX : m ≤ X := Nat.le_self_pow (by decide) m
  have hm2X : m^2 ≤ X := Nat.pow_le_pow_right (by omega) (by decide)
  have htotal : 2*total ≤ m := by dsimp [m,radius]; omega
  have hpay : payload.bits.length ≤ X := (show payload.bits.length ≤ m by dsimp [m,radius]; omega).trans hmX
  have ht : total ≤ X := (show total ≤ m by omega).trans hmX
  have hmass : RecoveryPrefixMeasure.mass payload total ≤ X :=
    (show RecoveryPrefixMeasure.mass payload total ≤ m by dsimp [RecoveryPrefixMeasure.mass,m,radius]; omega).trans hmX
  have hloop := Nat.mul_le_mul_left (10*C*m^2) htotal
  have hloop' : 20*total*C*m^2 ≤ 10*C*X := by dsimp [X]; nlinarith
  have h2 := Nat.mul_le_mul_left (6*C) hm2X
  have h1 := Nat.mul_le_mul_left (10*C) hmX
  have h0 := Nat.mul_le_mul_left (8*C) hX
  rw [budget_expansion]
  change 20*total*C*m^2+6*C*m^2+10*C*m+8*C+2*RecoveryPrefixMeasure.mass payload total+
    12*payload.bits.length+31*total+132  ≤  (40*C+200)*X
  calc
    _  ≤  (34*C+177)*X := by nlinarith
    _  ≤  (40*C+200)*X := Nat.mul_le_mul_right X (by omega)

theorem fixed_budget_bound (payload total : Nat) :
    budget 1073741824 payload total ≤ 68719476736*(radius payload total)^3 :=
  (budget_bound 1073741824 payload total).trans (Nat.mul_le_mul_right _ (by decide))

theorem polynomial_runs (payload total : Nat) (flat : Bool) :
    OrdinaryOracleRuns RecoveryOracle.correctedSat (program 1073741824 flat)
      (RecoveryPrefixMeasure.request payload total) (RecoveryPrefixBody.search flat payload total [])
      (68719476736*(radius payload total)^3) := by
  obtain ⟨cost,final,hcost,htrace,hhalt,hout⟩ := runs 1073741824 payload total flat (Nat.le_refl _)
  exact ⟨cost,final,hcost.trans (fixed_budget_bound payload total),htrace,hhalt,hout⟩

end NearCubicWires.RepairSource.RecoveryPrefixCold
