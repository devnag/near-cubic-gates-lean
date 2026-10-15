import Proof.PCP.PCPPNativeProjectionRead

namespace NearCubicWires.RepairOrdinary.PCPPNativeProjectionRead
open RadixSemantics RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem budget_eq (bits : List Bool) :
    budget bits=2048*(bits.length+1)^2+
      24*((Nat.unpair (value bits)).1+1)*(2*bits.length+4)+
      24*((Nat.unpair (value bits)).2+1)*(2*bits.length+4)+2 := by
  obtain ⟨hl,hr⟩ := RecoveryUnpair.word_lengths bits
  obtain ⟨vl,vr⟩ := RecoveryUnpair.word_values bits
  unfold budget RecoveryUnpair.budget Unary.budget
  rw [hl,hr,vl,vr]
  ring

theorem budget_bound (bits : List Bool) (a b : ℕ)
    (h : Nat.unpair (value bits)=(a,b)) :
    budget bits≤4096*(a+b+bits.length+1)^2 := by
  rw [budget_eq,h]
  dsimp only
  have hp : (bits.length+1)^2≤(a+b+bits.length+1)^2 :=
    Nat.pow_le_pow_left (by omega) 2
  have hleft : (a+1)*(2*bits.length+4)≤4*(a+b+bits.length+1)^2 := by
    calc
      _ ≤ (a+b+bits.length+1)*(4*(a+b+bits.length+1)) := Nat.mul_le_mul (by omega) (by omega)
      _ = _ := by ring
  have hright : (b+1)*(2*bits.length+4)≤4*(a+b+bits.length+1)^2 := by
    calc
      _ ≤ (a+b+bits.length+1)*(4*(a+b+bits.length+1)) := Nat.mul_le_mul (by omega) (by omega)
      _ = _ := by ring
  have hone : 1≤(a+b+bits.length+1)^2 := Nat.one_le_pow _ _ (by omega)
  nlinarith

end NearCubicWires.RepairOrdinary.PCPPNativeProjectionRead
