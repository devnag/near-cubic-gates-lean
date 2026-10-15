import Proof.MachineModel.OrdinaryAmplifierReplayDock

/-! A fixed quadratic envelope for the complete selected amplifier replay.
The table length follows from the actual schema, not a supplied clock tape. -/
namespace NearCubicWires.RepairOrdinary.AmplifierReplay
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem payload_bound (n : ℕ) (table : List Bool) (hlen : table.length=2^n) :
    Payload.budget n table ≤ 512*((frame n.bits++table).length+1)^2 := by
  let L := (frame n.bits++table).length
  have hL : 2*n.bits.length+1+2^n=L := by simp [L,hlen]
  have hpow : n+1 ≤ 2^n := Nat.succ_le_of_lt Nat.lt_two_pow_self
  have ht : 2^n ≤ L := by omega
  have hn : n ≤ L := by omega
  have hw : n.bits.length ≤ n := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr Nat.lt_two_pow_self
  have hnw : n*n.bits.length ≤ L*L := Nat.mul_le_mul hn (hw.trans hn)
  have htn : 2^n*n ≤ L*L := Nat.mul_le_mul ht hn
  change Payload.budget n table ≤ 512*(L+1)^2
  simp only [Payload.budget,Prepare.budget,Prepare.prefixBudget,Prepare.arityBudget,
    GeneratedAmplifier.Arity.budget,MatrixScorePower.budget,MatrixUnaryTemplate.budget]
  change 2*(4*n.bits.length+4+1+(n*(8*n.bits.length+10)+8*n.bits.length+n+17))+2+1+
    (4*n+12)+1+(8*n+40+(2^n*(8*(n+3)+10)+8*(n+3)+2^n+17))+1+(2*L+1) ≤ _
  nlinarith

theorem budget_bound (b inputLength n : ℕ) (table : List Bool) (hlen : table.length=2^n) :
    Dock.budget b n table ≤
      1024*(b+inputLength+(frame n.bits++table).length+1)^2 := by
  let L := (frame n.bits++table).length
  let S := b+inputLength+L+1
  have hS : 1 ≤ S := by unfold S; omega
  have hl : (L+1)^2 ≤ S^2 := Nat.pow_le_pow_left (by unfold S; omega) 2
  have hb : b ≤ S^2 := by
    have hbs : b ≤ S := by unfold S; omega
    have hss : S ≤ S^2 := by nlinarith
    omega
  have hp : 1 ≤ S^2 := Nat.one_le_pow _ _ hS
  have hbody := payload_bound n table hlen
  change Payload.budget n table ≤ 512*(L+1)^2 at hbody
  change 2*b+2+1+Payload.budget n table ≤ 1024*S^2
  nlinarith

end NearCubicWires.RepairOrdinary.AmplifierReplay
