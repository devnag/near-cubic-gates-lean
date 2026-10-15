import Proof.Hierarchy.HierarchyProjectionBounds

/-! The paper's length schedule uses the actual normalized native width.
Doubling the original input changes that width by a fixed additive amount;
the dyadic rounding and the fixed hierarchy slice are both retained. -/
namespace NearCubicWires.RepairSource.CloseoutNativeWidth
open RepairOrdinary ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem length_four {k : Nat} (H : OrdinaryHierarchy (fun n=>n^(k+2)))
    (Cpad n : Nat) : HierarchyEncode.length H Cpad (2*n) ≤ 4*HierarchyEncode.length H Cpad n := by
  let A:=HierarchyBinary.allocation Cpad (VerifierEncoding.code H.verifier).length H.coefficient n
  let B:=HierarchyBinary.allocation Cpad (VerifierEncoding.code H.verifier).length H.coefficient (2*n)
  have hA : B ≤ 2*A := by dsimp [A,B,HierarchyBinary.allocation]; nlinarith
  have hbase : 2^(k+1) ≤ PowerSlice.length k A := by
    unfold PowerSlice.length
    exact (Nat.le_mul_of_pos_right (2^(k+1)) (Nat.succ_pos (A/2^(k+1)))).trans (Nat.le_add_right _ _)
  have hlo:=(PowerSlice.length_bounds k A).1
  have hhi:=(PowerSlice.length_bounds k B).2
  have hp : 2^(k+2)=2*2^(k+1) := by rw [show k+2=(k+1)+1 by omega,pow_succ]; ring
  change PowerSlice.length k B ≤ 4*PowerSlice.length k A
  rw [hp] at hhi
  omega

theorem ell_four {x y : Nat} (h : y ≤ 4*x) : PCPResourceLedger.ell y ≤ PCPResourceLedger.ell x+2 := by
  apply Nat.clog_le_of_le_pow
  calc
    y+1 ≤ 4*(x+1) := by omega
    _ ≤ 4*2^PCPResourceLedger.ell x := Nat.mul_le_mul_left 4 (Nat.le_pow_clog (by decide) _)
    _ = _ := by rw [pow_add]; ring

def clockJump (k : Nat) := 2*(k+2)+10

theorem time_step_of_degree (k L L' : Nat) (hl : L' ≤ 4*L) (hL : 1 ≤ L)
    (hd : PowerSlice.degree L=k+2) (hd' : PowerSlice.degree L'=k+2) :
    UAggregateClock.time L' ≤ 2^clockJump k*UAggregateClock.time L := by
  have he:=ell_four hl
  have hpos : 1 ≤ PCPResourceLedger.ell L := Nat.clog_pos (by decide) (by omega)
  have hh:=ell_four (by omega : PCPResourceLedger.ell L' ≤ 4*PCPResourceLedger.ell L)
  have hexp : ClockEnvelope.exponent UAggregateClock.offset UAggregateClock.exponent L' ≤
      ClockEnvelope.exponent UAggregateClock.offset UAggregateClock.exponent L+clockJump k := by
    dsimp only [ClockEnvelope.exponent,ClockDyadicLedger.exponent,ClockEnvelope.logWidth]
    rw [hd,hd']
    change (k+2)*PCPResourceLedger.ell L'+5*PCPResourceLedger.ell (PCPResourceLedger.ell L')+23 ≤
      (k+2)*PCPResourceLedger.ell L+5*PCPResourceLedger.ell (PCPResourceLedger.ell L)+23+clockJump k
    have hm:=Nat.mul_le_mul_left (k+2) he
    dsimp only [clockJump]
    nlinarith
  calc
    _ ≤ 2^(ClockEnvelope.exponent UAggregateClock.offset UAggregateClock.exponent L+clockJump k) :=
      Nat.pow_le_pow_right (by decide : 0 < 2) hexp
    _ = _ := by rw [pow_add,Nat.mul_comm]; rfl

theorem time_step {k : Nat} (H : OrdinaryHierarchy (fun n=>n^(k+2)))
    (Cpad n : Nat) :
    UAggregateClock.time (HierarchyEncode.length H Cpad (2*n)) ≤
      2^clockJump k*UAggregateClock.time (HierarchyEncode.length H Cpad n) :=
  time_step_of_degree k _ _ (length_four H Cpad n)
    (by
      have hp:=(PowerSlice.length_bounds k
        (HierarchyBinary.allocation Cpad (VerifierEncoding.code H.verifier).length H.coefficient n)).1
      change 1 ≤ PowerSlice.length k _
      omega)
    (PowerSlice.length_degree _ _) (PowerSlice.length_degree _ _)

end NearCubicWires.RepairSource.CloseoutNativeWidth
