import Proof.MachineModel.ClosureCompactBounds
import Proof.CaseAnalysis.FinalSupplierFuel
import Proof.MachineModel.SourceEnvelope
import Proof.CaseAnalysis.RowsEstimatorDriverBounds

/-! Risk gate for the compact row. The actual table driver has one residual
factor; its other exponent is source-fixed once the original-cache envelope
is fixed. Preparation and reset capacities remain additive in Driver.value. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.CompactCost
open RepairRepresentation RepairOrdinary SupplierPipeline SupplierEstimator
open RepairSource CloseoutFinal C10SupplierFuel CloseoutRowsEstimator
open CompactBounds

theorem radix_from_source {q : Nat} (a : DecompositionAlgorithm)
    (live : Finset (Fin q)) (occ : List (SupportedNormalizedGate q))
    (top : List Bool) (P : Nat) (hq : q ≤ P)
    (hs : (ExtDecompositionBatch.segment (CloseoutRowsUniversal.pool live occ) top).length
      ≤ 1000*(P+2)^2) :
    radix a live occ ≤ ExtDecompositionBatch.SourceEnvelope.capacity a P+1 := by
  have h := ExtDecompositionBatch.SourceEnvelope.actual_capacity a
    (CloseoutRowsUniversal.pool live occ) top P hq hs
  exact Nat.add_le_add_right h.2.2.2.2.1 1

noncomputable def tableCoefficient (printer : WilliamsAlgorithm) (c : Nat) :=
  2*Driver.tableCoefficient printer*(c+3)^CompetitorCrossScheduler.exponent printer

theorem table_polynomial (printer : WilliamsAlgorithm) (q K s b degree c e : Nat)
    (harity : s+K=q) (hb : b ≤ c*(q+1)^e) (hd : degree ≤ q+1) :
    Driver.tableValue printer ((s+1)/2) (b*(degree*(K+1))+(K+1)) ≤
      tableCoefficient printer c *
        (2^(q-K)*(q+1)^((e+2)*CompetitorCrossScheduler.exponent printer)) := by
  have hK : K+1 ≤ q+1 := by omega
  have hbase : q+1 ≤ (q+1)^(e+2) := Nat.le_self_pow (by omega) _
  have hp : b*(degree*(K+1))+(K+1) ≤ (c+1)*(q+1)^(e+2) := by
    calc
      _ ≤ (c*(q+1)^e)*((q+1)*(q+1))+(q+1) := by gcongr
      _ = c*(q+1)^(e+2)+(q+1) := by rw [pow_add,pow_two]; ring
      _ ≤ (c+1)*(q+1)^(e+2) := by nlinarith
  have hscale : (s+1)/2+(b*(degree*(K+1))+(K+1))+1 ≤
      (c+3)*(q+1)^(e+2) := by
    have hdhalf : (s+1)/2 ≤ q+1 := by omega
    nlinarith
  have htwo : (2^((s+1)/2))^2 ≤ 2*2^s := by
    calc
      _ = 2^(2*((s+1)/2)) := by rw [←pow_mul]; congr 1; omega
      _ ≤ 2^(s+1) := Nat.pow_le_pow_right (by decide) (by omega)
      _ = 2*2^s := by rw [pow_succ]; omega
  have hs : s=q-K := by omega
  unfold Driver.tableValue tableCoefficient
  calc
    _ ≤ Driver.tableCoefficient printer * (2*2^s) *
        ((c+3)*(q+1)^(e+2))^(CompetitorCrossScheduler.exponent printer) := by gcongr
    _ = _ := by rw [hs,mul_pow,←pow_mul]; ring

theorem table_saving (printer : WilliamsAlgorithm) (q L kappa sigma s b degree c e : Nat)
    (harity : s+kappa*L=q) (hb : b ≤ c*(q+1)^e) (hd : degree ≤ q+1)
    (hlog : q+1 ≤ 2^L)
    (hslack : sigma+(e+2)*CompetitorCrossScheduler.exponent printer+2 ≤ kappa)
    (hcoef : tableCoefficient printer c ≤ 2^(2*L)) :
    Driver.tableValue printer ((s+1)/2) (b*(degree*(kappa*L+1))+(kappa*L+1)) ≤
      2^(q-sigma*L) :=
  (table_polynomial printer q (kappa*L) s b degree c e harity hb hd).trans
    (hot_absorb hlog (by omega) hslack hcoef)

end NearCubicWires.P1Closure.CompactCost
