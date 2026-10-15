import Proof.SourceAssembly.SourceBundle
import Proof.MachineModel.P1ClosureCompactCost

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace SourceAssemblyTableFactor
open NearCubicWires LocalBitMultitape RepairOrdinary RepairRepresentation
open SourceInterfaces P1Closure CloseoutRowsEstimator
open RepairSource RepairSource.CloseoutFinal
open FixedLivePackets PacketProduction
open NativeRecipes
noncomputable section

def nativeScale (printer : WilliamsAlgorithm) : Nat :=
  (3*P1TopDownPaidPayload.tapes printer+6)*
    (2*P1TopDownPaidReusableReserves.coefficient printer+20)

def nativeAdditive (printer : WilliamsAlgorithm) (d p G C b v N : Nat) : Nat :=
  N*(nativeScale printer*(64*(C+1)+2000000*(d+p+G+1)^3+1)+
    (3*P1TopDownPaidPayload.tapes printer+6)+3)+4+
    P1TopDownPaidFamilySum.budget b v N

/-- Exact native consumer formula: neither C nor G multiplies the table. -/
theorem native_split (printer : WilliamsAlgorithm) (d p G C b v N : Nat) :
    f_budget printer
      (P1TopDownPaidReusableReserves.workspace printer (Driver.value printer d p G C)) b v N =
    nativeAdditive printer d p G C b v N+
      N*nativeScale printer*Driver.tableValue printer d p := by
  unfold f_budget C10ExternalRowLoop.familyFuel P1TopDownPaidReusableReserves.workspace
    Driver.value nativeAdditive nativeScale
  ring

/-- Instantiates the driver bound at the actual packet geometry and effective
binary degree. It quantifies the exponent before the live-scale L. -/
theorem actual_native_table (printer : WilliamsAlgorithm) (c e : Nat)
    {q L : Nat} (a : DecompositionAlgorithm) (F : Packets.Family q L)
    (g : Packets.Geometry F) (layout : Packets.Layout a F g)
    (hc : CompactBounds.radix a (Packets.live F) F.occurrences ≤ c*(q+1)^e)
    (hd : layout.degree ≤ q+1) :
    Driver.tableValue printer ((Packets.residual F+1)/2)
      (CompactBounds.radix a (Packets.live F) F.occurrences*
        (min layout.degree (Packets.pool a F g).length*((Packets.live F).card+1))+
          ((Packets.live F).card+1)) ≤
    CompactCost.tableCoefficient printer c*
      (2^(Packets.residual F)*(q+1)^((e+2)*CompetitorCrossScheduler.exponent printer)) := by
  have harity : Packets.residual F+(Packets.live F).card=q := by
    rw [g.card]
    exact Nat.sub_add_cancel (SupplierEstimator.normalizedLiveCount_le q L)
  have hdegree : min layout.degree (Packets.pool a F g).length ≤ q+1 :=
    (Nat.min_le_left _ _).trans hd
  have h := CompactCost.table_polynomial printer q (Packets.live F).card
    (Packets.residual F) (CompactBounds.radix a (Packets.live F) F.occurrences)
    (min layout.degree (Packets.pool a F g).length) c e harity hc hdegree
  have he : q-(Packets.live F).card=Packets.residual F := by omega
  simpa only [he] using h

def rowAdditive (a : DecompositionAlgorithm) (c d : Nat) (r : Request)
    (C : Nat) (caps : RowCaps) (N : Nat) : Nat :=
  N*(c*((r.smallSize a)^d+caps.headerFuel+C+caps.copyCap+1)+3)+3

/-- The actual row-production family has the same one-table split. -/
theorem rows_split (a : DecompositionAlgorithm) (c d : Nat) (r : Request)
    (C : Nat) (caps : RowCaps) (N : Nat) :
    C10ExternalRowLoop.familyFuel N (rowBudget a c d r C caps) =
    rowAdditive a c d r C caps N+
      N*c*(2^(Packets.residual (r.family a))*(r.q+(r.input a).length+1)^d) := by
  unfold C10ExternalRowLoop.familyFuel rowBudget rowAdditive
  ring

/-- The exponent of the complete table coefficient, fixed before L, the cap
index and hierarchy. The two row initializations are covered by N+1. -/
def tableDegree (printer : WilliamsAlgorithm) (cacheDegree inputDegree rowDegree
    externalDegree monomialDegree clauseDegree : Nat) : Nat :=
  externalDegree+monomialDegree+clauseDegree+
    max ((cacheDegree+2)*CompetitorCrossScheduler.exponent printer)
      ((inputDegree+1)*rowDegree)

theorem coefficient_bound (printer : WilliamsAlgorithm)
    (q cacheC cacheE inputC inputE rowC rowD rowCount rowCountC rowCountE
      calls callsC callsE clauses clausesC clausesE inputLength : Nat)
    (hi : inputLength ≤ inputC*(q+1)^inputE)
    (hr : rowCount+1 ≤ rowCountC*(q+1)^rowCountE)
    (hm : calls ≤ callsC*(q+1)^callsE)
    (hp : clauses ≤ clausesC*(q+1)^clausesE) :
    clauses*calls*(rowCount+1)*
      (nativeScale printer*CompactCost.tableCoefficient printer cacheC*
          (q+1)^((cacheE+2)*CompetitorCrossScheduler.exponent printer)+
        rowC*(q+inputLength+1)^rowD) ≤
    clausesC*callsC*rowCountC*
      (nativeScale printer*CompactCost.tableCoefficient printer cacheC+
        rowC*(inputC+2)^rowD)*
      (q+1)^tableDegree printer cacheE inputE rowD rowCountE callsE clausesE := by
  let E := max ((cacheE+2)*CompetitorCrossScheduler.exponent printer) ((inputE+1)*rowD)
  have hbase : q+1 ≤ (q+1)^(inputE+1) := Nat.le_self_pow (by omega) _
  have hin : q+inputLength+1 ≤ (inputC+2)*(q+1)^(inputE+1) := by
    have hpow : (q+1)^inputE ≤ (q+1)^(inputE+1) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    nlinarith [Nat.mul_le_mul_left inputC hpow]
  have hnative : (q+1)^((cacheE+2)*CompetitorCrossScheduler.exponent printer) ≤ (q+1)^E :=
    Nat.pow_le_pow_right (by omega) (Nat.le_max_left _ _)
  have hrow : (q+inputLength+1)^rowD ≤ (inputC+2)^rowD*(q+1)^E := by
    calc
      _ ≤ ((inputC+2)*(q+1)^(inputE+1))^rowD := Nat.pow_le_pow_left hin _
      _ = (inputC+2)^rowD*(q+1)^((inputE+1)*rowD) := by rw [mul_pow,←pow_mul]
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (Nat.le_max_right _ _))
  have hsum : nativeScale printer*CompactCost.tableCoefficient printer cacheC*
      (q+1)^((cacheE+2)*CompetitorCrossScheduler.exponent printer)+rowC*(q+inputLength+1)^rowD ≤
      (nativeScale printer*CompactCost.tableCoefficient printer cacheC+rowC*(inputC+2)^rowD)*(q+1)^E := by
    nlinarith only [Nat.mul_le_mul_left (nativeScale printer*CompactCost.tableCoefficient printer cacheC) hnative,
      Nat.mul_le_mul_left rowC hrow]
  have hh := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hp hm) hr) hsum
  unfold tableDegree
  change _ ≤ _*(q+1)^(rowCountE+callsE+clausesE+E)
  calc
    _ ≤ _ := hh
    _ = _ := by simp only [pow_add]; ring

end
end SourceAssemblyTableFactor
