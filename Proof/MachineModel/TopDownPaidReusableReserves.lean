import Proof.MachineModel.TopDownPaidReusableCost

/-! Shared row reserves are linear in the already paid driver, with constants
depending only on the fixed Williams program. This supplies capacity bounds;
it does not manufacture the physical unary templates or the source stream. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1TopDownPaidReusableReserves
open LocalBitMultitape RepairOrdinary RepairRepresentation ExtDecompositionBatch
open CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount
open MatrixScoreBatch CompetitorCountMask RecoveryRootRound P1Closure
open P1TopDownPaidReusable

noncomputable def coefficient (a : WilliamsAlgorithm) : Nat :=
  10*DriverLayout.e a+10*DriverLayout.sweepCount a+1300
def buffer (D : Nat) := D+1
noncomputable def rewind (a : WilliamsAlgorithm) (D : Nat) :=
  (coefficient a+2)*(D+1)
noncomputable def workspace (a : WilliamsAlgorithm) (D : Nat) :=
  (2*coefficient a+20)*(D+1)

theorem core_fuel_le (a : WilliamsAlgorithm) (row : EquationRow.Input) (C Q : Nat)
    (hC : (Header.stream row).length≤C) (hQ : Q≤(EquationRow.request row).p) :
    P1TopDownPaidReloadCore.fuel a row C Q ≤
      coefficient a*(Driver.value a row.d row.p row.cuts.length C+1) := by
  have hprepare := Driver.fuel_bound a row C Q hC hQ
  have hw := P1TopDownPaidPayload.warm_budget_le a row C Q hC hQ
  have hd := DriverLayout.budget_linear a row.d row.p row.cuts.length C
  have hb := Driver.append_bound a row C Q hQ
  unfold Whole.budget Cold.budget Framed.budget at hprepare
  unfold ScannedClean.budget ScannedClean.cleanBudget at hw
  unfold P1TopDownPaidReloadCore.fuel P1TopDownPaidRetiredPayload.fuel coefficient
  nlinarith only [hprepare,hw,hd,hb]

/-- All five post-header storage inequalities hold for one common driver cap. -/
theorem capacities (a : WilliamsAlgorithm) (row : EquationRow.Input) (C Q D : Nat)
    (hC : (Header.stream row).length≤C) (hQ : Q≤(EquationRow.request row).p)
    (hD : Driver.value a row.d row.p row.cuts.length C≤D) :
    P1TopDownPaidReloadCore.fuel a row C Q≤rewind a D ∧
    RowPayload.budget (scalarWidth (EquationRow.request row) Q)≤buffer D ∧
    buffer D+1≤rewind a D ∧
    P1TopDownPaidReloadCore.budget a row C Q (buffer D)+1≤workspace a D ∧
    buffer D≤workspace a D := by
  have hf : P1TopDownPaidReloadCore.fuel a row C Q≤coefficient a*(D+1) :=
    (core_fuel_le a row C Q hC hQ).trans
      (Nat.mul_le_mul_left _ (Nat.add_le_add_right hD 1))
  have hb : RowPayload.budget (scalarWidth (EquationRow.request row) Q)≤buffer D := by
    have h:=Driver.append_bound a row C Q hQ
    change 20*scalarWidth (EquationRow.request row) Q+27≤D+1
    omega
  have hs:=RawRowJoin.budget_le (P1TopDownPaidReloadCore.fuel a row C Q)
    (scalarWidth (EquationRow.request row) Q) (buffer D) hb
  change P1TopDownPaidReloadCore.budget a row C Q (buffer D)≤_ at hs
  dsimp only [rewind,workspace,buffer] at *
  constructor
  · nlinarith only [hf]
  constructor
  · exact hb
  constructor
  · nlinarith only [Nat.zero_le (coefficient a)]
  constructor
  · nlinarith only [hf,hs]
  · nlinarith only [Nat.zero_le (coefficient a)]

theorem valid (a : WilliamsAlgorithm) (d : Datum) (D : Nat)
    (hC : (Header.stream d.row).length≤d.C)
    (hQ : d.Q≤(EquationRow.request d.row).p)
    (hf : ∀ i j,d.f i j<2^d.Q)
    (hc : ∀ i : Fin ((EquationRow.request d.row).U*(EquationRow.request d.row).U),
      Int.ModEq ((2 : Int)^d.Q)
        (SupplierPrinter.weightedDominance (leftScore (EquationRow.request d.row))
          (rightScore (EquationRow.request d.row)) (weight (EquationRow.request d.row))
          i.divNat i.modNat) (d.f i.divNat i.modNat))
    (hD : Driver.value a d.row.d d.row.p d.row.cuts.length d.C≤D) :
    Valid a (buffer D) (rewind a D) (workspace a D) d := by
  obtain ⟨hR,hB,hBR,hS,hBS⟩:=capacities a d.row d.C d.Q D hC hQ hD
  exact ⟨hC,hQ,hf,hc,hR,hB,hBR,hS,hBS⟩

end NearCubicWires.P1TopDownPaidReusableReserves
