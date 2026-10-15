import Proof.MachineModel.TopDownPaidReloadCore
import Proof.MachineModel.TopDownPaidReusableBody
import Proof.MachineModel.ClosureBinaryRequest
import Proof.CaseAnalysis.FinalRowFrameJoin

/-! The complete source-stream → scanner → actual paid count → retirement →
raw append → reusable false bank transaction. Only the original framed row
source and shared physical capacity templates remain upstream duties. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1TopDownPaidReusable
open LocalBitMultitape RepairOrdinary RepairRepresentation ExtDecompositionBatch
open CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount
open MatrixScoreBatch CompetitorCountMask RecoveryRootRound P1Closure
open CompetitorCrossScheduler (producer)
open P1TopDownPaidPayload (estimate port tapes)
attribute [local irreducible] CompetitorCrossScheduler.producer Paid.warmMachine
  Paid.driver Paid.warm Paid.retire Paid.retiredMachine RawRowJoin.machine
  P1TopDownPaidReloadCore.rawMachine P1TopDownPaidReusableBody.machine

private theorem append_bound {m n : Nat} (A : Fin m→List Bool) (B : Fin n→List Bool) (D : Nat)
    (ha : ∀ i,(A i).length≤D) (hb : ∀ i,(B i).length≤D) :
    ∀ i,(Fin.addCases (motive:=fun _=>List Bool) A B i).length≤D := by
  intro i
  refine Fin.addCases (m:=m) (n:=n) (fun j=>?_) (fun j=>?_) i
  · simpa only [Fin.addCases_left] using ha j
  · simpa only [Fin.addCases_right] using hb j

private theorem bank_bound (a : WilliamsAlgorithm) (A : Fin 64→List Bool) (C D : Nat)
    (fields : Fin 7→List Bool) (ha : ∀ i,(A i).length≤D) (hc : C≤D)
    (hf : ∀ i,(fields i).length≤D) :
    ∀ i,(P1TopDownPaidReloadCore.bank a A C fields i).length≤D := by
  unfold P1TopDownPaidReloadCore.bank WarmPrepare.data WarmPrepare.bank
  apply append_bound
  · apply append_bound
    · apply append_bound
      · apply append_bound
        · apply append_bound
          · apply append_bound (m:=64) (n:=6)
            · exact ha
            · intro i;fin_cases i <;> simp [Scanned.extra] <;> omega
          · intro i;simp
        · intro i;simp
      · intro i;fin_cases i <;> simp
    · exact hf
  · intro i;simp

theorem input_bound (a : WilliamsAlgorithm) (row : EquationRow.Input) (C Q : Nat)
    (select : Fin (EquationRow.request row).U→Fin (EquationRow.request row).U→Bool)
    (hC : (Header.stream row).length≤C) (hQ : Q≤(EquationRow.request row).p) :
    ∀ i,(P1TopDownPaidReloadCore.input a row C Q select i).length≤
      Driver.value a row.d row.p row.cuts.length C := by
  let D:=Driver.value a row.d row.p row.cuts.length C
  have hc : C≤D := by unfold D Driver.value;omega
  have hpow : row.d+row.p+row.cuts.length+1≤(row.d+row.p+row.cuts.length+1)^3 :=
    Nat.le_self_pow (by decide) _
  have hd : row.d≤D := by unfold D Driver.value;omega
  have hp : row.p≤D := by unfold D Driver.value;omega
  have h1 : 1≤D := by unfold D Driver.value;omega
  refine bank_bound a _ C D _ ?_ hc ?_
  · intro i
    unfold Prepare.input
    split_ifs
    · simpa using hd
    · simpa using hp
    · exact hC.trans hc
    · simpa using h1
    · simp
  · intro i
    rw [←WarmFields.projected (producer a) row C Q estimate 1 select i]
    exact InputSupport.warm a row C Q estimate 1 select hC hQ _

noncomputable def machine (a : WilliamsAlgorithm) :=
  P1TopDownPaidReusableBody.machine (P1TopDownPaidReloadCore.rawMachine a)
noncomputable def word (a : WilliamsAlgorithm) (row : EquationRow.Input) (C Q : Nat)
    (select : Fin (EquationRow.request row).U→Fin (EquationRow.request row).U→Bool) :=
  P1TopDownPaidReusableBody.word (P1TopDownPaidReloadCore.input a row C Q select)
noncomputable def budget (a : WilliamsAlgorithm) (row : EquationRow.Input) (C Q B S : Nat)
    (select : Fin (EquationRow.request row).U→Fin (EquationRow.request row).U→Bool) :=
  P1TopDownPaidReusableBody.budget (P1TopDownPaidReloadCore.input a row C Q select)
    (P1TopDownPaidReloadCore.budget a row C Q B) S
noncomputable def heads (a : WilliamsAlgorithm) := P1TopDownPaidReusableBody.heads (tapes a)
noncomputable def bank (a : WilliamsAlgorithm) (source : List Bool) (S R B : Nat) (out : List Bool) :=
  P1TopDownPaidReusableBody.bank (fun _ : Fin (tapes a)=>List.replicate S false) source S R B out

set_option maxHeartbeats 1000000 in
theorem run (a : WilliamsAlgorithm) (row : EquationRow.Input) (C Q B R S : Nat)
    (f : Fin (EquationRow.request row).U→Fin (EquationRow.request row).U→Nat)
    (select : Fin (EquationRow.request row).U→Fin (EquationRow.request row).U→Bool)
    (pre tail out : List Bool)
    (hC : (Header.stream row).length≤C) (hQ : Q≤(EquationRow.request row).p)
    (hf : ∀ i j,f i j<2^Q)
    (hc : ∀ i : Fin ((EquationRow.request row).U*(EquationRow.request row).U),
      Int.ModEq ((2 : Int)^Q)
        (SupplierPrinter.weightedDominance (leftScore (EquationRow.request row))
          (rightScore (EquationRow.request row)) (weight (EquationRow.request row)) i.divNat i.modNat)
        (f i.divNat i.modNat))
    (hR : P1TopDownPaidReloadCore.fuel a row C Q≤R)
    (hB : RowPayload.budget (scalarWidth (EquationRow.request row) Q)≤B)
    (hBR : B+1≤R) (hS : P1TopDownPaidReloadCore.budget a row C Q B+1≤S) (hBS : B≤S) :
    let b := scalarWidth (EquationRow.request row) Q
    let count := (selected (CompetitorSelectedCells.cells row.odd f select)).sum
    Step (machine a) (budget a row C Q B S select) (heads a pre.length out)
      (bank a (pre++word a row C Q select++tail) S R B out)
      (heads a (pre.length+(word a row C Q select).length) (out++SignedSortKey.binary b count))
      (bank a (pre++word a row C Q select++tail) S R B (out++SignedSortKey.binary b count)) := by
  dsimp only
  obtain ⟨Z,h⟩:=P1TopDownPaidReloadCore.run a row C Q B R f select out hC hQ hf hc hR hB hBR
  have hDS : Driver.value a row.d row.p row.cuts.length C≤S := by
    unfold P1TopDownPaidReloadCore.budget RawRowJoin.budget P1TopDownPaidReloadCore.fuel
      P1TopDownPaidRetiredPayload.fuel at hS
    omega
  exact P1TopDownPaidReusableBody.run (P1TopDownPaidReloadCore.rawMachine a) (port a)
    (P1TopDownPaidReloadCore.input a row C Q select) _ pre tail out _
    (P1TopDownPaidReloadCore.budget a row C Q B) S R B
    (fun i=>(input_bound a row C Q select hC hQ i).trans hDS) hS hBS h

end NearCubicWires.P1TopDownPaidReusable
