import Proof.MachineModel.ClosureRawRowState
import Proof.CaseAnalysis.RowsEstimatorPaidOwnedRun
import Proof.CaseAnalysis.RowsEstimatorDriverRuntime

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1TopDownPaidPayload
open LocalBitMultitape RepairOrdinary RepairRepresentation ExtDecompositionBatch
open CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount
open MatrixScoreBatch CompetitorCountMask
open CompetitorCrossScheduler (producer)
open P1Closure RecoveryRootRound
attribute [local irreducible] CompetitorCrossScheduler.producer Paid.warmMachine Paid.driver Paid.warm
  RawRowJoin.machine

def estimate : CompetitorValidity.Estimate := ⟨0,0,1⟩
noncomputable def tapes (a : WilliamsAlgorithm) := Paid.tapes a (producer a)
noncomputable def port (a : WilliamsAlgorithm) : Fin (tapes a) :=
  Paid.old a (producer a) (WarmPrepare.spare (producer a))
noncomputable def machine (a : WilliamsAlgorithm) := RawRowJoin.machine (Paid.warmMachine a) (port a)
noncomputable def input (a : WilliamsAlgorithm) (row : EquationRow.Input) (C Q : Nat)
    (select : Fin (EquationRow.request row).U→Fin (EquationRow.request row).U→Bool) :=
  Paid.input a (producer a) row C (WarmFields.words row Q estimate 1 select) []
noncomputable def budget (a : WilliamsAlgorithm) (row : EquationRow.Input) (C Q B : Nat) :=
  RawRowJoin.budget (Paid.warmBudget a row C Q) (scalarWidth (EquationRow.request row) Q) B

theorem empty_heads (a : WilliamsAlgorithm) :
    Paid.heads a (producer a) [] = (fun _=>0) := by
  funext i
  refine Fin.addCases (m:=WarmPrepare.tapes (producer a))
    (n:=ScannedClean.tapes a) (fun j=>?_) (fun j=>?_) i
  · simp [Paid.heads,WarmPrepare.heads]
  · simp only [Paid.heads,Fin.addCases_right]

private theorem step_of_startWith {t sp sq n : Nat}
    (first : Machine t sp) (last : Machine t sq) (hin hout : Fin t→Nat)
    (tin tout : Fin t→List Bool) (r : ExecutionReceipt t (sp+sq))
    (hr : runFrom (Composition.machine first last) n
      (WarmPrepared.startWith first last hin tin)=some r)
    (hh : r.final.heads=hout) (ht : r.final.tapes=tout) :
    Step (Composition.machine first last) n hin tin hout tout := by
  rw [Paid.prepare_config] at hr
  exact Step.of_run hr hh ht

set_option maxHeartbeats 1000000 in
/-- The real paid row, followed by existing rewind/extract/erase machinery.
The output is the selected count itself, even with neutral estimate fields. -/
theorem run (a : WilliamsAlgorithm) (row : EquationRow.Input) (C Q B R : Nat)
    (f : Fin (EquationRow.request row).U→Fin (EquationRow.request row).U→Nat)
    (select : Fin (EquationRow.request row).U→Fin (EquationRow.request row).U→Bool)
    (out : List Bool)
    (hC : (Header.stream row).length≤C) (hQ : Q≤(EquationRow.request row).p)
    (hf : ∀ i j,f i j<2^Q)
    (hc : ∀ i : Fin ((EquationRow.request row).U*(EquationRow.request row).U),
      Int.ModEq ((2 : Int)^Q)
        (SupplierPrinter.weightedDominance (leftScore (EquationRow.request row))
          (rightScore (EquationRow.request row)) (weight (EquationRow.request row)) i.divNat i.modNat)
        (f i.divNat i.modNat))
    (hR : Paid.warmBudget a row C Q≤R)
    (hB : RowPayload.budget (scalarWidth (EquationRow.request row) Q)≤B)
    (hBR : B+1≤R) :
    let p := producer a
    let b := scalarWidth (EquationRow.request row) Q
    let count := (selected (CompetitorSelectedCells.cells row.odd f select)).sum
    let word := Stream.recordWord b estimate count 1
    ∃ (A : Fin (WarmPrepare.tapes p)→List Bool)
      (extra : Fin (ScannedClean.tapes a)→List Bool),
      Step (machine a) (budget a row C Q B)
        (RawRowJoin.heads (tapes a) out)
        (RawRowJoin.bank (RawRowJoin.padded (port a) B (input a row C Q select)) R B out)
        (RawRowJoin.heads (tapes a) (out++SignedSortKey.binary b count))
        (RawRowJoin.bank (RawRowJoin.padded (port a) B
          (Function.update (Fin.addCases A extra) (port a) [])) R B
          (out++SignedSortKey.binary b count)) ∧
      Paid.Returned p (Driver.value a row.d row.p row.cuts.length C) word
        (WarmFields.words row Q estimate 1 select) A ∧
      Paid.Private a extra ∧ Paid.Protected p row C A ∧
      extra (ScannedClean.fresh a 1)=List.replicate (Driver.value a row.d row.p row.cuts.length C) true := by
  dsimp only
  obtain ⟨A,extra,r,hr,hh,ht,_hs,returned,copy,priv,protect⟩ :=
    Paid.warm_owned_run a row C Q estimate 1 f select [] hC hQ hf hc
  simp only [List.nil_append] at hh returned
  unfold Paid.warmMachine Paid.warmEntry at hr
  have printed := step_of_startWith (Paid.driver a) (Paid.warm a)
    (Paid.heads a (producer a) []) _ (input a row C Q select) _ r hr hh ht
  have printed' : Step (Paid.warmMachine a) (Paid.warmBudget a row C Q)
      (fun _=>0) (input a row C Q select)
      (Paid.heads a (producer a) (Stream.recordWord (scalarWidth (EquationRow.request row) Q)
        estimate (selected (CompetitorSelectedCells.cells row.odd f select)).sum 1))
      (Fin.addCases A extra) := by
    unfold Paid.warmMachine
    exact printed.congr_in (empty_heads a) rfl
  have hword : (Fin.addCases (motive:=fun _=>List Bool) A extra) (port a)=
      Stream.recordWord (scalarWidth (EquationRow.request row) Q) estimate
        (selected (CompetitorSelectedCells.cells row.odd f select)).sum 1 := by
    simp only [port,Paid.old,Fin.addCases_left]
    exact returned.1
  have joined := RawRowState.run (Paid.warmMachine a) (port a) _ _ B R estimate _ 1
    (input a row C Q select) (Fin.addCases A extra) _ out printed' hword hR hB hBR
  exact ⟨A,extra,joined,returned,priv,protect,copy⟩

theorem warm_budget_le (a : WilliamsAlgorithm) (row : EquationRow.Input) (C Q : Nat)
    (hC : (Header.stream row).length≤C) (hQ : Q≤(EquationRow.request row).p) :
    Paid.warmBudget a row C Q ≤ ScannedClean.budget a row C+1+
      (8*Driver.value a row.d row.p row.cuts.length C+
        40*scalarWidth (EquationRow.request row) Q+74) := by
  have hf := Driver.fuel_bound a row C Q hC hQ
  have he := Warm.split_budget a row C Q
  unfold Paid.warmBudget WarmPrepared.budget WarmActual.budget Reuse.budget Reuse.afterBudget
  omega

/-- Linear in the existing paid driver; its residual-table factor occurs once. -/
theorem budget_le (a : WilliamsAlgorithm) (row : EquationRow.Input) (C Q B : Nat)
    (hC : (Header.stream row).length≤C) (hQ : Q≤(EquationRow.request row).p)
    (hB : RowPayload.budget (scalarWidth (EquationRow.request row) Q)≤B) :
    budget a row C Q B ≤
      2*(10*DriverLayout.e a+10*DriverLayout.sweepCount a+1100)*
        (Driver.value a row.d row.p row.cuts.length C+1)+
      80*scalarWidth (EquationRow.request row) Q+4*B+200 := by
  have h1 := RawRowJoin.budget_le (Paid.warmBudget a row C Q)
    (scalarWidth (EquationRow.request row) Q) B hB
  have h2 := warm_budget_le a row C Q hC hQ
  have h3 := DriverLayout.budget_linear a row.d row.p row.cuts.length C
  unfold ScannedClean.budget ScannedClean.cleanBudget at h2
  unfold budget
  nlinarith

theorem reset_driver (a : WilliamsAlgorithm) (D : Nat) (word : List Bool)
    (fields : Fin 7→List Bool) (A : Fin (WarmPrepare.tapes (producer a))→List Bool)
    (extra : Fin (ScannedClean.tapes a)→List Bool)
    (h : Paid.Returned (producer a) D word fields A) :
    Function.update (Fin.addCases (motive:=fun _=>List Bool) A extra) (port a) []
      (Paid.old a (producer a) (WarmPrepare.driver (producer a))) = List.replicate D true := by
  have hne : Paid.old a (producer a) (WarmPrepare.driver (producer a))≠port a := by
    intro he
    have hv := congrArg (fun i : Fin (tapes a)=>i.val) he
    apply WarmPrepared.driver_ne (producer a)
    apply Fin.ext
    exact hv
  erw [Function.update_of_ne hne]
  simp only [Paid.old,Fin.addCases_left]
  exact h.2.2.1

theorem input_driver_empty (a : WilliamsAlgorithm) (row : EquationRow.Input) (C Q : Nat)
    (select : Fin (EquationRow.request row).U→Fin (EquationRow.request row).U→Bool) :
    input a row C Q select (Paid.old a (producer a) (WarmPrepare.driver (producer a)))=[] := by
  simp only [input,Paid.input,Paid.old,Fin.addCases_left,Paid.public_driver,List.replicate_zero]

/-- The complete direct extraction is not, by equality alone, the next cold entry. -/
theorem reset_ne_input (a : WilliamsAlgorithm) (row : EquationRow.Input) (C Q : Nat)
    (select : Fin (EquationRow.request row).U→Fin (EquationRow.request row).U→Bool)
    (word : List Bool) (A : Fin (WarmPrepare.tapes (producer a))→List Bool)
    (extra : Fin (ScannedClean.tapes a)→List Bool)
    (h : Paid.Returned (producer a) (Driver.value a row.d row.p row.cuts.length C)
      word (WarmFields.words row Q estimate 1 select) A) :
    Function.update (Fin.addCases A extra) (port a) [] ≠ input a row C Q select := by
  intro he
  have hv := congrFun he (Paid.old a (producer a) (WarmPrepare.driver (producer a)))
  erw [reset_driver a _ word _ A extra h,input_driver_empty] at hv
  have hl := congrArg List.length hv
  simp only [List.length_replicate,List.length_nil] at hl
  unfold Driver.value at hl
  omega

end NearCubicWires.P1TopDownPaidPayload
