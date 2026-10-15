import Proof.MachineModel.TopDownPaidPayload
import Proof.CaseAnalysis.RowsEstimatorPaidBacking

/-! Apply the existing paid retirement/backing parent before extracting the
already-computed count. No scan of an old false-tail length is introduced.
The scanner input words and next-row reload remain explicit boundaries. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1TopDownPaidRetiredPayload
open LocalBitMultitape RepairOrdinary RepairRepresentation ExtDecompositionBatch
open CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount
open MatrixScoreBatch CompetitorCountMask
open CompetitorCrossScheduler (producer)
open P1Closure RecoveryRootRound
open P1TopDownPaidPayload (estimate port tapes)
attribute [local irreducible] CompetitorCrossScheduler.producer Paid.warmMachine
  Paid.driver Paid.warm Paid.retire Paid.retiredMachine RawRowJoin.machine

noncomputable def fuel (a : WilliamsAlgorithm) (row : EquationRow.Input) (C Q : Nat) :=
  Paid.warmBudget a row C Q+1+(2*Driver.value a row.d row.p row.cuts.length C+4)
noncomputable def machine (a : WilliamsAlgorithm) :=
  RawRowJoin.machine (Paid.retiredMachine a) (port a)
noncomputable def input (a : WilliamsAlgorithm) (row : EquationRow.Input) (C Q : Nat)
    (select : Fin (EquationRow.request row).U→Fin (EquationRow.request row).U→Bool)
    (caps : Fin (tapes a)→Nat) :=
  fun i=>ZeroPadding.pad (Paid.backingCaps a (producer a) caps i)
    (P1TopDownPaidPayload.input a row C Q select i)
noncomputable def budget (a : WilliamsAlgorithm) (row : EquationRow.Input) (C Q B : Nat) :=
  RawRowJoin.budget (fuel a row C Q) (scalarWidth (EquationRow.request row) Q) B

private theorem step_of_nested_pad {t sp sq su n : Nat}
    (first : Machine t sp) (second : Machine t sq) (last : Machine t su)
    (caps : Fin t→Nat) (hin hout : Fin t→Nat) (tin tout : Fin t→List Bool)
    (r : ExecutionReceipt t (sp+sq+su))
    (hr : runFrom (Composition.machine (Composition.machine first second) last) n
      (ZeroPadding.config caps (Composition.leftConfig su
        (WarmPrepared.startWith first second hin tin)))=some r)
    (hh : r.final.heads=hout) (ht : r.final.tapes=tout) :
    Step (Composition.machine (Composition.machine first second) last) n hin
      (fun i=>ZeroPadding.pad (caps i) (tin i)) hout tout := by
  rw [Paid.nested_start first second last hin tin] at hr
  exact Step.of_run hr hh ht

theorem backed_update_record {a : WilliamsAlgorithm} {p : Program} {row : EquationRow.Input}
    {C : Nat} {word : List Bool} {fields : Fin 7→List Bool}
    {Z : Fin (Paid.tapes a p)→List Bool} (h : Paid.Backed a p row C word fields Z)
    (next : List Bool) :
    Paid.Backed a p row C next fields
      (Function.update Z (Paid.old a p (WarmPrepare.spare p)) next) := by
  have keep (i : Fin (WarmPrepare.tapes p)) (hi : i≠WarmPrepare.spare p) :
      Function.update Z (Paid.old a p (WarmPrepare.spare p)) next (Paid.old a p i)=Z (Paid.old a p i) := by
    apply Function.update_of_ne
    intro he
    apply hi
    apply Fin.ext
    exact congrArg (fun j : Fin (Paid.tapes a p)=>j.val) he
  refine ⟨Function.update_self _ _ _,?_,?_,?_,?_,?_,?_⟩
  · intro i
    have hn : WarmPrepare.work p i≠WarmPrepare.spare p := by
      intro he
      have hv:=congrArg (fun j : Fin (WarmPrepare.tapes p)=>j.val) he
      have hb:=(Reuse.work_bounds p i).1
      rw [WarmPrepared.spare_val] at hv
      change (Reuse.work p i).val=WholePrefix.tapes p+1 at hv
      omega
    rw [keep _ hn]
    exact h.work i
  · rw [keep _ (WarmPrepared.driver_ne p)]
    exact h.driver
  · rw [keep _ (WarmPrepared.log_ne p)]
    exact h.log
  · intro i
    rw [keep _ (WarmPrepared.source_ne p i)]
    exact h.sources i
  · intro i hi
    rw [keep _ (WarmPrepared.old_ne p _)]
    exact h.protectedWords i hi
  · intro i
    have hn : i.natAdd (WarmPrepare.tapes p)≠Paid.old a p (WarmPrepare.spare p) := by
      intro he
      have hv:=congrArg (fun j : Fin (Paid.tapes a p)=>j.val) he
      have hb:=(WarmPrepare.spare p).isLt
      simp only [Fin.val_natAdd,Paid.old,Fin.val_castAdd] at hv
      omega
    erw [Function.update_of_ne hn]
    exact h.privateWords i

set_option maxHeartbeats 1000000 in
theorem run (a : WilliamsAlgorithm) (row : EquationRow.Input) (C Q B R : Nat)
    (f : Fin (EquationRow.request row).U→Fin (EquationRow.request row).U→Nat)
    (select : Fin (EquationRow.request row).U→Fin (EquationRow.request row).U→Bool)
    (caps : Fin (tapes a)→Nat) (out : List Bool)
    (hC : (Header.stream row).length≤C) (hQ : Q≤(EquationRow.request row).p)
    (hf : ∀ i j,f i j<2^Q)
    (hc : ∀ i : Fin ((EquationRow.request row).U*(EquationRow.request row).U),
      Int.ModEq ((2 : Int)^Q)
        (SupplierPrinter.weightedDominance (leftScore (EquationRow.request row))
          (rightScore (EquationRow.request row)) (weight (EquationRow.request row)) i.divNat i.modNat)
        (f i.divNat i.modNat))
    (hR : fuel a row C Q≤R)
    (hB : RowPayload.budget (scalarWidth (EquationRow.request row) Q)≤B)
    (hBR : B+1≤R) :
    let p := producer a
    let b := scalarWidth (EquationRow.request row) Q
    let count := (selected (CompetitorSelectedCells.cells row.odd f select)).sum
    let word := Stream.recordWord b estimate count 1
    ∃ Z : Fin (tapes a)→List Bool,
      Step (machine a) (budget a row C Q B)
        (RawRowJoin.heads (tapes a) out)
        (RawRowJoin.bank (RawRowJoin.padded (port a) B (input a row C Q select caps)) R B out)
        (RawRowJoin.heads (tapes a) (out++SignedSortKey.binary b count))
        (RawRowJoin.bank (RawRowJoin.padded (port a) B (Function.update Z (port a) [])) R B
          (out++SignedSortKey.binary b count)) ∧
      Paid.Backed a p row C word (WarmFields.words row Q estimate 1 select) Z ∧
      Paid.Backed a p row C [] (WarmFields.words row Q estimate 1 select)
        (Function.update Z (port a) []) := by
  dsimp only
  let p:=producer a
  let D:=Driver.value a row.d row.p row.cuts.length C
  let b:=scalarWidth (EquationRow.request row) Q
  let word:=Stream.recordWord b estimate (selected (CompetitorSelectedCells.cells row.odd f select)).sum 1
  have hw:=Paid.warm_owned_run a row C Q estimate 1 f select [] hC hQ hf hc
  simp only [List.nil_append] at hw
  have ho:=Paid.retire_owned_join a p row C D _ _ word
    (WarmFields.words row Q estimate 1 select) (Paid.warmMachine a)
    (Paid.warmEntry a row C Q estimate 1 select []) hw
  obtain ⟨r,hr,hh,_hs,backed⟩:=ho.backed caps
  unfold Paid.warmMachine Paid.warmEntry at hr
  have printed:=step_of_nested_pad (Paid.driver a) (Paid.warm a) (Paid.retire a p)
    (Paid.backingCaps a p caps) (Paid.heads a p []) _
    (P1TopDownPaidPayload.input a row C Q select) _ r hr hh rfl
  have printed' : Step (Paid.retiredMachine a) (fuel a row C Q) (fun _=>0)
      (input a row C Q select caps) (Paid.heads a p word) r.final.tapes := by
    unfold Paid.retiredMachine Paid.warmMachine
    exact printed.congr_in (P1TopDownPaidPayload.empty_heads a) rfl
  have joined:=RawRowState.run (Paid.retiredMachine a) (port a) (fuel a row C Q) b B R
    estimate (selected (CompetitorSelectedCells.cells row.odd f select)).sum 1
    (input a row C Q select caps) r.final.tapes (Paid.heads a p word) out
    printed' backed.output hR hB hBR
  exact ⟨r.final.tapes,joined,backed,backed_update_record backed []⟩

theorem budget_le (a : WilliamsAlgorithm) (row : EquationRow.Input) (C Q B : Nat)
    (hB : RowPayload.budget (scalarWidth (EquationRow.request row) Q)≤B) :
    budget a row C Q B ≤ 2*Paid.warmBudget a row C Q+
      4*Driver.value a row.d row.p row.cuts.length C+4*B+20 := by
  have h:=RawRowJoin.budget_le (fuel a row C Q) (scalarWidth (EquationRow.request row) Q) B hB
  unfold budget fuel at *
  omega

end NearCubicWires.P1TopDownPaidRetiredPayload
