import Proof.MachineModel.ClosureRawRowJoin

/-! Actual scanner/printer → binary row payload, with a restored bounded
record buffer. This consumes the preceding joins at one physical bank.
Native header, metadata, mask and paid workspace are still produced upstream.
-/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.P1Closure.ScannedRawRow
open LocalBitMultitape ExtDecompositionBatch RepairRepresentation RepairOrdinary
open CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients C10RowFrameJoin RecoveryRootRound
open CompetitorSelectedCount CompetitorCountMask MatrixScoreBatch
open CompetitorCrossScheduler (producer)
open RepairSource.CloseoutFinal P1Independent

attribute [local irreducible] CompetitorCrossScheduler.producer Warm.input

def port (p : Program) : Fin (ScannedRow.tapes p) := ((Reuse.output p).castAdd 7).castAdd 3

theorem input_port (p : Program) (row : EquationRow.Input) (C D Q : Nat)
    (q : CompetitorValidity.Estimate) (den : Nat)
    (select : Fin (EquationRow.request row).U → Fin (EquationRow.request row).U → Bool)
    (old : Fin (WholePrefix.tapes p) → List Bool) (out : List Bool) :
    ScannedRow.input p row C D Q q den select old out (port p) = out := by
  have hne : Reuse.output p ≠ Reuse.native p := by
    intro h
    have hv := congrArg Fin.val h
    rw [output_val,native_val] at hv
    have := tapes_ge p
    omega
  simp only [ScannedRow.input,ScannedRow.bank,port,Fin.addCases_left]
  rw [Function.update_of_ne hne,exitTapes_output]

theorem output_port (p : Program) (row : EquationRow.Input) (C D Q : Nat)
    (q : CompetitorValidity.Estimate) (den : Nat)
    (select : Fin (EquationRow.request row).U → Fin (EquationRow.request row).U → Bool)
    (out : List Bool) : ScannedRow.output p row C D Q q den select out (port p) = out := by
  have hne : (Reuse.output p).val ≠ 52 := by
    rw [output_val]
    have := tapes_ge p
    omega
  simp only [ScannedRow.output,port,Fin.addCases_left,WarmTransaction.output,
    WarmTransaction.caps,Fin.val_castAdd,hne,if_false,ZeroPadding.pad_zero,exitTapes_output]

theorem empty_heads (p : Program) : ScannedRow.heads p [] = fun _ => 0 := by
  funext i
  simp [ScannedRow.heads,ScannedRow.bank,bankHeads,Fin.addCases]

noncomputable def machine (a : WilliamsAlgorithm) :=
  RawRowJoin.machine (ScannedRow.machine a) (port (producer a))

theorem run (a : WilliamsAlgorithm) (row : EquationRow.Input) (C D Q B R : Nat)
    (q : CompetitorValidity.Estimate) (den : Nat)
    (f : Fin (EquationRow.request row).U → Fin (EquationRow.request row).U → Nat)
    (select : Fin (EquationRow.request row).U → Fin (EquationRow.request row).U → Bool)
    (old : Fin (WholePrefix.tapes (producer a)) → List Bool) (out : List Bool)
    (hcapacity : old (Retained.capacity (producer a)) = List.replicate C true)
    (hCD : C ≤ D) (hd : row.d ≤ D) (hp : row.p ≤ D) (hDpos : 1 ≤ D)
    (hC : (Header.stream row).length ≤ C) (hQ : Q ≤ (EquationRow.request row).p)
    (hf : ∀ i j, f i j < 2^Q)
    (hc : ∀ i : Fin ((EquationRow.request row).U*(EquationRow.request row).U),
      Int.ModEq ((2 : Int)^Q)
        (SupplierPrinter.weightedDominance (leftScore (EquationRow.request row))
          (rightScore (EquationRow.request row)) (weight (EquationRow.request row)) i.divNat i.modNat)
        (f i.divNat i.modNat))
    (hD : Driver.value a row.d row.p row.cuts.length C ≤ D)
    (hB : RowPayload.budget (scalarWidth (EquationRow.request row) Q) ≤ B)
    (hR : ScannedRow.budget a row D Q ≤ R) (hBR : B+1 ≤ R) :
    let p := producer a
    let b := scalarWidth (EquationRow.request row) Q
    let count := (selected (CompetitorSelectedCells.cells row.odd f select)).sum
    let Z := ScannedRow.output p row C D Q q den select (Stream.recordWord b q count den)
    Step (machine a) (RawRowJoin.budget (ScannedRow.budget a row D Q) b B)
      (RawRowJoin.heads (ScannedRow.tapes p) out)
      (RawRowJoin.bank (RawRowJoin.padded (port p) B
        (ScannedRow.input p row C D Q q den select old [])) R B out)
      (dockH (RawRowJoin.slots (port p)) (RawRowJoin.heads (ScannedRow.tapes p) out)
        (RowPayloadReusable.heads (out++SignedSortKey.binary b count)))
      (install (RawRowJoin.slots (port p))
        (RawRowJoin.bank (RawRowJoin.padded (port p) B Z) R B out)
        (RowPayloadReusable.input [] (out++SignedSortKey.binary b count) B R)) ∧
    RawRowJoin.budget (ScannedRow.budget a row D Q) b B ≤ 22*D+4*B+170 := by
  dsimp only
  have printed := ScannedRow.run a row C D Q q den f select old []
    hcapacity hCD hd hp hDpos hC hQ hf hc hD
  dsimp only at printed
  rw [empty_heads,List.nil_append] at printed
  refine ⟨RawRowJoin.run (ScannedRow.machine a) (port (producer a))
    (ScannedRow.budget a row D Q) _ B R q _ den _ _ _ out printed
    (output_port _ _ _ _ _ _ _ _ _) hR hB hBR, ?_⟩
  have h := RawRowJoin.budget_le (ScannedRow.budget a row D Q) _ B hB
  have hrow := ScannedRow.budget_le a row C D Q hC hQ hD
  omega

end NearCubicWires.P1Closure.ScannedRawRow
