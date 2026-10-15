import Proof.Hierarchy.CompetitorCountTableDock

/-! One source-fixed ordinary program executes original matrix Request plus
row Q/parity through both count banks, signed merge, natural residue and
the paid odd-column crop. Actual row semantics discharge the residue contract. -/
namespace NearCubicWires.RepairOrdinary.CompetitorCountTable
open LocalBitMultitape RecoveryExecution RecoveryRootRound RepairRepresentation
open CompetitorCrossScheduler (producer)
open MatrixScoreBatch (Request)
open SupplierPrinter SupplierPipeline SupplierEstimator ThresholdCompiler
open SupplierPrime ThresholdAlignedEnvelope RowBinLift
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine (a : WilliamsAlgorithm) := Composition.machine (prefixMachine a) (finalProgram (producer a))
noncomputable def budget (a : WilliamsAlgorithm) (r : Request) (q : ℕ) :=
  prefixBudget a r+1+CompetitorFinalTable.budget r.U (CompetitorSameBucketColdDense.width r) q

theorem cold_run (a : WilliamsAlgorithm) (r : Request) (q : ℕ) (odd : Bool)
    (f : Fin r.U → Fin r.U → ℕ)
    (hq : q≤CompetitorSameBucketColdDense.width r) (he : odd=true → r.U/2+r.U/2=r.U)
    (hcount : ∀ i : Fin (r.U*r.U),f i.divNat i.modNat<2^q)
    (hcongruent : ∀ i : Fin (r.U*r.U),Int.ModEq ((2 : ℤ)^q)
      (weightedDominance (MatrixScoreBatch.leftScore r) (MatrixScoreBatch.rightScore r)
        (MatrixScoreBatch.weight r) i.divNat i.modNat) (f i.divNat i.modNat)) :
    ∃ actual,run (machine a) (budget a r q) (input (producer a) r q odd)=some actual ∧
      actual.steps≤budget a r q ∧ actual.final.heads=heads (producer a) (MatrixScoreBatch.output r).length ∧
      actual.final.tapes (slot (producer a) 141)=CompetitorFinalTable.word q odd f ∧
      actual.final.tapes (slot (producer a) 36)=List.replicate q true ∧
      actual.final.tapes (slot (producer a) 37)=UnaryTemplate.tape r.U ∧
      actual.final.tapes (slot (producer a) 38)=[odd] ∧
      actual.final.tapes (old (producer a) (CompetitorCountBanks.field (producer a) 0))=MatrixScoreBatch.physicalInput r := by
  obtain ⟨first,data,out,hr,hs,hh,ht,hn,hc,hb,h0,hU,hbank⟩ := prefix_run a r q odd
  exact final_dock (producer a) (prefixMachine a) (prefixBudget a r) r q odd f first data out
    hr hs hh ht hn hc hb h0 hU hbank hq he hcount hcongruent

def rowValues {l r : ℕ} (rows : List (List (List (Equation l r)))) (input : EquationRow.Input)
    (i j : Fin (EquationRow.request input).U) := CompetitorRowCountMeaning.count rows i.val j.val

theorem row_run {l r : ℕ} (a : WilliamsAlgorithm) (w Q : ℕ)
    (rows : List (List (List (Equation l r)))) (row : EquationRow.Input)
    (hc : row.cuts=RowPowerBinLift.batch w Q rows)
    (hw : ∀ ms ∈ rows,∀ e ∈ ms.flatten,equationMagnitudeBound e<2^w)
    (hrows : rows.length<2^Q) (hQ : Q≤row.p) :
    ∃ actual,run (machine a) (budget a (EquationRow.request row) Q)
      (input (producer a) (EquationRow.request row) Q row.odd)=some actual ∧
      actual.steps≤budget a (EquationRow.request row) Q ∧
      actual.final.heads=heads (producer a) (MatrixScoreBatch.output (EquationRow.request row)).length ∧
      actual.final.tapes (slot (producer a) 141)=CompetitorFinalTable.word Q row.odd (rowValues rows row) ∧
      actual.final.tapes (slot (producer a) 36)=List.replicate Q true ∧
      actual.final.tapes (slot (producer a) 37)=UnaryTemplate.tape (EquationRow.request row).U ∧
      actual.final.tapes (slot (producer a) 38)=[row.odd] ∧
      actual.final.tapes (old (producer a) (CompetitorCountBanks.field (producer a) 0))=
        MatrixScoreBatch.physicalInput (EquationRow.request row) := by
  have hwidth : Q≤CompetitorSameBucketColdDense.width (EquationRow.request row) := by
    rw [CompetitorSameBucketColdDense.width_eq]
    change Q≤row.d+2*(row.p+1)+3
    omega
  exact cold_run a (EquationRow.request row) Q row.odd (rowValues rows row) hwidth
    (CompetitorRowCountMeaning.odd_even_size row)
    (fun i => CompetitorRowCountMeaning.count_fit Q rows hrows i.divNat.val i.modNat.val)
    (fun i => CompetitorRowCountMeaning.request_modEq w Q rows row hc hw i.divNat i.modNat)

end NearCubicWires.RepairOrdinary.CompetitorCountTable
