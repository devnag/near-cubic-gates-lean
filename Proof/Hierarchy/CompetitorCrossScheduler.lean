import Proof.Hierarchy.CompetitorCrossSchedulerDock

/-! One source-fixed ordinary program executes original framed Request ->
all signed Williams packets -> the exact cross-bucket P/N bank. The request
supplies no dimensions, matrices, capacity, zero bank or semantic premise. -/
namespace NearCubicWires.RepairOrdinary.CompetitorCrossScheduler
open LocalBitMultitape RecoveryExecution RecoveryRootRound RepairRepresentation
open MatrixScoreBatch (Request)
open CompetitorPlaneTable
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def table (a : WilliamsAlgorithm) :=
  RecoveryFocus.machine (crossSlots (producer a)) CompetitorCrossTableCold.machine
noncomputable def machine (a : WilliamsAlgorithm) := Composition.machine (prefixMachine a) (table a)
noncomputable def budget (a : WilliamsAlgorithm) (r : Request) := prefixBudget a r+1+
  CompetitorCrossTableCold.budget (natBitLength r.U)
    (CompetitorPlaneWidth.width (natBitLength r.U) r.p) (r.U*r.U) r.p
theorem cold_run (a : WilliamsAlgorithm) (r : Request) : ∃ actual out,
    run (machine a) (budget a r) (input (producer a) r)=some actual ∧ actual.steps ≤ budget a r ∧
    actual.final.heads=heads (producer a) (MatrixScoreBatch.output r).length ∧
    (∀ i : Fin 35,actual.final.tapes (native (producer a) i)=CompetitorPlaneTableEntry.tapes out r.p i) ∧
    TableContext (natBitLength r.U) (CompetitorPlaneWidth.width (natBitLength r.U) r.p)
      (CompetitorCrossStateMeaning.state r) out ∧
    Bounded (natBitLength r.U) r.p (2*r.p) (CompetitorCrossStateMeaning.state r) ∧
    actual.final.tapes (fieldSlots (producer a) 0)=MatrixScoreBatch.physicalInput r ∧
    actual.final.tapes (fieldSlots (producer a) 44)=UnaryTemplate.tape r.U := by
  obtain ⟨prepared,hf,fi,f0,fU⟩ := prefix_run a r
  exact dock_cold (producer a) (prefixMachine a) (prefixBudget a r) r prepared hf fi f0 fU

end NearCubicWires.RepairOrdinary.CompetitorCrossScheduler
