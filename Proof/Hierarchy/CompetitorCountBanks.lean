import Proof.Hierarchy.CompetitorCountBanksDock

/-! Full original-request production of both canonical same and cross P/N
banks by one source-fixed ordinary program. Every matrix, dimension, stable
key, zero cell, count plane, allocation and grouping pass is executed. -/
namespace NearCubicWires.RepairOrdinary.CompetitorCountBanks
open LocalBitMultitape RecoveryRootRound RepairRepresentation
open CompetitorCrossScheduler (producer)
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
    (∀ i : Fin 35,actual.final.tapes (tableNative (producer a) i)=CompetitorPlaneTableEntry.tapes out r.p i) ∧
    TableContext (natBitLength r.U) (CompetitorPlaneWidth.width (natBitLength r.U) r.p)
      (CompetitorCrossStateMeaning.state r) out ∧
    Bounded (natBitLength r.U) r.p (2*r.p) (CompetitorCrossStateMeaning.state r) ∧
    actual.final.tapes (field (producer a) 0)=MatrixScoreBatch.physicalInput r ∧
    actual.final.tapes (field (producer a) 44)=UnaryTemplate.tape r.U ∧
    actual.final.tapes (bank (producer a))=sameWord r := by
  obtain ⟨prepared,hf,fi,f0,fU,fb⟩ := prefix_run a r
  exact dock_cold (producer a) (prefixMachine a) (prefixBudget a r) r prepared hf fi f0 fU fb

end NearCubicWires.RepairOrdinary.CompetitorCountBanks
