import Proof.Hierarchy.CompetitorCountTablePrefixDock
import Proof.Hierarchy.CompetitorCountTableInput

/-! Original Request plus actual row Q/parity metadata reaches both banks
and the precise final159 entry heads. All bank and preparation work is paid. -/
namespace NearCubicWires.RepairOrdinary.CompetitorCountTable
open LocalBitMultitape RecoveryExecution RecoveryRootRound RepairRepresentation
open CompetitorPlaneTable
open CompetitorCrossScheduler (producer)
open MatrixScoreBatch (Request)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def prefixMachine (a : WilliamsAlgorithm) := prefixOf (producer a) (CompetitorCountBanks.machine a)
noncomputable def prefixBudget (a : WilliamsAlgorithm) (r : Request) := CompetitorCountBanks.budget a r+2

theorem prefix_run (a : WilliamsAlgorithm) (r : Request) (q : ℕ) (odd : Bool) :
    ∃ actual data out,run (prefixMachine a) (prefixBudget a r) (input (producer a) r q odd)=some actual ∧
      actual.steps≤prefixBudget a r ∧ actual.final.heads=heads (producer a) (MatrixScoreBatch.output r).length ∧
      actual.final.tapes=extend (producer a) q odd data ∧
      (∀ i : Fin 35,data (CompetitorCountBanks.tableNative (producer a) i)=CompetitorPlaneTableEntry.tapes out r.p i) ∧
      TableContext (natBitLength r.U) (CompetitorPlaneWidth.width (natBitLength r.U) r.p)
        (CompetitorCrossStateMeaning.state r) out ∧
      Bounded (natBitLength r.U) r.p (2*r.p) (CompetitorCrossStateMeaning.state r) ∧
      data (CompetitorCountBanks.field (producer a) 0)=MatrixScoreBatch.physicalInput r ∧
      data (CompetitorCountBanks.field (producer a) 44)=UnaryTemplate.tape r.U ∧
      data (CompetitorCountBanks.bank (producer a))=CompetitorCountBanks.sameWord r := by
  obtain ⟨base,out,hr,hs,hh,ht,hc,hb,h0,hU,hbank⟩ := CompetitorCountBanks.cold_run a r
  obtain ⟨actual,ha,asteps,ah,atapes⟩ := prefix_dock (producer a) (CompetitorCountBanks.machine a)
    (CompetitorCountBanks.budget a r) r q odd base hr hh
  refine ⟨actual,base.final.tapes,out,ha,?_,ah,atapes,ht,hc,hb,h0,hU,hbank⟩
  unfold prefixBudget
  omega

end NearCubicWires.RepairOrdinary.CompetitorCountTable
