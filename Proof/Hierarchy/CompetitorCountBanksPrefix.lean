import Proof.Hierarchy.CompetitorCountBanksSame

/-! Original Request -> all Williams packets and same-bucket dense bank.
The complete cross-table input survives verbatim at this reusable endpoint. -/
namespace NearCubicWires.RepairOrdinary.CompetitorCountBanks
open LocalBitMultitape RecoveryRootRound RepairRepresentation
open CompetitorCrossScheduler (producer)
open MatrixScoreBatch (Request)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def first (a : WilliamsAlgorithm) := ClockJoin.lifted (e := 511)
  (Equiv.refl (Fin (tapes (producer a)))) (CompetitorCrossScheduler.prefixMachine a)
noncomputable def prefixMachine (a : WilliamsAlgorithm) := Composition.machine (first a) (same (producer a))
noncomputable def prefixBudget (a : WilliamsAlgorithm) (r : Request) :=
  CompetitorCrossScheduler.prefixBudget a r+1+CompetitorSameBucketColdDense.budget r

theorem prefix_run (a : WilliamsAlgorithm) (r : Request) : ∃ out,
    ClockJoin.ReadyRun (prefixMachine a) (prefixBudget a r) (input (producer a) r) out ∧
      (∀ i,out (crossSlots (producer a) i)=CompetitorCrossTablePrepare.input
        (natBitLength r.U) (CompetitorPlaneWidth.width (natBitLength r.U) r.p) (r.U*r.U) r.p (MatrixScoreBatch.output r) i) ∧
      out (native (producer a) (CompetitorCrossScheduler.fieldSlots (producer a) 0))=MatrixScoreBatch.physicalInput r ∧
      out (native (producer a) (CompetitorCrossScheduler.fieldSlots (producer a) 44))=UnaryTemplate.tape r.U ∧
      out (bank (producer a))=sameWord r := by
  obtain ⟨prepared,hp,pi,p0,pU⟩ := CompetitorCrossScheduler.prefix_run a r
  have hfirst : ClockJoin.ReadyRun (first a) (CompetitorCrossScheduler.prefixBudget a r)
      (input (producer a) r) (extend (producer a) prepared) :=
    ClockJoin.lift (e := 511) (Equiv.refl (Fin (tapes (producer a)))) _ _ _ _ (fun _ : Fin 511 => []) hp
  have pw : prepared (CompetitorCrossScheduler.fieldSlots (producer a) 52)=
      List.replicate (CompetitorSameBucketColdDense.width r) true := pi 9
  obtain ⟨out,hs,hkeep,hbank⟩ := same_run (producer a) r prepared p0 pw
  refine ⟨out,ClockJoin.join _ _ _ _ _ _ _ hfirst hs,?_,?_,?_,hbank⟩
  · intro i
    exact (hkeep (CompetitorCrossScheduler.crossSlots (producer a) i)).trans (pi i)
  · exact (hkeep (CompetitorCrossScheduler.fieldSlots (producer a) 0)).trans p0
  · exact (hkeep (CompetitorCrossScheduler.fieldSlots (producer a) 44)).trans pU

end NearCubicWires.RepairOrdinary.CompetitorCountBanks
