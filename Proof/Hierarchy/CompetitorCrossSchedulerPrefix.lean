import Proof.Hierarchy.CompetitorCrossSchedulerLayout

/-! One source-fixed cold prefix produces all dimensions and every signed
matrix packet from the original framed request. Its exact endpoint is the
input of the complete cross-table, with no prepared-field assumption. -/
namespace NearCubicWires.RepairOrdinary.CompetitorCrossScheduler
open LocalBitMultitape RecoveryRootRound CompetitorRationalProducts RepairRepresentation
open MatrixScoreBatch (Request)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def supplier (a : WilliamsAlgorithm) := MatrixPacketScheduler.coldScheduler a
noncomputable def producer (a : WilliamsAlgorithm) := (supplier a).program
noncomputable def fields (a : WilliamsAlgorithm) :=
  RecoveryFocus.machine (fieldSlots (producer a)) CompetitorCrossRequestFields.machine
noncomputable def scheduler (a : WilliamsAlgorithm) :=
  RecoveryFocus.machine (schedulerSlots (producer a)) (producer a).machine
noncomputable def prefixMachine (a : WilliamsAlgorithm) := Composition.machine (fields a) (scheduler a)
noncomputable def schedulerBudget (a : WilliamsAlgorithm) (r : Request) :=
  (supplier a).coefficient*(r.U+1)^2*(r.d+r.p+1)^(supplier a).exponent
noncomputable def prefixBudget (a : WilliamsAlgorithm) (r : Request) :=
  CompetitorCrossRequestFields.budget r+1+schedulerBudget a r

theorem prefix_run (a : WilliamsAlgorithm) (r : Request) : ∃ out,
    ClockJoin.ReadyRun (prefixMachine a) (prefixBudget a r) (input (producer a) r) out ∧
      (∀ i,out (crossSlots (producer a) i)=CompetitorCrossTablePrepare.input
        (natBitLength r.U) (CompetitorPlaneWidth.width (natBitLength r.U) r.p) (r.U*r.U) r.p (MatrixScoreBatch.output r) i) ∧
      out (fieldSlots (producer a) 0)=MatrixScoreBatch.physicalInput r ∧
      out (fieldSlots (producer a) 44)=UnaryTemplate.tape r.U := by
  obtain ⟨f,hf,f0,fp,fU,fb,fw,fn⟩ := CompetitorCrossRequestFields.fields_run r
  have hfields := bounded_focus (fieldSlots (producer a)) (field_injective (producer a)) _ _ _ hf
    (input (producer a) r) (field_input (producer a) r)
  let ftapes := install (fieldSlots (producer a)) (input (producer a) r) f
  obtain ⟨s,hs,so,s0,sh,_,ss⟩ := (supplier a).runs r
  have sready : ClockJoin.ReadyRun (producer a).machine (schedulerBudget a r)
      ((producer a).inputTapes (MatrixScoreBatch.word r)) s.final.tapes := ⟨s,hs,rfl,sh,ss⟩
  have hsch := bounded_focus (schedulerSlots (producer a)) (scheduler_injective (producer a)) _ _ _
    sready ftapes (scheduler_input (producer a) r f f0)
  let out := install (schedulerSlots (producer a)) ftapes s.final.tapes
  refine ⟨out,ClockJoin.join _ _ _ _ _ _ _ hfields hsch,
    cross_input (producer a) r f s.final.tapes fp fb fw fn so,?_,?_⟩
  · have he : schedulerSlots (producer a) ⟨0,by have h:=(producer a).twoTapes;omega⟩=fieldSlots (producer a) 0 := rfl
    change install (schedulerSlots (producer a)) ftapes s.final.tapes _=_
    rw [←he,install_slot _ (scheduler_injective (producer a))]
    exact s0
  · exact (scheduler_keep (producer a) ftapes s.final.tapes (fieldSlots (producer a) 44)
      (by simp [fieldSlots]) (by simp [fieldSlots]) (by simp [fieldSlots])).trans
      ((install_slot (fieldSlots (producer a)) (field_injective (producer a)) _ f 44).trans fU)

end NearCubicWires.RepairOrdinary.CompetitorCrossScheduler
