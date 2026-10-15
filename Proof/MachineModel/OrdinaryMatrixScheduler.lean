import Proof.MachineModel.OrdinaryMatrixPacketSchedulerLayout

/-! The whole cold raw-block producer is an actual ordinary finite program:
original framed Request, all sign/bit planes, exact packets, one rewind,
retained input and a source-fixed quadratic table envelope. -/
namespace NearCubicWires.RepairOrdinary.MatrixPacketScheduler
open LocalBitMultitape MatrixScoreBatch RepairRepresentation
open MatrixPacketSchedulerBounds (E C envelope)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem scheduler_run (a : WilliamsAlgorithm) (r : Request) : ∃ actual,
    run (program a (E a) (C a)).machine (envelope a r) ((program a (E a) (C a)).inputTapes (word r))=some actual ∧
    actual.final.tapes (program a (E a) (C a)).outputTape=output r ∧
    actual.final.tapes ⟨0,by have h:=(program a (E a) (C a)).twoTapes; omega⟩=physicalInput r ∧
    (∀ i,actual.final.heads i=0) ∧
    (∀ i,(actual.final.tapes i).length≤envelope a r) ∧ actual.steps≤envelope a r := by
  have hcap : ∀ j<r.p,∀ negative,MatrixVariablePacketWorkspace.footprint a r j negative≤
      MatrixPacketBootstrapState.capacity (E a) (C a) r := by
    intro j hj negative
    exact MatrixVariablePacketCapacity.capacity_bound a r negative j hj
  obtain ⟨base,hb,bout,bsrc,bheads,bsupport,bs⟩:=MatrixPacketReset.reset_run a (E a) (C a) r hcap
  obtain ⟨hbudget,hinput⟩:=MatrixPacketSchedulerBounds.final_bounds a r
  have htime : MatrixPacketReset.budget a (E a) (C a) r≤envelope a r := by
    unfold MatrixPacketReset.budget
    omega
  have hsupport : max (physicalInput r).length (MatrixPacketReset.budget a (E a) (C a) r+1)≤envelope a r := by
    exact max_le hinput hbudget
  have renamed:=TapeRenaming.run_rename (rename a (E a)) (MatrixPacketReset.machine a (E a) (C a))
    (MatrixPacketReset.budget a (E a) (C a) r)
    (initialConfiguration (MatrixPacketReset.machine a (E a) (C a)) (MatrixPacketReset.input a (E a) r)) base hb
  rw [configuration_rename] at renamed
  let actual:=TapeRenaming.receipt (rename a (E a)) base
  have hr : run (program a (E a) (C a)).machine (MatrixPacketReset.budget a (E a) (C a) r)
      ((program a (E a) (C a)).inputTapes (word r))=some actual := renamed
  have hm:=run_moreFuel (program a (E a) (C a)).machine (MatrixPacketReset.budget a (E a) (C a) r)
    (envelope a r-MatrixPacketReset.budget a (E a) (C a) r) _ actual hr
  rw [Nat.add_sub_of_le htime] at hm
  refine ⟨actual,hm,?_,?_,?_,?_,bs.trans htime⟩
  · change base.final.tapes ((rename a (E a)).symm ((rename a (E a)) (MatrixPacketReset.outputTape a (E a))))=_
    rw [Equiv.symm_apply_apply]
    exact bout
  · change base.final.tapes ((rename a (E a)).symm 0)=_
    have he : (rename a (E a)).symm 0=MatrixPacketReset.original a (E a) := by simp [rename]
    rw [he]
    exact bsrc
  · intro i
    exact bheads ((rename a (E a)).symm i)
  · intro i
    exact (bsupport ((rename a (E a)).symm i)).trans hsupport

noncomputable def coldScheduler (a : WilliamsAlgorithm) : ColdScheduler a where
  program := program a (E a) (C a)
  coefficient := MatrixPacketSchedulerBounds.coefficient a
  exponent := MatrixPacketSchedulerBounds.exponent a
  coefficientPositive := MatrixPacketSchedulerBounds.coefficient_positive a
  sourceExponentPaid := MatrixPacketSchedulerBounds.exponent_paid a
  runs := scheduler_run a

end NearCubicWires.RepairOrdinary.MatrixPacketScheduler
