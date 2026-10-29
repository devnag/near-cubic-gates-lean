import SourceAdapters.Compile.OraclePrintTransBounds

/-!
proof of `thm:short-pcp-ours`, Step 4: the complete transition template uses at most eleven binders
and sixteen arithmetic registers, uniformly over all program tables.
-/
namespace NearCubicGates.Adapters.Compile.OraclePrint
open NearCubicWires NearCubicWires.RepairSource NearCubicWires.FinitePredicateCircuit
  NearCubicWires.LocalBitMultitape OracleExecution
set_option autoImplicit false

theorem actionViewU_depth (p : OrdinaryOracleProgram) (action : Action p.base.tapeCount p.base.stateCount) :
    (actionViewU p action).depth≤1 := by
  simp only [actionViewU,U.depth,max_le_iff]
  refine ⟨by omega,?_,?_⟩
  · apply pickU_depth_le
    intro u hu
    obtain ⟨tape,rfl⟩ := List.mem_ofFn.mp hu
    simp [actionHeadU,headSelectionU,U.depth,U.ofBool]
  · apply pickU_depth_le
    intro u hu
    obtain ⟨tape,rfl⟩ := List.mem_ofFn.mp hu
    cases hw : action.write tape <;> simp [writtenCellU,hw,U.depth,U.ofBool]

theorem actionViewU_tneed (p : OrdinaryOracleProgram) (action : Action p.base.tapeCount p.base.stateCount) :
    (actionViewU p action).tneed≤16 := by
  simp only [actionViewU,U.tneed,max_le_iff]
  refine ⟨by simp [Tm.need],by simp [Tm.need],by simp [initHeadEndT,Tm.need],?_,?_⟩
  · apply pickU_tneed_le _ _ _ (by omega) (by simp [Tm.need])
    intro u hu
    obtain ⟨tape,rfl⟩ := List.mem_ofFn.mp hu
    cases hm : action.move tape <;>
      simp [actionHeadU,headSelectionU,moveT,hm,U.tneed,U.ofBool,Tm.ofBool,headT,Tm.need]
  · apply pickU_tneed_le _ _ _ (by omega) (by simp [initHeadEndT,Tm.need])
    intro u hu
    obtain ⟨tape,rfl⟩ := List.mem_ofFn.mp hu
    cases hw : action.write tape <;>
      simp [writtenCellU,hw,U.tneed,U.ofBool,Tm.ofBool,headT,cellT,initHeadEndT,Tm.need]

theorem localActionU_depth (p : OrdinaryOracleProgram) (action : Action p.base.tapeCount p.base.stateCount) :
    (localActionU p action).depth≤2 := by
  simp only [localActionU,U.depth,max_le_iff]
  refine ⟨(actionViewU_depth p action).trans (by omega),?_,?_⟩
  · apply pickU_depth_le
    intro u hu
    obtain ⟨tape,rfl⟩ := List.mem_ofFn.mp hu
    cases hw : action.write tape <;>
      simp [actionLengthU,hw,lengthSelectionU,headSelectionU,U.depth,U.ofBool]
  · simp [localRemainingU,U.depth,U.ofBool]

theorem localActionU_tneed (p : OrdinaryOracleProgram) (action : Action p.base.tapeCount p.base.stateCount) :
    (localActionU p action).tneed≤16 := by
  simp only [localActionU,U.tneed,max_le_iff]
  refine ⟨by simp [initWindowT,Tm.need],actionViewU_tneed p action,
    by simp [initLengthEndT,initWindowT,Tm.need],?_,?_⟩
  · apply pickU_tneed_le _ _ _ (by omega) (by simp [initWindowT,Tm.need])
    intro u hu
    obtain ⟨tape,rfl⟩ := List.mem_ofFn.mp hu
    cases hw : action.write tape <;>
      simp [actionLengthU,hw,lengthSelectionU,headSelectionU,maxT,U.tneed,U.ofBool,Tm.ofBool,
        headT,lenT,initWindowT,Tm.need]
  · simp [localRemainingU,U.tneed,U.ofBool,Tm.ofBool,budgetT,initLengthEndT,initWindowT,Tm.need]

theorem transitionRowU_depth (p : OrdinaryOracleProgram) (state : Fin p.base.stateCount)
    (scans : Fin p.base.tapeCount → Bool) : (transitionRowU p state scans).depth≤4 := by
  unfold transitionRowU
  split
  · simp [U.depth]
  · cases p.query state with
    | none =>
      cases p.base.machine.rule state scans with
      | none => simp [U.ofBool,U.depth]
      | some action =>
        exact max_le ((localGuardU_depth p action).trans (by omega))
          ((localActionU_depth p action).trans (by omega))
    | some rule => exact max_le (queryGuardU_depth p) ((queryActionU_depth p rule).trans (by omega))

theorem transitionRowU_tneed (p : OrdinaryOracleProgram) (state : Fin p.base.stateCount)
    (scans : Fin p.base.tapeCount → Bool) : (transitionRowU p state scans).tneed≤16 := by
  unfold transitionRowU
  split
  · simp [U.tneed,Tm.need]
  · cases p.query state with
    | none =>
      cases p.base.machine.rule state scans with
      | none => simp [U.ofBool,U.tneed,Tm.ofBool,Tm.need]
      | some action => exact max_le (localGuardU_tneed p action) (localActionU_tneed p action)
    | some rule => exact max_le (queryGuardU_tneed p) (queryActionU_tneed p rule)

theorem Tt_depth (p : OrdinaryOracleProgram) : (Tt p).depth≤11 := by
  apply (orList_depth_le _ _).2
  intro u hu
  obtain ⟨state,rfl⟩ := List.mem_ofFn.mp hu
  apply (orList_depth_le _ _).2
  intro u hu
  obtain ⟨mask,rfl⟩ := List.mem_ofFn.mp hu
  exact max_le ((rowU_depth state (scanMask mask) 5).trans (by omega))
    ((transitionRowU_depth p state (scanMask mask)).trans (by omega))

theorem Tt_tneed (p : OrdinaryOracleProgram) : (Tt p).tneed≤16 := by
  apply (orList_tneed_le _ 16 (by omega)).2
  intro u hu
  obtain ⟨state,rfl⟩ := List.mem_ofFn.mp hu
  apply (orList_tneed_le _ 16 (by omega)).2
  intro u hu
  obtain ⟨mask,rfl⟩ := List.mem_ofFn.mp hu
  exact max_le (rowU_tneed state (scanMask mask) 5) (transitionRowU_tneed p state (scanMask mask))

end NearCubicGates.Adapters.Compile.OraclePrint
