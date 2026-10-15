import Proof.CaseAnalysis.RecoverySuppliersSlots
import Proof.CaseAnalysis.RecoverySuppliersInput

/-! Execute the original hierarchy and count prefix in the final supplier
bank, retaining W and all subsequent work as actual empty physical tapes. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedColdSuppliers
open LocalBitMultitape RepairSource RepairSource.ProjectionNormalization RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
def countMachine (k d CH Cpad : ℕ) (code : List Bool):=
  RecoveryFocus.machine (countSlots source k d) (RecoveryBoundedColdHierarchyDock.Count.machine source k CH Cpad code)
def projectCount {k d s : ℕ} (c : Configuration (tapes source k d) s) : Configuration (base source k) s:=
  ⟨c.control,c.heads∘countSlots source k d,c.tapes∘countSlots source k d⟩

theorem count_run (k d CH Cpad : ℕ) (code x bound : List Bool) (W : ℕ) (hpad : k+3≤Cpad) :
    ∃ r,run (countMachine source k d CH Cpad code)
      (RecoveryBoundedColdHierarchyDock.Count.budget source k CH Cpad code x)
      (input source k d (frame x++frame bound) W)=some r ∧
      r.steps≤RecoveryBoundedColdHierarchyDock.Count.budget source k CH Cpad code x ∧
      RecoveryBoundedColdHierarchyDock.Count.Fields source k CH Cpad code x bound (projectCount source r.final) ∧
      (∀ i : Fin 158,r.final.heads (old source k d i)=0) ∧
      (∀ i : Fin 158,i≠70→i≠106→i≠157→ r.final.tapes (old source k d i)=[]) ∧
      (∀ i : Fin (tapes source k d),base source k ≤ i.val→
        r.final.heads i=0 ∧ r.final.tapes i=input source k d (frame x++frame bound) W i):=by
  obtain ⟨baseRun,hbase,hbs,hfields,hret⟩:=RecoveryBoundedColdHierarchyDock.Count.run
    source k CH Cpad code x bound hpad (fun _=>[]) (fun _=>0) rfl rfl rfl rfl rfl rfl
  obtain ⟨result,hr,hcontrol,hsteps,hheads,htapes,hother⟩:=RecoveryFocus.dock
    (countSlots source k d) (count_injective source k d)
    (RecoveryBoundedColdHierarchyDock.Count.machine source k CH Cpad code)
    (RecoveryBoundedColdHierarchyDock.Count.budget source k CH Cpad code x)
    (fun _=>0) (input source k d (frame x++frame bound) W) _
    (by intro i;exact (count_heads source k i).symm)
    (count_input source k d (frame x++frame bound) W) baseRun hbase
  have hp : projectCount source result.final=baseRun.final:=
    configuration_ext hcontrol (funext hheads) (funext htapes)
  have holdHead (i : Fin 158) : result.final.heads (old source k d i)=
      baseRun.final.heads (RecoveryBoundedColdHierarchyDock.Count.old source k i):=by
    simpa only [count_old] using hheads (RecoveryBoundedColdHierarchyDock.Count.old source k i)
  have holdTape (i : Fin 158) : result.final.tapes (old source k d i)=
      baseRun.final.tapes (RecoveryBoundedColdHierarchyDock.Count.old source k i):=by
    simpa only [count_old] using htapes (RecoveryBoundedColdHierarchyDock.Count.old source k i)
  refine ⟨result,hr,hsteps.trans_le hbs,?_,?_,?_,?_⟩
  · rw [hp]
    exact hfields
  · intro i
    by_cases h70 : i=70
    · subst i;exact (holdHead 70).trans hfields.clauseStreamHead
    by_cases h106 : i=106
    · subst i;exact (holdHead 106).trans hfields.queryStreamHead
    by_cases h157 : i=157
    · subst i;exact (holdHead 157).trans hfields.rawClausesHead
    exact (holdHead i).trans (hret i h70 h106 h157).1
  · intro i h70 h106 h157
    exact (holdTape i).trans (hret i h70 h106 h157).2
  · intro i hi
    exact hother i (by
      intro j he
      have hj:=j.isLt
      have hv:=congrArg Fin.val he
      change j.val=i.val at hv
      omega)

end
end NearCubicWires.RepairOrdinary.RecoveryBoundedColdSuppliers
