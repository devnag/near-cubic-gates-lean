import Proof.Supplier.RowTupleDerivedEnumeration

/-! The actual cold binary enumerator pays one recorded return of its
produced tuple stream. Its recording tape starts blank and its exponential
candidate count is never supplied as a runtime unary driver. -/
namespace NearCubicWires.RepairOrdinary.RowTupleEnumerationReady
open LocalBitMultitape RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def selected (i : Fin 40) : Bool := decide (i=17)
noncomputable def machine := MaskedReset.machine RowTupleDerivedEnumeration.machine selected
def input (w k M : ℕ) : Fin 41→List Bool :=
  Fin.addCases (m:=40) (n:=1) (motive:=fun _=>List Bool) (RowTupleDerivedEnumeration.input w k M) (fun _=>[])
def budget (w k : ℕ) := 2*RowTupleDerivedEnumeration.budget w k+2

theorem enumerate_run (w k M : ℕ) (hM:0<M) (hMw:M≤2^w) :
    ∃ r,run machine (budget w k) (input w k M)=some r ∧
      r.final.tapes 17=RowTupleEnumeration.word w k M ∧ r.final.heads 17=0 ∧
      r.steps≤budget w k := by
  obtain ⟨base,hbase,bt,_,bs⟩:=RowTupleDerivedEnumeration.enumerate_run w k M hM hMw
  obtain ⟨r,hr,rf,rs,_⟩:=MaskedReset.reset_run RowTupleDerivedEnumeration.machine selected _ _ base hbase (by
    intro i hi
    have h:=SelectiveReset.prefix_head (prefix_of_run RowTupleDerivedEnumeration.machine _ _ base hbase).1 i
    simpa only [initialConfiguration,zero_add] using h)
  have hb : 2*base.steps+2≤budget w k := by unfold budget; omega
  have more:=runFrom_moreFuel machine _ (budget w k-(2*base.steps+2)) _ r hr
  rw [Nat.add_sub_of_le hb] at more
  have hi : Rewind.recording (initialConfiguration RowTupleDerivedEnumeration.machine (RowTupleDerivedEnumeration.input w k M)) 0=
      initialConfiguration machine (input w k M) := by
    apply configuration_ext
    · rfl
    · funext i; refine Fin.addCases (m:=40) (n:=1) (fun j=>?_) (fun j=>?_) i
      all_goals simp [Rewind.recording,Rewind.config,initialConfiguration,input,Fin.addCases]
    · funext i; refine Fin.addCases (m:=40) (n:=1) (fun j=>?_) (fun j=>?_) i <;> rfl
  rw [hi] at more
  refine ⟨r,more,?_,?_,rs.le.trans hb⟩
  · rw [rf]
    exact bt
  · rw [rf]
    rfl

end NearCubicWires.RepairOrdinary.RowTupleEnumerationReady
