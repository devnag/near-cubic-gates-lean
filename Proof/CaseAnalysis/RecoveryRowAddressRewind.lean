import Proof.CaseAnalysis.RecoveryRowAddressRaw

/-! One paid final rewind exposes the raw projected-address batch at head
zero. The same physical finite driver and reset log survive for reuse. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedRowAddress
open LocalBitMultitape RepairSource.VerifierDecoding RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def selected (i : Fin 3):=decide (i.val<2)
noncomputable def rewind:=MaskedReset.machine machine selected
def resetBudget (fields : List (List Bool)):=2*budget fields+2
def heads : Fin 4→ℕ:=![0,0,1,0]
def input (fields : List (List Bool)) (tail : List Bool) (L : ℕ) : Fin 4→List Bool:=
  ![FieldList.stream fields++tail,[],CompareMachine.word fields.length,List.replicate L false]
def output (fields : List (List Bool)) (tail : List Bool) (L : ℕ) : Fin 4→List Bool:=
  ![FieldList.stream fields++tail,fields.flatten,CompareMachine.word fields.length,List.replicate L false]

theorem entry_eq (fields : List (List Bool)) (tail : List Bool) (L : ℕ) :
    ZeroPadding.config (Rewind.Workspace.capacities 3 L)
      (Rewind.recording (cfg 0 (FieldList.stream fields++tail) 0 [] fields.length 1) 0)=
      (⟨rewind.start,heads,input fields tail L⟩ : Configuration 4 _) := by
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;> rfl
  · funext i;fin_cases i
    · exact ZeroPadding.pad_zero _
    · exact ZeroPadding.pad_zero _
    · exact ZeroPadding.pad_zero _
    · rfl

theorem reset_run (fields : List (List Bool)) (tail : List Bool) (L : ℕ) (hL : budget fields ≤ L) :
    ∃ r,runFrom rewind (resetBudget fields) ⟨rewind.start,heads,input fields tail L⟩=some r ∧
      r.steps=resetBudget fields ∧ r.final.heads=heads ∧ r.final.tapes=output fields tail L := by
  obtain ⟨p,pr,pf,ps⟩:=copy_run [] fields tail []
  simp only [List.nil_append,List.length_nil,Nat.zero_add] at pr pf
  obtain ⟨r,rr,rf,rs,_⟩:=MaskedReset.workspace_run machine selected _ L _ p pr
    (by intro i hi;fin_cases i <;> first | rfl | contradiction)
    (ps.le.trans hL)
  rw [ps,entry_eq] at rr
  refine ⟨r,rr,?_,?_,?_⟩
  · rw [rs,ps];rfl
  · rw [rf,pf]
    funext i;fin_cases i <;> rfl
  · rw [rf,pf]
    funext i;fin_cases i <;> rfl

end NearCubicWires.RepairOrdinary.RecoveryBoundedRowAddress
