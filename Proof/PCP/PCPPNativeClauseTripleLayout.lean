import Proof.PCP.PCPPNativeClauseReusable

/-! Three raw references share one reusable original-field parser. Only
the selected reference destination changes between the three calls. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeClauseTriple
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def refSlots : Fin 3→Fin 25 := ![19,23,24]
def slots (target : Fin 3) (j : Fin 23) : Fin 25 :=
  if j=19 then refSlots target else j.castAdd 2
theorem injective (target : Fin 3) : Function.Injective (slots target) := by
  fin_cases target <;> decide
def data (source : List Bool) (stride p n C : ℕ) (refs : Fin 3→List Bool) : Fin 25→List Bool :=
  Fin.addCases (m:=23) (n:=2) (motive:=fun _ : Fin 25=>List Bool)
    (PCPPNativeClauseReusable.data source stride p n C (refs 0)) (fun j=>refs j.succ)
def heads (pos : ℕ) : Fin 25→ℕ :=
  Fin.addCases (m:=23) (n:=2) (motive:=fun _ : Fin 25=>ℕ)
    (PCPPNativeClauseReusable.heads pos) (fun _=>0)
noncomputable def fieldMachine (target : Fin 3) := RecoveryFocus.machine (slots target) PCPPNativeClauseReusable.machine
def entry {s : ℕ} (p : Machine 25 s) (pos : ℕ) (data : Fin 25→List Bool) : Configuration 25 s :=
  ⟨p.start,heads pos,data⟩

theorem field_input (source : List Bool) (stride p n C pos : ℕ)
    (refs : Fin 3→List Bool) (target : Fin 3) (j : Fin 23) :
    heads pos (slots target j)=PCPPNativeClauseReusable.heads pos j ∧
      data source stride p n C refs (slots target j)=
        PCPPNativeClauseReusable.data source stride p n C (refs target) j := by
  fin_cases target <;> fin_cases j <;> exact ⟨rfl,rfl⟩

theorem reference_data (source : List Bool) (stride p n C : ℕ)
    (refs : Fin 3→List Bool) (j : Fin 3) :
    data source stride p n C refs (refSlots j)=refs j := by
  fin_cases j <;> rfl
theorem reference_head (pos : ℕ) (j : Fin 3) : heads pos (refSlots j)=0 := by
  fin_cases j <;> rfl
theorem coverage (target : Fin 3) (i : Fin 25) :
    (∃ j,slots target j=i) ∨ ∃ k,k≠target ∧ refSlots k=i := by
  fin_cases target <;> fin_cases i <;> decide

end NearCubicWires.RepairOrdinary.PCPPNativeClauseTriple
