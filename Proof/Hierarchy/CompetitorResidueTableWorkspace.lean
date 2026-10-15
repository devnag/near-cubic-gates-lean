import Proof.Hierarchy.CompetitorResidueTablePadded

/-! The complete residue pass keeps only the P/N source and count output
heads streaming. A physical short capacity driver clears eight local tapes. -/
namespace NearCubicWires.RepairOrdinary.CompetitorResidueTable
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorPlaneWorkspace
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def workSlots : Fin 8 → Fin 27 := ![0,1,2,3,5,6,7,10]
def heads (sourcePos outputPos : ℕ) : Fin 27 → ℕ := fun i =>
  if i=19 then sourcePos else if i=8 then outputPos else 0
def cfg {s : ℕ} (state : Fin s) (sourcePos outputPos : ℕ)
    (ambient : Fin 27 → List Bool) : Configuration 27 s :=
  ⟨state,heads sourcePos outputPos,ambient⟩
structure Store (w q : ℕ) (source output : List Bool) (ambient : Fin 27 → List Bool) : Prop where
  width : ambient 9=List.replicate w true
  widthCopy : ambient 20=List.replicate w true
  crop : ambient 4=List.replicate q true
  source : ambient 19=source
  output : ambient 8=output
  erase : ambient 21=List.replicate (capacity w) true
  reset : ambient 22=List.replicate (capacity w+1) false
  support : ∀ i,(ambient (workSlots i)).length≤capacity w
noncomputable def clean (w : ℕ) (ambient : Fin 27 → List Bool) := cleared (capacity w) workSlots ambient
noncomputable def clearProgram := CompetitorPlaneWorkspace.clearProgram workSlots

theorem work_injective : Function.Injective workSlots := by decide
theorem work_avoids (i : Fin 8) (j : Fin 27)
    (hj : j=4 ∨ j=8 ∨ j=9 ∨ j=19 ∨ j=20 ∨ j=21 ∨ j=22) : workSlots i≠j := by
  rcases hj with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> fin_cases i <;> decide
theorem clean_work (w : ℕ) (ambient : Fin 27 → List Bool) (i : Fin 8) :
    clean w ambient (workSlots i)=List.replicate (capacity w) false := by
  simp [clean,cleared,show ∃ j,workSlots j=workSlots i from ⟨i,rfl⟩]
theorem clean_keep (w : ℕ) (ambient : Fin 27 → List Bool) (j : Fin 27)
    (hj : j=4 ∨ j=8 ∨ j=9 ∨ j=19 ∨ j=20 ∨ j=21 ∨ j=22) :
    clean w ambient j=ambient j := by
  simp [clean,cleared,show ¬∃ i,workSlots i=j from fun ⟨i,hi⟩ => work_avoids i j hj hi]

theorem clear_run (w q sourcePos outputPos : ℕ) (source output : List Bool)
    (ambient : Fin 27 → List Bool) (h : Store w q source output ambient) :
    ∃ r,runFrom clearProgram (2*capacity w+4)
      (cfg clearProgram.start sourcePos outputPos ambient)=some r ∧
      r.final.heads=heads sourcePos outputPos ∧ r.final.tapes=clean w ambient ∧
      r.steps=2*capacity w+4 := by
  have hh : ∀ i,heads sourcePos outputPos (extend workSlots i)=0 := by
    intro i
    rw [extend_cases]
    split
    · simp [heads,work_avoids _ 19 (by simp),work_avoids _ 8 (by simp)]
    · split <;> rfl
  exact CompetitorPlaneWorkspace.clear_run workSlots work_injective
    (fun i => work_avoids i 21 (by simp)) (fun i => work_avoids i 22 (by simp))
    (capacity w) (heads sourcePos outputPos) ambient h.erase h.reset h.support hh

end NearCubicWires.RepairOrdinary.CompetitorResidueTable
