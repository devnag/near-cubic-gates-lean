import Proof.Hierarchy.CompetitorOddRowSliceProjection

/-! Reusable workspace for merging two aligned raw P/N banks. The two
source cursors and append cursor are never included in local erasure. -/
namespace NearCubicWires.RepairOrdinary.CompetitorBankMerge
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorPlaneWorkspace
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev capacity := CompetitorResidueTable.capacity
abbrev workSlots := CompetitorResidueTable.workSlots
noncomputable abbrev clean := CompetitorResidueTable.clean
noncomputable abbrev clearProgram := CompetitorResidueTable.clearProgram
def heads (leftPos rightPos outPos : ℕ) : Fin 27 → ℕ := fun i =>
  if i=19 then leftPos else if i=23 then rightPos else if i=8 then outPos else 0
def cfg {s : ℕ} (state : Fin s) (leftPos rightPos outPos : ℕ) (tapes : Fin 27 → List Bool) : Configuration 27 s :=
  ⟨state,heads leftPos rightPos outPos,tapes⟩
structure Store (w : ℕ) (left right out : List Bool) (ambient : Fin 27 → List Bool) : Prop where
  width : ambient 9=List.replicate w true
  widthCopy : ambient 20=List.replicate w true
  sourceLeft : ambient 19=left
  sourceRight : ambient 23=right
  output : ambient 8=out
  erase : ambient 21=List.replicate (capacity w) true
  reset : ambient 22=List.replicate (capacity w+1) false
  support : ∀ i,(ambient (workSlots i)).length≤capacity w

theorem work_avoids (i : Fin 8) (j : Fin 27)
    (hj : j=8 ∨ j=9 ∨ j=19 ∨ j=20 ∨ j=21 ∨ j=22 ∨ j=23) : workSlots i≠j := by
  rcases hj with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> fin_cases i <;> decide

theorem clean_keep (w : ℕ) (ambient : Fin 27 → List Bool) (j : Fin 27)
    (hj : j=8 ∨ j=9 ∨ j=19 ∨ j=20 ∨ j=21 ∨ j=22 ∨ j=23) : clean w ambient j=ambient j := by
  simp [clean,CompetitorResidueTable.clean,cleared,
    show ¬∃ i,workSlots i=j from fun ⟨i,hi⟩ => work_avoids i j hj hi]

theorem Store.clean {w : ℕ} {left right out : List Bool} {ambient : Fin 27 → List Bool}
    (h : Store w left right out ambient) : Store w left right out (clean w ambient) := by
  constructor
  · exact (clean_keep w ambient 9 (by simp)).trans h.width
  · exact (clean_keep w ambient 20 (by simp)).trans h.widthCopy
  · exact (clean_keep w ambient 19 (by simp)).trans h.sourceLeft
  · exact (clean_keep w ambient 23 (by simp)).trans h.sourceRight
  · exact (clean_keep w ambient 8 (by simp)).trans h.output
  · exact (clean_keep w ambient 21 (by simp)).trans h.erase
  · exact (clean_keep w ambient 22 (by simp)).trans h.reset
  · intro i
    change (CompetitorResidueTable.clean w ambient (CompetitorResidueTable.workSlots i)).length≤capacity w
    rw [CompetitorResidueTable.clean_work]
    simp

theorem Store.work_update {w : ℕ} {left right out : List Bool} {ambient : Fin 27 → List Bool}
    (h : Store w left right out ambient) (i : Fin 8) (bits : List Bool) (hb : bits.length≤capacity w) :
    Store w left right out (Function.update ambient (workSlots i) bits) := by
  constructor
  · exact (Function.update_of_ne (work_avoids i 9 (by simp)).symm _ _).trans h.width
  · exact (Function.update_of_ne (work_avoids i 20 (by simp)).symm _ _).trans h.widthCopy
  · exact (Function.update_of_ne (work_avoids i 19 (by simp)).symm _ _).trans h.sourceLeft
  · exact (Function.update_of_ne (work_avoids i 23 (by simp)).symm _ _).trans h.sourceRight
  · exact (Function.update_of_ne (work_avoids i 8 (by simp)).symm _ _).trans h.output
  · exact (Function.update_of_ne (work_avoids i 21 (by simp)).symm _ _).trans h.erase
  · exact (Function.update_of_ne (work_avoids i 22 (by simp)).symm _ _).trans h.reset
  · intro j
    by_cases he : workSlots j=workSlots i
    · simp only [he,Function.update_self]
      exact hb
    · rw [Function.update_of_ne he]
      exact h.support j

theorem Store.emit {w : ℕ} {left right out : List Bool} {ambient : Fin 27 → List Bool}
    (h : Store w left right out ambient) (bits : List Bool) :
    Store w left right bits (Function.update ambient 8 bits) := by
  constructor
  · exact (Function.update_of_ne (by decide : (9 : Fin 27)≠8) _ _).trans h.width
  · exact (Function.update_of_ne (by decide : (20 : Fin 27)≠8) _ _).trans h.widthCopy
  · exact (Function.update_of_ne (by decide : (19 : Fin 27)≠8) _ _).trans h.sourceLeft
  · exact (Function.update_of_ne (by decide : (23 : Fin 27)≠8) _ _).trans h.sourceRight
  · exact Function.update_self ..
  · exact (Function.update_of_ne (by decide : (21 : Fin 27)≠8) _ _).trans h.erase
  · exact (Function.update_of_ne (by decide : (22 : Fin 27)≠8) _ _).trans h.reset
  · intro i
    rw [Function.update_of_ne (work_avoids i 8 (by simp))]
    exact h.support i

theorem clear_run (w pa pb po : ℕ) (left right out : List Bool) (ambient : Fin 27 → List Bool)
    (h : Store w left right out ambient) :
    ∃ r,runFrom clearProgram (2*capacity w+4) (cfg clearProgram.start pa pb po ambient)=some r ∧
      r.final.heads=heads pa pb po ∧ r.final.tapes=clean w ambient ∧ r.steps=2*capacity w+4 := by
  have hh : ∀ i,heads pa pb po (extend workSlots i)=0 := by
    intro i
    rw [extend_cases]
    split
    · simp [heads,work_avoids _ 19 (by simp),work_avoids _ 23 (by simp),work_avoids _ 8 (by simp)]
    · split <;> rfl
  exact CompetitorPlaneWorkspace.clear_run workSlots CompetitorResidueTable.work_injective
    (fun i => work_avoids i 21 (by simp)) (fun i => work_avoids i 22 (by simp))
    (capacity w) (heads pa pb po) ambient h.erase h.reset h.support hh

end NearCubicWires.RepairOrdinary.CompetitorBankMerge
