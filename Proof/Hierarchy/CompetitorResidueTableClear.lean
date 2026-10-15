import Proof.Hierarchy.CompetitorResidueTableLoop

/-! The first local erase starts from genuinely blank work tapes and creates
the reusable C-cell bank and C+1-cell reset log by actual execution. -/
namespace NearCubicWires.RepairOrdinary.CompetitorResidueTable
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorPlaneWorkspace
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def eraseOutput (w : ℕ) := eraseInput (capacity w) (fun _ : Fin 8 => List.replicate (capacity w) false)
noncomputable def coldCleared (w : ℕ) (ambient : Fin 27 → List Bool) :=
  install (extend workSlots) ambient (eraseOutput w)

theorem cold_clear_run (w q : ℕ) (source : List Bool) (ambient : Fin 27 → List Bool)
    (hw : ambient 9=List.replicate w true) (hwc : ambient 20=List.replicate w true)
    (hq : ambient 4=List.replicate q true) (hs : ambient 19=source)
    (ho : ambient 8=[]) (hd : ambient 21=List.replicate (capacity w) true)
    (hr : ambient 22=[]) (hblank : ∀ i,ambient (workSlots i)=[]) :
    ClockJoin.ReadyRun clearProgram (2*capacity w+4) ambient (coldCleared w ambient) ∧
      Store w q source [] (coldCleared w ambient) := by
  let initial : Fin 10 → List Bool := Fin.addCases (m := 9) (n := 1) (motive := fun _ => List Bool)
    (Fin.addCases (m := 8) (n := 1) (motive := fun _ => List Bool)
      (fun _ => []) (fun _ => List.replicate (capacity w) true)) (fun _ => [])
  have hi : Function.Injective (extend workSlots) := extend_injective workSlots work_injective
    (fun i => work_avoids i 21 (by simp)) (fun i => work_avoids i 22 (by simp))
  have ready : ClockJoin.ReadyRun (RecoveryScratchErase.resetMachine 8) (2*capacity w+4)
      initial (eraseOutput w) := by
    obtain ⟨r,hrun,ht,hh,hsteps⟩ := RecoveryScratchErase.erase_ready (capacity w) 0
      (fun _ : Fin 8 => []) (by intro i; simp)
    exact ⟨r,hrun,by simpa only [eraseOutput,eraseInput,Nat.zero_max,List.replicate_zero] using ht,hh,hsteps.le⟩
  have hin : ∀ i,ambient (extend workSlots i)=initial i := by
    intro i
    refine Fin.addCases (m := 9) (n := 1) ?_ ?_ i
    · intro j
      refine Fin.addCases (m := 8) (n := 1) ?_ ?_ j
      · intro k
        simpa only [extend,initial,Fin.addCases_left] using hblank k
      · intro k; fin_cases k; exact hd
    · intro j; fin_cases j; exact hr
  have run := CompetitorRationalProducts.bounded_focus (extend workSlots) hi _ _ _ ready ambient hin
  refine ⟨run,?_⟩
  have keep (i : Fin 27) (h : i=4 ∨ i=8 ∨ i=9 ∨ i=19 ∨ i=20) : coldCleared w ambient i=ambient i := by
    apply install_other
    intro j
    rw [extend_cases]
    split
    · apply work_avoids
      rcases h with rfl|rfl|rfl|rfl|rfl <;> simp
    · split
      · rcases h with rfl|rfl|rfl|rfl|rfl <;> decide
      · rcases h with rfl|rfl|rfl|rfl|rfl <;> decide
  refine ⟨(keep 9 (by simp)).trans hw,(keep 20 (by simp)).trans hwc,
    (keep 4 (by simp)).trans hq,(keep 19 (by simp)).trans hs,(keep 8 (by simp)).trans ho,?_,?_,?_⟩
  · exact install_slot (extend workSlots) hi ambient (eraseOutput w) 8
  · exact install_slot (extend workSlots) hi ambient (eraseOutput w) 9
  · intro i
    have he := install_slot (extend workSlots) hi ambient (eraseOutput w) ((i.castAdd 1).castAdd 1)
    simp only [extend,eraseOutput,eraseInput,Fin.addCases_left] at he
    change coldCleared w ambient (workSlots i)=List.replicate (capacity w) false at he
    rw [he,List.length_replicate]

end NearCubicWires.RepairOrdinary.CompetitorResidueTable
