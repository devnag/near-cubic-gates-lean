import Proof.Hierarchy.CompetitorMonomialClear

/-! The three runtime scalar widths are copied from retained physical unary
words into the cleared multiplication/normalization workspace. -/
namespace NearCubicWires.RepairOrdinary.CompetitorMonomialStream
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorReusableDecision CompetitorRationalDecision
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def widthSource : Fin 3 → Fin 88 := ![81,82,83]
def widthTarget : Fin 3 → Fin 88 := ![6,67,75]
def widthSlots (j : Fin 3) : Fin 4 → Fin 88 := ![widthSource j,86,widthTarget j,87]
def widths (b t : ℕ) : Fin 3 → ℕ := ![width b,width t,t]
noncomputable def widthProgram (j : Fin 3) := RecoveryFocus.machine (widthSlots j) ClockUnarySum.machine
def widthLoaded (t : ℕ) (j : Fin 3) (w : ℕ) (ambient : Fin 88 → List Bool) :=
  Function.update ambient (widthTarget j) (ZeroPadding.pad (capacity t) (List.replicate w true))

theorem width_run (t outPos pos : ℕ) (j : Fin 3) (w : ℕ) (ambient : Fin 88 → List Bool)
    (hs : ambient (widthSource j)=List.replicate w true)
    (hz : ambient 86=List.replicate (capacity t) false)
    (ht : ambient (widthTarget j)=List.replicate (capacity t) false)
    (hc : ambient 87=List.replicate (capacity t) false)
    (hw : w+2≤capacity t) :
    ∃ r,runFrom (widthProgram j) (2*w+6) (cfg outPos (widthProgram j).start pos ambient)=some r ∧
      r.steps≤2*w+6 ∧ r.final.heads=heads outPos pos ∧
      r.final.tapes=widthLoaded t j w ambient := by
  have hslot : Function.Injective (widthSlots j) := by fin_cases j <;> decide
  have hh : ∀ i,heads outPos pos (widthSlots j i)=0 := by
    intro i
    fin_cases j <;> fin_cases i <;> rfl
  have hin : ∀ i,ambient (widthSlots j i)=CompetitorUnaryWidthCopy.input w (capacity t) i := by
    intro i
    fin_cases i
    · exact hs
    · exact hz
    · exact ht
    · exact hc
  obtain ⟨r,hrun,hrh,hrt,hrs⟩ := bounded_focused_run (widthSlots j) hslot _ _ _
    (CompetitorUnaryWidthCopy.copy_ready w (capacity t) hw) (heads outPos pos) ambient hh hin
  refine ⟨r,hrun,hrs,hrh,?_⟩
  rw [hrt]
  funext i
  by_cases htarget : i=widthTarget j
  · subst i
    rw [widthLoaded,Function.update_self]
    exact install_slot (widthSlots j) hslot ambient (CompetitorUnaryWidthCopy.output w (capacity t)) 2
  · rw [widthLoaded,Function.update_of_ne htarget]
    by_cases hsource : i=widthSource j
    · subst i
      exact (install_slot (widthSlots j) hslot _ _ 0).trans hs.symm
    · by_cases hzero : i=86
      · subst i
        exact (install_slot (widthSlots j) hslot _ _ 1).trans hz.symm
      · by_cases hcounter : i=87
        · subst i
          exact (install_slot (widthSlots j) hslot _ _ 3).trans hc.symm
        · apply install_other
          intro a ha
          fin_cases a
          · exact hsource ha.symm
          · exact hzero ha.symm
          · exact htarget ha.symm
          · exact hcounter ha.symm

def widthStates : List (Fin 3) → ℕ
  | [] => 1
  | _::js => 5+widthStates js
noncomputable def widthsProgram : (js : List (Fin 3)) → Machine 88 (widthStates js)
  | [] => fieldHalt
  | j::js => Composition.machine (widthProgram j) (widthsProgram js)
def widthCost (b t : ℕ) : List (Fin 3) → ℕ
  | [] => 0
  | j::js => 2*widths b t j+7+widthCost b t js
def widthPlaced (b t : ℕ) : List (Fin 3) → (Fin 88 → List Bool) → (Fin 88 → List Bool)
  | [],ambient => ambient
  | j::js,ambient => widthPlaced b t js (widthLoaded t j (widths b t j) ambient)

theorem widths_run (b t outPos pos : ℕ) (js : List (Fin 3)) (hn : js.Nodup)
    (ambient : Fin 88 → List Bool)
    (hs : ∀ j∈js,ambient (widthSource j)=List.replicate (widths b t j) true)
    (ht : ∀ j∈js,ambient (widthTarget j)=List.replicate (capacity t) false)
    (hz : ambient 86=List.replicate (capacity t) false)
    (hc : ambient 87=List.replicate (capacity t) false)
    (hw : ∀ j∈js,widths b t j+2≤capacity t) :
    ∃ r,runFrom (widthsProgram js) (widthCost b t js) (cfg outPos (widthsProgram js).start pos ambient)=some r ∧
      r.steps≤widthCost b t js ∧ r.final.heads=heads outPos pos ∧ r.final.tapes=widthPlaced b t js ambient := by
  induction js generalizing ambient with
  | nil =>
    let r : ExecutionReceipt 88 1 := ⟨cfg outPos 0 pos ambient,0,(cfg outPos (0 : Fin 1) pos ambient).tapeCells⟩
    exact ⟨r,rfl,le_rfl,rfl,rfl⟩
  | cons j js ih =>
    obtain ⟨hj,hjs⟩ := List.nodup_cons.mp hn
    obtain ⟨first,hfirst,hfs,hfh,hft⟩ := width_run t outPos pos j (widths b t j) ambient
      (hs j (by simp)) hz (ht j (by simp)) hc (hw j (by simp))
    have hsource (a : Fin 3) : widthSource a≠widthTarget j := by fin_cases a <;> fin_cases j <;> decide
    have hs' : ∀ a∈js,widthLoaded t j (widths b t j) ambient (widthSource a)=List.replicate (widths b t a) true := by
      intro a ha
      rw [widthLoaded,Function.update_of_ne (hsource a)]
      exact hs a (by simp [ha])
    have ht' : ∀ a∈js,widthLoaded t j (widths b t j) ambient (widthTarget a)=List.replicate (capacity t) false := by
      intro a ha
      have hne : widthTarget a≠widthTarget j := by
        intro he
        have hin : Function.Injective widthTarget := by decide
        exact hj (hin he ▸ ha)
      rw [widthLoaded,Function.update_of_ne hne]
      exact ht a (by simp [ha])
    have hz' : widthLoaded t j (widths b t j) ambient 86=List.replicate (capacity t) false := by
      rw [widthLoaded,Function.update_of_ne (by fin_cases j <;> decide)]
      exact hz
    have hc' : widthLoaded t j (widths b t j) ambient 87=List.replicate (capacity t) false := by
      rw [widthLoaded,Function.update_of_ne (by fin_cases j <;> decide)]
      exact hc
    obtain ⟨last,hlast,hls,hlh,hlt⟩ := ih hjs (widthLoaded t j (widths b t j) ambient)
      hs' ht' hz' hc' (fun a ha => hw a (by simp [ha]))
    have he : Composition.restart first.final (widthsProgram js).start=
        cfg outPos (widthsProgram js).start pos (widthLoaded t j (widths b t j) ambient) := by
      apply configuration_ext
      · rfl
      · exact hfh
      · exact hft
    have hlast' : runFrom (widthsProgram js) (widthCost b t js)
        (Composition.restart first.final (widthsProgram js).start)=some last := by rw [he]; exact hlast
    have hall := Composition.run_join (widthProgram j) (widthsProgram js) _ _ _ first last hfirst hlast'
    have htime : (2*widths b t j+6)+1+widthCost b t js=widthCost b t (j::js) := by simp only [widthCost]
    rw [htime] at hall
    refine ⟨Composition.joinedReceipt first last,hall,?_,hlh,hlt⟩
    change first.steps+1+last.steps≤widthCost b t (j::js)
    omega

end NearCubicWires.RepairOrdinary.CompetitorMonomialStream
