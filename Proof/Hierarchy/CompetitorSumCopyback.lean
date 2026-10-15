import Proof.Hierarchy.CompetitorSumPrepare

/-! Actual copyback of the computed numerator pair and denominator. Each
old accumulator field is cleared first; framed copies preserve result words
and restore all local heads, retaining the term-stream cursor. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSumFold
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorReusableDecision CompetitorRationalDecision
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def resultSlot : Fin 3 → Fin 94 := ![63,64,85]
def copySlots (j : Fin 3) : Fin 4 → Fin 94 := ![resultSlot j,accumulatorSlot j,92,93]
noncomputable def copyProgram (j : Fin 3) := RecoveryFocus.machine (copySlots j) copyMachine
def copied (b : ℕ) (j : Fin 3) (bits : List Bool) (ambient : Fin 94 → List Bool) :=
  Function.update ambient (accumulatorSlot j) (ZeroPadding.pad (capacity b) (frame bits))
def resultBits (b : ℕ) (a : CompetitorValidity.Estimate) : Fin 3 → List Bool :=
  ![binary (width b) a.positive,binary (width b) a.negative,binary b a.denominator]
def copiedAll (b : ℕ) (a : CompetitorValidity.Estimate) (ambient : Fin 94 → List Bool) :=
  copied b 2 (resultBits b a 2) (copied b 1 (resultBits b a 1) (copied b 0 (resultBits b a 0) ambient))
noncomputable def copyAllProgram := Composition.machine (copyProgram 0)
  (Composition.machine (copyProgram 1) (copyProgram 2))

theorem copy_injective (j : Fin 3) : Function.Injective (copySlots j) := by fin_cases j <;> decide

theorem copy_run (b pos : ℕ) (j : Fin 3) (bits : List Bool) (ambient : Fin 94 → List Bool)
    (hsource : ambient (resultSlot j)=ZeroPadding.pad (capacity b) (frame bits))
    (htarget : ambient (accumulatorSlot j)=List.replicate (capacity b) false)
    (hcounter : ambient 92=List.replicate (capacity b) false)
    (hreset : ambient 93=List.replicate (capacity b) false) (hc : 4*bits.length+3≤capacity b) :
    ∃ r : ExecutionReceipt 94 6,
      runFrom (copyProgram j) (8*bits.length+8) (cfg (copyProgram j).start pos ambient)=some r ∧
      r.final.heads=heads pos ∧ r.final.tapes=copied b j bits ambient ∧ r.steps≤8*bits.length+8 := by
  have ready := CompetitorReusableSum.padded_copy_run bits (capacity b) hc
  obtain ⟨r,hr,hh,ht,hs⟩ := bounded_focused_run (copySlots j) (copy_injective j) _ _ _ ready
    (heads pos) ambient (by intro k; fin_cases j <;> fin_cases k <;> rfl)
    (by intro k; fin_cases k; exact hsource; exact htarget; exact hcounter; exact hreset)
  refine ⟨r,hr,hh,?_,hs⟩
  rw [ht]
  funext i
  by_cases ht' : i=accumulatorSlot j
  · subst i
    rw [copied,Function.update_self]
    exact install_slot (copySlots j) (copy_injective j) _ _ 1
  · rw [copied,Function.update_of_ne ht']
    by_cases hs' : i=resultSlot j
    · subst i
      exact (install_slot (copySlots j) (copy_injective j) _ _ 0).trans hsource.symm
    · by_cases h92 : i=92
      · subst i
        exact (install_slot (copySlots j) (copy_injective j) _ _ 2).trans hcounter.symm
      · by_cases h93 : i=93
        · subst i
          exact (install_slot (copySlots j) (copy_injective j) _ _ 3).trans hreset.symm
        · apply install_other
          intro k he
          fin_cases k
          · exact hs' he.symm
          · exact ht' he.symm
          · exact h92 he.symm
          · exact h93 he.symm

theorem copied_other (b : ℕ) (j : Fin 3) (bits : List Bool) (ambient : Fin 94 → List Bool)
    (i : Fin 94) (h : i≠accumulatorSlot j) : copied b j bits ambient i=ambient i :=
  Function.update_of_ne h _ _

theorem result_cap (b : ℕ) (a : CompetitorValidity.Estimate) (j : Fin 3) :
    4*(resultBits b a j).length+3≤capacity b := by
  fin_cases j <;> simp [resultBits,width,capacity] <;> nlinarith

theorem copy_all_run (b pos : ℕ) (a : CompetitorValidity.Estimate) (ambient : Fin 94 → List Bool)
    (hsource : ∀ j,ambient (resultSlot j)=ZeroPadding.pad (capacity b) (frame (resultBits b a j)))
    (htarget : ∀ j,ambient (accumulatorSlot j)=List.replicate (capacity b) false)
    (hcounter : ambient 92=List.replicate (capacity b) false)
    (hreset : ambient 93=List.replicate (capacity b) false) :
    ∃ r : ExecutionReceipt 94 18,
      runFrom copyAllProgram (40*b+58) (cfg copyAllProgram.start pos ambient)=some r ∧
      r.final.heads=heads pos ∧ r.final.tapes=copiedAll b a ambient ∧ r.steps≤40*b+58 := by
  obtain ⟨first,hfirst,hfh,hft,hfs⟩ := copy_run b pos 0 (resultBits b a 0) ambient
    (hsource 0) (htarget 0) hcounter hreset (result_cap b a 0)
  let mid := copied b 0 (resultBits b a 0) ambient
  obtain ⟨second,hsecond,hsh,hst,hss⟩ := copy_run b pos 1 (resultBits b a 1) mid
    ((copied_other _ _ _ _ 64 (by decide)).trans (hsource 1))
    ((copied_other _ _ _ _ 1 (by decide)).trans (htarget 1))
    ((copied_other _ _ _ _ 92 (by decide)).trans hcounter)
    ((copied_other _ _ _ _ 93 (by decide)).trans hreset) (result_cap b a 1)
  let lastInput := copied b 1 (resultBits b a 1) mid
  obtain ⟨last,hlast,hlh,hlt,hls⟩ := copy_run b pos 2 (resultBits b a 2) lastInput
    ((copied_other _ _ _ _ 85 (by decide)).trans ((copied_other _ _ _ _ 85 (by decide)).trans (hsource 2)))
    ((copied_other _ _ _ _ 4 (by decide)).trans ((copied_other _ _ _ _ 4 (by decide)).trans (htarget 2)))
    ((copied_other _ _ _ _ 92 (by decide)).trans ((copied_other _ _ _ _ 92 (by decide)).trans hcounter))
    ((copied_other _ _ _ _ 93 (by decide)).trans ((copied_other _ _ _ _ 93 (by decide)).trans hreset)) (result_cap b a 2)
  have he2 : Composition.restart second.final (copyProgram 2).start=cfg (copyProgram 2).start pos lastInput := by
    apply configuration_ext
    · rfl
    · exact hsh
    · exact hst
  have hl' : runFrom (copyProgram 2) (8*(resultBits b a 2).length+8)
      (Composition.restart second.final (copyProgram 2).start)=some last := by rw [he2]; exact hlast
  have htail := Composition.run_join (copyProgram 1) (copyProgram 2) _ _ _ second last hsecond hl'
  have he1 : Composition.restart first.final (Composition.machine (copyProgram 1) (copyProgram 2)).start=
      Composition.leftConfig 6 (cfg (copyProgram 1).start pos mid) := by
    apply configuration_ext
    · rfl
    · exact hfh
    · exact hft
  have ht' : runFrom (Composition.machine (copyProgram 1) (copyProgram 2))
      ((8*(resultBits b a 1).length+8)+1+(8*(resultBits b a 2).length+8))
      (Composition.restart first.final (Composition.machine (copyProgram 1) (copyProgram 2)).start)=
      some (Composition.joinedReceipt second last) := by rw [he1]; exact htail
  have hall := Composition.run_join (copyProgram 0) (Composition.machine (copyProgram 1) (copyProgram 2))
    _ _ _ first (Composition.joinedReceipt second last) hfirst ht'
  have hc : (8*(resultBits b a 0).length+8)+1+
      ((8*(resultBits b a 1).length+8)+1+(8*(resultBits b a 2).length+8))=40*b+58 := by
    simp [resultBits,width]
    omega
  rw [hc] at hall
  refine ⟨Composition.joinedReceipt first (Composition.joinedReceipt second last),hall,hlh,hlt,?_⟩
  change first.steps+1+(second.steps+1+last.steps)≤_
  omega

end NearCubicWires.RepairOrdinary.CompetitorSumFold
