import Proof.Hierarchy.CompetitorValidityErase

/-! Physical next-field loading at the retained validity-stream cursor. -/
namespace NearCubicWires.RepairOrdinary.CompetitorValidity
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorReusableDecision
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def target (j : Fin 6) : Fin 71 := j.castAdd 65
def loadSlots (j : Fin 6) : Fin 3 → Fin 71 := ![67,target j,68]
noncomputable def fieldProgram (j : Fin 6) := RecoveryFocus.machine (loadSlots j) FrameLoad.machine
def loaded (b : ℕ) (j : Fin 6) (bits : List Bool) (ambient : Fin 71 → List Bool) :=
  Function.update ambient (target j) (ZeroPadding.pad (capacity b) (frame bits))
theorem load_injective (j : Fin 6) : Function.Injective (loadSlots j) := by fin_cases j <;> decide
theorem target_ne_source (j : Fin 6) : target j≠67 := by
  intro h
  have hv := congrArg Fin.val h
  change j.val=67 at hv
  omega
theorem target_ne_counter (j : Fin 6) : target j≠68 := by
  intro h
  have hv := congrArg Fin.val h
  change j.val=68 at hv
  omega

theorem focus_heads (j : Fin 6) (q : Fin 4) (pos oldPos cap : ℕ) (source out : List Bool)
    (ambient : Fin 71 → List Bool) :
    (RecoveryFocus.config (loadSlots j) (heads oldPos) ambient (loadCfg q source pos cap out)).heads=heads pos := by
  funext i
  by_cases h0 : i=67
  · subst i
    have hp : RecoveryFocus.pick (loadSlots j) 67=some 0 :=
      RecoveryFocus.pick_slot (loadSlots j) (load_injective j) 0
    simp [RecoveryFocus.config,hp,loadCfg,heads]
  · by_cases h1 : i=target j
    · subst i
      have hj : (target j).val≠67 := fun h => target_ne_source j (Fin.ext h)
      have hp : RecoveryFocus.pick (loadSlots j) (target j)=some 1 :=
        RecoveryFocus.pick_slot (loadSlots j) (load_injective j) 1
      simp [RecoveryFocus.config,hp,loadCfg,heads,hj]
    · by_cases h2 : i=68
      · subst i
        have hp : RecoveryFocus.pick (loadSlots j) 68=some 2 :=
          RecoveryFocus.pick_slot (loadSlots j) (load_injective j) 2
        simp [RecoveryFocus.config,hp,loadCfg,heads]
      · have hn : ¬∃ k,loadSlots j k=i := by
          rintro ⟨k,hk⟩
          fin_cases k
          · exact h0 hk.symm
          · exact h1 hk.symm
          · exact h2 hk.symm
        have hv : i.val≠67 := fun h => h0 (Fin.ext h)
        simp [RecoveryFocus.config,RecoveryFocus.pick,hn,heads,hv]

theorem field_run (b : ℕ) (j : Fin 6) (pre bits suffix : List Bool) (ambient : Fin 71 → List Bool)
    (hsource : ambient 67=pre++frame bits++suffix)
    (htarget : ambient (target j)=List.replicate (capacity b) false)
    (hcounter : ambient 68=List.replicate (capacity b) false)
    (hc : 2*bits.length+1≤capacity b) :
    ∃ r : ExecutionReceipt 71 4,
      runFrom (fieldProgram j) (4*bits.length+3) (cfg (fieldProgram j).start pre.length ambient)=some r ∧
      r.final.heads=heads (pre.length+2*bits.length+1) ∧
      r.final.tapes=loaded b j bits ambient ∧ r.steps=4*bits.length+3 := by
  obtain ⟨base,hr,hf,hs⟩ := padded_load_run pre bits suffix (capacity b) hc
  obtain ⟨r,hrun,hfinal,hsteps⟩ := RecoveryFocus.run_config (loadSlots j) (load_injective j)
    FrameLoad.machine (heads pre.length) ambient _ _ base hr
  have hi : RecoveryFocus.config (loadSlots j) (heads pre.length) ambient
      (loadCfg 0 (pre++frame bits++suffix) pre.length (capacity b) (List.replicate (capacity b) false))=
      cfg (fieldProgram j).start pre.length ambient := by
    apply configuration_ext
    · rfl
    · exact focus_heads j 0 _ _ _ _ _ _
    · apply install_existing
      intro k
      fin_cases k
      · exact hsource
      · exact htarget
      · exact hcounter
  rw [hi] at hrun
  refine ⟨r,hrun,?_,?_,hsteps.trans hs⟩
  · rw [hfinal,hf]
    exact focus_heads j 3 _ _ _ _ _ _
  · rw [hfinal,hf]
    change install (loadSlots j) ambient
      (loadCfg 3 (pre++frame bits++suffix) (pre.length+2*bits.length+1) (capacity b)
        (ZeroPadding.pad (capacity b) (frame bits))).tapes=loaded b j bits ambient
    funext i
    by_cases h1 : i=target j
    · subst i
      rw [loaded,Function.update_self]
      exact install_slot (loadSlots j) (load_injective j) ambient
        (loadCfg 3 (pre++frame bits++suffix) (pre.length+2*bits.length+1) (capacity b)
          (ZeroPadding.pad (capacity b) (frame bits))).tapes 1
    · rw [loaded,Function.update_of_ne h1]
      by_cases h0 : i=67
      · subst i
        exact (install_slot (loadSlots j) (load_injective j) _ _ 0).trans hsource.symm
      · by_cases h2 : i=68
        · subst i
          exact (install_slot (loadSlots j) (load_injective j) _ _ 2).trans hcounter.symm
        · apply install_other
          intro k hk
          fin_cases k
          · exact h0 hk.symm
          · exact h1 hk.symm
          · exact h2 hk.symm

end NearCubicWires.RepairOrdinary.CompetitorValidity
