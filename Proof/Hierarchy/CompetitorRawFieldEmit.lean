import Proof.Hierarchy.CompetitorRawFrameAppend

/-! Focus the actual scalar appender into its enclosing producer. Every
unselected head is retained, including table and term-stream cursors. -/
namespace NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots {t : ℕ} (source target counter : Fin t) : Fin 3 → Fin t := ![source,target,counter]
noncomputable def program {t : ℕ} (source target counter : Fin t) :=
  RecoveryFocus.machine (slots source target counter) CompetitorFrameAppend.machine

theorem slots_injective {t : ℕ} (source target counter : Fin t)
    (hst : source≠target) (hsc : source≠counter) (htc : target≠counter) :
    Function.Injective (slots source target counter) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [slots]

theorem focused_heads {t : ℕ} (source target counter : Fin t)
    (hst : source≠target) (hsc : source≠counter) (htc : target≠counter)
    (q : Fin 4) (bits out : List Bool) (cap : ℕ) (heads : Fin t → ℕ) (ambient : Fin t → List Bool)
    (hs : heads source=0) (hc : heads counter=0) :
    (RecoveryFocus.config (slots source target counter) heads ambient
      (CompetitorRawFrameAppend.cfg q bits out cap)).heads=Function.update heads target out.length := by
  have hi := slots_injective source target counter hst hsc htc
  funext i
  by_cases h0 : i=source
  · subst i
    have hp : RecoveryFocus.pick (slots source target counter) source=some 0 :=
      RecoveryFocus.pick_slot _ hi 0
    simp [RecoveryFocus.config,hp,CompetitorRawFrameAppend.cfg,Function.update_of_ne hst,hs]
  · by_cases h1 : i=target
    · subst i
      have hp : RecoveryFocus.pick (slots source target counter) target=some 1 :=
        RecoveryFocus.pick_slot _ hi 1
      simp [RecoveryFocus.config,hp,CompetitorRawFrameAppend.cfg]
    · by_cases h2 : i=counter
      · subst i
        have hp : RecoveryFocus.pick (slots source target counter) counter=some 2 :=
          RecoveryFocus.pick_slot _ hi 2
        simp [RecoveryFocus.config,hp,CompetitorRawFrameAppend.cfg,Function.update_of_ne htc.symm,hc]
      · have hn : ¬∃ j,slots source target counter j=i := by
          rintro ⟨j,hj⟩
          fin_cases j
          · exact h0 hj.symm
          · exact h1 hj.symm
          · exact h2 hj.symm
        simp [RecoveryFocus.config,RecoveryFocus.pick,hn,Function.update_of_ne h1]

theorem field_run {t : ℕ} (source target counter : Fin t)
    (hst : source≠target) (hsc : source≠counter) (htc : target≠counter)
    (bits out : List Bool) (cap : ℕ) (heads : Fin t → ℕ) (ambient : Fin t → List Bool)
    (hs : heads source=0) (ht : heads target=out.length) (hc : heads counter=0)
    (hsource : ambient source=frame bits)
    (htarget : ambient target=out) (hcounter : ambient counter=List.replicate cap false)
    (hcap : 2*bits.length+1≤cap) :
    ∃ r : ExecutionReceipt t 4,
      runFrom (program source target counter) (4*bits.length+3)
        (RecoveryCalls.restarted (program source target counter) heads ambient)=some r ∧
      r.final.heads=Function.update heads target (out++frame bits).length ∧
      r.final.tapes=Function.update ambient target (out++frame bits) ∧ r.steps=4*bits.length+3 := by
  have hi := slots_injective source target counter hst hsc htc
  obtain ⟨base,hr,hf,hs'⟩ := CompetitorRawFrameAppend.raw_append_run bits out cap hcap
  obtain ⟨r,hrun,hfinal,hsteps⟩ := RecoveryFocus.run_config (slots source target counter) hi
    CompetitorFrameAppend.machine heads ambient _ _ base hr
  have hin : RecoveryFocus.config (slots source target counter) heads ambient (CompetitorRawFrameAppend.cfg 0 bits out cap)=
      RecoveryCalls.restarted (program source target counter) heads ambient := by
    apply configuration_ext
    · rfl
    · rw [focused_heads source target counter hst hsc htc _ _ _ _ _ _ hs hc]
      funext i
      by_cases hit : i=target
      · subst i
        simp [RecoveryCalls.restarted,ht]
      · simp [RecoveryCalls.restarted,Function.update_of_ne hit]
    · apply install_existing
      intro i
      fin_cases i
      · exact hsource
      · exact htarget
      · exact hcounter
  rw [hin] at hrun
  refine ⟨r,hrun,?_,?_,hsteps.trans hs'⟩
  · rw [hfinal,hf]
    exact focused_heads source target counter hst hsc htc _ _ _ _ _ _ hs hc
  · rw [hfinal,hf]
    change install (slots source target counter) ambient
      (CompetitorRawFrameAppend.cfg 3 bits (out++frame bits) cap).tapes=Function.update ambient target (out++frame bits)
    funext i
    by_cases hit : i=target
    · subst i
      rw [Function.update_self]
      exact install_slot _ hi _ _ 1
    · rw [Function.update_of_ne hit]
      by_cases his : i=source
      · subst i
        exact (install_slot _ hi _ _ 0).trans hsource.symm
      · by_cases hic : i=counter
        · subst i
          exact (install_slot _ hi _ _ 2).trans hcounter.symm
        · apply install_other
          intro j hj
          fin_cases j
          · exact his hj.symm
          · exact hit hj.symm
          · exact hic hj.symm

end NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit
