import Proof.Hierarchy.CompetitorPlaneWidthLoad

/-! The actual raw plane/P/N field loader in an ambient streaming program.
Only the chosen source cursor advances; every other head is retained. -/
namespace NearCubicWires.RepairOrdinary.CompetitorPlaneLoad
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots {t : ℕ} (source small width target counter : Fin t) : Fin 5 → Fin t :=
  ![source,small,width,target,counter]
noncomputable def program {t : ℕ} (source small width target counter : Fin t) :=
  RecoveryFocus.machine (slots source small width target counter) CompetitorRawCell.machine

theorem focused_heads {t : ℕ} (source small width target counter : Fin t)
    (hi : Function.Injective (slots source small width target counter))
    (state : Fin 4) (word out : List Bool) (pos b w nativeCap cap : ℕ)
    (heads : Fin t → ℕ) (ambient : Fin t → List Bool)
    (hsmall : heads small=0) (hwidth : heads width=0) (htarget : heads target=0) (hcounter : heads counter=0) :
    (RecoveryFocus.config (slots source small width target counter) heads ambient
      (widthCfg state word pos b w nativeCap cap out)).heads=Function.update heads source pos := by
  have hne (j : Fin 5) (hj : j≠0) : slots source small width target counter j≠source :=
    fun h => hj (hi h)
  funext i
  cases hp : RecoveryFocus.pick (slots source small width target counter) i with
  | none =>
    have hn : i≠source := by
      intro h
      subst i
      have hp' : RecoveryFocus.pick (slots source small width target counter) source=some 0 :=
        RecoveryFocus.pick_slot _ hi 0
      rw [hp'] at hp
      contradiction
    simp [RecoveryFocus.config,hp,Function.update_of_ne hn]
  | some j =>
    have he := RecoveryFocus.slot_of_pick (slots source small width target counter) hp
    subst i
    simp only [RecoveryFocus.config,hp]
    fin_cases j
    · simp [slots,widthCfg]
    · change 0=Function.update heads source pos small
      rw [Function.update_of_ne (show small≠source from hne 1 (by decide))]
      exact hsmall.symm
    · change 0=Function.update heads source pos width
      rw [Function.update_of_ne (show width≠source from hne 2 (by decide))]
      exact hwidth.symm
    · change 0=Function.update heads source pos target
      rw [Function.update_of_ne (show target≠source from hne 3 (by decide))]
      exact htarget.symm
    · change 0=Function.update heads source pos counter
      rw [Function.update_of_ne (show counter≠source from hne 4 (by decide))]
      exact hcounter.symm

theorem field_run {t : ℕ} (source small width target counter : Fin t)
    (hi : Function.Injective (slots source small width target counter))
    (pre suffix : List Bool) (b w count nativeCap cap : ℕ) (heads : Fin t → ℕ) (ambient : Fin t → List Bool)
    (hb : b≤w) (hc : count<2^b) (hcap : 2*w+1≤cap)
    (hs : heads source=pre.length) (hsmall : heads small=0) (hwidth : heads width=0)
    (ht : heads target=0) (hr : heads counter=0)
    (hsource : ambient source=pre++binary b count++suffix)
    (hnative : ambient small=ZeroPadding.pad nativeCap (List.replicate b true)) (hw : ambient width=List.replicate w true)
    (htarget : ambient target=List.replicate cap false) (hcounter : ambient counter=List.replicate cap false) :
    ∃ r,runFrom (program source small width target counter) (4*w+3)
        (RecoveryCalls.restarted (program source small width target counter) heads ambient)=some r ∧
      r.final.heads=Function.update heads source (pre.length+b) ∧
      r.final.tapes=Function.update ambient target (ZeroPadding.pad cap (frame (binary w count))) ∧
      r.steps=4*w+3 := by
  obtain ⟨base,hbase,hbf,hbs⟩ := width_load_run pre suffix b w count nativeCap cap hb hc hcap
  obtain ⟨r,hrun,hf,hsteps⟩ := RecoveryFocus.run_config (slots source small width target counter) hi
    CompetitorRawCell.machine heads ambient _ _ base hbase
  have hin : RecoveryFocus.config (slots source small width target counter) heads ambient
      (widthCfg 0 (pre++binary b count++suffix) pre.length b w nativeCap cap (List.replicate cap false))=
      RecoveryCalls.restarted (program source small width target counter) heads ambient := by
    apply configuration_ext
    · rfl
    · rw [focused_heads source small width target counter hi _ _ _ _ _ _ _ _ _ _ hsmall hwidth ht hr]
      change Function.update heads source pre.length=heads
      rw [← hs,Function.update_eq_self]
    · apply install_existing
      intro j
      fin_cases j
      · exact hsource
      · exact hnative
      · exact hw
      · exact htarget
      · exact hcounter
  rw [hin] at hrun
  refine ⟨r,hrun,?_,?_,hsteps.trans hbs⟩
  · rw [hf,hbf]
    exact focused_heads source small width target counter hi _ _ _ _ _ _ _ _ _ _ hsmall hwidth ht hr
  · rw [hf,hbf]
    let localTapes := (widthCfg 3 (pre++binary b count++suffix) (pre.length+b) b w nativeCap cap
      (ZeroPadding.pad cap (frame (binary w count)))).tapes
    change install (slots source small width target counter) ambient localTapes=
      Function.update ambient target (ZeroPadding.pad cap (frame (binary w count)))
    funext i
    by_cases hit : i=target
    · subst i
      rw [Function.update_self]
      exact install_slot _ hi _ _ 3
    · rw [Function.update_of_ne hit]
      cases hp : RecoveryFocus.pick (slots source small width target counter) i with
      | none => simp [install,hp]
      | some j =>
        have he := RecoveryFocus.slot_of_pick (slots source small width target counter) hp
        have hlocal : localTapes j=ambient (slots source small width target counter j) := by
          fin_cases j
          · exact hsource.symm
          · exact hnative.symm
          · exact hw.symm
          · exact False.elim (hit he.symm)
          · exact hcounter.symm
        simp only [install,hp]
        exact hlocal.trans (congrArg ambient he)

end NearCubicWires.RepairOrdinary.CompetitorPlaneLoad
