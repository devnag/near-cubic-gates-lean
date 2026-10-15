import Proof.Hierarchy.CompetitorMixedThreshold

/-! The literal fixed-threshold producer beside the retained scalar fold.
Its fresh work tapes begin blank; the global scalar cursor and loop driver
are preserved while the two physical width words are reused. -/
namespace NearCubicWires.RepairOrdinary.CompetitorThresholdAmbient
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorReusableDecision CompetitorRationalDecision CompetitorSumFold
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def native (i : Fin 94) : Fin 110 := i.castAdd 16
def project (ambient : Fin 110 → List Bool) : Fin 94 → List Bool := fun i => ambient (native i)
def constantSlots (i : Fin 17) : Fin 110 :=
  if i.val=0 then 6 else if i.val=1 then 84 else ⟨i.val+93,by omega⟩
noncomputable def constantsProgram (k : ℕ) (q : ℚ) :=
  RecoveryFocus.machine constantSlots
    (CompetitorThresholdConstants.machine k (CompetitorThresholdDecision.numerator q) q.den)

theorem native_injective : Function.Injective native := by
  intro i j h
  exact Fin.ext (congrArg (fun a : Fin 110 => a.val) h)
theorem constants_injective : Function.Injective constantSlots := by decide
theorem constants_native_other (j : Fin 17) (i : Fin 94) (h6 : i≠6) (h84 : i≠84) :
    constantSlots j≠native i := by
  intro h
  have hv := congrArg (fun a : Fin 110 => a.val) h
  change (constantSlots j).val=i.val at hv
  have hv6 : i.val≠6 := fun he => h6 (Fin.ext he)
  have hv84 : i.val≠84 := fun he => h84 (Fin.ext he)
  simp only [constantSlots] at hv
  split_ifs at hv <;> (try simp only at hv) <;> omega

theorem constants_run (b k pos : ℕ) (q : ℚ) (a : CompetitorValidity.Estimate) (source : List Bool)
    (hs : Fin 110 → ℕ) (ambient : Fin 110 → List Bool)
    (hstore : Store b a source (project ambient))
    (hheads : ∀ i,hs (native i)=heads pos i)
    (hfreshHeads : ∀ i : Fin 110,95 ≤ i.val → hs i=0)
    (hfresh : ∀ i : Fin 110,95 ≤ i.val → ambient i=[])
    (hk : k≤b) (hp : CompetitorThresholdDecision.numerator q<2^k) (hd : q.den<2^k) :
    ∃ r out,runFrom (constantsProgram k q) (CompetitorThresholdConstants.budget b k)
        (RecoveryCalls.restarted (constantsProgram k q) hs ambient)=some r ∧
      r.steps≤CompetitorThresholdConstants.budget b k ∧ r.final.heads=hs ∧ r.final.tapes=out ∧
      project out=project ambient ∧
      out 96=frame (binary (width b) (CompetitorThresholdDecision.numerator q)) ∧
      out 101=frame (binary (width b) 0) ∧ out 106=frame (binary b q.den) := by
  obtain ⟨constants,hr,h0,h1,h3,h8,h13⟩ := CompetitorThresholdConstants.constants_run b k
    (CompetitorThresholdDecision.numerator q) q.den hk hp hd
  have hh : ∀ i,hs (constantSlots i)=0 := by
    intro i
    by_cases h0' : i.val=0
    · have h := hheads 6
      simpa [constantSlots,h0',native,heads] using h
    · by_cases h1' : i.val=1
      · have h := hheads 84
        simpa [constantSlots,h0',h1',native,heads] using h
      · exact hfreshHeads _ (by simp [constantSlots,h0',h1']; omega)
  have ht : ∀ i,ambient (constantSlots i)=CompetitorThresholdConstants.input b i := by
    intro i
    by_cases h0' : i.val=0
    · simpa [constantSlots,h0',CompetitorThresholdConstants.input,project,native] using hstore.wideWidth
    · by_cases h1' : i.val=1
      · simpa [constantSlots,h0',h1',CompetitorThresholdConstants.input,project,native] using hstore.shortWidth
      · simpa [constantSlots,h0',h1',CompetitorThresholdConstants.input] using
          hfresh (constantSlots i) (by simp [constantSlots,h0',h1']; omega)
  obtain ⟨r,hrun,hrh,hrt,hrs⟩ := bounded_focused_run constantSlots constants_injective _ _ _ hr hs ambient hh ht
  let out := install constantSlots ambient constants
  refine ⟨r,out,hrun,hrs,hrh,hrt,?_,?_,?_,?_⟩
  · funext i
    by_cases h6 : i=6
    · subst i
      exact ((install_slot constantSlots constants_injective ambient constants 0).trans h0).trans hstore.wideWidth.symm
    · by_cases h84 : i=84
      · subst i
        exact ((install_slot constantSlots constants_injective ambient constants 1).trans h1).trans hstore.shortWidth.symm
      · exact install_other constantSlots ambient constants (native i) (fun j => constants_native_other j i h6 h84)
  · exact (install_slot constantSlots constants_injective ambient constants 3).trans h3
  · exact (install_slot constantSlots constants_injective ambient constants 8).trans h8
  · exact (install_slot constantSlots constants_injective ambient constants 13).trans h13

noncomputable def clearProgram := RecoveryFocus.machine native (CompetitorSumFold.clearProgram workSlot)
noncomputable def cleaned (b : ℕ) (ambient : Fin 110 → List Bool) :=
  install native ambient (cleared (capacity b) workSlot (project ambient))

theorem clear_run (b pos : ℕ) (a : CompetitorValidity.Estimate) (source : List Bool)
    (hs : Fin 110 → ℕ) (ambient : Fin 110 → List Bool)
    (hstore : Store b a source (project ambient)) (hheads : ∀ i,hs (native i)=heads pos i) :
    ∃ r,runFrom clearProgram (2*capacity b+4) (RecoveryCalls.restarted clearProgram hs ambient)=some r ∧
      r.steps=2*capacity b+4 ∧ r.final.heads=hs ∧ r.final.tapes=cleaned b ambient := by
  obtain ⟨base,hr,hh,ht,hsteps⟩ := CompetitorSumFold.clear_run workSlot work_injective
    (fun j => work_outside j 88 (by decide)) (fun j => work_outside j 90 (by decide))
    (fun j => work_outside j 91 (by decide)) (capacity b) pos (project ambient)
    hstore.eraseDriver hstore.eraseReset
    (fun j => hstore.support ⟨(workSlot j).val,(work_range j).1⟩)
  obtain ⟨r,hrun,hf,hs'⟩ := RecoveryFocus.run_config native native_injective _ hs ambient _ _ base hr
  have hi : RecoveryFocus.config native hs ambient
      (cfg (CompetitorSumFold.clearProgram workSlot).start pos (project ambient))=
      RecoveryCalls.restarted clearProgram hs ambient := by
    apply configuration_ext
    · rfl
    · funext i
      cases hp : RecoveryFocus.pick native i with
      | none => simp [RecoveryFocus.config,hp,RecoveryCalls.restarted]
      | some j =>
        have he := RecoveryFocus.slot_of_pick native hp
        simp only [RecoveryFocus.config,hp,cfg,RecoveryCalls.restarted]
        exact (hheads j).symm.trans (congrArg hs he)
    · exact install_existing native ambient (project ambient) (by intro i; rfl)
  rw [hi] at hrun
  refine ⟨r,hrun,hs'.trans hsteps,?_,?_⟩
  · rw [hf]
    funext i
    cases hp : RecoveryFocus.pick native i with
    | none => simp [RecoveryFocus.config,hp]
    | some j =>
      have he := RecoveryFocus.slot_of_pick native hp
      simp only [RecoveryFocus.config,hp,hh]
      exact (hheads j).symm.trans (congrArg hs he)
  · rw [hf]
    change install native ambient base.final.tapes=cleaned b ambient
    rw [ht]
    rfl

theorem cleaned_native (b : ℕ) (ambient : Fin 110 → List Bool) (i : Fin 94) :
    cleaned b ambient (native i)=cleared (capacity b) workSlot (project ambient) i :=
  install_slot native native_injective _ _ i
theorem cleaned_other (b : ℕ) (ambient : Fin 110 → List Bool) (i : Fin 110) (hi : 94 ≤ i.val) :
    cleaned b ambient i=ambient i := by
  apply install_other
  intro j hj
  have hv := congrArg (fun a : Fin 110 => a.val) hj
  change j.val=i.val at hv
  omega

end NearCubicWires.RepairOrdinary.CompetitorThresholdAmbient
