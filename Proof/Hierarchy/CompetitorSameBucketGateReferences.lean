import Proof.Hierarchy.CompetitorSameBucketReferences

/-! Retained zero-grid reference fields of the same cold all-gate machine.
Only its scalar-capacity tape is selected by the gate; the returned State
preserves it. All other required references lie outside the gate focus. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketColdGate
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open MatrixScoreBatch (Request)
open CompetitorSameBucketColdNativeLayout (slots entry ambient)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

private theorem pick_reference (j : Fin 7) (hj : j≠6) :
    RecoveryFocus.pick slots ((CompetitorSameBucketColdReferences.slots j).castAdd 44)=none := by
  fin_cases j <;> first | contradiction | decide

private theorem no_reference_advance (j : Fin 7) :
    ¬CompetitorSameBucketColdNativeLayout.advances ((CompetitorSameBucketColdReferences.slots j).castAdd 44) := by
  fin_cases j <;> decide

private theorem copied_reference (r : Request) (w : ℕ) (t : Fin 398 → List Bool)
    (bt : ∀ j,t (CompetitorSameBucketColdRetained.slots j)=CompetitorSameBucketColdRetained.values r w j)
    (rt : ∀ j,t (CompetitorSameBucketColdReferences.slots j)=CompetitorSameBucketColdReferences.values r j)
    (j : Fin 7) : CompetitorSameBucketColdNativeFields.copiedTapes r t
      ((CompetitorSameBucketColdReferences.slots j).castAdd 44)=CompetitorSameBucketColdReferences.values r j := by
  have old:=(CompetitorSameBucketColdAllocate.output_old _ _ t (bt 9) (bt 13)
    (CompetitorSameBucketColdReferences.slots j)).trans (rt j)
  fin_cases j <;> simpa [CompetitorSameBucketColdNativeFields.copiedTapes,CompetitorSameBucketColdCopies.output,
    CompetitorSameBucketColdCopyFields.copied,CompetitorSameBucketColdCopyFields.targetSlot,
    CompetitorSameBucketColdReferences.slots] using old

theorem reference_run (r : Request) (w : ℕ) : ∃ actual,
    run machine (budget r) (input r w)=some actual ∧
    actual.final.tapes 0=MatrixScoreBatch.physicalInput r ∧ actual.final.heads 0=0 ∧
    actual.final.tapes 1=List.replicate w true ∧ actual.final.heads 1=0 ∧
    actual.final.tapes 2=CompetitorSameBucketGateNative.output r ∧
    actual.final.heads 2=(CompetitorSameBucketGateNative.output r).length ∧
    (∀ j,actual.final.tapes ((CompetitorSameBucketColdReferences.slots j).castAdd 44)=CompetitorSameBucketColdReferences.values r j) ∧
    (∀ j,actual.final.heads ((CompetitorSameBucketColdReferences.slots j).castAdd 44)=0) ∧
    actual.steps≤budget r := by
  obtain ⟨base,workspace,initialized,hbase,hworkspace,hi,ih,it,allocated,wt,wh,fresh,ist⟩:=
    CompetitorSameBucketColdInitialized.initialized_run r w
  obtain ⟨bt,bh⟩:=CompetitorSameBucketColdRetained.retained r w base hbase
  obtain ⟨referencesT,referencesH⟩:=CompetitorSameBucketColdReferences.fields r w base hbase
  have itapes : initialized.final.tapes=CompetitorSameBucketColdNativeFields.copiedTapes r base.final.tapes := by
    rw [it,allocated]
    rfl
  have ihOld (j : Fin 17) : initialized.final.heads ((CompetitorSameBucketColdRetained.slots j).castAdd 44)=0 := by
    rw [ih]
    exact (wh _).trans (bh j)
  have ihFresh (j : Fin 44) : initialized.final.heads (j.natAdd 398)=0 := by rw [ih]; exact fresh j
  obtain ⟨advanced,ha,af,ast⟩:=CompetitorSameBucketColdNativeLayout.advance_run initialized.final
  have selectedH : ∀ j,advanced.final.heads (slots j)=(entry r).heads j := by
    rw [af]
    exact CompetitorSameBucketColdNativeFields.selected_heads r initialized.final ihOld ihFresh
  have selectedT : ∀ j,advanced.final.tapes (slots j)=(entry r).tapes j := by
    rw [af]
    change ∀ j,initialized.final.tapes (slots j)=(entry r).tapes j
    rw [itapes]
    exact CompetitorSameBucketColdNativeFields.selected_tapes r w base.final.tapes bt
  have capFits:=CompetitorSameBucketBucketBody.scalar_capacity_fits r
  obtain ⟨localRun,next,nextCoefficient,nextCached,nextRight,nextPacket,hl,ls,lf,state,_,_⟩:=
    CompetitorSameBucketGateNative.native_run r (CompetitorSameBucketBucketBody.scalarCapacity r) 0 none
      (List.replicate (MatrixScoreReusableRanks.D r) false) [] (ambient r) (List.replicate (MatrixScoreReusableRanks.D r) false)
      capFits.1 capFits.2 (by simp [ambient]) (by simp) (CompetitorSameBucketColdNativeLayout.initial_state r)
  have focusedInput : RecoveryFocus.config slots advanced.final.heads advanced.final.tapes (entry r)=
      Composition.restart advanced.final gate.start := WilliamsSourceCrop.focus_same slots _ _ selectedH selectedT
  obtain ⟨focused,hf,ff,fs⟩:=RecoveryFocus.run_config slots CompetitorSameBucketColdNativeLayout.slots_injective
    CompetitorSameBucketGateLoop.machine advanced.final.heads advanced.final.tapes _ (entry r) localRun hl
  rw [focusedInput] at hf
  have joinedTail:=Composition.run_join CompetitorSameBucketColdNativeLayout.advance gate _ _ _ advanced focused ha hf
  have tailInput : Composition.leftConfig _ (Composition.restart initialized.final CompetitorSameBucketColdNativeLayout.advance.start)=
      Composition.restart initialized.final tail.start := rfl
  rw [tailInput] at joinedTail
  have joined:=Composition.run_join CompetitorSameBucketColdInitialized.machine tail _ _ _ initialized
    (Composition.joinedReceipt advanced focused) hi joinedTail
  have nativeOut : localRun.final.tapes 34=CompetitorSameBucketGateNative.output r := by
    rw [lf,CompetitorSameBucketGateNative.cfg_tapes]
    exact state.fields 6
  have nativeHead : localRun.final.heads 34=(CompetitorSameBucketGateNative.output r).length := by
    rw [lf,CompetitorSameBucketGateNative.cfg_heads]
    rfl
  have oldT (j : Fin 17) : initialized.final.tapes ((CompetitorSameBucketColdRetained.slots j).castAdd 44)=
      CompetitorSameBucketColdRetained.values r w j := by
    rw [itapes]
    exact CompetitorSameBucketColdNativeFields.old_field r w base.final.tapes bt j
  have refT (j : Fin 7) : initialized.final.tapes ((CompetitorSameBucketColdReferences.slots j).castAdd 44)=
      CompetitorSameBucketColdReferences.values r j := by
    rw [itapes]
    exact copied_reference r w base.final.tapes bt referencesT j
  have refH (j : Fin 7) : initialized.final.heads ((CompetitorSameBucketColdReferences.slots j).castAdd 44)=0 := by
    rw [ih]
    exact (wh _).trans (referencesH j)
  have pick0 : RecoveryFocus.pick slots (0 : Fin 442)=none := by decide
  have pick1 : RecoveryFocus.pick slots (1 : Fin 442)=none := by decide
  refine ⟨Composition.joinedReceipt initialized (Composition.joinedReceipt advanced focused),joined,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · change focused.final.tapes 0=_
    rw [ff]
    simp only [RecoveryFocus.config,pick0,af,CompetitorSameBucketColdNativeLayout.advanced]
    exact oldT 0
  · change focused.final.heads 0=0
    rw [ff]
    simp only [RecoveryFocus.config,pick0,af,CompetitorSameBucketColdNativeLayout.advanced]
    simpa [CompetitorSameBucketColdNativeLayout.advances,CompetitorSameBucketColdRetained.slots] using ihOld 0
  · change focused.final.tapes 1=_
    rw [ff]
    simp only [RecoveryFocus.config,pick1,af,CompetitorSameBucketColdNativeLayout.advanced]
    exact oldT 1
  · change focused.final.heads 1=0
    rw [ff]
    simp only [RecoveryFocus.config,pick1,af,CompetitorSameBucketColdNativeLayout.advanced]
    simpa [CompetitorSameBucketColdNativeLayout.advances,CompetitorSameBucketColdRetained.slots] using ihOld 1
  · change focused.final.tapes (slots 34)=_
    rw [ff]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots CompetitorSameBucketColdNativeLayout.slots_injective]
    exact nativeOut
  · change focused.final.heads (slots 34)=_
    rw [ff]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots CompetitorSameBucketColdNativeLayout.slots_injective]
    exact nativeHead
  · intro j
    change focused.final.tapes ((CompetitorSameBucketColdReferences.slots j).castAdd 44)=_
    by_cases hj : j=6
    · subst j
      change focused.final.tapes (slots 36)=_
      rw [ff]
      simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots CompetitorSameBucketColdNativeLayout.slots_injective]
      rw [lf,CompetitorSameBucketGateNative.cfg_tapes]
      exact state.store.driver
    · have hp := pick_reference j hj
      rw [ff]
      simp only [RecoveryFocus.config,hp,af,CompetitorSameBucketColdNativeLayout.advanced]
      exact refT j
  · intro j
    change focused.final.heads ((CompetitorSameBucketColdReferences.slots j).castAdd 44)=0
    by_cases hj : j=6
    · subst j
      change focused.final.heads (slots 36)=0
      rw [ff]
      simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots CompetitorSameBucketColdNativeLayout.slots_injective]
      rw [lf,CompetitorSameBucketGateNative.cfg_heads]
      rfl
    · have hp := pick_reference j hj
      have noadvance := no_reference_advance j
      rw [ff]
      simp only [RecoveryFocus.config,hp,af,CompetitorSameBucketColdNativeLayout.advanced,noadvance,ite_false]
      exact refH j
  · change initialized.steps+1+(advanced.steps+1+focused.steps)≤budget r
    rw [ast,fs]
    unfold budget
    omega

end NearCubicWires.RepairOrdinary.CompetitorSameBucketColdGate
