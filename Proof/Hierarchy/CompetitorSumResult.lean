import Proof.Hierarchy.CompetitorSumCopyback

/-! The native scalar addition is installed on the actual term-stream
layout. Its result fields and bounded support feed the paid copyback parent. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSumFold
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorReusableDecision CompetitorRationalDecision
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def nativeSlots (j : Fin 88) : Fin 94 := j.castAdd 6
noncomputable def nativeProgram := RecoveryFocus.machine nativeSlots CompetitorRationalSum.machine
structure ResultStore (b : ℕ) (a : CompetitorValidity.Estimate) (source : List Bool)
    (tapes : Fin 94 → List Bool) : Prop where
  results : ∀ j,tapes (resultSlot j)=ZeroPadding.pad (capacity b) (frame (resultBits b a j))
  wideWidth : tapes 6=List.replicate (width b) true
  shortWidth : tapes 84=List.replicate b true
  source : tapes 88=source
  loaderReset : tapes 89=List.replicate (capacity b) false
  eraseDriver : tapes 90=List.replicate (capacity b) true
  eraseReset : tapes 91=List.replicate (capacity b+1) false
  copyCounter : tapes 92=List.replicate (capacity b) false
  copyReset : tapes 93=List.replicate (capacity b) false
  support : ∀ i : Fin 88,(tapes (i.castAdd 6)).length≤capacity b

theorem native_injective : Function.Injective nativeSlots := by
  intro i j h
  have hv := congrArg (fun a : Fin 94 => a.val) h
  exact Fin.ext hv
theorem native_outside (j : Fin 88) (i : Fin 94) (hi : 88 ≤ i.val) : nativeSlots j≠i := by
  intro h
  have hv := congrArg Fin.val h
  change j.val=i.val at hv
  omega

theorem native_run (b pos : ℕ) (a c : CompetitorValidity.Estimate) (source : List Bool)
    (ambient : Fin 94 → List Bool) (h : Store b a source ambient) (ha : a.Valid b) (hc : c.Valid b) :
    ∃ r,
      runFrom nativeProgram (3000*(b+1)^2) (cfg nativeProgram.start pos (prepared b c ambient))=some r ∧
      r.final.heads=heads pos ∧
      ResultStore b (CompetitorRationalNumerators.add a c) source r.final.tapes ∧ r.steps≤3000*(b+1)^2 := by
  obtain ⟨out,hrun,hbound,h63,h64,h85,h6,h84⟩ := CompetitorReusableSum.padded_sum_run b a c ha hc
  obtain ⟨r,hr,hh,ht,hs⟩ := bounded_focused_run nativeSlots native_injective _ _ _ hrun
    (heads pos) (prepared b c ambient) (by
      intro j
      have hj : (nativeSlots j).val≠88 := fun he => native_outside j 88 (by decide) (Fin.ext he)
      simp [heads,hj]) (prepared_native b a c source ambient h)
  refine ⟨r,hr,hh,?_,hs⟩
  rw [ht]
  have houtside (i : Fin 94) (hi : 88 ≤ i.val) :
      install nativeSlots (prepared b c ambient) out i=ambient i :=
    (install_other nativeSlots _ _ i (fun j => native_outside j i hi)).trans (prepared_outside b c ambient i hi)
  constructor
  · intro j
    fin_cases j
    · exact (install_slot nativeSlots native_injective _ out 63).trans h63
    · exact (install_slot nativeSlots native_injective _ out 64).trans h64
    · exact (install_slot nativeSlots native_injective _ out 85).trans h85
  · exact (install_slot nativeSlots native_injective _ out 6).trans h6
  · exact (install_slot nativeSlots native_injective _ out 84).trans h84
  · exact (houtside 88 (by decide)).trans h.source
  · exact (houtside 89 (by decide)).trans h.loaderReset
  · exact (houtside 90 (by decide)).trans h.eraseDriver
  · exact (houtside 91 (by decide)).trans h.eraseReset
  · exact (houtside 92 (by decide)).trans h.copyCounter
  · exact (houtside 93 (by decide)).trans h.copyReset
  · intro i
    rw [show i.castAdd 6=nativeSlots i by rfl,install_slot nativeSlots native_injective]
    exact hbound i

noncomputable def restored (b : ℕ) (a : CompetitorValidity.Estimate) (ambient : Fin 94 → List Bool) :=
  copiedAll b a (cleared (capacity b) accumulatorSlot ambient)

theorem restored_field (b : ℕ) (a : CompetitorValidity.Estimate) (ambient : Fin 94 → List Bool) (j : Fin 3) :
    restored b a ambient (accumulatorSlot j)=ZeroPadding.pad (capacity b) (frame (resultBits b a j)) := by
  fin_cases j <;> simp [restored,copiedAll,copied,accumulatorSlot]

theorem restored_other (b : ℕ) (a : CompetitorValidity.Estimate) (ambient : Fin 94 → List Bool)
    (i : Fin 94) (hi : ∀ j,accumulatorSlot j≠i) : restored b a ambient i=ambient i := by
  rw [restored,copiedAll,copied_other _ 2 _ _ i (hi 2).symm,
    copied_other _ 1 _ _ i (hi 1).symm,copied_other _ 0 _ _ i (hi 0).symm]
  exact clear_keep _ _ _ i hi

theorem restored_store (b : ℕ) (a : CompetitorValidity.Estimate) (source : List Bool)
    (ambient : Fin 94 → List Bool) (h : ResultStore b a source ambient) :
    Store b a source (restored b a ambient) := by
  constructor
  · exact restored_field b a ambient 0
  · exact restored_field b a ambient 1
  · exact restored_field b a ambient 2
  · exact (restored_other _ _ _ 6 (by decide)).trans h.wideWidth
  · exact (restored_other _ _ _ 84 (by decide)).trans h.shortWidth
  · exact (restored_other _ _ _ 88 (by decide)).trans h.source
  · exact (restored_other _ _ _ 89 (by decide)).trans h.loaderReset
  · exact (restored_other _ _ _ 90 (by decide)).trans h.eraseDriver
  · exact (restored_other _ _ _ 91 (by decide)).trans h.eraseReset
  · exact (restored_other _ _ _ 92 (by decide)).trans h.copyCounter
  · exact (restored_other _ _ _ 93 (by decide)).trans h.copyReset
  · intro i
    by_cases hi : ∃ j,accumulatorSlot j=i.castAdd 6
    · obtain ⟨j,hj⟩ := hi
      rw [← hj,restored_field]
      simp only [ZeroPadding.pad_length,frame_length]
      have hc := result_cap b a j
      omega
    · rw [restored_other _ _ _ _ (fun j he => hi ⟨j,he⟩)]
      exact h.support i

noncomputable def restoreProgram := Composition.machine (clearProgram accumulatorSlot) copyAllProgram

theorem restore_run (b pos : ℕ) (a : CompetitorValidity.Estimate) (source : List Bool)
    (ambient : Fin 94 → List Bool) (h : ResultStore b a source ambient) :
    ∃ r : ExecutionReceipt 94 22,
      runFrom restoreProgram (2*capacity b+40*b+63) (cfg restoreProgram.start pos ambient)=some r ∧
      r.final.heads=heads pos ∧ Store b a source r.final.tapes ∧ r.steps≤2*capacity b+40*b+63 := by
  obtain ⟨first,hfirst,hfh,hft,hfs⟩ := clear_run accumulatorSlot (by decide) (by decide) (by decide) (by decide)
    (capacity b) pos ambient h.eraseDriver h.eraseReset (by
      intro j
      fin_cases j
      · exact h.support 0
      · exact h.support 1
      · exact h.support 4)
  let clean := cleared (capacity b) accumulatorSlot ambient
  have hs : ∀ j,clean (resultSlot j)=ZeroPadding.pad (capacity b) (frame (resultBits b a j)) := by
    intro j
    exact (clear_keep _ _ _ _ (by fin_cases j <;> decide)).trans (h.results j)
  have ht : ∀ j,clean (accumulatorSlot j)=List.replicate (capacity b) false :=
    fun j => clear_cell _ _ _ _ ⟨j,rfl⟩
  obtain ⟨last,hlast,hlh,hlt,hls⟩ := copy_all_run b pos a clean hs ht
    ((clear_keep _ _ _ 92 (by decide)).trans h.copyCounter)
    ((clear_keep _ _ _ 93 (by decide)).trans h.copyReset)
  have he : Composition.restart first.final copyAllProgram.start=cfg copyAllProgram.start pos clean := by
    apply configuration_ext
    · rfl
    · exact hfh
    · exact hft
  have hl' : runFrom copyAllProgram (40*b+58) (Composition.restart first.final copyAllProgram.start)=some last := by
    rw [he]
    exact hlast
  have hall := Composition.run_join (clearProgram accumulatorSlot) copyAllProgram _ _ _ first last hfirst hl'
  have hc : (2*capacity b+4)+1+(40*b+58)=2*capacity b+40*b+63 := by omega
  rw [hc] at hall
  refine ⟨Composition.joinedReceipt first last,hall,hlh,?_,?_⟩
  · change Store b a source last.final.tapes
    rw [hlt]
    exact restored_store b a source ambient h
  · change first.steps+1+last.steps≤_
    omega

end NearCubicWires.RepairOrdinary.CompetitorSumFold
