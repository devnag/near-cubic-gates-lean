import Proof.Hierarchy.CompetitorSumFields
import Proof.Hierarchy.CompetitorSumWidth

/-! The actual term-stream producer for one rational-fold addition. The
retained accumulator is preserved while the old workspace is cleared and
the next three signed-rational fields are loaded at the global cursor. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSumFold
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorReusableDecision CompetitorRationalDecision
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure Store (b : ℕ) (a : CompetitorValidity.Estimate) (source : List Bool)
    (tapes : Fin 94 → List Bool) : Prop where
  positive : tapes 0=ZeroPadding.pad (capacity b) (frame (binary (width b) a.positive))
  negative : tapes 1=ZeroPadding.pad (capacity b) (frame (binary (width b) a.negative))
  denominator : tapes 4=ZeroPadding.pad (capacity b) (frame (binary b a.denominator))
  wideWidth : tapes 6=List.replicate (width b) true
  shortWidth : tapes 84=List.replicate b true
  source : tapes 88=source
  loaderReset : tapes 89=List.replicate (capacity b) false
  eraseDriver : tapes 90=List.replicate (capacity b) true
  eraseReset : tapes 91=List.replicate (capacity b+1) false
  copyCounter : tapes 92=List.replicate (capacity b) false
  copyReset : tapes 93=List.replicate (capacity b) false
  support : ∀ i : Fin 88,(tapes (i.castAdd 6)).length≤capacity b

def termTargets : List (Fin 6) := [2,3,5]
def termFields (b : ℕ) (c : CompetitorValidity.Estimate) : Fin 6 → List Bool :=
  ![[],[],binary (width b) c.negative,binary (width b) c.positive,[],binary b c.denominator]
def termWord (b : ℕ) (c : CompetitorValidity.Estimate) := fieldStream (termFields b c) termTargets
def termLoaded (b : ℕ) (c : CompetitorValidity.Estimate) := placed b (termFields b c) termTargets
noncomputable def termProgram := fieldsProgram termTargets
noncomputable def prepareProgram := Composition.machine (clearProgram workSlot) termProgram
noncomputable def prepared (b : ℕ) (c : CompetitorValidity.Estimate) (ambient : Fin 94 → List Bool) :=
  termLoaded b c (cleared (capacity b) workSlot ambient)
def preparedValues (b : ℕ) (a c : CompetitorValidity.Estimate) (i : Fin 94) : List Bool :=
  if i.val=0 then ZeroPadding.pad (capacity b) (frame (binary (width b) a.positive))
  else if i.val=1 then ZeroPadding.pad (capacity b) (frame (binary (width b) a.negative))
  else if i.val=2 then ZeroPadding.pad (capacity b) (frame (binary (width b) c.negative))
  else if i.val=3 then ZeroPadding.pad (capacity b) (frame (binary (width b) c.positive))
  else if i.val=4 then ZeroPadding.pad (capacity b) (frame (binary b a.denominator))
  else if i.val=5 then ZeroPadding.pad (capacity b) (frame (binary b c.denominator))
  else if i.val=6 then List.replicate (width b) true
  else if i.val=84 then List.replicate b true else List.replicate (capacity b) false

theorem termLoaded_cases (b : ℕ) (c : CompetitorValidity.Estimate) (ambient : Fin 94 → List Bool) (i : Fin 94) :
    termLoaded b c ambient i=
      if i.val=5 then ZeroPadding.pad (capacity b) (frame (binary b c.denominator))
      else if i.val=3 then ZeroPadding.pad (capacity b) (frame (binary (width b) c.positive))
      else if i.val=2 then ZeroPadding.pad (capacity b) (frame (binary (width b) c.negative)) else ambient i := by
  simp [termLoaded,placed,termTargets,loaded,termFields,target,Function.update_apply,Fin.ext_iff]

theorem clear_keep {k : ℕ} (cap : ℕ) (slot : Fin k → Fin 94) (ambient : Fin 94 → List Bool)
    (i : Fin 94) (hi : ∀ j,slot j≠i) : cleared cap slot ambient i=ambient i := by
  simp only [cleared,show ¬∃ j,slot j=i from fun ⟨j,hj⟩ => hi j hj,if_false]

theorem clear_cell {k : ℕ} (cap : ℕ) (slot : Fin k → Fin 94) (ambient : Fin 94 → List Bool)
    (i : Fin 94) (hi : ∃ j,slot j=i) : cleared cap slot ambient i=List.replicate cap false := by
  simp only [cleared,hi,if_true]

theorem work_outside (j : Fin 83) (i : Fin 94) (hi : 88 ≤ i.val) : workSlot j≠i := by
  intro h
  have hv := congrArg Fin.val h
  have hh := (work_range j).1
  omega

theorem prepared_outside (b : ℕ) (c : CompetitorValidity.Estimate) (ambient : Fin 94 → List Bool)
    (i : Fin 94) (hi : 88 ≤ i.val) : prepared b c ambient i=ambient i := by
  rw [prepared,termLoaded_cases]
  simp only [show i.val≠5 by omega,show i.val≠3 by omega,show i.val≠2 by omega,if_false]
  exact clear_keep _ _ _ i (fun j => work_outside j i hi)

theorem prepared_native (b : ℕ) (a c : CompetitorValidity.Estimate) (source : List Bool)
    (ambient : Fin 94 → List Bool) (h : Store b a source ambient) (i : Fin 88) :
    prepared b c ambient (i.castAdd 6)=CompetitorReusableSum.paddedInput b a c i := by
  have hp : CompetitorReusableSum.paddedInput b a c i=preparedValues b a c (i.castAdd 6) := by
    fin_cases i <;> first | rfl | exact ZeroPadding.pad_zero _
  rw [hp,prepared,termLoaded_cases]
  by_cases h0 : i=0
  · subst i
    simpa [preparedValues,clear_keep _ workSlot ambient 0 (fun j => (work_range j).2.1)] using h.positive
  · by_cases h1 : i=1
    · subst i
      simpa [preparedValues,clear_keep _ workSlot ambient 1 (fun j => (work_range j).2.2.1)] using h.negative
    · by_cases h4 : i=4
      · subst i
        simpa [preparedValues,clear_keep _ workSlot ambient 4 (fun j => (work_range j).2.2.2.1)] using h.denominator
      · by_cases h6 : i=6
        · subst i
          simpa [preparedValues,clear_keep _ workSlot ambient 6 (fun j => (work_range j).2.2.2.2.1)] using h.wideWidth
        · by_cases h84 : i=84
          · subst i
            simpa [preparedValues,clear_keep _ workSlot ambient 84 (fun j => (work_range j).2.2.2.2.2)] using h.shortWidth
          · have hz := clear_cell (capacity b) workSlot ambient (i.castAdd 6) (work_image i h0 h1 h4 h6 h84)
            have hv0 : i.val≠0 := fun he => h0 (Fin.ext he)
            have hv1 : i.val≠1 := fun he => h1 (Fin.ext he)
            have hv4 : i.val≠4 := fun he => h4 (Fin.ext he)
            have hv6 : i.val≠6 := fun he => h6 (Fin.ext he)
            have hv84 : i.val≠84 := fun he => h84 (Fin.ext he)
            simp only [Fin.val_castAdd,preparedValues,hv0,hv1,hv4,hv6,hv84,if_false,hz]
            split_ifs <;> (try congr 1) <;> omega

theorem term_length (b : ℕ) (c : CompetitorValidity.Estimate) : (termWord b c).length=10*b+11 := by
  simp [termWord,fieldStream,termTargets,termFields,width]
  omega
theorem term_cost (b : ℕ) (c : CompetitorValidity.Estimate) : fieldCost (termFields b c) termTargets=20*b+28 := by
  simp [fieldCost,termTargets,termFields,width]
  omega

theorem prepare_run (b : ℕ) (a c : CompetitorValidity.Estimate) (pre suffix : List Bool)
    (ambient : Fin 94 → List Bool) (h : Store b a (pre++termWord b c++suffix) ambient) :
    ∃ r : ExecutionReceipt 94 (4+fieldStates termTargets),
      runFrom prepareProgram (2*capacity b+20*b+33)
        (cfg prepareProgram.start pre.length ambient)=some r ∧
      r.final.heads=heads (pre.length+(termWord b c).length) ∧
      r.final.tapes=prepared b c ambient ∧ r.steps=2*capacity b+20*b+33 := by
  obtain ⟨first,hfirst,hfh,hft,hfs⟩ := clear_run workSlot work_injective
    (fun j => work_outside j 88 (by decide)) (fun j => work_outside j 90 (by decide))
    (fun j => work_outside j 91 (by decide)) (capacity b) pre.length ambient h.eraseDriver h.eraseReset
    (fun j => by
      have hj := (work_range j).1
      have hs := h.support ⟨(workSlot j).val,hj⟩
      exact hs)
  let clean := cleared (capacity b) workSlot ambient
  have hsource : clean 88=pre++fieldStream (termFields b c) termTargets++suffix :=
    (clear_keep _ _ _ 88 (fun j => work_outside j 88 (by decide))).trans h.source
  have hblank : ∀ j∈termTargets,clean (target j)=List.replicate (capacity b) false := by
    intro j hj
    simp only [termTargets,List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with hj | hj | hj <;> subst j
    · exact clear_cell _ _ _ 2 ⟨0,rfl⟩
    · exact clear_cell _ _ _ 3 ⟨1,rfl⟩
    · exact clear_cell _ _ _ 5 ⟨2,rfl⟩
  have hcounter : clean 89=List.replicate (capacity b) false :=
    (clear_keep _ _ _ 89 (fun j => work_outside j 89 (by decide))).trans h.loaderReset
  have hcap : ∀ j∈termTargets,2*(termFields b c j).length+1≤capacity b := by
    intro j hj
    simp only [termTargets,List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with hj | hj | hj <;> subst j
    all_goals simp [termFields,width,capacity]; nlinarith
  obtain ⟨last,hlast,hlh,hlt,hls⟩ := fields_run b (termFields b c) termTargets (by decide)
    pre suffix clean hsource hblank hcounter hcap
  have he : Composition.restart first.final termProgram.start=cfg termProgram.start pre.length clean := by
    apply configuration_ext
    · rfl
    · exact hfh
    · exact hft
  have hlast' : runFrom termProgram (fieldCost (termFields b c) termTargets)
      (Composition.restart first.final termProgram.start)=some last := by rw [he]; exact hlast
  have hall := Composition.run_join (clearProgram workSlot) termProgram _ _ _ first last hfirst hlast'
  have ht : (2*capacity b+4)+1+fieldCost (termFields b c) termTargets=2*capacity b+20*b+33 := by
    rw [term_cost]
    omega
  rw [ht] at hall
  refine ⟨Composition.joinedReceipt first last,hall,hlh,hlt,?_⟩
  change first.steps+1+last.steps=_
  rw [hfs,hls]
  exact ht

end NearCubicWires.RepairOrdinary.CompetitorSumFold
