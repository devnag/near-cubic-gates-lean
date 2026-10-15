import Proof.Amplification.RecoveryLiteralDecodeState
import Proof.Amplification.RecoveryAssignmentBudget

/-! Exact bounded clause state after literal decoding and natural tag
validation, so the next literal call reuses the actual returned workspace. -/
namespace NearCubicWires.RepairOrdinary.RecoveryCheckedLiteral
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryClauseState RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def checkedState (s : State) (which : Fin 3) (word : List Bool) : State :=
  ⟨s.bits,max (resetCapacity s word) (2*(tagWord word).length+1),
    Function.update (RecoveryChildSelection.backing word s.capacity) 16
      (ZeroPadding.pad (RecoveryReusableUnpair.capacity word)
        (frame (RecoveryLiteralTag.predWord (RecoveryLiteralTag.predWord (tagWord word))))),
    (RecoveryLiteralDecode.decodedState s which word).fields,
    RecoveryLiteralTag.nonzero (tagWord word),decide (value (tagWord word)≤1)⟩

def scratchSlot (j : Fin 20) : Fin 28 :=
  (((j.castAdd 1).castAdd 1).natAdd 1).castAdd 1 |>.castAdd 4
@[simp] theorem tapes_scratch (s : State) (j : Fin 20) : s.tapes (scratchSlot j)=s.backing j := by
  simp [scratchSlot,State.tapes,State.core,RecoveryRawListStep.input,RecoveryRawListStep.tapes,RecoveryReusableUnpair.input]

theorem checked_slot (s : State) (which : Fin 3) (word : List Bool) (j : Fin 4) :
    tagOutput s word j=(checkedState s which word).tapes (tagSlots j) := by
  fin_cases j <;> simp [tagOutput,RecoveryLiteralTag.tapes,tagSlots,checkedState,State.tapes,State.core,
    RecoveryRawListStep.input,RecoveryRawListStep.tapes,RecoveryReusableUnpair.input,Fin.addCases]

theorem checked_outside (s : State) (which : Fin 3) (word : List Bool) (i : Fin 28)
    (hi : ∀ j,tagSlots j≠i) :
    (RecoveryLiteralDecode.decodedState s which word).tapes i=(checkedState s which word).tapes i := by
  refine Fin.addCases (m:=24) (n:=4) (motive:=fun k=>(∀ j,tagSlots j≠k) →
    (RecoveryLiteralDecode.decodedState s which word).tapes k=(checkedState s which word).tapes k) ?_ ?_ i hi
  · intro a ha
    refine Fin.addCases (m:=23) (n:=1) (motive:=fun k=>(∀ j,tagSlots j≠k.castAdd 4) →
      (RecoveryLiteralDecode.decodedState s which word).tapes (k.castAdd 4)=(checkedState s which word).tapes (k.castAdd 4)) ?_ ?_ a ha
    · intro b hb
      refine Fin.addCases (m:=1) (n:=22) (motive:=fun k=>(∀ j,tagSlots j≠(k.castAdd 1).castAdd 4) →
        (RecoveryLiteralDecode.decodedState s which word).tapes ((k.castAdd 1).castAdd 4)=
          (checkedState s which word).tapes ((k.castAdd 1).castAdd 4)) ?_ ?_ b hb
      · intro c _; fin_cases c; rfl
      · intro c hc
        refine Fin.addCases (m:=21) (n:=1) (motive:=fun k=>(∀ j,tagSlots j≠((k.natAdd 1).castAdd 1).castAdd 4) →
          (RecoveryLiteralDecode.decodedState s which word).tapes (((k.natAdd 1).castAdd 1).castAdd 4)=
            (checkedState s which word).tapes (((k.natAdd 1).castAdd 1).castAdd 4)) ?_ ?_ c hc
        · intro e he
          refine Fin.addCases (m:=20) (n:=1) (motive:=fun k=>(∀ j,tagSlots j≠(((k.castAdd 1).natAdd 1).castAdd 1).castAdd 4) →
            (RecoveryLiteralDecode.decodedState s which word).tapes ((((k.castAdd 1).natAdd 1).castAdd 1).castAdd 4)=
              (checkedState s which word).tapes ((((k.castAdd 1).natAdd 1).castAdd 1).castAdd 4)) ?_ ?_ e he
          · intro f hf
            change (RecoveryLiteralDecode.decodedState s which word).tapes (scratchSlot f)=
              (checkedState s which word).tapes (scratchSlot f)
            rw [tapes_scratch,tapes_scratch]
            have hn : f≠16 := by intro h; subst f; exact hf 0 rfl
            simp [checkedState,RecoveryLiteralDecode.decodedState,hn]
          · intro f _; fin_cases f; rfl
        · intro e he; fin_cases e; exact False.elim (he 3 rfl)
    · intro b hb; fin_cases b; exact False.elim (hb 1 rfl)
  · intro a ha
    refine Fin.addCases (m:=3) (n:=1) (motive:=fun k=>(∀ j,tagSlots j≠k.natAdd 24) →
      (RecoveryLiteralDecode.decodedState s which word).tapes (k.natAdd 24)=
        (checkedState s which word).tapes (k.natAdd 24)) ?_ ?_ a ha
    · intro b _
      simp only [State.tapes,Fin.addCases_right,Fin.addCases_left]
      rfl
    · intro b hb; fin_cases b; exact False.elim (hb 2 rfl)

theorem checked_output (s : State) (which : Fin 3) (word : List Bool) (hw : word.length=s.bits.length) :
    output s which word=(checkedState s which word).tapes := by
  rw [output,RecoveryLiteralDecode.decoded_output s which word hw]
  funext i
  by_cases hi : ∃ j,tagSlots j=i
  · obtain ⟨j,rfl⟩ := hi
    rw [install_slot tagSlots (by decide)]
    exact checked_slot s which word j
  · rw [install_other tagSlots _ _ _ (by intro j he; exact hi ⟨j,he⟩)]
    exact checked_outside s which word i (by intro j he; exact hi ⟨j,he⟩)

theorem checked_valid (s : State) (which : Fin 3) (word : List Bool)
    (hv : s.Valid) (hw : word.length=s.bits.length) : (checkedState s which word).Valid := by
  have hcap : RecoveryReusableUnpair.capacity word=RecoveryReusableUnpair.capacity s.bits := by
    simp [RecoveryReusableUnpair.capacity,RecoveryTapeSupport.capacity,hw]
  constructor
  · intro i
    by_cases hi : i=16
    · subst i
      have hshort : 2*word.length+1≤RecoveryReusableUnpair.capacity word := by
        have h := (RecoveryAssignment.scratch_fits word.length).2.1
        exact (by omega : 2*word.length+1≤2*word.length+3).trans h
      simp [checkedState,ZeroPadding.pad_length,RecoveryLiteralTag.predWord,RecoveryListPredecessor.result_length,
        tagWord,RecoveryFixedUnpair.word_lengths,hcap] at hshort ⊢
      exact hshort
    · have h := RecoveryChildSelection.backing_bound word s.capacity i
      simpa [checkedState,hi,hcap] using h
  · exact (RecoveryLiteralDecode.decoded_valid s which word hv hw).2

theorem state_ready (s : State) (which : Fin 3) (word : List Bool)
    (hv : s.Valid) (hw : word.length=s.bits.length) (hf : s.fields which=frame word) :
    ReadyRun (machine which) (time word) s.tapes (checkedState s which word).tapes := by
  rw [← checked_output s which word hw]
  exact literal_ready s which word hv hw hf

end NearCubicWires.RepairOrdinary.RecoveryCheckedLiteral
