import Proof.CaseAnalysis.RowsGateNativeMeaning
import Proof.Amplification.RecoveryTseitinReadOnly

/-! The request writer retains the same physical weight count. Its arity
guard can therefore run after the request without counting or copying the
weights again. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsGateNativeCount
open LocalBitMultitape CloseoutRowsGateNative
open RepairSource.RecoveryTseitinReadOnly RepairSource.VerifierDecoding
open RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem repeat_count {t s : ℕ} (p : Machine t s) (accepted : Fin s → (Fin t → Bool) → Bool) :
    NoWrite (RepeatMachine.machine p accepted) ((0 : Fin 1).natAdd t) := by
  intro q bits a ha
  cases hc : (RepeatMachine.code s).symm q with
  | inl state =>
    simp only [RepeatMachine.machine,hc] at ha
    split at ha
    · cases ha;rfl
    · obtain ⟨b,_hb,he⟩ := Option.map_eq_some_iff.mp ha
      subst a
      simp only [RepeatMachine.bodyAction,Fin.addCases_right]
  | inr phase =>
    simp only [RepeatMachine.machine,hc] at ha
    split_ifs at ha <;> cases ha <;> rfl

theorem prefix_count (compressed : Bool) : NoWrite (CloseoutRowsGateNativePrefix.machine compressed) 1 := by
  apply composition
  · cases compressed
    · change NoWrite (RecoveryFocus.machine (CloseoutRowsGateNativePrefix.countSlots false)
        (UWalkUnary.machine false false)) (CloseoutRowsGateNativePrefix.countSlots false 0)
      apply focus _ (CloseoutRowsGateNativePrefix.count_injective false)
      refine rewind (UWalkUnary.raw false false) (0 : Fin 2) ?_
      intro q bits a ha
      simp only [UWalkUnary.raw] at ha
      split_ifs at ha <;> cases ha <;> rfl
    · exact unselected (CloseoutRowsGateNativePrefix.countSlots true) _ 1 (by decide)
  · apply unselected CloseoutRowsGateNativePrefix.headerSlots _ 1
    intro j he
    have hv := congrArg Fin.val he
    rw [CloseoutRowsGateNativePrefix.header_val] at hv
    split_ifs at hv <;> omega

theorem native_count (compressed : Bool) : NoWrite (CloseoutRowsGateNative.machine compressed) 1 := by
  apply composition
  · apply composition
    · exact embedded 14 _ (1 : Fin 24) (prefix_count compressed)
    · apply focus supportSlots support_injective _ 5
      apply composition
      · intro q bits a ha
        simp only [CloseoutRowsGateSupport.bootstrap] at ha
        split at ha
        · cases ha;rfl
        · contradiction
      · exact repeat_count (CloseoutRowsGateSupport.machine compressed) (fun _ _ => true)
  · exact unselected strictSlots _ 1 (by decide)

theorem record_count {t s : ℕ} (p : Machine t s) (target i : Fin t) (hp : NoWrite p i) :
    NoWrite (AppendOutputLength.record p target) (i.castAdd 1) := by
  intro state
  refine Fin.addCases (fun q bits a ha => ?_) (fun q bits a ha => ?_) state
  · simp only [AppendOutputLength.record,CursorRestore.machine,Fin.addCases_left] at ha
    split at ha
    · cases ha;rfl
    · obtain ⟨b,hb,he⟩ := Option.map_eq_some_iff.mp ha
      subst a
      simpa only [CursorRestore.recordAction,Fin.addCases_left] using hp q _ b hb
  · simp only [AppendOutputLength.record,CursorRestore.machine,Fin.addCases_right] at ha
    split_ifs at ha <;> cases ha <;> simp [MaskedReset.rewindAction,Rewind.finishAction,Fin.addCases_left]

theorem framed_count (compressed : Bool) : NoWrite (CloseoutRowsGateNative.framedMachine compressed) 1 := by
  apply composition
  · apply embedded 2 _ (1 : Fin 40)
    exact rewind (AppendOutputLength.record (CloseoutRowsGateNative.machine compressed) 23)
      (1 : Fin 39) (record_count _ 23 1 (native_count compressed))
  · exact unselected (AppendOutputFrame.slots (23 : Fin 38)) _ 1 (by decide)

theorem retained_count (compressed : Bool) (fuel : ℕ) (fields : List (Bool×List Bool))
    (membership source : List Bool) (n : ℕ) (out : Fin 42 → List Bool)
    (h : ClockJoin.ReadyRun (CloseoutRowsGateNative.framedMachine compressed) fuel
      (framedInput fields membership source n) out) : out 1=CompareMachine.word fields.length := by
  obtain ⟨r,hr,rt,_rh,_rs⟩ := h
  rw [←rt]
  exact run_tape _ 1 (framed_count compressed) _ _ r hr

end NearCubicWires.RepairOrdinary.CloseoutRowsGateNativeCount
