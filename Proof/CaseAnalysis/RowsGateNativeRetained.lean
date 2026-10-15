import Proof.CaseAnalysis.RowsGateSourceRaw

/-! Original native weights and the original support bitmap are read-only
through the SAME request writer. These ports supply circuit wire and
description guards without another canonical decoding traversal. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsGateNativeRetained
open LocalBitMultitape CloseoutRowsGateSupport
open RepairSource.RecoveryTseitinReadOnly RepairSource.ProjectionNormalization
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem repeat_body {t s : ℕ} (p : Machine t s) (accepted : Fin s → (Fin t → Bool) → Bool)
    (i : Fin t) (hp : NoWrite p i) : NoWrite (RepeatMachine.machine p accepted) (i.castAdd 1) := by
  intro q bits a ha
  cases hc : (RepeatMachine.code s).symm q with
  | inl state =>
    simp only [RepeatMachine.machine,hc] at ha
    split at ha
    · cases ha;rfl
    · obtain ⟨b,hb,he⟩ := Option.map_eq_some_iff.mp ha
      subst a
      simpa only [RepeatMachine.bodyAction,Fin.addCases_left] using hp state _ b hb
  | inr phase =>
    simp only [RepeatMachine.machine,hc] at ha
    split_ifs at ha <;> cases ha <;> rfl

theorem support_read (compressed : Bool) (i : Fin 5) (hi : i=0 ∨ i=3) :
    NoWrite (CloseoutRowsGateSupport.machine compressed) i := by
  intro q bits a ha
  simp only [CloseoutRowsGateSupport.machine] at ha
  rcases hi with rfl|rfl <;> split_ifs at ha <;> cases ha <;> rfl

theorem prepared_read (compressed : Bool) (i : Fin 5) (hi : i=0 ∨ i=3) :
    NoWrite (preparedMachine compressed) (i.castAdd 1) := by
  apply composition
  · intro q bits a ha
    simp only [bootstrap] at ha
    split at ha
    · cases ha
      rcases hi with rfl|rfl <;> rfl
    · contradiction
  · exact repeat_body _ (fun _ _ => true) i (support_read compressed i hi)

theorem prefix_read (compressed : Bool) (i : Fin 24) (hi : i=0 ∨ i=2) :
    NoWrite (CloseoutRowsGateNativePrefix.machine compressed) i := by
  apply composition
  · cases compressed
    · exact unselected (CloseoutRowsGateNativePrefix.countSlots false) _ i (by rcases hi with rfl|rfl <;> decide)
    · rcases hi with rfl|rfl
      · exact unselected (CloseoutRowsGateNativePrefix.countSlots true) _ 0 (by decide)
      · change NoWrite (RecoveryFocus.machine (CloseoutRowsGateNativePrefix.countSlots true)
          CloseoutRowsSupportCount.readyMachine) (CloseoutRowsGateNativePrefix.countSlots true 0)
        apply focus _ (CloseoutRowsGateNativePrefix.count_injective true)
        apply rewind CloseoutRowsSupportCount.machine (0 : Fin 2)
        intro q bits a ha
        simp only [CloseoutRowsSupportCount.machine] at ha
        split_ifs at ha <;> cases ha <;> rfl
  · apply unselected CloseoutRowsGateNativePrefix.headerSlots _ i
    intro j he
    have hv := congrArg Fin.val he
    rw [CloseoutRowsGateNativePrefix.header_val] at hv
    rcases hi with rfl|rfl <;> split_ifs at hv <;> omega

theorem native_read (compressed : Bool) (i : Fin 38) (hi : i=0 ∨ i=2) :
    NoWrite (CloseoutRowsGateNative.machine compressed) i := by
  apply composition
  · apply composition
    · rcases hi with rfl|rfl
      · exact embedded 14 _ (0 : Fin 24) (prefix_read compressed 0 (Or.inl rfl))
      · exact embedded 14 _ (2 : Fin 24) (prefix_read compressed 2 (Or.inr rfl))
    · rcases hi with rfl|rfl
      · exact focus CloseoutRowsGateNative.supportSlots CloseoutRowsGateNative.support_injective _ 0
          (prepared_read compressed 0 (Or.inl rfl))
      · exact focus CloseoutRowsGateNative.supportSlots CloseoutRowsGateNative.support_injective _ 3
          (prepared_read compressed 3 (Or.inr rfl))
  · exact unselected CloseoutRowsGateNative.strictSlots _ i (by rcases hi with rfl|rfl <;> decide)

theorem framed_read (compressed : Bool) (i : Fin 38) (hi : i=0 ∨ i=2) :
    NoWrite (CloseoutRowsGateNative.framedMachine compressed) (PCPPNativeFrame.old i) := by
  apply composition
  · apply embedded 2 _ (i.castAdd 2)
    exact rewind (AppendOutputLength.record (CloseoutRowsGateNative.machine compressed) 23)
      (i.castAdd 1) (CloseoutRowsGateNativeCount.record_count _ 23 i (native_read compressed i hi))
  · exact unselected (AppendOutputFrame.slots (23 : Fin 38)) _ (PCPPNativeFrame.old i)
      (by rcases hi with rfl|rfl <;> decide)

theorem retained (compressed : Bool) (fuel : ℕ) (fields : List (Bool×List Bool))
    (membership source : List Bool) (n : ℕ) (out : Fin 42 → List Bool)
    (h : ClockJoin.ReadyRun (CloseoutRowsGateNative.framedMachine compressed) fuel
      (CloseoutRowsGateNative.framedInput fields membership source n) out) :
    out 0=fields.flatMap fieldWord ∧ out 2=frame membership := by
  obtain ⟨r,hr,rt,_rh,_rs⟩ := h
  rw [←rt]
  exact ⟨run_tape _ 0 (framed_read compressed 0 (Or.inl rfl)) _ _ r hr,
    run_tape _ 2 (framed_read compressed 2 (Or.inr rfl)) _ _ r hr⟩

end NearCubicWires.RepairOrdinary.CloseoutRowsGateNativeRetained
