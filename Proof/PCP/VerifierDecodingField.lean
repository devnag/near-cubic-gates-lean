import Proof.PCP.VerifierDecodingFieldKernel

/-! Complete bounded field read, including physical cursor restoration and
malformed short-field rejection. Existing output storage is overwritten. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.FieldMachine
open LocalBitMultitape RepairOrdinary StablePartition.Workspace
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem rewind_first (source target : List Bool) (pos width k : ℕ) (hk : k < width) :
    step machine (reset 2 source target pos width (k+1)) =
      some (⟨3,![pos,2*k+1,k],![source,target,CompareMachine.word width]⟩ : Configuration 3 6) := by
  simp [step,machine,reset,Configuration.scanned,hk]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,action,HeadMove.apply]; omega
  · funext i; fin_cases i <;> simp [applyAction,action]

theorem rewind_second (source target : List Bool) (pos width k : ℕ) :
    step machine (⟨3,![pos,2*k+1,k],![source,target,CompareMachine.word width]⟩ : Configuration 3 6) =
      some (reset 2 source target pos width k) := by
  simp [step,machine]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,action,HeadMove.apply,reset]
  · funext i; fin_cases i <;> simp [applyAction,action,reset]

theorem rewind_stop (source target : List Bool) (pos width : ℕ) :
    step machine (reset 2 source target pos width 0) = some (finished source target pos width) := by
  simp [step,machine,reset,Configuration.scanned]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,action,HeadMove.apply,finished]
  · funext i; fin_cases i <;> simp [applyAction,action,finished]

theorem rewind_prefix (source target : List Bool) (pos width k : ℕ) (hk : k ≤ width) :
    Prefix machine (source.length+target.length+width+1) (2*k+1)
      (reset 2 source target pos width k) (finished source target pos width) := by
  induction k with
  | zero => exact Prefix.step (by simp) (by rfl) (rewind_stop source target pos width) (Prefix.refl _ (by simp))
  | succ k ih =>
    have hp := Prefix.step (by simp [Configuration.tapeCells,Fin.sum_univ_succ,CompareMachine.word]; omega)
      (by rfl : machine.halted (3 : Fin 6) = false) (rewind_second source target pos width k) (ih (by omega))
    have h := Prefix.step (by simp) (by rfl) (rewind_first source target pos width k (by omega)) hp
    convert h using 1
    omega

theorem field_run (pre bits tail backing : List Bool) (hb : backing.length ≤ 2*bits.length+1) :
    let source := pre++Streaming.marks bits++tail
    ∃ receipt : ExecutionReceipt 3 6,
      runFrom machine (4*bits.length+2) (scan 0 source pre.length bits.length 0 [] backing) = some receipt ∧
      receipt.final = finished source (frame bits) (pre.length+2*bits.length) bits.length ∧
      receipt.steps = 4*bits.length+2 ∧ receipt.peakTapeCells ≤ source.length+3*bits.length+2 := by
  let source := pre++Streaming.marks bits++tail
  have ho : overlay (frame bits) backing = frame bits := by
    simp [overlay,List.drop_eq_nil_iff.mpr (by simpa [RepairOrdinary.frame_length] using hb)]
  have hp := copy_prefix bits pre tail [] backing bits.length (by simp) hb
  dsimp only at hp
  simp only [List.length_nil,Streaming.marks,List.nil_append,Nat.zero_add] at hp
  have hs := finish_step source backing bits (pre.length+2*bits.length)
  rw [ho] at hs
  have ht := rewind_prefix source (frame bits) (pre.length+2*bits.length) bits.length bits.length (Nat.le_refl _)
  have he : source.length+(frame bits).length+bits.length+1 = source.length+3*bits.length+2 := by
    simp [RepairOrdinary.frame_length]
    omega
  rw [he] at ht
  have hj := Prefix.step (by simp [Streaming.marks_length]; omega) (by rfl) hs ht
  obtain ⟨r,hr,hf,hsteps,hpeak⟩ := (hp.trans hj).run (by rfl) (by simp [source,Streaming.marks_length]; omega)
  refine ⟨r,?_,hf,by omega,hpeak⟩
  have htime : 2*bits.length+(2*bits.length+1+1)=4*bits.length+2 := by omega
  simpa only [htime,Streaming.marks,List.flatMap_nil] using hr

theorem field_reject_run (pre bits backing : List Bool) (width : ℕ)
    (hw : bits.length < width) (hb : backing.length ≤ 2*width+1) :
    let source := pre++frame bits
    ∃ receipt : ExecutionReceipt 3 6,
      runFrom machine (2*bits.length+1) (scan 0 source pre.length width 0 [] backing) = some receipt ∧
      receipt.final = scan 5 source (pre.length+2*bits.length) width bits.length (Streaming.marks bits) backing ∧
      receipt.steps = 2*bits.length+1 ∧ receipt.peakTapeCells ≤ source.length+3*width+2 := by
  have he : Streaming.marks bits++[false] = frame bits := by
    simpa [RepairOrdinary.frame] using (Streaming.frame_append bits []).symm
  have hp := copy_prefix bits pre [false] [] backing width (by simp; omega) hb
  dsimp only at hp
  simp only [List.length_nil,Streaming.marks,List.nil_append,Nat.zero_add] at hp
  have hs := missing_step (pre++Streaming.marks bits) [] (Streaming.marks bits) backing width bits.length hw
  simp only [List.length_append,Streaming.marks_length] at hs
  rw [List.append_assoc,he] at hs
  have hsource : pre++List.flatMap (fun b => [true,b]) bits++[false] = pre++frame bits := by
    simpa only [Streaming.marks,List.append_assoc] using congrArg (fun x => pre++x) he
  rw [hsource] at hp
  have hj : Prefix machine ((pre++frame bits).length+3*width+2) 1
      (scan 0 (pre++frame bits) (pre.length+2*bits.length) width bits.length (Streaming.marks bits) backing)
      (scan 5 (pre++frame bits) (pre.length+2*bits.length) width bits.length (Streaming.marks bits) backing) :=
    Prefix.step (by simp [Streaming.marks_length]; omega) (by rfl) hs
      (Prefix.refl _ (by simp [Streaming.marks_length]; omega))
  obtain ⟨r,hr,hf,hsteps,hpeak⟩ := (hp.trans hj).run (by rfl) (by simp; omega)
  refine ⟨r,?_,hf,hsteps,hpeak⟩
  simpa only [Streaming.marks,List.flatMap_nil,Nat.zero_add] using hr

end NearCubicWires.RepairSource.VerifierDecoding.FieldMachine
