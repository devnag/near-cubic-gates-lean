import Proof.PCP.ProjectionFirstField

/-! Literal raw two-field hierarchy request to the selected PCP source.
The original request is retained; the next phase receives all actual fields. -/
namespace NearCubicWires.RepairSource.ProjectionNormalization.HierarchySourceInput
open LocalBitMultitape RepairOrdinary RecoveryRootRound SourceInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
def tapes (k : ℕ) := 4+HierarchySelectedSource.tapes source k
def loadSlots (k : ℕ) : Fin 4 → Fin (tapes source k) :=
  fun i => (![0,2,1,3] i : Fin 4).castAdd (HierarchySelectedSource.tapes source k)
def slots (k : ℕ) (i : Fin (HierarchySelectedSource.tapes source k)) : Fin (tapes source k) :=
  if i.val=2 then ⟨2,by dsimp [tapes]; omega⟩ else i.natAdd 4

theorem load_injective (k : ℕ) : Function.Injective (loadSlots source k) := by
  intro a b h
  have hv := congrArg Fin.val h
  fin_cases a <;> fin_cases b <;> simp [loadSlots] at hv ⊢
theorem slots_injective (k : ℕ) : Function.Injective (slots source k) := by
  intro a b h; apply Fin.ext
  have hv := congrArg Fin.val h
  dsimp [slots] at hv
  split_ifs at hv <;> dsimp at hv <;> omega

theorem selected_input (k : ℕ) (x : List Bool) : HierarchySelectedSource.input source k x=
    fun i => if i.val=2 then frame x else [] := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [HierarchySelectedSource.input,Fin.addCases_left,Fin.val_castAdd,HierarchyPrefix.input]
    rfl
  · have ht : 3 ≤ HierarchySelectedSource.base source k := by
      have h := HierarchyReduction.base_lower k
      dsimp [HierarchySelectedSource.base,HierarchyPrefix.tapes,HierarchyFramedInput.tapes,HierarchyReduction.tapes]
      omega
    simp only [HierarchySelectedSource.input,Fin.addCases_right,Fin.val_natAdd]
    rw [if_neg (by omega)]

noncomputable def loadProgram (k : ℕ) := RecoveryFocus.machine (loadSlots source k) FirstField.machine
noncomputable def sourceProgram (k CH Cpad : ℕ) (code : List Bool) :=
  RecoveryFocus.machine (slots source k) (HierarchySelectedSource.machine source k CH Cpad code)
noncomputable def machine (k CH Cpad : ℕ) (code : List Bool) :=
  Composition.machine (loadProgram source k) (sourceProgram source k CH Cpad code)
def budget (k CH Cpad : ℕ) (code x : List Bool) :=
  8*x.length+8+1+HierarchySelectedSource.budget source k CH Cpad code x
def outputTape (k : ℕ) := slots source k (HierarchySelectedSource.outputTape source k)

theorem raw_run (k CH Cpad : ℕ) (code x bound : List Bool) (hpad : k+3 ≤ Cpad) : ∃ out,
    ClockJoin.ReadyRun (machine source k CH Cpad code) (budget source k CH Cpad code x)
      (SourceHandoff.sourceTapes (frame x++frame bound)) out ∧
      HierarchySelectedSource.Fields source k CH Cpad code x
        (out ∘ slots source k ∘ HierarchySelectedSource.old source k) ∧
      out (outputTape source k)=(source.output (HierarchySelectedSource.request
        (HierarchyPadding.rawInput k CH Cpad code x))).word ∧
      out ⟨0,by dsimp [tapes]; omega⟩=frame x++frame bound := by
  let input : Fin (tapes source k) → List Bool := SourceHandoff.sourceTapes (frame x++frame bound)
  have hl := (FirstField.ready x (frame bound)).focus (loadSlots source k) (load_injective source k) input
    (by intro i; fin_cases i <;> rfl)
  let middle := install (loadSlots source k) input (FirstField.output x (frame bound))
  have hi : ∀ i,middle (slots source k i)=HierarchySelectedSource.input source k x i := by
    intro i
    rw [selected_input]
    change middle (slots source k i)=if i.val=2 then frame x else []
    by_cases hi : i.val=2
    · rw [if_pos hi]
      change install (loadSlots source k) input (FirstField.output x (frame bound)) (slots source k i)=_
      have he : slots source k i=loadSlots source k 1 := by simp [slots,hi,loadSlots]; rfl
      rw [he,install_slot _ (load_injective source k)]
      rfl
    · rw [if_neg hi]
      dsimp only [middle]
      rw [install_other _ _ _ _ (by
        intro j hj; have hv := congrArg Fin.val hj
        simp only [slots,hi,if_false,Fin.val_natAdd] at hv
        have hb : (loadSlots source k j).val<4 := by
          fin_cases j <;> simp [loadSlots]
        omega)]
      simp [input,SourceHandoff.sourceTapes,slots,hi]
  obtain ⟨b,hb,hfields,hbo⟩ := HierarchySelectedSource.selected_run source k CH Cpad code x hpad
  have hs := hb.focus (slots source k) (slots_injective source k) middle hi
  refine ⟨_,ClockJoin.join _ _ _ _ _ _ _ hl hs,?_,
    (install_slot _ (slots_injective source k) _ _ _).trans hbo,?_⟩
  · have he : install (slots source k) middle b ∘ slots source k=b :=
      funext (install_slot _ (slots_injective source k) _ _)
    change HierarchySelectedSource.Fields source k CH Cpad code x
      ((install (slots source k) middle b ∘ slots source k) ∘ HierarchySelectedSource.old source k)
    rw [he]
    exact hfields
  · rw [install_other _ _ _ _ (by
      intro i hi; have hv := congrArg Fin.val hi
      dsimp [slots] at hv
      split_ifs at hv; dsimp at hv; omega)]
    change install (loadSlots source k) input (FirstField.output x (frame bound)) (loadSlots source k 0)=_
    rw [install_slot _ (load_injective source k)]
    rfl

end
end NearCubicWires.RepairSource.ProjectionNormalization.HierarchySourceInput
