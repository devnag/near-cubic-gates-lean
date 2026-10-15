import Proof.PCP.ProjectionSourceCallABI

/-! Enclosing hierarchy padding, U-clock, length-only dimensions and one
call of the selected source. Every next input is a preceding physical field. -/
namespace NearCubicWires.RepairSource.ProjectionNormalization.HierarchySelectedSource
open LocalBitMultitape RepairOrdinary RecoveryRootRound SourceInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
def p := source.degrees.proofLog
def q := source.degrees.queries
def base (k : ℕ) := HierarchyPrefix.tapes k (p source) (q source)
def tapes (k : ℕ) := base source k+SourceCall.tapes source
def old (k : ℕ) (i : Fin (base source k)) : Fin (tapes source k) := i.castAdd (SourceCall.tapes source)
def dimension (k : ℕ) (i : Fin (DimensionsFromInput.tapes (p source) (q source))) : Fin (base source k) :=
  HierarchyPrefix.dimensionSlots k (p source) (q source) i
def rawSlot (k : ℕ) := dimension source k (DimensionsFromInput.old (p source) (q source) 12)
def clockSlot (k : ℕ) := dimension source k (DimensionsFromInput.old (p source) (q source) 29)
def slots (k : ℕ) (i : Fin (SourceCall.tapes source)) : Fin (tapes source k) :=
  if i.val=0 then old source k (rawSlot source k)
  else if i.val=1 then old source k (clockSlot source k)
  else i.natAdd (base source k)

theorem raw_val (k : ℕ) : (rawSlot source k).val=HierarchyReduction.tapes k := by
  rfl
theorem clock_val (k : ℕ) : (clockSlot source k).val=HierarchyFramedInput.tapes k+29 := by
  rfl
theorem raw_ne_clock (k : ℕ) : rawSlot source k≠clockSlot source k := by
  intro h; have hv := congrArg Fin.val h
  rw [raw_val,clock_val] at hv
  dsimp [HierarchyFramedInput.tapes] at hv
  omega

theorem old_injective (k : ℕ) : Function.Injective (old source k) := by
  intro a b h; exact Fin.ext (congrArg (fun i : Fin (tapes source k) => i.val) h)
theorem slots_injective (k : ℕ) : Function.Injective (slots source k) := by
  intro a b h; apply Fin.ext
  have hv := congrArg Fin.val h
  have hr := (rawSlot source k).isLt
  have hc := (clockSlot source k).isLt
  have hne : (rawSlot source k).val≠(clockSlot source k).val := fun h => raw_ne_clock source k (Fin.ext h)
  dsimp [slots,old] at hv
  split_ifs at hv <;> dsimp at hv <;> omega

def input (k : ℕ) (x : List Bool) : Fin (tapes source k) → List Bool :=
  Fin.addCases (HierarchyPrefix.input k (p source) (q source) x) (fun _ => [])
noncomputable def hierarchyProgram (k CH Cpad : ℕ) (code : List Bool) :=
  RecoveryFocus.machine (old source k) (HierarchyPrefix.machine k CH Cpad (p source) (q source) source.coefficient code)
noncomputable def sourceProgram (k : ℕ) := RecoveryFocus.machine (slots source k) (SourceCall.machine source)
noncomputable def machine (k CH Cpad : ℕ) (code : List Bool) :=
  Composition.machine (hierarchyProgram source k CH Cpad code) (sourceProgram source k)
def request (bits : List Bool) : InputRequest := ⟨bits.length,bits.get⟩
def budget (k CH Cpad : ℕ) (code x : List Bool) :=
  HierarchyPrefix.budget k CH Cpad (p source) (q source) source.coefficient code x+1+
    SourceCall.budget source (request (HierarchyPadding.rawInput k CH Cpad code x))
def outputTape (k : ℕ) := slots source k (SourceCall.outputTape source)

structure Fields (k CH Cpad : ℕ) (code x : List Bool) (out : Fin (base source k) → List Bool) : Prop where
  input : out (HierarchyPrefix.old k (p source) (q source)
    (HierarchyFramedInput.old k (HierarchyReduction.xTape k)))=frame x
  raw : out (rawSlot source k)=frame (HierarchyPadding.rawInput k CH Cpad code x)
  clock : out (clockSlot source k)=frame (UWhole.time (HierarchyPadding.rawInput k CH Cpad code x).length).bits
  rawR : out (dimension source k (DimensionsFromInput.rawR (p source) (q source)))=
    List.replicate (Dimensions.width source (HierarchyPadding.rawInput k CH Cpad code x).length) true
  bitsR : out (dimension source k (DimensionsFromInput.bitsR (p source) (q source)))=
    frame (Dimensions.width source (HierarchyPadding.rawInput k CH Cpad code x).length).bits
  rawQ : out (dimension source k (DimensionsFromInput.rawQ (p source) (q source)))=
    List.replicate (Dimensions.queries source (HierarchyPadding.rawInput k CH Cpad code x).length) true
  bitsQ : out (dimension source k (DimensionsFromInput.bitsQ (p source) (q source)))=
    frame (Dimensions.queries source (HierarchyPadding.rawInput k CH Cpad code x).length).bits

theorem retained (k : ℕ) (middle : Fin (base source k) → List Bool) (x : List Bool)
    (localOut : Fin (SourceCall.tapes source) → List Bool)
    (hraw : localOut (SourceCall.old source 0)=middle (rawSlot source k))
    (hclock : localOut (SourceCall.old source 1)=middle (clockSlot source k)) :
    ∀ i,install (slots source k) (install (old source k) (input source k x) middle) localOut
      (old source k i)=middle i := by
  intro i
  by_cases hr : i=rawSlot source k
  · subst i
    have he : old source k (rawSlot source k)=slots source k (SourceCall.old source 0) := rfl
    rw [he,install_slot _ (slots_injective source k)]
    exact hraw
  by_cases hc : i=clockSlot source k
  · subst i
    have he : old source k (clockSlot source k)=slots source k (SourceCall.old source 1) := rfl
    rw [he,install_slot _ (slots_injective source k)]
    exact hclock
  rw [install_other _ _ _ _ (by
    intro j hj; have hv := congrArg Fin.val hj
    have hr' : i.val≠(rawSlot source k).val := fun h => hr (Fin.ext h)
    have hc' : i.val≠(clockSlot source k).val := fun h => hc (Fin.ext h)
    dsimp [slots,old] at hv
    split_ifs at hv <;> dsimp at hv <;> omega)]
  exact install_slot _ (old_injective source k) _ _ i

theorem selected_run (k CH Cpad : ℕ) (code x : List Bool) (hpad : k+3 ≤ Cpad) : ∃ out,
    ClockJoin.ReadyRun (machine source k CH Cpad code) (budget source k CH Cpad code x)
      (input source k x) out ∧
      Fields source k CH Cpad code x (out ∘ old source k) ∧
      out (outputTape source k)=(source.output (request (HierarchyPadding.rawInput k CH Cpad code x))).word := by
  let y := HierarchyPadding.rawInput k CH Cpad code x
  obtain ⟨a,ha,hax,har,hat,haR,habR,haQ,habQ⟩ := HierarchyPrefix.prefix_run k CH Cpad code x hpad source
  have hfields : Fields source k CH Cpad code x a := ⟨hax,har,hat,haR,habR,haQ,habQ⟩
  have hp := ha.focus (old source k) (old_injective source k) (input source k x)
    (by intro i; simp [input,old,p,q])
  let middle := install (old source k) (input source k x) a
  have hi : ∀ i,middle (slots source k i)=SourceCall.input source (request y) i := by
    intro i
    rw [SourceCall.input_eq]
    change middle (slots source k i)=if i.val=0 then frame (List.ofFn (request y).2)
      else if i.val=1 then frame (UWhole.time (request y).1).bits else []
    by_cases h0 : i.val=0
    · rw [if_pos h0]
      dsimp only [middle]
      rw [slots,if_pos h0,install_slot _ (old_injective source k)]
      simpa only [request,List.ofFn_get] using hfields.raw
    by_cases h1 : i.val=1
    · rw [if_neg h0,if_pos h1]
      dsimp only [middle]
      rw [slots,if_neg h0,if_pos h1,install_slot _ (old_injective source k)]
      exact hat
    · rw [if_neg h0,if_neg h1]
      dsimp only [middle]
      rw [install_other _ _ _ _ (by
        intro j hj; have hv := congrArg Fin.val hj
        simp only [slots,h0,h1,if_false,old,Fin.val_castAdd,Fin.val_natAdd] at hv
        omega)]
      simp only [input,slots,h0,h1,if_false,Fin.addCases_right]
  obtain ⟨b,hb,hbo,hbr,hbt⟩ := SourceCall.call_run source (request y)
  have hc := hb.focus (slots source k) (slots_injective source k) middle hi
  have hbr' : b (SourceCall.old source 0)=frame y := by simpa only [request,List.ofFn_get] using hbr
  have hret := retained source k a x b (hbr'.trans hfields.raw.symm)
    (hbt.trans hfields.clock.symm)
  refine ⟨_,ClockJoin.join _ _ _ _ _ _ _ hp hc,?_,
    (install_slot _ (slots_injective source k) _ _ _).trans hbo⟩
  have he : (install (slots source k) middle b) ∘ old source k=a := funext hret
  rw [he]
  exact hfields

end
end NearCubicWires.RepairSource.ProjectionNormalization.HierarchySelectedSource
