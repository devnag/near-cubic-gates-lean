import Proof.Hierarchy.CompetitorPlanePaddedArithmetic
import Proof.Hierarchy.CompetitorRawScalarPaddedField

/-! One aligned plane cell's actual multiply/add and two-field raw append.
The global P/N stream is excluded from arithmetic workspace and clearing. -/
namespace NearCubicWires.RepairOrdinary.CompetitorPlane
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def native (i : Fin 17) : Fin 18 := i.castAdd 1
def kernelHeads (output : List Bool) : Fin 18 → ℕ := fun i => if i.val=17 then output.length else 0
def kernelInput (w count positive negative : ℕ) (bits output : List Bool) : Fin 18 → List Bool :=
  Fin.addCases (m := 17) (n := 1) (motive := fun _ => List Bool)
    (paddedArithmeticInput w count positive negative bits) (fun _ => output)
def pairWord (w positive negative : ℕ) := binary w positive++binary w negative
def nextWord (sign : Bool) (w positive negative count : ℕ) (bits : List Bool) :=
  pairWord w (nextPositive sign positive count bits) (nextNegative sign negative count bits)
noncomputable def kernelArithmetic (sign : Bool) := RecoveryFocus.machine native (arithmeticProgram sign)
noncomputable def positiveEmit (sign : Bool) := CompetitorRawScalarPaddedField.program (native (positiveTape sign)) 17 12
noncomputable def negativeEmit (sign : Bool) := CompetitorRawScalarPaddedField.program (native (negativeTape sign)) 17 12
noncomputable def kernelEmit (sign : Bool) := Composition.machine (positiveEmit sign) (negativeEmit sign)
noncomputable def kernelProgram (sign : Bool) := Composition.machine (kernelArithmetic sign) (kernelEmit sign)
def kernelBudget (w : ℕ) (bits : List Bool) := arithmeticBudget w bits+8*w+8

theorem native_injective : Function.Injective native := by
  intro i j h
  exact Fin.ext (congrArg (fun a : Fin 18 => a.val) h)
theorem native_avoids (i : Fin 17) : native i≠17 := by
  intro h
  have hv := congrArg (fun a : Fin 18 => a.val) h
  change i.val=17 at hv
  omega

theorem updated_heads (out bits : List Bool) :
    Function.update (kernelHeads out) (17 : Fin 18) (out++bits).length=kernelHeads (out++bits) := by
  funext i
  by_cases hi : i=17
  · subst i; simp [kernelHeads]
  · have hv : i.val≠17 := fun h => hi (Fin.ext h)
    simp [Function.update_of_ne hi,kernelHeads,hv]

theorem kernel_run (sign : Bool) (w count positive negative : ℕ) (bits pre : List Bool)
    (hb : bits.length≤w) (hshift : count*2^bits.length<2^w)
    (hadd : count*value bits+(if sign then negative else positive)<2^w) :
    ∃ r out,runFrom (kernelProgram sign) (kernelBudget w bits)
        (RecoveryCalls.restarted (kernelProgram sign) (kernelHeads pre)
          (kernelInput w count positive negative bits pre))=some r ∧
      r.steps≤kernelBudget w bits ∧
      r.final.heads=kernelHeads (pre++nextWord sign w positive negative count bits) ∧
      r.final.tapes=out ∧ out 17=pre++nextWord sign w positive negative count bits ∧
      out 0=frame bits ∧ out 9=List.replicate w true ∧
      (∀ i : Fin 17,(out (native i)).length≤capacity w) := by
  obtain ⟨produced,ready,hp,hn,h0,h9,h12,hsupp⟩ := padded_arithmetic_run sign w count positive negative bits hb hshift hadd
  obtain ⟨first,hfirst,hfh,hft,hfs⟩ := CompetitorReusableDecision.bounded_focused_run native native_injective _ _ _ ready
    (kernelHeads pre) (kernelInput w count positive negative bits pre)
    (by intro i; simp [kernelHeads,native,show i.val≠17 by omega])
    (by intro i; simp [kernelInput,native])
  let middle := install native (kernelInput w count positive negative bits pre) produced
  let pbits := binary w (nextPositive sign positive count bits)
  let nbits := binary w (nextNegative sign negative count bits)
  have hp' : middle (native (positiveTape sign))=ZeroPadding.pad (capacity w) (frame pbits) :=
    (install_slot native native_injective _ _ _).trans hp
  have hn' : middle (native (negativeTape sign))=ZeroPadding.pad (capacity w) (frame nbits) :=
    (install_slot native native_injective _ _ _).trans hn
  have hm17 : middle 17=pre := install_other native _ _ 17 native_avoids
  have hm12 : middle 12=List.replicate (capacity w) false := (install_slot native native_injective _ _ 12).trans h12
  have hcap : 2*w+1≤capacity w := by unfold capacity; nlinarith
  obtain ⟨emitP,hemitP,hph,hpt,hps⟩ := CompetitorRawScalarPaddedField.field_run
    (native (positiveTape sign)) (17 : Fin 18) 12 (native_avoids _)
    (by cases sign <;> decide) (by decide) pbits pre (capacity w) (kernelHeads pre) middle
    (by cases sign <;> rfl) rfl rfl hp' hm17 hm12 (by simpa [pbits] using hcap)
  let middleP := Function.update middle 17 (pre++pbits)
  have hpheads : emitP.final.heads=kernelHeads (pre++pbits) := hph.trans (updated_heads pre pbits)
  obtain ⟨emitN,hemitN,hnh,hnt,hns⟩ := CompetitorRawScalarPaddedField.field_run
    (native (negativeTape sign)) (17 : Fin 18) 12 (native_avoids _)
    (by cases sign <;> decide) (by decide) nbits (pre++pbits) (capacity w)
    (kernelHeads (pre++pbits)) middleP (by cases sign <;> rfl) rfl rfl
    ((Function.update_of_ne (native_avoids _) _ _).trans hn') (Function.update_self ..)
    ((Function.update_of_ne (by decide : (12 : Fin 18)≠17) _ _).trans hm12) (by simpa [nbits] using hcap)
  have hnrestart : Composition.restart emitP.final (negativeEmit sign).start=
      RecoveryCalls.restarted (negativeEmit sign) (kernelHeads (pre++pbits)) middleP := by
    apply configuration_ext
    · rfl
    · exact hpheads
    · exact hpt
  have hnrun : runFrom (negativeEmit sign) (4*w+3) (Composition.restart emitP.final (negativeEmit sign).start)=some emitN := by
    rw [hnrestart]
    simpa only [nbits,binary_length,negativeEmit] using hemitN
  have hprun : runFrom (positiveEmit sign) (4*w+3)
      (RecoveryCalls.restarted (positiveEmit sign) (kernelHeads pre) middle)=some emitP := by
    simpa only [pbits,binary_length,positiveEmit] using hemitP
  have hemits := Composition.run_join (positiveEmit sign) (negativeEmit sign) _ _ _ emitP emitN hprun hnrun
  let last := Composition.joinedReceipt emitP emitN
  have hrestart : Composition.restart first.final (kernelEmit sign).start=
      Composition.leftConfig 4 (RecoveryCalls.restarted (positiveEmit sign) (kernelHeads pre) middle) := by
    apply configuration_ext
    · rfl
    · exact hfh
    · exact hft
  have hlast : runFrom (kernelEmit sign) ((4*w+3)+1+(4*w+3))
      (Composition.restart first.final (kernelEmit sign).start)=some last := by rw [hrestart]; exact hemits
  have hall := Composition.run_join (kernelArithmetic sign) (kernelEmit sign) _ _ _ first last hfirst hlast
  have htime : arithmeticBudget w bits+1+((4*w+3)+1+(4*w+3))=kernelBudget w bits := by unfold kernelBudget; omega
  rw [htime] at hall
  let out := Function.update middleP 17 (pre++pbits++nbits)
  refine ⟨Composition.joinedReceipt first last,out,hall,?_,?_,hnt,?_,?_,?_,?_⟩
  · change first.steps+1+(emitP.steps+1+emitN.steps)≤kernelBudget w bits
    simp only [pbits,nbits,binary_length] at hps hns
    unfold kernelBudget
    omega
  · change emitN.final.heads=kernelHeads (pre++nextWord sign w positive negative count bits)
    rw [hnh,updated_heads]
    simp only [nextWord,pairWord,pbits,nbits,List.append_assoc]
  · simp [out,nextWord,pairWord,pbits,nbits,List.append_assoc]
  · exact (Function.update_of_ne (by decide : (0 : Fin 18)≠17) _ _).trans
      ((Function.update_of_ne (by decide : (0 : Fin 18)≠17) _ _).trans ((install_slot native native_injective _ _ 0).trans h0))
  · exact (Function.update_of_ne (by decide : (9 : Fin 18)≠17) _ _).trans
      ((Function.update_of_ne (by decide : (9 : Fin 18)≠17) _ _).trans ((install_slot native native_injective _ _ 9).trans h9))
  · intro i
    change (Function.update middleP 17 _ (native i)).length≤capacity w
    rw [Function.update_of_ne (native_avoids i)]
    change (Function.update middle 17 _ (native i)).length≤capacity w
    rw [Function.update_of_ne (native_avoids i)]
    change (install native _ produced (native i)).length≤capacity w
    rw [install_slot native native_injective]
    exact hsupp i

end NearCubicWires.RepairOrdinary.CompetitorPlane
