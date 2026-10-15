import Proof.Hierarchy.CompetitorPlaneNative

/-! One whole aligned native-count/P/N cell update, including physical clear,
runtime-width copy, all three input fields, multiply/add and raw output.
Only the three global stream cursors advance. -/
namespace NearCubicWires.RepairOrdinary.CompetitorPlaneStream
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def prepareProgram := Composition.machine clearWidthProgram fieldsProgram
def prepareBudget (w : ℕ) := clearWidthBudget w+12*w+12
noncomputable def bodyProgram (sign : Bool) := Composition.machine prepareProgram (nativeProgram sign)
def bodyBudget (w : ℕ) := 9000*(w+1)^2

theorem prepare_run (b w count positive negative : ℕ) (bits preCount tailCount preOld tailOld output : List Bool)
    (ambient : Fin 27 → List Bool)
    (h : Store b w bits (preCount++binary b count++tailCount)
      (preOld++CompetitorPlane.pairWord w positive negative++tailOld) output ambient)
    (hb : b≤w) (hc : count<2^b) (hp : positive<2^w) (hn : negative<2^w) :
    ∃ r,runFrom prepareProgram (prepareBudget w)
        (cfg prepareProgram.start preCount.length preOld.length output.length ambient)=some r ∧
      r.steps≤prepareBudget w ∧ r.final.heads=heads (preCount.length+b) (preOld.length+2*w) output.length ∧
      r.final.tapes=loadedFields w count positive negative ambient := by
  obtain ⟨first,hfirst,hfs,hfh,hft⟩ := clear_width_run b w preCount.length preOld.length output.length bits _ _ output ambient h
  obtain ⟨last,hlast,hls,hlh,hlt⟩ := fields_run b w count positive negative bits preCount tailCount preOld tailOld output ambient h hb hc hp hn
  have he : Composition.restart first.final fieldsProgram.start=
      cfg fieldsProgram.start preCount.length preOld.length output.length (widthPrepared w ambient) := by
    apply configuration_ext
    · rfl
    · exact hfh
    · exact hft
  have hl' : runFrom fieldsProgram (12*w+11) (Composition.restart first.final fieldsProgram.start)=some last := by rw [he]; exact hlast
  have hall := Composition.run_join clearWidthProgram fieldsProgram _ _ _ first last hfirst hl'
  have htime : clearWidthBudget w+1+(12*w+11)=prepareBudget w := by unfold prepareBudget; omega
  rw [htime] at hall
  refine ⟨Composition.joinedReceipt first last,hall,?_,hlh,hlt⟩
  change first.steps+1+last.steps≤prepareBudget w
  unfold prepareBudget
  omega

theorem body_run (sign : Bool) (b w count positive negative : ℕ) (bits preCount tailCount preOld tailOld output : List Bool)
    (ambient : Fin 27 → List Bool)
    (h : Store b w bits (preCount++binary b count++tailCount)
      (preOld++CompetitorPlane.pairWord w positive negative++tailOld) output ambient)
    (hb : b≤w) (hc : count<2^b) (hp : positive<2^w) (hn : negative<2^w)
    (hbits : bits.length≤w) (hshift : count*2^bits.length<2^w)
    (hadd : count*value bits+(if sign then negative else positive)<2^w) :
    ∃ r,runFrom (bodyProgram sign) (bodyBudget w)
        (cfg (bodyProgram sign).start preCount.length preOld.length output.length ambient)=some r ∧
      r.steps≤bodyBudget w ∧
      r.final.heads=heads (preCount.length+b) (preOld.length+2*w)
        (output++CompetitorPlane.nextWord sign w positive negative count bits).length ∧
      Store b w bits (preCount++binary b count++tailCount)
        (preOld++CompetitorPlane.pairWord w positive negative++tailOld)
        (output++CompetitorPlane.nextWord sign w positive negative count bits) r.final.tapes := by
  obtain ⟨first,hfirst,hfs,hfh,hft⟩ := prepare_run b w count positive negative bits preCount tailCount preOld tailOld output ambient h hb hc hp hn
  obtain ⟨last,out,hlast,hls,hlh,hlt,hstore⟩ := native_run sign b w count positive negative
    (preCount.length+b) (preOld.length+2*w) bits _ _ output ambient h hbits hshift hadd
  have he : Composition.restart first.final (nativeProgram sign).start=
      cfg (nativeProgram sign).start (preCount.length+b) (preOld.length+2*w) output.length
        (loadedFields w count positive negative ambient) := by
    apply configuration_ext
    · rfl
    · exact hfh
    · exact hft
  have hl' : runFrom (nativeProgram sign) (CompetitorPlane.kernelBudget w bits)
      (Composition.restart first.final (nativeProgram sign).start)=some last := by rw [he]; exact hlast
  have hall := Composition.run_join prepareProgram (nativeProgram sign) _ _ _ first last hfirst hl'
  have hcost : prepareBudget w+1+CompetitorPlane.kernelBudget w bits≤bodyBudget w := by
    have ha := CompetitorPlane.arithmetic_budget_bound w bits hbits
    unfold prepareBudget clearWidthBudget CompetitorPlane.kernelBudget bodyBudget CompetitorPlane.capacity
    nlinarith
  let result := Composition.joinedReceipt first last
  have hmore := runFrom_moreFuel (bodyProgram sign) _
    (bodyBudget w-(prepareBudget w+1+CompetitorPlane.kernelBudget w bits)) _ result hall
  rw [Nat.add_sub_of_le hcost] at hmore
  refine ⟨result,hmore,?_,hlh,?_⟩
  · change first.steps+1+last.steps≤bodyBudget w
    omega
  · change Store b w bits _ _ _ last.final.tapes
    rw [hlt]
    exact hstore

end NearCubicWires.RepairOrdinary.CompetitorPlaneStream
