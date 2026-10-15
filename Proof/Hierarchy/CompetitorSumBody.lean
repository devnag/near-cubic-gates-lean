import Proof.Hierarchy.CompetitorSumResult

/-! Enclosing paid update for the exact signed-rational term stream:
clear/load the next term, execute the addition and denominator product, then
clear/copy back the accumulator. The global source cursor advances once. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSumFold
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorReusableDecision CompetitorRationalDecision
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def bodyTail := Composition.machine nativeProgram restoreProgram
noncomputable def bodyProgram := Composition.machine prepareProgram bodyTail
def bodyBudget (b : ℕ) := 20000*(b+1)^2

theorem body_run (b : ℕ) (a c : CompetitorValidity.Estimate) (pre suffix : List Bool)
    (ambient : Fin 94 → List Bool) (h : Store b a (pre++termWord b c++suffix) ambient)
    (ha : a.Valid b) (hc : c.Valid b) :
    ∃ r,
      runFrom bodyProgram (bodyBudget b) (cfg bodyProgram.start pre.length ambient)=some r ∧
      r.final.heads=heads (pre.length+(termWord b c).length) ∧
      Store b (CompetitorRationalNumerators.add a c) (pre++termWord b c++suffix) r.final.tapes ∧
      r.steps≤bodyBudget b := by
  let source := pre++termWord b c++suffix
  let pos := pre.length+(termWord b c).length
  obtain ⟨prep,hprep,hph,hpt,hps⟩ := prepare_run b a c pre suffix ambient h
  obtain ⟨native,hnative,hnh,hnt,hns⟩ := native_run b pos a c source ambient h ha hc
  obtain ⟨restore,hrestore,hrh,hrt,hrs⟩ := restore_run b pos (CompetitorRationalNumerators.add a c)
    source native.final.tapes hnt
  have heRestore : Composition.restart native.final restoreProgram.start=
      cfg restoreProgram.start pos native.final.tapes := by
    apply configuration_ext
    · rfl
    · exact hnh
    · rfl
  have hr' : runFrom restoreProgram (2*capacity b+40*b+63)
      (Composition.restart native.final restoreProgram.start)=some restore := by
    rw [heRestore]
    exact hrestore
  have htail := Composition.run_join nativeProgram restoreProgram _ _ _ native restore hnative hr'
  let tail := Composition.joinedReceipt native restore
  have heNative : Composition.restart prep.final bodyTail.start=
      Composition.leftConfig 22 (cfg nativeProgram.start pos (prepared b c ambient)) := by
    apply configuration_ext
    · rfl
    · exact hph
    · exact hpt
  have ht' : runFrom bodyTail ((3000*(b+1)^2)+1+(2*capacity b+40*b+63))
      (Composition.restart prep.final bodyTail.start)=some tail := by
    rw [heNative]
    exact htail
  have hall := Composition.run_join prepareProgram bodyTail _ _ _ prep tail hprep ht'
  let r := Composition.joinedReceipt prep tail
  have hcost : (2*capacity b+20*b+33)+1+((3000*(b+1)^2)+1+(2*capacity b+40*b+63))≤bodyBudget b := by
    unfold capacity bodyBudget
    nlinarith
  have hmore := runFrom_moreFuel bodyProgram _
    (bodyBudget b-((2*capacity b+20*b+33)+1+((3000*(b+1)^2)+1+(2*capacity b+40*b+63)))) _ r hall
  rw [Nat.add_sub_of_le hcost] at hmore
  refine ⟨r,hmore,hrh,hrt,?_⟩
  change prep.steps+1+(native.steps+1+restore.steps)≤bodyBudget b
  omega

end NearCubicWires.RepairOrdinary.CompetitorSumFold
