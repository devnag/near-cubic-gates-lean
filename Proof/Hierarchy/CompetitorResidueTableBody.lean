import Proof.Hierarchy.CompetitorResidueTableNative

/-! One complete sequential residue-table iteration: local erase, two raw
operand loads, signed subtraction and exact fixed-Q output append. -/
namespace NearCubicWires.RepairOrdinary.CompetitorResidueTable
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def prepareProgram := Composition.machine clearProgram fieldsProgram
def prepareBudget (w : ℕ) := 2*capacity w+8*w+12
noncomputable def bodyProgram := Composition.machine prepareProgram nativeProgram
def bodyBudget (w q : ℕ) := 2*capacity w+12*w+8*q+26

theorem prepare_run (w q a b : ℕ) (pre suffix output : List Bool) (ambient : Fin 27 → List Bool)
    (h : Store w q (pre++CompetitorPlane.pairWord w a b++suffix) output ambient)
    (ha : a<2^w) (hb : b<2^w) :
    ∃ r,runFrom prepareProgram (prepareBudget w)
      (cfg prepareProgram.start pre.length output.length ambient)=some r ∧
      r.final.heads=heads (pre.length+2*w) output.length ∧
      r.final.tapes=loaded w a b ambient ∧ r.steps=prepareBudget w := by
  obtain ⟨first,hfirst,hfh,hft,hfs⟩ := clear_run w q pre.length output.length _ output ambient h
  obtain ⟨last,hlast,hlh,hlt,hls⟩ := fields_run w q a b pre suffix output ambient h ha hb
  have he : Composition.restart first.final fieldsProgram.start=
      cfg fieldsProgram.start pre.length output.length (clean w ambient) := by
    apply configuration_ext
    · rfl
    · exact hfh
    · exact hft
  have hl' : runFrom fieldsProgram (8*w+7) (Composition.restart first.final fieldsProgram.start)=some last := by
    rw [he]
    exact hlast
  have hall := Composition.run_join clearProgram fieldsProgram _ _ _ first last hfirst hl'
  have htime : (2*capacity w+4)+1+(8*w+7)=prepareBudget w := by unfold prepareBudget; omega
  rw [htime] at hall
  refine ⟨Composition.joinedReceipt first last,hall,hlh,hlt,?_⟩
  change first.steps+1+last.steps=prepareBudget w
  unfold prepareBudget
  omega

theorem body_run (w q a b : ℕ) (pre suffix output : List Bool) (ambient : Fin 27 → List Bool)
    (h : Store w q (pre++CompetitorPlane.pairWord w a b++suffix) output ambient)
    (ha : a<2^w) (hb : b<2^w) (hq : q≤w) :
    ∃ r,runFrom bodyProgram (bodyBudget w q)
      (cfg bodyProgram.start pre.length output.length ambient)=some r ∧
      r.steps≤bodyBudget w q ∧
      r.final.heads=heads (pre.length+2*w)
        (output++binary q (CompetitorSignedResidue.residue w q a b)).length ∧
      Store w q (pre++CompetitorPlane.pairWord w a b++suffix)
        (output++binary q (CompetitorSignedResidue.residue w q a b)) r.final.tapes := by
  obtain ⟨first,hfirst,hfh,hft,hfs⟩ := prepare_run w q a b pre suffix output ambient h ha hb
  obtain ⟨last,hlast,hls,hlh,hlt⟩ := native_run w q a b (pre.length+2*w) _ output ambient h ha hb hq
  have he : Composition.restart first.final nativeProgram.start=
      cfg nativeProgram.start (pre.length+2*w) output.length (loaded w a b ambient) := by
    apply configuration_ext
    · rfl
    · exact hfh
    · exact hft
  have hl' : runFrom nativeProgram (CompetitorResidueCell.budget w q)
      (Composition.restart first.final nativeProgram.start)=some last := by
    rw [he]
    exact hlast
  have hall := Composition.run_join prepareProgram nativeProgram _ _ _ first last hfirst hl'
  have htime : prepareBudget w+1+CompetitorResidueCell.budget w q=bodyBudget w q := by
    unfold prepareBudget CompetitorResidueCell.budget bodyBudget
    omega
  rw [htime] at hall
  refine ⟨Composition.joinedReceipt first last,hall,?_,hlh,hlt⟩
  change first.steps+1+last.steps≤bodyBudget w q
  omega

theorem body_budget_bound (w q : ℕ) (hq : q≤w) : bodyBudget w q≤9000*(w+1)^2 := by
  unfold bodyBudget capacity CompetitorReusableDecision.capacity
  nlinarith

end NearCubicWires.RepairOrdinary.CompetitorResidueTable
