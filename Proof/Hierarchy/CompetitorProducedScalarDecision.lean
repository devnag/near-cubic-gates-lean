import Proof.Hierarchy.CompetitorProducedScalarInput

/-! A single fixed ordinary machine now executes the bulk coefficient/count
producer, rewinds once, derives the scalar work dimensions, folds the exact
signed sum, prints its fixed rational threshold and decides the comparison. -/
namespace NearCubicWires.RepairOrdinary.CompetitorProducedScalar
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open CompetitorMonomialStream CompetitorRationalDecision
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def decisionProgram (lower : Bool) (l : ℕ) (q : ℚ) :=
  RecoveryFocus.machine decisionSlot (CompetitorDimensionedDecision.machine lower l q)
noncomputable def machine (lower : Bool) (l : ℕ) (q : ℚ) :=
  Composition.machine producerProgram (decisionProgram lower l q)
def commonWidth (b l n : ℕ) := CompetitorThresholdCold.runtimeWidth n (width b) l
def budget (t l n : ℕ) := CompetitorMonomialEntry.readyBudget t n+1+CompetitorDimensionedDecision.budget t l n

theorem common_width (b l n : ℕ) : width b≤commonWidth b l n ∧ n≤commonWidth b l n ∧ l≤commonWidth b l n := by
  unfold commonWidth CompetitorThresholdCold.runtimeWidth CompetitorSumWidth.width
  constructor
  · nlinarith
  · constructor <;> nlinarith

theorem runtime_run (lower : Bool) (l : ℕ) (q : ℚ) (b : ℕ) (xs : List Entry)
    (hv : ∀ a∈xs,a.Valid b) (hq : 0≤q)
    (hp : CompetitorThresholdDecision.numerator q<2^l) (hd : q.den<2^l) :
    ∃ r,run (machine lower l q) (budget (commonWidth b l xs.length) l xs.length)
        (input b (commonWidth b l xs.length) xs)=some r ∧
      r.steps≤budget (commonWidth b l xs.length) l xs.length ∧ r.final.heads 155=0 ∧
      (readTapeBit (r.final.tapes 155) 0=true ↔ CompetitorThresholdCold.passes lower q (contributions xs)) := by
  let t := commonWidth b l xs.length
  have hlen : (contributions xs).length=xs.length := List.length_map _
  obtain ⟨produced,⟨first,hfirst,hft,hfh,hfs⟩,hselected,hvalid⟩ := producer_run b t xs hv
    (common_width b l xs.length).1 (common_width b l xs.length).2.1
  obtain ⟨base,hbase,hbs,hbh,hflag⟩ := CompetitorDimensionedDecision.runtime_run lower l q (width b)
    (contributions xs) hvalid hq hp hd
  have hbase' : run (CompetitorDimensionedDecision.machine lower l q)
      (CompetitorDimensionedDecision.budget t l xs.length) (CompetitorDimensionedDecision.input t (contributions xs))=some base := by
    simpa only [hlen,t,commonWidth] using hbase
  have hbs' : base.steps≤CompetitorDimensionedDecision.budget t l xs.length := by simpa only [hlen,t,commonWidth] using hbs
  obtain ⟨last,hlast,hlf,hls⟩ := RecoveryFocus.run_config decisionSlot decision_injective
    (CompetitorDimensionedDecision.machine lower l q) (fun _ => 0) produced _ _ base hbase'
  have hi : RecoveryFocus.config decisionSlot (fun _ => 0) produced
      (initialConfiguration (CompetitorDimensionedDecision.machine lower l q)
        (CompetitorDimensionedDecision.input t (contributions xs)))=
      initialConfiguration (decisionProgram lower l q) produced := by
    apply configuration_ext
    · rfl
    · funext i
      cases h : RecoveryFocus.pick decisionSlot i <;> simp [RecoveryFocus.config,h,initialConfiguration]
    · exact install_existing decisionSlot produced _ hselected
  rw [hi] at hlast
  have he : Composition.restart first.final (decisionProgram lower l q).start=
      initialConfiguration (decisionProgram lower l q) produced := by
    apply configuration_ext
    · rfl
    · funext i
      exact hfh i
    · exact hft
  have hl' : runFrom (decisionProgram lower l q) (CompetitorDimensionedDecision.budget t l xs.length)
      (Composition.restart first.final (decisionProgram lower l q).start)=some last := by rw [he]; exact hlast
  have hall := Composition.run_join producerProgram (decisionProgram lower l q) _ _ _ first last hfirst hl'
  refine ⟨Composition.joinedReceipt first last,hall,?_,?_,?_⟩
  · change first.steps+1+last.steps≤budget t l xs.length
    unfold budget
    omega
  · change last.final.heads 155=0
    rw [hlf]
    change (RecoveryFocus.config decisionSlot (fun _ => 0) produced base.final).heads (decisionSlot 65)=0
    simpa only [RecoveryFocus.config,RecoveryFocus.pick_slot decisionSlot decision_injective] using hbh
  · change readTapeBit (last.final.tapes 155) 0=true ↔ CompetitorThresholdCold.passes lower q (contributions xs)
    have ht155 : last.final.tapes 155=base.final.tapes 65 := by
      rw [hlf]
      change install decisionSlot produced base.final.tapes (decisionSlot 65)=base.final.tapes 65
      exact install_slot decisionSlot decision_injective _ _ 65
    simpa only [ht155] using hflag

theorem budget_bound (t l n : ℕ) (hl : l≤t) : budget t l n≤120000*(n+1)*(t+1)^2 := by
  have hscalar := CompetitorDimensionedDecision.budget_bound t l n hl
  have hsq : 1≤(t+1)^2 := by nlinarith
  unfold budget CompetitorMonomialEntry.readyBudget CompetitorMonomialEntry.budget loopBudget bodyBudget CompetitorReusableDecision.capacity
  nlinarith

end NearCubicWires.RepairOrdinary.CompetitorProducedScalar
