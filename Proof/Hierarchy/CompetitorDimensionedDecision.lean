import Proof.Hierarchy.CompetitorDimensionedInput

/-! Whole fixed ordinary scalar decision with physically derived work
drivers. Its only scalar-entry inputs are the exact term stream, the short
width and term-count words; W and C are outputs of its dimension prefix. -/
namespace NearCubicWires.RepairOrdinary.CompetitorDimensionedDecision
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def decisionProgram (lower : Bool) (l : ℕ) (q : ℚ) :=
  RecoveryFocus.machine native (CompetitorThresholdCold.machine lower l q)
noncomputable def machine (lower : Bool) (l : ℕ) (q : ℚ) :=
  Composition.machine prepareProgram (decisionProgram lower l q)
def budget (b l n : ℕ) := CompetitorDimensions.budget b+1+CompetitorThresholdCold.budget b l n

theorem runtime_run (lower : Bool) (l : ℕ) (q : ℚ) (k : ℕ) (xs : List CompetitorValidity.Estimate)
    (hv : ∀ a∈xs,a.Valid k) (hq : 0≤q)
    (hp : CompetitorThresholdDecision.numerator q<2^l) (hd : q.den<2^l) :
    ∃ r,run (machine lower l q) (budget (CompetitorThresholdCold.runtimeWidth xs.length k l) l xs.length)
        (input (CompetitorThresholdCold.runtimeWidth xs.length k l) xs)=some r ∧
      r.steps≤budget (CompetitorThresholdCold.runtimeWidth xs.length k l) l xs.length ∧ r.final.heads 65=0 ∧
      (readTapeBit (r.final.tapes 65) 0=true ↔ CompetitorThresholdCold.passes lower q xs) := by
  let b := CompetitorThresholdCold.runtimeWidth xs.length k l
  obtain ⟨prepared,⟨first,hfirst,hft,hfh,hfs⟩,hselected⟩ := prepare_run b xs
  obtain ⟨base,hbase,hbs,hbh,hflag⟩ := CompetitorThresholdCold.runtime_decision_run lower l q k xs hv hq hp hd
  change base.steps≤CompetitorThresholdCold.budget b l xs.length at hbs
  obtain ⟨last,hlast,hlf,hls⟩ := RecoveryFocus.run_config native native_injective (CompetitorThresholdCold.machine lower l q)
    (fun _ => 0) prepared _ _ base hbase
  have hi : RecoveryFocus.config native (fun _ => 0) prepared
      (initialConfiguration (CompetitorThresholdCold.machine lower l q) (CompetitorThresholdCold.input b xs))=
      initialConfiguration (decisionProgram lower l q) prepared := by
    apply configuration_ext
    · rfl
    · funext i
      cases h : RecoveryFocus.pick native i <;> simp [RecoveryFocus.config,h,initialConfiguration]
    · exact install_existing native prepared (CompetitorThresholdCold.input b xs) hselected
  rw [hi] at hlast
  have he : Composition.restart first.final (decisionProgram lower l q).start=
      initialConfiguration (decisionProgram lower l q) prepared := by
    apply configuration_ext
    · rfl
    · funext i
      exact hfh i
    · exact hft
  have hl' : runFrom (decisionProgram lower l q) (CompetitorThresholdCold.budget b l xs.length)
      (Composition.restart first.final (decisionProgram lower l q).start)=some last := by rw [he]; exact hlast
  have hall := Composition.run_join prepareProgram (decisionProgram lower l q) _ _ _ first last hfirst hl'
  refine ⟨Composition.joinedReceipt first last,hall,?_,?_,?_⟩
  · change first.steps+1+last.steps≤budget b l xs.length
    unfold budget
    omega
  · change last.final.heads 65=0
    rw [hlf]
    change (RecoveryFocus.config native (fun _ => 0) prepared base.final).heads (native 65)=0
    simpa only [RecoveryFocus.config,RecoveryFocus.pick_slot native native_injective] using hbh
  · change readTapeBit (last.final.tapes 65) 0=true ↔ CompetitorThresholdCold.passes lower q xs
    have ht65 : last.final.tapes 65=base.final.tapes 65 := by
      rw [hlf]
      change install native prepared base.final.tapes (native 65)=base.final.tapes 65
      exact install_slot native native_injective _ _ 65
    simpa only [ht65] using hflag

theorem budget_bound (b l n : ℕ) (hl : l≤b) : budget b l n≤70000*(n+1)*(b+1)^2 := by
  have hd := CompetitorDimensions.budget_bound b
  have hs := CompetitorThresholdCold.budget_bound b l n hl
  unfold CompetitorReusableDecision.capacity at hd
  unfold budget
  have hsq : 1≤(b+1)^2 := by nlinarith
  nlinarith

end NearCubicWires.RepairOrdinary.CompetitorDimensionedDecision
