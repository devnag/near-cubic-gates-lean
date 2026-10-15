import Proof.CaseAnalysis.RowsEstimatorCoefficientsLoop
import Proof.Hierarchy.CompetitorRecordScalar

/-! The unchanged cold scalar decision consumes the unchanged six-field
stream with arbitrary signed natural fractions. It derives all work dimensions,
executes the original stream and exact rational sum, and compares its value. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open CompetitorRationalDecision Stream
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace Produced
open CompetitorProducedScalar

def input (b t : ℕ) (xs : List Entry) : Fin 213 → List Bool :=
  Fin.addCases (m := 90) (n := 123) (motive := fun _ => List Bool) (EntryMachine.readyInput b t xs) (fun _ => [])

theorem input_outside (b t : ℕ) (xs : List Entry) (i : Fin 213) (hi : 90 ≤ i.val) : input b t xs i=[] := by
  have he : i=(⟨i.val-90,by omega⟩ : Fin 123).natAdd 90 := Fin.ext (by simp; omega)
  rw [he]
  simp only [input,Fin.addCases_right]

theorem producer_run (b t : ℕ) (xs : List Entry) (hv : ∀ a∈xs,a.Valid b)
    (htarget : width b≤t) (hn : xs.length≤t) :
    ∃ out,ClockJoin.ReadyRun producerProgram (CompetitorMonomialEntry.readyBudget t xs.length) (input b t xs) out ∧
      (∀ i,out (decisionSlot i)=CompetitorDimensionedDecision.input t (contributions xs) i) ∧
      (∀ a∈contributions xs,a.Valid (width b)) := by
  obtain ⟨produced,hr,h74,h83,h88,hvalid⟩ := EntryMachine.ready_stream_run b t xs hv htarget hn
  have hin : ∀ i,input b t xs (native i)=EntryMachine.readyInput b t xs i := by simp [input,native]
  have hf := CompetitorRationalProducts.bounded_focus native native_injective _ _ _ hr (input b t xs) hin
  refine ⟨install native (input b t xs) produced,hf,?_,hvalid⟩
  intro i
  by_cases h84 : i=84
  · subst i
    exact (install_slot native native_injective _ produced 83).trans h83
  · by_cases h88' : i=88
    · subst i
      exact (install_slot native native_injective _ produced 74).trans h74
    · by_cases h94 : i=94
      · subst i
        have hl : (contributions xs).length=xs.length := List.length_map _
        change install native (input b t xs) produced (native 88)=RepairSource.VerifierDecoding.CompareMachine.word (contributions xs).length
        rw [hl]
        exact (install_slot native native_injective (input b t xs) produced 88).trans h88
      · rw [scalar_blank t (contributions xs) i h84 h88' h94]
        have hval := decision_other i h84 h88' h94
        exact (install_other native _ _ (decisionSlot i) (fun j => native_other j _ hval)).trans (input_outside b t xs _ hval)

theorem runtime_run (lower : Bool) (l : ℕ) (q : ℚ) (b : ℕ) (xs : List Entry)
    (hv : ∀ a∈xs,a.Valid b) (hq : 0≤q)
    (hp : CompetitorThresholdDecision.numerator q<2^l) (hd : q.den<2^l) :
    ∃ r,run (CompetitorProducedScalar.machine lower l q) (budget (commonWidth b l xs.length) l xs.length)
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

end Produced

namespace Scalar
open CompetitorRecordScalar

def extra (b : ℕ) (xs : List Entry) (i : Fin 214) : List Bool := if i=0 then words b xs else []
def input (b : ℕ) (xs : List Entry) : Fin 263 → List Bool :=
  Fin.addCases (m := 49) (n := 214) (motive := fun _ => List Bool)
    (CompetitorRecordScalarDimensions.input b xs.length) (extra b xs)
theorem scalar_input_cases (b t : ℕ) (xs : List Entry) (i : Fin 213) :
    Produced.input b t xs i=
      if i.val=79 then words b xs else if i.val=81 then List.replicate (width b) true
      else if i.val=82 then List.replicate (width t) true else if i.val=83 then List.replicate t true
      else if i.val=84 then List.replicate (CompetitorReusableDecision.capacity t) true
      else if i.val=88 then RepairSource.VerifierDecoding.CompareMachine.word xs.length else [] := by
  fin_cases i <;> rfl

theorem prepared_slots (b l : ℕ) (xs : List Entry) (data : Fin 49 → List Bool)
    (h15 : data 15=List.replicate (width b) true)
    (h42 : data 42=List.replicate (width (CompetitorProducedScalar.commonWidth b l xs.length)) true)
    (h26 : data 26=List.replicate (CompetitorProducedScalar.commonWidth b l xs.length) true)
    (h44 : data 44=List.replicate (CompetitorReusableDecision.capacity
      (CompetitorProducedScalar.commonWidth b l xs.length)) true)
    (h47 : data 47=RepairSource.VerifierDecoding.CompareMachine.word xs.length)
    (i : Fin 213) :
    Fin.addCases (m := 49) (n := 214) (motive := fun _ => List Bool) data (extra b xs) (slots i)=
      Produced.input b (CompetitorProducedScalar.commonWidth b l xs.length) xs i := by
  rw [scalar_input_cases]
  by_cases h79 : i.val=79
  · simp only [slots,h79,↓reduceIte]
    rfl
  by_cases h81 : i.val=81
  · simp only [slots,h81,↓reduceIte]
    exact h15
  by_cases h82 : i.val=82
  · simp only [slots,h82,↓reduceIte]
    exact h42
  by_cases h83 : i.val=83
  · simp only [slots,h83,↓reduceIte]
    exact h26
  by_cases h84 : i.val=84
  · simp only [slots,h84,↓reduceIte]
    exact h44
  by_cases h88 : i.val=88
  · simp only [slots,h88,↓reduceIte]
    exact h47
  have he : (⟨i.val+50,by omega⟩ : Fin 263)=
      (⟨i.val+1,by omega⟩ : Fin 214).natAdd 49 := Fin.ext (by simp;omega)
  have hn : (⟨i.val+1,by omega⟩ : Fin 214)≠0 := by
    intro h
    have hv := congrArg Fin.val h
    change i.val+1=0 at hv
    omega
  simp only [slots,h79,h81,h82,h83,h84,h88,↓reduceIte,he,Fin.addCases_right,extra,hn]

theorem runtime_run (lower : Bool) (l : ℕ) (q : ℚ) (b : ℕ) (xs : List Entry)
    (hv : ∀ a∈xs,a.Valid b) (hq : 0≤q)
    (hp : CompetitorThresholdDecision.numerator q<2^l) (hd : q.den<2^l) :
    ∃ actual,run (CompetitorRecordScalar.machine lower l q) (budget b l xs.length) (input b xs)=some actual ∧
      actual.steps≤budget b l xs.length ∧ actual.final.heads 205=0 ∧
      (readTapeBit (actual.final.tapes 205) 0=true ↔
        CompetitorThresholdCold.passes lower q (contributions xs)) := by
  let t := CompetitorProducedScalar.commonWidth b l xs.length
  obtain ⟨d,hdim,d15,d42,d26,d44,d47⟩ := CompetitorRecordScalarDimensions.dimensions_run b l xs.length
  let prepared : Fin 263 → List Bool := Fin.addCases (m := 49) (n := 214)
    (motive := fun _ => List Bool) d (extra b xs)
  have hfirst : ClockJoin.ReadyRun (first l) (CompetitorRecordScalarDimensions.budget b l xs.length)
      (input b xs) prepared := ClockJoin.lift (e := 214) (Equiv.refl (Fin 263)) _ _ _ _ (extra b xs) hdim
  obtain ⟨before,hbefore,bt,bh,bs⟩ := hfirst
  obtain ⟨child,ch,cs,chh,ct⟩ := Produced.runtime_run lower l q b xs hv hq hp hd
  have htapes : ∀ i,before.final.tapes (slots i)=Produced.input b t xs i := by
    intro i
    rw [bt]
    exact prepared_slots b l xs d d15 d42 d26 d44 d47 i
  obtain ⟨tail,htail,_,ts,th,tt,_⟩ := RecoveryFocus.dock slots slots_injective
    (CompetitorProducedScalar.machine lower l q) _ before.final.heads before.final.tapes _
    (fun i => bh _) htapes child ch
  have htail' : runFrom (last lower l q) (CompetitorProducedScalar.budget t l xs.length)
      (Composition.restart before.final (last lower l q).start)=some tail := htail
  have hj := Composition.run_join (first l) (last lower l q) _ _ _ before tail hbefore htail'
  have hcost : before.steps+1+tail.steps≤budget b l xs.length := by
    rw [ts]
    unfold budget
    omega
  refine ⟨Composition.joinedReceipt before tail,hj,hcost,(th 155).trans chh,?_⟩
  have h205 : tail.final.tapes 205=child.final.tapes 155 := tt 155
  change readTapeBit (tail.final.tapes 205) 0=true ↔_
  rw [h205]
  exact ct

theorem values (xs : List Entry) :
    ((contributions xs).map CompetitorValidity.Estimate.value).sum=
      (xs.map (fun a => a.coefficient.value*((a.count : ℚ)/a.denominator))).sum := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [contributions,List.map_cons,List.sum_cons] at *
    rw [Entry.estimate_value,ih]

theorem runtime_value_run (lower : Bool) (l : ℕ) (q : ℚ) (b : ℕ) (xs : List Entry)
    (hv : ∀ a∈xs,a.Valid b) (hq : 0≤q)
    (hp : CompetitorThresholdDecision.numerator q<2^l) (hd : q.den<2^l) :
    ∃ actual,run (CompetitorRecordScalar.machine lower l q) (budget b l xs.length) (input b xs)=some actual ∧
      actual.steps≤budget b l xs.length ∧ actual.final.heads 205=0 ∧
      (readTapeBit (actual.final.tapes 205) 0=true ↔
        if lower then q≤(xs.map (fun a => a.coefficient.value*((a.count : ℚ)/a.denominator))).sum
        else (xs.map (fun a => a.coefficient.value*((a.count : ℚ)/a.denominator))).sum≤q) := by
  obtain ⟨r,hr,hs,hh,hv⟩ := runtime_run lower l q b xs hv hq hp hd
  refine ⟨r,hr,hs,hh,?_⟩
  simpa only [CompetitorThresholdCold.passes,values] using hv

end Scalar
end NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients
