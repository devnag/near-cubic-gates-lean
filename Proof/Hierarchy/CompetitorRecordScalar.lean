import Proof.Hierarchy.CompetitorRecordScalarDimensions
import Proof.Amplification.RecoveryFocusDock

/-! One cold ordinary scalar program consumes the actual six-field record
stream and its raw width/count, physically derives every allocation/loop
driver, and executes the exact rational scalar comparison. -/
namespace NearCubicWires.RepairOrdinary.CompetitorRecordScalar
open LocalBitMultitape RecoveryRootRound RecoveryExecution
open CompetitorMonomialStream CompetitorRationalDecision
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def extra (b : ℕ) (xs : List Entry) (i : Fin 214) : List Bool := if i=0 then words b xs else []
def input (b : ℕ) (xs : List Entry) : Fin 263 → List Bool :=
  Fin.addCases (m := 49) (n := 214) (motive := fun _ => List Bool)
    (CompetitorRecordScalarDimensions.input b xs.length) (extra b xs)
def slots (i : Fin 213) : Fin 263 :=
  if i.val=79 then 49 else if i.val=81 then 15 else if i.val=82 then 42
  else if i.val=83 then 26 else if i.val=84 then 44 else if i.val=88 then 47
  else ⟨i.val+50,by omega⟩
noncomputable def first (l : ℕ) := ClockJoin.lifted (e := 214) (Equiv.refl (Fin 263))
  (CompetitorRecordScalarDimensions.machine l)
noncomputable def last (lower : Bool) (l : ℕ) (q : ℚ) :=
  RecoveryFocus.machine slots (CompetitorProducedScalar.machine lower l q)
noncomputable def machine (lower : Bool) (l : ℕ) (q : ℚ) :=
  Composition.machine (first l) (last lower l q)
def budget (b l n : ℕ) := CompetitorRecordScalarDimensions.budget b l n+1+
  CompetitorProducedScalar.budget (CompetitorProducedScalar.commonWidth b l n) l n

theorem slots_injective : Function.Injective slots := by
  intro i j h
  have hv := congrArg Fin.val h
  simp only [slots] at hv
  split_ifs at hv <;> (try simp only at hv) <;> omega

theorem scalar_input_cases (b t : ℕ) (xs : List Entry) (i : Fin 213) :
    CompetitorProducedScalar.input b t xs i=
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
      CompetitorProducedScalar.input b (CompetitorProducedScalar.commonWidth b l xs.length) xs i := by
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
    ∃ actual,run (machine lower l q) (budget b l xs.length) (input b xs)=some actual ∧
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
  obtain ⟨child,ch,cs,chh,ct⟩ := CompetitorProducedScalar.runtime_run lower l q b xs hv hq hp hd
  have htapes : ∀ i,before.final.tapes (slots i)=CompetitorProducedScalar.input b t xs i := by
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

end NearCubicWires.RepairOrdinary.CompetitorRecordScalar
