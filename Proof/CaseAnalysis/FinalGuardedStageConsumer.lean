import Proof.CaseAnalysis.FinalPipeline
import Proof.CaseAnalysis.FinalTailComposeVerdict

/-! Local adapters for paper C.10's syntactic rejection path. They preserve
actual machine, input, exit and fuel. Physical admission/cache and continuation
receipts remain explicit; none is supplied by this module. The fixed onset may
exceed the source's soundness cutoff. -/
namespace NearCubicWires.RepairSource.CloseoutFinal.C10GuardedStageConsumer
open LocalBitMultitape RepairOrdinary RepairOrdinary.CloseoutWitness
open RepairRepresentation CompetitorRationalGap ExtDecompositionBatch
open CloseoutRowsOriginalSchedule SelectedRecoveryIntegration CloseoutLanguage SourceInterfaces
open C10LengthGate C10Verdict C10Fusion
open RepairOrdinary.CloseoutFinalC10Realizes

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

/-- The existing one-step physical decision switch after the actual admission
admission. Failure writes false and halts; success continues from the exact cache. -/
def admittedInner {t a b : ℕ} (admission : Machine t a) (continuation : Machine t b)
    (admissionFlag result : Fin t) :=
  Composition.machine admission (branch admissionFlag result continuation)

/-- One fixed larger onset, followed by the actual admission/continuation code. -/
def admittedWorker {t a b : ℕ} (onset : ℕ) (admission : Machine t a)
    (continuation : Machine t b) (input lengthFlag admissionFlag result : Fin t) :=
  gated onset input lengthFlag result (admittedInner admission continuation admissionFlag result)

theorem inner_reject {t a b : ℕ} (admission : Machine t a) (continuation : Machine t b)
    (admissionFlag result : Fin t) (preFuel : ℕ)
    (H Hpre : Fin t → ℕ) (T Tpre : Fin t → List Bool)
    (hpre : Step admission preFuel H T Hpre Tpre)
    (hfalse : readTapeBit (Tpre admissionFlag) (Hpre admissionFlag) = false) :
    Step (admittedInner admission continuation admissionFlag result) (preFuel+1+1)
      H T Hpre (exitTapes result Tpre (Hpre result) false) :=
  hpre.seq (branch_reject admissionFlag result continuation Hpre Tpre hfalse)

theorem inner_pass {t a b : ℕ} (admission : Machine t a) (continuation : Machine t b)
    (admissionFlag result : Fin t) (preFuel bodyFuel : ℕ)
    (H Hpre Hout : Fin t → ℕ) (T Tpre Tout : Fin t → List Bool)
    (hpre : Step admission preFuel H T Hpre Tpre)
    (htrue : readTapeBit (Tpre admissionFlag) (Hpre admissionFlag) = true)
    (hbody : Step continuation bodyFuel Hpre Tpre Hout Tout) :
    Step (admittedInner admission continuation admissionFlag result) (preFuel+1+(bodyFuel+1))
      H T Hout Tout :=
  hpre.seq (branch_pass admissionFlag result continuation Hpre Tpre htrue bodyFuel Hout Tout hbody)

/-- Same-machine rejected/admitted receipts suffice for the revised Pipeline.
There is deliberately no requirement that every input above the cutoff emit
records. The admitted payload is supplied only at the chosen onset and flag. -/
def pipeline_of_guarded (sources : EightSources) (k : ℕ)
    (clock : OrdinaryClock (fun n => n^(k+2))) (constants : Constants (selectedPCPP sources))
    {t s : ℕ} (worker : Machine t s) (ht : 2 ≤ t) (result : Fin t) (fuel : ℕ → ℕ)
    (onset : ℕ) (passed : (n : ℕ) → BitInput n → List Bool → Bool)
    (rejected : ∀ n x bits, n < onset ∨ passed n x bits = false →
      RejectedAt worker ht result fuel n x bits)
    (estimated : ∀ n x bits, onset ≤ n → passed n x bits = true →
      EstimatedAt sources k clock constants worker ht result fuel n x bits) :
    Pipeline sources k clock constants worker ht result fuel := by
  intro n x bits
  by_cases hn : onset ≤ n
  · by_cases hp : passed n x bits = true
    · exact PSum.inr (estimated n x bits hn hp)
    · exact PSum.inl (rejected n x bits (Or.inr (Bool.eq_false_iff.mpr hp)))
  · exact PSum.inl (rejected n x bits (Or.inl (by omega)))

/-- A larger fixed rejection onset supplies the old Verdict's length gate.
The state lower bound is retained explicitly; the concrete admittedWorker has
at least its counter's 4*onset+2 states. -/
theorem gate_of_rejected_below {t s : ℕ} {source : PointwisePCPPAlgorithm}
    (constants : Constants source) (worker : Machine t s) (ht : 2 ≤ t)
    (result : Fin t) (fuel : ℕ → ℕ) (onset : ℕ)
    (hcut : Soundness.cutoff constants ≤ onset) (hstates : Soundness.cutoff constants ≤ s)
    (rejected : ∀ n x bits, n < onset → RejectedAt worker ht result fuel n x bits) :
    LengthGate constants worker ht result fuel where
  hstates := hstates
  rejects := by
    intro n x bits hn actual hrun
    apply Bool.eq_false_iff.mpr
    intro htrue
    exact rejected_not_decides (rejected n x bits (by omega)) ⟨actual, hrun, htrue⟩

/-- Assemble the unchanged Verdict from three phase realizations already
transported onto the actual selected worker, run and ports. This is conditional
assembly; producing those phase records remains a physical obligation. -/
def verdict_of_admitted {t s : ℕ} {Atom : Type} {arity : ℕ}
    {circuit : BooleanCircuit arity} {source : PointwisePCPPAlgorithm}
    (constants : Constants source) (pcpp : PointwisePCPP circuit)
    (proofValue : BitInput arity → Fin (pcpp.systematicBits+pcpp.auxiliaryBits) → ℝ)
    (evaluate : Atom → BitInput arity → Bool)
    (worker : Machine t s) (ht : 2 ≤ t) (fuel : ℕ → ℕ)
    (n : ℕ) (x : BitInput n) (bits : List Bool)
    (result : Fin t) (ports : Phase → Fin t) (width : Phase → ℕ)
    (gate : LengthGate constants worker ht result fuel)
    (hcut : Soundness.cutoff constants ≤ n)
    (heads : Fin t → ℕ) (exit : Fin t → List Bool)
    (hrun : Step worker (fuel n) (fun _ => 0)
      ((UAcceptanceCarrier.verifier worker ht result).inputTapes (List.ofFn x) bits) heads exit)
    (phase : ∀ ph, Realizes ph constants pcpp proofValue evaluate worker (fuel n) (fun _ => 0)
      ((UAcceptanceCarrier.verifier worker ht result).inputTapes (List.ofFn x) bits) (ports ph) (width ph))
    (htest : readTapeBit (exit result) (heads result) = true ↔
      (((phase .penalty).result.value : ℚ) : ℝ) ≤ bound constants .penalty ∧
      (((phase .moment).result.value : ℚ) : ℝ) ≤ bound constants .moment ∧
      bound constants .clause ≤ (((phase .clause).result.value : ℚ) : ℝ)) :
    Verdict constants pcpp proofValue evaluate worker ht fuel n x bits result ports width where
  gate := gate
  heads := heads
  exit := exit
  run := hrun
  realizes := fun _ ph => phase ph
  hshared := by
    intro _ ph
    obtain ⟨r, hr, _hh, htape, _hs⟩ := hrun
    obtain ⟨rp, hrp, _hhp, htapep, _hsp⟩ := (phase ph).run
    have heq : rp = r := Option.some.inj (hrp.symm.trans hr)
    rw [heq] at htapep
    exact htapep.symm.trans htape
  estimate := fun ph => (((phase ph).result.value : ℚ) : ℝ)
  hestimate := fun _ _ => rfl
  accepts_iff := htest.trans ⟨fun h => ⟨hcut, h⟩, fun h => h.2⟩

end
end NearCubicWires.RepairSource.CloseoutFinal.C10GuardedStageConsumer
