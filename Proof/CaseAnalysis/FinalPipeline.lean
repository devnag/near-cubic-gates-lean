import Proof.CaseAnalysis.FinalVerdict
import Proof.CaseAnalysis.FinalOneSidedness
import Proof.CaseAnalysis.FinalSupplierStepBridge

/-! Paper C.10 rejects malformed, noncanonical and oversized descriptions before
running the estimators. Each input therefore supplies either an actual rejecting
run or the existing estimate-bearing Verdict over that same worker and budget.
The two cases jointly supply totality; only the Verdict case can accept and
therefore contributes the accuracy facts consumed by C.12. Completeness remains
in the unchanged pinned SymDecides/ThrDecides consumers of the same worker. -/
namespace NearCubicWires.RepairSource.CloseoutFinal.C10Fusion

open LocalBitMultitape RepairOrdinary RepairOrdinary.CloseoutWitness
open RepairRepresentation CompetitorRationalGap ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.CloseoutFinalC10Realizes
open NearCubicWires.RepairSource.CloseoutFinal.C10Verdict
open NearCubicWires.RepairSource.CloseoutFinal
open CloseoutRowsOriginalSchedule SelectedRecoveryIntegration CloseoutLanguage
open NearCubicWires.SourceInterfaces

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (sources : EightSources) (k : Nat) (clock : OrdinaryClock (fun n => n^(k+2)))

/-- A real rejecting run at the worker's own input and budget. -/
def RejectedAt {t s : ℕ} (p : Machine t s) (ht : 2 ≤ t) (result : Fin t)
    (fuel : ℕ → ℕ) (n : ℕ) (x : BitInput n) (bits : List Bool) : Prop :=
  ∃ heads exit, Step p (fuel n) (fun _ => 0)
    ((UAcceptanceCarrier.verifier p ht result).inputTapes (List.ofFn x) bits) heads exit ∧
    readTapeBit (exit result) (heads result) = false

/-- The original estimated branch payload, needed only when validation runs on. -/
def EstimatedAt {t s : ℕ} (constants : Constants (selectedPCPP sources))
    (p : Machine t s) (ht : 2 ≤ t) (result : Fin t) (fuel : ℕ → ℕ)
    (n : ℕ) (x : BitInput n) (bits : List Bool) : Type 1 :=
  Σ' (oracle : BooleanCircuit ((outer sources k clock).result.pcp.nativeWidth n))
     (_Atom : Type)
     (proofValue : BitInput (req sources k clock x oracle).arity →
       Fin ((pcppAt sources k clock x oracle).systematicBits
         + (pcppAt sources k clock x oracle).auxiliaryBits) → ℝ)
     (evaluate : _Atom → BitInput (req sources k clock x oracle).arity → Bool)
     (ports : Phase → Fin t)
     (width : Phase → ℕ),
     Verdict constants (pcppAt sources k clock x oracle) proofValue evaluate
       p ht fuel n x bits result ports width

/-- One physical rejecting or estimated branch at every input. -/
def Pipeline {t s : ℕ} (constants : Constants (selectedPCPP sources))
    (p : Machine t s) (ht : 2 ≤ t) (result : Fin t) (fuel : ℕ → ℕ) : Type 1 :=
  (n : ℕ) → (x : BitInput n) → (bits : List Bool) →
    PSum (RejectedAt p ht result fuel n x bits)
      (EstimatedAt sources k clock constants p ht result fuel n x bits)

/-- Rejection excludes acceptance of the same machine at the same input/budget. -/
theorem rejected_not_decides {t s : ℕ} {p : Machine t s} {ht : 2 ≤ t}
    {result : Fin t} {fuel : ℕ → ℕ} {n : ℕ} {x : BitInput n} {bits : List Bool}
    (h : RejectedAt p ht result fuel n x bits) :
    ¬ Weak.decides p ht result fuel n x bits := by
  obtain ⟨heads, exit, hstep, hfalse⟩ := h
  obtain ⟨r, hr, hheads, htapes, _hsteps⟩ := hstep
  rintro ⟨actual, hrun, hscan⟩
  have hsame : actual = r := Option.some.inj (hrun.symm.trans hr)
  subst actual
  have hbit : readTapeBit (exit result) (heads result) = true := by
    rw [← htapes, ← hheads]
    exact hscan
  exact Bool.false_ne_true (hfalse.symm.trans hbit)

/-- **The supplier's halting fact**, read straight off `Verdict.run`. -/
theorem stepAtInputs_of_pipeline {t s : ℕ} {constants : Constants (selectedPCPP sources)}
    {p : Machine t s} {ht : 2 ≤ t} {result : Fin t} {fuel : ℕ → ℕ}
    (P : Pipeline sources k clock constants p ht result fuel) :
    Weak.StepAtInputs p ht result fuel := by
  intro n x bits
  cases P n x bits with
  | inl rejected =>
    obtain ⟨heads, exit, hrun, _hfalse⟩ := rejected
    exact ⟨heads, exit, hrun⟩
  | inr estimated =>
    obtain ⟨_oracle, _Atom, _proofValue, _evaluate, _ports, _width, V⟩ := estimated
    exact ⟨V.heads, V.exit, V.run⟩

/-- **Paper C.12's accuracy facts**, from the same object. -/
theorem exposes_of_pipeline {t s : ℕ} {constants : Constants (selectedPCPP sources)}
    {p : Machine t s} {ht : 2 ≤ t} {result : Fin t} {fuel : ℕ → ℕ}
    (P : Pipeline sources k clock constants p ht result fuel) :
    Exposes sources k clock constants (Weak.decides p ht result fuel) := by
  intro n x bits hm
  cases P n x bits with
  | inl rejected => exact (rejected_not_decides rejected hm).elim
  | inr estimated =>
    obtain ⟨oracle, _Atom, proofValue, _evaluate, _ports, _width, V⟩ := estimated
    obtain ⟨actual, hrun, hscan⟩ := hm
    obtain ⟨r, hr, hheads, htapes, _hsteps⟩ := V.run
    -- `run p fuel tin = runFrom p fuel ⟨p.start, fun _ => 0, tin⟩` definitionally,
    -- so the caller's receipt IS the verdict's receipt.
    have hsame : actual = r := by
      -- `run p fuel tin` is by definition `runFrom p fuel (initialConfiguration p tin)`,
      -- and `initialConfiguration` has heads uniformly `0` -- so `hr` IS a `run` fact.
      have h2 : run p (fuel n)
          ((UAcceptanceCarrier.verifier p ht result).inputTapes (List.ofFn x) bits) = some r := hr
      exact Option.some.inj (hrun.symm.trans h2)
    subst hsame
    have hbit : readTapeBit (V.exit result) (V.heads result) = true := by
      rw [← htapes, ← hheads]
      exact hscan
    obtain ⟨hcut, hp, hmom, hcl⟩ := V.accepts_iff.mp hbit
    refine ⟨hcut, oracle, proofValue, V.estimate .penalty, V.estimate .moment,
      V.estimate .clause, hp, hmom, hcl, ?_, ?_, ?_⟩
    · have h := accurate_of_verdict V hcut .penalty
      rwa [penalty_mean] at h
    · have h := accurate_of_verdict V hcut .moment
      rwa [moment_mean] at h
    · have h := accurate_of_verdict V hcut .clause
      rwa [clause_mean] at h

end
end NearCubicWires.RepairSource.CloseoutFinal.C10Fusion
