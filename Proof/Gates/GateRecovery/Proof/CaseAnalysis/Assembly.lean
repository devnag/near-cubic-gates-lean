import Proof.Gates.GateRecovery.Bundle
import Proof.Foundations.SourceRegistry
import Proof.Amplification.RecoveryEncodedNPVerifier

namespace GR

namespace NearCubicWires.RepairSource.Closeout
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def RecoveryRuns (language : ℝ → Language) : Prop :=
  ∀ gamma, 0 < gamma → gamma < 1 / 2 →
    Nonempty (OrdinaryENPCertificate RecoveryOracle.correctedSat (language gamma))

def SymmetricHardness (language : ℝ → Language) (coefficient : ℝ → ℝ) : Prop :=
  ∀ gamma, 0 < gamma → gamma < 1 / 2 →
    0 < coefficient gamma ∧ ∃ onset, ∀ n, onset ≤ n →
      ∀ circuit : SymmetricThresholdCircuit n,
        (circuit.wireCount : ℝ) ≤ wireScale (coefficient gamma) 5 n →
        agreement circuit.eval (language gamma n) < 1 / 2 + gamma

def ThresholdHardness (language : ℝ → Language) (coefficient : ℝ → ℝ) : Prop :=
  ∀ gamma, 0 < gamma → gamma < 1 / 2 →
    0 < coefficient gamma ∧ ∃ onset, ∀ n, onset ≤ n →
      ∀ circuit : ThresholdThresholdCircuit n,
        (circuit.wireCount : ℝ) ≤ wireScale (coefficient gamma) 9 n →
        agreement circuit.eval (language gamma n) < 1 / 2 + gamma

theorem membership (language : Language)
    (certificate : OrdinaryENPCertificate RecoveryOracle.correctedSat language) :
    OrdinaryInENP language :=
  ⟨RecoveryOracle.correctedSat, ⟨RepairOrdinary.RecoveryColdVerifier.encodedNPVerifier⟩,
    ⟨certificate⟩⟩

theorem assemble (language : ℝ → Language) (symmetricCoefficient thresholdCoefficient : ℝ → ℝ)
    (recovery : RecoveryRuns language)
    (symmetric : SymmetricHardness language symmetricCoefficient)
    (threshold : ThresholdHardness language thresholdCoefficient) :
    OrdinaryHeadlineTheorem25 := by
  intro gamma hgamma hhalf
  obtain ⟨certificate⟩ := recovery gamma hgamma hhalf
  obtain ⟨hsym, symOnset, symHard⟩ := symmetric gamma hgamma hhalf
  obtain ⟨hthr, thrOnset, thrHard⟩ := threshold gamma hgamma hhalf
  refine ⟨language gamma, symmetricCoefficient gamma, thresholdCoefficient gamma,
    membership _ certificate, hsym, hthr, max symOnset thrOnset, ?_⟩
  intro n hn
  constructor
  · intro circuit hagree
    by_contra hcap
    exact (not_lt_of_ge hagree) (symHard n ((Nat.le_max_left _ _).trans hn)
      circuit (le_of_not_gt hcap))
  · intro circuit hagree
    by_contra hcap
    exact (not_lt_of_ge hagree) (thrHard n ((Nat.le_max_right _ _).trans hn)
      circuit (le_of_not_gt hcap))

/-- This is the exact local producer obligation, not another imported source. -/
def LocalSuppliers : Prop :=
  ∃ language symmetricCoefficient thresholdCoefficient,
    RecoveryRuns language ∧ SymmetricHardness language symmetricCoefficient ∧
      ThresholdHardness language thresholdCoefficient

theorem from_local_suppliers (supply : GateEightSources → LocalSuppliers)
    (sources : GateEightSources) : OrdinaryHeadlineTheorem25 := by
  obtain ⟨language, sym, thr, recovery, symmetric, threshold⟩ := supply sources
  exact assemble language sym thr recovery symmetric threshold

end NearCubicWires.RepairSource.Closeout

end GR
