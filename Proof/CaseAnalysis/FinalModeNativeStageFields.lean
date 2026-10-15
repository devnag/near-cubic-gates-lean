import Proof.CaseAnalysis.FinalNaturalStageFields
import Proof.CaseAnalysis.FinalNaturalModeAtoms

/-!
Paper C10 chooses one carried class and compiles systematic parity into it.
Each actual call therefore has one native request and one live/residual split.
The THR numerator is A.13.10's natural child sum, with its own native denominator.
The total mathematical supplier uses the checked mixed estimate only on lists
outside the chosen mode; actual site membership eliminates that fallback.
This file supplies semantic fields and conditional stage assembly. Physical
runs and guarded bounds at these NEW denominators remain explicit obligations.
-/

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10ModeNativeStageFields

open NearCubicWires NearCubicWires.ComponentwisePolynomial
open NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairOrdinary.CloseoutWitness
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule
open NearCubicWires.RepairOrdinary.CloseoutFinalC10StageFields
open NearCubicWires.RepairOrdinary.CloseoutFinalC10ExactStagePackage
open NearCubicWires.RepairOrdinary.CloseoutFinalC10NaturalStageFields (stageTarget_pos)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10SupplierCalls
open NearCubicWires.RepairOrdinary.CloseoutFinalC10SupplierAccuracy
open NearCubicWires.RepairSource.CloseoutFinal.C10SumFamilyTransport
open NearCubicWires.RepairSource.CloseoutFinal.C10TailComposeUniform
open NearCubicWires.RepairSource.CloseoutFinal.C10UnionSupplier
open NearCubicWires.RepairSource.CloseoutFinal.C10NaturalModeAtoms
open NearCubicWires.RepairSource.CloseoutFinal.C10SupplierWidth (rowDenominator_pos)
open NearCubicWires.RepairSource.CompetitorRationalGap
open NearCubicWires.SupplierPipeline NearCubicWires.SupplierEstimator
open NearCubicWires.SourceInterfaces NearCubicWires.SupplierWalk

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

/-- A native integer fraction with only the error and positivity already proved. -/
structure FractionEstimate (probability : ℝ) (target : ℕ) where
  num : ℕ
  den : ℕ
  positive : 0 < den
  accurate : |(((num : ℚ) / den : ℚ) : ℝ) - probability| ≤ 1 / (target + 1 : ℕ)

def FractionEstimate.transport {p₁ p₂ : ℝ} {target : ℕ}
    (h : p₁ = p₂) (E : FractionEstimate p₁ target) : FractionEstimate p₂ target where
  num := E.num
  den := E.den
  positive := E.positive
  accurate := by rw [← h]; exact E.accurate

variable (sources : EightSources) (liveScale target : ℕ)

def symmetricEstimate (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) :
    FractionEstimate
      (conjunctionProbability NormalizedSymmetricThresholdCircuit.eval request.circuits) target where
  num := rowAnswer (symmetricFourfoldRows (expanderOf sources) liveScale (fun _ => target))
    request.q request.circuits
  den := rowDenominator (symmetricFourfoldRows (expanderOf sources) liveScale (fun _ => target))
    request.q request.circuits
  positive := rowDenominator_pos _ _ _
  accurate := by
    rw [rowSupplier_eq_ratio]
    exact rowSupplier_error_le _ _ _

def thresholdEstimate (request : FourfoldRequest NormalizedThresholdThresholdCircuit) :
    FractionEstimate
      (conjunctionProbability NormalizedThresholdThresholdCircuit.eval request.circuits) target where
  num := C10ThresholdNaturalSum.nativeNumerator (decompositionOf sources) request liveScale
    (CloseoutFinalC10ThresholdRows.listDenominator (decompositionOf sources) request target)
    (CloseoutFinalC10ThresholdRows.primeCutoff (decompositionOf sources) request target)
  den := C10ThresholdNaturalSum.nativeDenominator request liveScale
    (CloseoutFinalC10ThresholdRows.listDenominator (decompositionOf sources) request target)
    (CloseoutFinalC10ThresholdRows.primeCutoff (decompositionOf sources) request target)
  positive := by
    unfold C10ThresholdNaturalSum.nativeDenominator
    exact Nat.mul_pos (Nat.mul_pos
      (CloseoutFinalC10ThresholdRows.certificate (primeOf sources)
        (decompositionOf sources) request target).cardPositive
      (normalizedOccurrenceListCertificate (expanderOf sources)
        (thresholdFourfoldOccurrences request) liveScale
        (CloseoutFinalC10ThresholdRows.listDenominator (decompositionOf sources)
          request target)).cardPositive) (by positivity)
  accurate := by
    rw [Rat.cast_div, Rat.cast_natCast, Rat.cast_natCast,
      ← C10ThresholdNaturalSum.estimate_eq_ratio]
    exact C10ThresholdNaturalSum.estimate_error_le (decompositionOf sources) request
      (expanderOf sources) (primeOf sources) liveScale target

def mixedEstimate {q : ℕ} {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit}
    (atoms : List (C10TotalDecode.Atom pcpp)) :
    FractionEstimate (conjunctionProbability C10TotalDecode.evaluate atoms) target where
  num := C10ThresholdNaturalFit.numerator sources liveScale target ⟨q, atoms.map atomToUnion⟩
  den := C10ThresholdNaturalFit.denominator sources liveScale target ⟨q, atoms.map atomToUnion⟩
  positive := C10ThresholdNaturalFit.denominator_pos sources liveScale target _
  accurate := by
    rw [C10ThresholdNaturalFit.ratio_eq]
    exact C10ThresholdNaturalSum.mixedRatio_atoms_error_le (decompositionOf sources)
      (expanderOf sources) (primeOf sources) liveScale target atoms

/-- Actual lists choose one native family. The fallback is only for total semantics. -/
def modeEstimate {q : ℕ} {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit}
    (symmetric : Bool) (atoms : List (C10TotalDecode.Atom pcpp)) :
    FractionEstimate (conjunctionProbability C10TotalDecode.evaluate atoms) target := by
  classical
  exact match symmetric with
  | true => if h : ∀ atom ∈ atoms, ModeAtom true atom then
      (symmetricEstimate sources liveScale target ⟨q, atoms.map nativeSymmetricAtom⟩).transport
        (conjunctionProbability_nativeSymmetric atoms h)
      else mixedEstimate sources liveScale target atoms
  | false => if h : ∀ atom ∈ atoms, ModeAtom false atom then
      (thresholdEstimate sources liveScale target ⟨q, atoms.map nativeThresholdAtom⟩).transport
        (conjunctionProbability_nativeThreshold atoms h)
      else mixedEstimate sources liveScale target atoms

/-- Native mode values, useful at the physical printer consumer. -/
theorem modeEstimate_native {q : ℕ} {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit}
    (symmetric : Bool) (atoms : List (C10TotalDecode.Atom pcpp))
    (hmode : ∀ atom ∈ atoms, ModeAtom symmetric atom) :
    ((modeEstimate sources liveScale target symmetric atoms).num,
      (modeEstimate sources liveScale target symmetric atoms).den) =
      if symmetric then
        ((symmetricEstimate sources liveScale target ⟨q, atoms.map nativeSymmetricAtom⟩).num,
          (symmetricEstimate sources liveScale target ⟨q, atoms.map nativeSymmetricAtom⟩).den)
      else
        ((thresholdEstimate sources liveScale target ⟨q, atoms.map nativeThresholdAtom⟩).num,
          (thresholdEstimate sources liveScale target ⟨q, atoms.map nativeThresholdAtom⟩).den) := by
  cases symmetric <;> simp only [modeEstimate, dif_pos hmode, FractionEstimate.transport,
    Bool.false_eq_true, ↓reduceIte]

/-- Error below one gives `N < 2D`; the existing one-bit floor remains sufficient. -/
theorem FractionEstimate.numeric_fit {probability : ℝ} {target : ℕ}
    (E : FractionEstimate probability target) (hp : probability ≤ 1) (ht : 0 < target)
    (denBits width : ℕ) (hd : E.den ≤ 2 ^ denBits) (hw : denBits + 1 ≤ width) :
    E.num < 2 ^ width ∧ E.den < 2 ^ width := by
  have htarget : (1 : ℝ) < (target + 1 : ℕ) := by exact_mod_cast Nat.succ_lt_succ ht
  have herror : (1 : ℝ) / (target + 1 : ℕ) < 1 :=
    (div_lt_one (by positivity)).2 htarget
  have hratio : (((E.num : ℚ) / E.den : ℚ) : ℝ) < 2 := by
    have ha := (abs_le.mp E.accurate).2
    linarith
  have hpos : (0 : ℝ) < E.den := by exact_mod_cast E.positive
  rw [Rat.cast_div, Rat.cast_natCast, Rat.cast_natCast] at hratio
  have hn : E.num < 2 * E.den := by
    exact_mod_cast (div_lt_iff₀ hpos).mp hratio
  constructor
  · apply hn.trans_le
    calc
      2 * E.den ≤ 2 * 2 ^ denBits := Nat.mul_le_mul_left 2 hd
      _ = 2 ^ (denBits + 1) := by rw [pow_succ, Nat.mul_comm]
      _ ≤ _ := Nat.pow_le_pow_right (by decide) hw
  · exact hd.trans_lt (Nat.pow_lt_pow_right (by decide) (by omega))

section Stage

variable (k : ℕ) {gamma : ℝ} (p : Parameters sources gamma)

def stageEstimate (n : ℕ) (x : BitInput n) (bits : List Bool)
    (atoms : List (Atoms sources k p x bits)) :
    FractionEstimate (conjunctionProbability C10TotalDecode.evaluate atoms)
      (stageTarget sources p (stageArity sources k n)) :=
  modeEstimate sources liveScale (stageTarget sources p (stageArity sources k n))
    (BoundedFields.symmetric bits) atoms

/-- Actual site membership selects precisely one native request, never the fallback. -/
theorem stageEstimate_native {n : ℕ} (x : BitInput n) (bits : List Bool) (ph : Phase)
    (address : Fin (2 ^ (pcppOf sources k p x bits).clauseBits))
    (monomial : CircuitMonomial (Atoms sources k p x bits) 4)
    (hmem : monomial ∈ (siteCalls ph (pcppOf sources k p x bits)
      (stageCoordinate sources k p n x bits) C10TotalDecode.Atom.systematic address).monomials) :
    ((stageEstimate sources liveScale k p n x bits monomial.factors).num,
      (stageEstimate sources liveScale k p n x bits monomial.factors).den) =
      if BoundedFields.symmetric bits then
        ((symmetricEstimate sources liveScale (stageTarget sources p (stageArity sources k n))
          ⟨stageArity sources k n, monomial.factors.map nativeSymmetricAtom⟩).num,
         (symmetricEstimate sources liveScale (stageTarget sources p (stageArity sources k n))
          ⟨stageArity sources k n, monomial.factors.map nativeSymmetricAtom⟩).den)
      else
        ((thresholdEstimate sources liveScale (stageTarget sources p (stageArity sources k n))
          ⟨stageArity sources k n, monomial.factors.map nativeThresholdAtom⟩).num,
         (thresholdEstimate sources liveScale (stageTarget sources p (stageArity sources k n))
          ⟨stageArity sources k n, monomial.factors.map nativeThresholdAtom⟩).den) :=
  modeEstimate_native sources liveScale _ _ _
    (actual_site_mode sources k p x bits ph address monomial hmem)

/-- The denominator here is the selected native denominator, not the old union value. -/
def modeStageData (coefficientFloor : ℕ → ℕ) (extra : ℕ) (st : Phase → ℕ)
    (stage : (ph : Phase) → LocalBitMultitape.Machine (218 + (60 + extra)) (st ph))
    (stageFuel : Phase → ℕ → ℕ) (L budget : ℕ → ℕ) : StageData' sources k p :=
  { exactStageData sources k p liveScale coefficientFloor extra st stage stageFuel L budget with
    num := fun n x bits _ monomial => (stageEstimate sources liveScale k p n x bits monomial.factors).num
    den := fun n x bits _ monomial => (stageEstimate sources liveScale k p n x bits monomial.factors).den
    supplier := fun n x bits atoms =>
      ((stageEstimate sources liveScale k p n x bits atoms).num : ℚ) /
        (stageEstimate sources liveScale k p n x bits atoms).den }

variable (coefficientFloor denBits : ℕ → ℕ) (extra : ℕ) (st : Phase → ℕ)
  (stage : (ph : Phase) → LocalBitMultitape.Machine (218 + (60 + extra)) (st ph))
  (stageFuel : Phase → ℕ → ℕ) (L budget : ℕ → ℕ)

local notation "S" => modeStageData sources liveScale k p coefficientFloor extra st
  stage stageFuel L budget

/-- All-list semantic accuracy is already supplied. Remaining bounds name the
actual selected denominators and coefficients; the physical run is still required. -/
theorem modeStageBlock
    (hwidth : ∀ n, denBits n + 1 ≤ stageEntryWidth sources k p coefficientFloor n)
    (hden : ∀ (n : ℕ) (x : BitInput n) (bits : List Bool),
      Soundness.cutoff (constantsOf sources) ≤ n →
      ∀ (ph : Phase) (address : Fin (2 ^ (pcppOf sources k p x bits).clauseBits))
        (monomial : CircuitMonomial (Atoms sources k p x bits) 4),
        monomial ∈ (siteCalls ph (pcppOf sources k p x bits)
          (stageCoordinate sources k p n x bits) C10TotalDecode.Atom.systematic address).monomials →
        (stageEstimate sources liveScale k p n x bits monomial.factors).den ≤ 2 ^ denBits n)
    (ecoef : ∀ (n : ℕ) (x : BitInput n) (bits : List Bool),
      Soundness.cutoff (constantsOf sources) ≤ n →
      ∀ (ph : Phase) (address : Fin (2 ^ (pcppOf sources k p x bits).clauseBits)),
        CoefficientsFit (stageEntryWidth sources k p coefficientFloor n)
          (siteCalls ph (pcppOf sources k p x bits) (stageCoordinate sources k p n x bits)
            C10TotalDecode.Atom.systematic address))
    (hstage : ∀ (n : ℕ) (x : BitInput n) (bits : List Bool),
      Soundness.cutoff (constantsOf sources) ≤ n →
      ∀ ph, ∃ bank scratch,
        StageReady' sources k p S (by dsimp [modeStageData, exactStageData]; omega)
          x bits ph bank scratch)
    (hfuel : ∀ (n : ℕ) (x : BitInput n) (bits : List Bool),
      actualFuel' sources k p S x bits ≤ budget n) : StageBlock' sources k p S where
  he := by dsimp [modeStageData, exactStageData]; omega
  hstage := hstage
  hcoordinate := stage_field_hcoordinate sources k p
  hratio := fun _ _ _ _ _ _ => rfl
  hnum := fun n x bits hn ph address monomial hmem =>
    ((stageEstimate sources liveScale k p n x bits monomial.factors).numeric_fit
      (booleanMean_le_one _) (stageTarget_pos sources p _) (denBits n)
      (stageEntryWidth sources k p coefficientFloor n)
      (hden n x bits hn ph address monomial hmem) (hwidth n)).1
  hden := fun n x bits hn ph address monomial hmem =>
    ((stageEstimate sources liveScale k p n x bits monomial.factors).numeric_fit
      (booleanMean_le_one _) (stageTarget_pos sources p _) (denBits n)
      (stageEntryWidth sources k p coefficientFloor n)
      (hden n x bits hn ph address monomial hmem) (hwidth n)).2
  hdenPos := fun _ _ _ _ _ _ => FractionEstimate.positive _
  hcoefficients := ecoef
  hfailure := by
    intro n _ _ _ _
    change 0 ≤ (1 : ℝ) / ((stageTarget sources p (stageArity sources k n) + 1 : ℕ) : ℝ)
    positivity
  hpoint := fun _ _ _ _ _ _ => FractionEstimate.accurate _
  hmass := stage_field_hmass sources k p
  haccuracy := stage_field_haccuracy_row sources k p
  hthreshold := stage_field_hthreshold sources k p coefficientFloor
  hfuel := hfuel

end Stage

end
end NearCubicWires.RepairOrdinary.CloseoutFinalC10ModeNativeStageFields
