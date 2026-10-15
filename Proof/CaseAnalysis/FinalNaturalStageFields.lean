import Proof.CaseAnalysis.FinalExactStagePackage
import Proof.CaseAnalysis.FinalThresholdNaturalFit

/-!
An exact C10 stage adapter at A.13.10's natural child sum. Only the numerator
and rational supplier change; the native denominator, fixed accuracy target,
record width, coordinate expansion and machine budget remain the selected ones.
All numeric envelopes below are guarded by actual site membership. The final
constructor retains the physical stage run and its actual fuel as premises.
This mixed-row adapter does not select a physical printer: the left and right
row producers have separate live-set choices. The paper's mode-native parity
route may replace these values; no shared-live-set identity is assumed here.
-/

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10NaturalStageFields

open NearCubicWires NearCubicWires.ComponentwisePolynomial
open NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairOrdinary.CloseoutWitness
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule
open NearCubicWires.RepairOrdinary.CloseoutFinalC10StageFields
open NearCubicWires.RepairOrdinary.CloseoutFinalC10ExactStagePackage
open NearCubicWires.RepairOrdinary.CloseoutFinalC10SupplierCalls
open NearCubicWires.RepairOrdinary.CloseoutFinalC10SupplierAccuracy
open NearCubicWires.RepairSource.CloseoutFinal.C10SumFamilyTransport
open NearCubicWires.RepairSource.CloseoutFinal.C10TailComposeUniform
open NearCubicWires.RepairSource.CloseoutFinal.C10UnionSupplier
open NearCubicWires.RepairSource.CompetitorRationalGap
open NearCubicWires.SupplierPipeline NearCubicWires.SourceInterfaces

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (sources : EightSources) (k : ℕ) {gamma : ℝ} (p : Parameters sources gamma)

/-- The actual natural count on mixed atoms, including systematic parity atoms. -/
def naturalNum (liveScale : ℕ) :
    (n : ℕ) → (x : BitInput n) → (bits : List Bool) →
      Fin (2 ^ (pcppOf sources k p x bits).clauseBits) →
      CircuitMonomial (Atoms sources k p x bits) 4 → ℕ :=
  fun n _ _ _ monomial => C10ThresholdNaturalFit.numerator sources liveScale
    (stageTarget sources p (stageArity sources k n))
    ⟨stageArity sources k n, monomial.factors.map atomToUnion⟩

/-- The mixed rational estimate uses the same fixed accuracy reserve. -/
def naturalSupplier (liveScale : ℕ) :
    (n : ℕ) → (x : BitInput n) → (bits : List Bool) → List (Atoms sources k p x bits) → ℚ :=
  fun n _ _ atoms => C10ThresholdNaturalSum.mixedRatio (decompositionOf sources)
    (expanderOf sources) liveScale (stageTarget sources p (stageArity sources k n))
    ⟨stageArity sources k n, atoms.map atomToUnion⟩

theorem stageTarget_pos (q : ℕ) : 0 < stageTarget sources p q :=
  C10ThresholdNaturalFit.accuracyTargetAll_pos (constantsOf sources) (stageLimits sources p)
    (CloseoutSampledWitness.mass_nonneg _ p.hd p.hh p.copies)

/-- A.13.10 retains exactly the existing native denominator, with no child divisor. -/
theorem naturalDen_eq {n : ℕ} (x : BitInput n) (bits : List Bool) (liveScale : ℕ)
    (address : Fin (2 ^ (pcppOf sources k p x bits).clauseBits))
    (monomial : CircuitMonomial (Atoms sources k p x bits) 4) :
    C10ThresholdNaturalFit.denominator sources liveScale
      (stageTarget sources p (stageArity sources k n))
      ⟨stageArity sources k n, monomial.factors.map atomToUnion⟩ =
        stageDen sources k p liveScale n x bits address monomial :=
  C10ThresholdNaturalFit.denominator_eq_rowDenominator sources liveScale
    (stageTarget sources p (stageArity sources k n)) _

theorem natural_hratio (liveScale : ℕ) {n : ℕ} (x : BitInput n) (bits : List Bool)
    (address : Fin (2 ^ (pcppOf sources k p x bits).clauseBits))
    (monomial : CircuitMonomial (Atoms sources k p x bits) 4) :
    (naturalNum sources k p liveScale n x bits address monomial : ℚ) /
      stageDen sources k p liveScale n x bits address monomial =
        naturalSupplier sources k p liveScale n x bits monomial.factors := by
  rw [← naturalDen_eq sources k p x bits liveScale address monomial]
  exact C10ThresholdNaturalFit.ratio_eq sources liveScale
    (stageTarget sources p (stageArity sources k n)) _

theorem natural_hpoint (liveScale : ℕ) {n : ℕ} (x : BitInput n) (bits : List Bool)
    (atoms : List (Atoms sources k p x bits)) :
    |(naturalSupplier sources k p liveScale n x bits atoms : ℝ) -
        conjunctionProbability C10TotalDecode.evaluate atoms| ≤
      1 / ((stageTarget sources p (stageArity sources k n) + 1 : ℕ) : ℝ) :=
  C10ThresholdNaturalSum.mixedRatio_atoms_error_le (decompositionOf sources)
    (expanderOf sources) (primeOf sources) liveScale
    (stageTarget sources p (stageArity sources k n)) atoms

/-- Both numeric fits use the already reserved extra bit. No `num ≤ den` is assumed. -/
theorem natural_numeric_fit (liveScale seedBits width : ℕ) {n : ℕ}
    (x : BitInput n) (bits : List Bool)
    (address : Fin (2 ^ (pcppOf sources k p x bits).clauseBits))
    (monomial : CircuitMonomial (Atoms sources k p x bits) 4)
    (hrows : (unionAtomRows sources liveScale (stageTarget sources p)).rowCount
      ⟨stageArity sources k n, monomial.factors.map atomToUnion⟩ ≤ 2 ^ seedBits)
    (hwidth : stageArity sources k n + seedBits + 1 ≤ width) :
    naturalNum sources k p liveScale n x bits address monomial < 2 ^ width ∧
      stageDen sources k p liveScale n x bits address monomial < 2 ^ width := by
  constructor
  · exact C10ThresholdNaturalFit.numerator_lt_two_pow_of_rowCount sources liveScale
      (stageTarget sources p (stageArity sources k n)) seedBits width
      (stageTarget_pos sources p _) _ hrows hwidth
  · have hd : stageDen sources k p liveScale n x bits address monomial ≤
        2 ^ seedBits * 2 ^ stageArity sources k n := Nat.mul_le_mul_right _ hrows
    apply hd.trans_lt
    rw [← pow_add, Nat.add_comm]
    exact Nat.pow_lt_pow_right (by decide) (by omega)

/-- Reuse the exact stage data and replace only the two A.13.10 value fields. -/
def naturalStageData (liveScale : ℕ) (coefficientFloor : ℕ → ℕ) (extra : ℕ)
    (st : Phase → ℕ)
    (stage : (ph : Phase) → LocalBitMultitape.Machine (218 + (60 + extra)) (st ph))
    (stageFuel : Phase → ℕ → ℕ) (L budget : ℕ → ℕ) : StageData' sources k p :=
  { exactStageData sources k p liveScale coefficientFloor extra st stage stageFuel L budget with
    num := naturalNum sources k p liveScale
    supplier := naturalSupplier sources k p liveScale }

section Assembly

variable (liveScale : ℕ) (coefficientFloor seedBits : ℕ → ℕ) (extra : ℕ)
  (st : Phase → ℕ)
  (stage : (ph : Phase) → LocalBitMultitape.Machine (218 + (60 + extra)) (st ph))
  (stageFuel : Phase → ℕ → ℕ) (L budget : ℕ → ℕ)

local notation "S" => naturalStageData sources k p liveScale coefficientFloor extra st
  stage stageFuel L budget

/-- Value changes do not alter record counts or the demanded machine fuel.
This transports an existing budget proof; it does not produce the new records. -/
theorem natural_actualFuel_eq {n : ℕ} (x : BitInput n) (bits : List Bool) :
    actualFuel' sources k p S x bits =
      actualFuel' sources k p
        (exactStageData sources k p liveScale coefficientFloor extra st stage stageFuel L budget)
        x bits := by
  let T := exactStageData sources k p liveScale coefficientFloor extra st stage stageFuel L budget
  have hemit (ph : Phase) : emissionFuel sources k p (shell sources k p S) x bits ph =
      emissionFuel sources k p (shell sources k p T) x bits ph := by
    funext tick
    simp only [emissionFuel, records, shell, naturalStageData, T, exactStageData]
  have hphase : phaseFuel sources k p (shell sources k p S) x bits =
      phaseFuel sources k p (shell sources k p T) x bits := by
    funext ph
    rw [phaseFuel, phaseFuel, hemit]
    simp only [records, shell, naturalStageData, T, exactStageData]
  have hwidth : widthOf sources k p (shell sources k p S) x bits =
      widthOf sources k p (shell sources k p T) x bits := by
    funext ph
    simp only [widthOf, records, shell, naturalStageData, T, exactStageData]
  rw [actualFuel'_shell, actualFuel'_shell]
  unfold actualFuel
  rw [hphase, hwidth]

/-- Consumer check at the actual natural stage. Residuals are the guarded row
envelope and coefficient fit, the physical stage run, and that same stage's fuel.
All semantic fields are supplied here; no new accuracy or cost allowance is added. -/
theorem naturalStageBlock
    (hwidth : ∀ n, stageArity sources k n + seedBits n + 1 ≤
      stageEntryWidth sources k p coefficientFloor n)
    (hrows : ∀ (n : ℕ) (x : BitInput n) (bits : List Bool),
      Soundness.cutoff (constantsOf sources) ≤ n →
      ∀ (ph : Phase) (address : Fin (2 ^ (pcppOf sources k p x bits).clauseBits))
        (monomial : CircuitMonomial (Atoms sources k p x bits) 4),
        monomial ∈ (siteCalls ph (pcppOf sources k p x bits)
          (stageCoordinate sources k p n x bits) C10TotalDecode.Atom.systematic address).monomials →
        (unionAtomRows sources liveScale (stageTarget sources p)).rowCount
          ⟨stageArity sources k n, monomial.factors.map atomToUnion⟩ ≤ 2 ^ seedBits n)
    (ecoef : ∀ (n : ℕ) (x : BitInput n) (bits : List Bool),
      Soundness.cutoff (constantsOf sources) ≤ n →
      ∀ (ph : Phase) (address : Fin (2 ^ (pcppOf sources k p x bits).clauseBits)),
        CoefficientsFit (stageEntryWidth sources k p coefficientFloor n)
          (siteCalls ph (pcppOf sources k p x bits) (stageCoordinate sources k p n x bits)
            C10TotalDecode.Atom.systematic address))
    (hstage : ∀ (n : ℕ) (x : BitInput n) (bits : List Bool),
      Soundness.cutoff (constantsOf sources) ≤ n →
      ∀ ph, ∃ bank scratch,
        StageReady' sources k p S (by dsimp [naturalStageData, exactStageData]; omega)
          x bits ph bank scratch)
    (hfuel : ∀ (n : ℕ) (x : BitInput n) (bits : List Bool),
      actualFuel' sources k p S x bits ≤ budget n) : StageBlock' sources k p S where
  he := by dsimp [naturalStageData, exactStageData]; omega
  hstage := hstage
  hcoordinate := stage_field_hcoordinate sources k p
  hratio := fun _ x bits _ address monomial =>
    natural_hratio sources k p liveScale x bits address monomial
  hnum := fun n x bits hn ph address monomial hmem =>
    (natural_numeric_fit sources k p liveScale (seedBits n)
      (stageEntryWidth sources k p coefficientFloor n) x bits address monomial
      (hrows n x bits hn ph address monomial hmem) (hwidth n)).1
  hden := fun n x bits hn ph address monomial hmem =>
    (natural_numeric_fit sources k p liveScale (seedBits n)
      (stageEntryWidth sources k p coefficientFloor n) x bits address monomial
      (hrows n x bits hn ph address monomial hmem) (hwidth n)).2
  hdenPos := stage_field_hdenPos sources k p liveScale
  hcoefficients := ecoef
  hfailure := by
    intro n _ _ _ _
    change 0 ≤ (1 : ℝ) / ((stageTarget sources p (stageArity sources k n) + 1 : ℕ) : ℝ)
    positivity
  hpoint := fun _ x bits _ _ circuits => natural_hpoint sources k p liveScale x bits circuits
  hmass := stage_field_hmass sources k p
  haccuracy := stage_field_haccuracy_row sources k p
  hthreshold := stage_field_hthreshold sources k p coefficientFloor
  hfuel := hfuel

end Assembly

end
end NearCubicWires.RepairOrdinary.CloseoutFinalC10NaturalStageFields
