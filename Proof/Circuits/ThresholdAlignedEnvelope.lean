import Proof.Foundations.SupplierPrime

open Finset
open scoped BigOperators

namespace NearCubicWires.ThresholdAlignedEnvelope

open NearCubicWires.ExecutableInterfaces
open NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierPrime

/-! ## §1 The two generic folds -/

/-- Right fold of `max` with neutral `0`; the per-circuit aggregation. -/
def natListMax (values : List ℕ) : ℕ := values.foldr max 0

theorem le_natListMax_of_mem {value : ℕ} {values : List ℕ}
    (hmember : value ∈ values) : value ≤ natListMax values := by
  induction values with
  | nil => simp at hmember
  | cons head tail inductionHypothesis =>
      simp only [natListMax, List.foldr_cons] at *
      rcases List.mem_cons.mp hmember with rfl | htail
      · exact Nat.le_max_left _ _
      · exact le_trans (inductionHypothesis htail) (Nat.le_max_right _ _)

/-- Natural-number Horner fold: `[a₀, a₁, …] ↦ a₀ + base * (a₁ + base * …)`.
Mirrors the shape of `stackEquations` on the magnitude side. -/
def natHornerFold (base : ℕ) : List ℕ → ℕ
  | [] => 0
  | head :: tail => head + base * natHornerFold base tail

/-- The Horner fold is monotone in the base and in every entry. -/
theorem natHornerFold_mono {base base' : ℕ} (hbase : base ≤ base')
    {left right : List ℕ} (hentries : List.Forall₂ (· ≤ ·) left right) :
    natHornerFold base left ≤ natHornerFold base' right := by
  induction hentries with
  | nil => exact le_rfl
  | cons hhead htail inductionHypothesis =>
      simp only [natHornerFold]
      exact Nat.add_le_add hhead (Nat.mul_le_mul hbase inductionHypothesis)

/-- Entrywise domination gives sum domination; feeds the base comparison. -/
theorem sum_le_sum_of_forall₂ {left right : List ℕ}
    (hentries : List.Forall₂ (· ≤ ·) left right) : left.sum ≤ right.sum := by
  induction hentries with
  | nil => exact le_rfl
  | cons hhead _ inductionHypothesis =>
      simp only [List.sum_cons]
      exact Nat.add_le_add hhead inductionHypothesis

/-! ## §2 The stack-magnitude Horner bound (the file's one real lemma) -/

/-- The magnitude of a mixed-radix stack is dominated by the Horner fold of
the per-equation magnitudes at the base's absolute value.  Pure triangle
inequalities — no sign or block condition is needed for the `≤` direction. -/
theorem equationMagnitudeBound_stackEquations_le
    {Carrier : Type} [Fintype Carrier] (base : ℤ)
    (equations : List (LabelledEquation Carrier)) :
    equationMagnitudeBound (stackEquations base equations) ≤
      natHornerFold base.natAbs (equations.map equationMagnitudeBound) := by
  induction equations with
  | nil =>
      simp [stackEquations, equationMagnitudeBound, natHornerFold]
  | cons head tail inductionHypothesis =>
      simp only [List.map_cons, natHornerFold]
      have hweights : ∀ index : Carrier,
          (head.weights index +
              base * (stackEquations base tail).weights index).natAbs ≤
            (head.weights index).natAbs +
              base.natAbs *
                ((stackEquations base tail).weights index).natAbs := by
        intro index
        calc (head.weights index +
                base * (stackEquations base tail).weights index).natAbs ≤
              (head.weights index).natAbs +
                (base * (stackEquations base tail).weights index).natAbs :=
            Int.natAbs_add_le _ _
          _ = (head.weights index).natAbs +
                base.natAbs *
                  ((stackEquations base tail).weights index).natAbs := by
            rw [Int.natAbs_mul]
      have htarget :
          (head.target + base * (stackEquations base tail).target).natAbs ≤
            head.target.natAbs +
              base.natAbs * (stackEquations base tail).target.natAbs := by
        calc (head.target + base * (stackEquations base tail).target).natAbs ≤
              head.target.natAbs +
                (base * (stackEquations base tail).target).natAbs :=
            Int.natAbs_add_le _ _
          _ = head.target.natAbs +
                base.natAbs * (stackEquations base tail).target.natAbs := by
            rw [Int.natAbs_mul]
      have hsum :
          (∑ index, (head.weights index +
              base * (stackEquations base tail).weights index).natAbs) ≤
            (∑ index, (head.weights index).natAbs) +
              base.natAbs * ∑ index,
                ((stackEquations base tail).weights index).natAbs := by
        calc (∑ index, (head.weights index +
                base * (stackEquations base tail).weights index).natAbs) ≤
              ∑ index, ((head.weights index).natAbs +
                base.natAbs *
                  ((stackEquations base tail).weights index).natAbs) :=
            Finset.sum_le_sum fun index _ => hweights index
          _ = (∑ index, (head.weights index).natAbs) +
                base.natAbs * ∑ index,
                  ((stackEquations base tail).weights index).natAbs := by
            rw [Finset.sum_add_distrib, Finset.mul_sum]
      change (∑ index, (head.weights index +
            base * (stackEquations base tail).weights index).natAbs) +
          (head.target + base * (stackEquations base tail).target).natAbs ≤
        equationMagnitudeBound head +
          base.natAbs *
            natHornerFold base.natAbs (tail.map equationMagnitudeBound)
      calc (∑ index, (head.weights index +
              base * (stackEquations base tail).weights index).natAbs) +
            (head.target + base * (stackEquations base tail).target).natAbs ≤
            ((∑ index, (head.weights index).natAbs) +
              base.natAbs * ∑ index,
                ((stackEquations base tail).weights index).natAbs) +
            (head.target.natAbs +
              base.natAbs * (stackEquations base tail).target.natAbs) :=
          Nat.add_le_add hsum htarget
        _ = equationMagnitudeBound head +
              base.natAbs *
                equationMagnitudeBound (stackEquations base tail) := by
          unfold equationMagnitudeBound
          ring
        _ ≤ equationMagnitudeBound head +
              base.natAbs *
                natHornerFold base.natAbs (tail.map equationMagnitudeBound) := by
          gcongr

/-! ## §3 The aligned threshold envelope -/

/-- Magnitude of one raw child gate: total weight mass plus target mass.
Under the segment embedding this equals the embedded child equation's
`equationMagnitudeBound` (bridge proved beside `thresholdChildEquation`). -/
def childMagnitude {arity : ℕ} (gate : ExactThresholdGate arity) : ℕ :=
  (∑ index, (gate.weight index).natAbs) + gate.target.natAbs

/-- Per-circuit aligned magnitude: the maximum child magnitude the selected
decomposition emits for this circuit's retained top gate. -/
def circuitChildMagnitudeMax
    (algorithm : ExecutableExactDecompositionAlgorithm)
    {arity : ℕ} (circuit : NormalizedThresholdThresholdCircuit arity) : ℕ :=
  natListMax ((topChildren algorithm circuit).map childMagnitude)

theorem childMagnitude_le_circuitChildMagnitudeMax
    (algorithm : ExecutableExactDecompositionAlgorithm)
    {arity : ℕ} (circuit : NormalizedThresholdThresholdCircuit arity)
    {child : ExactThresholdGate circuit.top.support.card}
    (hmember : child ∈ topChildren algorithm circuit) :
    childMagnitude child ≤ circuitChildMagnitudeMax algorithm circuit :=
  le_natListMax_of_mem (List.mem_map.mpr ⟨child, hmember, rfl⟩)

/-- The per-request list of per-circuit aligned magnitudes. -/
def alignedMagnitudeList
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit) :
    List ℕ :=
  request.circuits.map fun circuit =>
    circuitChildMagnitudeMax algorithm circuit

@[simp] theorem alignedMagnitudeList_length
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit) :
    (alignedMagnitudeList algorithm request).length =
      request.circuits.length := by
  simp [alignedMagnitudeList]

/-- The aligned stacking base: dominates `equationListBase` of every
selection because entrywise the selection magnitudes sit below the aligned
maxima (`sum_le_sum_of_forall₂`). -/
def alignedStackBase
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit) : ℕ :=
  (alignedMagnitudeList algorithm request).sum + 1

/-- The aligned family envelope `G*`: the Horner combination of the aligned
per-circuit magnitudes at the aligned base.  Polynomial bit-length. -/
def alignedFamilyEnvelope
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit) : ℕ :=
  natHornerFold (alignedStackBase algorithm request)
    (alignedMagnitudeList algorithm request)

def alignedFamilyExponent
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit) : ℕ :=
  Nat.clog 2 (alignedFamilyEnvelope algorithm request + 1)

/-- Anything dominated by the aligned envelope sits strictly below the
aligned power of two — the exact shape the soundness consumer needs. -/
theorem lt_two_pow_alignedFamilyExponent
    (algorithm : ExecutableExactDecompositionAlgorithm)
    (request : FourfoldRequest NormalizedThresholdThresholdCircuit)
    {value : ℕ}
    (hvalue : value ≤ alignedFamilyEnvelope algorithm request) :
    value < 2 ^ alignedFamilyExponent algorithm request :=
  lt_of_lt_of_le (Nat.lt_succ_of_le hvalue)
    (Nat.le_pow_clog one_lt_two _)

end NearCubicWires.ThresholdAlignedEnvelope
