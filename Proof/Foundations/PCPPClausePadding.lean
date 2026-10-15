import Proof.Foundations.PaddedOracleRestriction
import Proof.Foundations.ProjectionWidthEnvelope
import Proof.Foundations.SupplierPrinter

/-!
# Branch-independent PCPP clause padding

The pointwise PCPP may return a circuit-dependent clause-address width.  The
headline schedule, however, must be fixed before the Case-1/Case-2 split.  This
module derives one source-only width envelope and repeats every native clause
over the added high address bits.  The repetition preserves the exact
acceptance fraction and keeps every padded query on the factory's one fixed
clause runner.
-/

namespace NearCubicWires.PCPPClausePadding

open Finset
open NearCubicWires
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PaddedOracleRestriction
open NearCubicWires.PolynomialClock
open NearCubicWires.ProjectionPCPPadding
open NearCubicWires.ProjectionWidthEnvelope
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierPrinter

def clauseAddressEquiv (native padded : ℕ) (hwidth : native ≤ padded) :
    Fin (2 ^ padded) ≃ Fin (2 ^ (padded - native)) × Fin (2 ^ native) := by
  let cast :
      Fin (2 ^ padded) ≃ Fin (2 ^ (padded - native) * 2 ^ native) :=
    finCongr (by
      rw [← Nat.pow_add, Nat.sub_add_cancel hwidth])
  exact cast.trans finProdFinEquiv.symm

def repeatedClauseIndex {native padded : ℕ} (hwidth : native ≤ padded)
    (index : Fin (2 ^ padded)) : Fin (2 ^ native) :=
  (clauseAddressEquiv native padded hwidth index).2

theorem binaryAddress_val_eq_ofBits {width : ℕ} (bits : BitInput width) :
    (binaryAddress bits).val = Nat.ofBits bits := by
  unfold binaryAddress
  change
    encodeBitInput bits % 2 ^ width =
      Nat.ofBits bits
  rw [encodeBitInput_eq_ofBits]
  exact Nat.mod_eq_of_lt (Nat.ofBits_lt_two_pow bits)

theorem ofBits_prefix_mod
    {native padded : ℕ} (hwidth : native ≤ padded)
    (bits : BitInput padded) :
    Nat.ofBits bits % 2 ^ native =
      Nat.ofBits (fun index : Fin native =>
        bits ⟨index.val, index.isLt.trans_le hwidth⟩) := by
  rw [← Nat.ofBits_testBit (Nat.ofBits bits) native]
  congr 1
  funext index
  exact Nat.testBit_ofBits_lt bits index.val
    (index.isLt.trans_le hwidth)

theorem repeatedClauseIndex_binaryAddress
    {native padded : ℕ} (hwidth : native ≤ padded)
    (bits : BitInput padded) :
    repeatedClauseIndex hwidth (binaryAddress bits) =
      binaryAddress (fun index : Fin native =>
        bits ⟨index.val, index.isLt.trans_le hwidth⟩) := by
  apply Fin.ext
  change
    (binaryAddress bits).val % 2 ^ native =
      (binaryAddress (fun index : Fin native =>
        bits ⟨index.val, index.isLt.trans_le hwidth⟩)).val
  rw [binaryAddress_val_eq_ofBits, binaryAddress_val_eq_ofBits,
    ← ofBits_prefix_mod hwidth bits]

/-- The semantic repeated-clause PCPP.  Systematic and auxiliary coordinates,
the honest assignment, and the charged construction are unchanged. -/
noncomputable def padClauses
    {n : ℕ} {circuit : BooleanCircuit n}
    (pcpp : PointwisePCPP circuit) (paddedClauseBits : ℕ)
    (hwidth : pcpp.clauseBits ≤ paddedClauseBits) :
    PointwisePCPP circuit where
  systematicBits := pcpp.systematicBits
  auxiliaryBits := pcpp.auxiliaryBits
  clauseBits := paddedClauseBits
  systematicSupport := pcpp.systematicSupport
  systematicSupportBound := pcpp.systematicSupportBound
  clauses := fun index => pcpp.clauses (repeatedClauseIndex hwidth index)
  honestAuxiliary := pcpp.honestAuxiliary
  constructionSteps := pcpp.constructionSteps
  honestSteps := pcpp.honestSteps

@[simp] theorem padClauses_assignment
    {n : ℕ} {circuit : BooleanCircuit n}
    (pcpp : PointwisePCPP circuit) (paddedClauseBits : ℕ)
    (hwidth : pcpp.clauseBits ≤ paddedClauseBits)
    (input : BitInput n) (auxiliary : BitInput pcpp.auxiliaryBits) :
    (padClauses pcpp paddedClauseBits hwidth).assignment input auxiliary =
      pcpp.assignment input auxiliary :=
  rfl

theorem occurrenceInput_projectPadded
    {inputArity nativeClauseBits paddedClauseBits : ℕ}
    (hwidth : nativeClauseBits ≤ paddedClauseBits)
    (input : BitInput (inputArity + paddedClauseBits + 1)) :
    occurrenceInput (projectPaddedOccurrenceInput hwidth input) =
      occurrenceInput input := by
  funext index
  simp [occurrenceInput, projectPaddedOccurrenceInput,
    show index.val < inputArity + nativeClauseBits by omega]

theorem occurrencePosition_projectPadded
    {inputArity nativeClauseBits paddedClauseBits : ℕ}
    (hwidth : nativeClauseBits ≤ paddedClauseBits)
    (input : BitInput (inputArity + paddedClauseBits + 1)) :
    occurrencePosition (projectPaddedOccurrenceInput hwidth input) =
      occurrencePosition input := by
  simp [occurrencePosition, projectPaddedOccurrenceInput]

theorem occurrenceClauseAddress_projectPadded
    {inputArity nativeClauseBits paddedClauseBits : ℕ}
    (hwidth : nativeClauseBits ≤ paddedClauseBits)
    (input : BitInput (inputArity + paddedClauseBits + 1)) :
    occurrenceClauseAddress (projectPaddedOccurrenceInput hwidth input) =
      fun index : Fin nativeClauseBits =>
        occurrenceClauseAddress input
          ⟨index.val, index.isLt.trans_le hwidth⟩ := by
  funext index
  simp [occurrenceClauseAddress, projectPaddedOccurrenceInput]

/-- The table consumed by the componentwise supplier is literally the honest
occurrence table of the repeated-clause PCPP, not a parallel projected
function. -/
theorem honestOccurrenceFunction_padClauses
    {n : ℕ} {circuit : BooleanCircuit n}
    (pcpp : PointwisePCPP circuit) (paddedClauseBits : ℕ)
    (hwidth : pcpp.clauseBits ≤ paddedClauseBits) :
    honestOccurrenceFunction (padClauses pcpp paddedClauseBits hwidth) =
      paddedHonestOccurrenceFunction pcpp paddedClauseBits hwidth := by
  funext input
  change
    honestOccurrenceFunction (padClauses pcpp paddedClauseBits hwidth) input =
      honestOccurrenceFunction pcpp
        (projectPaddedOccurrenceInput hwidth input)
  simp only [honestOccurrenceFunction]
  dsimp only [padClauses]
  rw [occurrenceInput_projectPadded,
    occurrencePosition_projectPadded,
    occurrenceClauseAddress_projectPadded]
  rw [repeatedClauseIndex_binaryAddress]
  rfl

/-! ## Simultaneous outer-randomness and clause-address padding -/

/-- Restrict only the first (PCPP-input) block of an occurrence address.
The clause-address block is shifted past the padded input block, and the
literal-position bit remains the final bit. -/
def projectPaddedSystematicOccurrenceInput
    {nativeInputBits paddedInputBits clauseBits : ℕ}
    (hinput : nativeInputBits ≤ paddedInputBits)
    (input : BitInput (paddedInputBits + clauseBits + 1)) :
    BitInput (nativeInputBits + clauseBits + 1) :=
  fun index =>
    if hprefix : index.val < nativeInputBits then
      input ⟨index.val, by omega⟩
    else
      input ⟨paddedInputBits + (index.val - nativeInputBits), by omega⟩

theorem occurrenceInput_projectPaddedSystematic
    {nativeInputBits paddedInputBits clauseBits : ℕ}
    (hinput : nativeInputBits ≤ paddedInputBits)
    (input : BitInput (paddedInputBits + clauseBits + 1)) :
    occurrenceInput
        (projectPaddedSystematicOccurrenceInput hinput input) =
      prefixBits hinput (occurrenceInput input) := by
  funext index
  simp [occurrenceInput, prefixBits,
    projectPaddedSystematicOccurrenceInput]

theorem occurrenceClauseAddress_projectPaddedSystematic
    {nativeInputBits paddedInputBits clauseBits : ℕ}
    (hinput : nativeInputBits ≤ paddedInputBits)
    (input : BitInput (paddedInputBits + clauseBits + 1)) :
    occurrenceClauseAddress
        (projectPaddedSystematicOccurrenceInput hinput input) =
      occurrenceClauseAddress input := by
  funext index
  simp [occurrenceClauseAddress,
    projectPaddedSystematicOccurrenceInput]

theorem occurrencePosition_projectPaddedSystematic
    {nativeInputBits paddedInputBits clauseBits : ℕ}
    (hinput : nativeInputBits ≤ paddedInputBits)
    (input : BitInput (paddedInputBits + clauseBits + 1)) :
    occurrencePosition
        (projectPaddedSystematicOccurrenceInput hinput input) =
      occurrencePosition input := by
  simp [occurrencePosition, projectPaddedSystematicOccurrenceInput]

/-- The scheduled Case-2 seed is the source factory's honest PCPP table
extended along exactly two ignored axes.  It remains literally the honest
occurrence function of `padClauses`; no independently chosen table or
semantic witness is introduced. -/
noncomputable def fullyPaddedHonestOccurrenceFunction
    {n : ℕ} {circuit : BooleanCircuit n}
    (pcpp : PointwisePCPP circuit)
    (paddedInputBits paddedClauseBits : ℕ)
    (hinput : n ≤ paddedInputBits)
    (hclause : pcpp.clauseBits ≤ paddedClauseBits) :
    BoolFunction (paddedInputBits + paddedClauseBits + 1) :=
  fun input =>
    honestOccurrenceFunction
        (padClauses pcpp paddedClauseBits hclause)
      (projectPaddedSystematicOccurrenceInput hinput input)

theorem fullyPaddedHonestOccurrenceFunction_eq
    {n : ℕ} {circuit : BooleanCircuit n}
    (pcpp : PointwisePCPP circuit)
    (paddedInputBits paddedClauseBits : ℕ)
    (hinput : n ≤ paddedInputBits)
    (hclause : pcpp.clauseBits ≤ paddedClauseBits) :
    fullyPaddedHonestOccurrenceFunction pcpp
        paddedInputBits paddedClauseBits hinput hclause =
      fun input =>
        paddedHonestOccurrenceFunction pcpp paddedClauseBits hclause
          (projectPaddedSystematicOccurrenceInput hinput input) := by
  unfold fullyPaddedHonestOccurrenceFunction
  rw [honestOccurrenceFunction_padClauses]
  rfl

private theorem repeated_filter_card
    {native padded : ℕ} (hwidth : native ≤ padded)
    (predicate : Fin (2 ^ native) → Bool) :
    (Finset.univ.filter fun index : Fin (2 ^ padded) =>
        predicate (repeatedClauseIndex hwidth index)).card =
      2 ^ (padded - native) *
        (Finset.univ.filter fun index : Fin (2 ^ native) =>
          predicate index).card := by
  classical
  rw [Finset.card_filter, Finset.card_filter]
  change
    (∑ index : Fin (2 ^ padded),
        if predicate (repeatedClauseIndex hwidth index) = true then 1 else 0) =
      2 ^ (padded - native) *
        ∑ index : Fin (2 ^ native),
          if predicate index = true then 1 else 0
  calc
    (∑ index : Fin (2 ^ padded),
        if predicate (repeatedClauseIndex hwidth index) = true then 1 else 0) =
        ∑ index : Fin (2 ^ (padded - native)) × Fin (2 ^ native),
          if predicate index.2 = true then 1 else 0 := by
      exact (clauseAddressEquiv native padded hwidth).sum_comp
        (fun index =>
          if predicate index.2 = true then (1 : ℕ) else 0)
    _ = 2 ^ (padded - native) *
        ∑ index : Fin (2 ^ native),
          if predicate index = true then 1 else 0 := by
      rw [Fintype.sum_prod_type]
      simp

/-- Exact power-of-two repetition scales numerator and denominator by the same
positive factor, so the PCPP acceptance fraction is unchanged. -/
theorem padClauses_satisfiedFraction
    {n : ℕ} {circuit : BooleanCircuit n}
    (pcpp : PointwisePCPP circuit) (paddedClauseBits : ℕ)
    (hwidth : pcpp.clauseBits ≤ paddedClauseBits)
    (input : BitInput n) (auxiliary : BitInput pcpp.auxiliaryBits) :
    (padClauses pcpp paddedClauseBits hwidth).satisfiedFraction
        input auxiliary =
      pcpp.satisfiedFraction input auxiliary := by
  rw [PointwisePCPP.satisfiedFraction,
    PointwisePCPP.satisfiedFraction]
  change
    (((Finset.univ.filter fun index : Fin (2 ^ paddedClauseBits) =>
        (pcpp.clauses (repeatedClauseIndex hwidth index)).eval
          (pcpp.assignment input auxiliary)).card : ℕ) : ℝ) /
        (2 ^ paddedClauseBits : ℝ) =
      (((Finset.univ.filter fun index : Fin (2 ^ pcpp.clauseBits) =>
        (pcpp.clauses index).eval
          (pcpp.assignment input auxiliary)).card : ℕ) : ℝ) /
        (2 ^ pcpp.clauseBits : ℝ)
  have hcard :
      (Finset.univ.filter fun index : Fin (2 ^ paddedClauseBits) =>
        (pcpp.clauses (repeatedClauseIndex hwidth index)).eval
          (pcpp.assignment input auxiliary)).card =
        2 ^ (paddedClauseBits - pcpp.clauseBits) *
          (Finset.univ.filter fun index : Fin (2 ^ pcpp.clauseBits) =>
            (pcpp.clauses index).eval
              (pcpp.assignment input auxiliary)).card :=
    repeated_filter_card hwidth fun index =>
      (pcpp.clauses index).eval (pcpp.assignment input auxiliary)
  rw [hcard]
  have hpow :
      2 ^ paddedClauseBits =
        2 ^ (paddedClauseBits - pcpp.clauseBits) *
          2 ^ pcpp.clauseBits := by
    rw [← Nat.pow_add, Nat.sub_add_cancel hwidth]
  have hpowReal :
      (2 ^ paddedClauseBits : ℝ) =
        (2 ^ (paddedClauseBits - pcpp.clauseBits) : ℝ) *
          (2 ^ pcpp.clauseBits : ℝ) := by
    exact_mod_cast hpow
  rw [Nat.cast_mul, hpowReal]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  exact mul_div_mul_left _ _ (by positivity :
    (2 ^ (paddedClauseBits - pcpp.clauseBits) : ℝ) ≠ 0)

theorem padClauses_complete
    {n : ℕ} {circuit : BooleanCircuit n}
    (pcpp : PointwisePCPP circuit) (paddedClauseBits : ℕ)
    (hwidth : pcpp.clauseBits ≤ paddedClauseBits)
    (completeness : ℝ)
    (complete : ∀ input, circuit.eval input →
      pcpp.satisfiedFraction input (pcpp.honestAuxiliary input) ≥
        completeness) :
    ∀ input, circuit.eval input →
      (padClauses pcpp paddedClauseBits hwidth).satisfiedFraction input
          ((padClauses pcpp paddedClauseBits hwidth).honestAuxiliary input) ≥
        completeness := by
  intro input hinput
  rw [padClauses_satisfiedFraction]
  exact complete input hinput

theorem padClauses_sound
    {n : ℕ} {circuit : BooleanCircuit n}
    (pcpp : PointwisePCPP circuit) (paddedClauseBits : ℕ)
    (hwidth : pcpp.clauseBits ≤ paddedClauseBits)
    (soundness : ℝ)
    (sound : ∀ input, ¬circuit.eval input → ∀ auxiliary,
      pcpp.satisfiedFraction input auxiliary ≤ soundness) :
    ∀ input, ¬circuit.eval input → ∀ auxiliary,
      (padClauses pcpp paddedClauseBits hwidth).satisfiedFraction input
          auxiliary ≤ soundness := by
  intro input hinput auxiliary
  rw [padClauses_satisfiedFraction]
  exact sound input hinput auxiliary

/-- The padded query is still evaluated by the factory's original fixed
clause runner; only the public index is projected to its native suffix. -/
theorem padded_clause_query
    {n : ℕ} {circuit : BooleanCircuit n}
    (pcpp : ExecutablePointwisePCPP circuit)
    (paddedClauseBits : ℕ) (hwidth : pcpp.clauseBits ≤ paddedClauseBits)
    (index : Fin (2 ^ paddedClauseBits)) :
    pcpp.clause (repeatedClauseIndex hwidth index) =
      decodeTwoLiteralClause
        (pcpp.systematicBits + pcpp.auxiliaryBits)
        (by
          apply Nat.add_pos_left
          simp [ExecutablePointwisePCPP.systematicBits,
            pointwiseSystematicBits])
        (pcpp.clauseRunner.execute
          { inputArity := n
            circuitSize := circuit.size
            circuitCode := encodeBooleanCircuit circuit
            assignmentArity := pcpp.systematicBits + pcpp.auxiliaryBits
            clauseIndex := (repeatedClauseIndex hwidth index).val }) :=
  rfl

/-! ## Source-only outer and clause-width envelopes -/

/-- A circuit-size envelope for the native executable substitution after a
common-width oracle has been restricted to its zero suffix.  Every occurrence
of the native width is enlarged to `q(n)`, keeping the bound source-only and
monotone. -/
def substitutedCircuitSizeEnvelope
    {depth : ℕ}
    {source : ExecutableRefuterSource (pairClock depth)}
    (outer : HierarchyOuterPCP source) (oracleSizeBound : ℕ → ℕ)
    (sourceLength : ℕ) : ℕ :=
  let width := widthEnvelope outer sourceLength
  outer.substitution.sizeCoefficient *
      (width + oracleSizeBound width + 1) ^
        outer.substitutionExponent +
    width

def clauseBitsEnvelope
    {depth : ℕ}
    {source : ExecutableRefuterSource (pairClock depth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource)
    (oracleSizeBound : ℕ → ℕ) (sourceLength : ℕ) : ℕ :=
  Nat.log 2 <|
    pcppSource.coefficient *
      (substitutedCircuitSizeEnvelope outer oracleSizeBound sourceLength + 1) ^
        pcppSource.degree

theorem substitutedCircuitSizeEnvelope_monotone
    {depth : ℕ}
    {source : ExecutableRefuterSource (pairClock depth)}
    (outer : HierarchyOuterPCP source) (oracleSizeBound : ℕ → ℕ)
    (horacleMonotone : Monotone oracleSizeBound) :
    Monotone
      (substitutedCircuitSizeEnvelope outer oracleSizeBound) := by
  intro left right hle
  have hwidth :=
    pairClock_widthEnvelope_mono outer hle
  unfold substitutedCircuitSizeEnvelope
  dsimp only
  gcongr
  exact horacleMonotone hwidth

theorem clauseBitsEnvelope_monotone
    {depth : ℕ}
    {source : ExecutableRefuterSource (pairClock depth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource)
    (oracleSizeBound : ℕ → ℕ)
    (horacleMonotone : Monotone oracleSizeBound) :
    Monotone
      (clauseBitsEnvelope outer pcppSource oracleSizeBound) := by
  intro left right hle
  unfold clauseBitsEnvelope
  apply Nat.log_mono_right
  gcongr
  exact substitutedCircuitSizeEnvelope_monotone
    outer oracleSizeBound horacleMonotone hle

/-- The honest table together with its definitional origin in the one factory
selected before any oracle circuit. -/
structure SourceHonestPCPPTable
    (pcppSource : UniformPointwisePCPPSource)
    {n : ℕ} (circuit : BooleanCircuit n) where
  table : HonestPCPPTable circuit
  executable_eq :
    table.executable = pcppSource.factory.forCircuit circuit
  coefficient_eq : table.coefficient = pcppSource.coefficient
  degree_eq : table.degree = pcppSource.degree

theorem existsSourceHonestPCPPTable
    (pcppSource : UniformPointwisePCPPSource)
    {n : ℕ} (circuit : BooleanCircuit n) (hsize : n ≤ circuit.size) :
    Nonempty (SourceHonestPCPPTable pcppSource circuit) := by
  let pcpp := pcppSource.factory.forCircuit circuit
  rcases pcppSource.guarantee circuit hsize with
    ⟨supportBound, hshape, hsupport, hclause, hhonest,
      hdescription, hclauseCount, hconstruction, hcomplete, hsound,
      hhonestSteps⟩
  let table : HonestPCPPTable circuit :=
    { completeness := pcppSource.completeness
      soundness := pcppSource.soundness
      gap := pcppSource.gap
      coefficient := pcppSource.coefficient
      degree := pcppSource.degree
      runnerDegree := pcppSource.runnerDegree
      coefficientPositive := pcppSource.coefficientPositive
      executable := pcpp
      supportBound := supportBound
      shapeDegree := hshape
      supportDegree := hsupport
      clauseDegree := hclause
      honestDegree := hhonest
      descriptionBound := hdescription
      clauseCountBound := hclauseCount
      constructionBound := hconstruction
      honestComplete := hcomplete
      rejectSound := hsound
      honestStepsBound := hhonestSteps }
  exact ⟨⟨table, rfl, rfl, rfl⟩⟩

theorem pcppCircuit_size_le_envelope
    {depth : ℕ}
    {source : ExecutableRefuterSource (pairClock depth)}
    (outer : HierarchyOuterPCP source)
    (oracleSizeBound : ℕ → ℕ) {n : ℕ} (input : BitInput n)
    (oracle : BooleanCircuit (outer.pcp.nativeWidth n))
    (horacle :
      oracle.size ≤
        oracleSizeBound (widthEnvelope outer n)) :
    (outer.pcppCircuit input oracle).size ≤
      substitutedCircuitSizeEnvelope outer oracleSizeBound n := by
  apply (outer.pcppCircuit_size_bound input oracle).trans
  have hwidth := nativeWidth_le_widthEnvelope outer n
  unfold substitutedCircuitSizeEnvelope
  dsimp only
  gcongr

theorem pcppCircuit_size_le_envelope_of_paddedOracle
    {depth : ℕ}
    {source : ExecutableRefuterSource (pairClock depth)}
    (outer : HierarchyOuterPCP source)
    (oracleSizeBound : ℕ → ℕ) {n : ℕ} (input : BitInput n)
    (oracle : BooleanCircuit (widthEnvelope outer n))
    (horacle :
      oracle.size ≤
        oracleSizeBound (widthEnvelope outer n)) :
    (outer.pcppCircuit input
        (restrictPaddedOracle oracle
          (nativeWidth_le_widthEnvelope outer n))).size ≤
      substitutedCircuitSizeEnvelope outer oracleSizeBound n := by
  apply pcppCircuit_size_le_envelope
  simpa using horacle

theorem SourceHonestPCPPTable.clauseBits_le_envelope
    {depth : ℕ}
    {source : ExecutableRefuterSource (pairClock depth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource)
    (oracleSizeBound : ℕ → ℕ) {n : ℕ} (input : BitInput n)
    (oracle : BooleanCircuit (outer.pcp.nativeWidth n))
    (horacle :
      oracle.size ≤
        oracleSizeBound (widthEnvelope outer n))
    (table : SourceHonestPCPPTable pcppSource
      (outer.pcppCircuit input oracle)) :
    table.table.semantic.clauseBits ≤
      clauseBitsEnvelope outer pcppSource oracleSizeBound n := by
  unfold clauseBitsEnvelope
  apply Nat.le_log_of_pow_le (by omega)
  have hcount := table.table.clauseCountBound
  rw [table.coefficient_eq, table.degree_eq] at hcount
  apply hcount.trans
  gcongr
  exact pcppCircuit_size_le_envelope outer oracleSizeBound input oracle horacle

theorem SourceHonestPCPPTable.clauseBits_le_envelope_of_paddedOracle
    {depth : ℕ}
    {source : ExecutableRefuterSource (pairClock depth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource)
    (oracleSizeBound : ℕ → ℕ) {n : ℕ} (input : BitInput n)
    (oracle : BooleanCircuit (widthEnvelope outer n))
    (horacle :
      oracle.size ≤
        oracleSizeBound (widthEnvelope outer n))
    (table : SourceHonestPCPPTable pcppSource
      (outer.pcppCircuit input
        (restrictPaddedOracle oracle
          (nativeWidth_le_widthEnvelope outer n)))) :
    table.table.semantic.clauseBits ≤
      clauseBitsEnvelope outer pcppSource oracleSizeBound n := by
  unfold clauseBitsEnvelope
  apply Nat.le_log_of_pow_le (by omega)
  have hcount := table.table.clauseCountBound
  rw [table.coefficient_eq, table.degree_eq] at hcount
  apply hcount.trans
  gcongr
  exact pcppCircuit_size_le_envelope_of_paddedOracle
    outer oracleSizeBound input oracle horacle

/-- The scheduled honest occurrence table has one source-only arity on both
axes.  Its oracle is the canonical common-width Case-2 circuit, while the
factory is instantiated exactly once on that circuit's native restriction. -/
noncomputable def SourceHonestPCPPTable.paddedFunction
    {depth : ℕ}
    {source : ExecutableRefuterSource (pairClock depth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource)
    (oracleSizeBound : ℕ → ℕ) {n : ℕ} (input : BitInput n)
    (oracle : BooleanCircuit (widthEnvelope outer n))
    (horacle :
      oracle.size ≤
        oracleSizeBound (widthEnvelope outer n))
    (table : SourceHonestPCPPTable pcppSource
      (outer.pcppCircuit input
        (restrictPaddedOracle oracle
          (nativeWidth_le_widthEnvelope outer n)))) :
    BoolFunction
      (widthEnvelope outer n +
        clauseBitsEnvelope outer pcppSource oracleSizeBound n + 1) :=
  fullyPaddedHonestOccurrenceFunction table.table.semantic
    (widthEnvelope outer n)
    (clauseBitsEnvelope outer pcppSource oracleSizeBound n)
    (nativeWidth_le_widthEnvelope outer n)
    (table.clauseBits_le_envelope_of_paddedOracle outer pcppSource
      oracleSizeBound input oracle horacle)

/-- Completeness of the exact two-axis table follows from the single padded
oracle chosen by Case 2.  The proof first restricts that oracle to the native
zero-suffix face and then invokes the source PCPP's honest completeness. -/
theorem SourceHonestPCPPTable.paddedComplete
    {depth : ℕ}
    {source : ExecutableRefuterSource (pairClock depth)}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource)
    (oracleSizeBound : ℕ → ℕ) {n : ℕ} (input : BitInput n)
    (oracle : BooleanCircuit (widthEnvelope outer n))
    (horacle :
      oracle.size ≤
        oracleSizeBound (widthEnvelope outer n))
    (accepts : ∀ randomness,
      acceptsOracleCircuit
        (padProjectionPCP outer.pcp.toSemantic
          (widthEnvelope outer)
          (nativeWidth_le_widthEnvelope outer))
        input oracle randomness)
    (table : SourceHonestPCPPTable pcppSource
      (outer.pcppCircuit input
        (restrictPaddedOracle oracle
          (nativeWidth_le_widthEnvelope outer n)))) :
    ∀ randomness : BitInput (widthEnvelope outer n),
      let hclause :=
        table.clauseBits_le_envelope_of_paddedOracle outer pcppSource
          oracleSizeBound input oracle horacle
      (padClauses table.table.semantic
          (clauseBitsEnvelope outer pcppSource oracleSizeBound n)
          hclause).satisfiedFraction
            (prefixBits (nativeWidth_le_widthEnvelope outer n) randomness)
            (table.table.semantic.honestAuxiliary
              (prefixBits
                (nativeWidth_le_widthEnvelope outer n) randomness)) ≥
        table.table.completeness := by
  intro randomness
  dsimp only
  rw [padClauses_satisfiedFraction]
  apply table.table.honestComplete
  apply outer.pcppCircuit_accepts
  apply restrictPaddedOracle_accepts
  exact accepts

end NearCubicWires.PCPPClausePadding
