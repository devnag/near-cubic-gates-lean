import Proof.CaseAnalysis.FinalStageContracts
import Proof.CaseAnalysis.FinalEncoder
import Proof.CaseAnalysis.SelectedClauses
import Proof.CaseAnalysis.NativeWidthPolynomial
import Proof.Hierarchy.CompetitorWitnessTripleSemantics
import Proof.MachineModel.OrdinarySignedSortKey
import Proof.Foundations.BooleanCircuitSizePadding

namespace NearCubicWires.RepairSource.CloseoutFinal.C10OracleSizeBound

open SourceInterfaces RepairRepresentation RepairOrdinary
open RepairOrdinary.CloseoutWitness CanonicalWitnessCodec ExecutableInterfaces
open SupplierPipeline CircuitRestriction
open RecoveryScheduleEnvelope SelectedRecoveryIntegration CloseoutLanguage
open PolynomialSchedule

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

/-! ## §0  The raw decoder, and the gate unfolded once -/

/-- **The RAW decoder, made total.**  `decodeBooleanCircuit`
(`Proof/Circuits/CanonicalWitnessCodec.lean`) with the same total fallback the
pre-gate `oracleOf` used.  It carries NO size test: the paper's "size-\(q^G\)"
guard is a property of the GUESS the machine accepts, not of the codec.  Every
negative in §2 is about THIS function. -/
def decodedOracle (sources : EightSources) (k : ℕ)
    (clock : OrdinaryClock (fun n => n^(k+2))) (n : ℕ) (bits : List Bool) :
    BooleanCircuit ((outer sources k clock).result.pcp.nativeWidth n) :=
  (decodeBooleanCircuit ((outer sources k clock).result.pcp.nativeWidth n)
    (RadixSemantics.value (BoundedFields.oracle bits))).getD
      (C10TotalDecode.trivialCircuit ((outer sources k clock).result.pcp.nativeWidth n))

theorem decodedOracle_pin (sources : EightSources) (k : ℕ)
    (clock : OrdinaryClock (fun n => n^(k+2))) (n : ℕ) (bits : List Bool)
    (oracle : BooleanCircuit ((outer sources k clock).result.pcp.nativeWidth n))
    (h : decodeBooleanCircuit ((outer sources k clock).result.pcp.nativeWidth n)
      (RadixSemantics.value (BoundedFields.oracle bits)) = some oracle) :
    decodedOracle sources k clock n bits = oracle := by
  simp [decodedOracle, h]

/-- **The gate, unfolded once.**  `oracleOf`
(`Proof/CaseAnalysis/FinalTotalDecode.lean`) is the raw decoder followed by the
machine's own size test, `paper.tex:4292`: "It deterministically rejects a branch
if ... it fails the fixed general-circuit size bound." -/
theorem oracleOf_eq_if (sources : EightSources) (k : ℕ)
    (clock : OrdinaryClock (fun n => n^(k+2))) (oracleDegree n : ℕ) (bits : List Bool) :
    C10TotalDecode.oracleOf sources k clock oracleDegree n bits =
      (if (decodedOracle sources k clock n bits).size ≤
            oracleSizeBound oracleDegree ((outer sources k clock).result.pcp.nativeWidth n)
        then decodedOracle sources k clock n bits
        else C10TotalDecode.trivialCircuit ((outer sources k clock).result.pcp.nativeWidth n)) :=
  rfl

/-! ## §1  A decodable circuit above any cap -/

/-- The decoder's own total fallback `trivialCircuit`
(`Proof/CaseAnalysis/FinalTotalDecode.lean`), padded past `cap` by
`BooleanCircuit.padSize` (`Proof/Foundations/BooleanCircuitSizePadding.lean`).  The
padding is semantics-preserving, so this is an ordinary legal oracle; only its
DAG size is large. -/
def oversized (arity cap : ℕ) : BooleanCircuit arity :=
  (C10TotalDecode.trivialCircuit arity).padSize (cap + 1)

theorem oversized_size (arity cap : ℕ) : (oversized arity cap).size = cap + 2 := by
  have hone : (C10TotalDecode.trivialCircuit arity).size = 1 := rfl
  rw [oversized, BooleanCircuit.padSize_size, hone]
  omega

/-- The canonical three-field header code whose oracle field is `circuit`'s own
canonical code.  `FamilyWitness.code` (`Proof/CaseAnalysis/WitnessFamily.lean`)
has exactly this shape. -/
def headerCode {arity : ℕ} (circuit : BooleanCircuit arity) : ℕ :=
  CanonicalBinary.encodeTaggedList [0, encodeBooleanCircuit circuit, 0]

/-- A witness string whose radix value is that header code. -/
def headerBits {arity : ℕ} (circuit : BooleanCircuit arity) : List Bool :=
  SignedSortKey.binary (headerCode circuit) (headerCode circuit)

/-- The oracle FIELD of that witness string is the circuit's canonical code.
`BoundedFields.oracle` (`Proof/CaseAnalysis/WitnessBoundedFields.lean`) is the
left word of header slot `3`, which is what `field bits 3`
(`Proof/Hierarchy/CompetitorWitnessTripleSemantics.lean`) measures. -/
theorem headerBits_oracle {arity : ℕ} (circuit : BooleanCircuit arity) :
    RadixSemantics.value (BoundedFields.oracle (headerBits circuit))
      = encodeBooleanCircuit circuit := by
  have hvalue : RadixSemantics.value (headerBits circuit) = headerCode circuit :=
    SignedSortKey.binary_value _ _ (Nat.lt_two_pow_self)
  exact (CompetitorWitnessTriple.extracted_values (headerBits circuit) 0
    (encodeBooleanCircuit circuit) 0 hvalue).2.2.1

/-- That witness string RAW-DECODES, at the live arity, to the oversized circuit.
(Was `oracleOf_headerBits`; the pin it uses is the codec's, not the machine's,
so the gate does not enter.) -/
theorem decodedOracle_headerBits (sources : EightSources) (k : ℕ)
    (clock : OrdinaryClock (fun n => n^(k+2))) (n cap : ℕ) :
    decodedOracle sources k clock n
        (headerBits (oversized ((outer sources k clock).result.pcp.nativeWidth n) cap))
      = oversized ((outer sources k clock).result.pcp.nativeWidth n) cap :=
  decodedOracle_pin sources k clock n _ _
    (by rw [headerBits_oracle]; exact decodeBooleanCircuit_encode _)

/-! ## §2  The refutation, at the object it is about: the raw decoder -/

/-- **The codec admits oracles above the paper's cap, at every parameter.**  This
is why the guard is needed and what it is guarding against.  Was
`oracleOf_size_unbounded`; the witness and the proof are unchanged, only the
subject moved from the gated `oracleOf` to the raw `decodedOracle`. -/
theorem decoded_size_above_cap (sources : EightSources) (k : ℕ)
    (clock : OrdinaryClock (fun n => n^(k+2))) (oracleDegree n : ℕ) :
    ∃ bits : List Bool,
      oracleSizeBound oracleDegree ((outer sources k clock).result.pcp.nativeWidth n)
        < (decodedOracle sources k clock n bits).size := by
  refine ⟨headerBits (oversized ((outer sources k clock).result.pcp.nativeWidth n)
    (oracleSizeBound oracleDegree ((outer sources k clock).result.pcp.nativeWidth n))), ?_⟩
  rw [decodedOracle_headerBits, oversized_size]
  omega

theorem not_decoded_size_le_cap (sources : EightSources) (k : ℕ)
    (clock : OrdinaryClock (fun n => n^(k+2))) (oracleDegree n : ℕ) :
    ¬ ∀ bits : List Bool,
        (decodedOracle sources k clock n bits).size ≤
          oracleSizeBound oracleDegree ((outer sources k clock).result.pcp.nativeWidth n) := by
  obtain ⟨bits, hbits⟩ := decoded_size_above_cap sources k clock oracleDegree n
  exact fun hall => absurd (hall bits) (by omega)

/-! ## §3  What the gate buys: the pinned branch, and then the cap outright -/

/-- **The honest branch.**  When the witness pins a decode inside the cap, the
gated oracle IS the pinned one and the cap transfers verbatim. -/
theorem oracleOf_size_le_of_pin (sources : EightSources) (k : ℕ)
    (clock : OrdinaryClock (fun n => n^(k+2))) (oracleDegree n : ℕ) (bits : List Bool)
    (oracle : BooleanCircuit ((outer sources k clock).result.pcp.nativeWidth n))
    (hdecode : decodeBooleanCircuit ((outer sources k clock).result.pcp.nativeWidth n)
      (RadixSemantics.value (BoundedFields.oracle bits)) = some oracle)
    (hsize : oracle.size ≤
      oracleSizeBound oracleDegree ((outer sources k clock).result.pcp.nativeWidth n)) :
    (C10TotalDecode.oracleOf sources k clock oracleDegree n bits).size ≤
      oracleSizeBound oracleDegree ((outer sources k clock).result.pcp.nativeWidth n) := by
  rw [C10TotalDecode.oracleOf_pin sources k clock oracleDegree n bits oracle hdecode hsize]
  exact hsize

/-- **The cap, for EVERY witness.**  Both branches of the gate are inside it: the
accepted one by the test itself, the rejected one because `trivialCircuit` has
size `1` and `oracleSizeBound` is `pairClock`
(`Proof/Foundations/RecoveryScheduleEnvelope.lean`), positive at positive width by
`pairClock_positive` (`Proof/Foundations/PolynomialClock.lean`).  A positive native
width is the whole residual. -/
theorem oracleOf_size_le_cap (sources : EightSources) (k : ℕ)
    (clock : OrdinaryClock (fun n => n^(k+2))) (oracleDegree n : ℕ) (bits : List Bool)
    (hwidth : 0 < (outer sources k clock).result.pcp.nativeWidth n) :
    (C10TotalDecode.oracleOf sources k clock oracleDegree n bits).size ≤
      oracleSizeBound oracleDegree ((outer sources k clock).result.pcp.nativeWidth n) := by
  by_cases hle : (decodedOracle sources k clock n bits).size ≤
      oracleSizeBound oracleDegree ((outer sources k clock).result.pcp.nativeWidth n)
  · rw [oracleOf_eq_if, if_pos hle]
    exact hle
  · rw [oracleOf_eq_if, if_neg hle]
    have hone : (C10TotalDecode.trivialCircuit
        ((outer sources k clock).result.pcp.nativeWidth n)).size = 1 := rfl
    rw [hone]
    exact PolynomialClock.pairClock_positive _ _ hwidth

/-- **The reduction ORACLE stated, kept verbatim.**  It is now a corollary of
`oracleOf_size_le_cap`: the hypothesis it carries is dischargeable, which was the
point of applying the guard. -/
theorem oracleOf_size_le_of_gate (sources : EightSources) (k : ℕ)
    (clock : OrdinaryClock (fun n => n^(k+2))) (oracleDegree n : ℕ) (bits : List Bool)
    (hwidth : 0 < (outer sources k clock).result.pcp.nativeWidth n)
    (_hgate : ∀ oracle : BooleanCircuit ((outer sources k clock).result.pcp.nativeWidth n),
      decodeBooleanCircuit ((outer sources k clock).result.pcp.nativeWidth n)
        (RadixSemantics.value (BoundedFields.oracle bits)) = some oracle →
      oracle.size ≤
        oracleSizeBound oracleDegree ((outer sources k clock).result.pcp.nativeWidth n)) :
    (C10TotalDecode.oracleOf sources k clock oracleDegree n bits).size ≤
      oracleSizeBound oracleDegree ((outer sources k clock).result.pcp.nativeWidth n) :=
  oracleOf_size_le_cap sources k clock oracleDegree n bits hwidth

/-- **The gate is not decoration: its `else` branch is reached.**  The very
witness that refutes the raw decoder in §2 fails the test, so the machine falls
back to `trivialCircuit` and the size strictly drops.  Stated at every `sources`,
`k`, `clock`, `oracleDegree` and `n`, with no width hypothesis. -/
theorem gate_not_vacuous (sources : EightSources) (k : ℕ)
    (clock : OrdinaryClock (fun n => n^(k+2))) (oracleDegree n : ℕ) :
    ∃ bits : List Bool,
      oracleSizeBound oracleDegree ((outer sources k clock).result.pcp.nativeWidth n)
          < (decodedOracle sources k clock n bits).size ∧
        C10TotalDecode.oracleOf sources k clock oracleDegree n bits
          = C10TotalDecode.trivialCircuit ((outer sources k clock).result.pcp.nativeWidth n) ∧
        (C10TotalDecode.oracleOf sources k clock oracleDegree n bits).size
          < (decodedOracle sources k clock n bits).size := by
  refine ⟨headerBits (oversized ((outer sources k clock).result.pcp.nativeWidth n)
    (oracleSizeBound oracleDegree ((outer sources k clock).result.pcp.nativeWidth n))), ?_⟩
  have hsize : (decodedOracle sources k clock n
      (headerBits (oversized ((outer sources k clock).result.pcp.nativeWidth n)
        (oracleSizeBound oracleDegree ((outer sources k clock).result.pcp.nativeWidth n))))).size
      = oracleSizeBound oracleDegree ((outer sources k clock).result.pcp.nativeWidth n) + 2 := by
    rw [decodedOracle_headerBits, oversized_size]
  have hgt : ¬ (decodedOracle sources k clock n
      (headerBits (oversized ((outer sources k clock).result.pcp.nativeWidth n)
        (oracleSizeBound oracleDegree ((outer sources k clock).result.pcp.nativeWidth n))))).size
      ≤ oracleSizeBound oracleDegree ((outer sources k clock).result.pcp.nativeWidth n) := by
    omega
  have htriv : C10TotalDecode.oracleOf sources k clock oracleDegree n
      (headerBits (oversized ((outer sources k clock).result.pcp.nativeWidth n)
        (oracleSizeBound oracleDegree ((outer sources k clock).result.pcp.nativeWidth n))))
      = C10TotalDecode.trivialCircuit ((outer sources k clock).result.pcp.nativeWidth n) := by
    rw [oracleOf_eq_if, if_neg hgt]
  have hone : (C10TotalDecode.trivialCircuit
      ((outer sources k clock).result.pcp.nativeWidth n)).size = 1 := rfl
  refine ⟨by omega, htriv, ?_⟩
  rw [htriv, hone]
  omega

/-! ## §4  The payoff, at the live `pcppOf` -/

/-- **`hfit` for `callsReady_at_clauseWidth`
(`Proof/CaseAnalysis/FinalEnvelopeCounter.lean`), at the live decoded PCPP, with
the oracle-size premise DISCHARGED.**  `selected_clause_degree`
(`Proof/CaseAnalysis/SelectedClauses.lean`) instantiated at `pcppOf`
(`Proof/CaseAnalysis/FinalStageContracts.lean`), whose oracle is `oracleOf` at
the closure parameters' own `p.degree` -- paper C.10's `G` (`paper.tex:4283`).
Taking `selected_clause_degree` at that SAME `p.degree` is what lets
`oracleOf_size_le_cap` supply its cap, so only a positive native width and the
`onset <= q` both routes carry remain.  No scheduled input, no `1 <= s`, no
cutoff, no `ClauseReady`. -/
theorem pcppOf_clause_degree (sources : EightSources) {gamma : ℝ}
    (p : Parameters sources gamma) :
    ∃ degree onset : ℕ, 1 ≤ degree ∧
      ∀ (k n : ℕ) (x : BitInput n) (bits : List Bool),
        0 < (outer sources k (PolynomialClock.ordinaryClock k)).result.pcp.nativeWidth n →
          onset ≤ (outer sources k (PolynomialClock.ordinaryClock k)).result.pcp.nativeWidth n →
          (C10TailComposeUniform.pcppOf sources k p x bits).clauseBits ≤
            clauseWidth degree
              ((outer sources k (PolynomialClock.ordinaryClock k)).result.pcp.nativeWidth n) := by
  obtain ⟨degree, onset, hdegree, hbound⟩ := selected_clause_degree sources p.degree
  refine ⟨degree, onset, hdegree, ?_⟩
  intro k n x bits hwidth honset
  exact (hbound k (PolynomialClock.ordinaryClock k) n x
    (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)
    (oracleOf_size_le_cap sources k (PolynomialClock.ordinaryClock k) p.degree n bits hwidth)
    honset).2

/-! ## §5  The completeness branch, with no residual premise -/

/-- **Where the cap does hold, outright.**  On the honest guesses the encoder
produces -- `symmetric_family_guess` (`Proof/CaseAnalysis/FinalEncoder.lean`) --
the decode is pinned to the small oracle, so `oracleOf` is that oracle and the
cap is discharged with nothing left over.  This separates the honest branch from
the general witness without appealing to the gate at all. -/
theorem oracleOf_size_le_at_guess (sources : EightSources) (k : ℕ)
    (clock : OrdinaryClock (fun n => n^(k+2)))
    (degree clauseDegree copies : ℕ) (delta : ℚ) (cap : ℝ) :
    ∃ onset : ℕ, ∀ s : ℕ, onset ≤ s → ∀ input : BitInput (2^s),
      ∀ oracle : BooleanCircuit ((outer sources k clock).result.pcp.nativeWidth (2^s)),
      oracle.size ≤ oracleSizeBound degree
        ((outer sources k clock).result.pcp.nativeWidth (2^s)) →
      ∀ _family : CloseoutWitness.SumFamily NormalizedSymmetricThresholdCircuit
          NormalizedSymmetricThresholdCircuit.wireCount
          NormalizedSymmetricThresholdCircuit.descriptionBits
          (CloseoutSampledWitness.symmetricLimits (selectedPCPP sources)
            (CloseoutWitnessPolicy.request sources k clock input oracle)
            (clauseWidth clauseDegree ((outer sources k clock).result.pcp.nativeWidth (2^s)))
            copies ⌊wireScale cap 5 ((outer sources k clock).result.pcp.nativeWidth (2^s))⌋₊ delta)
          (CloseoutWitnessPolicy.variableCount sources k clock input oracle),
      ∃ guess : BitInput (2^s/16),
        (C10TotalDecode.oracleOf sources k clock degree (2^s) (List.ofFn guess)).size ≤
          oracleSizeBound degree ((outer sources k clock).result.pcp.nativeWidth (2^s)) := by
  obtain ⟨onset, hguess⟩ :=
    symmetric_family_guess sources k clock degree clauseDegree copies delta cap
  refine ⟨onset, ?_⟩
  intro s hs input oracle hsize family
  obtain ⟨guess, _hlen, _hheader, hdecode, _hpayload, _hmode⟩ :=
    hguess s hs input oracle hsize family
  exact ⟨guess, oracleOf_size_le_of_pin sources k clock degree (2^s) (List.ofFn guess)
    oracle hdecode hsize⟩

theorem cap_dyadic_polynomial (sources : EightSources) (k : ℕ)
    (clock : OrdinaryClock (fun n => n^(k+2))) (oracleDegree : ℕ) :
    PolynomiallyBounded (fun s => oracleSizeBound oracleDegree
      ((outer sources k clock).result.pcp.nativeWidth (2^s))) :=
  polynomiallyBounded_comp (oracleSizeBound_polynomiallyBounded oracleDegree)
    (native_dyadic_polynomial sources k clock)

/-- **The separation.**  At some dyadic length the paper's `q^G` cap is STRICTLY
BELOW the header-length majorant `n = 2^s`. -/
theorem size_cap_below_length_majorant (sources : EightSources) (k : ℕ)
    (clock : OrdinaryClock (fun n => n^(k+2))) (oracleDegree : ℕ) :
    ∃ s : ℕ, oracleSizeBound oracleDegree
      ((outer sources k clock).result.pcp.nativeWidth (2^s)) < 2^s := by
  by_contra hcontra
  push Not at hcontra
  obtain ⟨onset, hsmall⟩ := polynomiallyBounded_eventually_le_sixteenth_exponential
    (cap_dyadic_polynomial sources k clock oracleDegree)
  have hcap := hcontra (onset + 3)
  have hpoly := hsmall (onset + 3) (by omega)
  have hsixteen : (2:ℕ)^(onset + 3 + 1) / 16 = 2^onset := by
    have hform : (2:ℕ)^(onset + 3 + 1) = 16 * 2^onset := by ring
    rw [hform]
    exact Nat.mul_div_cancel_left _ (by norm_num)
  rw [hsixteen] at hpoly
  have hchain : (2:ℕ)^(onset + 3) ≤ 2^onset := hcap.trans hpoly
  have height : (2:ℕ)^(onset + 3) = 8 * 2^onset := by ring
  have hpos : 1 ≤ (2:ℕ)^onset := Nat.one_le_pow onset 2 (by norm_num)
  rw [height] at hchain
  omega

/-- **The answer to "does a length gate discharge this cap".**  No: a majorant of
`2^s` does not entail the cap, at any `sources`, `k`, `clock` or `oracleDegree`. -/
theorem length_majorant_not_size_cap (sources : EightSources) (k : ℕ)
    (clock : OrdinaryClock (fun n => n^(k+2))) (oracleDegree : ℕ) :
    ¬ ∀ (s size : ℕ), size ≤ 2^s →
        size ≤ oracleSizeBound oracleDegree
          ((outer sources k clock).result.pcp.nativeWidth (2^s)) := by
  obtain ⟨s, hs⟩ := size_cap_below_length_majorant sources k clock oracleDegree
  exact fun hall => absurd (hall s (2^s) (Nat.le_refl _)) (by omega)

end
end NearCubicWires.RepairSource.CloseoutFinal.C10OracleSizeBound
