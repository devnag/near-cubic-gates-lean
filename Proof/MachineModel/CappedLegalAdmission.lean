import Proof.MachineModel.CappedConsumer
import Proof.CaseAnalysis.WitnessBoundedFamilyDecoded
import Proof.CaseAnalysis.WitnessDyadicGuards
import Proof.CaseAnalysis.WitnessInputCutoff
import Proof.CaseAnalysis.NaturalWireCaps

/-! Paper C.10's honest typed witnesses pass the actual bounded cold flag.
Both modes use the same frozen positive denominator, so the paper may choose
its wire coefficient after choosing the saving constants. A fixed outer onset absorbs the native guard
and padded-arity cutoffs; it does not change the earlier cold cutoff.
This proves admission, not the remaining physical worker/continuation run. -/
namespace NearCubicWires.P1Independent.CappedLegalAdmission
open RepairSource RepairSource.CloseoutFinal
open RepairOrdinary RepairOrdinary.CloseoutWitness SourceInterfaces RepairRepresentation
open SelectedRecoveryIntegration CanonicalWitnessCodec SupplierPipeline
open CloseoutLanguage CompetitorRationalGap CappedConsumer C10TotalDecode
open CloseoutWitness.SelectedSource
open private decode_cast from Proof.CaseAnalysis.WitnessDyadicGuards

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (sources : EightSources) {gamma : ℝ} (p : Parameters sources gamma) (W : WorkerData)

/-- Exactly the boolean retained by bounded_cache and bounded_zero. -/
def passed (coldCutoff : ℕ) (n : ℕ) (x : BitInput n) (bits : List Bool) : Bool :=
  BoundedFamily.passed (fixedProjection sources) (selectedPCPP sources) W.k
    (hierarchy sources W.k W.clock).coefficient (padding sources W.k W.clock)
    coldCutoff p.clauseDegree p.degree p.copies W.den W.den (zeta (constantsOf sources))
    (code sources W.k W.clock) x bits (Nat.le_max_right _ _)

private theorem wire_cap (den e q : ℕ) :
    LegalPolicy.W e den q = ⌊wireScale (1 / (den : ℝ)) e q⌋₊ := by
  exact (CloseoutRawRows.naturalWireCap_floor den e q).symm

/-- Only the dyadic witnesses used by pinned completeness are quantified. -/
theorem passed_legal_eventually (coldCutoff : ℕ) :
    ∃ onset, ∀ s, onset ≤ s → ∀ (x : BitInput (2^s)) (guess : BitInput (2^s/16)),
      LegalWitness sources p W (2^s) x (List.ofFn guess) →
      passed sources p W coldCutoff (2^s) x (List.ofFn guess) = true := by
  obtain ⟨nativeOnset, hnative⟩ := guards_eventually sources W.k W.clock coldCutoff p.degree
  refine ⟨max nativeOnset (CloseoutWitnessPolicy.inputCutoff sources), ?_⟩
  intro s hs x guess hlegal
  obtain ⟨hlen, hheader, oracle, hdecode, hsize, hfamily⟩ := hlegal
  have native := hnative s ((Nat.le_max_left _ _).trans hs) x oracle hsize
    (BoundedFields.oracle (List.ofFn guess)) hdecode
  have harity := CloseoutWitnessPolicy.input_cutoff_arity sources W.k W.clock x oracle
    (((Nat.le_max_right _ _).trans hs).trans (Nat.lt_two_pow_self).le)
  have hclause := congrArg (clauseWidth p.clauseDegree) harity
  have hwire (e : ℕ) : LegalPolicy.W e W.den (CloseoutWitnessPolicy.request sources W.k W.clock x oracle).arity =
      ⌊wireScale (1 / (W.den : ℝ)) e ((outer sources W.k W.clock).result.pcp.nativeWidth (2^s))⌋₊ := by
    rw [harity, wire_cap]
  apply (BoundedFamily.passed_exact (fixedProjection sources) (selectedPCPP sources) W.k
    (hierarchy sources W.k W.clock).coefficient (padding sources W.k W.clock)
    coldCutoff p.clauseDegree p.degree p.copies W.den W.den (zeta (constantsOf sources))
    (code sources W.k W.clock) x (List.ofFn guess) (Nat.le_max_right _ _)).mpr
  refine ⟨hlen, hheader, native,
    cast (congrArg BooleanCircuit (width sources W.k W.clock x).symm) oracle,
    decode_cast (width sources W.k W.clock x) hdecode, ?_⟩
  rcases hfamily with ⟨family, hfamily, hmode⟩ | ⟨family, hfamily, hmode⟩
  all_goals
    rw [hmode]
    unfold ColdFamily.decodedFamily
    rw [request_eq sources W.k W.clock x oracle]
    simp only [BoundedFamily.exponent, BoundedFamily.denominator,
      Bool.false_eq_true, if_false, if_true]
    first | rw [if_pos (rfl : true = true), if_pos (rfl : true = true)]
          | rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]
    rw [hclause, hwire]
    exact ⟨family, hfamily⟩

/-- Set the exact selected flag and enlarge only the fixed outer onset.
The worker, clock, tapes, ports and fuel remain the caller's concrete choices. -/
def admissionData (coldCutoff : ℕ) : WorkerData :=
  { W with
    onset := max W.onset (Classical.choose (passed_legal_eventually sources p W coldCutoff))
    passed := passed sources p W coldCutoff }

theorem onset_le (coldCutoff : ℕ) : W.onset ≤ (admissionData sources p W coldCutoff).onset :=
  Nat.le_max_left _ _

/-- Exact Requirements.admits_legal field for the selected admission data. -/
theorem admits_legal (coldCutoff : ℕ) :
    ∀ s, (admissionData sources p W coldCutoff).onset ≤ s →
      ∀ (x : BitInput (2^s)) (guess : BitInput (2^s/16)),
        LegalWitness sources p (admissionData sources p W coldCutoff) (2^s) x (List.ofFn guess) →
        (admissionData sources p W coldCutoff).passed (2^s) x (List.ofFn guess) = true := by
  intro s hs x guess hlegal
  exact Classical.choose_spec (passed_legal_eventually sources p W coldCutoff)
    s ((Nat.le_max_right _ _).trans hs) x guess hlegal

end
end NearCubicWires.P1Independent.CappedLegalAdmission
