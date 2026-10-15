import Proof.CaseAnalysis.FinalStageFields
import Proof.CaseAnalysis.FinalOracleSizeBound
import Proof.CaseAnalysis.FinalPartsSchedule
import Proof.CaseAnalysis.FinalLedgerAssembly

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10ClauseBitsUniform

open NearCubicWires
open NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.CloseoutWitness
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule (Phase)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10ExactnessFamily
open NearCubicWires.RepairOrdinary.CloseoutFinalC10SupplierCalls (CoefficientsFit siteCalls)
open NearCubicWires.RepairRepresentation
open NearCubicWires.RepairSource
open NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairSource.CloseoutFinal.C10SumFamilyTransport
open NearCubicWires.RepairSource.CloseoutFinal.C10StageFuelBound
open NearCubicWires.RepairSource.CloseoutFinal.C10TailComposeUniform
open NearCubicWires.RepairSource.CompetitorRationalGap (zeta)
open NearCubicWires.RepairSource.CloseoutLanguage (selectedPCPP clauseWidth)
open NearCubicWires.RepairSource.SelectedRecoveryIntegration (outer fixedProjection)
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierPipeline

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (sources : EightSources) (k : ℕ) {gamma : ℝ} (p : Parameters sources gamma)

/-! ## §1 The native width, and the only side condition the cap carries -/

/-- The selected source's native width at the route's own clock -- the paper's
`q(N)` (`paper.tex:3967`).  A function of the INPUT LENGTH alone: no input, no
guessed oracle. -/
abbrev nativeWidthOf (n : ℕ) : ℕ :=
  (outer sources k (PolynomialClock.ordinaryClock k)).result.pcp.nativeWidth n

theorem nativeWidthOf_pos (n : ℕ) : 0 < nativeWidthOf sources k n := Nat.succ_pos _

/-! ## §2 The cap, and the two facts it gives -/

/-- **The witness-uniform clause cap.**  `shortBound`
(`Proof/CaseAnalysis/SourceCounts.lean`) at the route's own native width: the
paper's \(M_0\) majorant of `paper.tex:4054-4057`, before the polynomial fit that
turns it into \((q+2)^{d_G}\).  It mentions no input and no guessed oracle. -/
def clauseCap (degree n : ℕ) : ℕ :=
  CloseoutSourceCounts.shortBound (selectedPCPP sources)
    (fixedProjection sources).coefficient (fixedProjection sources).degrees.queries degree
    (nativeWidthOf sources k n)

theorem two_pow_clauseBits_le (n : ℕ) (x : BitInput n) (bits : List Bool) :
    2 ^ (pcppOf sources k p x bits).clauseBits ≤ clauseCap sources k p.degree n :=
  (CloseoutSourceCounts.short_counts (selectedPCPP sources)
    (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)
    ((outer sources k (PolynomialClock.ordinaryClock k)).result.pcp.queryAddressBits x)
    ((outer sources k (PolynomialClock.ordinaryClock k)).result.pcp.decision x (fun _ => false))
    (fixedProjection sources).coefficient (fixedProjection sources).degrees.queries p.degree
    (CloseoutLanguage.selected_query_bound sources k (PolynomialClock.ordinaryClock k) n)
    (C10OracleSizeBound.oracleOf_size_le_cap sources k (PolynomialClock.ordinaryClock k)
      p.degree n bits (nativeWidthOf_pos sources k n))).2

/-- The same fact as a bound on the clause-address WIDTH, which is what
`coefficientBound` adds. -/
theorem clauseBits_le (n : ℕ) (x : BitInput n) (bits : List Bool) :
    (pcppOf sources k p x bits).clauseBits ≤ Nat.log 2 (clauseCap sources k p.degree n) :=
  Nat.le_log_of_pow_le (by norm_num) (two_pow_clauseBits_le sources k p n x bits)

/-! ## §3 The decoded family's limits, read off at a length-only argument -/

/-- The XOR sample arity the decoded limits are taken at.  `symmetricLimits`
(`Proof/CaseAnalysis/SampledWitness.lean`) forms `request.arity + r + 1`, and
`actual_arity` (`Proof/CaseAnalysis/WitnessAritySeam.lean`) is the `rfl` that says
`request.arity` is `max (nativeWidth n) minimumArity` -- STAGEFIELDS' `stageArity`
(`Proof/CaseAnalysis/FinalStageFields.lean`) -- with no input and no oracle in
it. -/
def sampleArity (n : ℕ) : ℕ :=
  CloseoutFinalC10StageFields.stageArity sources k n
    + clauseWidth p.clauseDegree (nativeWidthOf sources k n) + 1

/-- `Average.limits`' `coefficientBitCap` (`Proof/CaseAnalysis/WitnessAverage.lean`)
is `natBitLength (B * max 1 D)`, and `symmetricLimits` supplies
`D := 2 * 2 ^ clauseBits`.  The guessed oracle reaches this field through
`clauseBits` and NOTHING ELSE. -/
theorem symLimits_coefficientBitCap (n : ℕ) (x : BitInput n) (bits : List Bool) :
    (C10TotalDecode.symLimits sources k (PolynomialClock.ordinaryClock k) p x
        (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k)
          p.degree n bits)).coefficientBitCap
      = natBitLength (CloseoutXor.cap (zeta (constantsOf sources))
          (sampleArity sources k p n) p.copies
        * max 1 (2 * 2 ^ (pcppOf sources k p x bits).clauseBits)) := rfl

/-- The same reading for `termCap`, which is `D * J`. -/
theorem symLimits_termCap (n : ℕ) (x : BitInput n) (bits : List Bool) :
    (C10TotalDecode.symLimits sources k (PolynomialClock.ordinaryClock k) p x
        (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k)
          p.degree n bits)).termCap
      = 2 * 2 ^ (pcppOf sources k p x bits).clauseBits
        * xorTermBound (zeta (constantsOf sources)) (sampleArity sources k p n) p.copies := rfl

/-- The threshold branch's limits differ from the symmetric branch's only in the
wire and description caps; the term cap is the same number. -/
theorem thrLimits_termCap (n : ℕ) (x : BitInput n) (bits : List Bool) :
    (C10TotalDecode.thrLimits sources k (PolynomialClock.ordinaryClock k) p x
        (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k)
          p.degree n bits)).termCap
      = (C10TotalDecode.symLimits sources k (PolynomialClock.ordinaryClock k) p x
          (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k)
            p.degree n bits)).termCap := rfl

theorem natBitLength_mono {a b : ℕ} (h : a ≤ b) : natBitLength a ≤ natBitLength b :=
  Nat.add_le_add_right (Nat.log_mono_right h) 1

/-! ## §4 The two floors, both functions of the input length -/

/-- The uniform coefficient-bit cap. -/
def coefficientBitFloor (n : ℕ) : ℕ :=
  natBitLength (CloseoutXor.cap (zeta (constantsOf sources))
      (sampleArity sources k p n) p.copies
    * max 1 (2 * clauseCap sources k p.degree n))

/-- The uniform term cap -- the coordinate polynomials' monomial count. -/
def termFloor (n : ℕ) : ℕ :=
  2 * clauseCap sources k p.degree n
    * xorTermBound (zeta (constantsOf sources)) (sampleArity sources k p n) p.copies

/-- **`entryWidth`'s uniform coefficient floor**, the premise
`stage_field_hcoefficients` (`Proof/CaseAnalysis/FinalStageFields.lean`) asks
for. -/
def coefficientFloor (n : ℕ) : ℕ :=
  Nat.log 2 (clauseCap sources k p.degree n) + 4 * coefficientBitFloor sources k p n + 3

theorem coefficientBitCap_le (n : ℕ) (x : BitInput n) (bits : List Bool) :
    (C10TotalDecode.symLimits sources k (PolynomialClock.ordinaryClock k) p x
        (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k)
          p.degree n bits)).coefficientBitCap
      ≤ coefficientBitFloor sources k p n := by
  rw [symLimits_coefficientBitCap sources k p n x bits]
  refine natBitLength_mono (Nat.mul_le_mul_left _ (max_le_max le_rfl ?_))
  exact Nat.mul_le_mul_left 2 (two_pow_clauseBits_le sources k p n x bits)

theorem termCap_le (n : ℕ) (x : BitInput n) (bits : List Bool) :
    (C10TotalDecode.symLimits sources k (PolynomialClock.ordinaryClock k) p x
        (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k)
          p.degree n bits)).termCap
      ≤ termFloor sources k p n := by
  rw [symLimits_termCap sources k p n x bits]
  exact Nat.mul_le_mul_right _
    (Nat.mul_le_mul_left 2 (two_pow_clauseBits_le sources k p n x bits))

/-! ## §5 The three premises -/

/-- **`hcoefficients`' premise, discharged.** -/
theorem coefficientBound_le (n : ℕ) (x : BitInput n) (w : List Bool) :
    C10SiteCoefficientsFit.coefficientBound
        (C10TotalDecode.symLimits sources k (PolynomialClock.ordinaryClock k) p x
          (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n w))
        (pcppOf sources k p x w)
      ≤ coefficientFloor sources k p n := by
  have h1 := clauseBits_le sources k p n x w
  have h2 := coefficientBitCap_le sources k p n x w
  unfold C10SiteCoefficientsFit.coefficientBound coefficientFloor
  omega

/-- **`StageBlock.hcoefficients` (`Proof/CaseAnalysis/FinalStageContracts.lean`),
UNCONDITIONAL**, at `S.coordinate := stageCoordinate` and
`S.entryWidth := stageEntryWidth … coefficientFloor`. -/
theorem stage_field_hcoefficients_uniform :
    ∀ (n : ℕ) (x : BitInput n) (bits : List Bool),
      Soundness.cutoff (constantsOf sources) ≤ n →
      ∀ (ph : Phase) (address : Fin (2 ^ (pcppOf sources k p x bits).clauseBits)),
        CoefficientsFit
          (CloseoutFinalC10StageFields.stageEntryWidth sources k p
            (coefficientFloor sources k p) n)
          (siteCalls ph (pcppOf sources k p x bits)
            (stageCoordinate sources k p n x bits) C10TotalDecode.Atom.systematic address) :=
  CloseoutFinalC10StageFields.stage_field_hcoefficients sources k p
    (coefficientFloor sources k p) (coefficientBound_le sources k p)

/-! ## §6 `hfuel`'s coordinate-degree cap -- the same quantity, third use -/

theorem transportTerms_length {Circuit : CanonicalWitnessCodec.CircuitFamily} {source target : ℕ}
    (h : source = target) (terms : List (LegalCircuitTerm Circuit source)) :
    (transportTerms h terms).length = terms.length := by
  subst h
  rfl

theorem linearPolynomial_monomials_length {Circuit : CanonicalWitnessCodec.CircuitFamily} {q : ℕ}
    (terms : List (LegalCircuitTerm Circuit q)) :
    (linearPolynomial terms).monomials.length = terms.length := by
  unfold linearPolynomial
  simp

theorem mapPolynomial_monomials_length {Source Target : Type} {degree : ℕ}
    (F : Source → Target) (polynomial : CircuitPolynomial Source degree) :
    (mapPolynomial F polynomial).monomials.length = polynomial.monomials.length := by
  unfold mapPolynomial
  simp

/-- Every coordinate of a decoded family has at most `termCap` monomials:
`familyCoordinate` (`Proof/CaseAnalysis/FinalExactnessFamily.lean`) is
`linearPolynomial` of the sum's own transported term list, one monomial per term,
and `CheckedLegalCircuitSum.terms_le` (`Proof/Circuits/CanonicalWitnessCodec.lean`)
caps that list. -/
theorem familyCoordinate_monomials_length_le {Circuit : CanonicalWitnessCodec.CircuitFamily}
    {wires description : {q : ℕ} → Circuit q → ℕ}
    {limits : LegalSumLimits} {variableCount target : ℕ}
    (harity : limits.expectedArity = target)
    (family : CloseoutWitness.SumFamily Circuit wires description limits variableCount)
    (i : Fin variableCount) :
    (familyCoordinate harity family i).monomials.length ≤ limits.termCap := by
  unfold familyCoordinate
  rw [linearPolynomial_monomials_length, transportTerms_length]
  exact (family.getSum i).terms_le

theorem decodeCoordinate_monomials_length_le (n : ℕ) (x : BitInput n)
    (oracle : BooleanCircuit (nativeWidthOf sources k n)) (bits : List Bool)
    (j : Fin (CloseoutWitnessPolicy.variableCount sources k
      (PolynomialClock.ordinaryClock k) x oracle)) :
    (decodeCoordinate sources k (PolynomialClock.ordinaryClock k) p x oracle bits j).monomials.length
      ≤ (C10TotalDecode.symLimits sources k (PolynomialClock.ordinaryClock k) p x
          oracle).termCap := by
  by_cases hs : CloseoutWitness.BoundedFields.symmetric bits = true
  · rw [decodeCoordinate_sym sources k (PolynomialClock.ordinaryClock k) p x oracle bits hs j]
    exact (mapPolynomial_monomials_length _ _).trans_le
      (familyCoordinate_monomials_length_le rfl
        (C10TotalDecode.symFamilyOf sources k (PolynomialClock.ordinaryClock k) p x oracle bits) j)
  · rw [decodeCoordinate_thr sources k (PolynomialClock.ordinaryClock k) p x oracle bits hs j]
    exact (mapPolynomial_monomials_length _ _).trans_le
      (familyCoordinate_monomials_length_le rfl
        (C10TotalDecode.thrFamilyOf sources k (PolynomialClock.ordinaryClock k) p x oracle bits) j)

/-- **`stage_records_length_le`'s `hL` (`Proof/CaseAnalysis/FinalStageFields.lean`),
discharged at the pinned coordinate** -- and by the same `clauseBits` cap, since
`termCap` is `(2 * 2 ^ clauseBits) * J`. -/
theorem stage_hL_at_stageCoordinate (n : ℕ) (x : BitInput n) (bits : List Bool)
    (j : Fin ((pcppOf sources k p x bits).systematicBits
      + (pcppOf sources k p x bits).auxiliaryBits)) :
    ((stageCoordinate sources k p n x bits) j).monomials.length ≤ termFloor sources k p n :=
  (decodeCoordinate_monomials_length_le sources k p n x
    (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)
    bits j).trans (termCap_le sources k p n x bits)

/-! ## §7 `hfuel`'s call cap, and the field -/

/-- The uniform call-count cap `stage_field_hfuel`
(`Proof/CaseAnalysis/FinalStageFields.lean`) asks for. -/
def callCap (L : ℕ → ℕ) (n : ℕ) : ℕ :=
  clauseCap sources k p.degree n * CloseoutFinalC10CallCountCap.siteCap (L n)

theorem stage_records_length_le_uniform (S : StageData sources k p) (L : ℕ → ℕ)
    (hL : ∀ (n : ℕ) (x : BitInput n) (bits : List Bool) j,
      ((S.coordinate n x bits) j).monomials.length ≤ L n)
    (n : ℕ) (x : BitInput n) (bits : List Bool) (ph : Phase) :
    (records sources k p S x bits ph).length ≤ callCap sources k p L n :=
  (CloseoutFinalC10StageFields.stage_records_length_le sources k p S L hL n x bits ph).trans
    (Nat.mul_le_mul_right _ (two_pow_clauseBits_le sources k p n x bits))

/-- **`StageBlock.hfuel` (`Proof/CaseAnalysis/FinalStageContracts.lean`)** from
the coordinate cap and the budget alone: the call-count premise
`stage_field_hfuel` carries is now discharged. -/
theorem stage_field_hfuel_uniform (S : StageData sources k p) (L : ℕ → ℕ)
    (hL : ∀ (n : ℕ) (x : BitInput n) (bits : List Bool) j,
      ((S.coordinate n x bits) j).monomials.length ≤ L n)
    (hbudget : ∀ n, fuelAt sources k p S n (fun _ => callCap sources k p L n) ≤ S.budget n) :
    ∀ (n : ℕ) (x : BitInput n) (bits : List Bool),
      actualFuel sources k p S x bits ≤ S.budget n :=
  CloseoutFinalC10StageFields.stage_field_hfuel sources k p S (callCap sources k p L)
    (fun n x bits ph => stage_records_length_le_uniform sources k p S L hL n x bits ph) hbudget

/-- The budget half is free at the canonical choice: `S.budget` is a FIELD of
`StageData`, so the assembly may pin it to the cap's own `fuelAt`. -/
theorem fuel_budget_at_pin (S : StageData sources k p) (L : ℕ → ℕ)
    (hpin : ∀ n, S.budget n = fuelAt sources k p S n (fun _ => callCap sources k p L n)) :
    ∀ n, fuelAt sources k p S n (fun _ => callCap sources k p L n) ≤ S.budget n :=
  fun n => (hpin n).ge

/-! ## §8 The same quantity at a THIRD field: `hstage`'s `hfit`

`stageReady_at_polyFuel` (`Proof/CaseAnalysis/FinalFuelRepin.lean`) -- the
premise card's producer for `StageBlock.hstage` -- carries
`hfit : (pcppOf …).clauseBits ≤ clauseBitsSchedule sources k p.clauseDegree n`
(`:598`) and an `hL` of exactly §6's shape (`:596`).  So the `clauseBits`
uniformity gates THREE of the fourteen fields, not two.

`pcppOf_clause_degree` (`Proof/CaseAnalysis/FinalOracleSizeBound.lean`) does
NOT serve this one: it EXHIBITS its own `degree`, while `hfit` is pinned at
`p.clauseDegree`.  The producer at that degree is `Parameters.clauses`
(`Proof/CaseAnalysis/FinalResidualLeaves.lean`), which is a FIELD -- free at
every consumer holding `p` -- and `ClauseReady`
(`Proof/CaseAnalysis/HardnessPremises.lean`) quantifies over EVERY length and
EVERY input, not only dyadic ones.  Unlike §2 this one carries an onset, which
`hstage` can afford because its field type is guarded by `Soundness.cutoff`. -/

/-- **`hstage`'s `hfit`, from `Parameters.clauses` alone.**  `nativeWidth_ge`
(`Proof/CaseAnalysis/FinalLedgerAssembly.lean`) turns `ClauseReady`'s
width-onset into a length-onset, and `oracleOf_size_le_cap`
(`Proof/CaseAnalysis/FinalOracleSizeBound.lean`) discharges its oracle-size
premise for every guessed witness. -/
theorem clauseBits_le_schedule :
    ∃ onset : ℕ, ∀ (n : ℕ) (x : BitInput n) (bits : List Bool), onset ≤ n →
      (pcppOf sources k p x bits).clauseBits
        ≤ C10PartsSchedule.clauseBitsSchedule sources k p.clauseDegree n := by
  obtain ⟨qonset, hclause⟩ := p.clauses
  refine ⟨2 ^ qonset, ?_⟩
  intro n x bits hn
  exact hclause k (PolynomialClock.ordinaryClock k) n x
    (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)
    (C10OracleSizeBound.oracleOf_size_le_cap sources k (PolynomialClock.ordinaryClock k)
      p.degree n bits (nativeWidthOf_pos sources k n))
    (C10LedgerAssembly.nativeWidth_ge sources k (PolynomialClock.ordinaryClock k) qonset n hn)

/-- **`stageReady_at_polyFuel`'s `hq` (`Proof/CaseAnalysis/FinalFuelRepin.lean`),
free.**  `C10PartsSchedule.widthAt` (`Proof/CaseAnalysis/FinalPartsSchedule.lean`)
IS the native width, so §1's positivity is this premise verbatim. -/
theorem one_le_widthAt (n : ℕ) : 1 ≤ C10PartsSchedule.widthAt sources k n :=
  nativeWidthOf_pos sources k n

end

end NearCubicWires.RepairOrdinary.CloseoutFinalC10ClauseBitsUniform
