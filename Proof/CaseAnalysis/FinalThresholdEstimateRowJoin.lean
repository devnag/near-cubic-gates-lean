import Proof.CaseAnalysis.FinalThresholdNaturalRowPrint
import Proof.CaseAnalysis.FinalRowAnswerWord
import Proof.CaseAnalysis.FinalModeNativeStageFields

open NearCubicWires NearCubicWires.SupplierPipeline NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPrinter NearCubicWires.SupplierPrime
open NearCubicWires.SupplierRadix NearCubicWires.SourceInterfaces
open NearCubicWires.CanonicalFourfoldRowProgram NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary NearCubicWires.RepairSource.CloseoutRawRows
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.RepairOrdinary.CloseoutWitness
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule (Phase)
open NearCubicWires.ComponentwisePolynomial (CircuitMonomial)
open NearCubicWires.RepairSource (EightSources)
open scoped BigOperators

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.RepairSource.CloseoutFinal.C10ThresholdEstimateRowJoin

open C10ThresholdParityRow C10ThresholdNaturalSum C10ThresholdNaturalRowPrint
open C10SupplierCall (bank)
open C10SupplierCountStage (bank_scratch_apply scratchOf scratchOf_apply round_step_of_dock)
open C10TailComposeUniform (Atoms pcppOf)
open C10NaturalModeAtoms (nativeThresholdAtom)
open C10SumFamilyTransport (stageCoordinate)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10RowAnswerWord
  (sumMachine rowAnswerFuel sum_dock)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10ModeNativeStageFields
  (thresholdEstimate stageEstimate stageEstimate_native)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10StageFields (stageArity stageTarget)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10SupplierCalls (siteCalls)

noncomputable section

variable (a : DecompositionAlgorithm)
  (r : FourfoldRequest NormalizedThresholdThresholdCircuit)

/-! ## §1 A.13.10's four-fold sum, as the LIST the summation engine eats -/

/-- `flatMap` under `List.sum`, at `C10ExternalRowLoop.sum_map_flatMap`
(`Proof/CaseAnalysis/FinalExternalRowLoop.lean`) with the identity payload.  Nothing new: the
external-row family's own flattening lemma, specialised. -/
theorem sum_flatMap {A : Type} (l : List A) (h : A → List ℕ) :
    (l.flatMap h).sum = (l.map (fun x => (h x).sum)).sum := by
  simpa using C10ExternalRowLoop.sum_map_flatMap l h id

/-- **A.13.10's payloads, one per printed fixed-scalar row**, in the scan order
`sel → prime → seed → offset`.  The inner index type `Fin prime.val` DEPENDS on the prime, which
is why this is a nested `flatMap` over four enumerations rather than a product list: the
symmetric family (`payloadList`, `Proof/CaseAnalysis/FinalRowAnswerWord.lean`) crosses two
independent ranges, the threshold family cannot. -/
def thresholdPayloadList (liveScale listDen cutoff : ℕ) : List ℕ :=
  (Finset.univ : Finset (ThresholdRows.Selection a r)).toList.flatMap (fun sel =>
    (Finset.univ : Finset (PrimeIndex cutoff)).toList.flatMap (fun prime =>
      (Finset.univ : Finset (NormalizedOccurrenceListSeed
          (thresholdFourfoldOccurrences r) liveScale listDen)).toList.flatMap (fun seed =>
        (Finset.univ : Finset (Fin prime.val)).toList.map (fun offset =>
          scalarRowValue a r liveScale listDen sel prime seed offset))))

/-- **THE TOTAL.**  The printed fixed-scalar rows total exactly `nativeNumerator` -- A.13.10's
natural child sum.  This is the threshold analogue of `payloadList_sum`
(`Proof/CaseAnalysis/FinalRowAnswerWord.lean`), and the equation ESTIMATEJOIN recorded as
absent.  Every step is a `Finset.sum ↔ List.sum` transport; the mathematical content is
`nativeNumerator_eq_fixedScalarSum` (`Proof/CaseAnalysis/FinalThresholdNaturalRowPrint.lean`),
which already carries the extra outer partition over `Fin prime.val` by `thrOffset`. -/
theorem thresholdPayloadList_sum (liveScale listDen cutoff : ℕ) :
    (thresholdPayloadList a r liveScale listDen cutoff).sum
      = nativeNumerator a r liveScale listDen cutoff := by
  rw [nativeNumerator_eq_fixedScalarSum a r liveScale listDen cutoff]
  unfold thresholdPayloadList
  rw [sum_flatMap, Finset.sum_map_toList]
  refine Finset.sum_congr rfl (fun sel _ => ?_)
  rw [sum_flatMap, Finset.sum_map_toList]
  refine Finset.sum_congr rfl (fun prime _ => ?_)
  rw [sum_flatMap, Finset.sum_map_toList]
  refine Finset.sum_congr rfl (fun seed _ => ?_)
  exact Finset.sum_map_toList _ _

/-! ## §2 The width the record must pay -/

/-- **The total fits the record width.**  From `nativeNumerator_le`
(`Proof/CaseAnalysis/FinalThresholdNaturalSum.lean`) alone.  The hypothesis is stated at
`|G| * nativeDenominator` because A.13.10's denominator is `|primes| * |seeds| * 2 ^ q`, which is
not a power of two -- the symmetric side's `rowAnswer_lt_two_pow`
(`Proof/CaseAnalysis/FinalRowAnswerWord.lean`) has no threshold twin. -/
theorem thresholdPayloadList_sum_lt_two_pow (liveScale listDen cutoff w : ℕ)
    (hfit : Fintype.card (ThresholdRows.Selection a r) *
      nativeDenominator r liveScale listDen cutoff < 2 ^ w) :
    (thresholdPayloadList a r liveScale listDen cutoff).sum < 2 ^ w := by
  rw [thresholdPayloadList_sum]
  exact lt_of_le_of_lt (nativeNumerator_le a r liveScale listDen cutoff) hfit

/-- **Every single payload fits too.**  The payloads are naturals totalling `nativeNumerator`, so
each is under the same bound; the accumulator's per-cell hypothesis costs nothing beyond §2. -/
theorem thresholdPayload_lt_two_pow (liveScale listDen cutoff w : ℕ)
    (hfit : Fintype.card (ThresholdRows.Selection a r) *
      nativeDenominator r liveScale listDen cutoff < 2 ^ w) :
    ∀ x ∈ thresholdPayloadList a r liveScale listDen cutoff, x < 2 ^ w := by
  intro x hx
  have hle : x ≤ (thresholdPayloadList a r liveScale listDen cutoff).sum :=
    List.le_sum_of_mem hx
  have hlt := thresholdPayloadList_sum_lt_two_pow a r liveScale listDen cutoff w hfit
  omega

/-! ## §3 The payload words, and the word the engine reads -/

/-- The payload words at scalar width `w`, one per printed fixed-scalar row. -/
def thresholdPayloadWords (w liveScale listDen cutoff : ℕ) : List (List Bool) :=
  (thresholdPayloadList a r liveScale listDen cutoff).map (binary w)

@[simp] theorem thresholdPayloadWords_length (w liveScale listDen cutoff : ℕ) :
    (thresholdPayloadWords a r w liveScale listDen cutoff).length
      = (thresholdPayloadList a r liveScale listDen cutoff).length := by
  unfold thresholdPayloadWords
  exact List.length_map _

/-- **The concatenated payload words ARE the summation engine's input word.**
`CompetitorCountFold.raw` (`Proof/Hierarchy/CompetitorCountFold.lean`) is by definition the flat-mapped
binary words, so no reformatting stands between the emitted stream and the accumulator. -/
theorem thresholdPayloadWords_flatten (w liveScale listDen cutoff : ℕ) :
    (thresholdPayloadWords a r w liveScale listDen cutoff).flatten
      = CompetitorCountFold.raw w (thresholdPayloadList a r liveScale listDen cutoff) := by
  unfold thresholdPayloadWords CompetitorCountFold.raw
  rw [List.flatMap_def]

/-! ## §4 A.13.10's numerator on the C.10 band, in binary at width `w` -/

/-- **A.13.10's natural child sum on the bank, in binary.**  One `Step` of one machine, entered
and left with every head parked at `0`, carries the bank whose band holds the fixed-scalar
family's concatenated payload words to the bank whose band holds
`frame (binary w (nativeNumerator …))`.  The six ports and every tape below `278` are untouched;
the clock is `rowAnswerFuel w rows` (`Proof/CaseAnalysis/FinalRowAnswerWord.lean`), linear in
the printed-row count and the width.

The engine is `sum_dock` (`:264`) verbatim -- it is generic in `xs : List ℕ`, so the threshold
family needs no summation machinery of its own. -/
theorem nativeNumerator_bank_dock (extra : ℕ) (liveScale listDen cutoff w : ℕ)
    (hfit : Fintype.card (ThresholdRows.Selection a r) *
      nativeDenominator r liveScale listDen cutoff < 2 ^ w)
    (slots : Fin (9 + 1) → Fin (218 + (60 + extra))) (hinj : Function.Injective slots)
    (hband : ∀ j, 278 ≤ (slots j).val)
    (stream count driver input witness : List Bool) (s : ℕ → List Bool)
    (h0 : s (slots 0).val
      = CompetitorCountFold.raw w (thresholdPayloadList a r liveScale listDen cutoff))
    (h1 : s (slots 1).val = List.replicate w true)
    (h2 : s (slots 2).val = List.replicate w true)
    (h4 : s (slots 4).val = List.replicate (2 * w + 1) false)
    (h5 : s (slots 5).val = frame (binary w 0))
    (h8 : s (slots 8).val = NearCubicWires.RepairSource.VerifierDecoding.CompareMachine.word
      (thresholdPayloadList a r liveScale listDen cutoff).length)
    (hblank : ∀ j : Fin (9 + 1), j.val ≠ 0 → j.val ≠ 1 → j.val ≠ 2 → j.val ≠ 4 → j.val ≠ 5 →
      j.val ≠ 8 → s (slots j).val = []) :
    ∃ s' : ℕ → List Bool,
      ExtDecompositionBatch.Step (RecoveryFocus.machine slots sumMachine)
        (rowAnswerFuel w (thresholdPayloadList a r liveScale listDen cutoff).length)
        (fun _ => 0) (bank stream count driver input witness s)
        (fun _ => 0) (bank stream count driver input witness s') ∧
      s' (slots 5).val
        = frame (binary w (nativeNumerator a r liveScale listDen cutoff)) ∧
      (∀ i : Fin (218 + (60 + extra)), 278 ≤ i.val → (∀ j, slots j ≠ i) →
        s' i.val = s i.val) := by
  have hA : ∀ j : Fin (9 + 1),
      bank stream count driver input witness s (slots j) = s (slots j).val :=
    fun j => bank_scratch_apply stream count driver input witness s (slots j) (hband j)
  have hsum := thresholdPayloadList_sum a r liveScale listDen cutoff
  have hcells := thresholdPayload_lt_two_pow a r liveScale listDen cutoff w hfit
  have htotal := thresholdPayloadList_sum_lt_two_pow a r liveScale listDen cutoff w hfit
  obtain ⟨H', A', hstep, hzero, ht5, hframe⟩ :=
    sum_dock w (thresholdPayloadList a r liveScale listDen cutoff) hcells htotal
      slots hinj (fun _ => 0) (bank stream count driver input witness s) (fun _ => rfl)
      ((hA 0).trans h0) ((hA 1).trans h1) ((hA 2).trans h2) ((hA 4).trans h4)
      ((hA 5).trans h5) ((hA 8).trans h8)
      (fun j e0 e1 e2 e4 e5 e8 => (hA j).trans (hblank j e0 e1 e2 e4 e5 e8))
  refine ⟨scratchOf extra A' s, ?_, ?_, ?_⟩
  · exact round_step_of_dock extra
      (rowAnswerFuel w (thresholdPayloadList a r liveScale listDen cutoff).length)
      stream count driver input witness s slots hband H' A' hstep hzero hframe
  · rw [scratchOf_apply extra A' s (slots 5), ht5, hsum]
  · intro i hi hoff
    rw [scratchOf_apply extra A' s i, hframe i hoff,
      bank_scratch_apply stream count driver input witness s i hi]

/-! ## §5 The crossing no name search can make -/

/-- **THE ALIAS CROSSING.**  The route's `thresholdEstimate` numerator and A.13.10's
`nativeNumerator` are the SAME TERM -- `thresholdEstimate`'s `num` field
(`Proof/CaseAnalysis/FinalModeNativeStageFields.lean`) is literally
`nativeNumerator (decompositionOf sources) request liveScale (listDenominator …) (primeCutoff …)`.
This is what made the join invisible: the route spells the number `thresholdEstimate.num`, the
machine spells it `nativeNumerator`, and no search by NAME crosses that. -/
theorem thresholdEstimate_num_eq_nativeNumerator (sources : EightSources)
    (liveScale target : ℕ) (request : FourfoldRequest NormalizedThresholdThresholdCircuit) :
    (thresholdEstimate sources liveScale target request).num
      = nativeNumerator (decompositionOf sources) request liveScale
          (CloseoutFinalC10ThresholdRows.listDenominator (decompositionOf sources) request target)
          (CloseoutFinalC10ThresholdRows.primeCutoff (decompositionOf sources) request target) :=
  rfl

theorem nc_den_is_not_the_printed_word (sources : EightSources)
    (liveScale target : ℕ) (request : FourfoldRequest NormalizedThresholdThresholdCircuit) :
    (thresholdEstimate sources liveScale target request).den
      = nativeDenominator request liveScale
          (CloseoutFinalC10ThresholdRows.listDenominator (decompositionOf sources) request target)
          (CloseoutFinalC10ThresholdRows.primeCutoff (decompositionOf sources) request target) := by
  fail_if_success
    have _h :
        (thresholdEstimate sources liveScale target request).den
          = nativeNumerator (decompositionOf sources) request liveScale
              (CloseoutFinalC10ThresholdRows.listDenominator
                (decompositionOf sources) request target)
              (CloseoutFinalC10ThresholdRows.primeCutoff
                (decompositionOf sources) request target) := rfl
  rfl

/-! ## §6 The route's own estimate, printed by an existing machine -/

/-- **The threshold estimate on a tape.**  §4 at the route's own request and denominators,
restated so its conclusion names `thresholdEstimate`. -/
theorem thresholdEstimate_bank_dock (sources : EightSources) (extra : ℕ)
    (liveScale target w : ℕ) (request : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (hfit : Fintype.card (ThresholdRows.Selection (decompositionOf sources) request) *
      nativeDenominator request liveScale
        (CloseoutFinalC10ThresholdRows.listDenominator (decompositionOf sources) request target)
        (CloseoutFinalC10ThresholdRows.primeCutoff (decompositionOf sources) request target)
      < 2 ^ w)
    (slots : Fin (9 + 1) → Fin (218 + (60 + extra))) (hinj : Function.Injective slots)
    (hband : ∀ j, 278 ≤ (slots j).val)
    (stream count driver input witness : List Bool) (s : ℕ → List Bool)
    (h0 : s (slots 0).val = CompetitorCountFold.raw w
      (thresholdPayloadList (decompositionOf sources) request liveScale
        (CloseoutFinalC10ThresholdRows.listDenominator (decompositionOf sources) request target)
        (CloseoutFinalC10ThresholdRows.primeCutoff (decompositionOf sources) request target)))
    (h1 : s (slots 1).val = List.replicate w true)
    (h2 : s (slots 2).val = List.replicate w true)
    (h4 : s (slots 4).val = List.replicate (2 * w + 1) false)
    (h5 : s (slots 5).val = frame (binary w 0))
    (h8 : s (slots 8).val = NearCubicWires.RepairSource.VerifierDecoding.CompareMachine.word
      (thresholdPayloadList (decompositionOf sources) request liveScale
        (CloseoutFinalC10ThresholdRows.listDenominator (decompositionOf sources) request target)
        (CloseoutFinalC10ThresholdRows.primeCutoff
          (decompositionOf sources) request target)).length)
    (hblank : ∀ j : Fin (9 + 1), j.val ≠ 0 → j.val ≠ 1 → j.val ≠ 2 → j.val ≠ 4 → j.val ≠ 5 →
      j.val ≠ 8 → s (slots j).val = []) :
    ∃ s' : ℕ → List Bool,
      ExtDecompositionBatch.Step (RecoveryFocus.machine slots sumMachine)
        (rowAnswerFuel w
          (thresholdPayloadList (decompositionOf sources) request liveScale
            (CloseoutFinalC10ThresholdRows.listDenominator
              (decompositionOf sources) request target)
            (CloseoutFinalC10ThresholdRows.primeCutoff
              (decompositionOf sources) request target)).length)
        (fun _ => 0) (bank stream count driver input witness s)
        (fun _ => 0) (bank stream count driver input witness s') ∧
      s' (slots 5).val
        = frame (binary w (thresholdEstimate sources liveScale target request).num) ∧
      (∀ i : Fin (218 + (60 + extra)), 278 ≤ i.val → (∀ j, slots j ≠ i) →
        s' i.val = s i.val) := by
  obtain ⟨s', hstep, ht5, hrest⟩ := nativeNumerator_bank_dock (decompositionOf sources) request
    extra liveScale
    (CloseoutFinalC10ThresholdRows.listDenominator (decompositionOf sources) request target)
    (CloseoutFinalC10ThresholdRows.primeCutoff (decompositionOf sources) request target) w hfit
    slots hinj hband stream count driver input witness s h0 h1 h2 h4 h5 h8 hblank
  refine ⟨s', hstep, ?_, hrest⟩
  rw [ht5, thresholdEstimate_num_eq_nativeNumerator]

theorem stageEstimate_threshold_bank_dock (sources : EightSources) (liveScale k : ℕ) {gamma : ℝ}
    (p : Parameters sources gamma) (extra : ℕ) {n : ℕ} (x : BitInput n) (bits : List Bool)
    (ph : Phase) (address : Fin (2 ^ (pcppOf sources k p x bits).clauseBits))
    (monomial : CircuitMonomial (Atoms sources k p x bits) 4)
    (hmem : monomial ∈ (siteCalls ph (pcppOf sources k p x bits)
      (stageCoordinate sources k p n x bits) C10TotalDecode.Atom.systematic address).monomials)
    (hthr : BoundedFields.symmetric bits = false) (w : ℕ)
    (hfit : Fintype.card (ThresholdRows.Selection (decompositionOf sources)
        ⟨stageArity sources k n, monomial.factors.map nativeThresholdAtom⟩) *
      nativeDenominator ⟨stageArity sources k n, monomial.factors.map nativeThresholdAtom⟩
        liveScale
        (CloseoutFinalC10ThresholdRows.listDenominator (decompositionOf sources)
          ⟨stageArity sources k n, monomial.factors.map nativeThresholdAtom⟩
          (stageTarget sources p (stageArity sources k n)))
        (CloseoutFinalC10ThresholdRows.primeCutoff (decompositionOf sources)
          ⟨stageArity sources k n, monomial.factors.map nativeThresholdAtom⟩
          (stageTarget sources p (stageArity sources k n)))
      < 2 ^ w)
    (slots : Fin (9 + 1) → Fin (218 + (60 + extra))) (hinj : Function.Injective slots)
    (hband : ∀ j, 278 ≤ (slots j).val)
    (stream count driver input witness : List Bool) (s : ℕ → List Bool)
    (h0 : s (slots 0).val = CompetitorCountFold.raw w
      (thresholdPayloadList (decompositionOf sources)
        ⟨stageArity sources k n, monomial.factors.map nativeThresholdAtom⟩ liveScale
        (CloseoutFinalC10ThresholdRows.listDenominator (decompositionOf sources)
          ⟨stageArity sources k n, monomial.factors.map nativeThresholdAtom⟩
          (stageTarget sources p (stageArity sources k n)))
        (CloseoutFinalC10ThresholdRows.primeCutoff (decompositionOf sources)
          ⟨stageArity sources k n, monomial.factors.map nativeThresholdAtom⟩
          (stageTarget sources p (stageArity sources k n)))))
    (h1 : s (slots 1).val = List.replicate w true)
    (h2 : s (slots 2).val = List.replicate w true)
    (h4 : s (slots 4).val = List.replicate (2 * w + 1) false)
    (h5 : s (slots 5).val = frame (binary w 0))
    (h8 : s (slots 8).val = NearCubicWires.RepairSource.VerifierDecoding.CompareMachine.word
      (thresholdPayloadList (decompositionOf sources)
        ⟨stageArity sources k n, monomial.factors.map nativeThresholdAtom⟩ liveScale
        (CloseoutFinalC10ThresholdRows.listDenominator (decompositionOf sources)
          ⟨stageArity sources k n, monomial.factors.map nativeThresholdAtom⟩
          (stageTarget sources p (stageArity sources k n)))
        (CloseoutFinalC10ThresholdRows.primeCutoff (decompositionOf sources)
          ⟨stageArity sources k n, monomial.factors.map nativeThresholdAtom⟩
          (stageTarget sources p (stageArity sources k n)))).length)
    (hblank : ∀ j : Fin (9 + 1), j.val ≠ 0 → j.val ≠ 1 → j.val ≠ 2 → j.val ≠ 4 → j.val ≠ 5 →
      j.val ≠ 8 → s (slots j).val = []) :
    ∃ s' : ℕ → List Bool,
      ExtDecompositionBatch.Step (RecoveryFocus.machine slots sumMachine)
        (rowAnswerFuel w
          (thresholdPayloadList (decompositionOf sources)
            ⟨stageArity sources k n, monomial.factors.map nativeThresholdAtom⟩ liveScale
            (CloseoutFinalC10ThresholdRows.listDenominator (decompositionOf sources)
              ⟨stageArity sources k n, monomial.factors.map nativeThresholdAtom⟩
              (stageTarget sources p (stageArity sources k n)))
            (CloseoutFinalC10ThresholdRows.primeCutoff (decompositionOf sources)
              ⟨stageArity sources k n, monomial.factors.map nativeThresholdAtom⟩
              (stageTarget sources p (stageArity sources k n)))).length)
        (fun _ => 0) (bank stream count driver input witness s)
        (fun _ => 0) (bank stream count driver input witness s') ∧
      s' (slots 5).val
        = frame (binary w (stageEstimate sources liveScale k p n x bits monomial.factors).num) ∧
      (∀ i : Fin (218 + (60 + extra)), 278 ≤ i.val → (∀ j, slots j ≠ i) →
        s' i.val = s i.val) := by
  have hnum : (stageEstimate sources liveScale k p n x bits monomial.factors).num
      = (thresholdEstimate sources liveScale (stageTarget sources p (stageArity sources k n))
          ⟨stageArity sources k n, monomial.factors.map nativeThresholdAtom⟩).num := by
    have h := congrArg Prod.fst
      (stageEstimate_native sources liveScale k p x bits ph address monomial hmem)
    simpa [hthr] using h
  obtain ⟨s', hstep, ht5, hrest⟩ := thresholdEstimate_bank_dock sources extra liveScale
    (stageTarget sources p (stageArity sources k n)) w
    ⟨stageArity sources k n, monomial.factors.map nativeThresholdAtom⟩ hfit
    slots hinj hband stream count driver input witness s h0 h1 h2 h4 h5 h8 hblank
  exact ⟨s', hstep, by rw [ht5, hnum], hrest⟩

end
end NearCubicWires.RepairSource.CloseoutFinal.C10ThresholdEstimateRowJoin
