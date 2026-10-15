import Proof.CaseAnalysis.FinalExternalRowLoop
import Proof.CaseAnalysis.FinalNativeReload

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires
open NearCubicWires.LocalBitMultitape
open NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierEstimator
open NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimator
open NearCubicWires.ExtDecompositionBatch (Step)

namespace NearCubicWires.RepairSource.CloseoutFinal.C10RowOrdering

/-! ## 1. The key the chaining condition compares -/

section Ordering

variable (liveScale : ℕ) (targetDenominator : ℕ → ℕ)
  (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)

/-- One round of the family loop: a seed of A.13.9 crossed with an offset tuple of A.3 :1976. -/
abbrev Round : Type :=
  NormalizedOccurrenceListSeed (symmetricFourfoldOccurrences request) liveScale
      (C10ExternalRowLoop.familyDenominator targetDenominator request) ×
    (Fin request.circuits.length → ℕ)

/-- The comparison `native_step`'s `hgrow` makes, as a Boolean relation on rounds. -/
def streamLE (row : Round liveScale targetDenominator request → EquationRow.Input)
    (x y : Round liveScale targetDenominator request) : Bool :=
  decide ((Header.stream (row x)).length ≤ (Header.stream (row y)).length)

theorem streamLE_trans (row : Round liveScale targetDenominator request → EquationRow.Input)
    (x y z : Round liveScale targetDenominator request)
    (hxy : streamLE liveScale targetDenominator request row x y = true)
    (hyz : streamLE liveScale targetDenominator request row y z = true) :
    streamLE liveScale targetDenominator request row x z = true := by
  simp only [streamLE, decide_eq_true_eq] at hxy hyz ⊢
  exact le_trans hxy hyz

theorem streamLE_total (row : Round liveScale targetDenominator request → EquationRow.Input)
    (x y : Round liveScale targetDenominator request) :
    (streamLE liveScale targetDenominator request row x y ||
      streamLE liveScale targetDenominator request row y x) = true := by
  simp only [streamLE, Bool.or_eq_true, decide_eq_true_eq]
  exact Nat.le_total _ _

/-! ## 2. The re-ordered enumeration, and the two facts that make it free -/

/-- **The re-ordered enumeration**: A.3 :1976's (seed, offset) rounds sorted by the length of the
printed cut stream of the row each round prints. -/
noncomputable def orderedPairList
    (row : Round liveScale targetDenominator request → EquationRow.Input) :
    List (Round liveScale targetDenominator request) :=
  (C10ExternalRowLoop.pairList liveScale targetDenominator request).mergeSort
    (streamLE liveScale targetDenominator request row)

/-- **FACT ONE — the re-ordering is a permutation of the loop's own enumeration.** -/
theorem orderedPairList_perm (row : Round liveScale targetDenominator request → EquationRow.Input) :
    (orderedPairList liveScale targetDenominator request row).Perm
      (C10ExternalRowLoop.pairList liveScale targetDenominator request) :=
  List.mergeSort_perm _ _

/-- The round count is unchanged. -/
theorem orderedPairList_length
    (row : Round liveScale targetDenominator request → EquationRow.Input) :
    (orderedPairList liveScale targetDenominator request row).length =
      (C10ExternalRowLoop.pairList liveScale targetDenominator request).length :=
  List.length_mergeSort _

/-- The round count, in the closed form `C10ExternalRowLoop.pairList_length` (`:334`) gives it. -/
theorem orderedPairList_card (spectrum : SourceInterfaces.ExpanderSpectrumContract)
    (row : Round liveScale targetDenominator request → EquationRow.Input) :
    (orderedPairList liveScale targetDenominator request row).length =
      2 ^ C10SupplierWidth.seedExponent request liveScale (targetDenominator request.q) *
        (C10SupplierSelect.offsetRange request).card := by
  rw [orderedPairList_length]
  exact C10ExternalRowLoop.pairList_length spectrum liveScale targetDenominator request

/-- **THE COUNT SURVIVES THE RE-ORDERING.**  A.13.9's double sum is a sum over a set, and a list sum
is a permutation invariant, so the re-ordered family's record-word payloads still total
`FiniteRowAggregation.acceptanceCount`. -/
theorem orderedTotal_eq_acceptanceCount (spectrum : SourceInterfaces.ExpanderSpectrumContract)
    (row : Round liveScale targetDenominator request → EquationRow.Input) :
    (((orderedPairList liveScale targetDenominator request row).map
        (fun p => C10ExternalRowLoop.pairValue liveScale targetDenominator request p.1 p.2)).sum) =
      ((symmetricFourfoldRows spectrum liveScale targetDenominator).aggregation
        request).acceptanceCount := by
  rw [(((orderedPairList_perm liveScale targetDenominator request row).map
    (fun p => C10ExternalRowLoop.pairValue liveScale targetDenominator request p.1 p.2)).sum_eq)]
  exact C10ExternalRowLoop.familyTotal_eq_acceptanceCount spectrum liveScale targetDenominator
    request

/-- **FACT TWO — the re-ordering is sorted by the printed header length.** -/
theorem orderedPairList_sorted
    (row : Round liveScale targetDenominator request → EquationRow.Input) :
    (orderedPairList liveScale targetDenominator request row).Pairwise
      (fun x y => (Header.stream (row x)).length ≤ (Header.stream (row y)).length) := by
  refine (List.pairwise_mergeSort (streamLE_trans liveScale targetDenominator request row)
    (streamLE_total liveScale targetDenominator request row) _).imp ?_
  intro x y hxy
  simpa only [streamLE, decide_eq_true_eq] using hxy

/-- The same, as the CONSECUTIVE-rounds condition the family loop chains through. -/
theorem orderedPairList_chain
    (row : Round liveScale targetDenominator request → EquationRow.Input) :
    List.IsChain (fun x y => (Header.stream (row x)).length ≤ (Header.stream (row y)).length)
      (orderedPairList liveScale targetDenominator request row) :=
  (orderedPairList_sorted liveScale targetDenominator request row).isChain

/-- **`hgrow`, at rounds `k` and `k+1` of the re-ordered enumeration.** -/
theorem orderedPairList_growth
    (row : Round liveScale targetDenominator request → EquationRow.Input) (k : ℕ)
    (hk : k + 1 < (orderedPairList liveScale targetDenominator request row).length) :
    (Header.stream (row ((orderedPairList liveScale targetDenominator request row)[k]'
        (Nat.lt_of_succ_lt hk)))).length ≤
      (Header.stream (row ((orderedPairList liveScale targetDenominator request row)[k + 1]'
        hk))).length :=
  List.pairwise_iff_getElem.mp (orderedPairList_sorted liveScale targetDenominator request row)
    k (k + 1) (Nat.lt_of_succ_lt hk) hk (Nat.lt_succ_self k)

/-- The row round `k` of the re-ordered enumeration prints. -/
noncomputable def orderedRow (row : Round liveScale targetDenominator request → EquationRow.Input)
    (k : ℕ) (hk : k < (orderedPairList liveScale targetDenominator request row).length) :
    EquationRow.Input :=
  row ((orderedPairList liveScale targetDenominator request row)[k]'hk)

/-- **`hgrow` DISCHARGED.**  `C10NativeReload.native_step`
(`Proof/CaseAnalysis/FinalNativeReload.lean`) at two consecutive rounds of the re-ordered
enumeration: the writer that carries slot `52` from round `k`'s printed cut stream to round `k+1`'s
runs with NO growth hypothesis left. -/
theorem ordered_native_step (row : Round liveScale targetDenominator request → EquationRow.Input)
    (k : ℕ) (hk : k + 1 < (orderedPairList liveScale targetDenominator request row).length)
    (p : Program) (D : ℕ) (H : Fin (C10NativeReload.tapes p) → ℕ)
    (A : Fin (C10NativeReload.tapes p) → List Bool)
    (hfit : (Header.stream
      (orderedRow liveScale targetDenominator request row (k + 1) hk)).length ≤ D)
    (hwh : H (C10NativeReload.wordPort p) = 0)
    (hnh : H (C10NativeReload.nativeSlot p) = 0)
    (hdh : H (C10NativeReload.drivePort p) = 0)
    (hlh : H (C10NativeReload.logSlot p) = 0)
    (hword : A (C10NativeReload.wordPort p) =
      Header.stream (orderedRow liveScale targetDenominator request row (k + 1) hk))
    (hnative : A (C10NativeReload.nativeSlot p) =
      Header.stream (orderedRow liveScale targetDenominator request row k
        (Nat.lt_of_succ_lt hk)))
    (hdrive : A (C10NativeReload.drivePort p) = List.replicate
      (Header.stream (orderedRow liveScale targetDenominator request row (k + 1) hk)).length true)
    (hlog : A (C10NativeReload.logSlot p) = List.replicate (D + 1) false) :
    ∃ B, Step (C10NativeReload.machine p)
        (2 * (Header.stream
          (orderedRow liveScale targetDenominator request row (k + 1) hk)).length + 4) H A H B ∧
      B (C10NativeReload.nativeSlot p) =
        Header.stream (orderedRow liveScale targetDenominator request row (k + 1) hk) ∧
      B (C10NativeReload.wordPort p) =
        Header.stream (orderedRow liveScale targetDenominator request row (k + 1) hk) ∧
      B (C10NativeReload.drivePort p) = List.replicate
        (Header.stream
          (orderedRow liveScale targetDenominator request row (k + 1) hk)).length true ∧
      B (C10NativeReload.logSlot p) = List.replicate (D + 1) false ∧
      (∀ i, (∀ j, C10NativeReload.slots p j ≠ i) → B i = A i) :=
  C10NativeReload.native_step p
    (orderedRow liveScale targetDenominator request row k (Nat.lt_of_succ_lt hk))
    (orderedRow liveScale targetDenominator request row (k + 1) hk) D H A
    (orderedPairList_growth liveScale targetDenominator request row k hk) hfit hwh hnh hdh hlh
    hword hnative hdrive hlog

/-! ## 3. The family loop over the re-ordered enumeration -/

/-- The family's record words, in the re-ordered scan order. -/
noncomputable def orderedWordList
    (row : Round liveScale targetDenominator request → EquationRow.Input)
    (b : ℕ) (est : CompetitorValidity.Estimate) (denominator : ℕ) : List (List Bool) :=
  (orderedPairList liveScale targetDenominator request row).map
    (fun p => C10ExternalRowLoop.pairWord liveScale targetDenominator request b est denominator
      p.1 p.2)

/-- The accumulated stream of the re-ordered family. -/
noncomputable def orderedFamilyStream
    (row : Round liveScale targetDenominator request → EquationRow.Input)
    (b : ℕ) (est : CompetitorValidity.Estimate) (denominator : ℕ) : List Bool :=
  (orderedWordList liveScale targetDenominator request row b est denominator).flatten

theorem orderedWordList_length (spectrum : SourceInterfaces.ExpanderSpectrumContract)
    (row : Round liveScale targetDenominator request → EquationRow.Input)
    (b : ℕ) (est : CompetitorValidity.Estimate) (denominator : ℕ) :
    (orderedWordList liveScale targetDenominator request row b est denominator).length =
      2 ^ C10SupplierWidth.seedExponent request liveScale (targetDenominator request.q) *
        (C10SupplierSelect.offsetRange request).card := by
  unfold orderedWordList
  rw [List.length_map]
  exact orderedPairList_card liveScale targetDenominator request spectrum row

/-- **The family loop, re-ordered.**  `C10ExternalRowLoop.family_run`
(`Proof/CaseAnalysis/FinalExternalRowLoop.lean`) over `orderedPairList`: the same driver, the same
fuel, the whole family's record stream on the body's output slot, and the same
`FiniteRowAggregation.acceptanceCount`. -/
theorem ordered_family_run (spectrum : SourceInterfaces.ExpanderSpectrumContract)
    (row : Round liveScale targetDenominator request → EquationRow.Input)
    {tp st : ℕ} (body : Machine tp st)
    (source : ℕ → List Bool → Configuration tp st) (slot : Fin tp) (rowCost : ℕ)
    (b : ℕ) (est : CompetitorValidity.Estimate) (denominator : ℕ) (out : List Bool)
    (hslot : ∀ k pre, (source k pre).tapes slot = pre)
    (hstart : ∀ k < (orderedWordList liveScale targetDenominator request row b est
        denominator).length,
      ∀ pre, (source k pre).control = body.start)
    (hrow : ∀ k < (orderedWordList liveScale targetDenominator request row b est
        denominator).length,
      ∀ pre, ∃ rc : ExecutionReceipt tp st,
        runFrom body rowCost (source k pre) = some rc ∧
        rc.final.heads = (source (k + 1) (pre ++
          (orderedWordList liveScale targetDenominator request row b est
            denominator).getD k [])).heads ∧
        rc.final.tapes = (source (k + 1) (pre ++
          (orderedWordList liveScale targetDenominator request row b est
            denominator).getD k [])).tapes ∧
        rc.steps ≤ rowCost) :
    ∃ T, Step (C10ExternalRowLoop.familyWriter body)
        (C10ExternalRowLoop.familyFuel
          (orderedWordList liveScale targetDenominator request row b est denominator).length rowCost)
        (RepairSource.VerifierDecoding.RepeatMachine.cfg 0 (source 0 out)
          (orderedWordList liveScale targetDenominator request row b est
            denominator).length 1).heads
        (RepairSource.VerifierDecoding.RepeatMachine.cfg 0 (source 0 out)
          (orderedWordList liveScale targetDenominator request row b est
            denominator).length 1).tapes
        (RepairSource.VerifierDecoding.RepeatMachine.cfg 3
          (source (orderedWordList liveScale targetDenominator request row b est denominator).length
            (out ++ orderedFamilyStream liveScale targetDenominator request row b est denominator))
          (orderedWordList liveScale targetDenominator request row b est
            denominator).length 1).heads T ∧
      T (slot.castAdd 1) =
        out ++ orderedFamilyStream liveScale targetDenominator request row b est denominator ∧
      (((orderedPairList liveScale targetDenominator request row).map
          (fun p => C10ExternalRowLoop.pairValue liveScale targetDenominator request p.1 p.2)).sum) =
        ((symmetricFourfoldRows spectrum liveScale targetDenominator).aggregation
          request).acceptanceCount := by
  obtain ⟨r, hr, hf, hst⟩ := CloseoutRowsDegreeLoop.loop_run body source
    (fun k => (orderedWordList liveScale targetDenominator request row b est denominator).getD k [])
    rowCost (orderedWordList liveScale targetDenominator request row b est denominator).length
    hstart hrow out
  rw [C10ExternalRowLoop.flatten_getD
    (orderedWordList liveScale targetDenominator request row b est denominator)] at hf
  refine ⟨_, ⟨r, hr, congrArg Configuration.heads hf, congrArg Configuration.tapes hf, hst⟩, ?_,
    orderedTotal_eq_acceptanceCount liveScale targetDenominator request spectrum row⟩
  rw [C10SupplierSelect.cfg_tapes_castAdd]
  exact hslot _ _

end Ordering

/-! ## 4. The key, at the C10 supplier family's own printed rows -/

section RowFields

variable {q : ℕ} (a : DecompositionAlgorithm) (live : Finset (Fin q))
  (occ : List (SupportedNormalizedGate q)) (s : ℕ)
  (harity : (s + 1) / 2 + s / 2 = liveᶜ.card) (w : ℕ) (hs : 67 ≤ s) (hpos : 1 ≤ w)
  (hload : 200 * (live.card + w * (live.card + 2)) ≤ s)

/-- `C10SupplierRowInput.rowInput`'s half-width `d` is `(s+1)/2`: the printed polynomial does not
enter it. -/
theorem rowInput_d (P P' : StructuralGF2Polynomial)
    (hmon : (CloseoutRowsUniversal.lower a live occ P).length < 2 ^ w)
    (hmon' : (CloseoutRowsUniversal.lower a live occ P').length < 2 ^ w) :
    (C10SupplierRowInput.rowInput a live occ s harity P' w hs hmon' hpos hload).d =
      (C10SupplierRowInput.rowInput a live occ s harity P w hs hmon hpos hload).d := rfl

/-- Its scalar width `p` is fixed by the pool and `live.card` alone. -/
theorem rowInput_p (P P' : StructuralGF2Polynomial)
    (hmon : (CloseoutRowsUniversal.lower a live occ P).length < 2 ^ w)
    (hmon' : (CloseoutRowsUniversal.lower a live occ P').length < 2 ^ w) :
    (C10SupplierRowInput.rowInput a live occ s harity P' w hs hmon' hpos hload).p =
      (C10SupplierRowInput.rowInput a live occ s harity P w hs hmon hpos hload).p := rfl

/-- Its parity flag `odd` is `decide (s % 2 = 1)`. -/
theorem rowInput_odd (P P' : StructuralGF2Polynomial)
    (hmon : (CloseoutRowsUniversal.lower a live occ P).length < 2 ^ w)
    (hmon' : (CloseoutRowsUniversal.lower a live occ P').length < 2 ^ w) :
    (C10SupplierRowInput.rowInput a live occ s harity P' w hs hmon' hpos hload).odd =
      (C10SupplierRowInput.rowInput a live occ s harity P w hs hmon hpos hload).odd := rfl

end RowFields

section FamilyRows

variable (liveScale : ℕ) (targetDenominator : ℕ → ℕ)
  (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
  (a : DecompositionAlgorithm) (s : ℕ)
  (harity : (s + 1) / 2 + s / 2 =
    (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)ᶜ.card)
  (w : ℕ) (hs : 67 ≤ s) (hpos : 1 ≤ w)
  (hload : 200 * ((normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale).card +
    w * ((normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale).card + 2)) ≤ s)
  (hmon : ∀ p : Round liveScale targetDenominator request,
    (CloseoutRowsUniversal.lower a
      (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)
      (symmetricFourfoldOccurrences request)
      (C10ExternalRowLoop.familyPolynomial liveScale targetDenominator request p.1 p.2)).length <
      2 ^ w)

noncomputable def familyRow (p : Round liveScale targetDenominator request) : EquationRow.Input :=
  C10SupplierRowInput.rowInput a
    (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)
    (symmetricFourfoldOccurrences request) s harity
    (C10ExternalRowLoop.familyPolynomial liveScale targetDenominator request p.1 p.2) w hs
    (hmon p) hpos hload

/-- Every row of the family has the same `d`. -/
theorem familyRow_d (p p' : Round liveScale targetDenominator request) :
    (familyRow liveScale targetDenominator request a s harity w hs hpos hload hmon p').d =
      (familyRow liveScale targetDenominator request a s harity w hs hpos hload hmon p).d :=
  rowInput_d a (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)
    (symmetricFourfoldOccurrences request) s harity w hs hpos hload
    (C10ExternalRowLoop.familyPolynomial liveScale targetDenominator request p.1 p.2)
    (C10ExternalRowLoop.familyPolynomial liveScale targetDenominator request p'.1 p'.2)
    (hmon p) (hmon p')

/-- Every row of the family has the same `p`. -/
theorem familyRow_p (p p' : Round liveScale targetDenominator request) :
    (familyRow liveScale targetDenominator request a s harity w hs hpos hload hmon p').p =
      (familyRow liveScale targetDenominator request a s harity w hs hpos hload hmon p).p :=
  rowInput_p a (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)
    (symmetricFourfoldOccurrences request) s harity w hs hpos hload
    (C10ExternalRowLoop.familyPolynomial liveScale targetDenominator request p.1 p.2)
    (C10ExternalRowLoop.familyPolynomial liveScale targetDenominator request p'.1 p'.2)
    (hmon p) (hmon p')

/-- Every row of the family has the same `odd`. -/
theorem familyRow_odd (p p' : Round liveScale targetDenominator request) :
    (familyRow liveScale targetDenominator request a s harity w hs hpos hload hmon p').odd =
      (familyRow liveScale targetDenominator request a s harity w hs hpos hload hmon p).odd :=
  rowInput_odd a (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)
    (symmetricFourfoldOccurrences request) s harity w hs hpos hload
    (C10ExternalRowLoop.familyPolynomial liveScale targetDenominator request p.1 p.2)
    (C10ExternalRowLoop.familyPolynomial liveScale targetDenominator request p'.1 p'.2)
    (hmon p) (hmon p')

/-- The C10 supplier family's rounds, re-ordered by printed-header length. -/
noncomputable def orderedFamily : List (Round liveScale targetDenominator request) :=
  orderedPairList liveScale targetDenominator request
    (familyRow liveScale targetDenominator request a s harity w hs hpos hload hmon)

/-- **The printed headers of the C10 family never shrink along the re-ordered enumeration.** -/
theorem familyRow_growth (k : ℕ)
    (hk : k + 1 <
      (orderedFamily liveScale targetDenominator request a s harity w hs hpos hload hmon).length) :
    (Header.stream (familyRow liveScale targetDenominator request a s harity w hs hpos hload hmon
        ((orderedFamily liveScale targetDenominator request a s harity w hs hpos hload hmon)[k]'
          (Nat.lt_of_succ_lt hk)))).length ≤
      (Header.stream (familyRow liveScale targetDenominator request a s harity w hs hpos hload hmon
        ((orderedFamily liveScale targetDenominator request a s harity w hs hpos hload hmon)[k + 1]'
          hk))).length :=
  orderedPairList_growth liveScale targetDenominator request
    (familyRow liveScale targetDenominator request a s harity w hs hpos hload hmon) k hk

/-- **The cut count is non-decreasing along it** — `C10NativeReload.growth_iff_cuts`
(`Proof/CaseAnalysis/FinalNativeReload.lean`) at the family's rows, whose `d`, `p` and `odd` are
independent of the printed polynomial. -/
theorem familyRow_cuts_growth (k : ℕ)
    (hk : k + 1 <
      (orderedFamily liveScale targetDenominator request a s harity w hs hpos hload hmon).length) :
    (familyRow liveScale targetDenominator request a s harity w hs hpos hload hmon
        ((orderedFamily liveScale targetDenominator request a s harity w hs hpos hload hmon)[k]'
          (Nat.lt_of_succ_lt hk))).cuts.length ≤
      (familyRow liveScale targetDenominator request a s harity w hs hpos hload hmon
        ((orderedFamily liveScale targetDenominator request a s harity w hs hpos hload hmon)[k + 1]'
          hk)).cuts.length :=
  (C10NativeReload.growth_iff_cuts _ _
      (familyRow_d liveScale targetDenominator request a s harity w hs hpos hload hmon _ _)
      (familyRow_p liveScale targetDenominator request a s harity w hs hpos hload hmon _ _)
      (familyRow_odd liveScale targetDenominator request a s harity w hs hpos hload hmon _ _)).mp
    (familyRow_growth liveScale targetDenominator request a s harity w hs hpos hload hmon k hk)

end FamilyRows

end NearCubicWires.RepairSource.CloseoutFinal.C10RowOrdering
