import Proof.CaseAnalysis.FinalSupplierExternalRow

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires
open NearCubicWires.LocalBitMultitape
open NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPrinter
open NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimator
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients
open NearCubicWires.RepairOrdinary.CompetitorSelectedCount
open NearCubicWires.RepairOrdinary.CompetitorCountMask (selected)
open NearCubicWires.RepairOrdinary.CompetitorCrossScheduler (producer)
open NearCubicWires.ExtDecompositionBatch (Step)
open NearCubicWires.RepairSource.CloseoutFinal
open Finset
open scoped BigOperators

namespace NearCubicWires.RepairSource.CloseoutFinal.C10ExternalRowLoop

/-! ## 1. The printer's own cell-addressing convention -/

/-- `Fin.addCases` read through `finSumFinEquiv`: the block split the printer uses. -/
theorem addCases_eq_sumElim {l r : ℕ} (f : Fin l → Bool) (g : Fin r → Bool) (m : Fin (l + r)) :
    Fin.addCases (motive := fun _ => Bool) f g m = Sum.elim f g (finSumFinEquiv.symm m) := by
  refine Fin.addCases (motive := fun m => Fin.addCases (motive := fun _ => Bool) f g m =
    Sum.elim f g (finSumFinEquiv.symm m)) (fun t => ?_) (fun t => ?_) m <;> simp

/-- The residual arity carried by the row's arity split: `s = q - K`. -/
theorem harity_card {m : ℕ} (live : Finset (Fin m)) (s : ℕ)
    (harity : (s + 1) / 2 + s / 2 = liveᶜ.card) : s = liveᶜ.card := by omega

/-- The printer's ROW half is the larger external half. -/
theorem harity_right {m : ℕ} (live : Finset (Fin m)) (s : ℕ)
    (harity : (s + 1) / 2 + s / 2 = liveᶜ.card) :
    (s + 1) / 2 = normalizedExternalRightCount live := by
  have h := harity_card live s harity
  unfold normalizedExternalRightCount normalizedExternalLeftCount
  omega

/-- The printer's COLUMN half is the smaller external half. -/
theorem harity_left {m : ℕ} (live : Finset (Fin m)) (s : ℕ)
    (harity : (s + 1) / 2 + s / 2 = liveᶜ.card) :
    s / 2 = normalizedExternalLeftCount live := by
  have h := harity_card live s harity
  unfold normalizedExternalLeftCount
  omega

section PrinterPoint

variable {n : ℕ} (live : Finset (Fin n)) (s : ℕ) (harity : (s + 1) / 2 + s / 2 = liveᶜ.card)

/-- **The printer's coordinate split of the residual cube**: the ROW half first
(`C10SupplierRowInput.halfPoint`, `Proof/CaseAnalysis/FinalSupplierRowInput.lean`), then the
COLUMN half. -/
def printerCoordinates : Fin ((s + 1) / 2) ⊕ Fin (s / 2) ≃ Fin liveᶜ.card :=
  finSumFinEquiv.trans (finCongr harity)

/-- The printer's residual-cube splitting, as a `BitInput` equivalence. -/
def printerInput : BitInput liveᶜ.card ≃ BitInput ((s + 1) / 2) × BitInput (s / 2) :=
  bitInputSumEquiv (printerCoordinates live s harity)

/-- **The residual column addressed by the printed table's cell `(rowN, colN)`** — literally the
point `C10SupplierTable.table_eq_exactColumnCount`
(`Proof/CaseAnalysis/FinalSupplierTable.lean`) reads. -/
def printerPoint (rowN colN : ℕ) : BitInput liveᶜ.card :=
  C10SupplierRowInput.residualPoint live s harity
    (C10SupplierRowInput.halfPoint ((s + 1) / 2) (s / 2) rowN colN)

/-- The cell address, decoded: `printerPoint` is `printerInput`'s inverse at the two binary
addresses of the cell. -/
theorem printerPoint_eq (i : Fin (2 ^ ((s + 1) / 2))) (j : Fin (2 ^ (s / 2))) :
    printerPoint live s harity i.val j.val =
      (printerInput live s harity).symm
        (bitInputIndexEquiv ((s + 1) / 2) i, bitInputIndexEquiv (s / 2) j) := by
  funext k
  show C10SupplierRowInput.halfPoint ((s + 1) / 2) (s / 2) i.val j.val (Fin.cast harity.symm k) =
    Sum.elim (fun t : Fin ((s + 1) / 2) => i.val.testBit t.val)
      (fun t : Fin (s / 2) => j.val.testBit t.val)
      (finSumFinEquiv.symm (Fin.cast harity.symm k))
  exact addCases_eq_sumElim (fun t : Fin ((s + 1) / 2) => i.val.testBit t.val)
    (fun t : Fin (s / 2) => j.val.testBit t.val) (Fin.cast harity.symm k)

/-- **The printed grid enumerates the residual cube exactly once.**  Scanning the
`2 ^ ((s+1)/2)` printed rows against the `2 ^ (s/2)` printed columns visits every residual column
\(z\) once — the printer-convention counterpart of `C10SupplierSelect.sum_residualPoint`
(`Proof/CaseAnalysis/FinalSupplierSelect.lean`). -/
theorem sum_printerPoint (R L : ℕ) (hR : R = (s + 1) / 2) (hL : L = s / 2)
    (g : BitInput liveᶜ.card → ℕ) :
    (∑ i : Fin (2 ^ R), ∑ j : Fin (2 ^ L),
        g (printerPoint live s harity i.val j.val)) = ∑ z, g z := by
  subst hR
  subst hL
  have hinner : ∀ i : Fin (2 ^ ((s + 1) / 2)),
      (∑ j : Fin (2 ^ (s / 2)), g (printerPoint live s harity i.val j.val)) =
        ∑ b : BitInput (s / 2),
          g ((printerInput live s harity).symm (bitInputIndexEquiv ((s + 1) / 2) i, b)) := by
    intro i
    rw [Finset.sum_congr rfl (fun j _ => congrArg g (printerPoint_eq live s harity i j))]
    exact Equiv.sum_comp (bitInputIndexEquiv (s / 2))
      (fun b => g ((printerInput live s harity).symm (bitInputIndexEquiv ((s + 1) / 2) i, b)))
  rw [Finset.sum_congr rfl (fun i _ => hinner i),
    Equiv.sum_comp (bitInputIndexEquiv ((s + 1) / 2))
      (fun a => ∑ b : BitInput (s / 2), g ((printerInput live s harity).symm (a, b)))]
  have hprod := Equiv.sum_comp (printerInput live s harity).symm g
  rw [Fintype.sum_prod_type] at hprod
  exact hprod

end PrinterPoint

/-! ## 2. The column scan in the printer's convention, and A.13.9's per-offset sum -/

section Selector

variable (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) (liveScale s : ℕ)
  (harity : (s + 1) / 2 + s / 2 =
    (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)ᶜ.card)

/-- **A.3 :1978-1979 in the printer's coordinates**: the physical cell `(i,j)` is selected exactly
when the residual column the PRINTED TABLE put there has offset tuple \(\mathbf f\). -/
noncomputable def printerSelect (f : Fin request.circuits.length → ℕ) {u : ℕ} :
    Fin u → Fin u → Bool :=
  fun i j => decide (C10SupplierSelect.offsetOf request liveScale
    (printerPoint (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale) s harity
      i.val j.val) = f)

theorem selected_sum_printer (f : Fin request.circuits.length → ℕ)
    (monomials : StructuralGF2Polynomial) (u : ℕ) (odd : Bool)
    (hu : u = 2 ^ ((s + 1) / 2)) (hodd : odd = decide (s % 2 = 1))
    (table : Fin u → Fin u → ℕ)
    (htable : ∀ i j : Fin u, table i j =
      exactColumnCount (C10PrinterBridge.residualHolds request liveScale) monomials
        (printerPoint (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale) s
          harity i.val j.val)) :
    ((selected (CompetitorSelectedCells.cells odd table
        (printerSelect request liveScale s harity f))).sum : ℕ) =
      ∑ z : BitInput
          (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)ᶜ.card,
        if C10SupplierSelect.offsetOf request liveScale z = f then
          exactColumnCount (C10PrinterBridge.residualHolds request liveScale) monomials z
        else 0 := by
  have hR := harity_right (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)
    s harity
  have hL := harity_left (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)
    s harity
  have hcard := harity_card (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)
    s harity
  have hfun : (fun i j : Fin u =>
      if printerSelect request liveScale s harity f i j = true then table i j else 0) =
      fun i j : Fin u =>
        (fun a b : ℕ =>
          if C10SupplierSelect.offsetOf request liveScale
              (printerPoint (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)
                s harity a b) = f then
            exactColumnCount (C10PrinterBridge.residualHolds request liveScale) monomials
              (printerPoint (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)
                s harity a b)
          else 0) i.val j.val := by
    funext i j
    rw [htable i j]
    simp only [printerSelect, decide_eq_true_eq]
  rw [RowExternalSelection.cells_selected_sum, hfun,
    C10SupplierSelect.total_eq_sum_half
      (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)
      (fun a b : ℕ =>
        if C10SupplierSelect.offsetOf request liveScale
            (printerPoint (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)
              s harity a b) = f then
          exactColumnCount (C10PrinterBridge.residualHolds request liveScale) monomials
            (printerPoint (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)
              s harity a b)
        else 0) u odd (by rw [hu, hR]) (by rw [hodd, hcard])]
  exact sum_printerPoint (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale) s
    harity _ _ hR.symm hL.symm
    (fun z => if C10SupplierSelect.offsetOf request liveScale z = f then
      exactColumnCount (C10PrinterBridge.residualHolds request liveScale) monomials z else 0)

end Selector

/-! ## 3. The external-row family, and the count its record words total -/

/-- A.13.9's list denominator for this request. -/
def familyDenominator (targetDenominator : ℕ → ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) : ℕ :=
  symmetricListDenominator request (targetDenominator request.q)

/-- **One printed external row** (A.3 :1976-1978): seed `sample`, offset tuple `f`. -/
noncomputable def familyPolynomial (liveScale : ℕ) (targetDenominator : ℕ → ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (sample : NormalizedOccurrenceListSeed (symmetricFourfoldOccurrences request) liveScale
      (familyDenominator targetDenominator request))
    (f : Fin request.circuits.length → ℕ) : StructuralGF2Polynomial :=
  structuralCanonicalSymmetricFourfoldRow request liveScale
    (familyDenominator targetDenominator request) sample f

/-- **The payload of one external row's record word** — A.13.9's
\(\sum_{z:\mathbf F(z)=\mathbf f}T_{e,\mathbf f}(z)\). -/
noncomputable def pairValue (liveScale : ℕ) (targetDenominator : ℕ → ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (sample : NormalizedOccurrenceListSeed (symmetricFourfoldOccurrences request) liveScale
      (familyDenominator targetDenominator request))
    (f : Fin request.circuits.length → ℕ) : ℕ :=
  ∑ z : BitInput (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)ᶜ.card,
    if C10SupplierSelect.offsetOf request liveScale z = f then
      exactColumnCount (C10PrinterBridge.residualHolds request liveScale)
        (familyPolynomial liveScale targetDenominator request sample f) z
    else 0

/-- The `|\mathcal E|` seeds of A.13.9, enumerated. -/
noncomputable def seedList (liveScale : ℕ) (targetDenominator : ℕ → ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) :
    List (NormalizedOccurrenceListSeed (symmetricFourfoldOccurrences request) liveScale
      (familyDenominator targetDenominator request)) :=
  (Finset.univ : Finset (NormalizedOccurrenceListSeed (symmetricFourfoldOccurrences request)
    liveScale (familyDenominator targetDenominator request))).toList

/-- The offset tuples of A.3 :1976, enumerated. -/
noncomputable def offsetList (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) :
    List (Fin request.circuits.length → ℕ) :=
  (C10SupplierSelect.offsetRange request).toList

/-- **The rounds of the loop**: the seeds crossed with the offset range. -/
noncomputable def pairList (liveScale : ℕ) (targetDenominator : ℕ → ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) :
    List ((NormalizedOccurrenceListSeed (symmetricFourfoldOccurrences request) liveScale
      (familyDenominator targetDenominator request)) ×
      (Fin request.circuits.length → ℕ)) :=
  (seedList liveScale targetDenominator request).flatMap
    (fun e => (offsetList request).map (fun f => (e, f)))

theorem length_flatMap_const {A B : Type} (l : List A) (h : A → List B) (m : ℕ)
    (hm : ∀ a, (h a).length = m) : (l.flatMap h).length = l.length * m := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.flatMap_cons, List.length_append, ih, hm x, List.length_cons]
    ring

theorem sum_map_flatMap {A B : Type} (l : List A) (h : A → List B) (g : B → ℕ) :
    ((l.flatMap h).map g).sum = (l.map (fun a => ((h a).map g).sum)).sum := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    rw [List.flatMap_cons, List.map_append, List.sum_append, ih, List.map_cons, List.sum_cons]

theorem offsetList_length (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) :
    (offsetList request).length = (C10SupplierSelect.offsetRange request).card := by
  unfold offsetList
  exact Finset.length_toList _

theorem seedList_length (liveScale : ℕ) (targetDenominator : ℕ → ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) :
    (seedList liveScale targetDenominator request).length =
      Fintype.card (NormalizedOccurrenceListSeed (symmetricFourfoldOccurrences request) liveScale
        (familyDenominator targetDenominator request)) := by
  unfold seedList
  rw [Finset.length_toList, Finset.card_univ]

/-- **`|\mathcal E|` times the offset range** rounds: `2 ^ seedExponent` seeds
(`C10SupplierWidth.rowCount_eq_two_pow`, `Proof/CaseAnalysis/FinalSupplierWidth.lean`) crossed
with A.3 :1976's offsets. -/
theorem pairList_length (spectrum : SourceInterfaces.ExpanderSpectrumContract) (liveScale : ℕ)
    (targetDenominator : ℕ → ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) :
    (pairList liveScale targetDenominator request).length =
      2 ^ C10SupplierWidth.seedExponent request liveScale (targetDenominator request.q) *
        (C10SupplierSelect.offsetRange request).card := by
  unfold pairList
  rw [length_flatMap_const _ _ ((C10SupplierSelect.offsetRange request).card)
      (fun _ => by rw [List.length_map]; exact offsetList_length request),
    seedList_length]
  exact congrArg (fun x => x * (C10SupplierSelect.offsetRange request).card)
    (C10SupplierWidth.rowCount_eq_two_pow spectrum liveScale targetDenominator request)

/-- **THE COUNT.**  The record-word payloads of the whole external-row family total exactly
`FiniteRowAggregation.acceptanceCount` of the symmetric supplier's rows — A.13.9 :3155-3164's
\(\sum_e\sum_zT_{e,\mathbf F(z)}(z)\). -/
theorem familyTotal_eq_acceptanceCount (spectrum : SourceInterfaces.ExpanderSpectrumContract)
    (liveScale : ℕ) (targetDenominator : ℕ → ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) :
    (((pairList liveScale targetDenominator request).map
        (fun p => pairValue liveScale targetDenominator request p.1 p.2)).sum) =
      ((symmetricFourfoldRows spectrum liveScale targetDenominator).aggregation
        request).acceptanceCount := by
  unfold pairList
  rw [sum_map_flatMap]
  have hrow : ∀ e : NormalizedOccurrenceListSeed (symmetricFourfoldOccurrences request) liveScale
        (familyDenominator targetDenominator request),
      (((offsetList request).map (fun f => (e, f))).map
          (fun p => pairValue liveScale targetDenominator request p.1 p.2)).sum =
        ∑ z : BitInput
            (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)ᶜ.card,
          exactColumnCount (C10PrinterBridge.residualHolds request liveScale)
            (familyPolynomial liveScale targetDenominator request e
              (C10SupplierSelect.offsetOf request liveScale z)) z := by
    intro e
    rw [List.map_map]
    have hlist : ((offsetList request).map
        ((fun p => pairValue liveScale targetDenominator request p.1 p.2) ∘
          fun f => (e, f))).sum =
        ∑ f ∈ C10SupplierSelect.offsetRange request,
          pairValue liveScale targetDenominator request e f :=
      Finset.sum_map_toList (C10SupplierSelect.offsetRange request)
        (fun f => pairValue liveScale targetDenominator request e f)
    rw [hlist]
    exact C10SupplierSelect.offsets_partition request liveScale
      (fun f z => exactColumnCount (C10PrinterBridge.residualHolds request liveScale)
        (familyPolynomial liveScale targetDenominator request e f) z)
  rw [List.map_congr_left (fun e _ => hrow e)]
  unfold seedList
  rw [Finset.sum_map_toList (Finset.univ : Finset
      (NormalizedOccurrenceListSeed (symmetricFourfoldOccurrences request) liveScale
        (familyDenominator targetDenominator request)))
      (fun e => ∑ z : BitInput
          (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)ᶜ.card,
        exactColumnCount (C10PrinterBridge.residualHolds request liveScale)
          (familyPolynomial liveScale targetDenominator request e
            (C10SupplierSelect.offsetOf request liveScale z)) z)]
  exact (C10PrinterBridge.acceptanceCount_eq_sum_exactColumnCount spectrum liveScale
    targetDenominator request).symm

/-! ## 4. One round: the external row, and the record word it prints -/

section Round

variable (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
  (liveScale : ℕ) (targetDenominator : ℕ → ℕ) (a : DecompositionAlgorithm) (s : ℕ)
  (harity : (s + 1) / 2 + s / 2 =
    (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)ᶜ.card)
  (w : ℕ) (hs : 67 ≤ s) (hpos : 1 ≤ w)
  (hload : 200 * ((normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale).card +
    w * ((normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale).card + 2)) ≤ s)

theorem row_step
    (sample : NormalizedOccurrenceListSeed (symmetricFourfoldOccurrences request) liveScale
      (familyDenominator targetDenominator request))
    (f : Fin request.circuits.length → ℕ)
    (hmon : (CloseoutRowsUniversal.lower a
      (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)
      (symmetricFourfoldOccurrences request)
      (familyPolynomial liveScale targetDenominator request sample f)).length < 2 ^ w)
    (sources : EightSources) (C : ℕ)
    (hcap : ExtIncidence.NativeOutputBound.allowance
        (ExtIncidence.NativeMeasured.capacity
          (C10SupplierRowInput.pool a
            (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)
            (symmetricFourfoldOccurrences request) s harity)
          ((normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale).card + 1) w)
        ((normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale).card + 1)
        (2 ^ (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale).card) ≤ C)
    (est : CompetitorValidity.Estimate) (arity scale : ℕ) :
    ∃ actual,
      runFrom (Whole.machine (williamsOf sources))
          (Whole.budget (williamsOf sources)
            (C10SupplierRowInput.rowInput a
              (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)
              (symmetricFourfoldOccurrences request) s harity
              (familyPolynomial liveScale targetDenominator request sample f) w hs hmon hpos hload)
            C ((normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale).card + 1))
          (Whole.entry (williamsOf sources)
            (C10SupplierRowInput.rowInput a
              (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)
              (symmetricFourfoldOccurrences request) s harity
              (familyPolynomial liveScale targetDenominator request sample f) w hs hmon hpos hload)
            C ((normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale).card + 1) est
            (C10SupplierWidth.denominator arity scale)
            (printerSelect request liveScale s harity f)) = some actual ∧
      Whole.budget (williamsOf sources)
          (C10SupplierRowInput.rowInput a
            (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)
            (symmetricFourfoldOccurrences request) s harity
            (familyPolynomial liveScale targetDenominator request sample f) w hs hmon hpos hload)
          C ((normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale).card + 1)
          + actual.steps ≤
        C10SupplierExternalRow.rowEnvelope (williamsOf sources)
          (C10SupplierRowInput.rowInput a
            (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)
            (symmetricFourfoldOccurrences request) s harity
            (familyPolynomial liveScale targetDenominator request sample f) w hs hmon hpos hload)
          C ((normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale).card + 1) ∧
      actual.final.tapes (Whole.recordSlot (producer (williamsOf sources))) =
        Stream.recordWord
          (scalarWidth (EquationRow.request
            (C10SupplierRowInput.rowInput a
              (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)
              (symmetricFourfoldOccurrences request) s harity
              (familyPolynomial liveScale targetDenominator request sample f) w hs hmon hpos hload))
            ((normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale).card + 1)) est
          (pairValue liveScale targetDenominator request sample f)
          (C10SupplierWidth.denominator arity scale) := by
  obtain ⟨actual, hrun, hsteps, hrec, _, _, _, _⟩ :=
    C10SupplierExternalRow.externalRow_run a
      (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)
      (symmetricFourfoldOccurrences request) s harity
      (familyPolynomial liveScale targetDenominator request sample f) w hs hmon hpos hload
      sources C hcap est arity scale (printerSelect request liveScale s harity f)
  have hsum := selected_sum_printer request liveScale s harity f
    (familyPolynomial liveScale targetDenominator request sample f)
    (EquationRow.request (C10SupplierRowInput.rowInput a
      (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)
      (symmetricFourfoldOccurrences request) s harity
      (familyPolynomial liveScale targetDenominator request sample f) w hs hmon hpos hload)).U
    (C10SupplierRowInput.rowInput a
      (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)
      (symmetricFourfoldOccurrences request) s harity
      (familyPolynomial liveScale targetDenominator request sample f) w hs hmon hpos hload).odd
    rfl rfl
    (C10SupplierTable.table a
      (normalizedLiveSet (symmetricFourfoldOccurrences request) liveScale)
      (symmetricFourfoldOccurrences request) s harity
      (familyPolynomial liveScale targetDenominator request sample f) w hs hmon hpos hload)
    (fun i j => C10SupplierTable.table_eq_exactColumnCount_residualHolds request liveScale a s
      harity (familyPolynomial liveScale targetDenominator request sample f) w hs hmon hpos
      hload i j)
  exact ⟨actual, hrun, hsteps, by rw [hrec, hsum]; rfl⟩

end Round

/-! ## 5. The family loop: one machine, one accumulated stream, one count -/

noncomputable def familyWriter {tp st : ℕ} (body : Machine tp st) :=
  CloseoutRowsDegreeLoop.machine body

/-- **The whole family's fuel** — one external row per round at `rowCost`, plus the driver's three
paid steps per round and its final rewind. -/
def familyFuel (pairCount rowCost : ℕ) : ℕ := pairCount * (rowCost + 3) + 3

/-- The record word of one round. -/
noncomputable def pairWord (liveScale : ℕ) (targetDenominator : ℕ → ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (b : ℕ) (est : CompetitorValidity.Estimate) (denominator : ℕ)
    (sample : NormalizedOccurrenceListSeed (symmetricFourfoldOccurrences request) liveScale
      (familyDenominator targetDenominator request))
    (f : Fin request.circuits.length → ℕ) : List Bool :=
  Stream.recordWord b est (pairValue liveScale targetDenominator request sample f) denominator

/-- The family's record words, in scan order. -/
noncomputable def wordList (liveScale : ℕ) (targetDenominator : ℕ → ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (b : ℕ) (est : CompetitorValidity.Estimate) (denominator : ℕ) : List (List Bool) :=
  (pairList liveScale targetDenominator request).map
    (fun p => pairWord liveScale targetDenominator request b est denominator p.1 p.2)

/-- **The accumulated stream**: the record words of the whole external-row family. -/
noncomputable def familyStream (liveScale : ℕ) (targetDenominator : ℕ → ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (b : ℕ) (est : CompetitorValidity.Estimate) (denominator : ℕ) : List Bool :=
  (wordList liveScale targetDenominator request b est denominator).flatten

theorem flatten_getD {B : Type} (xs : List (List B)) :
    (List.range xs.length).flatMap (fun j => xs.getD j []) = xs.flatten := by
  have he : (List.range xs.length).map (fun j => xs.getD j []) = xs := by
    apply List.ext_getElem
    · simp
    · intro i _ hi
      simp only [List.getElem_map, List.getElem_range]
      exact List.getD_eq_getElem xs [] hi
  rw [List.flatMap_def, he]

/-- The accumulated stream is the family's record words, one per printed external row. -/
theorem familyStream_eq (liveScale : ℕ) (targetDenominator : ℕ → ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (b : ℕ) (est : CompetitorValidity.Estimate) (denominator : ℕ) :
    familyStream liveScale targetDenominator request b est denominator =
      (pairList liveScale targetDenominator request).flatMap
        (fun p => pairWord liveScale targetDenominator request b est denominator p.1 p.2) := by
  unfold familyStream wordList
  rw [List.flatMap_def]

theorem wordList_length (spectrum : SourceInterfaces.ExpanderSpectrumContract) (liveScale : ℕ)
    (targetDenominator : ℕ → ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (b : ℕ) (est : CompetitorValidity.Estimate) (denominator : ℕ) :
    (wordList liveScale targetDenominator request b est denominator).length =
      2 ^ C10SupplierWidth.seedExponent request liveScale (targetDenominator request.q) *
        (C10SupplierSelect.offsetRange request).card := by
  unfold wordList
  rw [List.length_map]
  exact pairList_length spectrum liveScale targetDenominator request

/-- **A.8 :2253-2259, the family line of the ledger.**  The whole loop stays inside
`|\mathcal E|` times a polynomial in `q` times the per-row cost. -/
theorem familyFuel_le (liveScale : ℕ) (targetDenominator : ℕ → ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) (rowCost degree : ℕ)
    (hfour : request.circuits.length ≤ 4)
    (hcap : ∀ c ∈ request.circuits, c.wireCount ≤ (request.q + 1) ^ degree) :
    familyFuel (2 ^ C10SupplierWidth.seedExponent request liveScale (targetDenominator request.q) *
        (C10SupplierSelect.offsetRange request).card) rowCost ≤
      2 ^ C10SupplierWidth.seedExponent request liveScale (targetDenominator request.q) *
        (16 * (request.q + 1) ^ (4 * degree)) * (rowCost + 3) + 3 :=
  Nat.add_le_add_right
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _
      (C10SupplierSelect.offsetRange_card_le request degree hfour hcap))) 3

theorem family_run (spectrum : SourceInterfaces.ExpanderSpectrumContract) (liveScale : ℕ)
    (targetDenominator : ℕ → ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    {tp st : ℕ} (body : Machine tp st)
    (source : ℕ → List Bool → Configuration tp st) (slot : Fin tp) (rowCost : ℕ)
    (b : ℕ) (est : CompetitorValidity.Estimate) (denominator : ℕ) (out : List Bool)
    (hslot : ∀ k pre, (source k pre).tapes slot = pre)
    (hstart : ∀ k < (wordList liveScale targetDenominator request b est denominator).length,
      ∀ pre, (source k pre).control = body.start)
    (hrow : ∀ k < (wordList liveScale targetDenominator request b est denominator).length,
      ∀ pre, ∃ rc : ExecutionReceipt tp st,
        runFrom body rowCost (source k pre) = some rc ∧
        rc.final.heads = (source (k + 1) (pre ++
          (wordList liveScale targetDenominator request b est denominator).getD k [])).heads ∧
        rc.final.tapes = (source (k + 1) (pre ++
          (wordList liveScale targetDenominator request b est denominator).getD k [])).tapes ∧
        rc.steps ≤ rowCost) :
    ∃ T, Step (familyWriter body)
        (familyFuel (wordList liveScale targetDenominator request b est denominator).length rowCost)
        (RepairSource.VerifierDecoding.RepeatMachine.cfg 0 (source 0 out)
          (wordList liveScale targetDenominator request b est denominator).length 1).heads
        (RepairSource.VerifierDecoding.RepeatMachine.cfg 0 (source 0 out)
          (wordList liveScale targetDenominator request b est denominator).length 1).tapes
        (RepairSource.VerifierDecoding.RepeatMachine.cfg 3
          (source (wordList liveScale targetDenominator request b est denominator).length
            (out ++ familyStream liveScale targetDenominator request b est denominator))
          (wordList liveScale targetDenominator request b est denominator).length 1).heads T ∧
      T (slot.castAdd 1) =
        out ++ familyStream liveScale targetDenominator request b est denominator ∧
      (((pairList liveScale targetDenominator request).map
          (fun p => pairValue liveScale targetDenominator request p.1 p.2)).sum) =
        ((symmetricFourfoldRows spectrum liveScale targetDenominator).aggregation
          request).acceptanceCount := by
  obtain ⟨r, hr, hf, hst⟩ := CloseoutRowsDegreeLoop.loop_run body source
    (fun k => (wordList liveScale targetDenominator request b est denominator).getD k []) rowCost
    (wordList liveScale targetDenominator request b est denominator).length hstart hrow out
  rw [flatten_getD (wordList liveScale targetDenominator request b est denominator)] at hf
  refine ⟨_, ⟨r, hr, congrArg Configuration.heads hf, congrArg Configuration.tapes hf, hst⟩, ?_,
    familyTotal_eq_acceptanceCount spectrum liveScale targetDenominator request⟩
  rw [C10SupplierSelect.cfg_tapes_castAdd]
  exact hslot _ _

end NearCubicWires.RepairSource.CloseoutFinal.C10ExternalRowLoop
