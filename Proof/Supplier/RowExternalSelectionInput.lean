import Proof.Supplier.RowExternalSelection

/-! External offsets ignore the live assignment. Thus the physical cell
selector built from zero live bits is the same selector for every summed
live row, with the larger row/smaller column orientation kept explicit. -/
namespace NearCubicWires.RepairOrdinary.RowExternalSelection
open SupplierPipeline SupplierEstimator SupplierPrime
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem split_external_eq {q : ℕ} (live : Finset (Fin q))
    (x y : BitInput live.card) (left : BitInput (normalizedExternalLeftCount live))
    (right : BitInput (normalizedExternalRightCount live)) (i : Fin q) (hi : i∉live) :
    normalizedSplitInput live x left right i=normalizedSplitInput live y left right i := by
  obtain ⟨c,rfl⟩ := (normalizedLiveExternalCoordinateEquiv live).surjective i
  cases c with
  | inl j =>
    exfalso
    apply hi
    simpa only [normalizedLiveExternalCoordinateEquiv,finSumEquivOfFinset_inl] using
      live.orderEmbOfFin_mem rfl j
  | inr j =>
    obtain ⟨c,rfl⟩ := (normalizedExternalCoordinateEquiv live).surjective j
    cases c <;> simp

theorem residual_constant_split {q : ℕ} (gate : NormalizedThresholdGate q) (live : Finset (Fin q))
    (x y : BitInput live.card) (left : BitInput (normalizedExternalLeftCount live))
    (right : BitInput (normalizedExternalRightCount live)) :
    residualConstant gate live (normalizedSplitInput live x left right)=
      residualConstant gate live (normalizedSplitInput live y left right) := by
  have hs : frozenScore gate live (normalizedSplitInput live x left right)=
      frozenScore gate live (normalizedSplitInput live y left right) := by
    unfold frozenScore
    apply Finset.sum_congr rfl
    intro i hi
    rw [split_external_eq live x y left right i (Finset.mem_sdiff.mp hi).2]
  simp only [residualConstant,hs]

theorem occurrence_constant_split {q : ℕ} (occurrences : List (SupportedNormalizedGate q))
    (liveScale : ℕ) (x y : BitInput (normalizedLiveSet occurrences liveScale).card)
    (row column : ℕ) (i : Fin occurrences.length) :
    occurrenceResidualConstant occurrences (normalizedLiveSet occurrences liveScale)
      (normalizedSplitInput (normalizedLiveSet occurrences liveScale) x
        (fun a=>column.testBit a.val) (fun a=>row.testBit a.val)) i=
    occurrenceResidualConstant occurrences (normalizedLiveSet occurrences liveScale)
      (normalizedSplitInput (normalizedLiveSet occurrences liveScale) y
        (fun a=>column.testBit a.val) (fun a=>row.testBit a.val)) i :=
  residual_constant_split (occurrences.get i).gate _ x y _ _

theorem symmetricOffset_full (r : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (liveScale row column : ℕ)
    (liveInput : BitInput (normalizedLiveSet (symmetricFourfoldOccurrences r) liveScale).card) :
    symmetricOffset r liveScale row column=RowOffsets.symmetricOffsets r liveScale
      (normalizedSplitInput (normalizedLiveSet (symmetricFourfoldOccurrences r) liveScale) liveInput
        (fun a=>column.testBit a.val) (fun a=>row.testBit a.val)) := by
  funext i
  apply Fin.ext
  simp only [symmetricOffset,RowOffsets.symmetricOffsets]
  unfold occurrenceResidualConstantCount input
  apply Finset.sum_congr rfl
  intro j _
  rw [occurrence_constant_split (symmetricFourfoldOccurrences r) liveScale (fun _=>false) liveInput row column j]

theorem thresholdOffset_full {q cutoff : ℕ} (occurrences : List (SupportedNormalizedGate q))
    (liveScale : ℕ) (equation : LabelledEquation (Fin occurrences.length))
    (prime : PrimeIndex cutoff) (row column : ℕ)
    (liveInput : BitInput (normalizedLiveSet occurrences liveScale).card) :
    thresholdOffset occurrences liveScale equation prime row column=
      RowOffsets.thresholdOffset occurrences liveScale
        (normalizedSplitInput (normalizedLiveSet occurrences liveScale) liveInput
          (fun a=>column.testBit a.val) (fun a=>row.testBit a.val)) equation prime := by
  have hs : occurrenceWeightedResidualConstant occurrences liveScale (input occurrences liveScale row column)
      Finset.univ equation.weights=occurrenceWeightedResidualConstant occurrences liveScale
        (normalizedSplitInput (normalizedLiveSet occurrences liveScale) liveInput
          (fun a=>column.testBit a.val) (fun a=>row.testBit a.val)) Finset.univ equation.weights := by
    unfold occurrenceWeightedResidualConstant input
    apply Finset.sum_congr rfl
    intro j _
    rw [occurrence_constant_split occurrences liveScale (fun _=>false) liveInput row column j]
  apply Fin.ext
  change modularResidualOffset occurrences liveScale (input occurrences liveScale row column) equation prime.val=_
  simp only [modularResidualOffset,hs,RowOffsets.thresholdOffset]

end
end NearCubicWires.RepairOrdinary.RowExternalSelection
