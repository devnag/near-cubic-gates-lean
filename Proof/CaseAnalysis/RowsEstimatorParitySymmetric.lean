import Proof.CaseAnalysis.RowsTupleSeekTyped

/-! The paper's native identity-bottom parity circuit, in increasing support order. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorParity
open Finset SupplierPipeline SourceInterfaces
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-- The canonical increasing enumeration of a finite support. -/
noncomputable def supportCoordinate {n : ℕ} (support : Finset (Fin n))
    (index : Fin support.card) : Fin n :=
  (support.orderIsoOfFin rfl index).val

theorem supportCoordinate_mem {n : ℕ} (support : Finset (Fin n))
    (index : Fin support.card) :
    supportCoordinate support index ∈ support :=
  (support.orderIsoOfFin rfl index).property

theorem supportCoordinate_injective {n : ℕ} (support : Finset (Fin n)) :
    Function.Injective (supportCoordinate support) := by
  intro left right heq
  apply (support.orderIsoOfFin rfl).injective
  exact Subtype.ext heq

theorem supportCoordinate_surjective {n : ℕ} (support : Finset (Fin n))
    (coordinate : Fin n) (hcoordinate : coordinate ∈ support) :
    ∃ index, supportCoordinate support index = coordinate := by
  let member : support := ⟨coordinate, hcoordinate⟩
  refine ⟨(support.orderIsoOfFin rfl).symm member, ?_⟩
  exact congrArg Subtype.val ((support.orderIsoOfFin rfl).apply_symm_apply member)

/-- A one-wire normalized threshold gate reading exactly one input bit. -/
def inputBitSupportedGate {n : ℕ} (coordinate : Fin n) :
    SupportedNormalizedGate n where
  gate :=
    { weight := fun index => if index = coordinate then 1 else 0
      threshold := 1 }
  support := {coordinate}
  zeroOutside := by
    intro index hindex
    simp only [Finset.mem_singleton] at hindex
    simp [hindex]

@[simp] theorem inputBitSupportedGate_eval {n : ℕ}
    (coordinate : Fin n) (input : BitInput n) :
    (inputBitSupportedGate coordinate).eval input = input coordinate := by
  unfold inputBitSupportedGate SupportedNormalizedGate.eval
    NormalizedThresholdGate.eval
  have hsum :
      (∑ index : Fin n,
          (if index = coordinate then (1 : ℤ) else 0) *
            if input index then 1 else 0) =
        if input coordinate then 1 else 0 := by
    calc
      _ = ∑ index : Fin n,
          if index = coordinate then
            (if input coordinate then (1 : ℤ) else 0)
          else 0 := by
            apply Finset.sum_congr rfl
            intro index _
            by_cases hindex : index = coordinate <;> simp [hindex]
      _ = if input coordinate then 1 else 0 := by simp
  rw [hsum]
  cases input coordinate <;> rfl

private theorem foldl_xor_eq_decide_odd_countP {Alpha : Type}
    (select : Alpha → Bool) (elements : List Alpha) (accumulator : Bool) :
    elements.foldl
        (fun parity element => xor parity (select element)) accumulator =
      xor accumulator (decide (Odd (elements.countP select))) := by
  induction elements generalizing accumulator with
  | nil => simp
  | cons head tail inductionHypothesis =>
      rw [List.foldl_cons, inductionHypothesis, List.countP_cons]
      by_cases hhead : select head = true
      · rcases Nat.mod_two_eq_zero_or_one (tail.countP select) with
          hparity | hparity
        · cases accumulator <;>
            simp [hhead, Nat.odd_add_one, Nat.odd_iff, hparity]
        · cases accumulator <;>
            simp [hhead, Nat.odd_add_one, Nat.odd_iff, hparity]
      · simp only [Bool.not_eq_true] at hhead
        simp [hhead]

theorem parityOn_eq_decide_odd_filter_card {n : ℕ}
    (support : Finset (Fin n)) (input : BitInput n) :
    parityOn support input =
      decide (Odd ((support.filter fun coordinate => input coordinate).card)) := by
  rw [parityOn, foldl_xor_eq_decide_odd_countP]
  simp only [Bool.false_xor]
  congr 2
  calc
    support.toList.countP input =
        support.toList.countP
          (fun coordinate => decide (input coordinate = true)) := by
      congr 2
      funext coordinate
      cases input coordinate <;> rfl
    _ = Multiset.countP (fun coordinate => input coordinate = true)
        support.val := by
      rw [← Finset.coe_toList]
      rfl
    _ = (support.filter fun coordinate => input coordinate).card := by
      rw [Multiset.countP_eq_card_filter]
      rfl

/-- A normalized symmetric-threshold circuit computing parity on a finite
support: one identity bottom gate per supported coordinate and an odd-count
top table. -/
noncomputable def normalizedParityCircuit {n : ℕ}
    (support : Finset (Fin n)) : NormalizedSymmetricThresholdCircuit n where
  bottomCount := support.card
  bottom := fun index => inputBitSupportedGate (supportCoordinate support index)
  top := fun accepted => decide (Odd accepted.val)

theorem normalizedParityCircuit_acceptedBottomCount {n : ℕ}
    (support : Finset (Fin n)) (input : BitInput n) :
    ((normalizedParityCircuit support).acceptedBottomCount input).val =
      (support.filter fun coordinate => input coordinate).card := by
  unfold NormalizedSymmetricThresholdCircuit.acceptedBottomCount
  dsimp only [normalizedParityCircuit]
  simp only [inputBitSupportedGate_eval]
  change
    ((univ : Finset (Fin support.card)).filter
      (fun index => input (supportCoordinate support index))).card = _
  apply Finset.card_bij
      (fun index _ => supportCoordinate support index)
  · intro index hindex
    simp only [Finset.mem_filter]
    exact ⟨supportCoordinate_mem support index,
      (Finset.mem_filter.mp hindex).2⟩
  · intro left _ right _ heq
    exact supportCoordinate_injective support heq
  · intro coordinate hcoordinate
    rcases supportCoordinate_surjective support coordinate
      (Finset.mem_filter.mp hcoordinate).1 with ⟨index, hindex⟩
    refine ⟨index, ?_, hindex⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simpa [hindex] using (Finset.mem_filter.mp hcoordinate).2

@[simp] theorem normalizedParityCircuit_eval {n : ℕ}
    (support : Finset (Fin n)) (input : BitInput n) :
    (normalizedParityCircuit support).eval input = parityOn support input := by
  unfold NormalizedSymmetricThresholdCircuit.eval
  change
    decide
        (Odd
          ((normalizedParityCircuit support).acceptedBottomCount input).val) =
      parityOn support input
  rw [normalizedParityCircuit_acceptedBottomCount]
  exact (parityOn_eq_decide_odd_filter_card support input).symm

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorParity
