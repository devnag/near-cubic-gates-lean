import Proof.Assembly.FinalNaturalHardwireScore
import Proof.Assembly.FinalNaturalHardwireWeights

/-! Exact increasing-coordinate meaning of a membership-controlled scatter.
The compressed assignment order is the existing normalized live equivalence. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.FrozenMask
open SupplierEstimator RepairSource.CloseoutFinal RepairOrdinary

def selected (xs : List (Bool × Bool)) : List Bool :=
  xs.filterMap (fun x => if x.1 then some x.2 else none)
def values (xs : List (Bool × Bool)) : List Bool := xs.map (fun x => x.1 && x.2)
noncomputable def pairs {q : Nat} (live : Finset (Fin q)) (y : BitInput live.card) : List (Bool × Bool) :=
  List.ofFn (fun i => (decide (i ∈ live), C10NaturalHardwireScore.frozenMask live y i))

theorem selected_map {α : Type} (xs : List α) (p : α → Bool) (f : α → Bool) :
    selected (xs.map (fun x => (p x, f x))) = (xs.filter p).map f := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases hp : p x <;> simpa [selected, hp] using ih

theorem live_order {q : Nat} (live : Finset (Fin q)) :
    (List.finRange q).filter (fun i => decide (i ∈ live)) = live.sort := by
  apply ((List.sortedLT_finRange q).pairwise.filter _).sortedLT.eq_of_mem_iff live.sortedLT_sort
  intro i
  simp

theorem selected_pairs {q : Nat} (live : Finset (Fin q)) (y : BitInput live.card) :
    selected (pairs live y) = List.ofFn y := by
  rw [pairs, List.ofFn_eq_map, selected_map, live_order,
    ← Finset.listMap_orderEmbOfFin_finRange live rfl, List.map_map, ← List.ofFn_eq_map]
  apply congrArg List.ofFn
  funext i
  change C10SupplierRowInput.joinInput live y (fun _ => false)
    (normalizedLiveExternalCoordinateEquiv live (Sum.inl i)) = y i
  exact C10SupplierRowInput.joinInput_coord live y (fun _ => false) (Sum.inl i)

theorem false_outside {q : Nat} (live : Finset (Fin q)) (y : BitInput live.card)
    (i : Fin q) (hi : i ∉ live) : C10NaturalHardwireScore.frozenMask live y i = false := by
  obtain ⟨side, rfl⟩ := (normalizedLiveExternalCoordinateEquiv live).surjective i
  cases side with
  | inl j =>
    exact False.elim (hi (Finset.orderEmbOfFin_mem live rfl j))
  | inr j =>
    exact C10SupplierRowInput.joinInput_coord live y (fun _ => false) (Sum.inr j)

theorem values_pairs {q : Nat} (live : Finset (Fin q)) (y : BitInput live.card) :
    values (pairs live y) = List.ofFn (C10NaturalHardwireScore.frozenMask live y) := by
  simp only [values, pairs, List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  by_cases hi : i ∈ live
  · simp [hi]
  · simp [hi, false_outside live y i hi]

theorem membership_pairs {q : Nat} (live : Finset (Fin q)) (y : BitInput live.card) :
    (pairs live y).map Prod.fst = CloseoutRowsGateSupport.gateMembers live := by
  simp only [pairs, List.map_ofFn, CloseoutRowsGateSupport.gateMembers]
  rfl

end NearCubicWires.P1Closure.FrozenMask
