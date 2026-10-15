import Proof.Wire_3_5.Shared.Carrier

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Stars
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.SupplierPipeline

namespace Carrier
variable {n : ℕ}

theorem count_residualBits (X : Carrier n) (c u v : BitInput n) :
    (X.residualBits c u v).count true = X.population c u v := by
  induction X with
  | nil => rfl
  | cons g X ih =>
    simp only [residualBits, List.flatMap_cons, List.count_append, population, List.map_cons,
      List.sum_cons] at ih ⊢
    rw [ih]
    simp only [atomResidual]
    cases residualPlus g.eval c u v <;> cases residualMinus g.eval c u v <;> simp

def atomWires (g : NormalizedThresholdGate n) : ℕ :=
  (Finset.univ.filter fun i => g.weight i ≠ 0).card + 1

def wires (X : Carrier n) : ℕ := (X.map atomWires).sum

theorem population_append (X Y : Carrier n) (c u v : BitInput n) :
    (X ++ Y).population c u v = X.population c u v + Y.population c u v := by
  simp [population, List.sum_append]

theorem wires_append (X Y : Carrier n) : (X ++ Y).wires = X.wires + Y.wires := by
  simp [wires, List.sum_append]

/-- The population of a union of named carriers is the sum of their populations. -/
theorem population_flatten (named : List (Carrier n)) (c u v : BitInput n) :
    population named.flatten c u v = (named.map fun X => population X c u v).sum := by
  induction named with
  | nil => rfl
  | cons X named ih =>
    rw [List.flatten_cons, population_append, ih, List.map_cons, List.sum_cons]

/-- A sub-multiset has at most the population (with multiplicity). -/
theorem population_le_of_subperm {X Y : Carrier n} (h : X.Subperm Y) (c u v : BitInput n) :
    X.population c u v ≤ Y.population c u v := by
  obtain ⟨l, hperm, hsub⟩ := h
  have h1 : (l.map fun g => atomResidual g c u v).sum = (X.map fun g => atomResidual g c u v).sum :=
    (hperm.map _).sum_eq
  have h2 : (l.map fun g => atomResidual g c u v).sum ≤ (Y.map fun g => atomResidual g c u v).sum :=
    (hsub.map _).sum_le_sum fun a _ => Nat.zero_le a
  unfold population; omega

/-- The integer complement of an atom: weights `−w`, threshold `1 − θ` (`¬[θ ≤ w·x] = [−w·x ≥ 1−θ]`). -/
def complAtom (g : NormalizedThresholdGate n) : NormalizedThresholdGate n :=
  ⟨fun i => -g.weight i, 1 - g.threshold⟩

/-- The constant atom `b`: zero weights, threshold `0` (true) or `1` (false). -/
def constAtom (b : Bool) : NormalizedThresholdGate n := ⟨fun _ => 0, if b then 0 else 1⟩

theorem complAtom_eval (g : NormalizedThresholdGate n) (x : BitInput n) :
    (complAtom g).eval x = !g.eval x := by
  simp only [complAtom, NormalizedThresholdGate.eval]
  have hs : (∑ i, -g.weight i * if x i then (1 : ℤ) else 0) = -∑ i, g.weight i * if x i then (1 : ℤ) else 0 := by
    rw [← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro i _; ring
  rw [hs]
  by_cases h : g.threshold ≤ ∑ i, g.weight i * if x i then (1 : ℤ) else 0
  · simp only [h, decide_true, Bool.not_true, decide_eq_false_iff_not]; omega
  · simp only [h, decide_false, Bool.not_false, decide_eq_true_eq]; omega

theorem constAtom_eval (b : Bool) (x : BitInput n) : (constAtom b : NormalizedThresholdGate n).eval x = b := by
  cases b <;> simp [constAtom, NormalizedThresholdGate.eval]

theorem mixedDifference_complAtom (g : NormalizedThresholdGate n) (c u v : BitInput n) :
    mixedDifference (complAtom g).eval c u v = -mixedDifference g.eval c u v := by
  simp only [mixedDifference, complAtom_eval, bitZ]
  cases g.eval (xorInput (xorInput c u) v) <;> cases g.eval (xorInput c u) <;>
    cases g.eval (xorInput c v) <;> cases g.eval c <;> simp

/-- A complemented atom has the same population contribution (its `Z⁺` and `Z⁻` swap). -/
theorem atomResidual_complAtom (g : NormalizedThresholdGate n) (c u v : BitInput n) :
    atomResidual (complAtom g) c u v = atomResidual g c u v := by
  simp only [atomResidual, residualPlus, residualMinus, mixedDifference_complAtom]
  have h1 : (-mixedDifference g.eval c u v = 1) ↔ (mixedDifference g.eval c u v = -1) := by omega
  have h2 : (-mixedDifference g.eval c u v = -1) ↔ (mixedDifference g.eval c u v = 1) := by omega
  simp only [h1, h2]
  omega

theorem atomResidual_constAtom (b : Bool) (c u v : BitInput n) :
    atomResidual (constAtom b : NormalizedThresholdGate n) c u v = 0 := by
  simp [atomResidual, residualPlus, residualMinus, mixedDifference, constAtom_eval, bitZ]

end Carrier

/-- Filtering a list and summing is summing the indicator-weighted terms. -/
theorem sum_map_filter_eq {α : Type} (l : List α) (p : α → Bool) (f : α → ℕ) :
    ((l.filter p).map f).sum = (l.map fun a => if p a then f a else 0).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => by_cases h : p a <;> simp [h, ih]

/-- An atom's actual support is inside its charged support (`zeroOutside`). -/
theorem atomWires_le {n : ℕ} (g : SupportedNormalizedGate n) :
    Carrier.atomWires g.gate ≤ g.wireCount + 1 := by
  unfold Carrier.atomWires SupportedNormalizedGate.wireCount
  have : (Finset.univ.filter fun i => g.gate.weight i ≠ 0) ⊆ g.support := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    by_contra h; exact hi (g.zeroOutside i h)
  have := Finset.card_le_card this
  omega

theorem wires_thrGates_eq {n : ℕ} (C : SupplierPipeline.NormalizedThresholdThresholdCircuit n) :
    (thrGates C).wires = ∑ i ∈ C.top.support, Carrier.atomWires (C.bottom i).gate := by
  unfold thrGates Carrier.wires
  rw [List.map_map, sum_map_filter_eq, ← Fin.sum_univ_def, ← Finset.sum_filter]
  congr 1
  ext i; simp

theorem wires_thrGates_le {n : ℕ} (C : SupplierPipeline.NormalizedThresholdThresholdCircuit n) :
    (thrGates C).wires ≤ C.wireCount := by
  rw [wires_thrGates_eq]
  unfold SupplierPipeline.NormalizedThresholdThresholdCircuit.wireCount
  exact Finset.sum_le_sum fun i _ => atomWires_le _

/-- The same for a `SYM∘THR` circuit. -/
theorem wires_symGates_le {n : ℕ} (C : SupplierPipeline.NormalizedSymmetricThresholdCircuit n) :
    (symGates C).wires ≤ C.wireCount := by
  unfold symGates Carrier.wires SupplierPipeline.NormalizedSymmetricThresholdCircuit.wireCount
  rw [List.map_map, ← Fin.sum_univ_def]
  exact Finset.sum_le_sum fun i _ => atomWires_le _

/-- **The duty of containment:** at every star point, each admitted circuit's residual population (with
multiplicity) is at most the sum of the named carriers' populations `Σ_X R_X`. This is what makes the named
filters on `R_X` control the circuits' own residual counts. -/
theorem GatesIn.population_le {n a : ℕ} {gates : Fin a → Carrier n} {named : List (Carrier n)}
    (h : GatesIn gates named) (i : Fin a) (c u v : BitInput n) :
    Carrier.population (gates i) c u v ≤ (named.map fun X => Carrier.population X c u v).sum := by
  rw [← Carrier.population_flatten]
  exact Carrier.population_le_of_subperm (h i) c u v

/-- The union machine's calls are admitted: a tuple whose every circuit's gates are the gates of one of the named
carriers' atoms (a sublist of that carrier) satisfies `GatesIn`. -/
theorem gatesIn_of_sublist {n a : ℕ} {gates : Fin a → Carrier n} {named : List (Carrier n)}
    (h : ∀ i, ∃ X ∈ named, (gates i).Sublist X) : GatesIn gates named := by
  intro i
  obtain ⟨X, hX, hsub⟩ := h i
  exact (hsub.trans (List.sublist_flatten_of_mem hX)).subperm

theorem sublist_flatten_of_mem {n : ℕ} {atoms : List (Carrier n)} {Y : Carrier n} (h : Y ∈ atoms) :
    Y.Sublist atoms.flatten :=
  List.sublist_flatten_of_mem h

end NearCubicWires.WireExponent3_5.Stars
