import SourceAdapters.Routing.CoordinateMachineAlgebra
import SourceAdapters.Routing.CoordinateMachineUpdate

/-!
# Field meanings of the numeric compact-array updates

The construction in `lem:generator`: the numeric update routines compute the existing
compact coefficient recurrences. This module proves pointwise meanings
and exact list equalities; the instruction counts and reducedness bounds
remain in the numeric routines.

-/

set_option autoImplicit false
noncomputable section

namespace NearCubicGates.Adapters.Routing.CoordinateMachineAlgebra

open Coordinates CoordinateMachine
open NearCubicGates.Adapters.ShortPCP.Machines.FL
open NearCubicWires.WireExponent3_5

/-- Zero-default reads commute with the word representation. -/
theorem rep_getD (p : ℕ) (xs : List ℕ) (i : ℕ) :
    GF.rep p (xs.getD i 0) = (xs.map (GF.rep p)).getD i 0 := by
  have hm := List.getD_map xs 0 (GF.rep p) (n := i)
  rw [GF.rep_zero] at hm
  exact hm.symm

variable (p f : ℕ) [Fact (Irreducible (GF.toPoly p))]
variable (hp : GF.ModulusOk p f) (e : ℕ → AdjoinRoot (GF.toPoly p))

include hp

/-- The numeric row expression represents every coefficient of the next row. -/
theorem rowValue_rep (n a inv v : ℕ) (L R : List ℕ)
    (hL : L.map (GF.rep p) = List.ofFn (annihilatorCoefficients e n))
    (hR : R.map (GF.rep p) = List.ofFn (coordinateCoefficients e n a))
    (hi : GF.rep p inv = (linearizedValue (annihilatorCoefficients e n) (e n))⁻¹)
    (hv : GF.rep p v = linearizedValue (coordinateCoefficients e n a) (e n)) (j : ℕ) :
    GF.rep p (rowValue p f a n inv v L R j) =
      (List.ofFn (coordinateCoefficients e (n + 1) a)).getD j 0 := by
  rw [coordinate_step_getD]
  unfold rowValue
  split_ifs
  · rw [rep_mulW p f _ _ hp, hi, rep_getD, hL]
  · rw [GF.rep_xor, rep_mulW p f _ _ hp, rep_mulW p f _ _ hp,
      rep_getD, rep_getD, hR, hL, hi, hv]

/-- The numeric annihilator expression represents every coefficient of the next annihilator. -/
theorem annValue_rep (n pivot : ℕ) (L : List ℕ)
    (hL : L.map (GF.rep p) = List.ofFn (annihilatorCoefficients e n))
    (hpivot : GF.rep p pivot = linearizedValue (annihilatorCoefficients e n) (e n)) (j : ℕ) :
    GF.rep p (annValue p f pivot L j) =
      (List.ofFn (annihilatorCoefficients e (n + 1))).getD j 0 := by
  rw [annihilator_step_getD]
  unfold annValue
  rw [GF.rep_xor, rep_mulW p f _ _ hp, hpivot, rep_getD, hL]
  split_ifs
  · rw [GF.rep_zero]
  · rw [rep_mulW p f _ _ hp, rep_getD, hL, pow_two]

/-- The exact generated list, including its length, is the next coefficient row. -/
theorem row_values (n a inv v : ℕ) (L R : List ℕ)
    (hL : L.map (GF.rep p) = List.ofFn (annihilatorCoefficients e n))
    (hR : R.map (GF.rep p) = List.ofFn (coordinateCoefficients e n a))
    (hi : GF.rep p inv = (linearizedValue (annihilatorCoefficients e n) (e n))⁻¹)
    (hv : GF.rep p v = linearizedValue (coordinateCoefficients e n a) (e n)) :
    ((List.range (n + 1)).map (rowValue p f a n inv v L R)).map (GF.rep p) =
      List.ofFn (coordinateCoefficients e (n + 1) a) := by
  apply List.ext_getElem
  · simp
  · intro j _ hj
    have hjn : j < n + 1 := by simpa using hj
    have he := rowValue_rep p f hp e n a inv v L R hL hR hi hv j
    rw [getD_ofFn, dif_pos hjn] at he
    simpa only [List.getElem_map, List.getElem_range, List.getElem_ofFn] using he

/-- The exact generated list, including its length, is the next annihilator array. -/
theorem ann_values (n pivot : ℕ) (L : List ℕ)
    (hL : L.map (GF.rep p) = List.ofFn (annihilatorCoefficients e n))
    (hpivot : GF.rep p pivot = linearizedValue (annihilatorCoefficients e n) (e n)) :
    ((List.range (n + 2)).map (annValue p f pivot L)).map (GF.rep p) =
      List.ofFn (annihilatorCoefficients e (n + 1)) := by
  apply List.ext_getElem
  · simp
  · intro j _ hj
    have hjn : j < n + 1 + 1 := by simpa using hj
    have he := annValue_rep p f hp e n pivot L hL hpivot j
    rw [getD_ofFn, dif_pos hjn] at he
    simpa only [List.getElem_map, List.getElem_range, List.getElem_ofFn] using he

end NearCubicGates.Adapters.Routing.CoordinateMachineAlgebra
