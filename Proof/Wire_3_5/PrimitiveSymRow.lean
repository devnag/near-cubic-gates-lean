import Proof.Wire_3_5.StarMixedScore
import Proof.Wire_3_5.StarCarrier

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Stars

variable {n : ℕ}

/-! ## Gate lists at unit weight -/

def unitGates (l : Carrier n) : List (ℤ × NormalizedThresholdGate n) := l.map fun g => (1, g)

/-- The residual vector `(Z_i^+)_i` of a gate list at the star point `(c,u,v)`. -/
def plusBits (l : Carrier n) (c u v : BitInput n) : List Bool := l.map fun g => residualPlus g.eval c u v

/-- The residual vector `(Z_i^−)_i`. -/
def minusBits (l : Carrier n) (c u v : BitInput n) : List Bool := l.map fun g => residualMinus g.eval c u v

theorem sum_bitZ_eq_count (l : List Bool) : ((l.map bitZ).sum : ℤ) = (l.count true : ℤ) := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    simp only [List.map_cons, List.sum_cons, ih, List.count_cons]
    cases b
    · simp [bitZ]
    · simp [bitZ]; ring

theorem residualTerm_unit (l : Carrier n) (c u v : BitInput n) :
    residualTerm (unitGates l) c u v = ((plusBits l c u v).count true : ℤ) - (minusBits l c u v).count true := by
  unfold residualTerm unitGates plusBits minusBits
  rw [← sum_bitZ_eq_count, ← sum_bitZ_eq_count]
  induction l with
  | nil => simp
  | cons g l ih =>
    simp only [List.map_cons, List.sum_cons, one_mul, Int.cast_id] at ih ⊢
    rw [ih]; ring

/-- The unit-weight top score counts the accepting gates. -/
theorem topScore_unit (l : Carrier n) (c u v : BitInput n) :
    topScore (unitGates l) c u v = ((l.map fun g => bitZ (g.eval (xorInput (xorInput c u) v))).sum : ℤ) := by
  unfold topScore unitGates
  simp only [List.map_map, Function.comp_def, one_mul, Int.cast_id]

/-- **The unit-weight identity** (row:identity at coefficient one, `a_0 = 0`): the number of accepting gates at
`c+u+v` is `A_c(u) + B_c(v) + s^+ − s^−`. -/
theorem count_identity (l : Carrier n) (c u v : BitInput n) (hdisj : ∀ i, ¬(u i = true ∧ v i = true)) :
    ((l.map fun g => bitZ (g.eval (xorInput (xorInput c u) v))).sum : ℤ) =
      rowLeft 0 (unitGates l) c u + rowRight (unitGates l) c v +
        (((plusBits l c u v).count true : ℤ) - (minusBits l c u v).count true) := by
  rw [← topScore_unit, ← residualTerm_unit]
  have h := row_identity (0 : ℤ) (unitGates l) c u v hdisj
  rw [zero_add] at h
  exact h

/-- `A_c(u) ∈ [−|l|, |l|]` at unit weights. -/
theorem rowLeft_unit_range (l : Carrier n) (c u : BitInput n) :
    -(l.length : ℤ) ≤ rowLeft 0 (unitGates l) c u ∧ rowLeft 0 (unitGates l) c u ≤ l.length := by
  unfold rowLeft unitGates
  rw [zero_add]
  induction l with
  | nil => simp
  | cons g l ih =>
    simp only [List.map_map, Function.comp_def, one_mul, List.map_cons, List.sum_cons, List.length_cons,
      Int.cast_id] at ih ⊢
    have h1 : bitZ (g.eval (xorInput c u)) = 0 ∨ bitZ (g.eval (xorInput c u)) = 1 := by
      cases g.eval (xorInput c u) <;> simp [bitZ]
    have h2 : bitZ (g.eval c) = 0 ∨ bitZ (g.eval c) = 1 := by cases g.eval c <;> simp [bitZ]
    push_cast
    constructor <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rw [h1, h2] <;> linarith [ih.1, ih.2]

/-- `B_c(v) ∈ [0, |l|]` at unit weights. -/
theorem rowRight_unit_range (l : Carrier n) (c v : BitInput n) :
    0 ≤ rowRight (unitGates l) c v ∧ rowRight (unitGates l) c v ≤ l.length := by
  unfold rowRight unitGates
  induction l with
  | nil => simp
  | cons g l ih =>
    simp only [List.map_map, Function.comp_def, one_mul, List.map_cons, List.sum_cons, List.length_cons,
      Int.cast_id] at ih ⊢
    have h1 : bitZ (g.eval (xorInput c v)) = 0 ∨ bitZ (g.eval (xorInput c v)) = 1 := by
      cases g.eval (xorInput c v) <;> simp [bitZ]
    push_cast
    constructor <;> rcases h1 with h1 | h1 <;> rw [h1] <;> linarith [ih.1, ih.2]

theorem count_plus_add_minus (l : Carrier n) (c u v : BitInput n) :
    (plusBits l c u v).count true + (minusBits l c u v).count true = Carrier.population l c u v := by
  unfold plusBits minusBits Carrier.population
  induction l with
  | nil => rfl
  | cons g l ih =>
    simp only [List.map_cons, List.sum_cons, List.count_cons, Carrier.atomResidual] at ih ⊢
    rw [← ih]
    cases residualPlus g.eval c u v <;> cases residualMinus g.eval c u v <;> simp <;> omega

theorem length_plusBits (l : Carrier n) (c u v : BitInput n) : (plusBits l c u v).length = l.length := by
  simp [plusBits]

theorem length_minusBits (l : Carrier n) (c u v : BitInput n) : (minusBits l c u v).length = l.length := by
  simp [minusBits]

/-! ## A symmetric-top circuit -/

section Sym
variable (C : NormalizedSymmetricThresholdCircuit n)

def symLeftScore (c u : BitInput n) : ℤ := rowLeft 0 (unitGates (symGates C)) c u

def symRightScore (c v : BitInput n) : ℤ := rowRight (unitGates (symGates C)) c v

def symLookupFn (s : ℤ) : Bool :=
  if h : 0 ≤ s ∧ s.toNat ≤ C.bottomCount then C.top ⟨s.toNat, Nat.lt_succ_of_le h.2⟩ else false

theorem length_symGates : (symGates C).length = C.bottomCount := by simp [symGates]

theorem acceptedBottomCount_eq (x : BitInput n) :
    ((C.acceptedBottomCount x : ℕ) : ℤ) = (((symGates C).map fun g => bitZ (g.eval x)).sum : ℤ) := by
  simp only [NormalizedSymmetricThresholdCircuit.acceptedBottomCount, symGates, List.map_map, Function.comp_def]
  rw [← List.ofFn_eq_map, List.sum_ofFn, Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [bitZ, SupportedNormalizedGate.eval]

theorem sym_eval_point (c u v : BitInput n) (hdisj : ∀ i, ¬(u i = true ∧ v i = true)) :
    C.eval (xorInput (xorInput c u) v) =
      symLookupFn C (symLeftScore C c u + symRightScore C c v +
        (((plusBits (symGates C) c u v).count true : ℤ) - (minusBits (symGates C) c u v).count true)) := by
  have hid := count_identity (symGates C) c u v hdisj
  rw [← acceptedBottomCount_eq] at hid
  unfold symLeftScore symRightScore
  rw [← hid]
  unfold symLookupFn
  have hle := Nat.lt_succ_iff.mp (C.acceptedBottomCount (xorInput (xorInput c u) v)).isLt
  rw [dif_pos ⟨Int.natCast_nonneg _, by simpa using hle⟩]
  unfold NormalizedSymmetricThresholdCircuit.eval
  congr 1

theorem symLeftScore_range (c u : BitInput n) :
    -(C.bottomCount : ℤ) ≤ symLeftScore C c u ∧ symLeftScore C c u ≤ C.bottomCount := by
  have h := rowLeft_unit_range (symGates C) c u
  rw [length_symGates] at h
  exact h

theorem symRightScore_range (c v : BitInput n) :
    0 ≤ symRightScore C c v ∧ symRightScore C c v ≤ C.bottomCount := by
  have h := rowRight_unit_range (symGates C) c v
  rw [length_symGates] at h
  exact h

end Sym

end NearCubicWires.WireExponent3_5.Primitive
