import Proof.Wire_3_5.PrimitiveSymRow
import Proof.Wire_3_5.RowsThr
import Proof.Foundations.SupplierPrime

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires NearCubicWires.SupplierPipeline NearCubicWires.SupplierPrime NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Rows

variable {n : ℕ} (occs : List (SupportedNormalizedGate n)) (eq : LabelledEquation (Fin occs.length))

/-- The occurrence values `X_i(x)`. -/
def occVals (x : BitInput n) : Fin occs.length → Bool := fun i => (occs.get i).eval x

/-- The equation's weighted gate list. -/
def eqGates : List (ℤ × NormalizedThresholdGate n) := List.ofFn fun i => (eq.weights i, (occs.get i).gate)

def thrLeft (c u : BitInput n) : ℤ := rowLeft (-eq.target) (eqGates occs eq) c u

def thrRight (c v : BitInput n) : ℤ := rowRight (eqGates occs eq) c v

/-- The residual vectors `Z_i^±` of the occurrences at `(c,u,v)`. -/
def occPlus (c u v : BitInput n) (i : Fin occs.length) : Bool := residualPlus (occs.get i).gate.eval c u v

def occMinus (c u v : BitInput n) (i : Fin occs.length) : Bool := residualMinus (occs.get i).gate.eval c u v

theorem list_sum_ofFn_eq {m : ℕ} (f : Fin m → ℤ) : (List.ofFn f).sum = ∑ i, f i := List.sum_ofFn

theorem thr_difference_point (c u v : BitInput n) (hdisj : ∀ i, ¬(u i = true ∧ v i = true)) :
    eq.difference (occVals occs (xorInput (xorInput c u) v)) =
      thrLeft occs eq c u + thrRight occs eq c v +
        ∑ i, eq.weights i * (bitZ (occPlus occs c u v i) - bitZ (occMinus occs c u v i)) := by
  have h := row_identity (-eq.target) (eqGates occs eq) c u v hdisj
  have htop : topScore (eqGates occs eq) c u v = eq.score (occVals occs (xorInput (xorInput c u) v)) := by
    unfold topScore eqGates LabelledEquation.score occVals
    rw [List.map_ofFn, list_sum_ofFn_eq]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Function.comp_apply, Int.cast_id, SupportedNormalizedGate.eval]
    rfl
  have hres : residualTerm (eqGates occs eq) c u v =
      ∑ i, eq.weights i * (bitZ (occPlus occs c u v i) - bitZ (occMinus occs c u v i)) := by
    unfold residualTerm eqGates occPlus occMinus
    rw [List.map_ofFn, list_sum_ofFn_eq]
    rfl
  unfold LabelledEquation.difference thrLeft thrRight
  rw [← hres, ← htop]
  linarith

/-! ## Digits -/

theorem digit_expansion (b0 : ℕ) (hb : 2 ≤ b0) : ∀ (τ₀ a : ℕ), a < b0 ^ τ₀ →
    a = ∑ d : Fin τ₀, a / b0 ^ (d : ℕ) % b0 * b0 ^ (d : ℕ)
  | 0, a, ha => by simp at ha; simp [ha]
  | τ₀ + 1, a, ha => by
    rw [Fin.sum_univ_succ]
    have hdiv : a / b0 < b0 ^ τ₀ := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]; rw [pow_succ] at ha; exact ha
    have ih := digit_expansion b0 hb τ₀ (a / b0) hdiv
    have hsucc : ∀ d : Fin τ₀, a / b0 ^ ((d.succ : Fin (τ₀ + 1)) : ℕ) % b0 * b0 ^ ((d.succ : Fin (τ₀ + 1)) : ℕ) =
        b0 * (a / b0 / b0 ^ (d : ℕ) % b0 * b0 ^ (d : ℕ)) := by
      intro d
      simp only [Fin.val_succ, pow_succ, Nat.div_div_eq_div_mul]
      rw [mul_comm (b0 ^ (d : ℕ)) b0]
      ring
    simp only [hsucc, ← Finset.mul_sum, ← ih]
    simp only [Fin.val_zero, pow_zero, Nat.div_one, mul_one]
    exact (Nat.mod_add_div a b0).symm

def redCoeff (p : ℕ) (i : Fin occs.length) : ℕ := (eq.weights i % (p : ℤ)).toNat

/-- The digits `v_{i,d}` of the reduced coefficient in radix `b_0`. -/
def digitOf (p b0 τ₀ : ℕ) (i : Fin occs.length) (d : Fin τ₀) : ℕ := redCoeff occs eq p i / b0 ^ (d : ℕ) % b0

theorem redCoeff_lt (p : ℕ) (hp : 0 < p) (i : Fin occs.length) : redCoeff occs eq p i < p := by
  unfold redCoeff
  have h1 := Int.emod_nonneg (eq.weights i) (by exact_mod_cast hp.ne' : (p : ℤ) ≠ 0)
  have h2 := Int.emod_lt_of_pos (eq.weights i) (by exact_mod_cast hp : (0 : ℤ) < p)
  omega

theorem redCoeff_cast (p : ℕ) (hp : 0 < p) (i : Fin occs.length) :
    ((redCoeff occs eq p i : ℕ) : ZMod p) = (eq.weights i : ZMod p) := by
  have hnn := Int.emod_nonneg (eq.weights i) (by exact_mod_cast hp.ne' : (p : ℤ) ≠ 0)
  have hk : ((redCoeff occs eq p i : ℕ) : ℤ) = eq.weights i % (p : ℤ) := Int.toNat_of_nonneg hnn
  calc ((redCoeff occs eq p i : ℕ) : ZMod p) = (((redCoeff occs eq p i : ℕ) : ℤ) : ZMod p) :=
        (Int.cast_natCast _).symm
    _ = ((eq.weights i % (p : ℤ) : ℤ) : ZMod p) := by rw [hk]
    _ = (eq.weights i : ZMod p) := ZMod.intCast_mod _ _

def digitPop (v : Fin occs.length → ℕ) (Z : Fin occs.length → Bool) : List Bool :=
  (List.finRange occs.length).flatMap fun i => List.replicate (v i) (Z i)

theorem count_digitPop (v : Fin occs.length → ℕ) (Z : Fin occs.length → Bool) :
    (digitPop occs v Z).count true = ∑ i, v i * (Z i).toNat := by
  unfold digitPop
  rw [List.count_flatMap, ← List.ofFn_eq_map, List.sum_ofFn]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Function.comp_apply, List.count_replicate]
  cases Z i <;> simp

theorem length_digitPop_le (v : Fin occs.length → ℕ) (Z : Fin occs.length → Bool) (K : ℕ) (hv : ∀ i, v i ≤ K) :
    (digitPop occs v Z).length ≤ occs.length * K := by
  unfold digitPop
  rw [List.length_flatMap, ← List.ofFn_eq_map, List.sum_ofFn]
  calc ∑ i, (List.replicate (v i) (Z i)).length = ∑ i, v i := by simp
    _ ≤ ∑ _i : Fin occs.length, K := Finset.sum_le_sum fun i _ => hv i
    _ = occs.length * K := by simp

/-! ## The modular row at a star point -/

theorem thr_modular_point {cutoff : ℕ} (prime : PrimeIndex cutoff) (b0 τ₀ : ℕ) (hb : 2 ≤ b0)
    (hτ : prime.val ≤ b0 ^ τ₀) [NeZero prime.val] (c u v : BitInput n)
    (hdisj : ∀ i, ¬(u i = true ∧ v i = true)) :
    modularEquationHolds eq prime (occVals occs (xorInput (xorInput c u) v)) =
      thrReported (thrLeft occs eq c u) (thrRight occs eq c v)
        (tupleResidue prime.val b0
          (fun d => (digitPop occs (fun i => digitOf occs eq prime.val b0 τ₀ i d) (occPlus occs c u v)).count true)
          (fun d => (digitPop occs (fun i => digitOf occs eq prime.val b0 τ₀ i d) (occMinus occs c u v)).count true)) := by
  set p := prime.val
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  have hdig : ∀ i, redCoeff occs eq p i = ∑ d : Fin τ₀, digitOf occs eq p b0 τ₀ i d * b0 ^ (d : ℕ) := fun i =>
    digit_expansion b0 hb τ₀ _ ((redCoeff_lt occs eq p hp i).trans_le hτ)
  have hradix := radix_signed_eq b0 (redCoeff occs eq p) (fun i d => digitOf occs eq p b0 τ₀ i d) hdig
    (occPlus occs c u v) (occMinus occs c u v)
  -- the residual term modulo `p` through the reduced coefficients
  have hres : ((∑ i, eq.weights i * (bitZ (occPlus occs c u v i) - bitZ (occMinus occs c u v i)) : ℤ) : ZMod p) =
      ((∑ i, (redCoeff occs eq p i : ℤ) * (((occPlus occs c u v i).toNat : ℤ) - (occMinus occs c u v i).toNat) : ℤ) :
        ZMod p) := by
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [redCoeff_cast occs eq p hp i]
    congr 1
    cases occPlus occs c u v i <;> cases occMinus occs c u v i <;> simp [bitZ]
  have hS : ((∑ i, eq.weights i * (bitZ (occPlus occs c u v i) - bitZ (occMinus occs c u v i)) : ℤ) : ZMod p) =
      tupleResidue p b0
        (fun d => (digitPop occs (fun i => digitOf occs eq p b0 τ₀ i d) (occPlus occs c u v)).count true)
        (fun d => (digitPop occs (fun i => digitOf occs eq p b0 τ₀ i d) (occMinus occs c u v)).count true) := by
    rw [hres, hradix]
    unfold tupleResidue
    simp only [count_digitPop, digitCount]
  have key : ((eq.difference (occVals occs (xorInput (xorInput c u) v)) : ℤ) : ZMod p) =
      (thrLeft occs eq c u : ZMod p) + (thrRight occs eq c v : ZMod p) +
        tupleResidue p b0
          (fun d => (digitPop occs (fun i => digitOf occs eq p b0 τ₀ i d) (occPlus occs c u v)).count true)
          (fun d => (digitPop occs (fun i => digitOf occs eq p b0 τ₀ i d) (occMinus occs c u v)).count true) := by
    rw [thr_difference_point occs eq c u v hdisj, Int.cast_add, Int.cast_add, hS]
  have hdvd : ∀ z : ℤ, z % (p : ℤ) = 0 ↔ ((z : ZMod p) = 0) := fun z => by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact ⟨Int.dvd_of_emod_eq_zero, Int.emod_eq_zero_of_dvd⟩
  unfold modularEquationHolds thrReported
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  unfold LabelledEquation.HoldsModulo
  rw [hdvd, key]

end NearCubicWires.WireExponent3_5.Primitive
