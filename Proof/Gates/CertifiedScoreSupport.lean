import Proof.Gates.DigitClassReconstruction
import Proof.Gates.MomentCompleteness
import Proof.Gates.ScoreBox

/-! Passing literal even moments supplies pointwise score support in the
    computed box for arbitrary proposed chains. This discharges the support
    premise used by digit-class reconstruction, rather than assuming it. -/

set_option autoImplicit false

namespace NearCubicGates.CertifiedScoreSupport

open scoped BigOperators
open CountingCore ScoreBox DigitClassReconstruction

theorem finite_integer_moment_sound {Points : Type*} [Fintype Points]
    (k R : ℕ) (v : Points → ℤ)
    (htest : (∑ x : Points, v x ^ (2 * k)) < (R : ℤ) ^ (2 * k)) :
    ∀ x, (v x).natAbs < R := by
  intro x
  have ht : (∑ x : Points, (v x).natAbs ^ (2 * k)) < R ^ (2 * k) := by
    simp_rw [even_power_eq_magnitude] at htest
    exact_mod_cast htest
  have hx := Finset.single_le_sum (fun y (_ : y ∈ (Finset.univ : Finset Points)) =>
    Nat.zero_le ((v y).natAbs ^ (2 * k))) (Finset.mem_univ x)
  by_contra hn
  have hp := Nat.pow_le_pow_left (by omega : R ≤ (v x).natAbs) (2 * k)
  omega

theorem reconstruct_ext_upto (rate e f : ℕ → ℤ) (J : ℕ)
    (hef : ∀ j, j ≤ J → e j = f j) : reconstruct rate e J = reconstruct rate f J := by
  induction J with
  | zero => exact hef 0 (by omega)
  | succ J ih =>
    simp only [reconstruct, ih (fun j hj => hef j (by omega)), hef (J + 1) (by omega)]

def digitVector {Points : Type*} (rate : ℕ → ℤ) (values : Points → ℕ → ℤ)
    (J : ℕ) (x : Points) (i : Fin (J + 1)) : ℤ := proposedDigit rate (values x) i.val

def extendDigits {J : ℕ} (κ : Fin (J + 1) → ℤ) (j : ℕ) : ℤ :=
  if hj : j < J + 1 then κ ⟨j, hj⟩ else 0

theorem final_value_on_class {Points : Type*} (rate : ℕ → ℤ)
    (values : Points → ℕ → ℤ) (J : ℕ) (κ : Fin (J + 1) → ℤ)
    (x : ExactClass (digitVector rate values J) κ) :
    values x.val J = reconstruct rate (extendDigits κ) J := by
  rw [← reconstruct_proposedDigit rate (values x.val) J]
  apply reconstruct_ext_upto
  intro j hj
  have hx := x.property ⟨j, by omega⟩
  simpa only [digitVector, extendDigits, dif_pos (by omega : j < J + 1)] using hx

def phi {Points : Type*} (M A : ℤ) (values : Points → ℕ → ℤ) (score : Points → ℤ)
    (J : ℕ) (x : Points) : ℤ := M * values x J - A * score x

def boxCenter {Points : Type*} (rate : ℕ → ℤ) (values : Points → ℕ → ℤ)
    (J : ℕ) (κ : Fin (J + 1) → ℤ) (M : ℤ) (reference : Points) : ℤ :=
  M * (reconstruct rate (extendDigits κ) J - values reference J)

theorem moment_implies_score_box {Points : Type*} [Fintype Points]
    (rate : ℕ → ℤ) (values : Points → ℕ → ℤ) (score : Points → ℤ)
    (J k R : ℕ) (M A : ℤ) (hA : 0 < A) (reference : Points)
    (htest : (∑ x : Points,
      (phi M A values score J x - phi M A values score J reference) ^ (2 * k)) <
        (R : ℤ) ^ (2 * k))
    (κ : Fin (J + 1) → ℤ) (x : ExactClass (digitVector rate values J) κ) :
    lower (boxCenter rate values J κ M reference) A (score reference) R ≤ score x.val ∧
      score x.val ≤ upper (boxCenter rate values J κ M reference) A (score reference) R := by
  have hmag := finite_integer_moment_sound k R
    (fun x => phi M A values score J x - phi M A values score J reference) htest x.val
  have hid : phi M A values score J x.val - phi M A values score J reference =
      boxCenter rate values J κ M reference - A * (score x.val - score reference) := by
    unfold phi boxCenter
    rw [final_value_on_class rate values J κ x]
    ring
  rw [hid] at hmag
  apply score_in_box _ _ _ _ _ hA
  exact_mod_cast hmag

def frameIndex (lo : ℤ) (L : ℕ) (score : ℤ) (_hlo : lo ≤ score)
    (hwidth : (score - lo).toNat < L) : Fin L := ⟨(score - lo).toNat, hwidth⟩

theorem frameIndex_score (lo : ℤ) (L : ℕ) (score : ℤ) (hlo : lo ≤ score)
    (hwidth : (score - lo).toNat < L) :
    lo + ((frameIndex lo L score hlo hwidth).val : ℤ) = score := by
  dsimp [frameIndex]
  rw [Int.toNat_of_nonneg (by omega : 0 ≤ score - lo)]
  omega

theorem score_offset_lt_window (center A reference R : ℤ) (L : ℕ) (score : ℤ)
    (hA : 0 < A) (hwidth : 2 * R - 2 ≤ ((L : ℤ) - 1) * A)
    (hscore : lower center A reference R ≤ score ∧ score ≤ upper center A reference R) :
    (score - lower center A reference R).toNat < L := by
  have hc := boxCount_le center A reference R L hA (by omega) hwidth
  unfold boxCount at hc
  omega

end NearCubicGates.CertifiedScoreSupport
