import Mathlib
import Proof.Wire_3_5.MaskedExpectation

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Shared

def KWiseUniform {S L V : Type} [Fintype S] [Fintype V] [DecidableEq V] (t : ℕ) (f : S → L → V) : Prop :=
  ∀ ls : Finset L, ls.card ≤ t → ∀ val : L → V,
    (Finset.univ.filter fun s => ∀ l ∈ ls, f s l = val l).card * Fintype.card V ^ ls.card = Fintype.card S

def ReadsOnly {L V : Type} (ls : Finset L) (g : (L → V) → ℝ) : Prop :=
  ∀ w w' : L → V, (∀ l ∈ ls, w l = w' l) → g w = g w'

/-- S3.1, moment transfer: a statistic reading at most `t` labels has the same mean under a `t`-wise
uniform family as under fully independent labels. -/
def ExpectEqIndep : Prop :=
  ∀ {S L V : Type} [Fintype S] [Fintype L] [Fintype V] [DecidableEq V] [DecidableEq L]
    (t : ℕ) (f : S → L → V), KWiseUniform t f →
    ∀ (ls : Finset L), ls.card ≤ t → ∀ g : (L → V) → ℝ, ReadsOnly ls g →
      uMean (fun s => g (f s)) = uMean (fun w : L → V => g w)

def PolyEvalKWise : Prop :=
  ∀ {K L : Type} [Field K] [Fintype K] [DecidableEq K] (t : ℕ) (label : L → K),
    Function.Injective label →
    KWiseUniform t (fun (c : Fin t → K) (l : L) => ∑ i : Fin t, c i * label l ^ (i : ℕ))

def ProjectKWise : Prop :=
  ∀ {S L V W : Type} [Fintype S] [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    [AddCommGroup V] [AddCommGroup W] (t : ℕ) (f : S → L → V) (π : V →+ W),
    Function.Surjective π → KWiseUniform t f → KWiseUniform t (fun s l => π (f s l))

def ScalarEvenMoment : Prop :=
  ∀ {S L V : Type} [Fintype S] [Fintype V] [DecidableEq V] [DecidableEq L]
    (t : ℕ) (f : S → L → V), KWiseUniform (2 * t) f →
    ∀ (φ : L → V → ℝ) (A : Finset L) (p : ℝ) (B : ℕ), A.card ≤ B →
      (∀ l v, |φ l v| ≤ 1) → (∀ l, uMean (φ l) = 0) → (∀ l, uMean (fun v => φ l v ^ 2) ≤ p) →
      uMean (fun s => (∑ l ∈ A, φ l (f s l)) ^ (2 * t)) ≤
        (2 * (Real.sqrt (t * B * p) + t)) ^ (2 * t)

theorem tail_le_moment {Ω : Type} [Fintype Ω] (X : Ω → ℝ) {a : ℝ} (ha : 0 < a) (t : ℕ) :
    uMean (fun ω => bitR (decide (a < |X ω|))) ≤ uMean (fun ω => X ω ^ (2 * t)) / a ^ (2 * t) := by
  have hpt : ∀ ω, bitR (decide (a < |X ω|)) ≤ X ω ^ (2 * t) / a ^ (2 * t) := by
    intro ω
    by_cases h : a < |X ω|
    · simp only [h, decide_true, bitR, if_true]
      rw [le_div_iff₀ (pow_pos ha _), one_mul, pow_mul, pow_mul, ← sq_abs (X ω)]
      exact pow_le_pow_left₀ (by positivity) (pow_le_pow_left₀ ha.le h.le 2) t
    · simp only [h, decide_false, bitR]
      exact div_nonneg (by rw [pow_mul]; positivity) (by positivity)
  calc _ ≤ uMean (fun ω => X ω ^ (2 * t) / a ^ (2 * t)) := uMean_mono hpt
    _ = _ := by unfold uMean; rw [← Finset.sum_div, div_div, div_div, mul_comm (a ^ (2 * t))]

def GreedySeedFixing : Prop :=
  ∀ (m : ℕ) (Φ : (Fin m → Bool) → ℝ), ∃ s : Fin m → Bool, Φ s ≤ uMean Φ

/-- The trivial SAT witness for `KWiseUniform`: independent labels (`P9`). Statement only. -/
def IdentityKWise : Prop :=
  ∀ {L V : Type} [Fintype L] [DecidableEq L] [Fintype V] [DecidableEq V] (t : ℕ),
    KWiseUniform t (fun (w : L → V) (l : L) => w l)

end NearCubicWires.WireExponent3_5.Shared
