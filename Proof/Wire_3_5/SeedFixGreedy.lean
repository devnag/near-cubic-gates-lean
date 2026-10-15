import Proof.Wire_3_5.FinalPassGreedy

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.SeedFix
open NearCubicWires.WireExponent3_5.FinalPass

/-- **The printed decisions**: the first bit is `true` iff the printed sum of child `true` is smaller (ties to `false`,
"a child with no larger sum"), then recurse on the chosen child. -/
def greedyPrefix : (m : ℕ) → (List Bool → ℤ) → List Bool
  | 0, _ => []
  | m + 1, R => decide (R [true] < R [false]) :: greedyPrefix m fun p => R (decide (R [true] < R [false]) :: p)

/-- One round of the machine's loop: append the child with no larger printed sum. -/
def greedyStep (R : List Bool → ℤ) (p : List Bool) : List Bool := p ++ [decide (R (p ++ [true]) < R (p ++ [false]))]

/-- **The machine's loop**: `m` rounds from the empty prefix. -/
def greedyLoop (m : ℕ) (R : List Bool → ℤ) : List Bool := (greedyStep R)^[m] []

theorem iterate_greedyStep (R : List Bool → ℤ) :
    ∀ (k : ℕ) (q : List Bool), (greedyStep R)^[k] q = q ++ greedyPrefix k fun p => R (q ++ p)
  | 0, q => by simp [greedyPrefix]
  | k + 1, q => by
    rw [Function.iterate_succ_apply, iterate_greedyStep R k]
    simp only [greedyStep, greedyPrefix, List.append_assoc, List.singleton_append]

/-- **The loop is the recursive decision list.** -/
theorem greedyLoop_eq_prefix (m : ℕ) (R : List Bool → ℤ) : greedyLoop m R = greedyPrefix m R := by
  unfold greedyLoop
  rw [iterate_greedyStep]
  rfl

/-- **The conditional objective** of a prefix: the mean of `Φ` over its completions (an overlong prefix reads `Φ` at the
all-`false` completion; it does not occur). -/
def condMean : (m : ℕ) → ((Fin m → Bool) → ℚ) → List Bool → ℚ
  | _, Φ, [] => qMean Φ
  | 0, Φ, _ :: _ => Φ Fin.elim0
  | m + 1, Φ, b :: p => condMean m (fun s => Φ (Fin.cons b s)) p

theorem condMean_nil (m : ℕ) (Φ : (Fin m → Bool) → ℚ) : condMean m Φ [] = qMean Φ := by
  cases m <;> rfl

theorem condMean_cons (m : ℕ) (Φ : (Fin (m + 1) → Bool) → ℚ) (b : Bool) (p : List Bool) :
    condMean (m + 1) Φ (b :: p) = condMean m (fun s => Φ (Fin.cons b s)) p := rfl

def ScaledSums (m : ℕ) (Φ : (Fin m → Bool) → ℚ) (R : List Bool → ℤ) (c : ℕ → ℚ) : Prop :=
  (∀ i, 0 < c i) ∧ ∀ (p : List Bool) (b : Bool), p.length < m → (R (p ++ [b]) : ℚ) = c p.length * condMean m Φ (p ++ [b])

theorem scaledSums_tail (m : ℕ) (Φ : (Fin (m + 1) → Bool) → ℚ) (R : List Bool → ℤ) (c : ℕ → ℚ)
    (h : ScaledSums (m + 1) Φ R c) (b : Bool) :
    ScaledSums m (fun s => Φ (Fin.cons b s)) (fun p => R (b :: p)) (fun i => c (i + 1)) := by
  refine ⟨fun i => h.1 (i + 1), fun p b' hp => ?_⟩
  have := h.2 (b :: p) b' (by simp; omega)
  simp only [List.cons_append, List.length_cons] at this
  rw [condMean_cons] at this
  exact this

theorem greedyPrefix_eq_greedyQ : ∀ (m : ℕ) (Φ : (Fin m → Bool) → ℚ) (R : List Bool → ℤ) (c : ℕ → ℚ),
    ScaledSums m Φ R c → greedyPrefix m R = List.ofFn (greedyQ m Φ)
  | 0, _, _, _, _ => rfl
  | m + 1, Φ, R, c, h => by
    have ht := h.2 [] true (by simp)
    have hf := h.2 [] false (by simp)
    simp only [List.nil_append, List.length_nil, condMean_cons, condMean_nil] at ht hf
    have hc := h.1 0
    have hdec : decide (R [true] < R [false]) =
        decide (qMean (fun s => Φ (Fin.cons true s)) < qMean (fun s => Φ (Fin.cons false s))) := by
      apply decide_eq_decide.mpr
      have e1 : (R [true] : ℚ) = c 0 * qMean (fun s => Φ (Fin.cons true s)) := ht
      have e2 : (R [false] : ℚ) = c 0 * qMean (fun s => Φ (Fin.cons false s)) := hf
      rw [← Int.cast_lt (R := ℚ), e1, e2]
      exact mul_lt_mul_iff_right₀ hc
    unfold greedyPrefix greedyQ
    rw [hdec]
    by_cases hlt : qMean (fun s => Φ (Fin.cons true s)) < qMean (fun s => Φ (Fin.cons false s))
    · rw [if_neg (not_le.mpr hlt), decide_eq_true hlt, List.ofFn_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [greedyPrefix_eq_greedyQ m _ _ _ (scaledSums_tail m Φ R c h true)]
    · rw [if_pos (not_lt.mp hlt), decide_eq_false hlt, List.ofFn_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [greedyPrefix_eq_greedyQ m _ _ _ (scaledSums_tail m Φ R c h false)]

/-- **The machine's loop is the rational greedy.** -/
theorem greedyLoop_eq_greedyQ (m : ℕ) (Φ : (Fin m → Bool) → ℚ) (R : List Bool → ℤ) (c : ℕ → ℚ)
    (h : ScaledSums m Φ R c) : greedyLoop m R = List.ofFn (greedyQ m Φ) := by
  rw [greedyLoop_eq_prefix, greedyPrefix_eq_greedyQ m Φ R c h]

end NearCubicWires.WireExponent3_5.SeedFix
