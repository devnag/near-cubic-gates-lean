import Proof.Wire_3_5.FinalPassHash

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Filters

/-- The uniform mean over a finite type, in `ℚ`. -/
def qMean {Ω : Type} [Fintype Ω] (f : Ω → ℚ) : ℚ := (∑ ω, f ω) / Fintype.card Ω

theorem uMean_cast {Ω : Type} [Fintype Ω] (f : Ω → ℚ) : uMean (fun ω => (f ω : ℝ)) = ((qMean f : ℚ) : ℝ) := by
  unfold uMean qMean
  push_cast
  rfl

def greedyQ : (m : ℕ) → ((Fin m → Bool) → ℚ) → (Fin m → Bool)
  | 0, _ => Fin.elim0
  | m + 1, Φ =>
    if qMean (fun s => Φ (Fin.cons false s)) ≤ qMean (fun s => Φ (Fin.cons true s)) then
      Fin.cons false (greedyQ m fun s => Φ (Fin.cons false s))
    else Fin.cons true (greedyQ m fun s => Φ (Fin.cons true s))

/-- **The real greedy on a rational objective is the rational greedy.** -/
theorem greedy_cast : ∀ (m : ℕ) (Φ : (Fin m → Bool) → ℚ), greedy m (fun s => (Φ s : ℝ)) = greedyQ m Φ
  | 0, _ => rfl
  | m + 1, Φ => by
    unfold greedy greedyQ
    simp only
    have hf := uMean_cast (fun s => Φ (Fin.cons false s))
    have ht := uMean_cast (fun s => Φ (Fin.cons true s))
    by_cases h : qMean (fun s => Φ (Fin.cons false s)) ≤ qMean (fun s => Φ (Fin.cons true s))
    · rw [if_pos h, if_pos (by rw [hf, ht]; exact_mod_cast h), greedy_cast m]
    · rw [if_neg h, if_neg (by rw [hf, ht]; exact_mod_cast h), greedy_cast m]

end NearCubicWires.WireExponent3_5.FinalPass
