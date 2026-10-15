import Proof.Gates.EveryLengthPadding
import Proof.Gates.MainBudgetDilation

/-! Assembly of the main theorem's budget and agreement target from a native family, a length schedule and an
    E^NP certificate, which are hypotheses of the lemmas below. -/

set_option autoImplicit false

namespace NearCubicGates.HeadlineAssembly

open NearCubicWires Target

def padded (q : ℕ → ℕ) (hq : ∀ n, q n ≤ n)
    (native : (n : ℕ) → BoolFunction (q n)) : Language :=
  fun n x => native n (fun i => x ⟨i.val, lt_of_lt_of_le i.isLt (hq n)⟩)

theorem exists_prefix_restriction {m n : ℕ} (h : m ≤ n)
    (C : WeightedSymmetricCircuit n) (f : BoolFunction m) :
    ∃ small : WeightedSymmetricCircuit m,
      small.topWeight = C.topWeight ∧
      FiniteAverages.agreement C.eval
        (fun x => f (fun i => x ⟨i.val, lt_of_lt_of_le i.isLt h⟩)) ≤
          FiniteAverages.agreement small.eval f := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  obtain ⟨suffix, hw, ha⟩ := exists_padding_restriction C f
  exact ⟨C.restrictSuffix suffix, hw, ha⟩

theorem padded_hardness
    (q : ℕ → ℕ) (hq : ∀ n, q n ≤ n)
    (native : (n : ℕ) → BoolFunction (q n))
    (D B onset : ℕ) (hD : 0 < D) (hB : 0 < B)
    (hdilate : ∀ n, onset ≤ n → n ≤ B * q n)
    (d : ℝ)
    (hnative : ∀ n, onset ≤ n → ∀ C : WeightedSymmetricCircuit (q n),
      MainBudget D (q n) C.topWeight →
        FiniteAverages.agreement C.eval (native n) < 1 - d) :
    ∃ K : ℕ, 0 < K ∧ ∀ n, onset ≤ n →
      ∀ C : WeightedSymmetricCircuit n,
        MainBudget K n C.topWeight → agreement C (padded q hq native) < 1 - d := by
  refine ⟨D * B ^ 3, by positivity, ?_⟩
  intro n hn C hC
  have hbudget := mainBudget_dilation hB (le_refl (D * B ^ 3))
    (hq n) (hdilate n hn) hC
  obtain ⟨small, hw, ha⟩ := exists_prefix_restriction (hq n) C (native n)
  have hh := hnative n hn small (by simpa [hw] using hbudget)
  rw [agreement_eq_mean]
  exact lt_of_le_of_lt ha hh

structure NativeFrontier (γ ε : ℝ) where
  q : ℕ → ℕ
  q_le : ∀ n, q n ≤ n
  native : (n : ℕ) → BoolFunction (q n)
  budgetConstant : ℕ
  budgetPositive : 0 < budgetConstant
  dilation : ℕ
  dilationPositive : 0 < dilation
  onset : ℕ
  lengthBound : ∀ n, onset ≤ n → n ≤ dilation * q n
  hard : ∀ n, onset ≤ n → ∀ C : WeightedSymmetricCircuit (q n),
    MainBudget budgetConstant (q n) C.topWeight →
      FiniteAverages.agreement C.eval (native n) < 1 - γ / 5 + ε
  ordinaryRecovery : InENP (padded q q_le native)

theorem mainAt_of_native_frontier (γ : ℚ) (hγ : 0 < γ)
    (hfrontier : ∀ ε : ℝ, 0 < ε → ε < (γ : ℝ) / 5 →
      Nonempty (NativeFrontier γ ε)) : MainAt γ := by
  intro d hd hdγ
  let ε : ℝ := ((γ : ℝ) / 5 - d) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hεγ : ε < (γ : ℝ) / 5 := by
    have hγr : (0 : ℝ) < γ := by exact_mod_cast hγ
    dsimp [ε]
    linarith
  obtain ⟨F⟩ := hfrontier ε hε hεγ
  have hn : ∀ n, F.onset ≤ n → ∀ C : WeightedSymmetricCircuit (F.q n),
      MainBudget F.budgetConstant (F.q n) C.topWeight →
        FiniteAverages.agreement C.eval (F.native n) < 1 - d := by
    intro n hn C hC
    have h := F.hard n hn C hC
    dsimp [ε] at h
    linarith
  obtain ⟨K, hK, hhard⟩ := padded_hardness F.q F.q_le F.native
    F.budgetConstant F.dilation F.onset F.budgetPositive F.dilationPositive F.lengthBound d hn
  refine ⟨K, hK, padded F.q F.q_le F.native, F.ordinaryRecovery,
    max 4 F.onset, le_max_left _ _, ?_⟩
  intro n hN
  exact hhard n (le_trans (le_max_right _ _) hN)

theorem mainStatement_of_native_frontier (γ : ℚ) (hγ : 0 < γ) (hγ₁ : γ < 1)
    (hfrontier : ∀ ε : ℝ, 0 < ε → ε < (γ : ℝ) / 5 →
      Nonempty (NativeFrontier γ ε)) : MainStatement :=
  ⟨γ, hγ, hγ₁, mainAt_of_native_frontier γ hγ hfrontier⟩

end NearCubicGates.HeadlineAssembly
