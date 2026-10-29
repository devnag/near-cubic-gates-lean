import SourceAdapters.Williams.Restriction

/-!
# Vacuity checks for the Williams leaf (identity machine; constant machine)

* `identityTM` halts at once; its output tape is its input (the model represents the trivial program).
* `constantTM` writes one digit and halts after one step (the model executes a real transition).
* `range_nonempty`: the leaf's hypotheses `N₀ ≤ N`, `m = N^{1/10}` hold at every onset (with `N = k^10`).
* `identity_fails`: at every onset some instance defeats the identity machine, so the leaf's conclusion is not
  satisfied by a trivial machine (its output really is the product, not the input).
-/

namespace NearCubicGates.Adapters.Williams.Vacuity

open NearCubicGates.Published.Williams NearCubicGates.Adapters.Williams

set_option autoImplicit false

/-- The machine with no transitions, one tape, one state. -/
def identityTM : MultitapeTM where
  tapes := 1
  extraSymbols := 0
  states := 1
  start := 0
  transition := fun _ _ => none

/-- The one tape of `identityTM`. -/
def identityTape : Fin identityTM.tapes := ⟨0, Nat.one_pos⟩

theorem identity_halts (w : List (Symbol 0)) :
    identityTM.run 0 (identityTM.initial identityTape w) = some (identityTM.initial identityTape w) ∧
      identityTM.step (identityTM.initial identityTape w) = none ∧
      (identityTM.initial identityTape w).contents identityTape = fun p => w.getD p Symbol.blank := by
  refine ⟨rfl, rfl, ?_⟩
  funext p
  rw [MultitapeTM.initial]
  dsimp only
  exact if_pos rfl

/-- Every run of the identity machine stays in its initial configuration. -/
theorem identity_run (w : List (Symbol 0)) (t : ℕ) (c : identityTM.Configuration)
    (h : identityTM.run t (identityTM.initial identityTape w) = some c) : c = identityTM.initial identityTape w := by
  cases t with
  | zero => simpa [MultitapeTM.run] using h.symm
  | succ t => simp [MultitapeTM.run, MultitapeTM.step, identityTM] at h

/-- The machine that writes the digit `1` on cell `0` and halts. -/
def constantTM : MultitapeTM where
  tapes := 1
  extraSymbols := 0
  states := 2
  start := 0
  transition := fun q _ => if q = 0 then some (1, fun _ => Symbol.digit true, fun _ => Move.stay) else none

/-- The one tape of `constantTM`. -/
def constantTape : Fin constantTM.tapes := ⟨0, Nat.one_pos⟩

theorem constant_run (w : List (Symbol 0)) :
    ∃ c, constantTM.run 1 (constantTM.initial constantTape w) = some c ∧ constantTM.step c = none ∧
      c.contents constantTape 0 = Symbol.digit true := by
  refine ⟨_, rfl, ?_, ?_⟩
  · simp [MultitapeTM.step, MultitapeTM.initial, constantTM]
  · simp [MultitapeTM.initial, constantTM]

/-- The hypotheses of the leaf are satisfiable at every onset. -/
theorem range_nonempty (N₀ : ℕ) : ∃ N m : ℕ, N₀ ≤ N ∧ (m : ℝ) = (N : ℝ) ^ (1 / 10 : ℝ) := by
  refine ⟨(N₀ + 1) ^ 10, N₀ + 1, ?_, tenthRoot_pow _⟩
  calc N₀ ≤ N₀ + 1 := Nat.le_succ _
    _ ≤ (N₀ + 1) ^ 10 := Nat.le_self_pow (by norm_num) _

/-- A nonempty matrix's row-major list starts with its `(0,0)` entry. -/
theorem rowMajor_cons {α : Type} {n m : ℕ} (A : Fin n → Fin m → α) (hn : 0 < n) (hm : 0 < m) :
    ∃ rest, rowMajor A = A ⟨0, hn⟩ ⟨0, hm⟩ :: rest := by
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  exact ⟨_, by simp [rowMajor, List.ofFn_succ]; rfl⟩

/-- At `N = k^10` with `k = 2(N₀+1)` and all-ones matrices, the identity machine's output cell `0` is the digit `1`
(the first input entry) while the product word starts with the digit `0` (every entry is `k`, which is even). -/
theorem identity_fails (N₀ : ℕ) : ∃ k : ℕ, N₀ ≤ k ^ 10 ∧
    ∃ (A : Fin (k ^ 10) → Fin k → Bool) (B : Fin k → Fin (k ^ 10) → Bool),
      ∀ (t : ℕ) (c : identityTM.Configuration),
        identityTM.run t (identityTM.initial identityTape (inputWord A B)) = some c →
        c.contents identityTape ≠ fun p => (outputWord (integerProduct A B)).getD p Symbol.blank := by
  have hk0 : 0 < 2 * (N₀ + 1) := by omega
  have hN0 : 0 < (2 * (N₀ + 1)) ^ 10 := by positivity
  refine ⟨2 * (N₀ + 1), ?_, fun _ _ => true, fun _ _ => true, ?_⟩
  · calc N₀ ≤ 2 * (N₀ + 1) := by omega
      _ ≤ (2 * (N₀ + 1)) ^ 10 := Nat.le_self_pow (by norm_num) _
  intro t c hrun heq
  have hc := identity_run _ t c hrun
  subst hc
  have h0 := congrFun heq 0
  obtain ⟨ra, hra⟩ := rowMajor_cons (fun (_ : Fin ((2 * (N₀ + 1)) ^ 10)) (_ : Fin (2 * (N₀ + 1))) => true) hN0 hk0
  obtain ⟨rp, hrp⟩ := rowMajor_cons (integerProduct (fun (_ : Fin ((2 * (N₀ + 1)) ^ 10)) (_ : Fin (2 * (N₀ + 1))) =>
    true) (fun (_ : Fin (2 * (N₀ + 1))) (_ : Fin ((2 * (N₀ + 1)) ^ 10)) => true)) hN0 hN0
  have hprod : integerProduct (fun (_ : Fin ((2 * (N₀ + 1)) ^ 10)) (_ : Fin (2 * (N₀ + 1))) => true)
      (fun (_ : Fin (2 * (N₀ + 1))) (_ : Fin ((2 * (N₀ + 1)) ^ 10)) => true) ⟨0, hN0⟩ ⟨0, hN0⟩ =
      2 * (N₀ + 1) := by
    simp [integerProduct]
  have hdig : Nat.digits 2 (2 * (N₀ + 1)) = 0 :: Nat.digits 2 (N₀ + 1) := by
    rw [Nat.digits_def' (by norm_num) hk0, show 2 * (N₀ + 1) % 2 = 0 by omega,
      show 2 * (N₀ + 1) / 2 = N₀ + 1 by omega]
  have hl : (identityTM.initial identityTape (inputWord (extra := identityTM.extraSymbols)
      (fun (_ : Fin ((2 * (N₀ + 1)) ^ 10)) (_ : Fin (2 * (N₀ + 1))) => true)
      (fun (_ : Fin (2 * (N₀ + 1))) (_ : Fin ((2 * (N₀ + 1)) ^ 10)) => true))).contents identityTape 0 =
      Symbol.digit true := by
    rw [MultitapeTM.initial]
    dsimp only
    rw [if_pos rfl, inputWord, hra, List.map_cons, List.cons_append, List.getD_cons_zero]
  have hr : (outputWord (extra := identityTM.extraSymbols) (integerProduct
      (fun (_ : Fin ((2 * (N₀ + 1)) ^ 10)) (_ : Fin (2 * (N₀ + 1))) => true)
      (fun (_ : Fin (2 * (N₀ + 1))) (_ : Fin ((2 * (N₀ + 1)) ^ 10)) => true))).getD 0 Symbol.blank =
      Symbol.digit false := by
    rw [outputWord, hrp, List.flatMap_cons, hprod, numberWord, hdig, List.map_cons, List.cons_append,
      List.cons_append, List.getD_cons_zero]
    rfl
  rw [hl, hr] at h0
  exact absurd h0 (by decide)

end NearCubicGates.Adapters.Williams.Vacuity
