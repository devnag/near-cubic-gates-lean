import Proof.Wire_3_5.StarSelection

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Shared.StarParams
open NearCubicWires Finset NearCubicWires.WireExponent3_5.Stars

/-- All code lists of length `j` with entries `< 2^s`. -/
def allCodes (s : ℕ) : ℕ → List (List ℕ)
  | 0 => [[]]
  | j + 1 => (List.range (2 ^ s)).flatMap fun a => (allCodes s j).map (a :: ·)

theorem mem_allCodes (s : ℕ) : ∀ (j : ℕ) (l : List ℕ), l ∈ allCodes s j ↔ l.length = j ∧ ∀ t ∈ l, t < 2 ^ s
  | 0, l => by
    cases l with
    | nil => simp [allCodes]
    | cons a l => simp [allCodes]
  | j + 1, l => by
    cases l with
    | nil => simp [allCodes]
    | cons a l =>
      simp only [allCodes, List.mem_flatMap, List.mem_range, List.mem_map, List.cons.injEq, List.length_cons,
        List.mem_cons, forall_eq_or_imp, Nat.add_right_cancel_iff]
      constructor
      · rintro ⟨b, hb, l', hl', rfl, rfl⟩
        have := (mem_allCodes s j l').mp hl'
        exact ⟨this.1, hb, this.2⟩
      · rintro ⟨hlen, ha, hl⟩
        exact ⟨a, ha, l, (mem_allCodes s j l).mpr ⟨hlen, hl⟩, rfl, rfl⟩

variable (P : StarParams)

/-- The codes of a translation: block `j`'s syndrome, read as a number `< 2^s`. -/
def codesOf (σ : P.Translation) : List ℕ := List.ofFn fun j => (finFunctionFinEquiv (σ j)).val

theorem codesOf_mem (σ : P.Translation) : P.codesOf σ ∈ allCodes P.s P.r := by
  rw [mem_allCodes]
  refine ⟨by simp [codesOf], fun t ht => ?_⟩
  simp only [codesOf, List.mem_ofFn] at ht
  obtain ⟨j, rfl⟩ := ht
  exact (finFunctionFinEquiv (σ j)).isLt

theorem translationOfCodes_codesOf (σ : P.Translation) : P.translationOfCodes (P.codesOf σ) = σ := by
  funext j
  simp only [translationOfCodes, codesOf]
  rw [Equiv.symm_apply_eq]
  apply Fin.ext
  have hj : j.val < (List.ofFn fun j => (finFunctionFinEquiv (σ j)).val).length := by simp
  simp only [List.getD_eq_getElem _ _ hj, List.getElem_ofFn]
  exact Nat.mod_eq_of_lt (finFunctionFinEquiv (σ j)).isLt

/-- The first minimizer of `f` in a fold (a deterministic tie-break). -/
def argminFold {α : Type} (f : α → ℚ) (init : α) (xs : List α) : α :=
  xs.foldl (fun best l => if f l < f best then l else best) init

theorem argminFold_spec {α : Type} (f : α → ℚ) :
    ∀ (xs : List α) (init : α), (argminFold f init xs = init ∨ argminFold f init xs ∈ xs) ∧
      f (argminFold f init xs) ≤ f init ∧ ∀ x ∈ xs, f (argminFold f init xs) ≤ f x
  | [], init => by simp [argminFold]
  | x :: xs, init => by
    have hfold : argminFold f init (x :: xs) = argminFold f (if f x < f init then x else init) xs := rfl
    rw [hfold]
    by_cases hx : f x < f init
    · rw [if_pos hx]
      obtain ⟨hmem, hle, hall⟩ := argminFold_spec f xs x
      refine ⟨?_, hle.trans hx.le, ?_⟩
      · right; rcases hmem with h | h
        · rw [h]; exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ h
      · intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hle
        · exact hall y hy
    · rw [if_neg hx]
      obtain ⟨hmem, hle, hall⟩ := argminFold_spec f xs init
      refine ⟨?_, hle, ?_⟩
      · rcases hmem with h | h
        · left; exact h
        · right; exact List.mem_cons_of_mem _ h
      · intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hle.trans (not_lt.mp hx)
        · exact hall y hy

def selectCodes (pops : List (ℚ × Carrier P.n)) : List ℕ :=
  argminFold (fun l => P.starObjectiveRef (P.translationOfCodes l) pops) (List.replicate P.r 0)
    (allCodes P.s P.r)

theorem replicate_mem_allCodes : List.replicate P.r 0 ∈ allCodes P.s P.r := by
  rw [mem_allCodes]
  exact ⟨List.length_replicate, fun t ht => by rw [List.eq_of_mem_replicate ht]; exact Nat.two_pow_pos _⟩

theorem selectCodes_mem (pops : List (ℚ × Carrier P.n)) : P.selectCodes pops ∈ allCodes P.s P.r := by
  rcases (argminFold_spec _ (allCodes P.s P.r) (List.replicate P.r 0)).1 with h | h
  · unfold selectCodes; rw [h]; exact P.replicate_mem_allCodes
  · exact h

/-- The chosen codes are one per block. -/
theorem selectCodes_length (pops : List (ℚ × Carrier P.n)) : (P.selectCodes pops).length = P.r :=
  ((mem_allCodes _ _ _).mp (P.selectCodes_mem pops)).1

/-- The chosen codes are syndromes: each `< 2^s`. -/
theorem selectCodes_lt (pops : List (ℚ × Carrier P.n)) : ∀ t ∈ P.selectCodes pops, t < 2 ^ P.s :=
  ((mem_allCodes _ _ _).mp (P.selectCodes_mem pops)).2

/-- The chosen translation minimizes the exact objective over all partitions. -/
theorem selectCodes_min (pops : List (ℚ × Carrier P.n)) (σ : P.Translation) :
    P.starObjectiveRef (P.translationOfCodes (P.selectCodes pops)) pops ≤ P.starObjectiveRef σ pops := by
  have h := (argminFold_spec (fun l => P.starObjectiveRef (P.translationOfCodes l) pops) (allCodes P.s P.r)
    (List.replicate P.r 0)).2.2 (P.codesOf σ) (P.codesOf_mem σ)
  rw [P.translationOfCodes_codesOf] at h
  exact h

theorem selectCodes_population_le (pops : List (ℚ × Carrier P.n)) (hp : ∀ p ∈ pops, 0 ≤ p.1) :
    (P.objective (P.translationOfCodes (P.selectCodes pops)) pops : ℝ) ≤
      P.popRate * (pops.map fun p => (p.1 : ℝ) * (Carrier.wires p.2 : ℝ)).sum :=
  P.minimizer_le pops hp _ (P.selectCodes_min pops)

end NearCubicWires.WireExponent3_5.Shared.StarParams
