import SourceAdapters.ShortPCP.Machines.FLangRand

/-!
# Single-run time, reference layer 9: each decision reads only the answers of its own queries

A flat verifier's decision `D r ans` is applied to `answersN` (`TimeVerdict.lean`), which is defined at every index,
while a machine holds only the answers to the queries `1, …, query` (proof of `thm:short-pcp-ours`: "The queries of V0 are computed
from the random string alone"; the oracle is read once per query). This module shows that the decisions of
`V_{RS,=}`, `V_{RS,<}`, `V_{RS,>}`, `V_RS` and `V_VRS` (poly-time forms, `TimeVerifiers.lean`) read the answer function
only at `1, …, query` (`vRSF_D_congr`, `vVRSF_D_congr`): the base test reads `1, …, 2^κ`, `D_{RS,=}` reads the base
test's answers at its last level (`κ_last ≤ min κ 4`, so `2^κ_last ≤ query_{RS,=}`), and the composed verifiers read
shifted blocks of these.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.ShortPCP.Time

open NearCubicGates.Published.BCGT13 NearCubicGates.Adapters.ShortPCP.Machines.FL

variable {F : Type} [Field F] [DecidableEq F]

/-- Two answer functions agree on `1, …, q`. -/
def AgreeOn {F : Type} (q : ℕ) (a b : ℕ → F) : Prop := ∀ i, 1 ≤ i → i ≤ q → a i = b i

omit [Field F] [DecidableEq F] in
theorem AgreeOn.mono {q q' : ℕ} {a b : ℕ → F} (h : AgreeOn q a b) (hq : q' ≤ q) : AgreeOn q' a b :=
  fun i h1 h2 => h i h1 (h2.trans hq)

omit [Field F] [DecidableEq F] in
/-- Agreement of a shifted block. -/
theorem AgreeOn.shift {q s n : ℕ} {a b : ℕ → F} (h : AgreeOn q a b) (hn : s + n ≤ q) :
    AgreeOn n (fun i => a (s + i)) (fun i => b (s + i)) :=
  fun i h1 h2 => h (s + i) (by omega) (by omega)

omit [DecidableEq F] in
theorem lagEval_congr' (m : ℕ) (pt val val' : ℕ → F) (x : F) (hv : ∀ j < m, val j = val' j) :
    lagEval m pt val x = lagEval m pt val' x := lagEval_congr m pt pt val val' x (fun _ _ => rfl) hv

/-- The base test reads `1, …, 2^κ`. -/
theorem degreeTestF_congr (B : List F) (O : F) (d : ℕ) {a b : ℕ → F} (h : AgreeOn (2 ^ B.length) a b) :
    degreeTestF B O d a = degreeTestF B O d b := by
  unfold degreeTestF
  split_ifs with h1
  · rfl
  · have hv : ∀ j < d + 1, a (j + 1) = b (j + 1) := fun j hj => h (j + 1) (by omega) (by omega)
    have hl : ∀ x, lagEval (d + 1) (fun j => eltWithIndex B O (j + 1)) (fun j => a (j + 1)) x =
        lagEval (d + 1) (fun j => eltWithIndex B O (j + 1)) (fun j => b (j + 1)) x :=
      fun x => lagEval_congr' _ _ _ _ x hv
    apply Bool.eq_iff_iff.mpr
    simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq]
    refine ⟨fun H i hi => ?_, fun H i hi => ?_⟩
    · rw [← hl, ← h (i + 1) (by omega) (by omega)]; exact H i hi
    · rw [hl, h (i + 1) (by omega) (by omega)]; exact H i hi

/-- `D_{RS,=}` reads `1, …, query_{RS,=}(κ)`. -/
theorem dEqR_congr (B : List F) (O : F) (r : List Bool) {a b : ℕ → F} (h : AgreeOn (queryEq T0 B.length) a b) :
    dEqR B O r a = dEqR B O r b := by
  unfold dEqR
  have e := dEqFF_iter degreeTestF B.length ⟨B, O, r⟩
  simp only at e
  rw [e a, e b]
  apply degreeTestF_congr
  have hst := stop_iterate_depth B.length (⟨B, O, r⟩ : Lvl F) le_rfl
  have hle := length_iterate_le B.length (⟨B, O, r⟩ : Lvl F) _ le_rfl
  simp only [Lvl.stop, decide_eq_true_eq, T0_κ0] at hst
  refine h.mono ?_
  rw [queryEq_eq]
  exact Nat.pow_le_pow_right (by norm_num) (le_min hle hst)

/-- `V_{RS,=}` reads `1, …, query`. -/
theorem vEqF_D_congr (B : List F) (O : F) (r : List Bool) {a b : ℕ → F} (h : AgreeOn (vEqF B O).query a b) :
    (vEqF B O).D r a = (vEqF B O).D r b := dEqR_congr B O r h

/-- `V_{RS,<}` reads `1, …, query`. -/
theorem vLtF_D_congr (B : List F) (O : F) (d : ℕ) (r : List Bool) {a b : ℕ → F}
    (h : AgreeOn (vLtF B O d).query a b) : (vLtF B O d).D r a = (vLtF B O d).D r b := by
  simp only [vLtF] at h ⊢
  rw [dEqR_congr B O r (h.mono (by omega))]
  congr 1
  apply dEqR_congr
  intro i h1 h2
  have e := h (queryEq T0 B.length + i) (by omega) (by omega)
  simp only
  split <;> (try split_ifs) <;> rw [e]

theorem all_congr' {l : List ℕ} {p q : ℕ → Bool} (h : ∀ x ∈ l, p x = q x) : l.all p = l.all q := by
  induction l with
  | nil => rfl
  | cons y l ih => simp only [List.all_cons]; rw [h y (by simp), ih (fun x hx => h x (by simp [hx]))]

/-- The consistency test of `V_{RS,>}` (Algorithm 14 step 4) reads `base + 1, …, base + 5`. -/
theorem gt_check_congr (B : List F) (O : F) (r : List Bool) (D' base : ℕ) {a b : ℕ → F}
    (h : ∀ i, 1 ≤ i → i ≤ 2 ^ T0.η + 1 → a (base + i) = b (base + i)) :
    decide (a (base + 1) = ∑ x ∈ Finset.range (2 ^ T0.η), getRandElt B O (r.take B.length) ^ (x * (D' + 1)) *
      a (base + 2 + x)) =
    decide (b (base + 1) = ∑ x ∈ Finset.range (2 ^ T0.η), getRandElt B O (r.take B.length) ^ (x * (D' + 1)) *
      b (base + 2 + x)) := by
  rw [h 1 le_rfl (by simp)]
  congr 2
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [Finset.mem_range] at hx
  have := h (2 + x) (by omega) (by omega)
  rw [show base + 2 + x = base + (2 + x) by omega, this]

/-- `V_{RS,>}` reads `1, …, query`. -/
theorem vGtF_D_congr (B : List F) (O : F) (d : ℕ) (r : List Bool) {a b : ℕ → F}
    (h : AgreeOn (vGtF B O d).query a b) : (vGtF B O d).D r a = (vGtF B O d).D r b := by
  simp only [vGtF] at h ⊢
  have h4 : 2 ^ T0.η = 4 := rfl
  rw [h4] at h
  split_ifs with hd hone
  · rfl
  · simp only [hone, if_true] at h
    rw [gt_check_congr B O r _ _ (fun i h1 h2 => h _ (by omega) (by rw [h4] at h2; omega)),
      all_congr' (fun z hz => dEqR_congr B O r (h.shift (by
        rw [List.mem_range] at hz
        have := Nat.mul_le_mul_right (queryEq T0 B.length) (show z + 1 ≤ mKED B.length T0.η d by omega)
        rw [Nat.add_mul, one_mul] at this; omega))),
      vLtF_D_congr B O _ r (h.shift (by omega))]
  · simp only [hone, if_false, Bool.false_eq_true] at h
    rw [gt_check_congr B O r _ _ (fun i h1 h2 => h _ (by omega) (by rw [h4] at h2; omega)),
      all_congr' (fun z hz => dEqR_congr B O r (h.shift (by
        rw [List.mem_range] at hz
        have := Nat.mul_le_mul_right (queryEq T0 B.length) (show z + 1 ≤ mKED B.length T0.η d by omega)
        rw [Nat.add_mul, one_mul] at this; omega)))]

/-- **`V_RS` reads `1, …, query`.** -/
theorem vRSF_D_congr (B : List F) (O : F) (d : ℕ) (r : List Bool) {a b : ℕ → F}
    (h : AgreeOn (vRSF B O d).query a b) : (vRSF B O d).D r a = (vRSF B O d).D r b := by
  unfold vRSF at h ⊢
  by_cases h1 : B.length ≤ T0.η
  · simp only [h1, if_true] at h ⊢; exact degreeTestF_congr B O d h
  · by_cases h2 : d < dKE B.length T0.η
    · simp only [h1, h2, if_true, if_false] at h ⊢; exact vLtF_D_congr B O d r h
    · by_cases h3 : d = dKE B.length T0.η
      · subst h3; simp only [h1, h2, if_true, if_false] at h ⊢; exact vEqF_D_congr B O r h
      · simp only [h1, h2, h3, if_false] at h ⊢; exact vGtF_D_congr B O d r h

/-- **`V_VRS` reads `1, …, query`.** -/
theorem vVRSF_D_congr (B : List F) (O : F) (BH : List F) (OH : F) (d : ℕ) (r : List Bool) {a b : ℕ → F}
    (h : AgreeOn (vVRSF B O BH OH d).query a b) : (vVRSF B O BH OH d).D r a = (vVRSF B O BH OH d).D r b := by
  simp only [vVRSF] at h ⊢
  rw [vRSF_D_congr B O _ r (h.mono (by omega)), h _ (by omega) (by omega), h _ (by omega) le_rfl]

end NearCubicGates.Adapters.ShortPCP.Time
