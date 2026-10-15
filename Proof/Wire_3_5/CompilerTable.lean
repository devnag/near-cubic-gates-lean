import Proof.Wire_3_5.CompilerExpression
import Proof.Wire_3_5.CompilerPullback
import Proof.Wire_3_5.CompilerPrinter

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Compiler
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.SupplierPrinter

variable {α ZL ZR : Type}

/-! ## Occurrence coefficients and stack sizes -/

/-- The polarized coefficients: `|c·2^{m−t}·(±1)| ≤ C_b·2^m`. -/
theorem polarize_coeff_abs_le (m : ℕ) (V : IntExpression α) (Cb : ℤ) (hc : ∀ t ∈ V, |t.1| ≤ Cb) :
    ∀ w ∈ polarize m V, |w.1| ≤ Cb * 2 ^ m := by
  intro w hw
  simp only [polarize, List.mem_flatMap] at hw
  obtain ⟨t, ht, hw⟩ := hw
  have hCt := hc t ht
  have hCb : 0 ≤ Cb := (abs_nonneg _).trans hCt
  unfold polarizeTerm at hw
  split_ifs at hw with h
  · simp only [List.mem_singleton] at hw
    subst hw
    dsimp only
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℤ) < 2 ^ (m - 1)), mul_comm]
    calc |t.1| * 2 ^ (m - 1) ≤ Cb * 2 ^ (m - 1) := mul_le_mul_of_nonneg_right hCt (by positivity)
      _ ≤ Cb * 2 ^ m := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)) hCb
  · simp only [List.mem_map] at hw
    obtain ⟨J, _, rfl⟩ := hw
    dsimp only
    have hs : |(-(-1 : ℤ) ^ J.length)| = 1 := by simp
    rw [abs_mul, abs_mul, hs, mul_one, abs_of_pos (by positivity : (0 : ℤ) < 2 ^ (m - t.2.length))]
    calc |t.1| * 2 ^ (m - t.2.length) ≤ Cb * 2 ^ (m - t.2.length) :=
          mul_le_mul_of_nonneg_right hCt (by positivity)
      _ ≤ Cb * 2 ^ m := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)) hCb

/-- An occurrence of a lifted polynomial: `(w(−2)^j, stack of ⋃J)` with `|J| = j+1 ≤ Q` supports of `P`. -/
theorem liftOccurrences_mem (eqs : ℕ → SeparatedEquation ZL ZR) (H : ℤ) (Q : ℕ) (w : ℤ) (P : ChildPoly)
    (o : ℤ × SeparatedEquation ZL ZR) (ho : o ∈ liftOccurrences eqs H Q w P) :
    ∃ j < Q, ∃ J : List (Finset ℕ), J.length = j + 1 ∧ (∀ S ∈ J, S ∈ P) ∧
      o = (w * (-2) ^ j, conjEquation eqs H (supportUnion J)) := by
  unfold liftOccurrences at ho
  simp only [List.mem_flatMap, List.mem_range, List.mem_map, List.mem_sublistsLen] at ho
  obtain ⟨j, hj, J, ⟨hsub, hlen⟩, rfl⟩ := ho
  exact ⟨j, hj, J, hlen, fun S hS => (mem_listSupports P S).mp (hsub.subset hS), rfl⟩

theorem compileExpression_coeff_abs_le (children : α → List ℕ) (eqs : ℕ → SeparatedEquation ZL ZR) (H : ℤ)
    (m Q : ℕ) (V : IntExpression α) (Cb : ℤ) (hc : ∀ t ∈ V, |t.1| ≤ Cb) :
    ∀ o ∈ compileExpression children eqs H m Q V, |o.1| ≤ Cb * 2 ^ m * 2 ^ Q := by
  intro o ho
  unfold compileExpression at ho
  rw [List.mem_flatMap] at ho
  obtain ⟨w, hw, ho⟩ := ho
  obtain ⟨j, hj, J, _, _, rfl⟩ := liftOccurrences_mem eqs H Q w.1 _ o ho
  have hw' := polarize_coeff_abs_le m V Cb hc w hw
  dsimp only
  rw [abs_mul, abs_pow, abs_neg, abs_two]
  calc |w.1| * 2 ^ j ≤ (Cb * 2 ^ m) * 2 ^ j := mul_le_mul_of_nonneg_right hw' (by positivity)
    _ ≤ Cb * 2 ^ m * 2 ^ Q :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hj.le) ((abs_nonneg _).trans hw')

theorem polarize_pool_hyps (children : α → List ℕ) (m d : ℕ) (V : IntExpression α) (pool : Finset ℕ)
    (hpool : ∀ t ∈ V, ∀ p ∈ t.2, ∀ mono ∈ p, ∀ a ∈ mono, ∀ c ∈ children a, c ∈ pool)
    (hd : ∀ t ∈ V, ∀ p ∈ t.2, ∀ mono ∈ p, mono.length ≤ d) (w : ℤ × F2Poly α) (hw : w ∈ polarize m V) :
    (∀ mono ∈ w.2, ∀ a ∈ mono, ∀ c ∈ children a, c ∈ pool) ∧ (∀ mono ∈ w.2, mono.length ≤ d) := by
  constructor
  · intro mono hmono a ha c hc
    rcases polarize_mono_mem m V w hw mono hmono with h | ⟨t, ht, p, hp, hm⟩
    · subst h; simp at ha
    · exact hpool t ht p hp mono hm a ha c hc
  · intro mono hmono
    rcases polarize_mono_mem m V w hw mono hmono with h | ⟨t, ht, p, hp, hm⟩
    · subst h; simp
    · exact hd t ht p hp mono hm

theorem compileExpression_stack (children : α → List ℕ) (eqs : ℕ → SeparatedEquation ZL ZR) (H : ℤ) (m Q d : ℕ)
    (V : IntExpression α) (pool : Finset ℕ)
    (hpool : ∀ t ∈ V, ∀ p ∈ t.2, ∀ mono ∈ p, ∀ a ∈ mono, ∀ c ∈ children a, c ∈ pool)
    (hd : ∀ t ∈ V, ∀ p ∈ t.2, ∀ mono ∈ p, mono.length ≤ d) :
    ∀ o ∈ compileExpression children eqs H m Q V,
      ∃ U : Finset ℕ, o.2 = conjEquation eqs H U ∧ U.card ≤ Q * d ∧ U ⊆ pool := by
  intro o ho
  unfold compileExpression at ho
  rw [List.mem_flatMap] at ho
  obtain ⟨w, hw, ho⟩ := ho
  obtain ⟨j, hj, J, hlen, hJ, rfl⟩ := liftOccurrences_mem eqs H Q w.1 _ o ho
  obtain ⟨hp, hdw⟩ := polarize_pool_hyps children m d V pool hpool hd w hw
  have hsub := substitute_subset children w.2 pool d hp hdw
  refine ⟨supportUnion J, rfl, ?_, ?_⟩
  · calc (supportUnion J).card ≤ J.length * d :=
          supportUnion_card_le J d (fun S hS => (Finset.mem_filter.mp (hsub (hJ S hS))).2)
      _ ≤ Q * d := Nat.mul_le_mul_right _ (by omega)
  · intro c hc
    obtain ⟨S, hS, hcS⟩ := (mem_supportUnion J c).mp hc
    exact Finset.mem_powerset.mp (Finset.mem_filter.mp (hsub (hJ S hS))).1 hcS

/-! ## Recovery of the table -/

def recoverTable (m Q : ℕ) (r : ℤ) : ℤ := recoverColumn Q r / 2 ^ (m - 1)

theorem compileExpression_table (children : α → List ℕ) (eqs : ℕ → SeparatedEquation ZL ZR) (H Vb : ℤ)
    (hH : Vb < H) (m Q : ℕ) (hm : 1 ≤ m) (V : IntExpression α) (hVm : ∀ t ∈ V, t.2.length ≤ m) (zl : ZL) (zr : ZR)
    (hV : ∀ c, |eqValue (eqs c) zl zr| ≤ Vb) (ρ : α → Bool)
    (hexact : ExactChildren children (fun c => (eqs c).holds zl zr) ρ) (J : ℤ)
    (h0 : 0 ≤ IntExpression.eval V ρ) (hJ : IntExpression.eval V ρ ≤ J) (hQ : 2 ^ (m - 1) * J < 2 ^ Q) :
    recoverTable m Q (SignedOccurrenceList.value (compileExpression children eqs H m Q V) zl zr) =
      IntExpression.eval V ρ := by
  unfold recoverTable
  rw [compileExpression_recover children eqs H Vb hH m Q hm V hVm zl zr hV ρ hexact J h0 hJ hQ]
  exact Int.mul_ediv_cancel_left _ (by positivity)

/-! ## The pool of pulled-back threshold atoms -/

structure PulledAtom (n : ℕ) (ZL ZR : Type) where
  coords : HalfCoords n ZL ZR
  gate : NormalizedThresholdGate n
  dec : ExactDecomposition gate

/-- The atom's value at the column `(z_L, z_R)`. -/
def PulledAtom.bit {n : ℕ} (a : PulledAtom n ZL ZR) (zl : ZL) (zr : ZR) : Bool :=
  a.gate.strictEval (a.coords.point zl zr)

/-- The pulled-back children of every atom, in pool order. -/
def poolChildren {n : ℕ} (pool : List (PulledAtom n ZL ZR)) : List (List (SeparatedEquation ZL ZR)) :=
  pool.map fun a => pullbackChildren a.coords a.dec

/-- The atom values at a column, indexed by pool position. -/
def poolBits {n : ℕ} (pool : List (PulledAtom n ZL ZR)) (zl : ZL) (zr : ZR) : ℕ → Bool :=
  fun i => (pool.map fun a => a.bit zl zr).getD i false

def poolSize {n : ℕ} (pool : List (PulledAtom n ZL ZR)) : ℕ := (poolChildren pool).flatten.length

/-- The trivial equation `0 = 0` (the default label). -/
def zeroEquation : SeparatedEquation ZL ZR := ⟨fun _ => 0, fun _ => 0⟩

def compilePool {n : ℕ} (pool : List (PulledAtom n ZL ZR)) (H : ℤ) (m Q : ℕ) (V : IntExpression ℕ) :
    SignedOccurrenceList ZL ZR :=
  compileExpression (labelChildren (poolChildren pool)) (labelEqs (poolChildren pool) zeroEquation) H m Q V

theorem poolBits_exact {n : ℕ} (pool : List (PulledAtom n ZL ZR)) (zl : ZL) (zr : ZR) :
    ExactChildren (labelChildren (poolChildren pool))
      (fun c => (labelEqs (poolChildren pool) zeroEquation c).holds zl zr) (poolBits pool zl zr) := by
  apply labelChildren_exact
  intro i
  unfold poolBits poolChildren
  by_cases hi : i < pool.length
  · rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getD_eq_getElem _ _ (by simpa using hi)]
    simp only [List.getElem_map]
    exact pullback_exact _ _ zl zr
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    simp [bitZ]

theorem pullChild_value {n : ℕ} (C : HalfCoords n ZL ZR) (e : ExactThresholdGate n) (zl : ZL) (zr : ZR) :
    eqValue (pullChild C e) zl zr = -e.target + ∑ i, e.weight i * bitZ (C.point zl zr i) := by
  unfold eqValue pullChild HalfCoords.point
  dsimp only
  rw [add_assoc, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : C.side i <;> simp [h]

/-- A pulled-back child's value envelope: `|E(z)| ≤ |target| + Σ|weight|`. -/
theorem pullChild_abs_le {n : ℕ} (C : HalfCoords n ZL ZR) (e : ExactThresholdGate n) (zl : ZL) (zr : ZR) :
    |eqValue (pullChild C e) zl zr| ≤ |e.target| + ∑ i, |e.weight i| := by
  rw [pullChild_value]
  refine (abs_add_le _ _).trans ?_
  rw [abs_neg]
  refine add_le_add (le_refl _) ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_))
  rw [abs_mul]
  cases C.point zl zr i <;> simp [bitZ]

/-- **The child-value envelope** `V` of `alg:stack` for the pooled children (and the default label). -/
theorem poolEqs_abs_le {n : ℕ} (pool : List (PulledAtom n ZL ZR)) (Vb : ℤ) (hVb0 : 0 ≤ Vb)
    (hVb : ∀ a ∈ pool, ∀ e ∈ a.dec.children, |e.target| + ∑ i, |e.weight i| ≤ Vb) (zl : ZL) (zr : ZR) (c : ℕ) :
    |eqValue (labelEqs (poolChildren pool) zeroEquation c) zl zr| ≤ Vb := by
  unfold labelEqs
  by_cases hc : c < (poolChildren pool).flatten.length
  · rw [List.getD_eq_getElem _ _ hc]
    have hmem := List.getElem_mem hc
    rw [List.mem_flatten] at hmem
    obtain ⟨L, hL, hE⟩ := hmem
    unfold poolChildren at hL
    rw [List.mem_map] at hL
    obtain ⟨a, ha, rfl⟩ := hL
    unfold pullbackChildren at hE
    rw [List.mem_map] at hE
    obtain ⟨e, he, hEe⟩ := hE
    rw [← hEe]
    exact (pullChild_abs_le _ _ zl zr).trans (hVb a ha e he)
  · rw [List.getD_eq_default _ _ (by omega)]
    simp [eqValue, zeroEquation, hVb0]

theorem labelOffset_succ_cons (A : List (SeparatedEquation ZL ZR)) (L : List (List (SeparatedEquation ZL ZR)))
    (i : ℕ) : labelOffset (A :: L) (i + 1) = A.length + labelOffset L i := by
  simp [labelOffset]

theorem labelOffset_add_le (L : List (List (SeparatedEquation ZL ZR))) (i : ℕ) :
    labelOffset L i + (L.getD i []).length ≤ L.flatten.length := by
  induction L generalizing i with
  | nil => simp [labelOffset]
  | cons A L ih =>
    cases i with
    | zero => simp [labelOffset]
    | succ i =>
      have := ih i
      rw [labelOffset_succ_cons, List.getD_cons_succ, List.flatten_cons, List.length_append]
      omega

/-- Every child label lies in the equation pool `[0, P_ex)`. -/
theorem labelChildren_mem (L : List (List (SeparatedEquation ZL ZR))) (i c : ℕ) (hc : c ∈ labelChildren L i) :
    c ∈ Finset.range L.flatten.length := by
  unfold labelChildren at hc
  rw [List.mem_range'_1] at hc
  have := labelOffset_add_le L i
  rw [Finset.mem_range]
  omega

theorem compilePool_length_le {n : ℕ} (pool : List (PulledAtom n ZL ZR)) (H : ℤ) (m Q d : ℕ) (V : IntExpression ℕ)
    (hVm : ∀ t ∈ V, t.2.length ≤ m) (hd : ∀ t ∈ V, ∀ p ∈ t.2, ∀ mono ∈ p, mono.length ≤ d) :
    (compilePool pool H m Q V).length ≤ V.length * 2 ^ m * (Q * (poolSize pool + 1) ^ (Q * d)) := by
  have := compileExpression_length_le (labelChildren (poolChildren pool)) (labelEqs (poolChildren pool) zeroEquation)
    H m Q d V (Finset.range (poolSize pool)) hVm
    (fun _ _ _ _ _ _ a _ c hc => labelChildren_mem _ a c hc) hd
  rw [Finset.card_range] at this
  exact this

/-- **`alg:eq-budget` in exponent form**: `A ≤ 2^a`, `Q' ≤ 2^q`, `P_ex+1 ≤ 2^p` and `a+m+q+Q'd·p ≤ B` give
`A·2^m·Q'·(P_ex+1)^{Q'd} ≤ 2^B`. -/
theorem occurrences_le_budget (A m Q P d a q p B : ℕ) (hA : A ≤ 2 ^ a) (hQ : Q ≤ 2 ^ q) (hP : P + 1 ≤ 2 ^ p)
    (hB : a + m + q + Q * d * p ≤ B) : A * 2 ^ m * (Q * (P + 1) ^ (Q * d)) ≤ 2 ^ B := by
  calc A * 2 ^ m * (Q * (P + 1) ^ (Q * d)) ≤ 2 ^ a * 2 ^ m * (2 ^ q * (2 ^ p) ^ (Q * d)) := by gcongr
    _ = 2 ^ (a + m + q + Q * d * p) := by
        rw [← pow_mul]; simp only [← pow_add]; congr 1; ring
    _ ≤ 2 ^ B := Nat.pow_le_pow_right (by norm_num) hB

theorem compilePool_budget {n : ℕ} (pool : List (PulledAtom n ZL ZR)) (H : ℤ) (m Q d : ℕ) (V : IntExpression ℕ)
    (hVm : ∀ t ∈ V, t.2.length ≤ m) (hd : ∀ t ∈ V, ∀ p ∈ t.2, ∀ mono ∈ p, mono.length ≤ d) (a q p B : ℕ)
    (hA : V.length ≤ 2 ^ a) (hQ : Q ≤ 2 ^ q) (hP : poolSize pool + 1 ≤ 2 ^ p) (hB : a + m + q + Q * d * p ≤ B) :
    (compilePool pool H m Q V).length ≤ 2 ^ B :=
  (compilePool_length_le pool H m Q d V hVm hd).trans (occurrences_le_budget _ m Q _ d a q p B hA hQ hP hB)

theorem compilePool_table {n R C : ℕ} (pool : List (PulledAtom n ZL ZR)) (H Vb : ℤ) (hH : Vb < H) (hVb0 : 0 ≤ Vb)
    (hVb : ∀ a ∈ pool, ∀ e ∈ a.dec.children, |e.target| + ∑ i, |e.weight i| ≤ Vb)
    (m Q : ℕ) (hm : 1 ≤ m) (V : IntExpression ℕ) (hVm : ∀ t ∈ V, t.2.length ≤ m) (J : ℤ)
    (hQ : 2 ^ (m - 1) * J < 2 ^ Q) (rowOf : Fin R → ZL) (colOf : Fin C → ZR) (r : Fin R) (c : Fin C)
    (h0 : 0 ≤ IntExpression.eval V (poolBits pool (rowOf r) (colOf c)))
    (hJ : IntExpression.eval V (poolBits pool (rowOf r) (colOf c)) ≤ J) :
    recoverTable m Q
        (weightedDominance (cutLeft (compilePool pool H m Q V) rowOf) (cutRight (compilePool pool H m Q V) colOf)
          (cutWeight (compilePool pool H m Q V)) r c) =
      IntExpression.eval V (poolBits pool (rowOf r) (colOf c)) := by
  rw [← value_eq_weightedDominance]
  exact compileExpression_table _ _ H Vb hH m Q hm V hVm (rowOf r) (colOf c)
    (poolEqs_abs_le pool Vb hVb0 hVb (rowOf r) (colOf c)) _ (poolBits_exact pool (rowOf r) (colOf c)) J h0 hJ hQ

end NearCubicWires.WireExponent3_5.Compiler
