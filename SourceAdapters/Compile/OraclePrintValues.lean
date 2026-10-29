import SourceAdapters.Compile.OraclePrintCompile

/-!
# A static value bound for templates

proof of `thm:short-pcp-ours`: the printer runs in polynomial time, so every number it computes must fit a register whose width is
polynomial in the request. For a template `u` (fixed once the oracle program is fixed) this module gives a static
exponent `U.vx E u`: when every bound number is at most `X ^ E` (with `X` at least the template's largest constant
plus two and `1 ≤ E`), every number evaluated during the run of `u` is at most `X ^ U.vx E u`
(**`U.okV_of_pow`**). The numbers bound inside the template (loop indices, local bindings) are covered by the
exponent, so the vector loop's side condition `U.okV` holds for every request with a polynomial `V`.
-/

namespace NearCubicGates.Adapters.Compile.OraclePrint

set_option autoImplicit false

/-- Largest constant of a template. -/
def U.kmax : U → ℕ
  | .cst c | .dat c | .inp c => c.kmax
  | .not u => u.kmax
  | .and u v | .or u v => max u.kmax v.kmax
  | .bigAnd n b f | .bigOr n b f => max n.kmax (max b.kmax f.kmax)
  | .ite c u v => max c.kmax (max u.kmax v.kmax)
  | .lett t b => max t.kmax b.kmax

/-- The value exponent of a template when the bound numbers are at most `X ^ E`. -/
def U.vx : ℕ → U → ℕ
  | E, .cst c | E, .dat c | E, .inp c => (E + 1) * c.sz
  | E, .not u => U.vx E u
  | E, .and u v | E, .or u v => max (U.vx E u) (U.vx E v)
  | E, .bigAnd n b f | E, .bigOr n b f =>
      max ((E + 1) * n.sz) (max (U.vx (max E ((E + 1) * n.sz)) b) (U.vx (max E ((E + 1) * n.sz)) f))
  | E, .ite c u v => max ((E + 1) * c.sz) (max (U.vx E u) (U.vx E v))
  | E, .lett t b => max ((E + 1) * t.sz) (U.vx (max E ((E + 1) * t.sz)) b)

theorem pow_step {X K E : ℕ} (hX : K + 2 ≤ X) (hE : 1 ≤ E) : X ^ E + K + 2 ≤ X ^ (E + 1) := by
  have h1 : X ≤ X ^ E := by
    calc X = X ^ 1 := (pow_one X).symm
      _ ≤ X ^ E := Nat.pow_le_pow_right (by omega) hE
  rw [pow_succ]
  nlinarith

/-- Term level: bound numbers at most `X ^ E` give values at most `X ^ ((E + 1) · sz)`. -/
theorem Tm.okV_pow (env : List ℕ) (X K E : ℕ) (hX : K + 2 ≤ X) (hE : 1 ≤ E) (hM : ∀ j, env.getD j 0 ≤ X ^ E)
    (t : Tm) (hk : t.kmax ≤ K) (V : ℕ) (hV : X ^ ((E + 1) * t.sz) ≤ V) :
    t.okV V env ∧ t.eval env ≤ X ^ ((E + 1) * t.sz) := by
  have hb : (X ^ E + K + 2) ^ t.sz ≤ X ^ ((E + 1) * t.sz) := by
    rw [pow_mul]; exact Nat.pow_le_pow_left (pow_step hX hE) _
  exact ⟨Tm.okV_of_le env (X ^ E) K hM t V hk (hb.trans hV), (Tm.eval_le_pow env (X ^ E) K hM t hk).trans hb⟩

theorem getD_snoc_le (env : List ℕ) (x B : ℕ) (h : ∀ j, env.getD j 0 ≤ B) (hx : x ≤ B) :
    ∀ j, (env ++ [x]).getD j 0 ≤ B := by
  intro j
  rw [getD_snoc]
  split_ifs
  · exact h j
  · exact hx
  · exact Nat.zero_le _

theorem pow_le_pow_of {X a b : ℕ} (hX : 2 ≤ X) (h : a ≤ b) : X ^ a ≤ X ^ b := Nat.pow_le_pow_right (by omega) h

/-- **The static value bound of a template.** -/
theorem U.okV_of_pow (D : List Bool) (X K : ℕ) (hX : K + 2 ≤ X) (u : U) (hk : u.kmax ≤ K) :
    ∀ (E : ℕ) (env : List ℕ), 1 ≤ E → (∀ j, env.getD j 0 ≤ X ^ E) → ∀ V, X ^ (U.vx E u) ≤ V → u.okV V D env := by
  have hX2 : 2 ≤ X := by omega
  induction u with
  | cst c =>
      intro E env hE hM V hV
      exact (Tm.okV_pow env X K E hX hE hM c hk V hV).1
  | dat c =>
      intro E env hE hM V hV
      exact (Tm.okV_pow env X K E hX hE hM c hk V hV).1
  | inp c =>
      intro E env hE hM V hV
      exact (Tm.okV_pow env X K E hX hE hM c hk V hV).1
  | not u ih =>
      intro E env hE hM V hV
      exact ih hk E env hE hM V hV
  | and u v ihu ihv =>
      intro E env hE hM V hV
      simp only [U.kmax, max_le_iff] at hk
      simp only [U.vx] at hV
      exact ⟨ihu hk.1 E env hE hM V ((pow_le_pow_of hX2 (le_max_left _ _)).trans hV),
        ihv hk.2 E env hE hM V ((pow_le_pow_of hX2 (le_max_right _ _)).trans hV)⟩
  | or u v ihu ihv =>
      intro E env hE hM V hV
      simp only [U.kmax, max_le_iff] at hk
      simp only [U.vx] at hV
      exact ⟨ihu hk.1 E env hE hM V ((pow_le_pow_of hX2 (le_max_left _ _)).trans hV),
        ihv hk.2 E env hE hM V ((pow_le_pow_of hX2 (le_max_right _ _)).trans hV)⟩
  | bigAnd n b f ihb ihf =>
      intro E env hE hM V hV
      simp only [U.kmax, max_le_iff] at hk
      simp only [U.vx] at hV
      set E' := max E ((E + 1) * n.sz)
      obtain ⟨hn, he⟩ := Tm.okV_pow env X K E hX hE hM n hk.1 V
        ((pow_le_pow_of hX2 (le_max_left _ _)).trans hV)
      have hE' : 1 ≤ E' := le_max_of_le_left hE
      have hM' : ∀ x, x ≤ n.eval env → ∀ j, (env ++ [x]).getD j 0 ≤ X ^ E' := fun x hx =>
        getD_snoc_le env x _ (fun j => (hM j).trans (pow_le_pow_of hX2 (le_max_left _ _)))
          (hx.trans (he.trans (pow_le_pow_of hX2 (le_max_right _ _))))
      refine ⟨hn, fun i hi => ihb hk.2.1 E' (env ++ [i]) hE' (hM' i hi.le) V
        ((pow_le_pow_of hX2 (le_max_of_le_right (le_max_left _ _))).trans hV),
        ihf hk.2.2 E' (env ++ [n.eval env]) hE' (hM' _ le_rfl) V
        ((pow_le_pow_of hX2 (le_max_of_le_right (le_max_right _ _))).trans hV)⟩
  | bigOr n b f ihb ihf =>
      intro E env hE hM V hV
      simp only [U.kmax, max_le_iff] at hk
      simp only [U.vx] at hV
      set E' := max E ((E + 1) * n.sz)
      obtain ⟨hn, he⟩ := Tm.okV_pow env X K E hX hE hM n hk.1 V
        ((pow_le_pow_of hX2 (le_max_left _ _)).trans hV)
      have hE' : 1 ≤ E' := le_max_of_le_left hE
      have hM' : ∀ x, x ≤ n.eval env → ∀ j, (env ++ [x]).getD j 0 ≤ X ^ E' := fun x hx =>
        getD_snoc_le env x _ (fun j => (hM j).trans (pow_le_pow_of hX2 (le_max_left _ _)))
          (hx.trans (he.trans (pow_le_pow_of hX2 (le_max_right _ _))))
      refine ⟨hn, fun i hi => ihb hk.2.1 E' (env ++ [i]) hE' (hM' i hi.le) V
        ((pow_le_pow_of hX2 (le_max_of_le_right (le_max_left _ _))).trans hV),
        ihf hk.2.2 E' (env ++ [n.eval env]) hE' (hM' _ le_rfl) V
        ((pow_le_pow_of hX2 (le_max_of_le_right (le_max_right _ _))).trans hV)⟩
  | ite c u v ihu ihv =>
      intro E env hE hM V hV
      simp only [U.kmax, max_le_iff] at hk
      simp only [U.vx] at hV
      exact ⟨(Tm.okV_pow env X K E hX hE hM c hk.1 V ((pow_le_pow_of hX2 (le_max_left _ _)).trans hV)).1,
        ihu hk.2.1 E env hE hM V ((pow_le_pow_of hX2 (le_max_of_le_right (le_max_left _ _))).trans hV),
        ihv hk.2.2 E env hE hM V ((pow_le_pow_of hX2 (le_max_of_le_right (le_max_right _ _))).trans hV)⟩
  | lett t b ih =>
      intro E env hE hM V hV
      simp only [U.kmax, max_le_iff] at hk
      simp only [U.vx] at hV
      set E' := max E ((E + 1) * t.sz)
      obtain ⟨ht, he⟩ := Tm.okV_pow env X K E hX hE hM t hk.1 V
        ((pow_le_pow_of hX2 (le_max_left _ _)).trans hV)
      have hE' : 1 ≤ E' := le_max_of_le_left hE
      refine ⟨ht, ih hk.2 E' (env ++ [t.eval env]) hE' (getD_snoc_le env _ _
        (fun j => (hM j).trans (pow_le_pow_of hX2 (le_max_left _ _)))
        (he.trans (pow_le_pow_of hX2 (le_max_right _ _)))) V
        ((pow_le_pow_of hX2 (le_max_right _ _)).trans hV)⟩

end NearCubicGates.Adapters.Compile.OraclePrint
