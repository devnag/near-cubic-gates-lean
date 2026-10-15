import Proof.Gates.Dispatch.Macros

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxRecDepth 4000

namespace NearCubicGates.Close.Dispatch

variable {C : Ctx}

/-- Expression stack variables `200 …`. -/
def tv (d : ℕ) : Fin VV := ⟨200 + d % 50, by have := Nat.mod_lt d (show 50 > 0 by norm_num); show _ < 256; omega⟩

theorem tv_val (d : ℕ) (hd : d < 50) : (tv d).val = 200 + d := by simp [tv, Nat.mod_eq_of_lt hd]

theorem tv_ne {d d' : ℕ} (hd : d < 50) (hd' : d' < 50) (h : d ≠ d') : tv d ≠ tv d' := by
  intro e; have := congrArg Fin.val e; rw [tv_val d hd, tv_val d' hd'] at this; omega

/-- Expressions. Variables must be below `200` (outside the stack). -/
inductive AE where
  | var (x : Fin VV)
  | lit (k : ℕ)
  | add (e f : AE)
  | sub (e f : AE)
  | mul (e f : AE)
  | div (e f : AE)
  | mod (e f : AE)

namespace AE

def eval (env : Fin VV → ℕ) : AE → ℕ
  | var x => env x
  | lit k => k
  | add e f => e.eval env + f.eval env
  | sub e f => e.eval env - f.eval env
  | mul e f => e.eval env * f.eval env
  | div e f => e.eval env / f.eval env
  | mod e f => e.eval env % f.eval env

/-- Stack slots used beyond the target slot. -/
def depth : AE → ℕ
  | var _ => 0
  | lit _ => 0
  | add e f => max e.depth (f.depth + 1)
  | sub e f => max e.depth (f.depth + 1)
  | mul e f => max (e.depth + 1) (f.depth + 2)
  | div e f => max (e.depth + 1) (max (f.depth + 2) 3)
  | mod e f => max (e.depth + 1) (max (f.depth + 2) 3)

/-- Every variable is outside the stack. -/
def vars_ok : AE → Prop
  | var x => x.val < 200 ∧ x ≠ vJ
  | lit _ => True
  | add e f => e.vars_ok ∧ f.vars_ok
  | sub e f => e.vars_ok ∧ f.vars_ok
  | mul e f => e.vars_ok ∧ f.vars_ok
  | div e f => e.vars_ok ∧ f.vars_ok
  | mod e f => e.vars_ok ∧ f.vars_ok

/-- No overflow of width `W`, positive divisors. -/
def ok (W : ℕ) (env : Fin VV → ℕ) : AE → Prop
  | var _ => True
  | lit k => k < 2 ^ W
  | add e f => e.ok W env ∧ f.ok W env ∧ e.eval env + f.eval env < 2 ^ W
  | sub e f => e.ok W env ∧ f.ok W env
  | mul e f => e.ok W env ∧ f.ok W env ∧ e.eval env * f.eval env < 2 ^ W
  | div e f => e.ok W env ∧ f.ok W env ∧ 0 < f.eval env ∧ 2 * f.eval env ≤ 2 ^ W
  | mod e f => e.ok W env ∧ f.ok W env ∧ 0 < f.eval env ∧ 2 * f.eval env ≤ 2 ^ W

def cost : AE → ℕ
  | var _ => 1
  | lit k => 2 * k + 3
  | add e f => e.cost + f.cost + 3
  | sub e f => e.cost + f.cost + 5
  | mul e f => e.cost + f.cost + 3
  | div e f => e.cost + f.cost + 3
  | mod e f => e.cost + f.cost + 3

end AE

/-- Evaluate `e` into `tv d`. -/
def cE : AE → ℕ → St VV
  | .var x, d => .op (.copy (tv d) x)
  | .lit k, d => setK (tv d) k
  | .add e f, d => .seq (cE e d) (.seq (cE f (d + 1)) (.op (.add (tv d) (tv (d + 1)))))
  | .sub e f, d => .seq (cE e d) (.seq (cE f (d + 1))
      (.ite (.lt (tv d) (tv (d + 1))) (.op (.zero (tv d))) (.op (.sub (tv d) (tv (d + 1))))))
  | .mul e f, d => .seq (cE e (d + 1)) (.seq (cE f (d + 2)) (.op (.mul (tv (d + 1)) (tv (d + 2)) (tv d))))
  | .div e f, d => .seq (cE e (d + 1)) (.seq (cE f (d + 2)) (.op (.dm (tv (d + 1)) (tv (d + 2)) (tv d) (tv (d + 3)))))
  | .mod e f, d => .seq (cE e (d + 1)) (.seq (cE f (d + 2)) (.op (.dm (tv (d + 1)) (tv (d + 2)) (tv (d + 3)) (tv d))))

/-- The frame of `cE e d`: stack slots `≥ d` and the junk variable. -/
def StackFr (a b : DS VV) (d : ℕ) : Prop := ∀ y : Fin VV, y.val < 200 + d → y ≠ vJ → b.env y = a.env y

theorem StackFr.refl (a : DS VV) (d : ℕ) : StackFr a a d := fun _ _ _ => rfl
theorem StackFr.trans {a b c : DS VV} {d : ℕ} (h1 : StackFr a b d) (h2 : StackFr b c d) : StackFr a c d :=
  fun y hy hj => (h2 y hy hj).trans (h1 y hy hj)
theorem StackFr.mono {a b : DS VV} {d d' : ℕ} (h : StackFr a b d') (hd : d ≤ d') : StackFr a b d :=
  fun y hy hj => h y (by omega) hj
theorem StackFr.set (a : DS VV) {x : Fin VV} (v : ℕ) {d : ℕ} (hx : 200 + d ≤ x.val ∨ x = vJ) : StackFr a (a.set x v) d := by
  intro y hy hj
  have : y ≠ x := by
    rintro rfl; rcases hx with h | h
    · omega
    · exact hj h
  exact DS.set_env_ne a v this

theorem tv_ge (d : ℕ) (hd : d < 50) : 200 + d ≤ (tv d).val := by rw [tv_val d hd]

theorem Cst.of_stack {a b : DS VV} {d : ℕ} (hc : Cst a) (h : StackFr a b d) (hp : b.env vPOS = b.cp) : Cst b :=
  ⟨by rw [h vZ (Nat.lt_of_lt_of_le (by decide : vZ.val < 200) (by omega)) (by decide)]; exact hc.z,
    by rw [h v1 (Nat.lt_of_lt_of_le (by decide : v1.val < 200) (by omega)) (by decide)]; exact hc.one,
    by rw [h v2 (Nat.lt_of_lt_of_le (by decide : v2.val < 200) (by omega)) (by decide)]; exact hc.two, hp⟩

theorem eval_congr (e : AE) (hv : e.vars_ok) (a b : DS VV) (d : ℕ) (h : StackFr a b d) :
    e.eval b.env = e.eval a.env := by
  induction e with
  | var x => exact h x (by simp only [AE.vars_ok] at hv; omega) hv.2
  | lit k => rfl
  | add e f ihe ihf => simp only [AE.eval]; rw [ihe hv.1, ihf hv.2]
  | sub e f ihe ihf => simp only [AE.eval]; rw [ihe hv.1, ihf hv.2]
  | mul e f ihe ihf => simp only [AE.eval]; rw [ihe hv.1, ihf hv.2]
  | div e f ihe ihf => simp only [AE.eval]; rw [ihe hv.1, ihf hv.2]
  | mod e f ihe ihf => simp only [AE.eval]; rw [ihe hv.1, ihf hv.2]

theorem ok_congr (W : ℕ) (e : AE) (hv : e.vars_ok) (a b : DS VV) (d : ℕ) (h : StackFr a b d) :
    e.ok W b.env ↔ e.ok W a.env := by
  induction e with
  | var x => exact Iff.rfl
  | lit k => exact Iff.rfl
  | add e f ihe ihf =>
    simp only [AE.ok]; rw [ihe hv.1, ihf hv.2, eval_congr e hv.1 a b d h, eval_congr f hv.2 a b d h]
  | sub e f ihe ihf => simp only [AE.ok]; rw [ihe hv.1, ihf hv.2]
  | mul e f ihe ihf =>
    simp only [AE.ok]; rw [ihe hv.1, ihf hv.2, eval_congr e hv.1 a b d h, eval_congr f hv.2 a b d h]
  | div e f ihe ihf =>
    simp only [AE.ok]; rw [ihe hv.1, ihf hv.2, eval_congr f hv.2 a b d h]
  | mod e f ihe ihf =>
    simp only [AE.ok]; rw [ihe hv.1, ihf hv.2, eval_congr f hv.2 a b d h]

theorem tv_ne_vJ (d : ℕ) (hd : d < 50) : tv d ≠ vJ := by
  intro e; have := congrArg Fin.val e; rw [tv_val d hd] at this; have : (vJ).val = 3 := rfl; omega

theorem tv_ne_vPOS (d : ℕ) (hd : d < 50) : vPOS ≠ tv d := by
  intro e; have := congrArg Fin.val e; rw [tv_val d hd] at this; have : (vPOS).val = 4 := rfl; omega

/-- Setting a stack slot keeps the constants. -/
theorem Cst.set_tv {a : DS VV} (hc : Cst a) (d : ℕ) (hd : d < 50) (v : ℕ) : Cst (a.set (tv d) v) :=
  Cst.of_stack hc (StackFr.set a v (Or.inl (tv_ge d hd))) (by rw [DS.set_env_ne _ _ (tv_ne_vPOS d hd)]; exact hc.pos)

/-- **The evaluator.** -/
theorem cE_spec (e : AE) : ∀ (d : ℕ) (a : DS VV), e.vars_ok → d + e.depth + 1 < 50 → Cst a → e.ok C.Wd a.env →
    Hs C (cE e d) a e.cost (fun b => b.env (tv d) = e.eval a.env ∧ StackFr a b d ∧ b.cp = a.cp ∧ b.wq = a.wq ∧
      b.out = a.out ∧ Cst b) := by
  induction e with
  | var x =>
    intro d a hv hd hc _
    have hdd : d < 50 := by simp [AE.depth] at hd; omega
    refine Hs.mono (hs_copy C (tv d) x a ?_) le_rfl ?_
    · intro e; have := congrArg Fin.val e; rw [tv_val d hdd] at this
      simp only [AE.vars_ok] at hv; omega
    · rintro b rfl
      exact ⟨by simp [AE.eval], StackFr.set a _ (Or.inl (tv_ge d hdd)), rfl, rfl, rfl, hc.set_tv d hdd _⟩
  | lit k =>
    intro d a _ hd hc hok
    have hdd : d < 50 := by simp [AE.depth] at hd; omega
    refine Hs.mono (setK_spec (tv d) (tv_ne_vJ d hdd) k a hok) le_rfl ?_
    rintro b ⟨b1, b2, b3, b4, b5⟩
    have hS : StackFr a b d := by
      intro y hy hj
      refine b5 y ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨by intro e; subst e; rw [tv_val d hdd] at hy; omega, hj⟩
    exact ⟨by simp [AE.eval, b1], hS, b2, b3, b4, Cst.of_stack hc hS (by
      rw [b5 vPOS (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
                      exact ⟨tv_ne_vPOS d hdd, by decide⟩), b2]
      exact hc.pos)⟩
  | add e f ihe ihf =>
    intro d a hv hd hc hok
    obtain ⟨ok1, ok2, ok3⟩ := hok
    simp only [AE.depth] at hd
    have hdd : d + 1 < 50 := by omega
    refine Hx.hs (Hs.then (ihe d a hv.1 (by omega) hc ok1) (fun b ⟨b1, b2, b3, b4, b5, b6⟩ n1 hn1 => ?_))
    have hf : f.eval b.env = f.eval a.env := eval_congr f hv.2 a b d b2
    refine Hs.then (ihf (d + 1) b hv.2 (by omega) b6 ((ok_congr _ f hv.2 a b d b2).2 ok2))
      (fun c ⟨c1, c2, c3, c4, c5, c6⟩ n2 hn2 => ?_)
    have cd : c.env (tv d) = e.eval a.env := by
      rw [c2 (tv d) (by rw [tv_val d (by omega)]; omega) (tv_ne_vJ d (by omega)), b1]
    refine Hs.last (hs_add C (tv d) (tv (d + 1)) c (tv_ne (by omega) hdd (by omega)) (by rw [cd, c1, hf]; exact ok3))
      (fun g hg n3 hn3 => ?_)
    subst hg
    refine ⟨⟨by rw [DS.set_env_self, cd, c1, hf]; rfl, StackFr.trans b2 (StackFr.trans (c2.mono (by omega))
      (StackFr.set _ _ (Or.inl (tv_ge d (by omega))))), by rw [← b3, ← c3]; rfl, by rw [← b4, ← c4]; rfl,
      by rw [← b5, ← c5]; rfl, c6.set_tv d (by omega) _⟩, by simp only [AE.cost]; omega⟩
  | sub e f ihe ihf =>
    intro d a hv hd hc hok
    obtain ⟨ok1, ok2⟩ := hok
    simp only [AE.depth] at hd
    have hdd : d + 1 < 50 := by omega
    refine Hx.hs (Hs.then (ihe d a hv.1 (by omega) hc ok1) (fun b ⟨b1, b2, b3, b4, b5, b6⟩ n1 hn1 => ?_))
    have hf : f.eval b.env = f.eval a.env := eval_congr f hv.2 a b d b2
    refine Hs.then (ihf (d + 1) b hv.2 (by omega) b6 ((ok_congr _ f hv.2 a b d b2).2 ok2))
      (fun c ⟨c1, c2, c3, c4, c5, c6⟩ n2 hn2 => ?_)
    have cd : c.env (tv d) = e.eval a.env := by
      rw [c2 (tv d) (by rw [tv_val d (by omega)]; omega) (tv_ne_vJ d (by omega)), b1]
    have hne : tv d ≠ tv (d + 1) := tv_ne (by omega) hdd (by omega)
    have step : Hs C (.ite (.lt (tv d) (tv (d + 1))) (.op (.zero (tv d))) (.op (.sub (tv d) (tv (d + 1))))) c 2
        (fun g => g = c.set (tv d) (e.eval a.env - f.eval a.env)) := by
      refine Hs.ite (c := .lt (tv d) (tv (d + 1))) hne (fun he => ?_) (fun he => ?_)
      · have hlt : e.eval a.env < f.eval a.env := by
          simp only [Cnd.eval, decide_eq_true_eq, cd, c1, hf] at he; exact he
        refine Hs.mono (hs_zero C (tv d) c) (by omega) ?_
        rintro g rfl; congr 1; omega
      · have hle : f.eval a.env ≤ e.eval a.env := by
          simp only [Cnd.eval, decide_eq_false_iff_not, not_lt, cd, c1, hf] at he; exact he
        refine Hs.mono (hs_sub C (tv d) (tv (d + 1)) c hne (by rw [cd, c1, hf]; exact hle)) (by omega) ?_
        rintro g rfl; rw [cd, c1, hf]
    refine Hs.last step (fun g hg n3 hn3 => ?_)
    subst hg
    refine ⟨⟨by rw [DS.set_env_self]; rfl, StackFr.trans b2 (StackFr.trans (c2.mono (by omega))
      (StackFr.set _ _ (Or.inl (tv_ge d (by omega))))), by rw [← b3, ← c3]; rfl, by rw [← b4, ← c4]; rfl,
      by rw [← b5, ← c5]; rfl, c6.set_tv d (by omega) _⟩, by simp only [AE.cost]; omega⟩
  | mul e f ihe ihf =>
    intro d a hv hd hc hok
    obtain ⟨ok1, ok2, ok3⟩ := hok
    simp only [AE.depth] at hd
    have h1 : d + 1 < 50 := by omega
    have h2 : d + 2 < 50 := by omega
    refine Hx.hs (Hs.then (ihe (d + 1) a hv.1 (by omega) hc ok1) (fun b ⟨b1, b2, b3, b4, b5, b6⟩ n1 hn1 => ?_))
    have hf : f.eval b.env = f.eval a.env := eval_congr f hv.2 a b (d + 1) b2
    refine Hs.then (ihf (d + 2) b hv.2 (by omega) b6 ((ok_congr _ f hv.2 a b (d + 1) b2).2 ok2))
      (fun c ⟨c1, c2, c3, c4, c5, c6⟩ n2 hn2 => ?_)
    have cd : c.env (tv (d + 1)) = e.eval a.env := by
      rw [c2 (tv (d + 1)) (by rw [tv_val _ h1]; omega) (tv_ne_vJ _ h1), b1]
    refine Hs.last (hs_mul C (tv (d + 1)) (tv (d + 2)) (tv d) c (tv_ne h1 h2 (by omega)) (tv_ne h1 (by omega) (by omega))
      (tv_ne h2 (by omega) (by omega)) (by rw [cd, c1, hf]; exact ok3)) (fun g hg n3 hn3 => ?_)
    subst hg
    refine ⟨⟨by rw [DS.set_env_self, cd, c1, hf]; rfl, StackFr.trans (b2.mono (by omega)) (StackFr.trans (c2.mono (by omega))
      (StackFr.set _ _ (Or.inl (tv_ge d (by omega))))), by rw [← b3, ← c3]; rfl, by rw [← b4, ← c4]; rfl,
      by rw [← b5, ← c5]; rfl, c6.set_tv d (by omega) _⟩, by simp only [AE.cost]; omega⟩
  | div e f ihe ihf =>
    intro d a hv hd hc hok
    obtain ⟨ok1, ok2, ok3, ok4⟩ := hok
    simp only [AE.depth] at hd
    have h1 : d + 1 < 50 := by omega
    have h2 : d + 2 < 50 := by omega
    have h3 : d + 3 < 50 := by omega
    refine Hx.hs (Hs.then (ihe (d + 1) a hv.1 (by omega) hc ok1) (fun b ⟨b1, b2, b3, b4, b5, b6⟩ n1 hn1 => ?_))
    have hf : f.eval b.env = f.eval a.env := eval_congr f hv.2 a b (d + 1) b2
    refine Hs.then (ihf (d + 2) b hv.2 (by omega) b6 ((ok_congr _ f hv.2 a b (d + 1) b2).2 ok2))
      (fun c ⟨c1, c2, c3, c4, c5, c6⟩ n2 hn2 => ?_)
    have cd : c.env (tv (d + 1)) = e.eval a.env := by
      rw [c2 (tv (d + 1)) (by rw [tv_val _ h1]; omega) (tv_ne_vJ _ h1), b1]
    refine Hs.last (hs_dm C (tv (d + 1)) (tv (d + 2)) (tv d) (tv (d + 3)) c (tv_ne h1 h2 (by omega))
      (tv_ne h1 (by omega) (by omega)) (tv_ne h1 h3 (by omega)) (tv_ne h2 (by omega) (by omega)) (tv_ne h2 h3 (by omega))
      (tv_ne (by omega) h3 (by omega)) (by rw [c1, hf]; exact ok3) (by rw [c1, hf]; exact ok4)) (fun g hg n3 hn3 => ?_)
    subst hg
    have hS : StackFr a ((c.set (tv d) (c.env (tv (d + 1)) / c.env (tv (d + 2)))).set (tv (d + 3))
        (c.env (tv (d + 1)) % c.env (tv (d + 2)))) d :=
      StackFr.trans (b2.mono (by omega)) (StackFr.trans (c2.mono (by omega)) (StackFr.trans
        (StackFr.set _ _ (Or.inl (tv_ge d (by omega)))) (StackFr.set _ _ (Or.inl (by rw [tv_val _ h3]; omega)))))
    refine ⟨⟨by rw [DS.set_env_ne _ _ (tv_ne (by omega) h3 (by omega)), DS.set_env_self, cd, c1, hf]; rfl, hS,
      by rw [← b3, ← c3]; rfl, by rw [← b4, ← c4]; rfl, by rw [← b5, ← c5]; rfl,
      (c6.set_tv d (by omega) _).set_tv (d + 3) h3 _⟩, by simp only [AE.cost]; omega⟩
  | mod e f ihe ihf =>
    intro d a hv hd hc hok
    obtain ⟨ok1, ok2, ok3, ok4⟩ := hok
    simp only [AE.depth] at hd
    have h1 : d + 1 < 50 := by omega
    have h2 : d + 2 < 50 := by omega
    have h3 : d + 3 < 50 := by omega
    refine Hx.hs (Hs.then (ihe (d + 1) a hv.1 (by omega) hc ok1) (fun b ⟨b1, b2, b3, b4, b5, b6⟩ n1 hn1 => ?_))
    have hf : f.eval b.env = f.eval a.env := eval_congr f hv.2 a b (d + 1) b2
    refine Hs.then (ihf (d + 2) b hv.2 (by omega) b6 ((ok_congr _ f hv.2 a b (d + 1) b2).2 ok2))
      (fun c ⟨c1, c2, c3, c4, c5, c6⟩ n2 hn2 => ?_)
    have cd : c.env (tv (d + 1)) = e.eval a.env := by
      rw [c2 (tv (d + 1)) (by rw [tv_val _ h1]; omega) (tv_ne_vJ _ h1), b1]
    refine Hs.last (hs_dm C (tv (d + 1)) (tv (d + 2)) (tv (d + 3)) (tv d) c (tv_ne h1 h2 (by omega))
      (tv_ne h1 h3 (by omega)) (tv_ne h1 (by omega) (by omega)) (tv_ne h2 h3 (by omega)) (tv_ne h2 (by omega) (by omega))
      (tv_ne h3 (by omega) (by omega)) (by rw [c1, hf]; exact ok3) (by rw [c1, hf]; exact ok4)) (fun g hg n3 hn3 => ?_)
    subst hg
    have hS : StackFr a ((c.set (tv (d + 3)) (c.env (tv (d + 1)) / c.env (tv (d + 2)))).set (tv d)
        (c.env (tv (d + 1)) % c.env (tv (d + 2)))) d :=
      StackFr.trans (b2.mono (by omega)) (StackFr.trans (c2.mono (by omega)) (StackFr.trans
        (StackFr.set _ _ (Or.inl (by rw [tv_val _ h3]; omega))) (StackFr.set _ _ (Or.inl (tv_ge d (by omega))))))
    refine ⟨⟨by rw [DS.set_env_self, cd, c1, hf]; rfl, hS,
      by rw [← b3, ← c3]; rfl, by rw [← b4, ← c4]; rfl, by rw [← b5, ← c5]; rfl,
      (c6.set_tv (d + 3) h3 _).set_tv d (by omega) _⟩, by simp only [AE.cost]; omega⟩

/-- Discharge `AE.ok` side conditions: unfold, then `omega` on every conjunct. -/
syntax "aeok" " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| aeok [$ls,*]) =>
    `(tactic| (simp only [AE.ok, AE.eval, true_and, and_true, $ls,*]; and_intros <;> first | trivial | omega))

/-- Discharge `vars_ok` and depth side conditions. -/
syntax "aevar" : tactic
macro_rules
  | `(tactic| aevar) => `(tactic| simp (config := { decide := true }) [AE.vars_ok, AE.depth])

/-! ## Assignment -/

/-- `x := e`. -/
def assign (x : Fin VV) (e : AE) : St VV := .seq (cE e 0) (.op (.copy x (tv 0)))

/-- The assignment's frame: `x`, the stack, `vJ`. -/
def AsgFr (a b : DS VV) (x : Fin VV) : Prop := ∀ y : Fin VV, y.val < 200 → y ≠ vJ → y ≠ x → b.env y = a.env y

theorem assign_spec (x : Fin VV) (hx : x.val < 200) (hxP : x ∉ [vZ, v1, v2, vPOS]) (e : AE) (a : DS VV)
    (hv : e.vars_ok) (hd : e.depth + 1 < 50) (hc : Cst a) (hok : e.ok C.Wd a.env) :
    Hs C (assign x e) a (e.cost + 2) (fun b => b.env x = e.eval a.env ∧ AsgFr a b x ∧ b.cp = a.cp ∧ b.wq = a.wq ∧
      b.out = a.out ∧ Cst b) := by
  refine Hs.seq (cE_spec e 0 a hv (by omega) hc hok) (fun b ⟨b1, b2, b3, b4, b5, b6⟩ => ?_)
  refine Hs.mono (hs_copy C x (tv 0) b (by intro h; have := congrArg Fin.val h; rw [tv_val 0 (by omega)] at this; omega))
    le_rfl ?_
  rintro g rfl
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hxP
  refine ⟨by rw [DS.set_env_self, b1], fun y hy hj hyx => by rw [DS.set_env_ne _ _ hyx, b2 y (by omega) hj], b3, b4, b5,
    ⟨by rw [DS.set_env_ne _ _ (Ne.symm hxP.1)]; exact b6.z, by rw [DS.set_env_ne _ _ (Ne.symm hxP.2.1)]; exact b6.one,
      by rw [DS.set_env_ne _ _ (Ne.symm hxP.2.2.1)]; exact b6.two,
      by rw [DS.set_env_ne _ _ (Ne.symm hxP.2.2.2)]; exact b6.pos⟩⟩

theorem AsgFr.of_fr {a b : DS VV} {x : Fin VV} (h : AsgFr a b x) (T : List (Fin VV)) (hT : x ∈ T)
    (hT' : ∀ y : Fin VV, 200 ≤ y.val → y ∈ T) (hJ : vJ ∈ T) : Fr a b T := by
  intro y hy
  by_cases h1 : y.val < 200
  · exact h y h1 (fun e => hy (e ▸ hJ)) (fun e => hy (e ▸ hT))
  · exact absurd (hT' y (by omega)) hy

end NearCubicGates.Close.Dispatch
