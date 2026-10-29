import SourceAdapters.Compile.OraclePrintTemplate
import SourceAdapters.Compile.OraclePrintCells

/-!
# Cell evaluation of the printer's index terms

proof of `thm:short-pcp-ours`: the circuit is computed by an ordinary machine in polynomial time. The templates of
`OraclePrintTemplate` read their numbers (widths, clock, member indices) at run time through index terms `Tm`. This
module compiles a term into straight cell code that leaves its value in an evaluation register (`compT_spec`): the
registers `Rg d` (40–55) form an evaluation stack, the registers `Sl j` (64–79) hold the bound numbers, `Bd j`
(80–95) the loop bounds of the template compiler. Values stay below a bound `V` with `2V + 2 ≤ 2^Wd` (`Tm.okV`);
`Tm.okV_of_le` discharges it from a bound on the bound numbers.
-/

namespace NearCubicGates.Adapters.Compile.OraclePrint

open NearCubicWires NearCubicGates.Close.Cells

set_option autoImplicit false

/-! ## Registers -/

/-- Evaluation registers. -/
def Rg (d : ℕ) : Fin VV := ⟨40 + d % 16, by have := Nat.mod_lt d (show 16 > 0 by norm_num); show _ < 128; omega⟩
/-- Bound-number (slot) registers. -/
def Sl (j : ℕ) : Fin VV := ⟨64 + j % 16, by have := Nat.mod_lt j (show 16 > 0 by norm_num); show _ < 128; omega⟩
/-- Loop-bound registers. -/
def Bd (j : ℕ) : Fin VV := ⟨80 + j % 16, by have := Nat.mod_lt j (show 16 > 0 by norm_num); show _ < 128; omega⟩

theorem Rg_val {d : ℕ} (h : d < 16) : (Rg d).val = 40 + d := by simp [Rg, Nat.mod_eq_of_lt h]
theorem Sl_val {j : ℕ} (h : j < 16) : (Sl j).val = 64 + j := by simp [Sl, Nat.mod_eq_of_lt h]
theorem Bd_val {j : ℕ} (h : j < 16) : (Bd j).val = 80 + j := by simp [Bd, Nat.mod_eq_of_lt h]

theorem ne_of_val {x y : Fin VV} (h : x.val ≠ y.val) : x ≠ y := fun e => h (congrArg Fin.val e)

theorem Rg_ne_low {d : ℕ} (hd : d < 16) {y : Fin VV} (hy : y.val < 40) : Rg d ≠ y :=
  ne_of_val (by rw [Rg_val hd]; omega)

/-! ## Terms: register need, cost, value bounds -/

/-- Evaluation registers used from the target register on. -/
def Tm.need : Tm → ℕ
  | .v _ => 1
  | .k _ => 1
  | .add a b | .sub a b | .lt a b | .eq a b => max a.need (b.need + 1)
  | .mul a b => max (max a.need (b.need + 1)) 3
  | .div a b | .md a b => max (max a.need (b.need + 1)) 4
  | .ite c a b => max c.need (max a.need b.need)

theorem Tm.one_le_need : ∀ t : Tm, 1 ≤ t.need
  | .v _ | .k _ => le_rfl
  | .add _ b | .sub _ b | .lt _ b | .eq _ b => le_max_of_le_right (by omega)
  | .mul _ _ => le_max_of_le_right (by omega)
  | .div _ _ | .md _ _ => le_max_of_le_right (by omega)
  | .ite c _ _ => le_max_of_le_left (Tm.one_le_need c)

/-- Cell cost bound. -/
def Tm.cost : Tm → ℕ
  | .v _ => 1
  | .k c => 2 * c + 1
  | .add a b | .sub a b | .mul a b | .div a b | .md a b | .lt a b | .eq a b => a.cost + b.cost + 8
  | .ite c a b => c.cost + a.cost + b.cost + 2

/-- Every intermediate value is at most `V`. -/
def Tm.okV (V : ℕ) (env : List ℕ) : Tm → Prop
  | .v j => env.getD j 0 ≤ V
  | .k c => c ≤ V
  | .add a b => a.okV V env ∧ b.okV V env ∧ a.eval env + b.eval env ≤ V
  | .sub a b => a.okV V env ∧ b.okV V env
  | .mul a b => a.okV V env ∧ b.okV V env ∧ a.eval env * b.eval env ≤ V
  | .div a b | .md a b | .lt a b | .eq a b => a.okV V env ∧ b.okV V env
  | .ite c a b => c.okV V env ∧ a.okV V env ∧ b.okV V env

theorem Tm.eval_le_of_okV {V : ℕ} (hV : 1 ≤ V) (env : List ℕ) : ∀ t : Tm, t.okV V env → t.eval env ≤ V
  | .v j, h => h
  | .k c, h => h
  | .add a b, h => h.2.2
  | .sub a b, h => (Nat.sub_le _ _).trans (Tm.eval_le_of_okV hV env a h.1)
  | .mul a b, h => h.2.2
  | .div a b, h => (Nat.div_le_self _ _).trans (Tm.eval_le_of_okV hV env a h.1)
  | .md a b, h => (Nat.mod_le _ _).trans (Tm.eval_le_of_okV hV env a h.1)
  | .lt a b, _ => by simp only [Tm.eval]; split <;> omega
  | .eq a b, _ => by simp only [Tm.eval]; split <;> omega
  | .ite c a b, h => by
      simp only [Tm.eval]
      split
      · exact Tm.eval_le_of_okV hV env b h.2.2
      · exact Tm.eval_le_of_okV hV env a h.2.1

/-- Size and largest constant, for the generic value bound. -/
def Tm.sz : Tm → ℕ
  | .v _ | .k _ => 1
  | .add a b | .sub a b | .mul a b | .div a b | .md a b | .lt a b | .eq a b => a.sz + b.sz + 1
  | .ite c a b => c.sz + a.sz + b.sz + 1

def Tm.kmax : Tm → ℕ
  | .v _ => 0
  | .k c => c
  | .add a b | .sub a b | .mul a b | .div a b | .md a b | .lt a b | .eq a b => max a.kmax b.kmax
  | .ite c a b => max c.kmax (max a.kmax b.kmax)

theorem pow_mono_le {X a b : ℕ} (hX : 1 ≤ X) (h : a ≤ b) : X ^ a ≤ X ^ b := Nat.pow_le_pow_right hX h

/-- **Generic value bound**: if every bound number is at most `M` and `X = M + K + 2` with `K` at least every
constant, every value is at most `X ^ sz`. -/
theorem Tm.eval_le_pow (env : List ℕ) (M K : ℕ) (hM : ∀ j, env.getD j 0 ≤ M) :
    ∀ t : Tm, t.kmax ≤ K → t.eval env ≤ (M + K + 2) ^ t.sz := by
  intro t
  induction t with
  | v j =>
      intro _
      simp only [Tm.eval, Tm.sz, pow_one]
      have := hM j; omega
  | k c => intro h; simp only [Tm.eval, Tm.sz, Tm.kmax, pow_one] at *; omega
  | add a b iha ihb =>
      intro h
      simp only [Tm.kmax, max_le_iff] at h
      have ha := iha h.1; have hb := ihb h.2
      simp only [Tm.eval, Tm.sz]
      have hX : 2 ≤ M + K + 2 := by omega
      have e1 : (M + K + 2) ^ a.sz ≤ (M + K + 2) ^ (a.sz + b.sz) := pow_mono_le (by omega) (by omega)
      have e2 : (M + K + 2) ^ b.sz ≤ (M + K + 2) ^ (a.sz + b.sz) := pow_mono_le (by omega) (by omega)
      rw [pow_succ]
      nlinarith
  | sub a b iha ihb =>
      intro h
      simp only [Tm.kmax, max_le_iff] at h
      have ha := iha h.1
      simp only [Tm.eval, Tm.sz]
      have e1 : (M + K + 2) ^ a.sz ≤ (M + K + 2) ^ (a.sz + b.sz + 1) := pow_mono_le (by omega) (by omega)
      omega
  | mul a b iha ihb =>
      intro h
      simp only [Tm.kmax, max_le_iff] at h
      have ha := iha h.1; have hb := ihb h.2
      simp only [Tm.eval, Tm.sz]
      have e1 : (M + K + 2) ^ (a.sz + b.sz) ≤ (M + K + 2) ^ (a.sz + b.sz + 1) := pow_mono_le (by omega) (by omega)
      rw [pow_add] at e1
      calc a.eval env * b.eval env ≤ (M + K + 2) ^ a.sz * (M + K + 2) ^ b.sz := Nat.mul_le_mul ha hb
        _ ≤ _ := e1
  | div a b iha ihb =>
      intro h
      simp only [Tm.kmax, max_le_iff] at h
      have ha := iha h.1
      simp only [Tm.eval, Tm.sz]
      have e1 : (M + K + 2) ^ a.sz ≤ (M + K + 2) ^ (a.sz + b.sz + 1) := pow_mono_le (by omega) (by omega)
      exact (Nat.div_le_self _ _).trans (ha.trans e1)
  | md a b iha ihb =>
      intro h
      simp only [Tm.kmax, max_le_iff] at h
      have ha := iha h.1
      simp only [Tm.eval, Tm.sz]
      have e1 : (M + K + 2) ^ a.sz ≤ (M + K + 2) ^ (a.sz + b.sz + 1) := pow_mono_le (by omega) (by omega)
      exact (Nat.mod_le _ _).trans (ha.trans e1)
  | lt a b _ _ =>
      intro _
      simp only [Tm.eval, Tm.sz]
      have : 1 ≤ (M + K + 2) ^ (a.sz + b.sz + 1) := Nat.one_le_pow _ _ (by omega)
      split <;> omega
  | eq a b _ _ =>
      intro _
      simp only [Tm.eval, Tm.sz]
      have : 1 ≤ (M + K + 2) ^ (a.sz + b.sz + 1) := Nat.one_le_pow _ _ (by omega)
      split <;> omega
  | ite c a b _ iha ihb =>
      intro h
      simp only [Tm.kmax, max_le_iff] at h
      have ha := iha h.2.1; have hb := ihb h.2.2
      simp only [Tm.eval, Tm.sz]
      have e1 : (M + K + 2) ^ a.sz ≤ (M + K + 2) ^ (c.sz + a.sz + b.sz + 1) := pow_mono_le (by omega) (by omega)
      have e2 : (M + K + 2) ^ b.sz ≤ (M + K + 2) ^ (c.sz + a.sz + b.sz + 1) := pow_mono_le (by omega) (by omega)
      split <;> omega

/-- The generic bound makes every term `okV` at `V = (M + K + 2) ^ sz`. -/
theorem Tm.okV_of_le (env : List ℕ) (M K : ℕ) (hM : ∀ j, env.getD j 0 ≤ M) :
    ∀ (t : Tm) (V : ℕ), t.kmax ≤ K → (M + K + 2) ^ t.sz ≤ V → t.okV V env := by
  intro t
  have hX : 2 ≤ M + K + 2 := by omega
  induction t with
  | v j => intro V _ hV; simp only [Tm.okV, Tm.sz, pow_one] at *; have := hM j; omega
  | k c => intro V h hV; simp only [Tm.okV, Tm.sz, Tm.kmax, pow_one] at *; omega
  | add a b iha ihb =>
      intro V h hV
      simp only [Tm.kmax, max_le_iff, Tm.sz] at h hV
      have ea : (M + K + 2) ^ a.sz ≤ (M + K + 2) ^ (a.sz + b.sz + 1) := pow_mono_le (by omega) (by omega)
      have eb : (M + K + 2) ^ b.sz ≤ (M + K + 2) ^ (a.sz + b.sz + 1) := pow_mono_le (by omega) (by omega)
      refine ⟨iha V h.1 (ea.trans hV), ihb V h.2 (eb.trans hV), ?_⟩
      have := Tm.eval_le_pow env M K hM (.add a b) (by simp [Tm.kmax]; omega)
      simp only [Tm.eval, Tm.sz] at this
      omega
  | sub a b iha ihb =>
      intro V h hV
      simp only [Tm.kmax, max_le_iff, Tm.sz] at h hV
      have ea : (M + K + 2) ^ a.sz ≤ (M + K + 2) ^ (a.sz + b.sz + 1) := pow_mono_le (by omega) (by omega)
      have eb : (M + K + 2) ^ b.sz ≤ (M + K + 2) ^ (a.sz + b.sz + 1) := pow_mono_le (by omega) (by omega)
      exact ⟨iha V h.1 (ea.trans hV), ihb V h.2 (eb.trans hV)⟩
  | mul a b iha ihb =>
      intro V h hV
      simp only [Tm.kmax, max_le_iff, Tm.sz] at h hV
      have ea : (M + K + 2) ^ a.sz ≤ (M + K + 2) ^ (a.sz + b.sz + 1) := pow_mono_le (by omega) (by omega)
      have eb : (M + K + 2) ^ b.sz ≤ (M + K + 2) ^ (a.sz + b.sz + 1) := pow_mono_le (by omega) (by omega)
      refine ⟨iha V h.1 (ea.trans hV), ihb V h.2 (eb.trans hV), ?_⟩
      have := Tm.eval_le_pow env M K hM (.mul a b) (by simp [Tm.kmax]; omega)
      simp only [Tm.eval, Tm.sz] at this
      omega
  | div a b iha ihb =>
      intro V h hV
      simp only [Tm.kmax, max_le_iff, Tm.sz] at h hV
      have ea : (M + K + 2) ^ a.sz ≤ (M + K + 2) ^ (a.sz + b.sz + 1) := pow_mono_le (by omega) (by omega)
      have eb : (M + K + 2) ^ b.sz ≤ (M + K + 2) ^ (a.sz + b.sz + 1) := pow_mono_le (by omega) (by omega)
      exact ⟨iha V h.1 (ea.trans hV), ihb V h.2 (eb.trans hV)⟩
  | md a b iha ihb =>
      intro V h hV
      simp only [Tm.kmax, max_le_iff, Tm.sz] at h hV
      have ea : (M + K + 2) ^ a.sz ≤ (M + K + 2) ^ (a.sz + b.sz + 1) := pow_mono_le (by omega) (by omega)
      have eb : (M + K + 2) ^ b.sz ≤ (M + K + 2) ^ (a.sz + b.sz + 1) := pow_mono_le (by omega) (by omega)
      exact ⟨iha V h.1 (ea.trans hV), ihb V h.2 (eb.trans hV)⟩
  | lt a b iha ihb =>
      intro V h hV
      simp only [Tm.kmax, max_le_iff, Tm.sz] at h hV
      have ea : (M + K + 2) ^ a.sz ≤ (M + K + 2) ^ (a.sz + b.sz + 1) := pow_mono_le (by omega) (by omega)
      have eb : (M + K + 2) ^ b.sz ≤ (M + K + 2) ^ (a.sz + b.sz + 1) := pow_mono_le (by omega) (by omega)
      exact ⟨iha V h.1 (ea.trans hV), ihb V h.2 (eb.trans hV)⟩
  | eq a b iha ihb =>
      intro V h hV
      simp only [Tm.kmax, max_le_iff, Tm.sz] at h hV
      have ea : (M + K + 2) ^ a.sz ≤ (M + K + 2) ^ (a.sz + b.sz + 1) := pow_mono_le (by omega) (by omega)
      have eb : (M + K + 2) ^ b.sz ≤ (M + K + 2) ^ (a.sz + b.sz + 1) := pow_mono_le (by omega) (by omega)
      exact ⟨iha V h.1 (ea.trans hV), ihb V h.2 (eb.trans hV)⟩
  | ite c a b ihc iha ihb =>
      intro V h hV
      simp only [Tm.kmax, max_le_iff, Tm.sz] at h hV
      have ec : (M + K + 2) ^ c.sz ≤ (M + K + 2) ^ (c.sz + a.sz + b.sz + 1) := pow_mono_le (by omega) (by omega)
      have ea : (M + K + 2) ^ a.sz ≤ (M + K + 2) ^ (c.sz + a.sz + b.sz + 1) := pow_mono_le (by omega) (by omega)
      have eb : (M + K + 2) ^ b.sz ≤ (M + K + 2) ^ (c.sz + a.sz + b.sz + 1) := pow_mono_le (by omega) (by omega)
      exact ⟨ihc V h.1 (ec.trans hV), iha V h.2.1 (ea.trans hV), ihb V h.2.2 (eb.trans hV)⟩

/-! ## Compilation of terms -/

/-- `x := c`. -/
def ldK (x : Fin VV) : ℕ → St VV MM
  | 0 => .op (.zero x)
  | c + 1 => .seq (ldK x c) (.op (.inc x))

/-- Evaluate `t` into `Rg d`, using `Rg d'` for `d' > d` as scratch. -/
def compT : Tm → ℕ → St VV MM
  | .v j, d => if j < 16 then .op (.copy (Rg d) (Sl j)) else .op (.zero (Rg d))
  | .k c, d => ldK (Rg d) c
  | .add a b, d => .seq (compT a d) (.seq (compT b (d + 1)) (.op (.add (Rg d) (Rg (d + 1)))))
  | .sub a b, d => .seq (compT a d) (.seq (compT b (d + 1))
      (.ite (.lt (Rg d) (Rg (d + 1))) (.op (.zero (Rg d))) (.op (.sub (Rg d) (Rg (d + 1))))))
  | .mul a b, d => .seq (compT a d) (.seq (compT b (d + 1))
      (.seq (.op (.mul (Rg d) (Rg (d + 1)) (Rg (d + 2)))) (.op (.copy (Rg d) (Rg (d + 2))))))
  | .div a b, d => .seq (compT a d) (.seq (compT b (d + 1))
      (.ite (.eq (Rg (d + 1)) vZ) (.op (.zero (Rg d)))
        (.seq (.op (.dm (Rg d) (Rg (d + 1)) (Rg (d + 2)) (Rg (d + 3)))) (.op (.copy (Rg d) (Rg (d + 2)))))))
  | .md a b, d => .seq (compT a d) (.seq (compT b (d + 1))
      (.ite (.eq (Rg (d + 1)) vZ) (.op (.copy (Rg (d + 2)) (Rg d)))
        (.seq (.op (.dm (Rg d) (Rg (d + 1)) (Rg (d + 2)) (Rg (d + 3)))) (.op (.copy (Rg d) (Rg (d + 3)))))))
  | .lt a b, d => .seq (compT a d) (.seq (compT b (d + 1))
      (.ite (.lt (Rg d) (Rg (d + 1))) (.op (.copy (Rg d) v1)) (.op (.zero (Rg d)))))
  | .eq a b, d => .seq (compT a d) (.seq (compT b (d + 1))
      (.ite (.eq (Rg d) (Rg (d + 1))) (.op (.copy (Rg d) v1)) (.op (.zero (Rg d)))))
  | .ite c a b, d => .seq (compT c d) (.ite (.eq (Rg d) vZ) (compT b d) (compT a d))

variable {C : Ctx}

theorem ldK_spec (x : Fin VV) (a : DS VV MM) : ∀ c : ℕ, c < 2 ^ C.Wd →
    Hs C (ldK x c) a (2 * c + 1) (fun b => b = a.set x c)
  | 0, _ => Hs.mono (hs_zero C x a) le_rfl (fun b hb => hb)
  | c + 1, h => by
      refine Hs.mono (t := 2 * c + 1 + 1 + 1) (Hs.seq (ldK_spec x a c (by omega)) (fun b hb => ?_)) (by omega)
        (fun b hb => hb)
      subst hb
      refine Hs.mono (hs_inc C x _ (by rw [DS.set_env_self]; omega)) le_rfl ?_
      rintro b rfl
      rw [DS.set_env_self, DS.set_set]

/-- The evaluation registers from `d` on. -/
def EvFrom (d : ℕ) (y : Fin VV) : Prop := 40 + d ≤ y.val ∧ y.val < 56

/-- The registers outside `EvFrom d` keep their values and nothing else changes. -/
structure TFr (d : ℕ) (a b : DS VV MM) : Prop where
  env : ∀ y : Fin VV, ¬ EvFrom d y → b.env y = a.env y
  same : Same a b

theorem TFr.refl (d : ℕ) (a : DS VV MM) : TFr d a a := ⟨fun _ _ => rfl, Same.refl a⟩

theorem TFr.trans {d : ℕ} {a b c : DS VV MM} (h1 : TFr d a b) (h2 : TFr d b c) : TFr d a c :=
  ⟨fun y hy => (h2.env y hy).trans (h1.env y hy), Same.trans h1.same h2.same⟩

theorem TFr.weaken {d e : ℕ} {a b : DS VV MM} (h : TFr e a b) (hde : d ≤ e) : TFr d a b :=
  ⟨fun y hy => h.env y (fun ⟨h1, h2⟩ => hy ⟨by omega, h2⟩), h.same⟩

theorem TFr.set {d e : ℕ} (a : DS VV MM) (v : ℕ) (hd : d ≤ e) (he : e < 16) : TFr d a (a.set (Rg e) v) := by
  refine ⟨fun y hy => ?_, Same.set a _ v⟩
  have : y ≠ Rg e := by
    intro h; subst h; apply hy; rw [EvFrom, Rg_val he]; omega
  exact DS.set_env_ne a v this

theorem notEv {d : ℕ} {y : Fin VV} (h : y.val < 40 ∨ 56 ≤ y.val) : ¬ EvFrom d y := by
  unfold EvFrom; omega

theorem TFr.cst {d : ℕ} {a b : DS VV MM} (h : TFr d a b) (hc : Cst a) : Cst b :=
  ⟨by rw [h.env vZ (notEv (by left; decide)), hc.z], by rw [h.env v1 (notEv (by left; decide)), hc.one],
    by rw [h.env v2 (notEv (by left; decide)), hc.two]⟩

theorem TFr.slots {d : ℕ} {a b : DS VV MM} (h : TFr d a b) (env : List ℕ)
    (hs : ∀ j < 16, a.env (Sl j) = env.getD j 0) : ∀ j < 16, b.env (Sl j) = env.getD j 0 := fun j hj => by
  rw [h.env (Sl j) (notEv (by rw [Sl_val hj]; omega)), hs j hj]

/-- The two operands of a binary term, then a tail. -/
theorem pair_spec (env : List ℕ) (a b : Tm) (d : ℕ) (hd : d + 1 < 16) (s : DS VV MM) (hc : Cst s)
    (hs : ∀ j < 16, s.env (Sl j) = env.getD j 0)
    (ha : Hs C (compT a d) s a.cost (fun x => x.env (Rg d) = a.eval env ∧ TFr d s x))
    (hb : ∀ s1, Cst s1 → (∀ j < 16, s1.env (Sl j) = env.getD j 0) →
      Hs C (compT b (d + 1)) s1 b.cost (fun x => x.env (Rg (d + 1)) = b.eval env ∧ TFr (d + 1) s1 x))
    (tail : St VV MM) (tc : ℕ) (R : DS VV MM → Prop)
    (ht : ∀ s2, Cst s2 → s2.env (Rg d) = a.eval env → s2.env (Rg (d + 1)) = b.eval env → TFr d s s2 →
      Hs C tail s2 tc R) :
    Hs C (.seq (compT a d) (.seq (compT b (d + 1)) tail)) s (a.cost + (b.cost + tc + 1) + 1) R := by
  refine Hs.seq ha (fun s1 h1 => ?_)
  obtain ⟨v1', f1⟩ := h1
  refine Hs.seq (hb s1 (f1.cst hc) (f1.slots env hs)) (fun s2 h2 => ?_)
  obtain ⟨v2', f2⟩ := h2
  have hr : s2.env (Rg d) = a.eval env := by
    rw [f2.env (Rg d) (by simp only [EvFrom, Rg_val (by omega : d < 16)]; omega), v1']
  exact ht s2 ((f1.trans (f2.weaken (by omega))).cst hc) hr v2' (f1.trans (f2.weaken (by omega)))

/-- **Term evaluation** (`compT_spec`): from a state whose slot registers hold `env`, `compT t d` leaves
`t.eval env` in `Rg d`, changes only `Rg d … Rg 15`, and costs at most `t.cost`. -/
theorem compT_spec (V : ℕ) (hV : 2 * V + 2 ≤ 2 ^ C.Wd) (hV1' : 1 ≤ V) (env : List ℕ) (henv : env.length ≤ 16) :
    ∀ (t : Tm) (d : ℕ) (a : DS VV MM), Cst a → d + t.need ≤ 16 → (∀ j < 16, a.env (Sl j) = env.getD j 0) →
      t.okV V env → Hs C (compT t d) a t.cost (fun b => b.env (Rg d) = t.eval env ∧ TFr d a b) := by
  have hV1 : V < 2 ^ C.Wd := by omega
  intro t
  induction t with
  | v j =>
      intro d a _ hd hs _
      have hd16 : d < 16 := by simp only [Tm.need] at hd; omega
      simp only [compT, Tm.cost, Tm.eval]
      split
      · rename_i hj
        refine Hs.mono (hs_copy C (Rg d) (Sl j) a (ne_of_val (by rw [Rg_val hd16, Sl_val hj]; omega))) le_rfl ?_
        rintro b rfl
        exact ⟨by rw [DS.set_env_self, hs j hj], TFr.set a _ le_rfl hd16⟩
      · rename_i hj
        refine Hs.mono (hs_zero C (Rg d) a) le_rfl ?_
        rintro b rfl
        refine ⟨by rw [DS.set_env_self, List.getD_eq_default _ _ (by omega)], TFr.set a _ le_rfl hd16⟩
  | k c =>
      intro d a _ hd _ hok
      have hd16 : d < 16 := by simp only [Tm.need] at hd; omega
      simp only [Tm.okV] at hok
      refine Hs.mono (ldK_spec (C := C) (Rg d) a c (by omega)) (by simp [Tm.cost]) ?_
      rintro b rfl
      exact ⟨by rw [DS.set_env_self]; rfl, TFr.set a _ le_rfl hd16⟩
  | add a b iha ihb =>
      intro d s hc hd hs hok
      simp only [Tm.need] at hd
      have hd16 : d + 1 < 16 := by have := Tm.one_le_need b; omega
      obtain ⟨oa, ob, hsum⟩ := hok
      refine Hs.mono (pair_spec env a b d hd16 s hc hs (iha d s hc (by omega) hs oa)
        (fun s1 c1 h1 => ihb (d + 1) s1 c1 (by omega) h1 ob) _ 1 _ (fun s2 _ r1 r2 f => ?_))
        (by simp only [Tm.cost]; omega) (fun x hx => hx)
      have hne : Rg d ≠ Rg (d + 1) := ne_of_val (by rw [Rg_val (by omega), Rg_val hd16]; omega)
      refine Hs.mono (hs_add C (Rg d) (Rg (d + 1)) s2 hne (by rw [r1, r2]; omega)) le_rfl ?_
      rintro x rfl
      exact ⟨by rw [DS.set_env_self, r1, r2]; rfl, f.trans (TFr.set s2 _ le_rfl (by omega))⟩
  | sub a b iha ihb =>
      intro d s hc hd hs hok
      simp only [Tm.need] at hd
      have hd16 : d + 1 < 16 := by have := Tm.one_le_need b; omega
      obtain ⟨oa, ob⟩ := hok
      refine Hs.mono (pair_spec env a b d hd16 s hc hs (iha d s hc (by omega) hs oa)
        (fun s1 c1 h1 => ihb (d + 1) s1 c1 (by omega) h1 ob) _ 2 _ (fun s2 _ r1 r2 f => ?_))
        (by simp only [Tm.cost]; omega) (fun x hx => hx)
      have hne : Rg d ≠ Rg (d + 1) := ne_of_val (by rw [Rg_val (by omega), Rg_val hd16]; omega)
      refine Hs.ite (C := C) hne (fun he => ?_) (fun he => ?_)
      · simp only [Cnd.eval, decide_eq_true_eq, r1, r2] at he
        refine Hs.mono (hs_zero C (Rg d) s2) le_rfl ?_
        rintro x rfl
        exact ⟨by rw [DS.set_env_self]; simp only [Tm.eval]; omega, f.trans (TFr.set s2 _ le_rfl (by omega))⟩
      · simp only [Cnd.eval, decide_eq_false_iff_not, r1, r2, not_lt] at he
        refine Hs.mono (hs_sub C (Rg d) (Rg (d + 1)) s2 hne (by rw [r1, r2]; exact he)) (by omega) ?_
        rintro x rfl
        exact ⟨by rw [DS.set_env_self, r1, r2]; rfl, f.trans (TFr.set s2 _ le_rfl (by omega))⟩
  | mul a b iha ihb =>
      intro d s hc hd hs hok
      simp only [Tm.need] at hd
      have hd16 : d + 2 < 16 := by omega
      obtain ⟨oa, ob, hprod⟩ := hok
      refine Hs.mono (pair_spec env a b d (by omega) s hc hs (iha d s hc (by omega) hs oa)
        (fun s1 c1 h1 => ihb (d + 1) s1 c1 (by omega) h1 ob) _ 3 _ (fun s2 _ r1 r2 f => ?_))
        (by simp only [Tm.cost]; omega) (fun x hx => hx)
      have n01 : Rg d ≠ Rg (d + 1) := ne_of_val (by rw [Rg_val (by omega), Rg_val (by omega)]; omega)
      have n02 : Rg d ≠ Rg (d + 2) := ne_of_val (by rw [Rg_val (by omega), Rg_val (by omega)]; omega)
      have n12 : Rg (d + 1) ≠ Rg (d + 2) := ne_of_val (by rw [Rg_val (by omega), Rg_val (by omega)]; omega)
      refine Hs.mono (t := 1 + 1 + 1) (Hs.seq (hs_mul C (Rg d) (Rg (d + 1)) (Rg (d + 2)) s2 n01 n02 n12
        (by rw [r1, r2]; omega)) (fun s3 h3 => ?_)) (by omega) (fun x hx => hx)
      subst h3
      refine Hs.mono (hs_copy C (Rg d) (Rg (d + 2)) _ n02) le_rfl ?_
      rintro x rfl
      refine ⟨by rw [DS.set_env_self, DS.set_env_self, r1, r2]; rfl, ?_⟩
      exact f.trans ((TFr.set s2 _ (by omega) (by omega)).trans (TFr.set _ _ le_rfl (by omega)))
  | div a b iha ihb =>
      intro d s hc hd hs hok
      simp only [Tm.need] at hd
      have hd16 : d + 3 < 16 := by omega
      obtain ⟨oa, ob⟩ := hok
      have hbV : b.eval env ≤ V := Tm.eval_le_of_okV hV1' env b ob
      refine Hs.mono (pair_spec env a b d (by omega) s hc hs (iha d s hc (by omega) hs oa)
        (fun s1 c1 h1 => ihb (d + 1) s1 c1 (by omega) h1 ob) _ 4 _ (fun s2 c2 r1 r2 f => ?_))
        (by simp only [Tm.cost]; omega) (fun x hx => hx)
      have hv : Rg (d + 1) ≠ vZ := Rg_ne_low (by omega) (by decide)
      have n01 : Rg d ≠ Rg (d + 1) := ne_of_val (by rw [Rg_val (by omega), Rg_val (by omega)]; omega)
      have n02 : Rg d ≠ Rg (d + 2) := ne_of_val (by rw [Rg_val (by omega), Rg_val (by omega)]; omega)
      have n03 : Rg d ≠ Rg (d + 3) := ne_of_val (by rw [Rg_val (by omega), Rg_val (by omega)]; omega)
      have n12 : Rg (d + 1) ≠ Rg (d + 2) := ne_of_val (by rw [Rg_val (by omega), Rg_val (by omega)]; omega)
      have n13 : Rg (d + 1) ≠ Rg (d + 3) := ne_of_val (by rw [Rg_val (by omega), Rg_val (by omega)]; omega)
      have n23 : Rg (d + 2) ≠ Rg (d + 3) := ne_of_val (by rw [Rg_val (by omega), Rg_val (by omega)]; omega)
      refine Hs.ite (C := C) hv (fun he => ?_) (fun he => ?_)
      · simp only [Cnd.eval, decide_eq_true_eq, r2, c2.z] at he
        refine Hs.mono (hs_zero C (Rg d) s2) (by omega) ?_
        rintro x rfl
        exact ⟨by rw [DS.set_env_self]; simp only [Tm.eval, he, Nat.div_zero],
          f.trans (TFr.set s2 _ le_rfl (by omega))⟩
      · simp only [Cnd.eval, decide_eq_false_iff_not, r2, c2.z] at he
        refine Hs.mono (t := 1 + 1 + 1) (Hs.seq (hs_dm C (Rg d) (Rg (d + 1)) (Rg (d + 2)) (Rg (d + 3)) s2 n01 n02
          n03 n12 n13 n23 (by rw [r2]; omega) (by rw [r2]; omega)) (fun s3 h3 => ?_)) (by omega) (fun x hx => hx)
        subst h3
        refine Hs.mono (hs_copy C (Rg d) (Rg (d + 2)) _ n02) le_rfl ?_
        rintro x rfl
        refine ⟨by rw [DS.set_env_self, DS.set_env_ne _ _ n23, DS.set_env_self, r1, r2]; rfl, ?_⟩
        exact f.trans ((TFr.set s2 _ (by omega) (by omega)).trans
          ((TFr.set _ _ (by omega) (by omega)).trans (TFr.set _ _ le_rfl (by omega))))
  | md a b iha ihb =>
      intro d s hc hd hs hok
      simp only [Tm.need] at hd
      have hd16 : d + 3 < 16 := by omega
      obtain ⟨oa, ob⟩ := hok
      have hbV : b.eval env ≤ V := Tm.eval_le_of_okV hV1' env b ob
      refine Hs.mono (pair_spec env a b d (by omega) s hc hs (iha d s hc (by omega) hs oa)
        (fun s1 c1 h1 => ihb (d + 1) s1 c1 (by omega) h1 ob) _ 4 _ (fun s2 c2 r1 r2 f => ?_))
        (by simp only [Tm.cost]; omega) (fun x hx => hx)
      have hv : Rg (d + 1) ≠ vZ := Rg_ne_low (by omega) (by decide)
      have n01 : Rg d ≠ Rg (d + 1) := ne_of_val (by rw [Rg_val (by omega), Rg_val (by omega)]; omega)
      have n02 : Rg d ≠ Rg (d + 2) := ne_of_val (by rw [Rg_val (by omega), Rg_val (by omega)]; omega)
      have n03 : Rg d ≠ Rg (d + 3) := ne_of_val (by rw [Rg_val (by omega), Rg_val (by omega)]; omega)
      have n12 : Rg (d + 1) ≠ Rg (d + 2) := ne_of_val (by rw [Rg_val (by omega), Rg_val (by omega)]; omega)
      have n13 : Rg (d + 1) ≠ Rg (d + 3) := ne_of_val (by rw [Rg_val (by omega), Rg_val (by omega)]; omega)
      have n23 : Rg (d + 2) ≠ Rg (d + 3) := ne_of_val (by rw [Rg_val (by omega), Rg_val (by omega)]; omega)
      refine Hs.ite (C := C) hv (fun he => ?_) (fun he => ?_)
      · simp only [Cnd.eval, decide_eq_true_eq, r2, c2.z] at he
        refine Hs.mono (hs_copy C (Rg (d + 2)) (Rg d) s2 (Ne.symm n02)) (by omega) ?_
        rintro x rfl
        refine ⟨by rw [DS.set_env_ne _ _ n02, r1]; simp only [Tm.eval, he, Nat.mod_zero],
          f.trans (TFr.set s2 _ (by omega) (by omega))⟩
      · simp only [Cnd.eval, decide_eq_false_iff_not, r2, c2.z] at he
        refine Hs.mono (t := 1 + 1 + 1) (Hs.seq (hs_dm C (Rg d) (Rg (d + 1)) (Rg (d + 2)) (Rg (d + 3)) s2 n01 n02
          n03 n12 n13 n23 (by rw [r2]; omega) (by rw [r2]; omega)) (fun s3 h3 => ?_)) (by omega) (fun x hx => hx)
        subst h3
        refine Hs.mono (hs_copy C (Rg d) (Rg (d + 3)) _ n03) le_rfl ?_
        rintro x rfl
        refine ⟨by rw [DS.set_env_self, DS.set_env_self, r1, r2]; rfl, ?_⟩
        exact f.trans ((TFr.set s2 _ (by omega) (by omega)).trans
          ((TFr.set _ _ (by omega) (by omega)).trans (TFr.set _ _ le_rfl (by omega))))
  | lt a b iha ihb =>
      intro d s hc hd hs hok
      simp only [Tm.need] at hd
      have hd16 : d + 1 < 16 := by have := Tm.one_le_need b; omega
      obtain ⟨oa, ob⟩ := hok
      refine Hs.mono (pair_spec env a b d hd16 s hc hs (iha d s hc (by omega) hs oa)
        (fun s1 c1 h1 => ihb (d + 1) s1 c1 (by omega) h1 ob) _ 2 _ (fun s2 c2 r1 r2 f => ?_))
        (by simp only [Tm.cost]; omega) (fun x hx => hx)
      have hne : Rg d ≠ Rg (d + 1) := ne_of_val (by rw [Rg_val (by omega), Rg_val hd16]; omega)
      have hv1 : Rg d ≠ v1 := Rg_ne_low (by omega) (by decide)
      refine Hs.ite (C := C) hne (fun he => ?_) (fun he => ?_)
      · simp only [Cnd.eval, decide_eq_true_eq, r1, r2] at he
        refine Hs.mono (hs_copy C (Rg d) v1 s2 hv1) (by omega) ?_
        rintro x rfl
        exact ⟨by rw [DS.set_env_self, c2.one]; simp only [Tm.eval, if_pos he],
          f.trans (TFr.set s2 _ le_rfl (by omega))⟩
      · simp only [Cnd.eval, decide_eq_false_iff_not, r1, r2] at he
        refine Hs.mono (hs_zero C (Rg d) s2) (by omega) ?_
        rintro x rfl
        exact ⟨by rw [DS.set_env_self]; simp only [Tm.eval, if_neg he],
          f.trans (TFr.set s2 _ le_rfl (by omega))⟩
  | eq a b iha ihb =>
      intro d s hc hd hs hok
      simp only [Tm.need] at hd
      have hd16 : d + 1 < 16 := by have := Tm.one_le_need b; omega
      obtain ⟨oa, ob⟩ := hok
      refine Hs.mono (pair_spec env a b d hd16 s hc hs (iha d s hc (by omega) hs oa)
        (fun s1 c1 h1 => ihb (d + 1) s1 c1 (by omega) h1 ob) _ 2 _ (fun s2 c2 r1 r2 f => ?_))
        (by simp only [Tm.cost]; omega) (fun x hx => hx)
      have hne : Rg d ≠ Rg (d + 1) := ne_of_val (by rw [Rg_val (by omega), Rg_val hd16]; omega)
      have hv1 : Rg d ≠ v1 := Rg_ne_low (by omega) (by decide)
      refine Hs.ite (C := C) hne (fun he => ?_) (fun he => ?_)
      · simp only [Cnd.eval, decide_eq_true_eq, r1, r2] at he
        refine Hs.mono (hs_copy C (Rg d) v1 s2 hv1) (by omega) ?_
        rintro x rfl
        exact ⟨by rw [DS.set_env_self, c2.one]; simp only [Tm.eval, if_pos he],
          f.trans (TFr.set s2 _ le_rfl (by omega))⟩
      · simp only [Cnd.eval, decide_eq_false_iff_not, r1, r2] at he
        refine Hs.mono (hs_zero C (Rg d) s2) (by omega) ?_
        rintro x rfl
        exact ⟨by rw [DS.set_env_self]; simp only [Tm.eval, if_neg he],
          f.trans (TFr.set s2 _ le_rfl (by omega))⟩
  | ite c a b ihc iha ihb =>
      intro d s hc hd hs hok
      simp only [Tm.need] at hd
      obtain ⟨oc, oa, ob⟩ := hok
      have hd16 : d < 16 := by have := Tm.one_le_need c; omega
      simp only [compT, Tm.cost]
      refine Hs.mono (Hs.seq (ihc d s hc (by omega) hs oc) (fun s1 h1 => ?_)) (t := c.cost + (a.cost + b.cost + 1) + 1)
        (by omega) (fun x hx => hx)
      obtain ⟨v1', f1⟩ := h1
      have hv : Rg d ≠ vZ := Rg_ne_low hd16 (by decide)
      have c1 := f1.cst hc
      refine Hs.ite (C := C) hv (fun he => ?_) (fun he => ?_)
      · simp only [Cnd.eval, decide_eq_true_eq, v1', c1.z] at he
        refine Hs.mono (ihb d s1 c1 (by omega) (f1.slots env hs) ob) (by omega) ?_
        rintro x ⟨r, f⟩
        exact ⟨by rw [r]; simp only [Tm.eval, if_pos he], f1.trans f⟩
      · simp only [Cnd.eval, decide_eq_false_iff_not, v1', c1.z] at he
        refine Hs.mono (iha d s1 c1 (by omega) (f1.slots env hs) oa) (by omega) ?_
        rintro x ⟨r, f⟩
        exact ⟨by rw [r]; simp only [Tm.eval, if_neg he], f1.trans f⟩

end NearCubicGates.Adapters.Compile.OraclePrint
