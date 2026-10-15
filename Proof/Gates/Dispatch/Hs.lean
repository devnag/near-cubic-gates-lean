import Proof.Gates.Dispatch.Lang

set_option autoImplicit false

namespace NearCubicGates.Close.Dispatch

/-- `simp` that also decides equalities of concrete variables (`Fin` literals behind definitions). -/
syntax "vsimp" " [" Lean.Parser.Tactic.simpLemma,* "]" (Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic| vsimp [$ls,*] $[$loc]?) =>
    `(tactic| simp (config := { decide := true }) [DS.set, $ls,*] $[$loc]?)

variable {V : ℕ} {C : Ctx}

/-- Hoare-style run statement with a step bound. -/
def Hs (C : Ctx) (s : St V) (a : DS V) (t : ℕ) (R : DS V → Prop) : Prop :=
  ∃ b n, Ex C s a b n ∧ n ≤ t ∧ R b

namespace Hs

theorem mono {s : St V} {a : DS V} {t t' : ℕ} {R R' : DS V → Prop} (h : Hs C s a t R) (ht : t ≤ t')
    (hR : ∀ b, R b → R' b) : Hs C s a t' R' := by
  obtain ⟨b, n, he, hn, hb⟩ := h
  exact ⟨b, n, he, le_trans hn ht, hR b hb⟩

theorem seq {s u : St V} {a : DS V} {t1 t2 : ℕ} {R1 R2 : DS V → Prop} (h1 : Hs C s a t1 R1)
    (h2 : ∀ b, R1 b → Hs C u b t2 R2) : Hs C (.seq s u) a (t1 + t2 + 1) R2 := by
  obtain ⟨b, n, he, hn, hb⟩ := h1
  obtain ⟨d, k, he2, hk, hd⟩ := h2 b hb
  exact ⟨d, n + k + 1, Ex.seq he he2, by omega, hd⟩

theorem op {o : Op V} {a b : DS V} {R : DS V → Prop} (h : OpEx C o a b) (hR : R b) : Hs C (.op o) a 1 R :=
  ⟨b, 1, Ex.op h, le_rfl, hR⟩

theorem iteT {c : Cnd V} {s u : St V} {a : DS V} {t : ℕ} {R : DS V → Prop} (hc : c.wf) (he : c.eval a = true)
    (h : Hs C s a t R) : Hs C (.ite c s u) a (t + 1) R := by
  obtain ⟨b, n, hx, hn, hb⟩ := h
  exact ⟨b, n + 1, Ex.iteT hc he hx, by omega, hb⟩

theorem iteF {c : Cnd V} {s u : St V} {a : DS V} {t : ℕ} {R : DS V → Prop} (hc : c.wf) (he : c.eval a = false)
    (h : Hs C u a t R) : Hs C (.ite c s u) a (t + 1) R := by
  obtain ⟨b, n, hx, hn, hb⟩ := h
  exact ⟨b, n + 1, Ex.iteF hc he hx, by omega, hb⟩

theorem ite {c : Cnd V} {s u : St V} {a : DS V} {t : ℕ} {R : DS V → Prop} (hc : c.wf)
    (h1 : c.eval a = true → Hs C s a t R) (h2 : c.eval a = false → Hs C u a t R) : Hs C (.ite c s u) a (t + 1) R := by
  cases he : c.eval a
  · exact iteF hc he (h2 he)
  · exact iteT hc he (h1 he)

/-- **Counted loop.** -/
theorem loopN {c : Cnd V} {s : St V} (hc : c.wf) (I : ℕ → DS V → Prop) (m t : ℕ)
    (hstep : ∀ k < m, ∀ a, I k a → c.eval a = true ∧ Hs C s a t (I (k + 1)))
    (hstop : ∀ a, I m a → c.eval a = false) :
    ∀ a, I 0 a → Hs C (.loop c s) a (m * (t + 2) + 2) (I m) := by
  have key : ∀ r j, j + r = m → ∀ a, I j a → Hs C (.loop c s) a (r * (t + 2) + 2) (I m) := by
    intro r
    induction r with
    | zero =>
      intro j hj a ha
      rw [Nat.add_zero] at hj; subst hj
      exact ⟨a, 2, Ex.loopF hc (hstop a ha), by omega, ha⟩
    | succ r ih =>
      intro j hj a ha
      obtain ⟨he, b, n, hx, hn, hb⟩ := hstep j (by omega) a ha
      obtain ⟨d, k, hx2, hk, hd⟩ := ih (j + 1) (by omega) b hb
      exact ⟨d, n + k + 2, Ex.loopT hc he hx hx2, by nlinarith, hd⟩
  intro a ha
  exact key m 0 (by omega) a ha

/-- Loop with a variable number of passes: the invariant carries a measure `μ` that drops each pass; the loop stops
when the test fails. -/
theorem loopM {c : Cnd V} {s : St V} (hc : c.wf) (I : DS V → Prop) (μ : DS V → ℕ) (t : ℕ)
    (hstep : ∀ a, I a → c.eval a = true → Hs C s a t (fun b => I b ∧ μ b < μ a)) :
    ∀ a, I a → Hs C (.loop c s) a (μ a * (t + 2) + 2) (fun b => I b ∧ c.eval b = false) := by
  have key : ∀ r a, μ a ≤ r → I a → Hs C (.loop c s) a (μ a * (t + 2) + 2) (fun b => I b ∧ c.eval b = false) := by
    intro r
    induction r with
    | zero =>
      intro a hμ ha
      cases he : c.eval a
      · exact ⟨a, 2, Ex.loopF hc he, by omega, ha, he⟩
      · obtain ⟨b, n, _, _, _, hlt⟩ := hstep a ha he
        omega
    | succ r ih =>
      intro a hμ ha
      cases he : c.eval a
      · exact ⟨a, 2, Ex.loopF hc he, by omega, ha, he⟩
      · obtain ⟨b, n, hx, hn, hb, hlt⟩ := hstep a ha he
        obtain ⟨d, k, hx2, hk, hd⟩ := ih b (by omega) hb
        refine ⟨d, n + k + 2, Ex.loopT hc he hx hx2, ?_, hd⟩
        have : μ b * (t + 2) + (t + 2) ≤ μ a * (t + 2) := by
          rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hlt
        omega
  intro a ha
  exact key (μ a) a le_rfl ha

end Hs

/-! ## Continuation style with counts as data -/

/-- `s` reaches from `a` a state `b` in `n` steps with `R b n`. -/
def Hx (C : Ctx) (s : St V) (a : DS V) (R : DS V → ℕ → Prop) : Prop := ∃ b n, Ex C s a b n ∧ R b n

/-- Sequencing: run a spec'd first part, then continue. -/
theorem Hs.then {s u : St V} {a : DS V} {t : ℕ} {R1 : DS V → Prop} {R : DS V → ℕ → Prop} (h1 : Hs C s a t R1)
    (h2 : ∀ b, R1 b → ∀ n, n ≤ t → Hx C u b (fun d k => R d (n + k + 1))) : Hx C (.seq s u) a R := by
  obtain ⟨b, n, he, hn, hb⟩ := h1
  obtain ⟨d, k, he2, hd⟩ := h2 b hb n hn
  exact ⟨d, n + k + 1, Ex.seq he he2, hd⟩

/-- The last part. -/
theorem Hs.last {s : St V} {a : DS V} {t : ℕ} {R1 : DS V → Prop} {R : DS V → ℕ → Prop} (h1 : Hs C s a t R1)
    (h2 : ∀ b, R1 b → ∀ n, n ≤ t → R b n) : Hx C s a R := by
  obtain ⟨b, n, he, hn, hb⟩ := h1
  exact ⟨b, n, he, h2 b hb n hn⟩

theorem Hx.hs {s : St V} {a : DS V} {t : ℕ} {R : DS V → Prop} (h : Hx C s a (fun b n => R b ∧ n ≤ t)) :
    Hs C s a t R := by
  obtain ⟨b, n, he, hb, hn⟩ := h
  exact ⟨b, n, he, hn, hb⟩

/-! ## Frames -/

/-- Every variable outside `T` is unchanged. -/
def Fr (a b : DS V) (T : List (Fin V)) : Prop := ∀ y, y ∉ T → b.env y = a.env y

theorem Fr.refl (a : DS V) (T : List (Fin V)) : Fr a a T := fun _ _ => rfl

theorem Fr.trans {a b d : DS V} {T : List (Fin V)} (h1 : Fr a b T) (h2 : Fr b d T) : Fr a d T :=
  fun y hy => (h2 y hy).trans (h1 y hy)

theorem Fr.weaken {a b : DS V} {T T' : List (Fin V)} (h : Fr a b T) (hT : ∀ y ∈ T, y ∈ T') : Fr a b T' :=
  fun y hy => h y (fun h' => hy (hT y h'))

theorem Fr.set (a : DS V) {x : Fin V} (v : ℕ) {T : List (Fin V)} (hx : x ∈ T) : Fr a (a.set x v) T := by
  intro y hy
  have : y ≠ x := fun e => hy (e ▸ hx)
  exact DS.set_env_ne a v this

/-! ## Single operations -/

section Ops
variable (C)

theorem hs_zero (x : Fin V) (a : DS V) : Hs C (.op (.zero x)) a 1 (· = a.set x 0) :=
  Hs.op (OpEx.zero x a) rfl

theorem hs_inc (x : Fin V) (a : DS V) (h : a.env x + 1 < 2 ^ C.Wd) :
    Hs C (.op (.inc x)) a 1 (· = a.set x (a.env x + 1)) := Hs.op (OpEx.inc x a h) rfl

theorem hs_add (x y : Fin V) (a : DS V) (hxy : x ≠ y) (h : a.env x + a.env y < 2 ^ C.Wd) :
    Hs C (.op (.add x y)) a 1 (· = a.set x (a.env x + a.env y)) := Hs.op (OpEx.add x y a hxy h) rfl

theorem hs_sub (x y : Fin V) (a : DS V) (hxy : x ≠ y) (h : a.env y ≤ a.env x) :
    Hs C (.op (.sub x y)) a 1 (· = a.set x (a.env x - a.env y)) := Hs.op (OpEx.sub x y a hxy h) rfl

theorem hs_copy (x y : Fin V) (a : DS V) (hxy : x ≠ y) :
    Hs C (.op (.copy x y)) a 1 (· = a.set x (a.env y)) := Hs.op (OpEx.copy x y a hxy) rfl

theorem hs_half (x : Fin V) (a : DS V) : Hs C (.op (.half x)) a 1 (· = a.set x (a.env x / 2)) :=
  Hs.op (OpEx.half x a) rfl

theorem hs_shl (x : Fin V) (a : DS V) (h : 2 * a.env x < 2 ^ C.Wd) :
    Hs C (.op (.shl x)) a 1 (· = a.set x (2 * a.env x)) := Hs.op (OpEx.shl x a h) rfl

theorem hs_mul (x y z : Fin V) (a : DS V) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (h : a.env x * a.env y < 2 ^ C.Wd) :
    Hs C (.op (.mul x y z)) a 1 (· = a.set z (a.env x * a.env y)) := Hs.op (OpEx.mul x y z a hxy hxz hyz h) rfl

theorem hs_dm (x y q r : Fin V) (a : DS V) (hxy : x ≠ y) (hxq : x ≠ q) (hxr : x ≠ r) (hyq : y ≠ q) (hyr : y ≠ r)
    (hqr : q ≠ r) (hy : 0 < a.env y) (h2 : 2 * a.env y ≤ 2 ^ C.Wd) :
    Hs C (.op (.dm x y q r)) a 1 (· = (a.set q (a.env x / a.env y)).set r (a.env x % a.env y)) :=
  Hs.op (OpEx.dm x y q r a hxy hxq hxr hyq hyr hqr hy h2) rfl

theorem hs_rdC (x : Fin V) (a : DS V) (h : a.cp < C.cw.length) :
    Hs C (.op (.rdC x)) a 1 (· = { a.set x (bitOf C.cw a.cp) with cp := a.cp + 1 }) := Hs.op (OpEx.rdC x a h) rfl

theorem hs_rstC (a : DS V) : Hs C (.op .rstC) a 1 (· = { a with cp := 0 }) := Hs.op (OpEx.rstC a) rfl

theorem hs_rdW (x : Fin V) (a : DS V) :
    Hs C (.op (.rdW x)) a 1
      (· = { a.set x (bitOf C.wit a.wq) with wq := if a.wq < C.wit.length then a.wq + 1 else a.wq }) :=
  Hs.op (OpEx.rdW x a) rfl

theorem hs_emit (b : Bool) (a : DS V) : Hs C (.op (.emit b)) a 1 (· = { a with out := a.out ++ [b] }) :=
  Hs.op (OpEx.emit b a) rfl

end Ops

end NearCubicGates.Close.Dispatch
