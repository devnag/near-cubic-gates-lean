import Proof.Gates.Cells.Lang

set_option autoImplicit false

namespace NearCubicGates.Close.Cells

/-- `simp` that also decides equalities of concrete variables (`Fin` literals behind definitions). -/
syntax "vsimp" " [" Lean.Parser.Tactic.simpLemma,* "]" (Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic| vsimp [$ls,*] $[$loc]?) =>
    `(tactic| simp (config := { decide := true }) [DS.set, $ls,*] $[$loc]?)

variable {V M : ℕ} {C : Ctx}

/-- Hoare-style run statement with a cost bound. -/
def Hs (C : Ctx) (s : St V M) (a : DS V M) (t : ℕ) (R : DS V M → Prop) : Prop :=
  ∃ b n, Ex C s a b n ∧ n ≤ t ∧ R b

namespace Hs

theorem mono {s : St V M} {a : DS V M} {t t' : ℕ} {R R' : DS V M → Prop} (h : Hs C s a t R) (ht : t ≤ t')
    (hR : ∀ b, R b → R' b) : Hs C s a t' R' := by
  obtain ⟨b, n, he, hn, hb⟩ := h
  exact ⟨b, n, he, le_trans hn ht, hR b hb⟩

theorem seq {s u : St V M} {a : DS V M} {t1 t2 : ℕ} {R1 R2 : DS V M → Prop} (h1 : Hs C s a t1 R1)
    (h2 : ∀ b, R1 b → Hs C u b t2 R2) : Hs C (.seq s u) a (t1 + t2 + 1) R2 := by
  obtain ⟨b, n, he, hn, hb⟩ := h1
  obtain ⟨d, k, he2, hk, hd⟩ := h2 b hb
  exact ⟨d, n + k + 1, Ex.seq he he2, by omega, hd⟩

theorem op {o : Op V M} {a b : DS V M} {k : ℕ} {R : DS V M → Prop} (h : OpEx C o a b k) (hR : R b) :
    Hs C (.op o) a k R :=
  ⟨b, k, Ex.op h, le_rfl, hR⟩

theorem iteT {c : Cnd V} {s u : St V M} {a : DS V M} {t : ℕ} {R : DS V M → Prop} (hc : c.wf)
    (he : c.eval a = true) (h : Hs C s a t R) : Hs C (.ite c s u) a (t + 1) R := by
  obtain ⟨b, n, hx, hn, hb⟩ := h
  exact ⟨b, n + 1, Ex.iteT hc he hx, by omega, hb⟩

theorem iteF {c : Cnd V} {s u : St V M} {a : DS V M} {t : ℕ} {R : DS V M → Prop} (hc : c.wf)
    (he : c.eval a = false) (h : Hs C u a t R) : Hs C (.ite c s u) a (t + 1) R := by
  obtain ⟨b, n, hx, hn, hb⟩ := h
  exact ⟨b, n + 1, Ex.iteF hc he hx, by omega, hb⟩

theorem ite {c : Cnd V} {s u : St V M} {a : DS V M} {t : ℕ} {R : DS V M → Prop} (hc : c.wf)
    (h1 : c.eval a = true → Hs C s a t R) (h2 : c.eval a = false → Hs C u a t R) :
    Hs C (.ite c s u) a (t + 1) R := by
  cases he : c.eval a
  · exact iteF hc he (h2 he)
  · exact iteT hc he (h1 he)

/-- **Counted loop.** -/
theorem loopN {c : Cnd V} {s : St V M} (hc : c.wf) (I : ℕ → DS V M → Prop) (m t : ℕ)
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

/-- **Counted loop with a per-pass cost.** -/
theorem loopNc {c : Cnd V} {s : St V M} (hc : c.wf) (I : ℕ → DS V M → Prop) (m : ℕ) (t : ℕ → ℕ)
    (hstep : ∀ k < m, ∀ a, I k a → c.eval a = true ∧ Hs C s a (t k) (I (k + 1)))
    (hstop : ∀ a, I m a → c.eval a = false) :
    ∀ a, I 0 a → Hs C (.loop c s) a ((∑ k ∈ Finset.range m, (t k + 2)) + 2) (I m) := by
  have key : ∀ r j, j + r = m → ∀ a, I j a →
      Hs C (.loop c s) a ((∑ k ∈ Finset.Ico j m, (t k + 2)) + 2) (I m) := by
    intro r
    induction r with
    | zero =>
      intro j hj a ha
      rw [Nat.add_zero] at hj; subst hj
      exact ⟨a, 2, Ex.loopF hc (hstop a ha), by simp, ha⟩
    | succ r ih =>
      intro j hj a ha
      obtain ⟨he, b, n, hx, hn, hb⟩ := hstep j (by omega) a ha
      obtain ⟨d, k, hx2, hk, hd⟩ := ih (j + 1) (by omega) b hb
      refine ⟨d, n + k + 2, Ex.loopT hc he hx hx2, ?_, hd⟩
      rw [Finset.sum_eq_sum_Ico_succ_bot (by omega)]
      omega
  intro a ha
  have := key m 0 (by omega) a ha
  rwa [Finset.range_eq_Ico]

/-- Loop with a variable number of passes: the invariant carries a measure `μ` that drops each pass; the loop stops
when the test fails. -/
theorem loopM {c : Cnd V} {s : St V M} (hc : c.wf) (I : DS V M → Prop) (μ : DS V M → ℕ) (t : ℕ)
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

/-! ## Frames -/

/-- Every variable outside `T` is unchanged. -/
def Fr (a b : DS V M) (T : List (Fin V)) : Prop := ∀ y, y ∉ T → b.env y = a.env y

theorem Fr.refl (a : DS V M) (T : List (Fin V)) : Fr a a T := fun _ _ => rfl

theorem Fr.trans {a b d : DS V M} {T : List (Fin V)} (h1 : Fr a b T) (h2 : Fr b d T) : Fr a d T :=
  fun y hy => (h2 y hy).trans (h1 y hy)

theorem Fr.weaken {a b : DS V M} {T T' : List (Fin V)} (h : Fr a b T) (hT : ∀ y ∈ T, y ∈ T') : Fr a b T' :=
  fun y hy => h y (fun h' => hy (hT y h'))

theorem Fr.set (a : DS V M) {x : Fin V} (v : ℕ) {T : List (Fin V)} (hx : x ∈ T) : Fr a (a.set x v) T := by
  intro y hy
  have : y ≠ x := fun e => hy (e ▸ hx)
  exact DS.set_env_ne a v this

/-- The non-variable components agree. -/
structure Same (a b : DS V M) : Prop where
  ip : b.ip = a.ip
  out : b.out = a.out
  ram : b.ram = a.ram
  rc : b.rc = a.rc
  kin : b.kin = a.kin
  kout : b.kout = a.kout
  kc : b.kc = a.kc

theorem Same.refl (a : DS V M) : Same a a := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
theorem Same.trans {a b d : DS V M} (h1 : Same a b) (h2 : Same b d) : Same a d :=
  ⟨h2.ip.trans h1.ip, h2.out.trans h1.out, h2.ram.trans h1.ram, h2.rc.trans h1.rc, h2.kin.trans h1.kin,
    h2.kout.trans h1.kout, h2.kc.trans h1.kc⟩
theorem Same.set (a : DS V M) (x : Fin V) (v : ℕ) : Same a (a.set x v) := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end NearCubicGates.Close.Cells
