import SourceAdapters.Compile.OraclePrintMachine

/-!
# The template compiler of the oracle circuit printer

proof of `thm:short-pcp-ours`: the printer computes the circuit "in the standard way" in polynomial time; the expression families of
`OracleExpressions.requestCircuit` are generated at run time from their templates (`OraclePrintTemplate.U`). This
module compiles a template into ONE cell program (`compU`) and proves (`compU_spec`) that, from any state representing
the token machine, it runs exactly the template's tokens (`U.toks`), restores the bound-number registers, changes only
its scratch, and costs at most `(ucost u + tokCost L L + 20) · |tokens|` — linear in the number of emitted tokens.
-/

namespace NearCubicGates.Adapters.Compile.OraclePrint

open NearCubicWires NearCubicWires.Bindings.MW20 NearCubicGates.Close.Cells

set_option autoImplicit false

/-! ## Static data of a template -/

/-- Binding depth. -/
def U.depth : U → ℕ
  | .cst _ | .dat _ | .inp _ => 0
  | .not u => u.depth
  | .and u v | .or u v => max u.depth v.depth
  | .bigAnd _ body fin | .bigOr _ body fin => max body.depth fin.depth + 1
  | .ite _ u v => max u.depth v.depth
  | .lett _ body => body.depth + 1

/-- Largest register need of a term. -/
def U.tneed : U → ℕ
  | .cst c | .dat c | .inp c => c.need
  | .not u => u.tneed
  | .and u v | .or u v => max u.tneed v.tneed
  | .bigAnd n body fin | .bigOr n body fin => max n.need (max body.tneed fin.tneed)
  | .ite c u v => max c.need (max u.tneed v.tneed)
  | .lett t body => max t.need body.tneed

/-- Static cost overhead. -/
def U.ucost : U → ℕ
  | .cst c => c.cost + 10
  | .dat t => t.cost + 20
  | .inp t => t.cost + 10
  | .not u => u.ucost + 10
  | .and u v | .or u v => u.ucost + v.ucost + 10
  | .bigAnd n body fin | .bigOr n body fin => n.cost + body.ucost + fin.ucost + 30
  | .ite c u v => c.cost + u.ucost + v.ucost + 10
  | .lett t body => t.cost + body.ucost + 10

/-- Every term evaluated during the template's run has its values at most `V`. -/
def U.okV (V : ℕ) (D : List Bool) : List ℕ → U → Prop
  | env, .cst c => c.okV V env
  | env, .dat t => t.okV V env
  | env, .inp t => t.okV V env
  | env, .not u => u.okV V D env
  | env, .and u v | env, .or u v => u.okV V D env ∧ v.okV V D env
  | env, .bigAnd n body fin | env, .bigOr n body fin =>
      n.okV V env ∧ (∀ i < n.eval env, body.okV V D (env ++ [i])) ∧ fin.okV V D (env ++ [n.eval env])
  | env, .ite c u v => c.okV V env ∧ u.okV V D env ∧ v.okV V D env
  | env, .lett t body => t.okV V env ∧ body.okV V D (env ++ [t.eval env])

/-! ## Run bounds of the token machine -/

variable {n arity : ℕ}

theorem PS.step_cnt_le (w : List ℕ) (S : PS n arity) (t : Tok) : (S.step w t).cnt ≤ S.cnt + 1 := by
  cases t <;> simp [PS.step, PS.emit]

theorem PS.step_stk_le (w : List ℕ) (S : PS n arity) (t : Tok) : (S.step w t).stk.length ≤ S.stk.length + 1 := by
  cases t <;> simp [PS.step, PS.emit] <;> omega

theorem PS.run_cnt_le (w : List ℕ) (l : List Tok) : ∀ S : PS n arity, (S.run w l).cnt ≤ S.cnt + l.length := by
  induction l with
  | nil => intro S; simp
  | cons t l ih => intro S; have := ih (S.step w t); have := PS.step_cnt_le w S t; simp; omega

theorem PS.run_stk_le (w : List ℕ) (l : List Tok) :
    ∀ S : PS n arity, (S.run w l).stk.length ≤ S.stk.length + l.length := by
  induction l with
  | nil => intro S; simp
  | cons t l ih => intro S; have := ih (S.step w t); have := PS.step_stk_le w S t; simp; omega

theorem PS.run_replicate (w : List ℕ) (t : Tok) (k : ℕ) (S : PS n arity) :
    S.run w (List.replicate (k + 1) t) = (S.run w (List.replicate k t)).step w t := by
  rw [List.replicate_succ', PS.run_append]; rfl

theorem PS.run_flatMap_range (w : List ℕ) (f : ℕ → List Tok) (k : ℕ) (S : PS n arity) :
    S.run w ((List.range (k + 1)).flatMap f) = (S.run w ((List.range k).flatMap f)).run w (f k) := by
  rw [List.range_succ, List.flatMap_append, PS.run_append]; simp

/-! ## Frames of the compiler -/

/-- The compiler's scratch at level `ℓ`: evaluation registers, loop bounds from `ℓ`, machine registers. -/
def Scr (ℓ : ℕ) (y : ℕ) : Prop := (40 ≤ y ∧ y < 56) ∨ (80 + ℓ ≤ y ∧ y < 96) ∨ MachT y

/-- Stores whose cursors the compiler moves. -/
def CurM (m : ℕ) : Prop := m ≤ 3

theorem Scr.mono {ℓ : ℕ} {y : ℕ} (h : Scr (ℓ + 1) y) : Scr ℓ y := by
  unfold Scr MachT at *; omega

theorem keep_of_tfr {d ℓ : ℕ} {a b : DS VV MM} (h : TFr d a b) : Keep (Scr ℓ) MachR CurM a b :=
  ⟨fun y hy => h.env y (fun h' => hy (by unfold EvFrom at h'; unfold Scr; omega)),
    fun m _ => by rw [h.same.ram], fun m _ => by rw [h.same.rc], h.same.ip, h.same.out, h.same.kin, h.same.kout,
    h.same.kc⟩

theorem keep_of_mach {ℓ : ℕ} {a b : DS VV MM} (h : Keep MachT MachR MachM a b) : Keep (Scr ℓ) MachR CurM a b :=
  h.mono (fun y hy => by unfold Scr; exact Or.inr (Or.inr hy)) (fun _ h => h)
    (fun m hm => by unfold MachM at hm; unfold CurM; omega)

theorem Rep.of_tfr {w : List ℕ} {D : List Bool} {S : PS n arity} {d : ℕ} {a b : DS VV MM} (h : Rep w D S a)
    (k : TFr d a b) : Rep w D S b := by
  have hk : ∀ y : Fin VV, 56 ≤ y.val → b.env y = a.env y := fun y hy => k.env y (by unfold EvFrom; omega)
  obtain ⟨⟨c, cn, ns, nsc, wm, wl, wc, dsr, dl, dc⟩, s1, s2, s3⟩ := h
  exact ⟨⟨k.cst c, by rw [hk CNT (by simp), cn], by rw [k.same.ram, ns], by rw [k.same.rc, k.same.ram, nsc],
    by rw [k.same.ram, wm], by rw [hk WL (by simp), wl], by rw [k.same.rc]; exact wc, by rw [k.same.ram, dsr],
    by rw [hk DL (by simp), dl], by rw [k.same.rc]; exact dc⟩,
    by rw [hk HR (by simp), s1], by rw [k.same.rc, s2], by rw [k.same.ram, s3]⟩

/-! ## Hoare combinators with an accumulated cost -/

variable {C : Ctx}

theorem Hx.ofHs {s : St VV MM} {a : DS VV MM} {t : ℕ} {R : DS VV MM → Prop} (h : Hs C s a t R) :
    Hx C s a (fun b c => c ≤ t ∧ R b) := by
  obtain ⟨b, c, he, hc, hb⟩ := h
  exact ⟨b, c, he, hc, hb⟩

theorem Hx.seq' {s u : St VV MM} {a : DS VV MM} {R1 : DS VV MM → ℕ → Prop} {R : DS VV MM → ℕ → Prop}
    (h1 : Hx C s a R1) (h2 : ∀ b c, R1 b c → Hx C u b (fun d k => R d (c + k + 1))) : Hx C (.seq s u) a R := by
  obtain ⟨b, c, he, hb⟩ := h1
  obtain ⟨d, k, he2, hd⟩ := h2 b c hb
  exact ⟨d, c + k + 1, Ex.seq he he2, hd⟩

theorem Hx.mono' {s : St VV MM} {a : DS VV MM} {R R' : DS VV MM → ℕ → Prop} (h : Hx C s a R)
    (hR : ∀ b c, R b c → R' b c) : Hx C s a R' := by
  obtain ⟨b, c, he, hb⟩ := h
  exact ⟨b, c, he, hR b c hb⟩

theorem Hx.ite' {c : Cnd VV} {s u : St VV MM} {a : DS VV MM} {R : DS VV MM → ℕ → Prop} (hc : c.wf)
    (h1 : c.eval a = true → Hx C s a (fun b k => R b (k + 1)))
    (h2 : c.eval a = false → Hx C u a (fun b k => R b (k + 1))) : Hx C (.ite c s u) a R := by
  cases he : c.eval a
  · obtain ⟨b, k, hx, hb⟩ := h2 he
    exact ⟨b, k + 1, Ex.iteF hc he hx, hb⟩
  · obtain ⟨b, k, hx, hb⟩ := h1 he
    exact ⟨b, k + 1, Ex.iteT hc he hx, hb⟩

/-- **Counted loop with an accumulated cost.** -/
theorem Hx.loopAcc {c : Cnd VV} {s : St VV MM} (hc : c.wf) (I : ℕ → DS VV MM → ℕ → Prop) (m : ℕ)
    (hstep : ∀ k < m, ∀ a c0, I k a c0 → c.eval a = true ∧ Hx C s a (fun b c1 => I (k + 1) b (c0 + c1 + 2)))
    (hstop : ∀ a c0, I m a c0 → c.eval a = false) :
    ∀ a, I 0 a 0 → Hx C (.loop c s) a (fun b k => ∃ c0, I m b c0 ∧ k = c0 + 2) := by
  have key : ∀ r j, j + r = m → ∀ a c0, I j a c0 →
      ∃ b k cf, Ex C (.loop c s) a b k ∧ I m b cf ∧ c0 + k = cf + 2 := by
    intro r
    induction r with
    | zero =>
        intro j hj a c0 ha
        rw [Nat.add_zero] at hj; subst hj
        exact ⟨a, 2, c0, Ex.loopF hc (hstop a c0 ha), ha, rfl⟩
    | succ r ih =>
        intro j hj a c0 ha
        obtain ⟨he, b1, c1, hx1, hb1⟩ := hstep j (by omega) a c0 ha
        obtain ⟨b, k, cf, hx2, hb, hk⟩ := ih (j + 1) (by omega) b1 (c0 + c1 + 2) hb1
        exact ⟨b, c1 + k + 2, cf, Ex.loopT hc he hx1 hx2, hb, by omega⟩
  intro a ha
  obtain ⟨b, k, cf, hx, hb, hk⟩ := key m 0 (by omega) a 0 ha
  exact ⟨b, k, hx, cf, hb, by omega⟩

/-! ## The compiler -/

/-- `BV := [Rg 0 ≠ 0]`. -/
def setBV : St VV MM := .ite (.eq (Rg 0) vZ) (.op (.zero BV)) (.op (.copy BV v1))

/-- `BV := D[Rg 0]` (`0` past the end). -/
def datBV : St VV MM :=
  .ite (.lt (Rg 0) DL) (.seq (.op (.copy KX (Rg 0))) (.seq (seek DSt KX) (.op (.rdM DSt BV)))) (.op (.zero BV))

/-- A chain: the members at level `ℓ + 1` (`B`), the final member (`F`), then `n` operator tokens (`G`). -/
def bigP (ℓ : ℕ) (n : Tm) (B F G : St VV MM) : St VV MM :=
  .seq (compT n 0) (.seq (.op (.copy (Bd ℓ) (Rg 0))) (.seq (.op (.zero (Sl ℓ)))
    (.seq (.loop (.lt (Sl ℓ) (Bd ℓ)) (.seq B (.op (.inc (Sl ℓ)))))
      (.seq F (.seq (.op (.zero (Sl ℓ))) (.seq (.loop (.lt (Sl ℓ) (Bd ℓ)) (.seq G (.op (.inc (Sl ℓ)))))
        (.op (.zero (Sl ℓ)))))))))

/-- **The template compiler** (bound numbers of level `j` in `Sl j`). -/
def compU : ℕ → U → St VV MM
  | _, .cst c => .seq (compT c 0) (.seq setBV (execTok (.cst true)))
  | _, .dat t => .seq (compT t 0) (.seq datBV (execTok (.cst true)))
  | _, .inp t => .seq (compT t 0) (.seq (.op (.copy KX (Rg 0))) (execTok (.wir 0)))
  | ℓ, .not u => .seq (compU ℓ u) (execTok .neg)
  | ℓ, .and u v => .seq (compU ℓ u) (.seq (compU ℓ v) (execTok .conj))
  | ℓ, .or u v => .seq (compU ℓ u) (.seq (compU ℓ v) (execTok .disj))
  | ℓ, .bigAnd n body fin => bigP ℓ n (compU (ℓ + 1) body) (compU (ℓ + 1) fin) (execTok .conj)
  | ℓ, .bigOr n body fin => bigP ℓ n (compU (ℓ + 1) body) (compU (ℓ + 1) fin) (execTok .disj)
  | ℓ, .ite c u v => .seq (compT c 0) (.ite (.eq (Rg 0) vZ) (compU ℓ v) (compU ℓ u))
  | ℓ, .lett t body =>
      .seq (compT t 0) (.seq (.op (.copy (Sl ℓ) (Rg 0))) (.seq (compU (ℓ + 1) body) (.op (.zero (Sl ℓ)))))

/-- The per-token budget. -/
def Qc (L : ℕ) : ℕ := 40 * L + 120

/-- The run-wide side conditions. -/
structure Gk (C : Ctx) (w : List ℕ) (D : List Bool) (V L : ℕ) : Prop where
  hV : 2 * V + 2 ≤ 2 ^ C.Wd
  hV1 : 1 ≤ V
  hL : 2 * L + 2 ≤ 2 ^ C.Wd
  hw : w.length ≤ L
  hD : D.length ≤ L
  h8 : 8 ≤ 2 ^ C.Wd

/-- The specification of `compU ℓ u`. -/
def USpec (C : Ctx) (n arity : ℕ) (w : List ℕ) (D : List Bool) (V L : ℕ) (u : U) : Prop :=
  ∀ (ℓ : ℕ) (env : List ℕ) (S : PS n arity) (a : DS VV MM),
    env.length = ℓ → ℓ + u.depth ≤ 16 → u.tneed ≤ 16 → u.okV V D env →
    Rep w D S a → (∀ j < 16, a.env (Sl j) = env.getD j 0) →
    S.cnt + (u.toks D env).length ≤ L → S.stk.length + (u.toks D env).length ≤ L →
    Hx C (compU ℓ u) a (fun b c => Rep w D (S.run w (u.toks D env)) b ∧ Keep (Scr ℓ) MachR CurM a b ∧
      c ≤ (u.ucost + Qc L) * (u.toks D env).length)

theorem Keep.slots {ℓ : ℕ} {R M : ℕ → Prop} {a b : DS VV MM} (k : Keep (Scr ℓ) R M a b) (env : List ℕ)
    (hs : ∀ j < 16, a.env (Sl j) = env.getD j 0) : ∀ j < 16, b.env (Sl j) = env.getD j 0 := fun j hj => by
  rw [k.env (Sl j) (by rw [Sl_val hj]; unfold Scr MachT; omega), hs j hj]

theorem tokCost_le {L h wl : ℕ} (hh : h ≤ L) (hw : wl ≤ L) : tokCost h wl ≤ tokCost L L := by
  unfold tokCost; omega

/-- One token at the compiler level. -/
theorem tok_step {w : List ℕ} {D : List Bool} {V L : ℕ} (G : Gk C w D V L) (S : PS n arity) (tk : Tok)
    (a : DS VV MM) (h : Rep w D S a) (hreg : TokReg a tk) (h1 : S.cnt + 1 ≤ L) (h2 : S.stk.length + 1 ≤ L)
    (ℓ : ℕ) :
    Hx C (execTok tk) a (fun b c => c ≤ tokCost L L ∧ Rep w D (S.step w tk) b ∧ Keep (Scr ℓ) MachR CurM a b) := by
  have e := exec_spec w D S tk a h hreg (by have := G.hL; omega) (by have := G.hL; omega)
    (by have := G.hL; have := G.hw; omega) G.h8
  refine Hx.mono' (Hx.ofHs e) (fun b c ⟨hc, r, k⟩ => ⟨hc.trans (tokCost_le (by omega) G.hw), r, keep_of_mach k⟩)

/-- One term at the compiler level. -/
theorem term_step {w : List ℕ} {D : List Bool} {V L : ℕ} (G : Gk C w D V L) (env : List ℕ) (henv : env.length ≤ 16)
    (t : Tm) (ht : t.need ≤ 16) (hok : t.okV V env) (S : PS n arity) (a : DS VV MM) (h : Rep w D S a)
    (hs : ∀ j < 16, a.env (Sl j) = env.getD j 0) (ℓ : ℕ) :
    Hx C (compT t 0) a (fun b c => c ≤ t.cost ∧ b.env (Rg 0) = t.eval env ∧ Rep w D S b ∧
      Keep (Scr ℓ) MachR CurM a b) := by
  refine Hx.mono' (Hx.ofHs (compT_spec V G.hV G.hV1 env henv t 0 a h.base.cst (by omega) hs hok))
    (fun b c ⟨hc, r, k⟩ => ⟨hc, r, h.of_tfr k, keep_of_tfr k⟩)

theorem Rep.of_regs {w : List ℕ} {D : List Bool} {S : PS n arity} {T : ℕ → Prop} {a b : DS VV MM}
    (h : Rep w D S a) (k : Keep T (fun _ => False) (fun _ => False) a b)
    (hT : ∀ y, T y → 105 ≤ y ∨ (40 ≤ y ∧ y < 100)) : Rep w D S b := by
  have hk : ∀ y : Fin VV, y.val < 40 ∨ (100 ≤ y.val ∧ y.val < 105) → b.env y = a.env y :=
    fun y hy => k.env y (fun h' => by have := hT _ h'; omega)
  obtain ⟨⟨c, cn, ns, nsc, wm, wl, wc, dsr, dl, dc⟩, s1, s2, s3⟩ := h
  have cb : Cst b := ⟨by rw [hk vZ (by left; decide), c.z], by rw [hk v1 (by left; decide), c.one],
    by rw [hk v2 (by left; decide), c.two]⟩
  exact ⟨⟨cb, by rw [hk CNT (by simp), cn], by rw [k.ram NS id, ns], by rw [k.rc NS id, k.ram NS id, nsc],
    by rw [k.ram WM id, wm], by rw [hk WL (by simp), wl], by rw [k.rc WM id]; exact wc, by rw [k.ram DSt id, dsr],
    by rw [hk DL (by simp), dl], by rw [k.rc DSt id]; exact dc⟩,
    by rw [hk HR (by simp), s1], by rw [k.rc STK id, s2], by rw [k.ram STK id, s3]⟩

theorem run_single (w : List ℕ) (S : PS n arity) (t : Tok) : S.run w [t] = S.step w t := rfl

/-! ### Leaves -/

theorem cst_case {w : List ℕ} {D : List Bool} {V L : ℕ} (G : Gk C w D V L) (c : Tm) :
    USpec C n arity w D V L (.cst c) := by
  intro ℓ env S a hlen _ ht hok h hs h1 h2s
  simp only [U.toks, List.length_singleton] at h1 h2s ⊢
  simp only [U.tneed] at ht
  simp only [U.okV] at hok
  refine Hx.seq' (term_step G env (by omega) c ht hok S a h hs ℓ) (fun b1 c1 ⟨hc1, r1, h1', k1⟩ => ?_)
  have hbv : Hs C setBV b1 2 (fun b => b.env BV = (c.eval env != 0).toNat ∧
      Keep (· = 107) (fun _ => False) (fun _ => False) b1 b) := by
    refine Hs.ite (C := C) (Rg_ne_low (by omega) (by decide)) (fun he => ?_) (fun he => ?_)
    · simp only [Cnd.eval, decide_eq_true_eq, r1, h1'.base.cst.z] at he
      refine Hs.mono (hs_zero C BV b1) le_rfl ?_
      rintro x rfl
      exact ⟨by rw [DS.set_env_self, he]; rfl, Keep.set _ _ _ rfl⟩
    · simp only [Cnd.eval, decide_eq_false_iff_not, r1, h1'.base.cst.z] at he
      refine Hs.mono (hs_copy C BV v1 b1 (by decide)) le_rfl ?_
      rintro x rfl
      have hb : (c.eval env != 0) = true := bne_iff_ne.mpr he
      exact ⟨by rw [DS.set_env_self, h1'.base.cst.one, hb]; rfl, Keep.set _ _ _ rfl⟩
  refine Hx.seq' (Hx.ofHs hbv) (fun b2 c2 ⟨hc2, r2, k2⟩ => ?_)
  have h2 : Rep w D S b2 := h1'.of_regs k2 (fun y hy => by omega)
  have k2' : Keep (Scr ℓ) MachR CurM b1 b2 := k2.mono (fun y hy => by unfold Scr MachT; omega) (fun _ h => h.elim)
    (fun _ h => h.elim)
  refine Hx.mono' (tok_step G S (.cst (c.eval env != 0)) b2 h2 r2 (by omega) (by omega) ℓ)
    (fun b c3 ⟨hc3, r3, k3⟩ => ⟨r3, k1.trans (k2'.trans k3), ?_⟩)
  simp only [U.ucost, Qc, tokCost] at *
  omega

theorem inp_case {w : List ℕ} {D : List Bool} {V L : ℕ} (G : Gk C w D V L) (t : Tm) :
    USpec C n arity w D V L (.inp t) := by
  intro ℓ env S a hlen _ ht hok h hs h1 h2s
  simp only [U.toks, List.length_singleton] at h1 h2s ⊢
  simp only [U.tneed] at ht
  simp only [U.okV] at hok
  refine Hx.seq' (term_step G env (by omega) t ht hok S a h hs ℓ) (fun b1 c1 ⟨hc1, r1, h1', k1⟩ => ?_)
  refine Hx.seq' (Hx.ofHs (hs_copy C KX (Rg 0) b1 (by decide))) (fun b2 c2 ⟨hc2, hb2⟩ => ?_)
  subst hb2
  have k2 : Keep (· = 108) (fun _ => False) (fun _ => False) b1 (b1.set KX (b1.env (Rg 0))) := Keep.set _ _ _ rfl
  have h2 := h1'.of_regs k2 (fun y hy => by omega)
  have k2' : Keep (Scr ℓ) MachR CurM b1 (b1.set KX (b1.env (Rg 0))) :=
    k2.mono (fun y hy => by unfold Scr MachT; omega) (fun _ h => h.elim) (fun _ h => h.elim)
  refine Hx.mono' (tok_step G S (.wir (t.eval env)) _ h2 (by simp only [TokReg]; rw [DS.set_env_self, r1])
    (by omega) (by omega) ℓ) (fun b c3 ⟨hc3, r3, k3⟩ => ⟨r3, k1.trans (k2'.trans k3), ?_⟩)
  simp only [U.ucost, Qc, tokCost] at *
  omega

theorem getD_map_toNat (D : List Bool) (k : ℕ) : (D.map Bool.toNat).getD k 0 = (D.getD k false).toNat := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases D[k]? <;> rfl

theorem Rep.of_regsD {w : List ℕ} {D : List Bool} {S : PS n arity} {T : ℕ → Prop} {a b : DS VV MM}
    (h : Rep w D S a) (k : Keep T (fun _ => False) (· = 3) a b)
    (hT : ∀ y, T y → 105 ≤ y ∨ (40 ≤ y ∧ y < 100)) (hdc : b.rc DSt ≤ D.length) : Rep w D S b := by
  have hk : ∀ y : Fin VV, y.val < 40 ∨ (100 ≤ y.val ∧ y.val < 105) → b.env y = a.env y :=
    fun y hy => k.env y (fun h' => by have := hT _ h'; omega)
  obtain ⟨⟨c, cn, ns, nsc, wm, wl, wc, dsr, dl, dc⟩, s1, s2, s3⟩ := h
  have cb : Cst b := ⟨by rw [hk vZ (by left; decide), c.z], by rw [hk v1 (by left; decide), c.one],
    by rw [hk v2 (by left; decide), c.two]⟩
  exact ⟨⟨cb, by rw [hk CNT (by simp), cn], by rw [k.ram NS id, ns],
    by rw [k.rc NS (by simp), k.ram NS id, nsc], by rw [k.ram WM id, wm], by rw [hk WL (by simp), wl],
    by rw [k.rc WM (by simp)]; exact wc, by rw [k.ram DSt id, dsr], by rw [hk DL (by simp), dl], hdc⟩,
    by rw [hk HR (by simp), s1], by rw [k.rc STK (by simp), s2], by rw [k.ram STK id, s3]⟩

theorem dat_case {w : List ℕ} {D : List Bool} {V L : ℕ} (G : Gk C w D V L) (t : Tm) :
    USpec C n arity w D V L (.dat t) := by
  intro ℓ env S a hlen _ ht hok h hs h1 h2s
  simp only [U.toks, List.length_singleton] at h1 h2s ⊢
  simp only [U.tneed] at ht
  simp only [U.okV] at hok
  refine Hx.seq' (term_step G env (by omega) t ht hok S a h hs ℓ) (fun b1 c1 ⟨hc1, r1, h1', k1⟩ => ?_)
  have hDL := G.hD
  have hLW := G.hL
  have hdb : Hs C datBV b1 (6 * L + 12) (fun b => b.env BV = (D.getD (t.eval env) false).toNat ∧
      Keep (fun y => 105 ≤ y ∧ y ≤ 111) (fun _ => False) (· = 3) b1 b ∧ b.rc DSt ≤ D.length) := by
    refine Hs.ite (C := C) (ne_of_val (by rw [Rg_val (by omega)]; simp)) (fun he => ?_) (fun he => ?_)
    · simp only [Cnd.eval, decide_eq_true_eq, r1, h1'.base.dl] at he
      refine Hs.mono (t := 1 + ((b1.rc DSt + 5 * t.eval env + 6) + 1 + 1) + 1)
        (Hs.seq (hs_copy C KX (Rg 0) b1 (by decide)) (fun b2 hb2 => ?_)) (by have := h1'.base.dc; omega)
        (fun x hx => hx)
      subst hb2
      have hk2 : (b1.set KX (b1.env (Rg 0))).env KX = t.eval env := by rw [DS.set_env_self, r1]
      have hram : (b1.set KX (b1.env (Rg 0))).ram DSt = D.map Bool.toNat := h1'.base.dsr
      refine Hs.seq (t1 := b1.rc DSt + 5 * t.eval env + 6) (t2 := 1)
        (Hs.mono (seek_spec DSt KX (by unfold SkT; decide) _ (by rw [hk2, hram]; simp; omega)
        (by rw [hk2]; omega)) (by rw [hk2]; simp) (fun x hx => hx)) (fun b3 ⟨r3, k3⟩ => ?_)
      rw [hk2] at r3
      have hram3 : b3.ram DSt = D.map Bool.toNat := by rw [k3.ram DSt id, hram]
      refine Hs.mono (hs_rdM C DSt BV b3 (by rw [r3, hram3]; simp; omega)) le_rfl ?_
      rintro x rfl
      refine ⟨by simp only [DS.adv]; rw [DS.set_env_self, r3, hram3, getD_map_toNat], ?_,
        by simp [DS.adv, r3]; omega⟩
      refine (Keep.set (T := fun y => 105 ≤ y ∧ y ≤ 111) (R := fun _ => False) (M := (· = 3)) b1 KX _
        (by simp)).trans ((k3.mono (fun y hy => by unfold SkT at hy; omega) (fun _ h => h)
          (fun m hm => by simp at hm; exact hm)).trans ⟨fun y hy => ?_, fun _ _ => rfl, fun m hm => ?_,
            rfl, rfl, rfl, rfl, rfl⟩)
      · simp only [DS.adv]; exact DS.set_env_ne _ _ (neP (P := fun y => 105 ≤ y ∧ y ≤ 111) hy (by simp))
      · simp only [DS.adv, DS.set_rc]; exact Function.update_of_ne (neM (by simpa using hm)) _ _
    · simp only [Cnd.eval, decide_eq_false_iff_not, r1, h1'.base.dl, not_lt] at he
      refine Hs.mono (hs_zero C BV b1) (by omega) ?_
      rintro x rfl
      refine ⟨by rw [DS.set_env_self, List.getD_eq_default _ _ he]; rfl, Keep.set _ _ _ (by simp),
        h1'.base.dc⟩
  refine Hx.seq' (Hx.ofHs hdb) (fun b2 c2 ⟨hc2, r2, k2, d2⟩ => ?_)
  have h2 : Rep w D S b2 := h1'.of_regsD k2 (fun y hy => by omega) d2
  have k2' : Keep (Scr ℓ) MachR CurM b1 b2 :=
    k2.mono (fun y hy => by unfold Scr MachT; omega) (fun _ h => h.elim) (fun m hm => by unfold CurM; omega)
  refine Hx.mono' (tok_step G S (.cst (D.getD (t.eval env) false)) b2 h2 r2 (by omega) (by omega) ℓ)
    (fun b c3 ⟨hc3, r3, k3⟩ => ⟨r3, k1.trans (k2'.trans k3), ?_⟩)
  simp only [U.ucost, Qc, tokCost] at *
  omega

theorem cost_one {A T x y Q : ℕ} (hx : x ≤ A * T) (hy : y ≤ Q) (hQ : Q ≤ A) : x + y + 1 ≤ (A + 10) * (T + 1) := by
  nlinarith

theorem not_case {w : List ℕ} {D : List Bool} {V L : ℕ} (G : Gk C w D V L) (u : U)
    (ih : USpec C n arity w D V L u) : USpec C n arity w D V L (.not u) := by
  intro ℓ env S a hlen hd ht hok h hs h1 h2s
  simp only [U.toks, List.length_append, List.length_singleton] at h1 h2s ⊢
  simp only [U.depth] at hd
  simp only [U.tneed] at ht
  simp only [U.okV] at hok
  refine Hx.seq' (ih ℓ env S a hlen hd ht hok h hs (by omega) (by omega)) (fun b1 c1 ⟨r1, k1, hc1⟩ => ?_)
  have e1 := PS.run_cnt_le w (u.toks D env) S
  have e2 := PS.run_stk_le w (u.toks D env) S
  refine Hx.mono' (tok_step G _ .neg b1 r1 trivial (by omega) (by omega) ℓ)
    (fun b c2 ⟨hc2, r2, k2⟩ => ⟨by rw [PS.run_append]; exact r2, k1.trans k2, ?_⟩)
  have := cost_one hc1 (hc2.trans (show tokCost L L ≤ Qc L by unfold tokCost Qc; omega))
    (show Qc L ≤ u.ucost + Qc L by omega)
  simp only [U.ucost]
  calc c1 + c2 + 1 ≤ (u.ucost + Qc L + 10) * ((u.toks D env).length + 1) := this
    _ = (u.ucost + 10 + Qc L) * ((u.toks D env).length + 1) := by ring

theorem cost_two {a b T1 T2 x y z Q : ℕ} (hx : x ≤ (a + Q) * T1) (hy : y ≤ (b + Q) * T2) (hz : z ≤ Q) :
    x + (y + z + 1) + 1 ≤ (a + b + 10 + Q) * (T1 + T2 + 1) := by
  nlinarith

theorem bin_core {w : List ℕ} {D : List Bool} {V L : ℕ} (G : Gk C w D V L) (u v : U)
    (ihu : USpec C n arity w D V L u) (ihv : USpec C n arity w D V L v) (tk : Tok) (htk : ∀ a, TokReg a tk)
    (ℓ : ℕ) (env : List ℕ) (S : PS n arity) (a : DS VV MM) (hlen : env.length = ℓ)
    (hd : ℓ + max u.depth v.depth ≤ 16) (ht : max u.tneed v.tneed ≤ 16) (hok : u.okV V D env ∧ v.okV V D env)
    (h : Rep w D S a) (hs : ∀ j < 16, a.env (Sl j) = env.getD j 0)
    (h1 : S.cnt + ((u.toks D env).length + (v.toks D env).length + 1) ≤ L)
    (h2 : S.stk.length + ((u.toks D env).length + (v.toks D env).length + 1) ≤ L) :
    Hx C (.seq (compU ℓ u) (.seq (compU ℓ v) (execTok tk))) a (fun b c =>
      Rep w D (S.run w (u.toks D env ++ v.toks D env ++ [tk])) b ∧ Keep (Scr ℓ) MachR CurM a b ∧
      c ≤ (u.ucost + v.ucost + 10 + Qc L) * ((u.toks D env).length + (v.toks D env).length + 1)) := by
  refine Hx.seq' (ihu ℓ env S a hlen (by omega) (by omega) hok.1 h hs (by omega) (by omega))
    (fun b1 c1 ⟨r1, k1, hc1⟩ => ?_)
  have e1 := PS.run_cnt_le w (u.toks D env) S
  have e2 := PS.run_stk_le w (u.toks D env) S
  refine Hx.seq' (ihv ℓ env _ b1 hlen (by omega) (by omega) hok.2 r1 (k1.slots env hs) (by omega) (by omega))
    (fun b2 c2 ⟨r2, k2, hc2⟩ => ?_)
  have e3 := PS.run_cnt_le w (v.toks D env) (S.run w (u.toks D env))
  have e4 := PS.run_stk_le w (v.toks D env) (S.run w (u.toks D env))
  refine Hx.mono' (tok_step G _ tk b2 r2 (htk b2) (by omega) (by omega) ℓ)
    (fun b c3 ⟨hc3, r3, k3⟩ => ⟨by rw [PS.run_append, PS.run_append]; exact r3, k1.trans (k2.trans k3), ?_⟩)
  exact cost_two hc1 hc2 (hc3.trans (show tokCost L L ≤ Qc L by unfold tokCost Qc; omega))

theorem and_case {w : List ℕ} {D : List Bool} {V L : ℕ} (G : Gk C w D V L) (u v : U)
    (ihu : USpec C n arity w D V L u) (ihv : USpec C n arity w D V L v) : USpec C n arity w D V L (.and u v) := by
  intro ℓ env S a hlen hd ht hok h hs h1 h2s
  simp only [U.toks, List.length_append, List.length_singleton] at h1 h2s ⊢
  simp only [U.depth] at hd
  simp only [U.tneed] at ht
  simp only [U.okV] at hok
  simp only [U.ucost]
  exact bin_core G u v ihu ihv .conj (fun _ => trivial) ℓ env S a hlen hd ht hok h hs h1 h2s

theorem or_case {w : List ℕ} {D : List Bool} {V L : ℕ} (G : Gk C w D V L) (u v : U)
    (ihu : USpec C n arity w D V L u) (ihv : USpec C n arity w D V L v) : USpec C n arity w D V L (.or u v) := by
  intro ℓ env S a hlen hd ht hok h hs h1 h2s
  simp only [U.toks, List.length_append, List.length_singleton] at h1 h2s ⊢
  simp only [U.depth] at hd
  simp only [U.tneed] at ht
  simp only [U.okV] at hok
  simp only [U.ucost]
  exact bin_core G u v ihu ihv .disj (fun _ => trivial) ℓ env S a hlen hd ht hok h hs h1 h2s

theorem ite_case {w : List ℕ} {D : List Bool} {V L : ℕ} (G : Gk C w D V L) (c : Tm) (u v : U)
    (ihu : USpec C n arity w D V L u) (ihv : USpec C n arity w D V L v) :
    USpec C n arity w D V L (.ite c u v) := by
  intro ℓ env S a hlen hd ht hok h hs h1 h2s
  simp only [U.depth] at hd
  simp only [U.tneed] at ht
  simp only [U.okV] at hok
  obtain ⟨hc, hu, hv⟩ := hok
  refine Hx.seq' (term_step G env (by omega) c (by omega) hc S a h hs ℓ) (fun b1 c1 ⟨hc1, r1, h1', k1⟩ => ?_)
  refine Hx.ite' (Rg_ne_low (by omega) (by decide)) (fun he => ?_) (fun he => ?_)
  · simp only [Cnd.eval, decide_eq_true_eq, r1, h1'.base.cst.z] at he
    have ht' : U.toks D env (.ite c u v) = v.toks D env := by simp [U.toks, he]
    rw [ht'] at h1 h2s ⊢
    refine Hx.mono' (ihv ℓ env S b1 hlen (by omega) (by omega) hv h1' (k1.slots env hs) h1 h2s)
      (fun b c2 ⟨r2, k2, hc2⟩ => ⟨r2, k1.trans k2, ?_⟩)
    have hT := List.length_pos_of_ne_nil (U.toks_ne_nil D v env)
    simp only [U.ucost]
    nlinarith
  · simp only [Cnd.eval, decide_eq_false_iff_not, r1, h1'.base.cst.z] at he
    have ht' : U.toks D env (.ite c u v) = u.toks D env := by simp [U.toks, he]
    rw [ht'] at h1 h2s ⊢
    refine Hx.mono' (ihu ℓ env S b1 hlen (by omega) (by omega) hu h1' (k1.slots env hs) h1 h2s)
      (fun b c2 ⟨r2, k2, hc2⟩ => ⟨r2, k1.trans k2, ?_⟩)
    have hT := List.length_pos_of_ne_nil (U.toks_ne_nil D u env)
    simp only [U.ucost]
    nlinarith

/-! ### Bound-number slots -/

theorem getD_snoc (env : List ℕ) (x j : ℕ) :
    (env ++ [x]).getD j 0 = if j < env.length then env.getD j 0 else if j = env.length then x else 0 := by
  split_ifs with h1 h2
  · rw [List.getD_append _ _ _ _ h1]
  · subst h2; simp
  · rw [List.getD_eq_default _ _ (by simp; omega)]

theorem slots_set {b : DS VV MM} {env : List ℕ} {ℓ x : ℕ} (hlen : env.length = ℓ) (hl : ℓ < 16)
    (hs : ∀ j < 16, b.env (Sl j) = (env ++ [x]).getD j 0) (y : ℕ) :
    ∀ j < 16, (b.set (Sl ℓ) y).env (Sl j) = (env ++ [y]).getD j 0 := by
  intro j hj
  by_cases hjl : j = ℓ
  · subst hjl; rw [DS.set_env_self, getD_snoc]; simp [hlen]
  · rw [DS.set_env_ne _ _ (ne_of_val (by rw [Sl_val hj, Sl_val hl]; omega)), hs j hj, getD_snoc, getD_snoc]
    simp [hlen, hjl]

theorem slots_ext {b : DS VV MM} {env : List ℕ} {ℓ : ℕ} (hlen : env.length = ℓ)
    (hs : ∀ j < 16, b.env (Sl j) = env.getD j 0) : ∀ j < 16, b.env (Sl j) = (env ++ [0]).getD j 0 := by
  intro j hj
  rw [hs j hj, getD_snoc]
  split_ifs with h1 h2
  · rfl
  · rw [List.getD_eq_default _ _ (by omega)]
  · rw [List.getD_eq_default _ _ (by omega)]

theorem slots_drop {b : DS VV MM} {env : List ℕ} {ℓ : ℕ} (hlen : env.length = ℓ)
    (hs : ∀ j < 16, b.env (Sl j) = (env ++ [0]).getD j 0) : ∀ j < 16, b.env (Sl j) = env.getD j 0 := by
  intro j hj
  rw [hs j hj, getD_snoc]
  split_ifs with h1 h2
  · rfl
  · rw [List.getD_eq_default _ _ (by omega)]
  · rw [List.getD_eq_default _ _ (by omega)]

/-- A frame that also allowed `Sl ℓ`, once `Sl ℓ` is back. -/
theorem Keep.restore {ℓ : ℕ} {R M : ℕ → Prop} {a b : DS VV MM} (hl : ℓ < 16)
    (k : Keep (fun y => Scr ℓ y ∨ y = 64 + ℓ) R M a b) (hb : b.env (Sl ℓ) = a.env (Sl ℓ)) : Keep (Scr ℓ) R M a b :=
  ⟨fun y hy => by
    by_cases hyl : y = Sl ℓ
    · rw [hyl, hb]
    · exact k.env y (fun h => h.elim hy (fun e => hyl (Fin.ext (by rw [Sl_val hl]; exact e)))),
    k.ram, k.rc, k.ip, k.out, k.kin, k.kout, k.kc⟩

theorem keep_scrL {ℓ : ℕ} {R M : ℕ → Prop} {a b : DS VV MM} (k : Keep (Scr ℓ) R M a b) :
    Keep (fun y => Scr ℓ y ∨ y = 64 + ℓ) R M a b := k.mono (fun _ h => Or.inl h) (fun _ h => h) (fun _ h => h)

theorem keep_scrL1 {ℓ : ℕ} {R M : ℕ → Prop} {a b : DS VV MM} (k : Keep (Scr (ℓ + 1)) R M a b) :
    Keep (fun y => Scr ℓ y ∨ y = 64 + ℓ) R M a b := k.mono (fun _ h => Or.inl h.mono) (fun _ h => h) (fun _ h => h)

theorem keep_slot {ℓ : ℕ} (hl : ℓ < 16) (R M : ℕ → Prop) (a : DS VV MM) (v : ℕ) :
    Keep (fun y => Scr ℓ y ∨ y = 64 + ℓ) R M a (a.set (Sl ℓ) v) := Keep.set _ _ _ (Or.inr (Sl_val hl))

theorem lett_case {w : List ℕ} {D : List Bool} {V L : ℕ} (G : Gk C w D V L) (t : Tm) (body : U)
    (ihb : USpec C n arity w D V L body) : USpec C n arity w D V L (.lett t body) := by
  intro ℓ env S a hlen hd ht hok h hs h1 h2s
  simp only [U.depth] at hd
  simp only [U.tneed] at ht
  simp only [U.okV] at hok
  obtain ⟨hot, hob⟩ := hok
  simp only [U.toks] at h1 h2s ⊢
  have hl16 : ℓ < 16 := by omega
  refine Hx.seq' (term_step G env (by omega) t (by omega) hot S a h hs ℓ) (fun b1 c1 ⟨hc1, r1, h1', k1⟩ => ?_)
  have hne : Sl ℓ ≠ Rg 0 := ne_of_val (by rw [Sl_val hl16, Rg_val (by omega)]; omega)
  refine Hx.seq' (Hx.ofHs (hs_copy C (Sl ℓ) (Rg 0) b1 hne)) (fun b2 c2 ⟨hc2, hb2⟩ => ?_)
  subst hb2
  rw [r1]
  have hs2 := slots_set hlen hl16 (slots_ext hlen (k1.slots env hs)) (t.eval env)
  have h2 : Rep w D S (b1.set (Sl ℓ) (t.eval env)) :=
    h1'.of_regs (Keep.set (T := (· = 64 + ℓ)) (R := fun _ => False) (M := fun _ => False) _ _ _ (Sl_val hl16))
      (fun y hy => by omega)
  refine Hx.seq' (ihb (ℓ + 1) (env ++ [t.eval env]) S _ (by simp [hlen]) (by omega) (by omega) hob h2 hs2 h1 h2s)
    (fun b3 c3 ⟨r3, k3, hc3⟩ => ?_)
  refine Hx.mono' (Hx.ofHs (hs_zero C (Sl ℓ) b3)) (fun b4 c4 ⟨hc4, hb4⟩ => ?_)
  subst hb4
  have hz : (b3.set (Sl ℓ) 0).env (Sl ℓ) = a.env (Sl ℓ) := by
    rw [DS.set_env_self, hs ℓ hl16, List.getD_eq_default _ _ (by omega)]
  refine ⟨r3.of_regs (Keep.set (T := (· = 64 + ℓ)) (R := fun _ => False) (M := fun _ => False) _ _ _
    (Sl_val hl16)) (fun y hy => by omega), Keep.restore hl16 ((keep_scrL k1).trans ((keep_slot hl16 _ _ _ _).trans
      ((keep_scrL1 k3).trans (keep_slot hl16 _ _ _ _)))) hz, ?_⟩
  have hT := List.length_pos_of_ne_nil (U.toks_ne_nil D body (env ++ [t.eval env]))
  simp only [U.ucost]
  nlinarith

/-! ### Chains -/

theorem flat_le (f : ℕ → List Tok) {i N : ℕ} (h : i ≤ N) :
    ((List.range i).flatMap f).length ≤ ((List.range N).flatMap f).length := by
  induction N with
  | zero => have : i = 0 := by omega
            subst this; rfl
  | succ N ih =>
      rcases Nat.lt_or_ge i (N + 1) with h' | h'
      · rw [List.range_succ, List.flatMap_append, List.length_append]
        have := ih (by omega); omega
      · have : i = N + 1 := by omega
        subst this; rfl

theorem flat_succ_len (f : ℕ → List Tok) (i : ℕ) :
    ((List.range (i + 1)).flatMap f).length = ((List.range i).flatMap f).length + (f i).length := by
  rw [List.range_succ, List.flatMap_append]; simp

theorem big_cost {nc ub uf Q F Ft N c1 c2 c3 c0a c5 c6 c0b c8 : ℕ} (h1 : c1 ≤ nc) (h2 : c2 ≤ 1) (h3 : c3 ≤ 1)
    (ha : c0a ≤ (ub + Q) * F + 4 * N) (h5 : c5 ≤ (uf + Q) * Ft) (h6 : c6 ≤ 1) (hb : c0b ≤ (Q + 4) * N)
    (h8 : c8 ≤ 1) (hFt : 1 ≤ Ft) :
    c1 + (c2 + (c3 + ((c0a + 2) + (c5 + (c6 + ((c0b + 2) + c8 + 1) + 1) + 1) + 1) + 1) + 1) + 1 ≤
      (nc + ub + uf + 30 + Q) * (F + Ft + N) := by
  nlinarith

theorem big_core {w : List ℕ} {D : List Bool} {V L : ℕ} (G : Gk C w D V L) (nt : Tm) (body fin : U)
    (ihb : USpec C n arity w D V L body) (ihf : USpec C n arity w D V L fin) (tk : Tok) (htk : ∀ a, TokReg a tk)
    (ℓ : ℕ) (env : List ℕ) (S : PS n arity) (a : DS VV MM) (hlen : env.length = ℓ)
    (hd : ℓ + (max body.depth fin.depth + 1) ≤ 16) (ht : max nt.need (max body.tneed fin.tneed) ≤ 16)
    (hon : nt.okV V env) (hob : ∀ i < nt.eval env, body.okV V D (env ++ [i]))
    (hof : fin.okV V D (env ++ [nt.eval env])) (h : Rep w D S a) (hs : ∀ j < 16, a.env (Sl j) = env.getD j 0)
    (h1 : S.cnt + (((List.range (nt.eval env)).flatMap (fun i => body.toks D (env ++ [i]))).length +
      (fin.toks D (env ++ [nt.eval env])).length + nt.eval env) ≤ L)
    (h2 : S.stk.length + (((List.range (nt.eval env)).flatMap (fun i => body.toks D (env ++ [i]))).length +
      (fin.toks D (env ++ [nt.eval env])).length + nt.eval env) ≤ L) :
    Hx C (bigP ℓ nt (compU (ℓ + 1) body) (compU (ℓ + 1) fin) (execTok tk)) a (fun b c =>
      Rep w D (S.run w ((List.range (nt.eval env)).flatMap (fun i => body.toks D (env ++ [i])) ++
        fin.toks D (env ++ [nt.eval env]) ++ List.replicate (nt.eval env) tk)) b ∧ Keep (Scr ℓ) MachR CurM a b ∧
      c ≤ (nt.cost + body.ucost + fin.ucost + 30 + Qc L) *
        (((List.range (nt.eval env)).flatMap (fun i => body.toks D (env ++ [i]))).length +
          (fin.toks D (env ++ [nt.eval env])).length + nt.eval env)) := by
  have hl16 : ℓ < 16 := by omega
  set N := nt.eval env with hN
  set fb : ℕ → List Tok := fun i => body.toks D (env ++ [i]) with hfb
  set ft := fin.toks D (env ++ [N]) with hft
  have hNV : N ≤ V := Tm.eval_le_of_okV G.hV1 env nt hon
  have hVW := G.hV
  have hSB : Sl ℓ ≠ Bd ℓ := ne_of_val (by rw [Sl_val hl16, Bd_val hl16]; omega)
  have hBl : ¬ Scr (ℓ + 1) (Bd ℓ).val := by rw [Bd_val hl16]; unfold Scr MachT; omega
  -- the bound
  refine Hx.seq' (term_step G env (by omega) nt (by omega) hon S a h hs ℓ) (fun b1 c1 ⟨hc1, r1, h1', k1⟩ => ?_)
  have hBR : Bd ℓ ≠ Rg 0 := ne_of_val (by rw [Bd_val hl16, Rg_val (by omega)]; omega)
  refine Hx.seq' (Hx.ofHs (hs_copy C (Bd ℓ) (Rg 0) b1 hBR)) (fun b2 c2 ⟨hc2, hb2⟩ => ?_)
  subst hb2
  have kB : Keep (Scr ℓ) MachR CurM b1 (b1.set (Bd ℓ) (b1.env (Rg 0))) :=
    Keep.set _ _ _ (by unfold Scr; right; left; rw [Bd_val hl16]; omega)
  have h2' : Rep w D S (b1.set (Bd ℓ) (b1.env (Rg 0))) :=
    h1'.of_regs (Keep.set (T := (· = 80 + ℓ)) (R := fun _ => False) (M := fun _ => False) _ _ _ (Bd_val hl16))
      (fun y hy => by omega)
  -- the member counter
  refine Hx.seq' (Hx.ofHs (hs_zero C (Sl ℓ) _)) (fun b3 c3 ⟨hc3, hb3⟩ => ?_)
  subst hb3
  have hs3 := slots_set hlen hl16 (slots_ext hlen ((k1.trans kB).slots env hs)) 0
  have h3' := h2'.of_regs (Keep.set (T := (· = 64 + ℓ)) (R := fun _ => False) (M := fun _ => False) _ (Sl ℓ) 0
    (Sl_val hl16)) (fun y hy => by omega)
  have hB3 : ((b1.set (Bd ℓ) (b1.env (Rg 0))).set (Sl ℓ) 0).env (Bd ℓ) = N := by
    rw [DS.set_env_ne _ _ hSB.symm, DS.set_env_self, r1]
  have k3 := (keep_scrL k1).trans ((keep_scrL kB).trans (keep_slot hl16 MachR CurM _ 0))
  -- the members
  let I : ℕ → DS VV MM → ℕ → Prop := fun i b c0 =>
    Rep w D (S.run w ((List.range i).flatMap fb)) b ∧ b.env (Bd ℓ) = N ∧
    (∀ j < 16, b.env (Sl j) = (env ++ [i]).getD j 0) ∧ Keep (fun y => Scr ℓ y ∨ y = 64 + ℓ) MachR CurM a b ∧
    c0 ≤ (body.ucost + Qc L) * ((List.range i).flatMap fb).length + 4 * i
  have hflN : ((List.range N).flatMap fb).length + ft.length + N ≥ ((List.range N).flatMap fb).length := by omega
  have step1 : ∀ i < N, ∀ b c0, I i b c0 → Cnd.eval b (.lt (Sl ℓ) (Bd ℓ)) = true ∧
      Hx C (.seq (compU (ℓ + 1) body) (.op (.inc (Sl ℓ)))) b (fun b' c1 => I (i + 1) b' (c0 + c1 + 2)) := by
    intro i hi b c0 ⟨rb, hBb, hsb, kb, hcb⟩
    have hSl : b.env (Sl ℓ) = i := by rw [hsb ℓ hl16, getD_snoc]; simp [hlen]
    refine ⟨by simp [Cnd.eval, hSl, hBb, hi], ?_⟩
    have e1 := PS.run_cnt_le w ((List.range i).flatMap fb) S
    have e2 := PS.run_stk_le w ((List.range i).flatMap fb) S
    have hfl := flat_le fb (show i + 1 ≤ N by omega)
    have hsl := flat_succ_len fb i
    have hfbi : (fb i).length = (body.toks D (env ++ [i])).length := rfl
    rw [hfbi] at hsl
    refine Hx.seq' (ihb (ℓ + 1) (env ++ [i]) _ b (by simp [hlen]) (by omega) (by omega) (hob i hi) rb hsb
      (by omega) (by omega)) (fun b' c1 ⟨rb', kb', hc1⟩ => ?_)
    have hsb' := kb'.slots _ hsb
    have hSl' : b'.env (Sl ℓ) = i := by rw [hsb' ℓ hl16, getD_snoc]; simp [hlen]
    refine Hx.mono' (Hx.ofHs (hs_inc C (Sl ℓ) b' (by rw [hSl']; omega))) (fun b'' c2 ⟨hc2, hb''⟩ => ?_)
    subst hb''
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [PS.run_flatMap_range]
      exact rb'.of_regs (Keep.set (T := (· = 64 + ℓ)) (R := fun _ => False) (M := fun _ => False) _ (Sl ℓ) _
        (Sl_val hl16)) (fun y hy => by omega)
    · rw [DS.set_env_ne _ _ hSB.symm, kb'.env (Bd ℓ) hBl, hBb]
    · have := slots_set hlen hl16 hsb' (b'.env (Sl ℓ) + 1)
      rw [hSl'] at this ⊢
      exact this
    · exact kb.trans ((keep_scrL1 kb').trans (keep_slot hl16 MachR CurM _ _))
    · rw [hsl, Nat.mul_add]; omega
  have stop1 : ∀ b c0, I N b c0 → Cnd.eval b (.lt (Sl ℓ) (Bd ℓ)) = false := by
    intro b c0 ⟨_, hBb, hsb, _, _⟩
    have hSl : b.env (Sl ℓ) = N := by rw [hsb ℓ hl16, getD_snoc]; simp [hlen]
    simp [Cnd.eval, hSl, hBb]
  refine Hx.seq' (Hx.loopAcc (show Cnd.wf (.lt (Sl ℓ) (Bd ℓ)) from hSB) I N step1 stop1 _ ⟨h3', hB3, hs3, k3, by simp⟩)
    (fun b4 c4 ⟨c0a, ⟨r4, hB4, hs4, k4, hc0a⟩, hc4⟩ => ?_)
  -- the final member
  have e1 := PS.run_cnt_le w ((List.range N).flatMap fb) S
  have e2 := PS.run_stk_le w ((List.range N).flatMap fb) S
  have hftl : (fin.toks D (env ++ [N])).length = ft.length := rfl
  refine Hx.seq' (ihf (ℓ + 1) (env ++ [N]) _ b4 (by simp [hlen]) (by omega) (by omega) hof r4 hs4
    (by omega) (by omega)) (fun b5 c5 ⟨r5, k5, hc5⟩ => ?_)
  have hs5 := k5.slots _ hs4
  have hB5 : b5.env (Bd ℓ) = N := by rw [k5.env (Bd ℓ) hBl, hB4]
  refine Hx.seq' (Hx.ofHs (hs_zero C (Sl ℓ) b5)) (fun b6 c6 ⟨hc6, hb6⟩ => ?_)
  subst hb6
  have hs6 := slots_set hlen hl16 hs5 0
  have r6 := r5.of_regs (Keep.set (T := (· = 64 + ℓ)) (R := fun _ => False) (M := fun _ => False) _ (Sl ℓ) 0
    (Sl_val hl16)) (fun y hy => by omega)
  have hB6 : (b5.set (Sl ℓ) 0).env (Bd ℓ) = N := by rw [DS.set_env_ne _ _ hSB.symm, hB5]
  have k6 := k4.trans ((keep_scrL1 k5).trans (keep_slot hl16 MachR CurM _ 0))
  -- the operators
  set S' := (S.run w ((List.range N).flatMap fb)).run w ft with hS'
  have e3 : S'.cnt ≤ (S.run w ((List.range N).flatMap fb)).cnt + ft.length :=
    PS.run_cnt_le w ft (S.run w ((List.range N).flatMap fb))
  have e4 : S'.stk.length ≤ (S.run w ((List.range N).flatMap fb)).stk.length + ft.length :=
    PS.run_stk_le w ft (S.run w ((List.range N).flatMap fb))
  let J : ℕ → DS VV MM → ℕ → Prop := fun i b c0 =>
    Rep w D (S'.run w (List.replicate i tk)) b ∧ b.env (Bd ℓ) = N ∧
    (∀ j < 16, b.env (Sl j) = (env ++ [i]).getD j 0) ∧ Keep (fun y => Scr ℓ y ∨ y = 64 + ℓ) MachR CurM a b ∧
    c0 ≤ (Qc L + 4) * i
  have step2 : ∀ i < N, ∀ b c0, J i b c0 → Cnd.eval b (.lt (Sl ℓ) (Bd ℓ)) = true ∧
      Hx C (.seq (execTok tk) (.op (.inc (Sl ℓ)))) b (fun b' c1 => J (i + 1) b' (c0 + c1 + 2)) := by
    intro i hi b c0 ⟨rb, hBb, hsb, kb, hcb⟩
    have hSl : b.env (Sl ℓ) = i := by rw [hsb ℓ hl16, getD_snoc]; simp [hlen]
    refine ⟨by simp [Cnd.eval, hSl, hBb, hi], ?_⟩
    have e5 := PS.run_cnt_le w (List.replicate i tk) S'
    have e6 := PS.run_stk_le w (List.replicate i tk) S'
    simp only [List.length_replicate] at e5 e6
    refine Hx.seq' (tok_step G _ tk b rb (htk b) (by omega) (by omega) (ℓ + 1)) (fun b' c1 ⟨hce, rb', kb'⟩ => ?_)
    have hsb' := kb'.slots _ hsb
    have hSl' : b'.env (Sl ℓ) = i := by rw [hsb' ℓ hl16, getD_snoc]; simp [hlen]
    refine Hx.mono' (Hx.ofHs (hs_inc C (Sl ℓ) b' (by rw [hSl']; omega))) (fun b'' c2 ⟨hc2, hb''⟩ => ?_)
    subst hb''
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [PS.run_replicate]
      exact rb'.of_regs (Keep.set (T := (· = 64 + ℓ)) (R := fun _ => False) (M := fun _ => False) _ (Sl ℓ) _
        (Sl_val hl16)) (fun y hy => by omega)
    · rw [DS.set_env_ne _ _ hSB.symm, kb'.env (Bd ℓ) hBl, hBb]
    · have := slots_set hlen hl16 hsb' (b'.env (Sl ℓ) + 1)
      rw [hSl'] at this ⊢
      exact this
    · exact kb.trans ((keep_scrL1 kb').trans (keep_slot hl16 MachR CurM _ _))
    · have : tokCost L L ≤ Qc L := by unfold tokCost Qc; omega
      rw [Nat.mul_add]; omega
  have stop2 : ∀ b c0, J N b c0 → Cnd.eval b (.lt (Sl ℓ) (Bd ℓ)) = false := by
    intro b c0 ⟨_, hBb, hsb, _, _⟩
    have hSl : b.env (Sl ℓ) = N := by rw [hsb ℓ hl16, getD_snoc]; simp [hlen]
    simp [Cnd.eval, hSl, hBb]
  refine Hx.seq' (Hx.loopAcc (show Cnd.wf (.lt (Sl ℓ) (Bd ℓ)) from hSB) J N step2 stop2 _ ⟨by simpa using r6, hB6, hs6, k6, by simp⟩)
    (fun b7 c7 ⟨c0b, ⟨r7, hB7, hs7, k7, hc0b⟩, hc7⟩ => ?_)
  refine Hx.mono' (Hx.ofHs (hs_zero C (Sl ℓ) b7)) (fun b8 c8 ⟨hc8, hb8⟩ => ?_)
  subst hb8
  have hz : (b7.set (Sl ℓ) 0).env (Sl ℓ) = a.env (Sl ℓ) := by
    rw [DS.set_env_self, hs ℓ hl16, List.getD_eq_default _ _ (by omega)]
  refine ⟨?_, Keep.restore hl16 (k7.trans (keep_slot hl16 MachR CurM _ 0)) hz, ?_⟩
  · rw [PS.run_append, PS.run_append]
    exact r7.of_regs (Keep.set (T := (· = 64 + ℓ)) (R := fun _ => False) (M := fun _ => False) _ (Sl ℓ) 0
      (Sl_val hl16)) (fun y hy => by omega)
  · have hFt := List.length_pos_of_ne_nil (U.toks_ne_nil D fin (env ++ [N]))
    subst hc4 hc7
    exact big_cost hc1 hc2 hc3 hc0a hc5 hc6 hc0b hc8 hFt

theorem bigAnd_case {w : List ℕ} {D : List Bool} {V L : ℕ} (G : Gk C w D V L) (nt : Tm) (body fin : U)
    (ihb : USpec C n arity w D V L body) (ihf : USpec C n arity w D V L fin) :
    USpec C n arity w D V L (.bigAnd nt body fin) := by
  intro ℓ env S a hlen hd ht hok h hs h1 h2s
  simp only [U.toks, List.length_append, List.length_replicate] at h1 h2s ⊢
  simp only [U.depth] at hd
  simp only [U.tneed] at ht
  simp only [U.okV] at hok
  simp only [U.ucost]
  exact big_core G nt body fin ihb ihf .conj (fun _ => trivial) ℓ env S a hlen hd ht hok.1 hok.2.1 hok.2.2 h hs
    h1 h2s

theorem bigOr_case {w : List ℕ} {D : List Bool} {V L : ℕ} (G : Gk C w D V L) (nt : Tm) (body fin : U)
    (ihb : USpec C n arity w D V L body) (ihf : USpec C n arity w D V L fin) :
    USpec C n arity w D V L (.bigOr nt body fin) := by
  intro ℓ env S a hlen hd ht hok h hs h1 h2s
  simp only [U.toks, List.length_append, List.length_replicate] at h1 h2s ⊢
  simp only [U.depth] at hd
  simp only [U.tneed] at ht
  simp only [U.okV] at hok
  simp only [U.ucost]
  exact big_core G nt body fin ihb ihf .disj (fun _ => trivial) ℓ env S a hlen hd ht hok.1 hok.2.1 hok.2.2 h hs
    h1 h2s

/-- **The template compiler is correct**: for every template `u`, `compU ℓ u` runs exactly the tokens
`u.toks D env` on the represented token machine, restores the bound-number registers, changes only its scratch,
and costs at most `(u.ucost + Qc L) · |u.toks D env|`. -/
theorem compU_spec {w : List ℕ} {D : List Bool} {V L : ℕ} (G : Gk C w D V L) :
    ∀ u : U, USpec C n arity w D V L u := by
  intro u
  induction u with
  | cst c => exact cst_case G c
  | dat t => exact dat_case G t
  | inp t => exact inp_case G t
  | not u ih => exact not_case G u ih
  | and u v ihu ihv => exact and_case G u v ihu ihv
  | or u v ihu ihv => exact or_case G u v ihu ihv
  | bigAnd nt body fin ihb ihf => exact bigAnd_case G nt body fin ihb ihf
  | bigOr nt body fin ihb ihf => exact bigOr_case G nt body fin ihb ihf
  | ite c u v ihu ihv => exact ite_case G c u v ihu ihv
  | lett t body ih => exact lett_case G t body ih

end NearCubicGates.Adapters.Compile.OraclePrint
