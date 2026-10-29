import SourceAdapters.ShortPCP.Machines.FLangOps

/-!
# Single-run time, machine layer 6: the compiler from `FL` to the cell language

`compE e d` evaluates the expression `e` into temporary `d`; `compS p d` runs the statement `p` at loop depth `d`
(loop counters and bounds of depth `d` in registers `32 + 2d`, `33 + 2d`). The theorem `compS_ok` says: from a cell
state related to an `FL` state `s` (`Rel`: the program variables, the output and the fixed registers agree), the
compiled program runs within `costS G p` units to a cell state related to `evalS G p s`, without touching the input
position, the stores or the call registers. With `costS_le` (`FLang.lean`) this is the time bound of proof of `thm:short-pcp-ours`
for every program written in `FL`: polynomial in the clamp exponent `K` and the pass bound `N`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicGates.Adapters.ShortPCP.Machines.FL

open NearCubicGates.Close.Cells NearCubicWires.WireExponent3_5
open NearCubicGates.Adapters.Joins NearCubicGates.Adapters.Joins.FieldCells

/-! ## Values stay below the clamp -/

theorem evalE_le {G : Glob} {s : FS} (hK : 3 ≤ G.K) (hs : ∀ i, s.env i ≤ G.cap) (fok : fieldOk G s.fl s.fp = true) :
    ∀ e : E, evalE G s e ≤ G.cap
  | .v i => hs i
  | .k n => min_le_right _ _
  | .gk => by have := K_le_cap G hK; simp only [evalE]; omega
  | .add a b | .mul a b | .shl a b => min_le_right _ _
  | .sub a b => (Nat.sub_le _ _).trans (evalE_le hK hs fok a)
  | .div a b => (Nat.div_le_self _ _).trans (evalE_le hK hs fok a)
  | .md a b => (Nat.mod_le _ _).trans (evalE_le hK hs fok a)
  | .shr a b => (Nat.div_le_self _ _).trans (evalE_le hK hs fok a)
  | .bxor a b => by
    have := cap_add G; have := Nat.mod_lt (evalE G s a ^^^ evalE G s b) (Nat.two_pow_pos G.K)
    simp only [evalE]; omega
  | .fadd a b => by
    have := tf_le fok; have := Nat.mod_lt (evalE G s a ^^^ evalE G s b) (Nat.two_pow_pos s.fl)
    simp only [evalE]; omega
  | .fmul a b => by have := tf_le fok; have := redW_lt s.fp s.fl (GF.toPoly (evalE G s a % 2 ^ s.fl) *
      GF.toPoly (evalE G s b % 2 ^ s.fl)); simp only [evalE, mulW]; omega
  | .fpow a b => by have := tf_le fok; have := redW_lt s.fp s.fl (GF.toPoly (evalE G s a % 2 ^ s.fl) ^ evalE G s b)
                    simp only [evalE, powW]; omega
  | .finv a => by have := tf_le fok; have := redW_lt s.fp s.fl (GF.toPoly (evalE G s a % 2 ^ s.fl) ^ (2 ^ s.fl - 2))
                  simp only [evalE, powW]; omega
  | .lt a b | .eq a b => by
    have := K_le_cap G hK; simp only [evalE]; split_ifs <;> omega

/-! ## Expressions -/

/-- Temporaries used beyond the target. -/
def dE : E → ℕ
  | .v _ | .k _ | .gk => 0
  | .finv a => dE a
  | .add a b | .sub a b | .mul a b | .div a b | .md a b | .shl a b | .shr a b | .bxor a b | .fadd a b
  | .fmul a b | .fpow a b | .lt a b | .eq a b => max (dE a) (dE b + 1)

/-- A binary operation: both operands, then the macro on temporaries `d`, `d + 1`. -/
def binC (m : Fin VV → Fin VV → St VV MM) (ca cb : St VV MM) (d : ℕ) : St VV MM :=
  .seq ca (.seq cb (m (tmp d) (tmp (d + 1))))

/-- **The expression compiler.** -/
def compE : E → ℕ → St VV MM
  | .v i, d => .op (.copy (tmp d) (uv i))
  | .k n, d => .seq (.op (.zero (tmp d))) (incK n (tmp d))
  | .gk, d => .op (.copy (tmp d) kR)
  | .add a b, d => binC addM (compE a d) (compE b (d + 1)) d
  | .sub a b, d => binC subM (compE a d) (compE b (d + 1)) d
  | .mul a b, d => binC mulM (compE a d) (compE b (d + 1)) d
  | .div a b, d => binC divM (compE a d) (compE b (d + 1)) d
  | .md a b, d => binC mdM (compE a d) (compE b (d + 1)) d
  | .shl a b, d => binC shlM (compE a d) (compE b (d + 1)) d
  | .shr a b, d => binC shrM (compE a d) (compE b (d + 1)) d
  | .bxor a b, d => binC bxorM (compE a d) (compE b (d + 1)) d
  | .fadd a b, d => binC faddM (compE a d) (compE b (d + 1)) d
  | .fmul a b, d => binC fmulM (compE a d) (compE b (d + 1)) d
  | .fpow a b, d => binC fpowM (compE a d) (compE b (d + 1)) d
  | .lt a b, d => binC ltM (compE a d) (compE b (d + 1)) d
  | .eq a b, d => binC eqM (compE a d) (compE b (d + 1)) d
  | .finv a, d => .seq (compE a d) (finvM (tmp d))

/-- After an expression: the target holds the value; only scratch and temporaries `≥ d` changed. -/
structure EPost (d v : ℕ) (a b : DS VV MM) : Prop where
  val : b.env (tmp d) = v
  sh : b.sh = a.sh
  env : ∀ z, ¬ Scr z → ¬ (16 + d ≤ z.val ∧ z.val < 32) → b.env z = a.env z

theorem tmp_opd {d : ℕ} (h : d < 16) : Opd (tmp d) := by unfold Opd; rw [tmp_val h]; omega

theorem uv_ok (i : Var) : ¬ Scr (uv i) ∧ ∀ d, ¬ (16 + d ≤ (uv i).val ∧ (uv i).val < 32) := by
  unfold Scr; rw [uv_val]; constructor <;> [omega; (intro d; omega)]

theorem EPost.envOf {d v : ℕ} {a b : DS VV MM} {G : Glob} {fl fp : ℕ} (h : EPost d v a b) (e : Env G fl fp a) :
    Env G fl fp b := by
  have hr : ∀ i, i < 9 → b.env (vr i) = a.env (vr i) := fun i hi =>
    h.env _ (by unfold Scr; rw [vr_val' (by simp only [VV]; omega)]; omega)
      (by rw [vr_val' (by simp only [VV]; omega)]; omega)
  exact ⟨(hr 0 (by omega)).trans e.c0, (hr 1 (by omega)).trans e.c1, (hr 2 (by omega)).trans e.c2,
    (hr 3 (by omega)).trans e.cap, (hr 4 (by omega)).trans e.cap1, (hr 5 (by omega)).trans e.k,
    (hr 6 (by omega)).trans e.n, (hr 7 (by omega)).trans e.t, (hr 8 (by omega)).trans e.p⟩

section Expr

variable {C : Ctx} {G : Glob} (hg : GOk C G) (s : FS) (hs : ∀ i, s.env i ≤ G.cap) (fok : fieldOk G s.fl s.fp = true)

/-- The statement proved for every expression. -/
def EOk (C : Ctx) (G : Glob) (s : FS) (e : E) : Prop :=
  ∀ (d : ℕ) (a : DS VV MM), d + dE e < 16 → Env G s.fl s.fp a → (∀ i, a.env (uv i) = s.env i) →
    Hs C (compE e d) a (costE G e) (EPost d (evalE G s e) a)

include hg hs fok in
/-- A binary operation from its macro specification. -/
theorem bin_ok {m : Fin VV → Fin VV → St VV MM} {f : ℕ → ℕ → ℕ}
    (hm : ∀ (x y : Fin VV) (a : DS VV MM), Bin C G s.fl s.fp x y a →
      Hs C (m x y) a (opc G) (fun b => b.env x = f (a.env x) (a.env y) ∧ Keep x a b))
    (ea eb : E) (iha : EOk C G s ea) (ihb : EOk C G s eb) (d : ℕ) (a : DS VV MM) (hd : d + max (dE ea) (dE eb + 1) < 16)
    (e : Env G s.fl s.fp a) (hu : ∀ i, a.env (uv i) = s.env i) :
    Hs C (binC m (compE ea d) (compE eb (d + 1)) d) a (costE G ea + costE G eb + opc G + 2)
      (EPost d (f (evalE G s ea) (evalE G s eb)) a) := by
  unfold binC
  refine hs_pre (t2 := costE G eb + opc G + 1) (iha d a (by omega) e hu) (fun b1 h1 => ?_) |>.mono (by omega)
    (fun _ h => h)
  have e1 := h1.envOf e
  have hu1 : ∀ i, b1.env (uv i) = s.env i := fun i => (h1.env _ (uv_ok i).1 ((uv_ok i).2 d)).trans (hu i)
  refine hs_pre (ihb (d + 1) b1 (by omega) e1 hu1) (fun b2 h2 => ?_)
  have e2 := h2.envOf e1
  have hd1 : b2.env (tmp d) = evalE G s ea := by
    rw [h2.env _ (by unfold Scr; rw [tmp_val (by omega)]; omega) (by rw [tmp_val (by omega)]; omega), h1.val]
  refine Hs.mono (hm (tmp d) (tmp (d + 1)) b2 ⟨hg, e2, fok, tmp_opd (by omega), tmp_opd (by omega),
    ne_of_val (by rw [tmp_val (by omega), tmp_val (by omega)]; omega), by rw [hd1]; exact evalE_le hg.1 hs fok ea,
    by rw [h2.val]; exact evalE_le hg.1 hs fok eb⟩) le_rfl ?_
  rintro b3 ⟨v3, k3⟩
  refine ⟨by rw [v3, hd1, h2.val], k3.sh.trans (h2.sh.trans h1.sh), fun z hz hz2 => ?_⟩
  have hzd : z ≠ tmp d := by rintro rfl; rw [tmp_val (by omega)] at hz2; omega
  rw [k3.env z hz hzd, h2.env z hz (by omega), h1.env z hz hz2]

include hg hs fok in
/-- **Expressions compile correctly.** -/
theorem compE_ok : ∀ e : E, EOk C G s e
  | .v i => fun d a hd e hu => by
    refine Hs.mono (hs_opq (OpEx.copy (tmp d) (uv i) a (ne_of_val (by rw [tmp_val (by omega), uv_val]; omega))))
      (by simp only [costE]; omega) ?_
    rintro b rfl
    refine ⟨by rw [DS.set_env_self, hu]; rfl, rfl, fun z hz hz2 => DS.set_env_ne _ _ ?_⟩
    rintro rfl; rw [tmp_val (by omega)] at hz2; omega
  | .k n => fun d a hd e hu => by
    refine hs_step (OpEx.zero (tmp d) a) ?_ |>.mono (t := 3 * n + 1 + 2) (by simp only [costE]; omega)
      (fun _ h => h)
    have e1 := e.keep (keep_set_self (tmp d) a 0) (opd_ge (tmp_opd (by omega)))
    refine Hs.mono (incK_spec hg n (tmp d) _ e1 (tmp_opd (by omega)) (by simp)) le_rfl ?_
    rintro b ⟨b1, b2⟩
    refine ⟨by rw [b1]; simp [evalE], b2.sh, fun z hz hz2 => ?_⟩
    have hzd : z ≠ tmp d := by rintro rfl; rw [tmp_val (by omega)] at hz2; omega
    rw [b2.env z hz hzd, DS.set_env_ne _ _ hzd]
  | .gk => fun d a hd e hu => by
    refine Hs.mono (hs_opq (OpEx.copy (tmp d) kR a (opd_ne (tmp_opd (by omega)) (by norm_num))))
      (by simp only [costE]; omega) ?_
    rintro b rfl
    refine ⟨by rw [DS.set_env_self, e.k]; rfl, rfl, fun z hz hz2 => DS.set_env_ne _ _ ?_⟩
    rintro rfl; rw [tmp_val (by omega)] at hz2; omega
  | .add a b => bin_ok hg s hs fok (f := fun u w => min (u + w) G.cap) (fun x y c h => addM_spec h) a b (compE_ok a) (compE_ok b)
  | .sub a b => bin_ok hg s hs fok (f := fun u w => u - w) (fun x y c h => subM_spec h) a b (compE_ok a) (compE_ok b)
  | .mul a b => bin_ok hg s hs fok (f := fun u w => min (u * w) G.cap) (fun x y c h => mulM_spec h) a b (compE_ok a) (compE_ok b)
  | .div a b => bin_ok hg s hs fok (f := fun u w => u / w) (fun x y c h => divM_spec h) a b (compE_ok a) (compE_ok b)
  | .md a b => bin_ok hg s hs fok (f := fun u w => u % w) (fun x y c h => mdM_spec h) a b (compE_ok a) (compE_ok b)
  | .shl a b => bin_ok hg s hs fok (f := fun u w => min (u * 2 ^ w) G.cap) (fun x y c h => shlM_spec h) a b (compE_ok a) (compE_ok b)
  | .shr a b => bin_ok hg s hs fok (f := fun u w => u / 2 ^ w) (fun x y c h => shrM_spec h) a b (compE_ok a) (compE_ok b)
  | .bxor a b => bin_ok hg s hs fok (f := fun u w => (u ^^^ w) % 2 ^ G.K) (fun x y c h => bxorM_spec h) a b (compE_ok a) (compE_ok b)
  | .fadd a b => bin_ok hg s hs fok (f := fun u w => (u ^^^ w) % 2 ^ s.fl) (fun x y c h => faddM_spec h) a b (compE_ok a) (compE_ok b)
  | .fmul a b => bin_ok hg s hs fok (f := fun u w => mulW s.fp s.fl (u % 2 ^ s.fl) (w % 2 ^ s.fl)) (fun x y c h => fmulM_spec h) a b (compE_ok a) (compE_ok b)
  | .fpow a b => bin_ok hg s hs fok (f := fun u w => powW s.fp s.fl (u % 2 ^ s.fl) w) (fun x y c h => fpowM_spec h) a b (compE_ok a) (compE_ok b)
  | .lt a b => bin_ok hg s hs fok (f := fun u w => if u < w then 1 else 0) (fun x y c h => ltM_spec h) a b (compE_ok a) (compE_ok b)
  | .eq a b => bin_ok hg s hs fok (f := fun u w => if u = w then 1 else 0) (fun x y c h => eqM_spec h) a b (compE_ok a) (compE_ok b)
  | .finv a => fun d c hd e hu => by
    refine hs_pre (t2 := opc G) (compE_ok a d c hd e hu) (fun b1 h1 => ?_) |>.mono (by simp only [costE]; omega)
      (fun _ h => h)
    refine Hs.mono (finvM_spec hg (h1.envOf e) fok (tmp_opd (by omega))) le_rfl ?_
    rintro b2 ⟨v2, k2⟩
    refine ⟨by rw [v2, h1.val]; rfl, k2.sh.trans h1.sh, fun z hz hz2 => ?_⟩
    have hzd : z ≠ tmp d := by rintro rfl; rw [tmp_val (by omega)] at hz2; omega
    rw [k2.env z hz hzd, h1.env z hz hz2]

end Expr

/-! ## The field test -/

theorem okE_eval {G : Glob} (s : FS) (hK : 3 ≤ G.K) (f p : E) :
    evalE G s (okE f p) = if fieldOk G (evalE G s f) (evalE G s p) then 1 else 0 := by
  have hc := cap_add G
  have hKc := K_le_cap G hK
  have h1 : min 1 G.cap = 1 := by omega
  have h0 : min 0 G.cap = 0 := by omega
  simp only [okE, evalE, h0, h1, one_mul, fieldOk]
  generalize evalE G s f = F
  generalize evalE G s p = P
  by_cases hF : F + 2 ≤ G.K
  · have hp : 4 * 2 ^ F ≤ 2 ^ G.K := by
      calc 4 * 2 ^ F = 2 ^ (F + 2) := by rw [pow_add]; ring
        _ ≤ 2 ^ G.K := Nat.pow_le_pow_right (by norm_num) hF
    have e1 : min (2 ^ F) G.cap = 2 ^ F := by omega
    have e2 : min (F + 1) G.cap = F + 1 := by omega
    have e3 : min (2 ^ F + 2 ^ F) G.cap = 2 * 2 ^ F := by omega
    have hpos : 1 ≤ 2 ^ F := Nat.one_le_two_pow
    simp only [e1, e2, e3, decide_eq_true_eq]
    clear e1 e2 e3
    generalize 2 ^ F = T at *
    split_ifs <;> simp only [mul_one, one_mul, mul_zero, zero_mul, h1, h0] <;> omega
  · have hB : ¬ (min (F + 1) G.cap < G.K) := by omega
    simp [hB, hF]

/-! ## Statements -/

/-- Expression depths and loop depths fit the register layout. -/
def wfS : S → ℕ → Bool
  | .skip, _ => true
  | .set _ e, _ => decide (dE e < 16)
  | .seq a b, d => wfS a d && wfS b d
  | .ite c a b, d => decide (dE c < 16) && wfS a d && wfS b d
  | .loop _ n body, d => decide (dE n < 16) && decide (d < 8) && wfS body (d + 1)
  | .whl c body, d => decide (dE c < 16) && decide (d < 8) && wfS body (d + 1)
  | .emit e, _ => decide (dE e < 16)
  | .field f p, _ => decide (dE (okE f p) < 16) && decide (dE (.shl (.k 1) f) + 1 < 16) && decide (dE p + 2 < 16)
  | .rd _, _ => true

/-- **The statement compiler.** -/
def compS : S → ℕ → St VV MM
  | .skip, _ => nop
  | .set i e, _ => .seq (compE e 0) (.op (.copy (uv i) (tmp 0)))
  | .seq a b, d => .seq (compS a d) (compS b d)
  | .ite c a b, d => .seq (compE c 0) (.ite (.eq (tmp 0) r0) (compS b d) (compS a d))
  | .loop i n body, d => .seq (compE n 0) (.seq (.op (.copy (lb d) (tmp 0)))
      (.seq (.ite (.lt nR (lb d)) (.op (.copy (lb d) nR)) nop) (.seq (.op (.zero (lc d)))
        (.loop (.lt (lc d) (lb d)) (.seq (.op (.copy (uv i) (lc d))) (.seq (compS body (d + 1)) (.op (.inc (lc d)))))))))
  | .whl c body, d => .seq (.op (.zero (lc d))) (.loop (.lt (lc d) nR)
      (.seq (compE c 0) (.ite (.eq (tmp 0) r0) (.op (.copy (lc d) nR)) (.seq (compS body (d + 1)) (.op (.inc (lc d)))))))
  | .emit e, _ => .seq (compE e 0) (.ite (.eq (tmp 0) r0) (.op (.emit false)) (.op (.emit true)))
  | .field f p, _ => .seq (compE (okE f p) 0) (.seq (compE (.shl (.k 1) f) 1) (.seq (compE p 2)
      (.ite (.eq (tmp 0) r0) (.seq (.op (.copy tR r2)) (.op (.copy pR r2)))
        (.seq (.op (.copy tR (tmp 1))) (.op (.copy pR (tmp 2)))))))
  | .rd i, _ => .op (.rdI (uv i))

/-- A cell state represents an `FL` state. -/
structure Rel (G : Glob) (s : FS) (a : DS VV MM) : Prop where
  env : Env G s.fl s.fp a
  uv : ∀ i, a.env (uv i) = s.env i
  out : a.out = s.out
  le : ∀ i, s.env i ≤ G.cap
  fok : fieldOk G s.fl s.fp = true
  ip : a.ip = s.ip

/-- The stores and the call registers are unchanged. -/
def Fix (a b : DS VV MM) : Prop :=
  b.ram = a.ram ∧ b.rc = a.rc ∧ b.kin = a.kin ∧ b.kout = a.kout ∧ b.kc = a.kc

theorem Fix.refl (a : DS VV MM) : Fix a a := ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem Fix.trans {a b c : DS VV MM} (h1 : Fix a b) (h2 : Fix b c) : Fix a c :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1, h2.2.2.2.1.trans h1.2.2.2.1,
    h2.2.2.2.2.trans h1.2.2.2.2⟩
theorem Fix.of_sh {a b : DS VV MM} (h : b.sh = a.sh) : Fix a b := by
  simp only [DS.sh, Prod.mk.injEq] at h
  exact ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩
theorem ip_of_sh {a b : DS VV MM} (h : b.sh = a.sh) : b.ip = a.ip := by
  simp only [DS.sh, Prod.mk.injEq] at h; exact h.1
theorem out_of_sh {a b : DS VV MM} (h : b.sh = a.sh) : b.out = a.out := by
  simp only [DS.sh, Prod.mk.injEq] at h; exact h.2.1
theorem Fix.set (a : DS VV MM) (x : Fin VV) (v : ℕ) : Fix a (a.set x v) := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- After a statement at loop depth `d`. -/
structure SPost (G : Glob) (d : ℕ) (s : FS) (a b : DS VV MM) : Prop where
  rel : Rel G s b
  fix : Fix a b
  lp : ∀ j < d, b.env (lc j) = a.env (lc j) ∧ b.env (lb j) = a.env (lb j)

theorem lc_ok {j : ℕ} (h : j < 8) : ¬ Scr (lc j) ∧ ∀ d, ¬ (16 + d ≤ (lc j).val ∧ (lc j).val < 32) := by
  unfold Scr; rw [lc_val h]; constructor <;> [omega; (intro d; omega)]
theorem lb_ok {j : ℕ} (h : j < 8) : ¬ Scr (lb j) ∧ ∀ d, ¬ (16 + d ≤ (lb j).val ∧ (lb j).val < 32) := by
  unfold Scr; rw [lb_val h]; constructor <;> [omega; (intro d; omega)]

theorem Rel.epost {G : Glob} {s : FS} {a b : DS VV MM} {d v : ℕ} (r : Rel G s a) (h : EPost d v a b) :
    Rel G s b :=
  ⟨h.envOf r.env, fun i => (h.env _ (uv_ok i).1 ((uv_ok i).2 d)).trans (r.uv i), (out_of_sh h.sh).trans r.out,
    r.le, r.fok, (ip_of_sh h.sh).trans r.ip⟩

theorem EPost.lp {d v : ℕ} {a b : DS VV MM} (h : EPost d v a b) (d' : ℕ) (hd : d' ≤ 8) :
    ∀ j < d', b.env (lc j) = a.env (lc j) ∧ b.env (lb j) = a.env (lb j) := fun j hj =>
  ⟨h.env _ (lc_ok (by omega)).1 ((lc_ok (by omega)).2 d), h.env _ (lb_ok (by omega)).1 ((lb_ok (by omega)).2 d)⟩

theorem Rel.keepS {G : Glob} {s : FS} {a b : DS VV MM} (r : Rel G s a) (h : KeepS a b) : Rel G s b :=
  ⟨r.env.keep (h.keep junk) (by unfold junk; rw [vr_val' (by simp only [VV]; omega)]; omega),
    fun i => (h.2 _ (uv_ok i).1).trans (r.uv i), (out_of_sh h.1).trans r.out, r.le, r.fok, (ip_of_sh h.1).trans r.ip⟩

theorem nop_keepS {C : Ctx} (a : DS VV MM) : Hs C nop a 1 (KeepS a) :=
  Hs.mono (hs_opq (OpEx.zero junk a)) le_rfl (by
    rintro b rfl; exact ⟨rfl, fun z hz => DS.set_env_ne _ _ (by rintro rfl; exact hz scr_junk)⟩)

theorem hs_loopT {C : Ctx} {c : Cnd VV} {p : St VV MM} {a : DS VV MM} {t1 t2 : ℕ} {R1 R : DS VV MM → Prop}
    (hc : c.wf) (he : c.eval a = true) (h1 : Hs C p a t1 R1) (h2 : ∀ b, R1 b → Hs C (.loop c p) b t2 R) :
    Hs C (.loop c p) a (t1 + t2 + 2) R := by
  obtain ⟨b, n, hx, hn, hb⟩ := h1
  obtain ⟨d, k, hx2, hk, hd⟩ := h2 b hb
  exact ⟨d, n + k + 2, Ex.loopT hc he hx hx2, by omega, hd⟩

theorem hs_loopF {C : Ctx} {c : Cnd VV} {p : St VV MM} {a : DS VV MM} {R : DS VV MM → Prop}
    (hc : c.wf) (he : c.eval a = false) (hR : R a) : Hs C (.loop c p) a 2 R :=
  ⟨a, 2, Ex.loopF hc he, le_rfl, hR⟩

theorem lc_ne_lb {d : ℕ} (h : d < 8) : lc d ≠ lb d := ne_of_val (by rw [lc_val h, lb_val h]; omega)

theorem foldl_range_succ (f : FS → ℕ → FS) (s : FS) (j : ℕ) :
    (List.range (j + 1)).foldl f s = f ((List.range j).foldl f s) j := by
  rw [List.range_succ, List.foldl_append]; rfl


/-! ## The out-of-input flag only rises -/

theorem whileN_bad (c : FS → Bool) (f : FS → FS) (hf : ∀ s, s.bad = true → (f s).bad = true) :
    ∀ n s, s.bad = true → (whileN c f n s).bad = true
  | 0, _, h => h
  | n + 1, s, h => by
    unfold whileN; split_ifs
    · exact whileN_bad c f hf n _ (hf s h)
    · exact h

theorem foldl_bad (f : FS → ℕ → FS) (hf : ∀ s j, s.bad = true → (f s j).bad = true) :
    ∀ (l : List ℕ) (s : FS), s.bad = true → (l.foldl f s).bad = true
  | [], _, h => h
  | j :: l, s, h => foldl_bad f hf l _ (hf s j h)

theorem bad_mono (G : Glob) : ∀ (p : S) (s : FS), s.bad = true → (evalS G p s).bad = true
  | .skip, _, h => h
  | .set _ _, _, h => h
  | .seq a b, s, h => bad_mono G b _ (bad_mono G a s h)
  | .ite c a b, s, h => by
    simp only [evalS]; split_ifs
    · exact bad_mono G b s h
    · exact bad_mono G a s h
  | .loop i n body, s, h => foldl_bad _ (fun s' j h' => bad_mono G body _ (by simpa using h')) _ s h
  | .whl c body, s, h => whileN_bad _ _ (fun s' h' => bad_mono G body s' h') _ s h
  | .emit _, _, h => h
  | .field f p, s, h => by simp only [evalS]; split_ifs <;> exact h
  | .rd i, s, h => by simp only [evalS]; split_ifs <;> simp [h]

theorem bad_pre {G : Glob} {p : S} {s : FS} (h : (evalS G p s).bad = false) : s.bad = false := by
  cases hs : s.bad
  · rfl
  · rw [bad_mono G p s hs] at h; exact h

section Stmt

variable {C : Ctx} {G : Glob} (hg : GOk C G)

/-- The statement proved for every statement. -/
def SOk (C : Ctx) (G : Glob) (p : S) : Prop :=
  ∀ (d : ℕ) (s : FS) (a : DS VV MM), d ≤ 8 → wfS p d = true → (evalS G p s).bad = false → Rel G s a →
    Hs C (compS p d) a (costS G p) (SPost G d (evalS G p s) a)

include hg in
theorem expr_run (s : FS) (e : E) (dd : ℕ) (a : DS VV MM) (r : Rel G s a) (hd : dd + dE e < 16) :
    Hs C (compE e dd) a (costE G e) (EPost dd (evalE G s e) a) :=
  compE_ok hg s r.le r.fok e dd a hd r.env r.uv

include hg in
theorem set_ok (i : Var) (e : E) : SOk C G (.set i e) := by
  intro d s a hd8 hw hbad r
  simp only [wfS, decide_eq_true_eq] at hw
  refine hs_pre (t2 := 1) (expr_run hg s e 0 a r (by omega)) (fun b1 h1 => ?_) |>.mono
    (by simp only [costS]; omega) (fun _ h => h)
  have r1 := r.epost h1
  have hne : uv i ≠ tmp 0 := ne_of_val (by rw [uv_val, tmp_val (by norm_num)]; omega)
  refine Hs.mono (hs_opq (OpEx.copy (uv i) (tmp 0) b1 hne)) le_rfl ?_
  rintro b rfl
  have hv := h1.val
  refine ⟨⟨r1.env.keep (Keep.set b1 _ (Or.inr rfl) (x := uv i)) (by rw [uv_val]; omega), fun j => ?_, r1.out, fun j => ?_,
    r.fok, r1.ip⟩, Fix.of_sh h1.sh |>.trans (Fix.set _ _ _), fun j hj => ?_⟩
  · by_cases hij : j = i
    · subst hij; simp [hv, evalS]
    · rw [DS.set_env_ne _ _ (fun h => hij (uv_inj h)), r1.uv]
      simp [evalS, Function.update_of_ne hij]
  · simp only [evalS, FS.setv_env]
    by_cases hij : j = i
    · subst hij; simp only [Function.update_self]; exact evalE_le hg.1 r.le r.fok e
    · rw [Function.update_of_ne hij]; exact r.le j
  · have hl : lc j ≠ uv i := ne_of_val (by rw [lc_val (by omega), uv_val]; omega)
    have hb : lb j ≠ uv i := ne_of_val (by rw [lb_val (by omega), uv_val]; omega)
    rw [DS.set_env_ne _ _ hl, DS.set_env_ne _ _ hb]
    exact h1.lp 8 le_rfl j (by omega)

theorem SPost.of_keepS {d : ℕ} {s : FS} {a b : DS VV MM} (hd : d ≤ 8) (r : Rel G s a) (hb : KeepS a b) :
    SPost G d s a b :=
  ⟨r.keepS hb, Fix.of_sh hb.1, fun j hj => ⟨hb.2 _ (lc_ok (by omega)).1, hb.2 _ (lb_ok (by omega)).1⟩⟩

theorem SPost.trans {d : ℕ} {s s' : FS} {a b c : DS VV MM} (h1 : SPost G d s a b) (h2 : SPost G d s' b c) :
    SPost G d s' a c :=
  ⟨h2.rel, h1.fix.trans h2.fix, fun j hj => ⟨(h2.lp j hj).1.trans (h1.lp j hj).1, (h2.lp j hj).2.trans (h1.lp j hj).2⟩⟩

theorem skip_ok : SOk C G .skip := by
  intro d s a hd8 hw hbad r
  exact Hs.mono (nop_keepS a) (by simp only [costS]; omega) (fun b hb => SPost.of_keepS hd8 r hb)


theorem SPost.of_epost {d dd v : ℕ} {s : FS} {a b : DS VV MM} (hd : d ≤ 8) (r : Rel G s a) (h : EPost dd v a b) :
    SPost G d s a b := ⟨r.epost h, Fix.of_sh h.sh, h.lp d hd⟩

theorem Env.of_env {fl fp : ℕ} {a b : DS VV MM} (h : b.env = a.env) (e : Env G fl fp a) : Env G fl fp b :=
  ⟨by rw [h]; exact e.c0, by rw [h]; exact e.c1, by rw [h]; exact e.c2, by rw [h]; exact e.cap, by rw [h]; exact e.cap1,
    by rw [h]; exact e.k, by rw [h]; exact e.n, by rw [h]; exact e.t, by rw [h]; exact e.p⟩

theorem seq_ok {p q : S} (hp : SOk C G p) (hq : SOk C G q) : SOk C G (.seq p q) := by
  intro d s a hd8 hw hbad r
  simp only [wfS, Bool.and_eq_true] at hw
  refine hs_pre (t2 := costS G q) (hp d s a hd8 hw.1 (bad_pre (p := q) hbad) r) (fun b hb => ?_) |>.mono
    (by simp only [costS]; omega) (fun _ h => h)
  exact Hs.mono (hq d _ b hd8 hw.2 hbad hb.rel) le_rfl (fun c hc => hb.trans hc)

include hg in
theorem ite_ok {c : E} {p q : S} (hp : SOk C G p) (hq : SOk C G q) : SOk C G (.ite c p q) := by
  intro d s a hd8 hw hbad r
  simp only [wfS, Bool.and_eq_true, decide_eq_true_eq] at hw
  refine hs_pre (t2 := costS G p + costS G q + 1) (expr_run hg s c 0 a r (by omega)) (fun b1 h1 => ?_) |>.mono
    (by simp only [costS]; omega) (fun _ h => h)
  have r1 := r.epost h1
  have p1 := SPost.of_epost hd8 r h1
  refine Hs.ite (c := .eq (tmp 0) r0) (opd_ne (tmp_opd (by norm_num)) (by norm_num)) (fun hc => ?_) (fun hc => ?_)
  · simp only [Cnd.eval, h1.val, r1.env.c0, decide_eq_true_eq] at hc
    have : evalS G (.ite c p q) s = evalS G q s := by simp [evalS, hc]
    rw [this] at hbad ⊢
    exact Hs.mono (hq d s b1 hd8 hw.2 hbad r1) (by omega) (fun b hb => p1.trans hb)
  · simp only [Cnd.eval, h1.val, r1.env.c0, decide_eq_false_iff_not] at hc
    have : evalS G (.ite c p q) s = evalS G p s := by simp [evalS, hc]
    rw [this] at hbad ⊢
    exact Hs.mono (hp d s b1 hd8 hw.1.2 hbad r1) (by omega) (fun b hb => p1.trans hb)

include hg in
theorem emit_ok (e : E) : SOk C G (.emit e) := by
  intro d s a hd8 hw hbad r
  simp only [wfS, decide_eq_true_eq] at hw
  refine hs_pre (t2 := 2) (expr_run hg s e 0 a r (by omega)) (fun b1 h1 => ?_) |>.mono
    (by simp only [costS]; omega) (fun _ h => h)
  have r1 := r.epost h1
  have p1 := SPost.of_epost hd8 r h1
  have key : ∀ bit : Bool, bit = (evalE G s e != 0) →
      SPost G d (evalS G (.emit e) s) a { b1 with out := b1.out ++ [bit] } := by
    rintro bit rfl
    have hev : evalS G (.emit e) s = { s with out := s.out ++ [evalE G s e != 0] } := rfl
    rw [hev]
    have e' : Env G s.fl s.fp { b1 with out := b1.out ++ [evalE G s e != 0] } :=
      Env.of_env (a := b1) (b := { b1 with out := b1.out ++ [evalE G s e != 0] }) rfl r1.env
    exact ⟨⟨e', r1.uv, by rw [r1.out], r1.le, r1.fok, r1.ip⟩, p1.fix, p1.lp⟩
  refine Hs.ite (c := .eq (tmp 0) r0) (opd_ne (tmp_opd (by norm_num)) (by norm_num)) (fun hc => ?_) (fun hc => ?_)
  · simp only [Cnd.eval, h1.val, r1.env.c0, decide_eq_true_eq] at hc
    exact Hs.mono (hs_opq (OpEx.emit false b1)) le_rfl (by rintro b rfl; exact key false (by simp [hc]))
  · simp only [Cnd.eval, h1.val, r1.env.c0, decide_eq_false_iff_not] at hc
    exact Hs.mono (hs_opq (OpEx.emit true b1)) le_rfl (by rintro b rfl; exact key true (by simp [hc]))

include hg in
theorem field_ok (f p : E) : SOk C G (.field f p) := by
  intro d s a hd8 hw hbad r
  simp only [wfS, Bool.and_eq_true, decide_eq_true_eq] at hw
  obtain ⟨⟨w1, w2⟩, w3⟩ := hw
  refine hs_pre (t2 := costE G (.shl (.k 1) f) + costE G p + 6) (expr_run hg s (okE f p) 0 a r (by omega))
    (fun b1 h1 => ?_) |>.mono (by simp only [costS]; omega) (fun _ h => h)
  have q1 := r.epost h1
  refine (hs_pre (t2 := costE G p + 5) (expr_run hg s (.shl (.k 1) f) 1 b1 q1 (by omega))
    (fun b2 h2 => ?_)).mono (by omega) (fun _ h => h)
  have q2 := q1.epost h2
  refine (hs_pre (t2 := 4) (expr_run hg s p 2 b2 q2 (by omega)) (fun b3 h3 => ?_)).mono (by omega) (fun _ h => h)
  have q3 := q2.epost h3
  have p3 := ((SPost.of_epost hd8 r h1).trans (SPost.of_epost hd8 q1 h2)).trans (SPost.of_epost hd8 q2 h3)
  have v0 : b3.env (tmp 0) = evalE G s (okE f p) := by
    rw [h3.env _ (by unfold Scr; rw [tmp_val (by norm_num)]; omega) (by rw [tmp_val (by norm_num)]; omega),
      h2.env _ (by unfold Scr; rw [tmp_val (by norm_num)]; omega) (by rw [tmp_val (by norm_num)]; omega), h1.val]
  have v1 : b3.env (tmp 1) = evalE G s (.shl (.k 1) f) := by
    rw [h3.env _ (by unfold Scr; rw [tmp_val (by norm_num)]; omega) (by rw [tmp_val (by norm_num)]; omega), h2.val]
  have v2 : b3.env (tmp 2) = evalE G s p := h3.val
  have e3 := q3.env
  -- setting the two field registers
  have setTP : ∀ (fl' fp' : ℕ), fieldOk G fl' fp' = true → ∀ (u w : Fin VV), u ≠ tR → u ≠ pR → w ≠ tR → w ≠ pR →
      b3.env u = 2 ^ fl' → b3.env w = fp' →
      Hs C (.seq (.op (.copy tR u)) (.op (.copy pR w))) b3 3
        (SPost G d { s with fl := fl', fp := fp' } a) := by
    intro fl' fp' hok u w hu1 hu2 hw1 hw2 hu hw
    refine hs_step (OpEx.copy tR u b3 hu1.symm) ?_
    refine Hs.mono (hs_opq (OpEx.copy pR w _ hw2.symm)) le_rfl ?_
    rintro b rfl
    have hreg : ∀ z : Fin VV, z ≠ tR → z ≠ pR → ((b3.set tR (b3.env u)).set pR ((b3.set tR (b3.env u)).env w)).env z =
        b3.env z := fun z h1 h2 => by rw [DS.set_env_ne _ _ h2, DS.set_env_ne _ _ h1]
    have hne : ∀ i, i < 7 → vr i ≠ tR ∧ vr i ≠ pR := fun i hi =>
      ⟨ne_of_val (by unfold tR; rw [vr_val' (by simp only [VV]; omega), vr_val' (by simp only [VV]; omega)]; omega),
       ne_of_val (by unfold pR; rw [vr_val' (by simp only [VV]; omega), vr_val' (by simp only [VV]; omega)]; omega)⟩
    have hT : ∀ z : Fin VV, 9 ≤ z.val → z ≠ tR ∧ z ≠ pR := fun z hz =>
      ⟨ne_of_val (by unfold tR; rw [vr_val' (by simp only [VV]; omega)]; omega),
       ne_of_val (by unfold pR; rw [vr_val' (by simp only [VV]; omega)]; omega)⟩
    refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun i => ?_, q3.out, q3.le, hok, q3.ip⟩, p3.fix.trans
      ((Fix.set _ _ _).trans (Fix.set _ _ _)), fun j hj => ?_⟩
    · rw [hreg r0 (hne 0 (by omega)).1 (hne 0 (by omega)).2]; exact e3.c0
    · rw [hreg FL.r1 (hne 1 (by omega)).1 (hne 1 (by omega)).2]; exact e3.c1
    · rw [hreg FL.r2 (hne 2 (by omega)).1 (hne 2 (by omega)).2]; exact e3.c2
    · rw [hreg capR (hne 3 (by omega)).1 (hne 3 (by omega)).2]; exact e3.cap
    · rw [hreg cap1R (hne 4 (by omega)).1 (hne 4 (by omega)).2]; exact e3.cap1
    · rw [hreg kR (hne 5 (by omega)).1 (hne 5 (by omega)).2]; exact e3.k
    · rw [hreg nR (hne 6 (by omega)).1 (hne 6 (by omega)).2]; exact e3.n
    · rw [DS.set_env_ne _ _ (by decide), DS.set_env_self, hu]
    · rw [DS.set_env_self, DS.set_env_ne _ _ hw1, hw]
    · rw [hreg (uv i) (hT _ (by rw [uv_val]; omega)).1 (hT _ (by rw [uv_val]; omega)).2]; exact q3.uv i
    · rw [hreg (lc j) (hT _ (by rw [lc_val (by omega)]; omega)).1 (hT _ (by rw [lc_val (by omega)]; omega)).2,
        hreg (lb j) (hT _ (by rw [lb_val (by omega)]; omega)).1 (hT _ (by rw [lb_val (by omega)]; omega)).2]
      exact p3.lp j hj
  have hok0 := okE_eval s hg.1 f p
  refine Hs.ite (c := .eq (tmp 0) r0) (opd_ne (tmp_opd (by norm_num)) (by norm_num)) (fun hc => ?_) (fun hc => ?_)
  · simp only [Cnd.eval, v0, e3.c0, decide_eq_true_eq, hok0] at hc
    have hnot : fieldOk G (evalE G s f) (evalE G s p) = false := by
      by_contra h; simp [h] at hc
    have : evalS G (.field f p) s = { s with fl := 1, fp := 2 } := by simp [evalS, hnot]
    rw [this]
    exact setTP 1 2 (by simp [fieldOk]; have := hg.1; omega) FL.r2 FL.r2 (by decide) (by decide) (by decide) (by decide)
      (by rw [e3.c2]; norm_num) e3.c2
  · simp only [Cnd.eval, v0, e3.c0, decide_eq_false_iff_not, hok0] at hc
    have hyes : fieldOk G (evalE G s f) (evalE G s p) = true := by
      by_contra h; simp [h] at hc
    have : evalS G (.field f p) s = { s with fl := evalE G s f, fp := evalE G s p } := by simp [evalS, hyes]
    rw [this]
    have hF := fl_bounds hyes
    have h2f : evalE G s (.shl (.k 1) f) = 2 ^ evalE G s f := by
      have := cap_add G
      have h1 : min 1 G.cap = 1 := by have := K_le_cap G hg.1; omega
      simp only [evalE, h1, one_mul]
      have := hF.2.2.2; omega
    exact setTP _ _ hyes (tmp 1) (tmp 2) (opd_ne (tmp_opd (by norm_num)) (by norm_num))
      (opd_ne (tmp_opd (by norm_num)) (by norm_num)) (opd_ne (tmp_opd (by norm_num)) (by norm_num))
      (opd_ne (tmp_opd (by norm_num)) (by norm_num))
      (by rw [v1, h2f]) v2


/-- Setting a register that is neither fixed nor a program variable keeps the relation. -/
theorem Rel.set_free {s : FS} {c : DS VV MM} (r : Rel G s c) {x : Fin VV} (h1 : 9 ≤ x.val) (h2 : x.val < 72)
    (v : ℕ) : Rel G s (c.set x v) := by
  have hreg : ∀ i, i < 9 → (c.set x v).env (vr i) = c.env (vr i) := fun i hi =>
    DS.set_env_ne _ _ (ne_of_val (by rw [vr_val' (by simp only [VV]; omega)]; omega))
  refine ⟨⟨(hreg 0 (by omega)).trans r.env.c0, (hreg 1 (by omega)).trans r.env.c1, (hreg 2 (by omega)).trans r.env.c2,
    (hreg 3 (by omega)).trans r.env.cap, (hreg 4 (by omega)).trans r.env.cap1, (hreg 5 (by omega)).trans r.env.k,
    (hreg 6 (by omega)).trans r.env.n, (hreg 7 (by omega)).trans r.env.t, (hreg 8 (by omega)).trans r.env.p⟩,
    fun i => ?_, r.out, r.le, r.fok, r.ip⟩
  rw [DS.set_env_ne _ _ (ne_of_val (by rw [uv_val]; omega)), r.uv]

/-- Setting a program variable. -/
theorem Rel.setv {s : FS} {c : DS VV MM} (r : Rel G s c) (i : Var) {v : ℕ} (hv : v ≤ G.cap) :
    Rel G (s.setv i v) (c.set (FL.uv i) v) := by
  have hreg : ∀ k, k < 9 → (c.set (FL.uv i) v).env (vr k) = c.env (vr k) := fun k hk =>
    DS.set_env_ne _ _ (ne_of_val (by rw [vr_val' (by simp only [VV]; omega), uv_val]; omega))
  refine ⟨⟨(hreg 0 (by omega)).trans r.env.c0, (hreg 1 (by omega)).trans r.env.c1, (hreg 2 (by omega)).trans r.env.c2,
    (hreg 3 (by omega)).trans r.env.cap, (hreg 4 (by omega)).trans r.env.cap1, (hreg 5 (by omega)).trans r.env.k,
    (hreg 6 (by omega)).trans r.env.n, (hreg 7 (by omega)).trans r.env.t, (hreg 8 (by omega)).trans r.env.p⟩,
    fun i' => ?_, r.out, fun i' => ?_, r.fok, r.ip⟩
  · by_cases hii : i' = i
    · subst hii; simp
    · rw [DS.set_env_ne _ _ (fun h => hii (uv_inj h)), r.uv]; simp [Function.update_of_ne hii]
  · by_cases hii : i' = i
    · subst hii; simp; exact hv
    · simp [Function.update_of_ne hii]; exact r.le i'

theorem lcd_range {d : ℕ} (h : d < 8) : 9 ≤ (lc d).val ∧ (lc d).val < 72 := by rw [lc_val h]; omega
theorem lbd_range {d : ℕ} (h : d < 8) : 9 ≤ (lb d).val ∧ (lb d).val < 72 := by rw [lb_val h]; omega

include hg in
theorem loop_ok (i : Var) (n : E) {body : S} (hb : SOk C G body) : SOk C G (.loop i n body) := by
  intro d s a hd8 hw hbad r
  simp only [wfS, Bool.and_eq_true, decide_eq_true_eq] at hw
  obtain ⟨⟨hwn, hd⟩, hwb⟩ := hw
  have hW := two_cap_lt hg
  have hNc := hg.2.2
  set m := min (evalE G s n) G.N with hm
  let F : ℕ → FS := fun j => (List.range j).foldl (fun s' j => evalS G body (s'.setv i j)) s
  have hF : ∀ j, F (j + 1) = evalS G body ((F j).setv i j) := fun j => foldl_range_succ _ s j
  have hFb : ∀ j k, (F j).bad = true → (F (j + k)).bad = true := by
    intro j k hj
    induction k with
    | zero => exact hj
    | succ k ih => rw [← Nat.add_assoc, hF]; exact bad_mono G body _ (by simpa using ih)
  have hFm : ∀ j, j ≤ m → (F j).bad = false := by
    intro j hj
    cases hc : (F j).bad
    · rfl
    · have := hFb j (m - j) hc; rw [Nat.add_sub_cancel' hj] at this
      have hb' : (F m).bad = false := hbad
      rw [this] at hb'; exact hb'
  have lcb := lc_ne_lb hd
  -- the prefix
  refine (hs_pre (t2 := m * (costS G body + 4 + 2) + 2 + 9) (expr_run hg s n 0 a r (by omega)) (fun b1 h1 => ?_)).mono
    (by
      have : m * (costS G body + 4 + 2) ≤ G.N * (costS G body + 10) :=
        Nat.mul_le_mul (min_le_right _ _) (by omega)
      simp only [costS]; omega) (fun _ h => h)
  have q1 := r.epost h1
  have p1 := SPost.of_epost hd8 r h1
  have hlb0 : lb d ≠ tmp 0 := ne_of_val (by rw [lb_val hd, tmp_val (by norm_num)]; omega)
  refine (hs_step (OpEx.copy (lb d) (tmp 0) b1 hlb0) ?_).mono (t := m * (costS G body + 4 + 2) + 2 + 7) (by omega)
    (fun _ h => h)
  set b2 := b1.set (lb d) (b1.env (tmp 0))
  have q2 := q1.set_free (lbd_range hd).1 (lbd_range hd).2 (b1.env (tmp 0))
  have b2n : b2.env nR = G.N := q2.env.n
  have b2lb : b2.env (lb d) = evalE G s n := by simp only [b2, DS.set_env_self, h1.val]
  have hnlb : nR ≠ lb d := ne_of_val (by unfold nR; rw [vr_val' (by simp only [VV]; omega), lb_val hd]; omega)
  -- clamp the bound
  refine (hs_pre (t1 := 2) (t2 := m * (costS G body + 4 + 2) + 2 + 2)
    (R1 := fun c => c.env (lb d) = m ∧ Rel G s c ∧ Fix a c ∧ ∀ j < d, c.env (lc j) = a.env (lc j) ∧
      c.env (lb j) = a.env (lb j))
    (Hs.ite (c := .lt nR (lb d)) hnlb (fun hc => ?_) (fun hc => ?_)) (fun c0 hc0 => ?_)).mono (by omega)
    (fun _ h => h)
  · simp only [Cnd.eval, b2n, b2lb, decide_eq_true_eq] at hc
    refine Hs.mono (hs_opq (OpEx.copy (lb d) nR b2 hnlb.symm)) le_rfl ?_
    rintro c rfl
    refine ⟨by rw [DS.set_env_self, b2n]; omega, q2.set_free (lbd_range hd).1 (lbd_range hd).2 _,
      p1.fix.trans ((Fix.set _ _ _).trans (Fix.set _ _ _)), fun j hj => ?_⟩
    have h1' : lc j ≠ lb d := ne_of_val (by rw [lc_val (by omega), lb_val hd]; omega)
    have h2' : lb j ≠ lb d := ne_of_val (by rw [lb_val (by omega), lb_val hd]; omega)
    simp only [b2, DS.set_env_ne _ _ h1', DS.set_env_ne _ _ h2']
    exact p1.lp j hj
  · simp only [Cnd.eval, b2n, b2lb, decide_eq_false_iff_not, not_lt] at hc
    refine Hs.mono (nop_keepS b2) (by omega) ?_
    intro c hc'
    refine ⟨by rw [hc'.2 _ (lb_ok hd).1, b2lb]; omega, q2.keepS hc', p1.fix.trans ((Fix.set _ _ _).trans
      (Fix.of_sh hc'.1)), fun j hj => ?_⟩
    have h1' : lc j ≠ lb d := ne_of_val (by rw [lc_val (by omega), lb_val hd]; omega)
    have h2' : lb j ≠ lb d := ne_of_val (by rw [lb_val (by omega), lb_val hd]; omega)
    rw [hc'.2 _ (lc_ok (by omega)).1, hc'.2 _ (lb_ok (by omega)).1]
    simp only [b2, DS.set_env_ne _ _ h1', DS.set_env_ne _ _ h2']
    exact p1.lp j hj
  -- zero the counter, then the passes
  obtain ⟨c0lb, q0, f0, l0⟩ := hc0
  refine hs_step (OpEx.zero (lc d) c0) ?_
  let I : ℕ → DS VV MM → Prop := fun j c => Rel G (F j) c ∧ c.env (lc d) = j ∧ c.env (lb d) = m ∧ Fix a c ∧
    ∀ j' < d, c.env (lc j') = a.env (lc j') ∧ c.env (lb j') = a.env (lb j')
  have hI0 : I 0 (c0.set (lc d) 0) := by
    refine ⟨q0.set_free (lcd_range hd).1 (lcd_range hd).2 0, by simp, by rw [DS.set_env_ne _ _ lcb.symm, c0lb],
      f0.trans (Fix.set _ _ _), fun j hj => ?_⟩
    have h1' : lc j ≠ lc d := ne_of_val (by rw [lc_val (by omega), lc_val hd]; omega)
    have h2' : lb j ≠ lc d := ne_of_val (by rw [lb_val (by omega), lc_val hd]; omega)
    rw [DS.set_env_ne _ _ h1', DS.set_env_ne _ _ h2']; exact l0 j hj
  refine Hs.mono (Hs.loopN (c := .lt (lc d) (lb d)) lcb I m (costS G body + 4) ?_ ?_ _ hI0) le_rfl ?_
  · intro j hj c ⟨qc, cl, cb, fc, lpc⟩
    refine ⟨by simp only [Cnd.eval, cl, cb, decide_eq_true_eq]; exact hj, ?_⟩
    have hjc : j ≤ G.cap := by have : m ≤ G.N := min_le_right _ _; omega
    have hul : uv i ≠ lc d := ne_of_val (by rw [uv_val, lc_val hd]; omega)
    refine hs_step (OpEx.copy (uv i) (lc d) c hul) ?_
    have qc' : Rel G ((F j).setv i j) (c.set (uv i) (c.env (lc d))) := by
      rw [cl]; exact qc.setv i hjc
    have := hb (d + 1) ((F j).setv i j) _ (by omega) hwb (by rw [← hF]; exact hFm (j + 1) (by omega)) qc'
    refine hs_pre (t2 := 1) this (fun c2 hc2 => ?_)
    have c2l : c2.env (lc d) = j := by
      rw [(hc2.lp d (by omega)).1, DS.set_env_ne _ _ hul.symm, cl]
    have c2b : c2.env (lb d) = m := by
      rw [(hc2.lp d (by omega)).2, DS.set_env_ne _ _ (ne_of_val (by rw [lb_val hd, uv_val]; omega)), cb]
    refine Hs.mono (hs_opq (OpEx.inc (lc d) c2 (by rw [c2l]; have : m ≤ G.N := min_le_right _ _; omega))) le_rfl ?_
    rintro c3 rfl
    refine ⟨by rw [hF]; exact hc2.rel.set_free (lcd_range hd).1 (lcd_range hd).2 _, by simp [c2l],
      by rw [DS.set_env_ne _ _ lcb.symm, c2b], fc.trans ((Fix.set _ _ _).trans (hc2.fix.trans (Fix.set _ _ _))),
      fun j' hj' => ?_⟩
    have h1' : lc j' ≠ lc d := ne_of_val (by rw [lc_val (by omega), lc_val hd]; omega)
    have h2' : lb j' ≠ lc d := ne_of_val (by rw [lb_val (by omega), lc_val hd]; omega)
    have h3' : lc j' ≠ uv i := ne_of_val (by rw [lc_val (by omega), uv_val]; omega)
    have h4' : lb j' ≠ uv i := ne_of_val (by rw [lb_val (by omega), uv_val]; omega)
    rw [DS.set_env_ne _ _ h1', DS.set_env_ne _ _ h2', (hc2.lp j' (by omega)).1, (hc2.lp j' (by omega)).2,
      DS.set_env_ne _ _ h3', DS.set_env_ne _ _ h4']
    exact lpc j' hj'
  · intro c ⟨_, cl, cb, _, _⟩
    simp only [Cnd.eval, cl, cb, decide_eq_false_iff_not]; omega
  · rintro c ⟨qc, _, _, fc, lpc⟩
    exact ⟨qc, fc, lpc⟩


/-- One pass of the compiled while loop. -/
def whlBody (c : E) (body : S) (d : ℕ) : St VV MM :=
  .seq (compE c 0) (.ite (.eq (tmp 0) r0) (.op (.copy (lc d) nR)) (.seq (compS body (d + 1)) (.op (.inc (lc d)))))

include hg in
theorem whl_aux (c : E) {body : S} (hb : SOk C G body) (d : ℕ) (hd : d < 8) (hwc : dE c < 16)
    (hwb : wfS body (d + 1) = true) (a : DS VV MM) : ∀ k, k ≤ G.N → ∀ (s : FS) (x : DS VV MM), Rel G s x →
      x.env (lc d) = G.N - k → Fix a x → (∀ j < d, x.env (lc j) = a.env (lc j) ∧ x.env (lb j) = a.env (lb j)) →
      (whileN (fun s' => evalE G s' c != 0) (evalS G body) k s).bad = false →
      Hs C (.loop (.lt (lc d) nR) (whlBody c body d)) x (k * (costE G c + costS G body + 12) + 6)
        (SPost G d (whileN (fun s' => evalE G s' c != 0) (evalS G body) k s) a)
  | 0, _, s, x, r, hl, fx, lx, _ => by
    have hN := r.env.n
    exact Hs.mono (hs_loopF (c := .lt (lc d) nR) (ne_of_val (by unfold nR; rw [lc_val hd, vr_val' (by simp only [VV]; omega)]; omega))
      (by simp only [Cnd.eval, hl, hN, decide_eq_false_iff_not]; omega) ⟨r, fx, lx⟩) (by omega) (fun _ h => h)
  | k + 1, hk, s, x, r, hl, fx, lx, hbad => by
    have hW := two_cap_lt hg
    have hN := r.env.n
    have hNc := hg.2.2
    have hwf : (Cnd.lt (lc d) nR).wf :=
      ne_of_val (by unfold nR; rw [lc_val hd, vr_val' (by simp only [VV]; omega)]; omega)
    have hnl : nR ≠ lc d := fun h => hwf h.symm
    refine (hs_loopT (t1 := costE G c + costS G body + 4) (t2 := k * (costE G c + costS G body + 12) + 6) hwf
      (by simp only [Cnd.eval, hl, hN, decide_eq_true_eq]; omega) ?_ (fun y hy => hy)).mono
      (by rw [Nat.succ_mul]; omega) (fun _ h => h)
    unfold whlBody
    refine (hs_pre (t2 := costS G body + 3) (expr_run hg s c 0 x r (by omega)) (fun b1 h1 => ?_)).mono (by omega)
      (fun _ h => h)
    have q1 := r.epost h1
    have p1 := SPost.of_epost (d := d) (by omega) r h1
    have b1l : b1.env (lc d) = G.N - (k + 1) := by rw [h1.env (lc d) (lc_ok hd).1 ((lc_ok hd).2 0)]; exact hl
    have lpd : ∀ (y : DS VV MM) (v : ℕ), (∀ j < d, y.env (lc j) = b1.env (lc j) ∧ y.env (lb j) = b1.env (lb j)) →
        ∀ j < d, (y.set (lc d) v).env (lc j) = a.env (lc j) ∧ (y.set (lc d) v).env (lb j) = a.env (lb j) := by
      intro y v hy j hj
      have h1' : lc j ≠ lc d := ne_of_val (by rw [lc_val (by omega), lc_val hd]; omega)
      have h2' : lb j ≠ lc d := ne_of_val (by rw [lb_val (by omega), lc_val hd]; omega)
      rw [DS.set_env_ne _ _ h1', DS.set_env_ne _ _ h2', (hy j hj).1, (hy j hj).2, (p1.lp j hj).1, (p1.lp j hj).2]
      exact lx j hj
    refine Hs.ite (c := .eq (tmp 0) r0) (opd_ne (tmp_opd (by norm_num)) (by norm_num)) (fun hc => ?_) (fun hc => ?_)
    · simp only [Cnd.eval, h1.val, q1.env.c0, decide_eq_true_eq] at hc
      have hw : whileN (fun s' => evalE G s' c != 0) (evalS G body) (k + 1) s = s := by
        simp [whileN, hc]
      rw [hw]
      refine Hs.mono (hs_opq (OpEx.copy (lc d) nR b1 hwf)) (by omega) ?_
      rintro y rfl
      have q2 := q1.set_free (lcd_range hd).1 (lcd_range hd).2 (b1.env nR)
      have hl2 : (b1.set (lc d) (b1.env nR)).env (lc d) = G.N := by rw [DS.set_env_self, q1.env.n]
      exact Hs.mono (hs_loopF hwf (by simp only [Cnd.eval, hl2, q2.env.n, decide_eq_false_iff_not]; omega)
        ⟨q2, fx.trans (p1.fix.trans (Fix.set _ _ _)), lpd b1 _ (fun j hj => ⟨rfl, rfl⟩)⟩) (by omega) (fun _ h => h)
    · simp only [Cnd.eval, h1.val, q1.env.c0, decide_eq_false_iff_not] at hc
      have hw : whileN (fun s' => evalE G s' c != 0) (evalS G body) (k + 1) s =
          whileN (fun s' => evalE G s' c != 0) (evalS G body) k (evalS G body s) := by
        simp [whileN, hc]
      rw [hw] at hbad ⊢
      have hbody : (evalS G body s).bad = false := by
        cases hc' : (evalS G body s).bad
        · rfl
        · rw [whileN_bad _ _ (fun s' h' => bad_mono G body s' h') k _ hc'] at hbad; exact hbad
      refine hs_pre (t2 := 1) (hb (d + 1) s b1 (by omega) hwb hbody q1) (fun b2 h2 => ?_)
      have b2l : b2.env (lc d) = G.N - (k + 1) := by rw [(h2.lp d (by omega)).1, b1l]
      refine Hs.mono (hs_opq (OpEx.inc (lc d) b2 (by rw [b2l]; omega))) le_rfl ?_
      rintro b3 rfl
      have q3 := h2.rel.set_free (lcd_range hd).1 (lcd_range hd).2 (b2.env (lc d) + 1)
      exact whl_aux c hb d hd hwc hwb a k (by omega) _ _ q3 (by rw [DS.set_env_self, b2l]; omega)
        (fx.trans (p1.fix.trans (h2.fix.trans (Fix.set _ _ _))))
        (lpd b2 _ (fun j hj => h2.lp j (by omega))) hbad

include hg in
theorem whl_ok (c : E) {body : S} (hb : SOk C G body) : SOk C G (.whl c body) := by
  intro d s a hd8 hw hbad r
  simp only [wfS, Bool.and_eq_true, decide_eq_true_eq] at hw
  obtain ⟨⟨hwc, hd⟩, hwb⟩ := hw
  refine hs_step (OpEx.zero (lc d) a) ?_ |>.mono (t := G.N * (costE G c + costS G body + 12) + 6 + 2)
    (by simp only [costS]; omega) (fun _ h => h)
  have q := r.set_free (lcd_range hd).1 (lcd_range hd).2 0
  have := whl_aux hg c hb d hd hwc hwb a G.N le_rfl s _ q (by simp) (Fix.set _ _ _) (fun j hj => by
    have h1' : lc j ≠ lc d := ne_of_val (by rw [lc_val (by omega), lc_val hd]; omega)
    have h2' : lb j ≠ lc d := ne_of_val (by rw [lb_val (by omega), lc_val hd]; omega)
    exact ⟨DS.set_env_ne _ _ h1', DS.set_env_ne _ _ h2'⟩) hbad
  exact this

include hg in
theorem rd_ok (hinp : C.inp = G.inp) (i : Var) : SOk C G (.rd i) := by
  intro d s a hd8 hw hbad r
  have hlt : s.ip < G.inp.length := by
    by_contra h; simp [evalS, h] at hbad
  have hev : evalS G (.rd i) s = { s.setv i (G.inp.getD s.ip false).toNat with ip := s.ip + 1 } := by
    simp [evalS, hlt]
  rw [hev]
  refine Hs.mono (hs_opq (OpEx.rdI (uv i) a (by rw [r.ip, hinp]; exact hlt))) (by simp only [costS]; omega) ?_
  rintro b rfl
  have hbit : bitOf C.inp a.ip = (G.inp.getD s.ip false).toNat := by rw [bitOf, hinp, r.ip]
  have hv : (G.inp.getD s.ip false).toNat ≤ G.cap := by
    have := K_le_cap G hg.1; cases G.inp.getD s.ip false <;> simp <;> omega
  have q := r.setv i hv
  refine ⟨⟨Env.of_env (a := a.set (uv i) (G.inp.getD s.ip false).toNat) (by rw [hbit]) q.env,
    fun j => by rw [← q.uv j, hbit], q.out, q.le, q.fok, by simp [r.ip]⟩,
    ⟨rfl, rfl, rfl, rfl, rfl⟩, fun j hj => ?_⟩
  have h1' : lc j ≠ uv i := ne_of_val (by rw [lc_val (by omega), uv_val]; omega)
  have h2' : lb j ≠ uv i := ne_of_val (by rw [lb_val (by omega), uv_val]; omega)
  exact ⟨DS.set_env_ne _ _ h1', DS.set_env_ne _ _ h2'⟩

include hg in
/-- **Statements compile correctly** (proof of `thm:short-pcp-ours`: every program of `FL` runs in the cell language with its
`FL` semantics, within `costS`). -/
theorem compS_ok (hinp : C.inp = G.inp) : ∀ p : S, SOk C G p
  | .skip => skip_ok
  | .set i e => set_ok hg i e
  | .seq a b => seq_ok (compS_ok hinp a) (compS_ok hinp b)
  | .ite c a b => ite_ok hg (compS_ok hinp a) (compS_ok hinp b)
  | .loop i n body => loop_ok hg i n (compS_ok hinp body)
  | .whl c body => whl_ok hg c (compS_ok hinp body)
  | .emit e => emit_ok hg e
  | .field f p => field_ok hg f p
  | .rd i => rd_ok hg hinp i

end Stmt

end NearCubicGates.Adapters.ShortPCP.Machines.FL
