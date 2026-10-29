import SourceAdapters.ShortPCP.Machines.FLang
import SourceAdapters.ShortPCP.Machines.FieldCellsProof

/-!
# Single-run time, machine layer 5: the primitive operations of `FL` as cell programs

Each operation of the field-word language (`FLang.lean`) is a fixed cell program on two operand variables `x y`
(temporaries `16 … 31`), leaving its result in `x` and changing only `x` and the scratch variables (`9 … 15`,
`48 … 71`). Integer operations are clamped at `cap = 2^K − 1`; field operations reduce their operands mod `2^f` and
call the field kit `Joins/FieldCells.lean` (proof of `thm:short-pcp-ours`, "each field operation takes poly(f) steps"). Every
operation costs at most `opc G = 400 (K+1)^3 + 400` units.

Register layout of the compiled programs: `0, 1, 2` the constants; `3` = `cap`, `4` = `2^K`, `5` = `K`, `6` = `N`,
`7` = `2^f`, `8` = the modulus; `9 … 15` scratch; `16 … 31` expression temporaries; `32 … 47` loop counters and
bounds; `48 … 65` the field kit's block; `66 … 71` scratch; `72 … 127` the program variables.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace NearCubicGates.Adapters.ShortPCP.Machines.FL

open NearCubicGates.Close.Cells NearCubicWires.WireExponent3_5
open NearCubicGates.Adapters.Joins NearCubicGates.Adapters.Joins.FieldCells

/-! ## Registers -/

def r0 : Fin VV := vr 0
def r1 : Fin VV := vr 1
def r2 : Fin VV := vr 2
def capR : Fin VV := vr 3
def cap1R : Fin VV := vr 4
def kR : Fin VV := vr 5
def nR : Fin VV := vr 6
def tR : Fin VV := vr 7
def pR : Fin VV := vr 8
/-- Scratch `9 … 15`. -/
def sc (i : ℕ) : Fin VV := vr (9 + i)
/-- Expression temporary `d` (`d < 16`). -/
def tmp (d : ℕ) : Fin VV := vr (16 + d)
/-- Loop counter and loop bound at nesting depth `d` (`d < 8`). -/
def lc (d : ℕ) : Fin VV := vr (32 + 2 * d)
def lb (d : ℕ) : Fin VV := vr (33 + 2 * d)
/-- A scratch variable written by the empty statement. -/
def junk : Fin VV := vr 66
/-- Program variable `i`. -/
def uv (i : Var) : Fin VV := vr (72 + i.val)

/-- The field kit's block starts here. -/
abbrev fb : ℕ := 48

theorem vr_val' {i : ℕ} (h : i < VV) : (vr i).val = i := Nat.mod_eq_of_lt h

theorem uv_val (i : Var) : (uv i).val = 72 + i.val := vr_val' (by have := i.isLt; simp only [VV, NU] at *; omega)
theorem tmp_val {d : ℕ} (h : d < 16) : (tmp d).val = 16 + d := vr_val' (by simp only [VV]; omega)
theorem lc_val {d : ℕ} (h : d < 8) : (lc d).val = 32 + 2 * d := vr_val' (by simp only [VV]; omega)
theorem lb_val {d : ℕ} (h : d < 8) : (lb d).val = 33 + 2 * d := vr_val' (by simp only [VV]; omega)
theorem sc_val {i : ℕ} (h : i < 7) : (sc i).val = 9 + i := vr_val' (by simp only [VV]; omega)

theorem uv_inj {i j : Var} (h : uv i = uv j) : i = j := by
  have := congrArg Fin.val h; rw [uv_val, uv_val] at this; exact Fin.ext (by omega)

/-- Distinct registers, by their numbers. -/
theorem ne_of_val {x y : Fin VV} (h : x.val ≠ y.val) : x ≠ y := fun e => h (congrArg Fin.val e)

/-- Scratch registers (changed freely by every operation). -/
def Scr (z : Fin VV) : Prop := (9 ≤ z.val ∧ z.val < 16) ∨ (48 ≤ z.val ∧ z.val < 72)

/-- Operand registers: the temporaries. -/
def Opd (x : Fin VV) : Prop := 16 ≤ x.val ∧ x.val < 32

/-- The fixed registers of a run (field `𝔽₂[X]/(fp)` of degree `fl`). -/
structure Env (G : Glob) (fl fp : ℕ) (a : DS VV MM) : Prop where
  c0 : a.env r0 = 0
  c1 : a.env r1 = 1
  c2 : a.env r2 = 2
  cap : a.env capR = G.cap
  cap1 : a.env cap1R = 2 ^ G.K
  k : a.env kR = G.K
  n : a.env nR = G.N
  t : a.env tR = 2 ^ fl
  p : a.env pR = fp

/-- The run constants fit the width. -/
def GOk (C : Ctx) (G : Glob) : Prop := 3 ≤ G.K ∧ G.K + 1 ≤ C.Wd ∧ G.N ≤ G.cap

/-- Only `x` and scratch change; the non-variable part is unchanged. -/
structure Keep (x : Fin VV) (a b : DS VV MM) : Prop where
  sh : b.sh = a.sh
  env : ∀ z, ¬ Scr z → z ≠ x → b.env z = a.env z

theorem Keep.refl (x : Fin VV) (a : DS VV MM) : Keep x a a := ⟨rfl, fun _ _ _ => rfl⟩

theorem Keep.trans {x : Fin VV} {a b c : DS VV MM} (h1 : Keep x a b) (h2 : Keep x b c) : Keep x a c :=
  ⟨h2.sh.trans h1.sh, fun z hz hx => (h2.env z hz hx).trans (h1.env z hz hx)⟩

theorem Keep.set {x y : Fin VV} (a : DS VV MM) (v : ℕ) (hy : Scr y ∨ y = x) : Keep x a (a.set y v) := by
  refine ⟨rfl, fun z hz hx => DS.set_env_ne _ _ ?_⟩
  rintro rfl; rcases hy with h | h
  · exact hz h
  · exact hx h

theorem Keep.env_of {x : Fin VV} {a b : DS VV MM} (h : Keep x a b) {z : Fin VV} (hz : z.val < 9 ∨ (72 ≤ z.val) ∨
    (16 ≤ z.val ∧ z.val < 48)) (hx : z ≠ x) : b.env z = a.env z :=
  h.env z (by unfold Scr; omega) hx

theorem Env.keep {G : Glob} {fl fp : ℕ} {x : Fin VV} {a b : DS VV MM} (he : Env G fl fp a) (hk : Keep x a b)
    (hx : 9 ≤ x.val) : Env G fl fp b := by
  have h : ∀ i, i < 9 → b.env (vr i) = a.env (vr i) := fun i hi =>
    hk.env_of (by rw [vr_val' (by simp only [VV]; omega)]; omega)
      (ne_of_val (by rw [vr_val' (by simp only [VV]; omega)]; omega))
  exact ⟨(h 0 (by omega)).trans he.c0, (h 1 (by omega)).trans he.c1, (h 2 (by omega)).trans he.c2,
    (h 3 (by omega)).trans he.cap, (h 4 (by omega)).trans he.cap1, (h 5 (by omega)).trans he.k,
    (h 6 (by omega)).trans he.n, (h 7 (by omega)).trans he.t, (h 8 (by omega)).trans he.p⟩

/-! ## Step lemmas -/

section Steps

variable {C : Ctx}

theorem hs_opq {o : Op VV MM} {a b : DS VV MM} {k : ℕ} (h : OpEx C o a b k) : Hs C (.op o) a k (· = b) :=
  Hs.op h rfl

theorem hs_step {o : Op VV MM} {r : St VV MM} {a b : DS VV MM} {t : ℕ} {R : DS VV MM → Prop}
    (h : OpEx C o a b 1) (hr : Hs C r b t R) : Hs C (.seq (.op o) r) a (t + 2) R :=
  Hs.mono (Hs.seq (hs_opq h) (fun _ e => e ▸ hr)) (by omega) (fun _ h => h)

theorem hs_pre {p r : St VV MM} {a : DS VV MM} {t1 t2 : ℕ} {R1 R : DS VV MM → Prop}
    (h1 : Hs C p a t1 R1) (h2 : ∀ b, R1 b → Hs C r b t2 R) : Hs C (.seq p r) a (t1 + t2 + 1) R := Hs.seq h1 h2

end Steps

/-! ## Arithmetic facts -/

theorem cap_add (G : Glob) : G.cap + 1 = 2 ^ G.K := by
  unfold Glob.cap; have := Nat.one_le_two_pow (n := G.K); omega

theorem two_cap_lt {C : Ctx} {G : Glob} (hG : GOk C G) : 2 * G.cap + 2 ≤ 2 ^ C.Wd := by
  have h1 := cap_add G
  have h2 : 2 ^ (G.K + 1) ≤ 2 ^ C.Wd := Nat.pow_le_pow_right (by norm_num) hG.2.1
  rw [pow_succ] at h2; omega

theorem add_two_lt_pow : ∀ n : ℕ, 3 ≤ n → n + 2 < 2 ^ n
  | 0, h | 1, h | 2, h => by omega
  | 3, _ => by norm_num
  | n + 4, _ => by have := add_two_lt_pow (n + 3) (by omega); rw [pow_succ]; omega

theorem K_le_cap (G : Glob) (h : 3 ≤ G.K) : G.K + 1 ≤ G.cap := by
  have h1 := cap_add G
  have := add_two_lt_pow G.K h
  omega

theorem fl_bounds {G : Glob} {fl fp : ℕ} (h : fieldOk G fl fp = true) :
    1 ≤ fl ∧ fl + 2 ≤ G.K ∧ GF.ModulusOk fp fl ∧ 4 * 2 ^ fl ≤ 2 ^ G.K := by
  simp only [fieldOk, decide_eq_true_eq] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2, ⟨?_, by rw [pow_succ]; omega⟩, ?_⟩
  · rw [Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_eq]
    have hq : fp / 2 ^ fl = 1 := by
      apply le_antisymm
      · exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul (by positivity)).mpr (by omega))
      · exact (Nat.le_div_iff_mul_le (by positivity)).mpr (by omega)
    rw [hq]
  · calc 4 * 2 ^ fl = 2 ^ (fl + 2) := by rw [pow_add]; ring
      _ ≤ 2 ^ G.K := Nat.pow_le_pow_right (by norm_num) h2

theorem tf_le {G : Glob} {fl fp : ℕ} (h : fieldOk G fl fp = true) : 2 * 2 ^ fl ≤ G.cap := by
  have := (fl_bounds h).2.2.2; have := cap_add G; have : 1 ≤ 2 ^ fl := Nat.one_le_two_pow; omega

/-! ## The macros -/

def nop : St VV MM := .op (.zero junk)

def clampM (x : Fin VV) : St VV MM := .ite (.lt capR x) (.op (.copy x capR)) nop

def addM (x y : Fin VV) : St VV MM := .seq (.op (.add x y)) (clampM x)

def subM (x y : Fin VV) : St VV MM := .ite (.lt x y) (.op (.zero x)) (.op (.sub x y))

def mulM (x y : Fin VV) : St VV MM :=
  .ite (.eq y r0) (.op (.zero x))
    (.seq (.op (.dm capR y (sc 0) (sc 1)))
      (.ite (.lt (sc 0) x) (.op (.copy x capR)) (.seq (.op (.mul x y (sc 2))) (.op (.copy x (sc 2))))))

def divM (x y : Fin VV) : St VV MM :=
  .ite (.eq y r0) (.op (.zero x)) (.seq (.op (.dm x y (sc 0) (sc 1))) (.op (.copy x (sc 0))))

def mdM (x y : Fin VV) : St VV MM :=
  .ite (.eq y r0) nop (.seq (.op (.dm x y (sc 0) (sc 1))) (.op (.copy x (sc 1))))

/-- `sc 0 := min y K`, `sc 1 := 0`. -/
def passM (y : Fin VV) : St VV MM :=
  .seq (.op (.copy (sc 0) y)) (.seq (.ite (.lt kR (sc 0)) (.op (.copy (sc 0) kR)) nop) (.op (.zero (sc 1))))

def shlBody (x : Fin VV) : St VV MM :=
  .seq (.op (.copy (sc 2) x)) (.seq (.op (.shl (sc 2)))
    (.seq (.ite (.lt capR (sc 2)) (.op (.copy x capR)) (.op (.copy x (sc 2)))) (.op (.inc (sc 1)))))

def shlM (x y : Fin VV) : St VV MM :=
  .ite (.eq x r0) nop (.seq (passM y) (.loop (.lt (sc 1) (sc 0)) (shlBody x)))

def shrM (x y : Fin VV) : St VV MM :=
  .seq (passM y) (.loop (.lt (sc 1) (sc 0)) (.seq (.op (.half x)) (.op (.inc (sc 1)))))

def bxorM (x y : Fin VV) : St VV MM := .seq (fxorS x y (sc 3) cap1R fb) (.op (.copy x (sc 3)))

def faddM (x y : Fin VV) : St VV MM := .seq (fxorS x y (sc 3) tR fb) (.op (.copy x (sc 3)))

def fmulM (x y : Fin VV) : St VV MM :=
  .seq (.op (.dm x tR (sc 0) (sc 4))) (.seq (.op (.dm y tR (sc 0) (sc 5)))
    (.seq (fmulS (sc 4) (sc 5) (sc 3) tR pR fb) (.op (.copy x (sc 3)))))

def fpowM (x y : Fin VV) : St VV MM :=
  .seq (.op (.dm x tR (sc 0) (sc 4))) (.seq (fpowS (sc 4) y (sc 3) tR pR fb) (.op (.copy x (sc 3))))

def finvM (x : Fin VV) : St VV MM :=
  .seq (.op (.dm x tR (sc 0) (sc 4))) (.seq (finvS (sc 4) (sc 3) tR pR fb) (.op (.copy x (sc 3))))

def ltM (x y : Fin VV) : St VV MM := .ite (.lt x y) (.seq (.op (.zero x)) (.op (.inc x))) (.op (.zero x))

def eqM (x y : Fin VV) : St VV MM := .ite (.eq x y) (.seq (.op (.zero x)) (.op (.inc x))) (.op (.zero x))

/-- `x := min (x + n) cap` by `n` guarded increments. -/
def incK : ℕ → Fin VV → St VV MM
  | 0, _ => nop
  | n + 1, x => .seq (incK n x) (.ite (.lt x capR) (.op (.inc x)) nop)

/-! ## Specifications -/

section Specs

variable {C : Ctx} {G : Glob} {fl fp : ℕ}

/-- The common hypotheses of a binary operation on `x`, `y`. -/
structure Bin (C : Ctx) (G : Glob) (fl fp : ℕ) (x y : Fin VV) (a : DS VV MM) : Prop where
  g : GOk C G
  env : Env G fl fp a
  fok : fieldOk G fl fp = true
  ox : Opd x
  oy : Opd y
  xy : x ≠ y
  hx : a.env x ≤ G.cap
  hy : a.env y ≤ G.cap

theorem scr_sc {i : ℕ} (h : i < 7) : Scr (sc i) := by unfold Scr; rw [sc_val h]; omega
theorem scr_junk : Scr junk := by unfold Scr junk; rw [vr_val' (by simp only [VV]; omega)]; omega

theorem opd_ne {x : Fin VV} (hx : Opd x) {i : ℕ} (hi : i < 9) : x ≠ vr i :=
  ne_of_val (by rw [vr_val' (by simp only [VV]; omega)]; unfold Opd at hx; omega)
theorem opd_ne_sc {x : Fin VV} (hx : Opd x) {i : ℕ} (hi : i < 7) : x ≠ sc i :=
  ne_of_val (by rw [sc_val hi]; unfold Opd at hx; omega)
theorem opd_ne_junk {x : Fin VV} (hx : Opd x) : x ≠ junk :=
  ne_of_val (by unfold junk; rw [vr_val' (by simp only [VV]; omega)]; unfold Opd at hx; omega)

theorem nop_spec (x : Fin VV) (a : DS VV MM) : Hs C nop a 1 (fun b => b.env x = a.env x ∨ x = junk) ∧
    Hs C nop a 1 (Keep x a) := by
  constructor
  · refine Hs.mono (hs_opq (OpEx.zero junk a)) le_rfl ?_
    rintro b rfl
    by_cases h : x = junk
    · exact Or.inr h
    · exact Or.inl (DS.set_env_ne _ _ h)
  · exact Hs.mono (hs_opq (OpEx.zero junk a)) le_rfl (by rintro b rfl; exact Keep.set a 0 (Or.inl scr_junk))

theorem nop_keep (x : Fin VV) (a : DS VV MM) (hx : x ≠ junk) : Hs C nop a 1 (fun b => b.env x = a.env x ∧ Keep x a b) :=
  Hs.mono (hs_opq (OpEx.zero junk a)) le_rfl
    (by rintro b rfl; exact ⟨DS.set_env_ne _ _ hx, Keep.set a 0 (Or.inl scr_junk)⟩)

theorem ne_capR {x : Fin VV} (hx : Opd x) : x ≠ capR := opd_ne hx (by norm_num)

theorem clampM_spec (x : Fin VV) (a : DS VV MM) (he : Env G fl fp a) (ox : Opd x) :
    Hs C (clampM x) a 2 (fun b => b.env x = min (a.env x) G.cap ∧ Keep x a b) := by
  unfold clampM
  refine Hs.ite (Ne.symm (ne_capR ox)) (fun hc => ?_) (fun hc => ?_)
  · simp only [Cnd.eval, he.cap, decide_eq_true_eq] at hc
    refine Hs.mono (hs_opq (OpEx.copy x capR a (ne_capR ox))) le_rfl ?_
    rintro b rfl
    exact ⟨by simp [he.cap]; omega, Keep.set a _ (Or.inr rfl)⟩
  · simp only [Cnd.eval, he.cap, decide_eq_false_iff_not, not_lt] at hc
    refine Hs.mono (nop_keep x a (opd_ne_junk ox)) le_rfl ?_
    rintro b ⟨h1, h2⟩
    exact ⟨by rw [h1]; omega, h2⟩


/-- After a field-kit call: only the output `sc 3` and the kit's block changed. -/
theorem keep_of_fr {a b : DS VV MM} {k : ℕ} (hk : k ≤ 18) (hsh : b.sh = a.sh) (hf : Fr a b (sc 3 :: blk fb k))
    (x : Fin VV) : Keep x a b := by
  refine ⟨hsh, fun z hz _ => hf z ?_⟩
  intro hm
  rcases List.mem_cons.mp hm with rfl | hm
  · exact hz (scr_sc (by norm_num))
  · rw [mem_blk _ (by simp only [VV, fb]; omega)] at hm; exact hz (by unfold Scr; simp only [fb] at hm; omega)

theorem opd_ge {x : Fin VV} (h : Opd x) : 9 ≤ x.val := by unfold Opd at h; omega

theorem keep_set_self (x : Fin VV) (a : DS VV MM) (v : ℕ) : Keep x a (a.set x v) := Keep.set a v (Or.inr rfl)
theorem keep_set_sc (x : Fin VV) (a : DS VV MM) (v : ℕ) {i : ℕ} (hi : i < 7) : Keep x a (a.set (sc i) v) :=
  Keep.set a v (Or.inl (scr_sc hi))

theorem addM_spec {x y : Fin VV} {a : DS VV MM} (h : Bin C G fl fp x y a) :
    Hs C (addM x y) a (opc G) (fun b => b.env x = min (a.env x + a.env y) G.cap ∧ Keep x a b) := by
  have hW := two_cap_lt h.g
  have hx := h.hx; have hy := h.hy
  refine Hs.mono (hs_pre (t2 := 2) (hs_opq (OpEx.add x y a h.xy (by omega))) (fun b hb => ?_))
    (by unfold opc; omega) (fun _ h => h)
  subst hb
  refine Hs.mono (clampM_spec x _ (h.env.keep (keep_set_self x a _) (opd_ge h.ox)) h.ox) le_rfl ?_
  rintro c ⟨c1, c2⟩
  exact ⟨by rw [c1]; simp, (keep_set_self x a _).trans c2⟩

theorem subM_spec {x y : Fin VV} {a : DS VV MM} (h : Bin C G fl fp x y a) :
    Hs C (subM x y) a (opc G) (fun b => b.env x = a.env x - a.env y ∧ Keep x a b) := by
  unfold subM
  refine Hs.mono (Hs.ite (t := 1) h.xy (fun hc => ?_) (fun hc => ?_)) (by unfold opc; omega) (fun _ h => h)
  · simp only [Cnd.eval, decide_eq_true_eq] at hc
    exact Hs.mono (hs_opq (OpEx.zero x a)) le_rfl (by
      rintro b rfl; exact ⟨by simp; omega, keep_set_self x a _⟩)
  · simp only [Cnd.eval, decide_eq_false_iff_not, not_lt] at hc
    exact Hs.mono (hs_opq (OpEx.sub x y a h.xy hc)) le_rfl (by
      rintro b rfl; exact ⟨by simp, keep_set_self x a _⟩)

theorem mul_clamp (u w c : ℕ) (hw : 0 < w) : (c / w < u → min (u * w) c = c) ∧ (u ≤ c / w → u * w ≤ c) := by
  constructor
  · intro h
    have : c < u * w := by
      have := (Nat.div_lt_iff_lt_mul hw).mp h; exact this
    omega
  · intro h; exact (Nat.le_div_iff_mul_le hw).mp h

theorem mulM_spec {x y : Fin VV} {a : DS VV MM} (h : Bin C G fl fp x y a) :
    Hs C (mulM x y) a (opc G) (fun b => b.env x = min (a.env x * a.env y) G.cap ∧ Keep x a b) := by
  unfold mulM
  have hW := two_cap_lt h.g
  have e := h.env
  have hx := h.hx; have hy := h.hy
  have ny0 : y ≠ r0 := opd_ne h.oy (by norm_num)
  refine Hs.mono (Hs.ite (t := 8) ny0 (fun hc => ?_) (fun hc => ?_)) (by unfold opc; omega) (fun _ h => h)
  · simp only [Cnd.eval, e.c0, decide_eq_true_eq] at hc
    exact Hs.mono (hs_opq (OpEx.zero x a)) (by omega) (by
      rintro b rfl; exact ⟨by simp [hc], keep_set_self x a _⟩)
  · simp only [Cnd.eval, e.c0, decide_eq_false_iff_not] at hc
    have hpos : 0 < a.env y := Nat.pos_of_ne_zero hc
    have hcy : capR ≠ y := Ne.symm (ne_capR h.oy)
    refine hs_step (OpEx.dm capR y (sc 0) (sc 1) a hcy (by decide) (by decide) (opd_ne_sc h.oy (by norm_num))
      (opd_ne_sc h.oy (by norm_num)) (by decide) hpos (by omega)) ?_
    set a1 := (a.set (sc 0) (a.env capR / a.env y)).set (sc 1) (a.env capR % a.env y) with ha1
    have k1 : Keep x a a1 := (keep_set_sc x a _ (by norm_num)).trans (keep_set_sc x _ _ (by norm_num))
    have a1x : a1.env x = a.env x := by
      rw [ha1, DS.set_env_ne _ _ (opd_ne_sc h.ox (by norm_num)), DS.set_env_ne _ _ (opd_ne_sc h.ox (by norm_num))]
    have a1y : a1.env y = a.env y := by
      rw [ha1, DS.set_env_ne _ _ (opd_ne_sc h.oy (by norm_num)), DS.set_env_ne _ _ (opd_ne_sc h.oy (by norm_num))]
    have a1q : a1.env (sc 0) = G.cap / a.env y := by
      rw [ha1, DS.set_env_ne _ _ (by decide), DS.set_env_self, e.cap]
    have a1c : a1.env capR = G.cap := by
      rw [ha1, DS.set_env_ne _ _ (by decide), DS.set_env_ne _ _ (by decide), e.cap]
    obtain ⟨m1, m2⟩ := mul_clamp (a.env x) (a.env y) G.cap hpos
    refine Hs.ite (t := 5) (c := .lt (sc 0) x)
      (show sc 0 ≠ x from ne_of_val (by rw [sc_val (by norm_num)]; have := h.ox; unfold Opd at this; omega))
      (fun hc2 => ?_) (fun hc2 => ?_)
    · simp only [Cnd.eval, a1q, a1x, decide_eq_true_eq] at hc2
      exact Hs.mono (hs_opq (OpEx.copy x capR a1 (ne_capR h.ox))) (by omega) (by
        rintro b rfl; exact ⟨by simp [a1c, m1 hc2], k1.trans (keep_set_self x _ _)⟩)
    · simp only [Cnd.eval, a1q, a1x, decide_eq_false_iff_not, not_lt] at hc2
      have hm := m2 hc2
      refine hs_step (OpEx.mul x y (sc 2) a1 h.xy (opd_ne_sc h.ox (by norm_num)) (opd_ne_sc h.oy (by norm_num))
        (by rw [a1x, a1y]; omega)) ?_
      refine Hs.mono (hs_opq (OpEx.copy x (sc 2) _ (opd_ne_sc h.ox (by norm_num)))) (by omega) ?_
      rintro b rfl
      refine ⟨by simp [a1x, a1y]; omega, k1.trans ((keep_set_sc x _ _ (by norm_num)).trans (keep_set_self x _ _))⟩

theorem divM_spec {x y : Fin VV} {a : DS VV MM} (h : Bin C G fl fp x y a) :
    Hs C (divM x y) a (opc G) (fun b => b.env x = a.env x / a.env y ∧ Keep x a b) := by
  unfold divM
  have hW := two_cap_lt h.g
  have e := h.env
  have hx := h.hx; have hy := h.hy
  refine Hs.mono (Hs.ite (t := 3) (opd_ne h.oy (by norm_num)) (fun hc => ?_) (fun hc => ?_)) (by unfold opc; omega)
    (fun _ h => h)
  · simp only [Cnd.eval, e.c0, decide_eq_true_eq] at hc
    exact Hs.mono (hs_opq (OpEx.zero x a)) (by omega) (by
      rintro b rfl; exact ⟨by simp [hc], keep_set_self x a _⟩)
  · simp only [Cnd.eval, e.c0, decide_eq_false_iff_not] at hc
    refine hs_step (OpEx.dm x y (sc 0) (sc 1) a h.xy (opd_ne_sc h.ox (by norm_num)) (opd_ne_sc h.ox (by norm_num))
      (opd_ne_sc h.oy (by norm_num)) (opd_ne_sc h.oy (by norm_num)) (by decide) (Nat.pos_of_ne_zero hc) (by omega)) ?_
    refine Hs.mono (hs_opq (OpEx.copy x (sc 0) _ (opd_ne_sc h.ox (by norm_num)))) le_rfl ?_
    rintro b rfl
    refine ⟨by simp [DS.set_env_ne _ _ (show sc 0 ≠ sc 1 by decide)], ?_⟩
    exact ((keep_set_sc x a _ (by norm_num)).trans (keep_set_sc x _ _ (by norm_num))).trans (keep_set_self x _ _)

theorem mdM_spec {x y : Fin VV} {a : DS VV MM} (h : Bin C G fl fp x y a) :
    Hs C (mdM x y) a (opc G) (fun b => b.env x = a.env x % a.env y ∧ Keep x a b) := by
  unfold mdM
  have hW := two_cap_lt h.g
  have e := h.env
  have hx := h.hx; have hy := h.hy
  refine Hs.mono (Hs.ite (t := 3) (opd_ne h.oy (by norm_num)) (fun hc => ?_) (fun hc => ?_)) (by unfold opc; omega)
    (fun _ h => h)
  · simp only [Cnd.eval, e.c0, decide_eq_true_eq] at hc
    exact Hs.mono (nop_keep x a (opd_ne_junk h.ox)) (by omega) (by
      rintro b ⟨b1, b2⟩; exact ⟨by rw [b1, hc, Nat.mod_zero], b2⟩)
  · simp only [Cnd.eval, e.c0, decide_eq_false_iff_not] at hc
    refine hs_step (OpEx.dm x y (sc 0) (sc 1) a h.xy (opd_ne_sc h.ox (by norm_num)) (opd_ne_sc h.ox (by norm_num))
      (opd_ne_sc h.oy (by norm_num)) (opd_ne_sc h.oy (by norm_num)) (by decide) (Nat.pos_of_ne_zero hc) (by omega)) ?_
    refine Hs.mono (hs_opq (OpEx.copy x (sc 1) _ (opd_ne_sc h.ox (by norm_num)))) le_rfl ?_
    rintro b rfl
    refine ⟨by simp, ?_⟩
    exact ((keep_set_sc x a _ (by norm_num)).trans (keep_set_sc x _ _ (by norm_num))).trans (keep_set_self x _ _)

theorem ltM_spec {x y : Fin VV} {a : DS VV MM} (h : Bin C G fl fp x y a) :
    Hs C (ltM x y) a (opc G) (fun b => b.env x = (if a.env x < a.env y then 1 else 0) ∧ Keep x a b) := by
  unfold ltM
  have hW := two_cap_lt h.g
  refine Hs.mono (Hs.ite (t := 3) h.xy (fun hc => ?_) (fun hc => ?_)) (by unfold opc; omega) (fun _ h => h)
  · simp only [Cnd.eval, decide_eq_true_eq] at hc
    refine hs_step (OpEx.zero x a) ?_
    refine Hs.mono (hs_opq (OpEx.inc x _ (by simp only [DS.set_env_self]; omega))) le_rfl ?_
    rintro b rfl
    exact ⟨by simp [hc], (keep_set_self x a _).trans (keep_set_self x _ _)⟩
  · simp only [Cnd.eval, decide_eq_false_iff_not] at hc
    exact Hs.mono (hs_opq (OpEx.zero x a)) (by omega) (by
      rintro b rfl; exact ⟨by simp [hc], keep_set_self x a _⟩)

theorem eqM_spec {x y : Fin VV} {a : DS VV MM} (h : Bin C G fl fp x y a) :
    Hs C (eqM x y) a (opc G) (fun b => b.env x = (if a.env x = a.env y then 1 else 0) ∧ Keep x a b) := by
  unfold eqM
  have hW := two_cap_lt h.g
  refine Hs.mono (Hs.ite (t := 3) h.xy (fun hc => ?_) (fun hc => ?_)) (by unfold opc; omega) (fun _ h => h)
  · simp only [Cnd.eval, decide_eq_true_eq] at hc
    refine hs_step (OpEx.zero x a) ?_
    refine Hs.mono (hs_opq (OpEx.inc x _ (by simp only [DS.set_env_self]; omega))) le_rfl ?_
    rintro b rfl
    exact ⟨by simp [hc], (keep_set_self x a _).trans (keep_set_self x _ _)⟩
  · simp only [Cnd.eval, decide_eq_false_iff_not] at hc
    exact Hs.mono (hs_opq (OpEx.zero x a)) (by omega) (by
      rintro b rfl; exact ⟨by simp [hc], keep_set_self x a _⟩)


/-- Only scratch variables change. -/
def KeepS (a b : DS VV MM) : Prop := b.sh = a.sh ∧ ∀ z, ¬ Scr z → b.env z = a.env z

theorem KeepS.keep {a b : DS VV MM} (h : KeepS a b) (x : Fin VV) : Keep x a b := ⟨h.1, fun z hz _ => h.2 z hz⟩

theorem keepS_set (a : DS VV MM) {i : ℕ} (hi : i < 7) (v : ℕ) : KeepS a (a.set (sc i) v) :=
  ⟨rfl, fun z hz => DS.set_env_ne _ _ (by rintro rfl; exact hz (scr_sc hi))⟩

theorem KeepS.trans {a b c : DS VV MM} (h1 : KeepS a b) (h2 : KeepS b c) : KeepS a c :=
  ⟨h2.1.trans h1.1, fun z hz => (h2.2 z hz).trans (h1.2 z hz)⟩

theorem passM_spec (y : Fin VV) (a : DS VV MM) (e : Env G fl fp a) (oy : Opd y) :
    Hs C (passM y) a 6 (fun b => b.env (sc 0) = min (a.env y) G.K ∧ b.env (sc 1) = 0 ∧ KeepS a b) := by
  unfold passM
  refine hs_step (OpEx.copy (sc 0) y a (Ne.symm (opd_ne_sc oy (by norm_num)))) ?_
  set a1 := a.set (sc 0) (a.env y)
  have k1 : KeepS a a1 := keepS_set a (by norm_num) _
  have a1k : a1.env kR = G.K := by simp only [a1, DS.set_env_ne _ _ (show kR ≠ sc 0 by decide), e.k]
  refine hs_pre (t1 := 2) (t2 := 1) (R1 := fun b => b.env (sc 0) = min (a.env y) G.K ∧ KeepS a b)
    (Hs.ite (c := .lt kR (sc 0)) (show kR ≠ sc 0 by decide) (fun hc => ?_) (fun hc => ?_)) (fun b hb => ?_)
  · simp only [Cnd.eval, a1k, a1, DS.set_env_self, decide_eq_true_eq] at hc
    refine Hs.mono (hs_opq (OpEx.copy (sc 0) kR a1 (by decide))) le_rfl ?_
    rintro b rfl
    exact ⟨by simp [a1k]; omega, k1.trans (keepS_set _ (by norm_num) _)⟩
  · simp only [Cnd.eval, a1k, a1, DS.set_env_self, decide_eq_false_iff_not, not_lt] at hc
    refine Hs.mono (hs_opq (OpEx.zero junk a1)) (by omega) ?_
    rintro b rfl
    refine ⟨by simp only [DS.set_env_ne _ _ (show sc 0 ≠ junk by decide), a1, DS.set_env_self]; omega,
      k1.trans ⟨rfl, fun z hz => DS.set_env_ne _ _ (by rintro rfl; exact hz scr_junk)⟩⟩
  · refine Hs.mono (hs_opq (OpEx.zero (sc 1) b)) le_rfl ?_
    rintro c rfl
    exact ⟨by rw [DS.set_env_ne _ _ (by decide)]; exact hb.1, by simp, hb.2.trans (keepS_set _ (by norm_num) _)⟩

theorem min_two_mul (A c : ℕ) : min (2 * min A c) c = min (2 * A) c := by omega

theorem shlM_spec {x y : Fin VV} {a : DS VV MM} (h : Bin C G fl fp x y a) :
    Hs C (shlM x y) a (opc G) (fun b => b.env x = min (a.env x * 2 ^ a.env y) G.cap ∧ Keep x a b) := by
  unfold shlM
  have hW := two_cap_lt h.g
  have e := h.env
  have hK := K_le_cap G h.g.1
  have hx := h.hx
  have hcp := cap_add G
  have hK3 : G.K + 1 ≤ (G.K + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
  refine Hs.mono (Hs.ite (t := 10 * G.K + 12) (opd_ne h.ox (by norm_num)) (fun hc => ?_) (fun hc => ?_))
    (by unfold opc; omega) (fun _ h => h)
  · simp only [Cnd.eval, e.c0, decide_eq_true_eq] at hc
    exact Hs.mono (nop_keep x a (opd_ne_junk h.ox)) (by omega) (by
      rintro b ⟨b1, b2⟩; exact ⟨by rw [b1, hc]; simp, b2⟩)
  · simp only [Cnd.eval, e.c0, decide_eq_false_iff_not] at hc
    set m := min (a.env y) G.K with hm
    refine hs_pre (t1 := 6) (t2 := m * (8 + 2) + 2) (passM_spec y a e h.oy) (fun b hb => ?_) |>.mono
      (by have : m ≤ G.K := min_le_right _ _; nlinarith) (fun _ h => h)
    obtain ⟨b0, b1, b2⟩ := hb
    have bx : b.env x = a.env x := b2.2 x (by have := h.ox; unfold Opd at this; unfold Scr; omega)
    let I : ℕ → DS VV MM → Prop := fun j c => c.env (sc 1) = j ∧ c.env (sc 0) = m ∧
      c.env x = min (a.env x * 2 ^ j) G.cap ∧ Keep x a c
    have hI0 : I 0 b := ⟨b1, by rw [b0], by rw [bx]; simp; omega, b2.keep x⟩
    refine Hs.mono (Hs.loopN (c := .lt (sc 1) (sc 0)) (show sc 1 ≠ sc 0 by decide) I m 8 ?_ ?_ b hI0) le_rfl ?_
    · intro j hj c ⟨c1, c0, cx, ck⟩
      refine ⟨by simp only [Cnd.eval, c1, c0, decide_eq_true_eq]; exact hj, ?_⟩
      have ec := e.keep ck (opd_ge h.ox)
      have hv : c.env x ≤ G.cap := by rw [cx]; exact min_le_right _ _
      unfold shlBody
      refine hs_step (OpEx.copy (sc 2) x c (Ne.symm (opd_ne_sc h.ox (by norm_num)))) ?_
      refine hs_step (OpEx.shl (sc 2) _ (by simp only [DS.set_env_self]; omega)) ?_
      set c2 := (c.set (sc 2) (c.env x)).set (sc 2) (2 * (c.set (sc 2) (c.env x)).env (sc 2)) with hc2
      have c2s : c2.env (sc 2) = 2 * c.env x := by simp [c2]
      have c2c : c2.env capR = G.cap := by
        simp only [c2, DS.set_env_ne _ _ (show capR ≠ sc 2 by decide), ec.cap]
      have kc2 : Keep x c c2 := (keep_set_sc x c _ (by norm_num)).trans (keep_set_sc x _ _ (by norm_num))
      have c2_1 : c2.env (sc 1) = j := by simp only [c2, DS.set_env_ne _ _ (show sc 1 ≠ sc 2 by decide), c1]
      have c2_0 : c2.env (sc 0) = m := by simp only [c2, DS.set_env_ne _ _ (show sc 0 ≠ sc 2 by decide), c0]
      refine hs_pre (t1 := 2) (t2 := 1) (R1 := fun d => d.env x = min (a.env x * 2 ^ (j + 1)) G.cap ∧
          d.env (sc 1) = j ∧ d.env (sc 0) = m ∧ Keep x c d)
        (Hs.ite (show capR ≠ sc 2 by decide) (fun hc' => ?_) (fun hc' => ?_)) (fun d hd => ?_)
      · simp only [Cnd.eval, c2c, c2s, decide_eq_true_eq] at hc'
        refine Hs.mono (hs_opq (OpEx.copy x capR c2 (ne_capR h.ox))) le_rfl ?_
        rintro d rfl
        refine ⟨?_, ?_, ?_, kc2.trans (keep_set_self x _ _)⟩
        · simp only [DS.set_env_self, c2c]; rw [cx] at hc'; rw [pow_succ, ← mul_assoc, mul_comm _ 2,
            ← min_two_mul]; omega
        · rw [DS.set_env_ne _ _ (opd_ne_sc h.ox (by norm_num)).symm, c2_1]
        · rw [DS.set_env_ne _ _ (opd_ne_sc h.ox (by norm_num)).symm, c2_0]
      · simp only [Cnd.eval, c2c, c2s, decide_eq_false_iff_not, not_lt] at hc'
        refine Hs.mono (hs_opq (OpEx.copy x (sc 2) c2 (opd_ne_sc h.ox (by norm_num)))) (by omega) ?_
        rintro d rfl
        refine ⟨?_, ?_, ?_, kc2.trans (keep_set_self x _ _)⟩
        · simp only [DS.set_env_self, c2s]; rw [cx] at hc' ⊢; rw [pow_succ, ← mul_assoc, mul_comm _ 2,
            ← min_two_mul]; omega
        · rw [DS.set_env_ne _ _ (opd_ne_sc h.ox (by norm_num)).symm, c2_1]
        · rw [DS.set_env_ne _ _ (opd_ne_sc h.ox (by norm_num)).symm, c2_0]
      · obtain ⟨d1, d2, d3, d4⟩ := hd
        have hjK : j + 1 ≤ G.K := by have : m ≤ G.K := min_le_right _ _; omega
        refine Hs.mono (hs_opq (OpEx.inc (sc 1) d (by rw [d2]; omega))) le_rfl ?_
        rintro f rfl
        refine ⟨by simp [d2], by rw [DS.set_env_ne _ _ (by decide), d3], ?_, ?_⟩
        · rw [DS.set_env_ne _ _ (opd_ne_sc h.ox (by norm_num)), d1]
        · exact ck.trans (d4.trans (keep_set_sc x _ _ (by norm_num)))
    · intro c ⟨c1, c0, _, _⟩
      simp only [Cnd.eval, c1, c0, decide_eq_false_iff_not]; omega
    · rintro c ⟨_, _, cx, ck⟩
      refine ⟨?_, ck⟩
      rw [cx]
      rcases le_total (a.env y) G.K with hy | hy
      · rw [hm, min_eq_left hy]
      · rw [hm, min_eq_right hy]
        have h1 : 2 ^ G.K ≤ a.env x * 2 ^ G.K := Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hc)
        have h2 : 2 ^ G.K ≤ a.env x * 2 ^ a.env y :=
          h1.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hy))
        omega

theorem shrM_spec {x y : Fin VV} {a : DS VV MM} (h : Bin C G fl fp x y a) :
    Hs C (shrM x y) a (opc G) (fun b => b.env x = a.env x / 2 ^ a.env y ∧ Keep x a b) := by
  unfold shrM
  have hW := two_cap_lt h.g
  have e := h.env
  have hK := K_le_cap G h.g.1
  have hx := h.hx
  have hcp := cap_add G
  set m := min (a.env y) G.K with hm
  have hK3 : G.K + 1 ≤ (G.K + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
  refine hs_pre (t1 := 6) (t2 := m * (3 + 2) + 2) (passM_spec y a e h.oy) (fun b hb => ?_) |>.mono
    (by have : m ≤ G.K := min_le_right _ _; unfold opc; omega) (fun _ h => h)
  obtain ⟨b0, b1, b2⟩ := hb
  have bx : b.env x = a.env x := b2.2 x (by have := h.ox; unfold Opd at this; unfold Scr; omega)
  let I : ℕ → DS VV MM → Prop := fun j c => c.env (sc 1) = j ∧ c.env (sc 0) = m ∧
    c.env x = a.env x / 2 ^ j ∧ Keep x a c
  have hI0 : I 0 b := ⟨b1, by rw [b0], by rw [bx]; simp, b2.keep x⟩
  refine Hs.mono (Hs.loopN (c := .lt (sc 1) (sc 0)) (show sc 1 ≠ sc 0 by decide) I m 3 ?_ ?_ b hI0) le_rfl ?_
  · intro j hj c ⟨c1, c0, cx, ck⟩
    refine ⟨by simp only [Cnd.eval, c1, c0, decide_eq_true_eq]; exact hj, ?_⟩
    have hjK : j + 1 ≤ G.K := by have : m ≤ G.K := min_le_right _ _; omega
    refine hs_step (OpEx.half x c) ?_
    have n1 : sc 1 ≠ x := (opd_ne_sc (i := 1) h.ox (by norm_num)).symm
    have n0 : sc 0 ≠ x := (opd_ne_sc (i := 0) h.ox (by norm_num)).symm
    refine Hs.mono (hs_opq (OpEx.inc (sc 1) _ (by rw [DS.set_env_ne _ _ n1, c1]; omega))) le_rfl ?_
    rintro d rfl
    refine ⟨by rw [DS.set_env_self, DS.set_env_ne _ _ n1, c1],
      by rw [DS.set_env_ne _ _ (by decide), DS.set_env_ne _ _ n0, c0], ?_,
      ck.trans ((keep_set_self x _ _).trans (keep_set_sc x _ _ (by norm_num)))⟩
    rw [DS.set_env_ne _ _ n1.symm, DS.set_env_self, cx, Nat.div_div_eq_div_mul, pow_succ]
  · intro c ⟨c1, c0, _, _⟩
    simp only [Cnd.eval, c1, c0, decide_eq_false_iff_not]; omega
  · rintro c ⟨_, _, cx, ck⟩
    refine ⟨?_, ck⟩
    rw [cx]
    rcases le_total (a.env y) G.K with hy | hy
    · rw [hm, min_eq_left hy]
    · rw [hm, min_eq_right hy]
      have h1 : a.env x < 2 ^ G.K := by omega
      rw [Nat.div_eq_of_lt h1, Nat.div_eq_of_lt (lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by norm_num) hy))]


theorem out_lt {x : Fin VV} {k : ℕ} (h : x.val < 48) : Out fb k x := Or.inl h
theorem opd_out {x : Fin VV} (h : Opd x) (k : ℕ) : Out fb k x := Or.inl (by unfold Opd at h; simp only [fb]; omega)
theorem sc_out {i : ℕ} (hi : i < 7) (k : ℕ) : Out fb k (sc i) := Or.inl (by rw [sc_val hi]; simp only [fb]; omega)
theorem reg_out {i : ℕ} (hi : i < 9) (k : ℕ) : Out fb k (vr i) :=
  Or.inl (by rw [vr_val' (by simp only [VV]; omega)]; simp only [fb]; omega)

theorem xorTo_spec {x y t : Fin VV} {a : DS VV MM} {ℓ : ℕ} (h : Bin C G fl fp x y a) (ht : t.val < 9)
    (hta : a.env t = 2 ^ ℓ) (hℓ : ℓ ≤ G.K) :
    Hs C (.seq (fxorS x y (sc 3) t fb) (.op (.copy x (sc 3)))) a (opc G)
      (fun b => b.env x = (a.env x ^^^ a.env y) % 2 ^ ℓ ∧ Keep x a b) := by
  have hK3 : G.K + 1 ≤ (G.K + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
  have hxc := (fieldCells.2.2.2.2 ℓ).1
  have s3t : sc 3 ≠ t := ne_of_val (by rw [sc_val (by norm_num)]; omega)
  refine hs_pre (t2 := 1) (fieldCells.1 C x y (sc 3) t fb ℓ a (by norm_num [VV, fb]) (opd_out h.ox 5)
    (opd_out h.oy 5) (sc_out (by norm_num) 5) (Or.inl (by simp only [fb]; omega)) (opd_ne_sc h.ox (by norm_num)).symm
    (opd_ne_sc h.oy (by norm_num)).symm s3t hta (by have := h.g.2.1; omega)) (fun b hb => ?_) |>.mono
    (by unfold opc; omega) (fun _ h => h)
  obtain ⟨b1, b2, b3⟩ := hb
  refine Hs.mono (hs_opq (OpEx.copy x (sc 3) b (opd_ne_sc h.ox (by norm_num)))) le_rfl ?_
  rintro c rfl
  exact ⟨by rw [DS.set_env_self, b1], (keep_of_fr (by norm_num) b2 b3 x).trans (keep_set_self x _ _)⟩

theorem bxorM_spec {x y : Fin VV} {a : DS VV MM} (h : Bin C G fl fp x y a) :
    Hs C (bxorM x y) a (opc G) (fun b => b.env x = (a.env x ^^^ a.env y) % 2 ^ G.K ∧ Keep x a b) :=
  xorTo_spec h (by unfold cap1R; rw [vr_val' (by simp only [VV]; omega)]; omega) h.env.cap1 le_rfl

theorem faddM_spec {x y : Fin VV} {a : DS VV MM} (h : Bin C G fl fp x y a) :
    Hs C (faddM x y) a (opc G) (fun b => b.env x = (a.env x ^^^ a.env y) % 2 ^ fl ∧ Keep x a b) :=
  xorTo_spec h (by unfold tR; rw [vr_val' (by simp only [VV]; omega)]; omega) h.env.t
    (by have := (fl_bounds h.fok).2.1; omega)

/-- Reduce `x` mod `2^fl` into `sc i` (scratch `sc 0` for the quotient). -/
theorem redStep {x : Fin VV} {a : DS VV MM} {i : ℕ} (hi : 1 ≤ i) (hi7 : i < 7) (hg : GOk C G)
    (e : Env G fl fp a) (fok : fieldOk G fl fp = true) (ox : Opd x) :
    OpEx C (.dm x tR (sc 0) (sc i)) a ((a.set (sc 0) (a.env x / 2 ^ fl)).set (sc i) (a.env x % 2 ^ fl)) 1 := by
  have hW := two_cap_lt hg
  have := tf_le fok
  have h := OpEx.dm (C := C) x tR (sc 0) (sc i) a (opd_ne ox (by norm_num)) (opd_ne_sc ox (by norm_num))
    (opd_ne_sc ox hi7) (by decide) (ne_of_val (by unfold tR; rw [sc_val hi7, vr_val' (by simp only [VV]; omega)]; omega))
    (ne_of_val (by rw [sc_val (by norm_num), sc_val hi7]; omega)) (by rw [e.t]; positivity) (by rw [e.t]; omega)
  rwa [e.t] at h

theorem fmulM_spec {x y : Fin VV} {a : DS VV MM} (h : Bin C G fl fp x y a) :
    Hs C (fmulM x y) a (opc G)
      (fun b => b.env x = mulW fp fl (a.env x % 2 ^ fl) (a.env y % 2 ^ fl) ∧ Keep x a b) := by
  unfold fmulM
  obtain ⟨hf1, hf2, hmod, hf4⟩ := fl_bounds h.fok
  have hK3 : (fl + 1) ^ 2 ≤ (G.K + 1) ^ 3 := by
    calc (fl + 1) ^ 2 ≤ (G.K + 1) ^ 2 := Nat.pow_le_pow_left (by omega) _
      _ ≤ (G.K + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hmc := (fieldCells.2.2.2.2 fl).2.1
  refine hs_step (redStep (i := 4) (by norm_num) (by norm_num) h.g h.env h.fok h.ox) ?_
  set a1 := (a.set (sc 0) (a.env x / 2 ^ fl)).set (sc 4) (a.env x % 2 ^ fl)
  have k1 : KeepS a a1 := (keepS_set a (by norm_num) _).trans (keepS_set _ (by norm_num) _)
  have e1 := h.env.keep (k1.keep x) (opd_ge h.ox)
  have a1y : a1.env y = a.env y := k1.2 y (by have := h.oy; unfold Opd at this; unfold Scr; omega)
  refine hs_step (redStep (i := 5) (by norm_num) (by norm_num) h.g e1 h.fok h.oy) ?_
  set a2 := (a1.set (sc 0) (a1.env y / 2 ^ fl)).set (sc 5) (a1.env y % 2 ^ fl)
  have k2 : KeepS a1 a2 := (keepS_set a1 (by norm_num) _).trans (keepS_set _ (by norm_num) _)
  have e2 := e1.keep (k2.keep x) (opd_ge h.ox)
  have a2_4 : a2.env (sc 4) = a.env x % 2 ^ fl := by
    simp only [a2, a1, DS.set_env_ne _ _ (show sc 4 ≠ sc 5 by decide), DS.set_env_ne _ _ (show sc 4 ≠ sc 0 by decide),
      DS.set_env_self]
  have a2_5 : a2.env (sc 5) = a.env y % 2 ^ fl := by simp only [a2, DS.set_env_self, a1y]
  refine hs_pre (t2 := 1) (fieldCells.2.1 C (sc 4) (sc 5) (sc 3) tR pR fb fl fp a2 (by norm_num [VV, fb])
    (sc_out (by norm_num) 11) (sc_out (by norm_num) 11) (sc_out (by norm_num) 11) (reg_out (by norm_num) 11)
    (reg_out (by norm_num) 11) (by decide) (by decide) (by decide) (by decide) e2.t e2.p hmod
    (by have := h.g.2.1; omega) (by rw [a2_4]; exact Nat.mod_lt _ (by positivity))
    (by rw [a2_5]; exact Nat.mod_lt _ (by positivity))) (fun b hb => ?_) |>.mono
    (by omega) (fun _ h => h)
  obtain ⟨_, b2, b3, b4, b5⟩ := hb
  refine Hs.mono (hs_opq (OpEx.copy x (sc 3) b (opd_ne_sc h.ox (by norm_num)))) le_rfl ?_
  rintro c rfl
  refine ⟨?_, ((k1.trans k2).keep x).trans ((keep_of_fr (by norm_num) b4 b5 x).trans (keep_set_self x _ _))⟩
  rw [DS.set_env_self]
  apply eq_of_rep fp fl _ _ hmod b2 (redW_lt _ _ _)
  rw [b3, a2_4, a2_5]; exact (rep_mulW _ _ _ _ hmod).symm

theorem fpowM_spec {x y : Fin VV} {a : DS VV MM} (h : Bin C G fl fp x y a) :
    Hs C (fpowM x y) a (opc G) (fun b => b.env x = powW fp fl (a.env x % 2 ^ fl) (a.env y) ∧ Keep x a b) := by
  unfold fpowM
  obtain ⟨hf1, hf2, hmod, hf4⟩ := fl_bounds h.fok
  have hpc := (fieldCells.2.2.2.2 fl).2.2.2 (a.env y)
  have hsz : Nat.size (a.env y) ≤ G.K := Nat.size_le.mpr (by have := cap_add G; have := h.hy; omega)
  have hK3 : 250 * (Nat.size (a.env y) + 1) * (fl + 1) ^ 2 ≤ 250 * (G.K + 1) ^ 3 := by
    have e1 : (fl + 1) ^ 2 ≤ (G.K + 1) ^ 2 := Nat.pow_le_pow_left (by omega) _
    calc 250 * (Nat.size (a.env y) + 1) * (fl + 1) ^ 2 ≤ 250 * (G.K + 1) * (G.K + 1) ^ 2 :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) e1
      _ = 250 * (G.K + 1) ^ 3 := by ring
  refine hs_step (redStep (i := 4) (by norm_num) (by norm_num) h.g h.env h.fok h.ox) ?_
  set a1 := (a.set (sc 0) (a.env x / 2 ^ fl)).set (sc 4) (a.env x % 2 ^ fl)
  have k1 : KeepS a a1 := (keepS_set a (by norm_num) _).trans (keepS_set _ (by norm_num) _)
  have e1 := h.env.keep (k1.keep x) (opd_ge h.ox)
  have a1y : a1.env y = a.env y := k1.2 y (by have := h.oy; unfold Opd at this; unfold Scr; omega)
  have a1_4 : a1.env (sc 4) = a.env x % 2 ^ fl := by simp only [a1, DS.set_env_self]
  refine hs_pre (t2 := 1) (fieldCells.2.2.1 C (sc 4) y (sc 3) tR pR fb fl fp a1 (by norm_num [VV, fb])
    (sc_out (by norm_num) 16) (opd_out h.oy 16) (sc_out (by norm_num) 16) (reg_out (by norm_num) 16)
    (reg_out (by norm_num) 16) (by decide) (opd_ne_sc h.oy (by norm_num)).symm (by decide) (by decide) e1.t e1.p hmod
    hf1 (by have := h.g.2.1; omega) (by rw [a1_4]; exact Nat.mod_lt _ (by positivity))) (fun b hb => ?_) |>.mono
    (by simp only [a1y] at *; omega) (fun _ h => h)
  obtain ⟨b1, b2, b3, b4⟩ := hb
  refine Hs.mono (hs_opq (OpEx.copy x (sc 3) b (opd_ne_sc h.ox (by norm_num)))) le_rfl ?_
  rintro c rfl
  refine ⟨?_, (k1.keep x).trans ((keep_of_fr (by norm_num) b3 b4 x).trans (keep_set_self x _ _))⟩
  rw [DS.set_env_self]
  apply eq_of_rep fp fl _ _ hmod b1 (redW_lt _ _ _)
  rw [b2, a1_4, a1y]; exact (rep_powW _ _ _ _ hmod).symm

theorem finvM_spec {x : Fin VV} {a : DS VV MM} (hg : GOk C G) (e : Env G fl fp a) (fok : fieldOk G fl fp = true)
    (ox : Opd x) :
    Hs C (finvM x) a (opc G) (fun b => b.env x = powW fp fl (a.env x % 2 ^ fl) (2 ^ fl - 2) ∧ Keep x a b) := by
  unfold finvM
  obtain ⟨hf1, hf2, hmod, hf4⟩ := fl_bounds fok
  have hic := (fieldCells.2.2.2.2 fl).2.2.1
  have hK3 : (fl + 1) ^ 3 ≤ (G.K + 1) ^ 3 := Nat.pow_le_pow_left (by omega) _
  refine hs_step (redStep (i := 4) (by norm_num) (by norm_num) hg e fok ox) ?_
  set a1 := (a.set (sc 0) (a.env x / 2 ^ fl)).set (sc 4) (a.env x % 2 ^ fl)
  have k1 : KeepS a a1 := (keepS_set a (by norm_num) _).trans (keepS_set _ (by norm_num) _)
  have e1 := e.keep (k1.keep x) (opd_ge ox)
  have a1_4 : a1.env (sc 4) = a.env x % 2 ^ fl := by simp only [a1, DS.set_env_self]
  refine hs_pre (t2 := 1) (fieldCells.2.2.2.1 C (sc 4) (sc 3) tR pR fb fl fp a1 (by norm_num [VV, fb])
    (sc_out (by norm_num) 18) (sc_out (by norm_num) 18) (reg_out (by norm_num) 18)
    (reg_out (by norm_num) 18) (by decide) (by decide) (by decide) e1.t e1.p hmod
    hf1 (by have := hg.2.1; omega) (by rw [a1_4]; exact Nat.mod_lt _ (by positivity))) (fun b hb => ?_) |>.mono
    (by omega) (fun _ h => h)
  obtain ⟨b1, b2, _, b3, b4⟩ := hb
  refine Hs.mono (hs_opq (OpEx.copy x (sc 3) b (opd_ne_sc ox (by norm_num)))) le_rfl ?_
  rintro c rfl
  refine ⟨?_, (k1.keep x).trans ((keep_of_fr (by norm_num) b3 b4 x).trans (keep_set_self x _ _))⟩
  rw [DS.set_env_self]
  apply eq_of_rep fp fl _ _ hmod b1 (redW_lt _ _ _)
  rw [b2, a1_4]; exact (rep_powW _ _ _ _ hmod).symm

theorem incK_spec (hg : GOk C G) : ∀ (n : ℕ) (x : Fin VV) (a : DS VV MM), Env G fl fp a → Opd x →
    a.env x ≤ G.cap → Hs C (incK n x) a (3 * n + 1) (fun b => b.env x = min (a.env x + n) G.cap ∧ Keep x a b)
  | 0, x, a, e, ox, hx => Hs.mono (nop_keep x a (opd_ne_junk ox)) le_rfl (by
      rintro b ⟨b1, b2⟩; exact ⟨by rw [b1]; omega, b2⟩)
  | n + 1, x, a, e, ox, hx => by
    have hW := two_cap_lt hg
    refine hs_pre (t1 := 3 * n + 1) (t2 := 2) (incK_spec hg n x a e ox hx) (fun b hb => ?_) |>.mono
      (by omega) (fun _ h => h)
    obtain ⟨b1, b2⟩ := hb
    have eb := e.keep b2 (opd_ge ox)
    refine Hs.ite (c := .lt x capR) (ne_capR ox) (fun hc => ?_) (fun hc => ?_)
    · simp only [Cnd.eval, eb.cap, decide_eq_true_eq] at hc
      refine Hs.mono (hs_opq (OpEx.inc x b (by omega))) le_rfl ?_
      rintro c rfl
      exact ⟨by rw [DS.set_env_self, b1] at *; omega, b2.trans (keep_set_self x _ _)⟩
    · simp only [Cnd.eval, eb.cap, decide_eq_false_iff_not, not_lt] at hc
      refine Hs.mono (nop_keep x b (opd_ne_junk ox)) le_rfl ?_
      rintro c ⟨c1, c2⟩
      exact ⟨by rw [c1, b1] at *; omega, b2.trans c2⟩

end Specs

end NearCubicGates.Adapters.ShortPCP.Machines.FL
