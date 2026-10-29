import Proof.Gates.Cells.Lang
import Mathlib

/-!
# Cell-language programs with framed postconditions (toolkit for the X9 encoder)

The encoder of X9 (`app:sources`, "Full-range amplification interface") is written in the released cell language
(`Proof/Gates/Cells/Lang.lean`: variables holding numbers, `add`/`sub`/`mul`/`dm`/`half`/`shl`, sequential input
reading, output emission) and compiled by the released `Cells.wordFunction_of_lang` (`Cells/Run.lean:569`).
This module gives the reasoning layer: `Fr S w a b` (only the variables in `S` change, the output grows by `w`),
`Runs` (a run with a framed postcondition), sequencing, conditionals, a counted loop rule `Runs.loopN`, and the
single operations. Programs use a fixed bank of `NV` variables (`Fin NV` numerals), so distinctness side
conditions are decided by `decide`.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Amplification.Enc

open NearCubicGates.Close.Cells

/-- The size of the variable bank. -/
abbrev NV : ℕ := 96

abbrev Var := Fin NV
abbrev Ds := DS NV 0
abbrev Sc := St NV 0

theorem env_set (a : Ds) (x y : Var) (v : ℕ) : (a.set x v).env y = if y = x then v else a.env y := by
  unfold DS.set; simp only [Function.update_apply]

/-- Normalize the variable reads of an explicit state. -/
macro "norm_env" : tactic =>
  `(tactic| try simp (config := { decide := true }) only [env_set, ite_true, ite_false, Fin.isValue])

/-- **Frame**: only the variables in `S` change; the output grows by `w`; the input position and everything else
are unchanged. -/
structure Fr (S : List Var) (w : List Bool) (a b : Ds) : Prop where
  env : ∀ x, x ∉ S → b.env x = a.env x
  ip : b.ip = a.ip
  out : b.out = a.out ++ w
  ram : b.ram = a.ram
  rc : b.rc = a.rc
  kin : b.kin = a.kin
  kout : b.kout = a.kout
  kc : b.kc = a.kc

theorem Fr.refl (S : List Var) (a : Ds) : Fr S [] a a := ⟨fun _ _ => rfl, rfl, by simp, rfl, rfl, rfl, rfl, rfl⟩

theorem Fr.trans {S : List Var} {w1 w2 : List Bool} {a b c : Ds} (h1 : Fr S w1 a b) (h2 : Fr S w2 b c) :
    Fr S (w1 ++ w2) a c :=
  ⟨fun x hx => (h2.env x hx).trans (h1.env x hx), h2.ip.trans h1.ip, by rw [h2.out, h1.out, List.append_assoc],
    h2.ram.trans h1.ram, h2.rc.trans h1.rc, h2.kin.trans h1.kin, h2.kout.trans h1.kout, h2.kc.trans h1.kc⟩

theorem Fr.trans0 {S : List Var} {a b c : Ds} (h1 : Fr S [] a b) (h2 : Fr S [] b c) : Fr S [] a c := by
  simpa using h1.trans h2

theorem Fr.mono {S S' : List Var} {w : List Bool} {a b : Ds} (h : Fr S w a b) (hS : S ⊆ S') : Fr S' w a b :=
  ⟨fun x hx => h.env x (fun h' => hx (hS h')), h.ip, h.out, h.ram, h.rc, h.kin, h.kout, h.kc⟩

theorem Fr.set (S : List Var) (a : Ds) (x : Var) (v : ℕ) (hx : x ∈ S) : Fr S [] a (a.set x v) :=
  ⟨fun y hy => DS.set_env_ne _ _ (fun e => hy (e ▸ hx)), rfl, by simp, rfl, rfl, rfl, rfl, rfl⟩

theorem Fr.emit (S : List Var) (a : Ds) (bit : Bool) : Fr S [bit] a { a with out := a.out ++ [bit] } :=
  ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Fr.set_right {S : List Var} {w : List Bool} {a b : Ds} (h : Fr S w a b) (x : Var) (v : ℕ) (hx : x ∈ S) :
    Fr S w a (b.set x v) :=
  ⟨fun y hy => (DS.set_env_ne _ _ (fun e : y = x => hy (e ▸ hx))).trans (h.env y hy), h.ip, h.out, h.ram, h.rc,
    h.kin, h.kout, h.kc⟩

/-- **A run with a framed postcondition.** -/
def Runs (C : Ctx) (P : Sc) (a : Ds) (n : ℕ) (S : List Var) (w : List Bool) (Q : Ds → Prop) : Prop :=
  ∃ b, Ex C P a b n ∧ Fr S w a b ∧ Q b

theorem Runs.mono {C : Ctx} {P : Sc} {a : Ds} {n n' : ℕ} {S S' : List Var} {w : List Bool} {Q Q' : Ds → Prop}
    (h : Runs C P a n S w Q) (hn : n ≤ n') (hS : S ⊆ S') (hQ : ∀ b, Fr S w a b → Q b → Q' b) :
    Runs C P a n' S' w Q' := by
  obtain ⟨b, h1, h2, h3⟩ := h
  exact ⟨b, h1.mono hn, h2.mono hS, hQ b h2 h3⟩

theorem Runs.seq {C : Ctx} {P P' : Sc} {a : Ds} {n n' : ℕ} {S : List Var} {w w' : List Bool}
    {Q Q' : Ds → Prop} (h : Runs C P a n S w Q) (h' : ∀ b, Fr S w a b → Q b → Runs C P' b n' S w' Q') :
    Runs C (.seq P P') a (n + n' + 1) S (w ++ w') Q' := by
  obtain ⟨b, h1, h2, h3⟩ := h
  obtain ⟨c, h4, h5, h6⟩ := h' b h2 h3
  exact ⟨c, Ex.seq h1 h4, h2.trans h5, h6⟩

theorem Runs.iteT {C : Ctx} {c : Cnd NV} {P P' : Sc} {a : Ds} {n : ℕ} {S : List Var} {w : List Bool}
    {Q : Ds → Prop} (hwf : c.wf) (hc : c.eval a = true) (h : Runs C P a n S w Q) :
    Runs C (.ite c P P') a (n + 1) S w Q := by
  obtain ⟨b, h1, h2, h3⟩ := h
  exact ⟨b, Ex.iteT hwf hc h1, h2, h3⟩

theorem Runs.iteF {C : Ctx} {c : Cnd NV} {P P' : Sc} {a : Ds} {n : ℕ} {S : List Var} {w : List Bool}
    {Q : Ds → Prop} (hwf : c.wf) (hc : c.eval a = false) (h : Runs C P' a n S w Q) :
    Runs C (.ite c P P') a (n + 1) S w Q := by
  obtain ⟨b, h1, h2, h3⟩ := h
  exact ⟨b, Ex.iteF hwf hc h1, h2, h3⟩

theorem Runs.step {C : Ctx} {P P' : Sc} {a f : Ds} {n n' : ℕ} {S : List Var} {w w' : List Bool}
    {Q : Ds → Prop} (h : Runs C P a n S w (· = f)) (h' : Runs C P' f n' S w' Q) :
    Runs C (.seq P P') a (n + n' + 1) S (w ++ w') Q :=
  Runs.seq h (fun _ _ hb => hb ▸ h')

/-- A silent exact step followed by a run. -/
theorem Runs.step0 {C : Ctx} {P P' : Sc} {a f : Ds} {n n' : ℕ} {S : List Var} {w : List Bool}
    {Q : Ds → Prop} (h : Runs C P a n S [] (· = f)) (h' : Runs C P' f n' S w Q) :
    Runs C (.seq P P') a (n + n' + 1) S w Q := by
  have := Runs.step h h'
  simpa using this

/-- A silent framed run followed by a run. -/
theorem Runs.seq0 {C : Ctx} {P P' : Sc} {a : Ds} {n n' : ℕ} {S : List Var} {w : List Bool}
    {Q Q' : Ds → Prop} (h : Runs C P a n S [] Q) (h' : ∀ b, Fr S [] a b → Q b → Runs C P' b n' S w Q') :
    Runs C (.seq P P') a (n + n' + 1) S w Q' := by
  have := Runs.seq h h'
  simpa using this

theorem Runs.costLe {C : Ctx} {P : Sc} {a : Ds} {n n' : ℕ} {S : List Var} {w : List Bool} {Q : Ds → Prop}
    (h : Runs C P a n S w Q) (hn : n ≤ n') : Runs C P a n' S w Q :=
  h.mono hn (List.Subset.refl _) (fun _ _ h => h)

/-! ### Budget-driven chaining: the remaining budget is read off the goal -/

theorem Runs.op1 {C : Ctx} {P P' : Sc} {a f : Ds} {m : ℕ} {S : List Var} {w : List Bool}
    {Q : Ds → Prop} (h : Runs C P a 1 S [] (· = f)) (h' : Runs C P' f (m - 2) S w Q) (hm : 2 ≤ m) :
    Runs C (.seq P P') a m S w Q :=
  (Runs.step0 h h').costLe (by omega)

theorem Runs.emit1 {C : Ctx} {P P' : Sc} {a f : Ds} {m : ℕ} {S : List Var} {bit : Bool} {w : List Bool}
    {Q : Ds → Prop} (h : Runs C P a 1 S [bit] (· = f)) (h' : Runs C P' f (m - 2) S w Q) (hm : 2 ≤ m) :
    Runs C (.seq P P') a m S (bit :: w) Q :=
  (Runs.step h h').costLe (by omega)

theorem Runs.call {C : Ctx} {P P' : Sc} {a : Ds} {n m : ℕ} {S : List Var} {w : List Bool}
    {Q1 Q : Ds → Prop} (h : Runs C P a n S [] Q1) (h' : ∀ b, Fr S [] a b → Q1 b → Runs C P' b (m - n - 1) S w Q)
    (hm : n + 1 ≤ m) : Runs C (.seq P P') a m S w Q :=
  (Runs.seq0 h h').costLe (by omega)

theorem Runs.last {C : Ctx} {P : Sc} {a f : Ds} {n m : ℕ} {S : List Var} {w : List Bool} {Q : Ds → Prop}
    (h : Runs C P a n S w (· = f)) (hQ : Fr S w a f → Q f) (hm : n ≤ m) : Runs C P a m S w Q := by
  obtain ⟨b, h1, h2, rfl⟩ := h
  exact ⟨b, h1.mono hm, h2, hQ h2⟩

theorem Runs.iteT' {C : Ctx} {c : Cnd NV} {P P' : Sc} {a : Ds} {m : ℕ} {S : List Var} {w : List Bool}
    {Q : Ds → Prop} (hwf : c.wf) (hc : c.eval a = true) (h : Runs C P a (m - 1) S w Q) (hm : 1 ≤ m) :
    Runs C (.ite c P P') a m S w Q :=
  (Runs.iteT hwf hc h).costLe (by omega)

theorem Runs.iteF' {C : Ctx} {c : Cnd NV} {P P' : Sc} {a : Ds} {m : ℕ} {S : List Var} {w : List Bool}
    {Q : Ds → Prop} (hwf : c.wf) (hc : c.eval a = false) (h : Runs C P' a (m - 1) S w Q) (hm : 1 ≤ m) :
    Runs C (.ite c P P') a m S w Q :=
  (Runs.iteF hwf hc h).costLe (by omega)

/-- A routine run in a smaller frame, followed by a run. -/
theorem Runs.callS {C : Ctx} {P P' : Sc} {a : Ds} {n m : ℕ} {S0 S : List Var} {w : List Bool}
    {Q1 Q : Ds → Prop} (h : Runs C P a n S0 [] Q1) (hS : S0 ⊆ S)
    (h' : ∀ b, Fr S0 [] a b → Q1 b → Runs C P' b (m - n - 1) S w Q) (hm : n + 1 ≤ m) : Runs C (.seq P P') a m S w Q :=
  Runs.call (Q1 := fun b => Fr S0 [] a b ∧ Q1 b) (h.mono le_rfl hS (fun _ hb hq => ⟨hb, hq⟩))
    (fun b _ hq => h' b hq.1 hq.2) hm

/-- A routine run in a smaller frame, last. -/
theorem Runs.lastS {C : Ctx} {P : Sc} {a : Ds} {n m : ℕ} {S0 S : List Var} {w : List Bool} {Q1 Q : Ds → Prop}
    (h : Runs C P a n S0 w Q1) (hS : S0 ⊆ S) (hQ : ∀ b, Fr S0 w a b → Q1 b → Q b) (hm : n ≤ m) :
    Runs C P a m S w Q :=
  h.mono hm hS hQ

theorem Runs.post {C : Ctx} {P : Sc} {a f : Ds} {n : ℕ} {S : List Var} {w : List Bool} {Q : Ds → Prop}
    (h : Runs C P a n S w (· = f)) (hQ : Fr S w a f → Q f) : Runs C P a n S w Q := by
  obtain ⟨b, h1, h2, rfl⟩ := h
  exact ⟨b, h1, h2, hQ h2⟩

/-- **The counted loop rule.** `Inv j` holds before the `j`-th round; the test holds before rounds `j < N` and
fails after `N` rounds; round `j` writes `ow j`. -/
theorem Runs.loopN {C : Ctx} {c : Cnd NV} {body : Sc} {S : List Var} (hwf : c.wf) (N cost : ℕ)
    (ow : ℕ → List Bool) (Inv : ℕ → Ds → Prop)
    (hstep : ∀ j < N, ∀ b, Inv j b → c.eval b = true ∧ Runs C body b cost S (ow j) (Inv (j + 1)))
    (hstop : ∀ b, Inv N b → c.eval b = false) (a : Ds) (ha : Inv 0 a) :
    Runs C (.loop c body) a (N * (cost + 2) + 2) S ((List.range N).flatMap ow) (Inv N) := by
  have key : ∀ d j, j + d = N → ∀ b, Inv j b →
      Runs C (.loop c body) b (d * (cost + 2) + 2) S ((List.range' j d).flatMap ow) (Inv N) := by
    intro d
    induction d with
    | zero =>
      intro j hj b hb
      rw [Nat.add_zero] at hj; subst hj
      exact ⟨b, (Ex.loopF hwf (hstop b hb)).mono (by omega), by simpa using Fr.refl S b, hb⟩
    | succ d ih =>
      intro j hj b hb
      obtain ⟨hc, b1, h1, h2, h3⟩ := hstep j (by omega) b hb
      obtain ⟨b2, h4, h5, h6⟩ := ih (j + 1) (by omega) b1 h3
      refine ⟨b2, (Ex.loopT hwf hc h1 h4).mono (by nlinarith), ?_, h6⟩
      have e : (List.range' j (d + 1)).flatMap ow = ow j ++ (List.range' (j + 1) d).flatMap ow := by
        rw [List.range'_succ, List.flatMap_cons]
      rw [e]; exact h2.trans h5
  have h := key N 0 (by omega) a ha
  rwa [List.range_eq_range'] 

/-- The counted loop rule for silent bodies. -/
theorem Runs.loopN0 {C : Ctx} {c : Cnd NV} {body : Sc} {S : List Var} (hwf : c.wf) (N cost : ℕ)
    (Inv : ℕ → Ds → Prop)
    (hstep : ∀ j < N, ∀ b, Inv j b → c.eval b = true ∧ Runs C body b cost S [] (Inv (j + 1)))
    (hstop : ∀ b, Inv N b → c.eval b = false) (a : Ds) (ha : Inv 0 a) :
    Runs C (.loop c body) a (N * (cost + 2) + 2) S [] (Inv N) := by
  have h := Runs.loopN hwf N cost (fun _ => []) Inv hstep hstop a ha
  have e : (List.range N).flatMap (fun _ => ([] : List Bool)) = [] := List.flatMap_eq_nil_iff.mpr (fun _ _ => rfl)
  rwa [e] at h

/-! ## Runs that move the input position -/

/-- **Frame without the input position**: as `Fr`, but `ip` may change. -/
structure FrI (S : List Var) (w : List Bool) (a b : Ds) : Prop where
  env : ∀ x, x ∉ S → b.env x = a.env x
  out : b.out = a.out ++ w
  ram : b.ram = a.ram
  rc : b.rc = a.rc
  kin : b.kin = a.kin
  kout : b.kout = a.kout
  kc : b.kc = a.kc

theorem Fr.toI {S : List Var} {w : List Bool} {a b : Ds} (h : Fr S w a b) : FrI S w a b :=
  ⟨h.env, h.out, h.ram, h.rc, h.kin, h.kout, h.kc⟩

theorem FrI.trans {S : List Var} {w1 w2 : List Bool} {a b c : Ds} (h1 : FrI S w1 a b) (h2 : FrI S w2 b c) :
    FrI S (w1 ++ w2) a c :=
  ⟨fun x hx => (h2.env x hx).trans (h1.env x hx), by rw [h2.out, h1.out, List.append_assoc],
    h2.ram.trans h1.ram, h2.rc.trans h1.rc, h2.kin.trans h1.kin, h2.kout.trans h1.kout, h2.kc.trans h1.kc⟩

theorem FrI.trans0 {S : List Var} {a b c : Ds} (h1 : FrI S [] a b) (h2 : FrI S [] b c) : FrI S [] a c := by
  simpa using h1.trans h2

theorem FrI.toFr {S : List Var} {w : List Bool} {a b : Ds} (h : FrI S w a b) (hip : b.ip = a.ip) : Fr S w a b :=
  ⟨h.env, hip, h.out, h.ram, h.rc, h.kin, h.kout, h.kc⟩

theorem FrI.mono {S S' : List Var} {w : List Bool} {a b : Ds} (h : FrI S w a b) (hS : S ⊆ S') : FrI S' w a b :=
  ⟨fun x hx => h.env x (fun h' => hx (hS h')), h.out, h.ram, h.rc, h.kin, h.kout, h.kc⟩

theorem FrI.rd (S : List Var) (b : Ds) (x : Var) (hx : x ∈ S) (v ip' : ℕ) :
    FrI S [] b { b.set x v with ip := ip' } :=
  ⟨fun y hy => DS.set_env_ne _ _ (fun e : y = x => hy (e ▸ hx)), by simp, rfl, rfl, rfl, rfl, rfl⟩

theorem FrI.set_right {S : List Var} {w : List Bool} {a b : Ds} (h : FrI S w a b) (x : Var) (v : ℕ) (hx : x ∈ S) :
    FrI S w a (b.set x v) :=
  ⟨fun y hy => (DS.set_env_ne _ _ (fun e : y = x => hy (e ▸ hx))).trans (h.env y hy), h.out, h.ram, h.rc, h.kin,
    h.kout, h.kc⟩

theorem FrI.ip_right {S : List Var} {w : List Bool} {a b : Ds} (h : FrI S w a b) (ip' : ℕ) :
    FrI S w a { b with ip := ip' } := ⟨h.env, h.out, h.ram, h.rc, h.kin, h.kout, h.kc⟩

/-- The counted loop rule at the level of `Ex`, with an arbitrary invariant. -/
theorem ex_loopN {C : Ctx} {c : Cnd NV} {body : Sc} (hwf : c.wf) (N cost : ℕ) (Inv : ℕ → Ds → Prop)
    (hstep : ∀ j < N, ∀ b, Inv j b → c.eval b = true ∧ ∃ b', Ex C body b b' cost ∧ Inv (j + 1) b')
    (hstop : ∀ b, Inv N b → c.eval b = false) (a : Ds) (ha : Inv 0 a) :
    ∃ b, Ex C (.loop c body) a b (N * (cost + 2) + 2) ∧ Inv N b := by
  have key : ∀ d j, j + d = N → ∀ b, Inv j b → ∃ b', Ex C (.loop c body) b b' (d * (cost + 2) + 2) ∧ Inv N b' := by
    intro d
    induction d with
    | zero =>
      intro j hj b hb
      rw [Nat.add_zero] at hj; subst hj
      exact ⟨b, (Ex.loopF hwf (hstop b hb)).mono (by omega), hb⟩
    | succ d ih =>
      intro j hj b hb
      obtain ⟨hc, b1, h1, h3⟩ := hstep j (by omega) b hb
      obtain ⟨b2, h4, h6⟩ := ih (j + 1) (by omega) b1 h3
      exact ⟨b2, (Ex.loopT hwf hc h1 h4).mono (by nlinarith), h6⟩
  exact key N 0 (by omega) a ha

/-! ## Single operations -/

section Ops

variable (C : Ctx) (S : List Var) (a : Ds)

theorem run_zero (x : Var) (hx : x ∈ S) : Runs C (.op (.zero x)) a 1 S [] (fun b => b = a.set x 0) :=
  ⟨_, Ex.op (OpEx.zero x a), Fr.set S a x 0 hx, rfl⟩

theorem run_inc (x : Var) (hx : x ∈ S) (hv : a.env x + 1 < 2 ^ C.Wd) :
    Runs C (.op (.inc x)) a 1 S [] (fun b => b = a.set x (a.env x + 1)) :=
  ⟨_, Ex.op (OpEx.inc x a hv), Fr.set S a x _ hx, rfl⟩

theorem run_add (x y : Var) (hx : x ∈ S) (hxy : x ≠ y) (hv : a.env x + a.env y < 2 ^ C.Wd) :
    Runs C (.op (.add x y)) a 1 S [] (fun b => b = a.set x (a.env x + a.env y)) :=
  ⟨_, Ex.op (OpEx.add x y a hxy hv), Fr.set S a x _ hx, rfl⟩

theorem run_sub (x y : Var) (hx : x ∈ S) (hxy : x ≠ y) (hv : a.env y ≤ a.env x) :
    Runs C (.op (.sub x y)) a 1 S [] (fun b => b = a.set x (a.env x - a.env y)) :=
  ⟨_, Ex.op (OpEx.sub x y a hxy hv), Fr.set S a x _ hx, rfl⟩

theorem run_copy (x y : Var) (hx : x ∈ S) (hxy : x ≠ y) :
    Runs C (.op (.copy x y)) a 1 S [] (fun b => b = a.set x (a.env y)) :=
  ⟨_, Ex.op (OpEx.copy x y a hxy), Fr.set S a x _ hx, rfl⟩

theorem run_half (x : Var) (hx : x ∈ S) : Runs C (.op (.half x)) a 1 S [] (fun b => b = a.set x (a.env x / 2)) :=
  ⟨_, Ex.op (OpEx.half x a), Fr.set S a x _ hx, rfl⟩

theorem run_shl (x : Var) (hx : x ∈ S) (hv : 2 * a.env x < 2 ^ C.Wd) :
    Runs C (.op (.shl x)) a 1 S [] (fun b => b = a.set x (2 * a.env x)) :=
  ⟨_, Ex.op (OpEx.shl x a hv), Fr.set S a x _ hx, rfl⟩

theorem run_mul (x y z : Var) (hz : z ∈ S) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hv : a.env x * a.env y < 2 ^ C.Wd) :
    Runs C (.op (.mul x y z)) a 1 S [] (fun b => b = a.set z (a.env x * a.env y)) :=
  ⟨_, Ex.op (OpEx.mul x y z a hxy hxz hyz hv), Fr.set S a z _ hz, rfl⟩

theorem run_dm (x y q r : Var) (hq : q ∈ S) (hr : r ∈ S) (hd : [x, y, q, r].Nodup) (hy : 0 < a.env y)
    (hv : 2 * a.env y ≤ 2 ^ C.Wd) :
    Runs C (.op (.dm x y q r)) a 1 S [] (fun b => b = (a.set q (a.env x / a.env y)).set r (a.env x % a.env y)) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true] at hd
  obtain ⟨⟨hxy, hxq, hxr⟩, ⟨hyq, hyr⟩, hqr, -⟩ := hd
  exact ⟨_, Ex.op (OpEx.dm x y q r a hxy hxq hxr hyq hyr hqr hy hv), (Fr.set S a q _ hq).trans (Fr.set S _ r _ hr),
    rfl⟩

theorem run_emit (bit : Bool) : Runs C (.op (.emit bit)) a 1 S [bit] (fun b => b = { a with out := a.out ++ [bit] }) :=
  ⟨_, Ex.op (OpEx.emit bit a), Fr.emit S a bit, rfl⟩

end Ops

end NearCubicGates.Adapters.Amplification.Enc
