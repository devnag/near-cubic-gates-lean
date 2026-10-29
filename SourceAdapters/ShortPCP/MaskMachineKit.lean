import Proof.Gates.Cells.Kit

/-!
# The mask machine: a framed-run toolkit for the released cell language

 (proof of `thm:short-pcp-ours`, Step 3): "Choosing `m` uses only integer comparisons; constructing
the field and listing the multiset also take `poly(n, log T)` time." The mask machine is written in the released
cell language (L `Proof/Gates/Cells/Lang.lean`: variables holding numbers, record stores, sequential input,
output emission) and packaged by `Cells.wordFunction_of_lang` (L `Cells/Run.lean:569`).

This module is the reasoning layer used by the `MaskMachine*` modules: `Fx S w a b` (only the variables in `S`
change, the output grows by `w`, everything else is unchanged), `Runs` (a run with a framed postcondition), the
single operations, sequencing with the remaining budget read off the goal, conditionals, a counted loop rule
`Runs.loopN` (output of pass `j` is `ow j`) and a measured while rule `Runs.loopW`.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.ShortPCP.MaskMachine

open NearCubicGates.Close.Cells

abbrev Ds := DS VV MM
abbrev Sc := St VV MM
abbrev Var := Fin VV

theorem env_set (a : Ds) (x y : Var) (v : ℕ) : (a.set x v).env y = if y = x then v else a.env y := by
  unfold DS.set; simp only [Function.update_apply]

/-- **Frame**: only the variables in `S` (and the record stores) change; the output grows by `w`; the input
position and the call registers do not change. (The stores are tracked by the invariants of the one routine that
uses them, the table of `rand_{RS,=}`.) -/
structure Fx (S : List Var) (w : List Bool) (a b : Ds) : Prop where
  env : ∀ x, x ∉ S → b.env x = a.env x
  ip : b.ip = a.ip
  out : b.out = a.out ++ w
  kin : b.kin = a.kin
  kout : b.kout = a.kout
  kc : b.kc = a.kc

theorem Fx.refl (S : List Var) (a : Ds) : Fx S [] a a := ⟨fun _ _ => rfl, rfl, by simp, rfl, rfl, rfl⟩

theorem Fx.trans {S : List Var} {w1 w2 : List Bool} {a b c : Ds} (h1 : Fx S w1 a b) (h2 : Fx S w2 b c) :
    Fx S (w1 ++ w2) a c :=
  ⟨fun x hx => (h2.env x hx).trans (h1.env x hx), h2.ip.trans h1.ip, by rw [h2.out, h1.out, List.append_assoc],
    h2.kin.trans h1.kin, h2.kout.trans h1.kout, h2.kc.trans h1.kc⟩

theorem Fx.mono {S S' : List Var} {w : List Bool} {a b : Ds} (h : Fx S w a b) (hS : S ⊆ S') : Fx S' w a b :=
  ⟨fun x hx => h.env x (fun h' => hx (hS h')), h.ip, h.out, h.kin, h.kout, h.kc⟩

theorem Fx.set (S : List Var) (a : Ds) (x : Var) (v : ℕ) (hx : x ∈ S) : Fx S [] a (a.set x v) :=
  ⟨fun y hy => DS.set_env_ne _ _ (fun e => hy (e ▸ hx)), rfl, by simp, rfl, rfl, rfl⟩

theorem Fx.emit (S : List Var) (a : Ds) (bit : Bool) : Fx S [bit] a { a with out := a.out ++ [bit] } :=
  ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Fx.store (S : List Var) (a : Ds) (ram : Fin MM → List ℕ) (rc : Fin MM → ℕ) :
    Fx S [] a { a with ram := ram, rc := rc } := ⟨fun _ _ => rfl, rfl, by simp, rfl, rfl, rfl⟩

/-- **A run with a framed postcondition.** -/
def Runs (C : Ctx) (P : Sc) (a : Ds) (n : ℕ) (S : List Var) (w : List Bool) (Q : Ds → Prop) : Prop :=
  ∃ b, Ex C P a b n ∧ Fx S w a b ∧ Q b

section Rules

variable {C : Ctx}

theorem Runs.mono {P : Sc} {a : Ds} {n n' : ℕ} {S S' : List Var} {w : List Bool} {Q Q' : Ds → Prop}
    (h : Runs C P a n S w Q) (hn : n ≤ n') (hS : S ⊆ S') (hQ : ∀ b, Fx S w a b → Q b → Q' b) :
    Runs C P a n' S' w Q' := by
  obtain ⟨b, h1, h2, h3⟩ := h
  exact ⟨b, h1.mono hn, h2.mono hS, hQ b h2 h3⟩

theorem Runs.costLe {P : Sc} {a : Ds} {n n' : ℕ} {S : List Var} {w : List Bool} {Q : Ds → Prop}
    (h : Runs C P a n S w Q) (hn : n ≤ n') : Runs C P a n' S w Q :=
  h.mono hn (List.Subset.refl _) (fun _ _ h => h)

theorem Runs.wout {P : Sc} {a : Ds} {n : ℕ} {S : List Var} {w w' : List Bool} {Q : Ds → Prop}
    (h : Runs C P a n S w Q) (hw : w = w') : Runs C P a n S w' Q := hw ▸ h

theorem Runs.seq {P P' : Sc} {a : Ds} {n n' : ℕ} {S : List Var} {w w' : List Bool}
    {Q Q' : Ds → Prop} (h : Runs C P a n S w Q) (h' : ∀ b, Fx S w a b → Q b → Runs C P' b n' S w' Q') :
    Runs C (.seq P P') a (n + n' + 1) S (w ++ w') Q' := by
  obtain ⟨b, h1, h2, h3⟩ := h
  obtain ⟨c, h4, h5, h6⟩ := h' b h2 h3
  exact ⟨c, Ex.seq h1 h4, h2.trans h5, h6⟩

/-- Sequencing with the remaining budget read off the goal. -/
theorem Runs.call {P P' : Sc} {a : Ds} {n m : ℕ} {S : List Var} {w w' : List Bool}
    {Q1 Q : Ds → Prop} (h : Runs C P a n S w Q1) (h' : ∀ b, Fx S w a b → Q1 b → Runs C P' b (m - n - 1) S w' Q)
    (hm : n + 1 ≤ m) : Runs C (.seq P P') a m S (w ++ w') Q :=
  (Runs.seq h h').costLe (by omega)

/-- A silent run followed by a run. -/
theorem Runs.call0 {P P' : Sc} {a : Ds} {n m : ℕ} {S : List Var} {w : List Bool}
    {Q1 Q : Ds → Prop} (h : Runs C P a n S [] Q1) (h' : ∀ b, Fx S [] a b → Q1 b → Runs C P' b (m - n - 1) S w Q)
    (hm : n + 1 ≤ m) : Runs C (.seq P P') a m S w Q := by
  have := Runs.call h h' hm
  simpa using this

/-- One silent exact step followed by a run. -/
theorem Runs.op1 {P P' : Sc} {a f : Ds} {m : ℕ} {S : List Var} {w : List Bool}
    {Q : Ds → Prop} (h : Runs C P a 1 S [] (· = f)) (h' : Runs C P' f (m - 2) S w Q) (hm : 2 ≤ m) :
    Runs C (.seq P P') a m S w Q :=
  Runs.call0 h (fun _ _ hb => hb ▸ h') hm

/-- One emitting exact step followed by a run. -/
theorem Runs.emit1 {P P' : Sc} {a f : Ds} {m : ℕ} {S : List Var} {bit : Bool} {w : List Bool}
    {Q : Ds → Prop} (h : Runs C P a 1 S [bit] (· = f)) (h' : Runs C P' f (m - 2) S w Q) (hm : 2 ≤ m) :
    Runs C (.seq P P') a m S (bit :: w) Q :=
  Runs.call h (fun _ _ hb => hb ▸ h') hm

/-- A routine run in a smaller frame, followed by a run. -/
theorem Runs.callS {P P' : Sc} {a : Ds} {n m : ℕ} {S0 S : List Var} {w w' : List Bool}
    {Q1 Q : Ds → Prop} (h : Runs C P a n S0 w Q1) (hS : S0 ⊆ S)
    (h' : ∀ b, Fx S0 w a b → Q1 b → Runs C P' b (m - n - 1) S w' Q) (hm : n + 1 ≤ m) :
    Runs C (.seq P P') a m S (w ++ w') Q :=
  Runs.call (Q1 := fun b => Fx S0 w a b ∧ Q1 b) (h.mono le_rfl hS (fun _ hb hq => ⟨hb, hq⟩))
    (fun b _ hq => h' b hq.1 hq.2) hm

/-- A silent routine run in a smaller frame, followed by a run. -/
theorem Runs.callS0 {P P' : Sc} {a : Ds} {n m : ℕ} {S0 S : List Var} {w : List Bool}
    {Q1 Q : Ds → Prop} (h : Runs C P a n S0 [] Q1) (hS : S0 ⊆ S)
    (h' : ∀ b, Fx S0 [] a b → Q1 b → Runs C P' b (m - n - 1) S w Q) (hm : n + 1 ≤ m) :
    Runs C (.seq P P') a m S w Q := by
  have := Runs.callS h hS h' hm
  simpa using this

/-- A routine run in a smaller frame, last. -/
theorem Runs.lastS {P : Sc} {a : Ds} {n m : ℕ} {S0 S : List Var} {w : List Bool} {Q1 Q : Ds → Prop}
    (h : Runs C P a n S0 w Q1) (hS : S0 ⊆ S) (hQ : ∀ b, Fx S0 w a b → Q1 b → Q b) (hm : n ≤ m) :
    Runs C P a m S w Q :=
  h.mono hm hS hQ

/-- An exact last step. -/
theorem Runs.last {P : Sc} {a f : Ds} {n m : ℕ} {S : List Var} {w : List Bool} {Q : Ds → Prop}
    (h : Runs C P a n S w (· = f)) (hQ : Fx S w a f → Q f) (hm : n ≤ m) : Runs C P a m S w Q := by
  obtain ⟨b, h1, h2, rfl⟩ := h
  exact ⟨b, h1.mono hm, h2, hQ h2⟩

theorem Runs.iteT {c : Cnd VV} {P P' : Sc} {a : Ds} {m : ℕ} {S : List Var} {w : List Bool}
    {Q : Ds → Prop} (hwf : c.wf) (hc : c.eval a = true) (h : Runs C P a (m - 1) S w Q) (hm : 1 ≤ m) :
    Runs C (.ite c P P') a m S w Q := by
  obtain ⟨b, h1, h2, h3⟩ := h
  exact ⟨b, (Ex.iteT hwf hc h1).mono (by omega), h2, h3⟩

theorem Runs.iteF {c : Cnd VV} {P P' : Sc} {a : Ds} {m : ℕ} {S : List Var} {w : List Bool}
    {Q : Ds → Prop} (hwf : c.wf) (hc : c.eval a = false) (h : Runs C P' a (m - 1) S w Q) (hm : 1 ≤ m) :
    Runs C (.ite c P P') a m S w Q := by
  obtain ⟨b, h1, h2, h3⟩ := h
  exact ⟨b, (Ex.iteF hwf hc h1).mono (by omega), h2, h3⟩

/-- **The counted loop rule.** `Inv j` holds before pass `j`; the test holds before passes `j < N` and fails after
`N` passes; pass `j` writes `ow j`. -/
theorem Runs.loopN {c : Cnd VV} {body : Sc} {S : List Var} (hwf : c.wf) (N cost : ℕ)
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
      exact ⟨b, (Ex.loopF hwf (hstop b hb)).mono (by omega), by simpa using Fx.refl S b, hb⟩
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
theorem Runs.loopN0 {c : Cnd VV} {body : Sc} {S : List Var} (hwf : c.wf) (N cost : ℕ)
    (Inv : ℕ → Ds → Prop)
    (hstep : ∀ j < N, ∀ b, Inv j b → c.eval b = true ∧ Runs C body b cost S [] (Inv (j + 1)))
    (hstop : ∀ b, Inv N b → c.eval b = false) (a : Ds) (ha : Inv 0 a) :
    Runs C (.loop c body) a (N * (cost + 2) + 2) S [] (Inv N) := by
  have h := Runs.loopN hwf N cost (fun _ => []) Inv hstep hstop a ha
  have e : (List.range N).flatMap (fun _ => ([] : List Bool)) = [] := List.flatMap_eq_nil_iff.mpr (fun _ _ => rfl)
  rwa [e] at h

/-- **The measured while rule** (silent bodies): each pass lowers the measure `μ`. -/
theorem Runs.loopW {c : Cnd VV} {body : Sc} {S : List Var} (hwf : c.wf) (Inv : Ds → Prop) (μ : Ds → ℕ)
    (cost : ℕ) (hstep : ∀ b, Inv b → c.eval b = true → Runs C body b cost S [] (fun b' => Inv b' ∧ μ b' < μ b))
    (a : Ds) (ha : Inv a) :
    Runs C (.loop c body) a (μ a * (cost + 2) + 2) S [] (fun b => Inv b ∧ c.eval b = false) := by
  have key : ∀ r b, μ b ≤ r → Inv b →
      Runs C (.loop c body) b (μ b * (cost + 2) + 2) S [] (fun b => Inv b ∧ c.eval b = false) := by
    intro r
    induction r with
    | zero =>
      intro b hμ hb
      cases he : c.eval b
      · exact ⟨b, (Ex.loopF hwf he).mono (by omega), Fx.refl S b, hb, he⟩
      · obtain ⟨b1, _, _, _, hlt⟩ := hstep b hb he
        omega
    | succ r ih =>
      intro b hμ hb
      cases he : c.eval b
      · exact ⟨b, (Ex.loopF hwf he).mono (by omega), Fx.refl S b, hb, he⟩
      · obtain ⟨b1, h1, h2, h3, hlt⟩ := hstep b hb he
        obtain ⟨b2, h4, h5, h6⟩ := ih b1 (by omega) h3
        refine ⟨b2, (Ex.loopT hwf he h1 h4).mono ?_, by simpa using h2.trans h5, h6⟩
        have : μ b1 * (cost + 2) + (cost + 2) ≤ μ b * (cost + 2) := by
          rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hlt
        omega
  exact key (μ a) a le_rfl ha

/-! ### Steps that keep a frame from a base state -/

theorem Runs.op1B {P P' : Sc} {base a f : Ds} {m : ℕ} {S : List Var} {w0 w : List Bool} {Q : Ds → Prop}
    (hb : Fx S w0 base a) (h : Runs C P a 1 S [] (· = f)) (h' : Fx S w0 base f → Runs C P' f (m - 2) S w Q)
    (hm : 2 ≤ m) : Runs C (.seq P P') a m S w Q := by
  obtain ⟨b, h1, h2, rfl⟩ := h
  exact Runs.op1 ⟨b, h1, h2, rfl⟩ (h' (by simpa using hb.trans h2)) hm

theorem Runs.emit1B {P P' : Sc} {base a f : Ds} {m : ℕ} {S : List Var} {bit : Bool} {w0 w : List Bool}
    {Q : Ds → Prop} (hb : Fx S w0 base a) (h : Runs C P a 1 S [bit] (· = f))
    (h' : Fx S (w0 ++ [bit]) base f → Runs C P' f (m - 2) S w Q) (hm : 2 ≤ m) :
    Runs C (.seq P P') a m S (bit :: w) Q := by
  obtain ⟨b, h1, h2, rfl⟩ := h
  exact Runs.emit1 ⟨b, h1, h2, rfl⟩ (h' (hb.trans h2)) hm

theorem Runs.callSB {P P' : Sc} {base a : Ds} {n m : ℕ} {S0 S : List Var} {w0 w1 w : List Bool}
    {Q1 Q : Ds → Prop} (hb : Fx S w0 base a) (h : Runs C P a n S0 w1 Q1) (hS : S0 ⊆ S)
    (h' : ∀ b, Fx S0 w1 a b → Fx S (w0 ++ w1) base b → Q1 b → Runs C P' b (m - n - 1) S w Q) (hm : n + 1 ≤ m) :
    Runs C (.seq P P') a m S (w1 ++ w) Q :=
  Runs.call (Q1 := fun b => Fx S0 w1 a b ∧ Q1 b) (h.mono le_rfl hS (fun _ hb hq => ⟨hb, hq⟩))
    (fun b _ hq => h' b hq.1 (hb.trans (hq.1.mono hS)) hq.2) hm

theorem Runs.callS0B {P P' : Sc} {base a : Ds} {n m : ℕ} {S0 S : List Var} {w0 w : List Bool}
    {Q1 Q : Ds → Prop} (hb : Fx S w0 base a) (h : Runs C P a n S0 [] Q1) (hS : S0 ⊆ S)
    (h' : ∀ b, Fx S0 [] a b → Fx S w0 base b → Q1 b → Runs C P' b (m - n - 1) S w Q) (hm : n + 1 ≤ m) :
    Runs C (.seq P P') a m S w Q := by
  have := Runs.callSB hb h hS (fun b hl hf hq => h' b hl (by simpa using hf) hq) hm
  simpa using this

theorem Runs.lastB {P : Sc} {base a f : Ds} {n m : ℕ} {S : List Var} {w0 w : List Bool} {Q : Ds → Prop}
    (hb : Fx S w0 base a) (h : Runs C P a n S w (· = f)) (hQ : Fx S (w0 ++ w) base f → Q f) (hm : n ≤ m) :
    Runs C P a m S w Q := by
  obtain ⟨b, h1, h2, rfl⟩ := h
  exact ⟨b, h1.mono hm, h2, hQ (hb.trans h2)⟩

theorem Runs.lastSB {P : Sc} {base a : Ds} {n m : ℕ} {S0 S : List Var} {w0 w : List Bool} {Q1 Q : Ds → Prop}
    (hb : Fx S w0 base a) (h : Runs C P a n S0 w Q1) (hS : S0 ⊆ S)
    (hQ : ∀ b, Fx S (w0 ++ w) base b → Q1 b → Q b) (hm : n ≤ m) : Runs C P a m S w Q :=
  h.mono hm hS (fun b hf hq => hQ b (hb.trans (hf.mono hS)) hq)

/-- **The counted loop rule with the frame from the loop start.** -/
theorem Runs.loopNF {c : Cnd VV} {body : Sc} {S : List Var} (hwf : c.wf) (N cost : ℕ)
    (ow : ℕ → List Bool) (Inv : ℕ → Ds → Prop) (a : Ds)
    (hstep : ∀ j < N, ∀ b, Fx S ((List.range j).flatMap ow) a b → Inv j b →
      c.eval b = true ∧ Runs C body b cost S (ow j) (Inv (j + 1)))
    (hstop : ∀ b, Fx S ((List.range N).flatMap ow) a b → Inv N b → c.eval b = false) (ha : Inv 0 a) :
    Runs C (.loop c body) a (N * (cost + 2) + 2) S ((List.range N).flatMap ow) (Inv N) := by
  have key : ∀ d j, j + d = N → ∀ b, Fx S ((List.range j).flatMap ow) a b → Inv j b →
      Runs C (.loop c body) b (d * (cost + 2) + 2) S ((List.range' j d).flatMap ow) (Inv N) := by
    intro d
    induction d with
    | zero =>
      intro j hj b hfb hb
      rw [Nat.add_zero] at hj; subst hj
      exact ⟨b, (Ex.loopF hwf (hstop b hfb hb)).mono (by omega), by simpa using Fx.refl S b, hb⟩
    | succ d ih =>
      intro j hj b hfb hb
      obtain ⟨hc, b1, h1, h2, h3⟩ := hstep j (by omega) b hfb hb
      have hf1 : Fx S ((List.range (j + 1)).flatMap ow) a b1 := by
        rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]; exact hfb.trans h2
      obtain ⟨b2, h4, h5, h6⟩ := ih (j + 1) (by omega) b1 hf1 h3
      refine ⟨b2, (Ex.loopT hwf hc h1 h4).mono (by nlinarith), ?_, h6⟩
      have e : (List.range' j (d + 1)).flatMap ow = ow j ++ (List.range' (j + 1) d).flatMap ow := by
        rw [List.range'_succ, List.flatMap_cons]
      rw [e]; exact h2.trans h5
  have h := key N 0 (by omega) a (by simpa using Fx.refl S a) ha
  rwa [List.range_eq_range']

/-- The counted loop rule with the frame from the loop start, for silent bodies. -/
theorem Runs.loopN0F {c : Cnd VV} {body : Sc} {S : List Var} (hwf : c.wf) (N cost : ℕ)
    (Inv : ℕ → Ds → Prop) (a : Ds)
    (hstep : ∀ j < N, ∀ b, Fx S [] a b → Inv j b → c.eval b = true ∧ Runs C body b cost S [] (Inv (j + 1)))
    (hstop : ∀ b, Fx S [] a b → Inv N b → c.eval b = false) (ha : Inv 0 a) :
    Runs C (.loop c body) a (N * (cost + 2) + 2) S [] (Inv N) := by
  have e : ∀ k, (List.range k).flatMap (fun _ => ([] : List Bool)) = [] :=
    fun _ => List.flatMap_eq_nil_iff.mpr (fun _ _ => rfl)
  have h := Runs.loopNF hwf N cost (fun _ => []) Inv a (fun j hj b hf hb => hstep j hj b (by rwa [e] at hf) hb)
    (fun b hf hb => hstop b (by rwa [e] at hf) hb) ha
  rwa [e] at h

/-- **The measured while rule with the frame from the loop start** (silent bodies). -/
theorem Runs.loopWF {c : Cnd VV} {body : Sc} {S : List Var} (hwf : c.wf) (Inv : Ds → Prop) (μ : Ds → ℕ)
    (cost : ℕ) (a : Ds)
    (hstep : ∀ b, Fx S [] a b → Inv b → c.eval b = true → Runs C body b cost S [] (fun b' => Inv b' ∧ μ b' < μ b))
    (ha : Inv a) :
    Runs C (.loop c body) a (μ a * (cost + 2) + 2) S [] (fun b => Inv b ∧ c.eval b = false) := by
  have h := Runs.loopW (S := S) (C := C) hwf (fun b => Fx S [] a b ∧ Inv b) μ cost (fun b ⟨hf, hb⟩ hc => by
    obtain ⟨b', h1, h2, h3, h4⟩ := hstep b hf hb hc
    exact ⟨b', h1, h2, ⟨by simpa using hf.trans h2, h3⟩, h4⟩) a ⟨Fx.refl S a, ha⟩
  exact h.mono le_rfl (List.Subset.refl _) (fun b _ hb => ⟨hb.1.2, hb.2⟩)

end Rules

/-! ## Single operations -/

section Ops

variable (C : Ctx)

theorem r_zero (S : List Var) (a : Ds) (x : Var) (hx : x ∈ S) :
    Runs C (.op (.zero x)) a 1 S [] (· = a.set x 0) :=
  ⟨_, Ex.op (OpEx.zero x a), Fx.set S a x 0 hx, rfl⟩

theorem r_inc (S : List Var) (a : Ds) (x : Var) (hx : x ∈ S) (h : a.env x + 1 < 2 ^ C.Wd) :
    Runs C (.op (.inc x)) a 1 S [] (· = a.set x (a.env x + 1)) :=
  ⟨_, Ex.op (OpEx.inc x a h), Fx.set S a x _ hx, rfl⟩

theorem r_add (S : List Var) (a : Ds) (x y : Var) (hx : x ∈ S) (hxy : x ≠ y)
    (h : a.env x + a.env y < 2 ^ C.Wd) :
    Runs C (.op (.add x y)) a 1 S [] (· = a.set x (a.env x + a.env y)) :=
  ⟨_, Ex.op (OpEx.add x y a hxy h), Fx.set S a x _ hx, rfl⟩

theorem r_sub (S : List Var) (a : Ds) (x y : Var) (hx : x ∈ S) (hxy : x ≠ y) (h : a.env y ≤ a.env x) :
    Runs C (.op (.sub x y)) a 1 S [] (· = a.set x (a.env x - a.env y)) :=
  ⟨_, Ex.op (OpEx.sub x y a hxy h), Fx.set S a x _ hx, rfl⟩

theorem r_copy (S : List Var) (a : Ds) (x y : Var) (hx : x ∈ S) (hxy : x ≠ y) :
    Runs C (.op (.copy x y)) a 1 S [] (· = a.set x (a.env y)) :=
  ⟨_, Ex.op (OpEx.copy x y a hxy), Fx.set S a x _ hx, rfl⟩

theorem r_half (S : List Var) (a : Ds) (x : Var) (hx : x ∈ S) :
    Runs C (.op (.half x)) a 1 S [] (· = a.set x (a.env x / 2)) :=
  ⟨_, Ex.op (OpEx.half x a), Fx.set S a x _ hx, rfl⟩

theorem r_shl (S : List Var) (a : Ds) (x : Var) (hx : x ∈ S) (h : 2 * a.env x < 2 ^ C.Wd) :
    Runs C (.op (.shl x)) a 1 S [] (· = a.set x (2 * a.env x)) :=
  ⟨_, Ex.op (OpEx.shl x a h), Fx.set S a x _ hx, rfl⟩

theorem r_mul (S : List Var) (a : Ds) (x y z : Var) (hz : z ∈ S) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (h : a.env x * a.env y < 2 ^ C.Wd) :
    Runs C (.op (.mul x y z)) a 1 S [] (· = a.set z (a.env x * a.env y)) :=
  ⟨_, Ex.op (OpEx.mul x y z a hxy hxz hyz h), Fx.set S a z _ hz, rfl⟩

theorem r_dm (S : List Var) (a : Ds) (x y q r : Var) (hq : q ∈ S) (hr : r ∈ S) (hxy : x ≠ y) (hxq : x ≠ q)
    (hxr : x ≠ r) (hyq : y ≠ q) (hyr : y ≠ r) (hqr : q ≠ r) (hy : 0 < a.env y) (h2 : 2 * a.env y ≤ 2 ^ C.Wd) :
    Runs C (.op (.dm x y q r)) a 1 S [] (· = (a.set q (a.env x / a.env y)).set r (a.env x % a.env y)) := by
  have hf := (Fx.set S a q (a.env x / a.env y) hq).trans (Fx.set S _ r (a.env x % a.env y) hr)
  exact ⟨_, Ex.op (OpEx.dm x y q r a hxy hxq hxr hyq hyr hqr hy h2), by simpa using hf, rfl⟩

theorem r_emit (S : List Var) (a : Ds) (bit : Bool) :
    Runs C (.op (.emit bit)) a 1 S [bit] (· = { a with out := a.out ++ [bit] }) :=
  ⟨_, Ex.op (OpEx.emit bit a), Fx.emit S a bit, rfl⟩

theorem r_rdM (S : List Var) (a : Ds) (m : Fin MM) (x : Var) (hx : x ∈ S) (h : a.rc m < (a.ram m).length) :
    Runs C (.op (.rdM m x)) a 1 S [] (· = (a.set x ((a.ram m).getD (a.rc m) 0)).adv m) :=
  ⟨_, Ex.op (OpEx.rdM m x a h), ⟨fun _ hy => DS.set_env_ne _ _ (fun e => hy (e ▸ hx)), rfl,
    (List.append_nil _).symm, rfl, rfl, rfl⟩, rfl⟩

theorem r_wrM (S : List Var) (a : Ds) (m : Fin MM) (x : Var) (h : a.rc m ≤ (a.ram m).length) :
    Runs C (.op (.wrM m x)) a 1 S [] (· = a.put m (a.env x)) :=
  ⟨_, Ex.op (OpEx.wrM m x a h), Fx.store S a _ _, rfl⟩

theorem r_rwM (S : List Var) (a : Ds) (m : Fin MM) : Runs C (.op (.rwM m)) a (a.rc m + 1) S [] (· = a.rew m) :=
  ⟨_, Ex.op (OpEx.rwM m a), Fx.store S a _ _, rfl⟩

end Ops

@[simp] theorem out_env (a : Ds) (l : List Bool) : ({ a with out := l }).env = a.env := rfl
@[simp] theorem adv_env (a : Ds) (m : Fin MM) : (a.adv m).env = a.env := rfl
@[simp] theorem put_env (a : Ds) (m : Fin MM) (v : ℕ) : (a.put m v).env = a.env := rfl
@[simp] theorem rew_env (a : Ds) (m : Fin MM) : (a.rew m).env = a.env := rfl

theorem wf_eq {x y : Var} (h : x ≠ y) : (Cnd.eq x y).wf := h
theorem wf_lt {x y : Var} (h : x ≠ y) : (Cnd.lt x y).wf := h

@[simp] theorem eval_eq (a : Ds) (x y : Var) : (Cnd.eq x y).eval a = decide (a.env x = a.env y) := rfl
@[simp] theorem eval_lt (a : Ds) (x y : Var) : (Cnd.lt x y).eval a = decide (a.env x < a.env y) := rfl

/-- Normalize the variable reads of an explicit state. -/
syntax "norm_env" (Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic| norm_env $[$loc]?) =>
    `(tactic| simp (config := { decide := true }) only [env_set, eval_eq, eval_lt, out_env, adv_env, put_env, rew_env,
      ite_true, ite_false, Fin.isValue] $[$loc]?)

end NearCubicGates.Adapters.ShortPCP.MaskMachine
