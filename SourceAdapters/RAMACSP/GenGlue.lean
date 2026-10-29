import SourceAdapters.RAMACSP.GenEmit

/-!
# The generator's calls: cell glue between `FL` stages

Paper: `lem:generator`. Shoup's ordinary algorithm supplies the irreducible
polynomial; its coefficients are read as the modulus mask used by subsequent
field operations and output stages.

Three cell programs, each keeping the `FL` relation `Rel G s` (the fixed registers, the program variables, the output
and the input position) except for the documented change:
- `callIrr`: `kin := true :: 1^f` (`f` in program variable `36`), `kcall`, read the callee's `f + 1` output bits
  `u` into program variable `37` as `bitsValue u` (`callIrr_spec`);
- `callCons`: `kin := false :: frame x ++ frame y` from the program variables `20, 21` (`bitsValue x`, `|x|`) and
  `22, 23` (`bitsValue y`, `|y|`), then `kcall` (`callCons_spec`);
- `copyOut`: the callee's output `frame u` is appended to the output as `dbl u` (`copyOut_spec`).
Scratch registers: `9 … 15` and `67, 68` (free for `Rel`, `Rel.set_free`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace NearCubicGates.Adapters.RAMACSP.Gen

open NearCubicGates.Close.Cells NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Adapters.ShortPCP NearCubicGates.Adapters.ShortPCP.Machines
open NearCubicGates.Adapters.ShortPCP.Machines.FL
open NearCubicGates.Adapters.Joins.FieldCells (vr)

/-! ## `Rel` is blind to the call registers and to scratch -/

theorem relKin {G : Glob} {s : FS} {a : DS VV MM} (r : Rel G s a) (k : List Bool) : Rel G s { a with kin := k } :=
  ⟨Env.of_env (a := a) rfl r.env, r.uv, r.out, r.le, r.fok, r.ip⟩

theorem relCalled {G : Glob} {s : FS} {a : DS VV MM} (r : Rel G s a) (o : List Bool) : Rel G s (a.called o) :=
  ⟨Env.of_env (a := a) rfl r.env, r.uv, r.out, r.le, r.fok, r.ip⟩

theorem relKc {G : Glob} {s : FS} {a : DS VV MM} (r : Rel G s a) (x : Fin VV) (v k : ℕ) (h1 : 9 ≤ x.val)
    (h2 : x.val < 72) : Rel G s { a.set x v with kc := k } :=
  let r' := r.set_free h1 h2 v
  ⟨Env.of_env (a := a.set x v) rfl r'.env, r'.uv, r'.out, r'.le, r'.fok, r'.ip⟩

/-- Emitting a bit: the `FL` state's output grows the same way. -/
theorem relEmit {G : Glob} {s : FS} {a : DS VV MM} (r : Rel G s a) (b : Bool) :
    Rel G { s with out := s.out ++ [b] } { a with out := a.out ++ [b] } :=
  ⟨Env.of_env (a := a) rfl r.env, r.uv, by rw [r.out], r.le, r.fok, r.ip⟩

/-- Glue scratch registers. -/
def g0 : Fin VV := vr 9
def g1 : Fin VV := vr 10
def g2 : Fin VV := vr 11
def g3 : Fin VV := vr 12
def g4 : Fin VV := vr 13
def g5 : Fin VV := vr 14
def g6 : Fin VV := vr 15

theorem g_free {x : Fin VV} (hx : x = g0 ∨ x = g1 ∨ x = g2 ∨ x = g3 ∨ x = g4 ∨ x = g5 ∨ x = g6) :
    9 ≤ x.val ∧ x.val < 72 := by
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem relSetg {G : Glob} {s : FS} {a : DS VV MM} (r : Rel G s a) (x : Fin VV) (v : ℕ)
    (hx : x = g0 ∨ x = g1 ∨ x = g2 ∨ x = g3 ∨ x = g4 ∨ x = g5 ∨ x = g6 := by decide) : Rel G s (a.set x v) :=
  r.set_free (g_free hx).1 (g_free hx).2 v

theorem g_ne_uv (i : Var) {x : Fin VV} (hx : x = g0 ∨ x = g1 ∨ x = g2 ∨ x = g3 ∨ x = g4 ∨ x = g5 ∨ x = g6) :
    x ≠ FL.uv i := ne_of_val (by rw [uv_val]; have := g_free hx; omega)

/-! ## The Shoup call (G3) -/

/-- `kin := true :: 1^f` (`f` in program variable `36`). -/
def kemOnes : St VV MM :=
  .seq (.op (.kem true)) (.seq (.op (.zero g0)) (.loop (.lt g0 (FL.uv 36)) (.seq (.op (.kem true)) (.op (.inc g0)))))

theorem kemOnes_spec (C : Ctx) (G : Glob) (s : FS) (a : DS VV MM) (r : Rel G s a) (hk : a.kin = [])
    (f : ℕ) (hf : s.env 36 = f) (hLk : f + 1 < C.Lk) (hW : f + 1 < 2 ^ C.Wd) :
    Hs C kemOnes a (5 * f + 6) (fun b => Rel G s b ∧ b.kin = true :: List.replicate f true) := by
  refine hs_step (OpEx.kem true a (by rw [hk]; simp; omega)) ?_
  have r1 : Rel G s { a with kin := a.kin ++ [true] } := relKin r _
  refine hs_step (OpEx.zero g0 _) ?_
  let I : ℕ → DS VV MM → Prop := fun j b => Rel G s b ∧ b.env g0 = j ∧ b.kin = true :: List.replicate j true
  have hI0 : I 0 (({ a with kin := a.kin ++ [true] } : DS VV MM).set g0 0) :=
    ⟨relSetg r1 g0 0, by simp, by show a.kin ++ [true] = _; rw [hk]; rfl⟩
  have hwf : (Cnd.lt g0 (FL.uv 36)).wf := g_ne_uv 36 (Or.inl rfl)
  refine Hs.mono (Hs.loopN (c := .lt g0 (FL.uv 36)) hwf I f 3 (fun j hj b ⟨rb, b0, bk⟩ => ⟨?_, ?_⟩)
    (fun b ⟨rb, b0, bk⟩ => ?_) _ hI0) (by omega) (fun b ⟨rb, _, bk⟩ => ⟨rb, bk⟩)
  · simp only [Cnd.eval, b0, (rb.uv 36).trans hf, decide_eq_true_eq]; exact hj
  · refine hs_step (OpEx.kem true b (by rw [bk]; simp; omega)) ?_
    refine Hs.op (OpEx.inc g0 _ (by show b.env g0 + 1 < _; omega)) ?_
    refine ⟨relSetg (relKin rb _) g0 _, by rw [DS.set_env_self]; show b.env g0 + 1 = j + 1; rw [b0], ?_⟩
    show b.kin ++ [true] = _; rw [bk, List.replicate_succ']; rfl
  · simp only [Cnd.eval, b0, (rb.uv 36).trans hf, decide_eq_false_iff_not]; omega

/-- Read `f + 1` bits of the callee output into `g1` (as `bitsValue`), then `37 := g1`. -/
def readBits : St VV MM :=
  .seq (.op (.zero g1)) (.seq (.op (.copy g2 r1)) (.seq (.op (.zero g0)) (.seq (.op (.copy g3 (FL.uv 36)))
    (.seq (.op (.inc g3)) (.seq (.loop (.lt g0 g3) (.seq (.op (.rdK g4)) (.seq (.ite (.eq g4 r1) (.op (.add g1 g2)) (.op (.zero g6)))
      (.seq (.op (.shl g2)) (.op (.inc g0))))))
      (.op (.copy (FL.uv 37) g1)))))))

theorem readBits_spec (C : Ctx) (G : Glob) (s : FS) (a : DS VV MM) (r : Rel G s a) (f : ℕ) (hf : s.env 36 = f)
    (u : List Bool) (ho : a.kout = u) (hc : a.kc = 0) (hu : u.length = f + 1)
    (hW : 2 ^ (f + 3) < 2 ^ C.Wd) (hcap : 2 ^ (f + 1) ≤ G.cap + 1) :
    Hs C readBits a (10 * f + 40) (fun b => Rel G (s.setv 37 (CanonicalBinary.bitsValue u)) b ∧ b.kin = a.kin) := by
  have hpw : ∀ j ≤ f + 1, 2 * 2 ^ j < 2 ^ C.Wd := fun j hj => by
    have : 2 ^ (j + 1) ≤ 2 ^ (f + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [pow_succ] at this; omega
  have hfW : f + 3 < 2 ^ C.Wd := lt_of_lt_of_le Nat.lt_two_pow_self (le_of_lt hW)
  have hF : a.env (FL.uv 36) = f := (r.uv 36).trans hf
  refine hs_step (OpEx.zero g1 a) ?_
  refine hs_step (OpEx.copy g2 r1 _ (by decide)) ?_
  refine hs_step (OpEx.zero g0 _) ?_
  refine hs_step (OpEx.copy g3 (FL.uv 36) _ (g_ne_uv 36 (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) ?_
  set a4 := (((a.set g1 0).set g2 ((a.set g1 0).env r1)).set g0 0).set g3
    ((((a.set g1 0).set g2 ((a.set g1 0).env r1)).set g0 0).env (FL.uv 36)) with ha4
  have a4g3 : a4.env g3 = f := by
    simp only [a4, DS.set_env_self]
    rw [DS.set_env_ne _ _ (g_ne_uv 36 (Or.inl rfl)).symm, DS.set_env_ne _ _ (g_ne_uv 36 (Or.inr (Or.inr (Or.inl rfl)))).symm,
      DS.set_env_ne _ _ (g_ne_uv 36 (Or.inr (Or.inl rfl))).symm, hF]
  refine hs_step (OpEx.inc g3 a4 (by rw [a4g3]; omega)) ?_
  set a5 := a4.set g3 (a4.env g3 + 1) with ha5
  have r5 : Rel G s a5 := relSetg (relSetg (relSetg (relSetg (relSetg r g1 _)
    g2 _) g0 _) g3 _)
    g3 _
  have e1 : a5.env g1 = 0 := by simp [a5, a4, DS.set_env_ne _ _ (show g1 ≠ g3 by decide),
    DS.set_env_ne _ _ (show g1 ≠ g0 by decide), DS.set_env_ne _ _ (show g1 ≠ g2 by decide)]
  have e2 : a5.env g2 = 1 := by
    simp only [a5, a4, DS.set_env_ne _ _ (show g2 ≠ g3 by decide), DS.set_env_ne _ _ (show g2 ≠ g0 by decide),
      DS.set_env_self, DS.set_env_ne _ _ (show r1 ≠ g1 by decide), r.env.c1]
  have e0 : a5.env g0 = 0 := by simp [a5, a4, DS.set_env_ne _ _ (show g0 ≠ g3 by decide)]
  have e3 : a5.env g3 = f + 1 := by simp [a5, a4g3]
  -- the read loop
  let I : ℕ → DS VV MM → Prop := fun j b => Rel G s b ∧ b.env g0 = j ∧
    b.env g1 = CanonicalBinary.bitsValue (u.take j) ∧ b.env g2 = 2 ^ j ∧ b.env g3 = f + 1 ∧ b.kc = j ∧ b.kout = u ∧
    b.kin = a.kin
  have hI0 : I 0 a5 := ⟨r5, e0, by simp [e1, CanonicalBinary.bitsValue], by simp [e2], e3, by simp [a5, a4, hc],
    by simp [a5, a4, ho], by simp [a5, a4]⟩
  have hbody : ∀ j < f + 1, ∀ b, I j b → (Cnd.lt g0 g3).eval b = true ∧
      Hs C (.seq (.op (.rdK g4)) (.seq (.ite (.eq g4 r1) (.op (.add g1 g2)) (.op (.zero g6))) (.seq (.op (.shl g2)) (.op (.inc g0)))))
        b 8 (I (j + 1)) := by
    rintro j hj b ⟨rb, b0, b1, b2, b3, bc, bo, bk⟩
    refine ⟨by simp only [Cnd.eval, b0, b3, decide_eq_true_eq]; omega, ?_⟩
    refine hs_step (OpEx.rdK g4 b (by rw [bc, bo, hu]; omega)) ?_
    set c := ({ b.set g4 (bitOf b.kout b.kc) with kc := b.kc + 1 } : DS VV MM) with hcdef
    have rc : Rel G s c := relKc rb g4 _ _ (by decide) (by decide)
    have c4 : c.env g4 = (u.getD j false).toNat := by simp [c, bitOf, bo, bc]
    have c1 : c.env g1 = CanonicalBinary.bitsValue (u.take j) := by
      simp [c, DS.set_env_ne _ _ (show g1 ≠ g4 by decide), b1]
    have c2 : c.env g2 = 2 ^ j := by simp [c, DS.set_env_ne _ _ (show g2 ≠ g4 by decide), b2]
    have c0 : c.env g0 = j := by simp [c, DS.set_env_ne _ _ (show g0 ≠ g4 by decide), b0]
    have c3 : c.env g3 = f + 1 := by simp [c, DS.set_env_ne _ _ (show g3 ≠ g4 by decide), b3]
    have hjl : j < u.length := by omega
    have hbt := bitsValue_take_succ u j hjl
    have hbl : CanonicalBinary.bitsValue (u.take j) < 2 ^ j := by
      have := bv_lt (u.take j); simp only [List.length_take] at this; rwa [min_eq_left (by omega)] at this
    -- after the conditional add: `g1 = bitsValue (take (j+1))`
    have hite : Hs C (.ite (.eq g4 r1) (.op (.add g1 g2)) (.op (.zero g6))) c 2 (fun d => Rel G s d ∧ d.env g0 = j ∧
        d.env g1 = CanonicalBinary.bitsValue (u.take (j + 1)) ∧ d.env g2 = 2 ^ j ∧ d.env g3 = f + 1 ∧
        d.kc = j + 1 ∧ d.kout = u ∧ d.kin = a.kin) := by
      refine Hs.ite (show g4 ≠ r1 by decide) (fun he => ?_) (fun he => ?_)
      · have hb1 : (u.getD j false) = true := by
          simp only [Cnd.eval, c4, rc.env.c1, decide_eq_true_eq] at he
          cases h : u.getD j false <;> simp_all
        refine Hs.op (OpEx.add g1 g2 c (by decide) (by rw [c1, c2]; have := hpw j (by omega); omega)) ?_
        refine ⟨relSetg rc g1 _, by simp [DS.set_env_ne _ _ (show g0 ≠ g1 by decide), c0], ?_,
          by simp [DS.set_env_ne _ _ (show g2 ≠ g1 by decide), c2],
          by simp [DS.set_env_ne _ _ (show g3 ≠ g1 by decide), c3], by simp [c, bc], by simp [c, bo], by simp [c, bk]⟩
        simp only [DS.set_env_self, c1, c2, hbt, hb1]; simp
      · have hb0 : (u.getD j false) = false := by
          simp only [Cnd.eval, c4, rc.env.c1, decide_eq_false_iff_not] at he
          cases h : u.getD j false <;> simp_all
        refine Hs.op (OpEx.zero g6 c) ⟨relSetg rc g6 _,
          by simp [DS.set_env_ne _ _ (show g0 ≠ g6 by decide), c0], ?_,
          by simp [DS.set_env_ne _ _ (show g2 ≠ g6 by decide), c2],
          by simp [DS.set_env_ne _ _ (show g3 ≠ g6 by decide), c3], by simp [c, bc], by simp [c, bo], by simp [c, bk]⟩
        simp only [DS.set_env_ne _ _ (show g1 ≠ g6 by decide), c1, hbt, hb0]; simp
    refine Hs.mono (Hs.seq (t2 := 3) hite (fun d ⟨rd, d0, d1, d2, d3, dc, dout, dk⟩ => ?_)) (by omega) (fun _ h => h)
    refine hs_step (OpEx.shl g2 d (by rw [d2]; exact hpw j (by omega))) ?_
    have hjl2 : j < 2 ^ j := Nat.lt_two_pow_self
    refine Hs.op (OpEx.inc g0 _ (by
      rw [DS.set_env_ne _ _ (show g0 ≠ g2 by decide), d0]; have := hpw j (by omega); omega)) ?_
    refine ⟨relSetg (relSetg rd g2 _) g0 _, ?_, ?_, ?_, ?_, by simp [dc],
      by simp [dout], by simp [dk]⟩
    · simp [DS.set_env_ne _ _ (show g0 ≠ g2 by decide), d0]
    · simp [DS.set_env_ne _ _ (show g1 ≠ g0 by decide), DS.set_env_ne _ _ (show g1 ≠ g2 by decide), d1]
    · simp [DS.set_env_ne _ _ (show g2 ≠ g0 by decide), d2, pow_succ]; ring
    · simp [DS.set_env_ne _ _ (show g3 ≠ g0 by decide), DS.set_env_ne _ _ (show g3 ≠ g2 by decide), d3]
  refine Hs.mono (Hs.seq (t2 := 1) (Hs.loopN (c := .lt g0 g3) (show g0 ≠ g3 by decide) I (f + 1) 8 hbody
    (fun b ⟨_, b0, _, _, b3, _⟩ => by simp only [Cnd.eval, b0, b3, decide_eq_false_iff_not]; omega) a5 hI0)
    (fun b hb => ?_)) (by omega) (fun _ h => h)
  obtain ⟨rb, b0, b1, b2, b3, bc, bo, bk⟩ := hb
  refine Hs.op (OpEx.copy (FL.uv 37) g1 b (g_ne_uv 37 (Or.inr (Or.inl rfl))).symm) ?_
  rw [b1, ← hu, List.take_length]
  have hbu : CanonicalBinary.bitsValue u ≤ G.cap := by have := bv_lt u; rw [hu] at this; omega
  exact ⟨rb.setv 37 hbu, by simp [bk]⟩

/-- **The Shoup call** (G3): `kemOnes`, `kcall`, `readBits`. -/
def callIrr : St VV MM := .seq kemOnes (.seq (.op .kcall) readBits)

/-- The cost bound of `callIrr`. -/
def callIrrCost (C : Ctx) (f : ℕ) : ℕ := 15 * f + C.Lk + C.Bk + 60

theorem callIrr_spec (C : Ctx) (G : Glob) (s : FS) (a : DS VV MM) (r : Rel G s a) (hk : a.kin = [])
    (f : ℕ) (hf : s.env 36 = f) (q : C.K.Req) (hin : C.K.inw q = true :: List.replicate f true)
    (u : List Bool) (hout : C.K.outw q = u) (hu : u.length = f + 1) (hbud : C.K.bud q ≤ C.Bk)
    (hLk : f + 1 < C.Lk) (hW : 2 ^ (f + 3) < 2 ^ C.Wd) (hcap : 2 ^ (f + 1) ≤ G.cap + 1) :
    Hs C callIrr a (callIrrCost C f) (fun b => Rel G (s.setv 37 (CanonicalBinary.bitsValue u)) b ∧ b.kin = []) := by
  have hfW : f + 1 < 2 ^ C.Wd := lt_of_lt_of_le (Nat.lt_of_lt_of_le (by omega) (Nat.lt_two_pow_self (n := f + 3)))
    (le_of_lt hW)
  refine Hs.mono (Hs.seq (t2 := 1 + C.Lk + C.Bk + (10 * f + 40) + 1) (kemOnes_spec C G s a r hk f hf hLk hfW)
    (fun b ⟨rb, bk⟩ => Hs.seq (t2 := 10 * f + 40)
    (Hs.op (R := fun c => c = b.called (C.K.outw q)) (OpEx.kcall q b (by rw [bk, hin]) hbud) rfl)
    (fun c hc => ?_))) (by unfold callIrrCost; omega) (fun _ h => h)
  -- after the call: read the `f + 1` output bits
  subst hc
  refine Hs.mono (readBits_spec C G s _ (relCalled rb (C.K.outw q)) f hf u (by simp [DS.called, hout]) rfl hu hW hcap)
    le_rfl (fun d ⟨rd, dk⟩ => ⟨rd, by rw [dk]; rfl⟩)

/-! ## The cons call (G5): `kin := false :: frame x ++ frame y`, then `kcall` -/

/-- Append `frame` of the `n` low bits of program variable `vX` (`n` in `vN`) to `kin`. -/
def kemFrame (vX vN : Var) : St VV MM :=
  .seq (.op (.copy g5 (FL.uv vX))) (.seq (.op (.zero g0)) (.seq (.loop (.lt g0 (FL.uv vN))
    (.seq (.op (.kem true)) (.seq (.op (.dm g5 r2 g6 g4)) (.seq (.ite (.eq g4 r1) (.op (.kem true)) (.op (.kem false)))
      (.seq (.op (.copy g5 g6)) (.op (.inc g0)))))))
    (.op (.kem false))))

theorem dbl_length (w : List Bool) : (dbl w).length = 2 * w.length := by
  induction w with
  | nil => rfl
  | cons b w ih => simp [dbl] at ih ⊢; omega

theorem dbl_take_succ (x : List Bool) (j : ℕ) (hj : j < x.length) :
    dbl (x.take (j + 1)) = dbl (x.take j) ++ [true, x.getD j false] := by
  rw [List.take_add_one, dbl_append, List.getElem?_eq_getElem hj]
  simp [dbl, List.getElem?_eq_getElem hj]

theorem kemFrame_spec (C : Ctx) (G : Glob) (s : FS) (a : DS VV MM) (r : Rel G s a) (vX vN : Var)
    (x : List Bool) (hX : s.env vX = CanonicalBinary.bitsValue x) (hN : s.env vN = x.length)
    (hLk : a.kin.length + 2 * x.length + 1 < C.Lk) (hW : x.length + 4 < 2 ^ C.Wd) :
    Hs C (kemFrame vX vN) a (12 * x.length + 10) (fun b => Rel G s b ∧ b.kin = a.kin ++ frame x) := by
  have hXa : a.env (FL.uv vX) = CanonicalBinary.bitsValue x := (r.uv vX).trans hX
  refine hs_step (OpEx.copy g5 (FL.uv vX) a (g_ne_uv vX (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))) ?_
  refine hs_step (OpEx.zero g0 _) ?_
  set a2 := (a.set g5 (a.env (FL.uv vX))).set g0 0 with ha2
  have ra2 : Rel G s a2 := relSetg (relSetg r g5 _) g0 _
  let I : ℕ → DS VV MM → Prop := fun j b => Rel G s b ∧ b.env g0 = j ∧
    b.env g5 = CanonicalBinary.bitsValue x / 2 ^ j ∧ b.kin = a.kin ++ dbl (x.take j)
  have hI0 : I 0 a2 := ⟨ra2, by simp [a2], by simp [a2, DS.set_env_ne _ _ (show g5 ≠ g0 by decide), hXa],
    by simp [a2, dbl]⟩
  have hwf : (Cnd.lt g0 (FL.uv vN)).wf := g_ne_uv vN (Or.inl rfl)
  have hbody : ∀ j < x.length, ∀ b, I j b → (Cnd.lt g0 (FL.uv vN)).eval b = true ∧
      Hs C (.seq (.op (.kem true)) (.seq (.op (.dm g5 r2 g6 g4)) (.seq (.ite (.eq g4 r1) (.op (.kem true))
        (.op (.kem false))) (.seq (.op (.copy g5 g6)) (.op (.inc g0)))))) b 10 (I (j + 1)) := by
    rintro j hj b ⟨rb, b0, b5, bk⟩
    refine ⟨by simp only [Cnd.eval, b0, (rb.uv vN).trans hN, decide_eq_true_eq]; exact hj, ?_⟩
    have hkl : (a.kin ++ dbl (x.take j)).length = a.kin.length + 2 * j := by
      rw [List.length_append, dbl_length, List.length_take, min_eq_left (by omega)]
    refine hs_step (OpEx.kem true b (by rw [bk, hkl]; omega)) ?_
    set c := ({ b with kin := b.kin ++ [true] } : DS VV MM) with hc
    have rc : Rel G s c := relKin rb _
    have hW4 : 2 * 2 ≤ 2 ^ C.Wd := by omega
    refine hs_step (OpEx.dm g5 r2 g6 g4 c (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by rw [rc.env.c2]; omega) (by rw [rc.env.c2]; exact hW4)) ?_
    set d := (c.set g6 (c.env g5 / c.env r2)).set g4 (c.env g5 % c.env r2) with hd
    have rd : Rel G s d := relSetg (relSetg rc g6 _) g4 _
    have c5 : c.env g5 = CanonicalBinary.bitsValue x / 2 ^ j := b5
    have c2 : c.env r2 = 2 := rc.env.c2
    have d4 : d.env g4 = (x.getD j false).toNat := by
      simp only [d, DS.set_env_self, c5, c2]; exact testBit_bitsValue x j
    have d6 : d.env g6 = CanonicalBinary.bitsValue x / 2 ^ (j + 1) := by
      simp only [d, DS.set_env_ne _ _ (show g6 ≠ g4 by decide), DS.set_env_self, c5, c2, pow_succ,
        Nat.div_div_eq_div_mul]
    have d0 : d.env g0 = j := by
      simp only [d, DS.set_env_ne _ _ (show g0 ≠ g4 by decide), DS.set_env_ne _ _ (show g0 ≠ g6 by decide)]; exact b0
    have dk : d.kin = a.kin ++ dbl (x.take j) ++ [true] := by simp [d, c, bk]
    have hite : Hs C (.ite (.eq g4 r1) (.op (.kem true)) (.op (.kem false))) d 2 (fun e => Rel G s e ∧
        e.env = d.env ∧ e.kin = a.kin ++ dbl (x.take (j + 1))) := by
      have hkl' : d.kin.length < C.Lk := by rw [dk, List.length_append, hkl]; simp; omega
      refine Hs.ite (show g4 ≠ r1 by decide) (fun he => ?_) (fun he => ?_)
      · have hb : x.getD j false = true := by
          simp only [Cnd.eval, d4, rd.env.c1, decide_eq_true_eq] at he; cases h : x.getD j false <;> simp_all
        refine Hs.op (OpEx.kem true d hkl') ⟨relKin rd _, rfl, ?_⟩
        show d.kin ++ [true] = _; rw [dk, dbl_take_succ x j hj, hb]; simp
      · have hb : x.getD j false = false := by
          simp only [Cnd.eval, d4, rd.env.c1, decide_eq_false_iff_not] at he; cases h : x.getD j false <;> simp_all
        refine Hs.op (OpEx.kem false d hkl') ⟨relKin rd _, rfl, ?_⟩
        show d.kin ++ [false] = _; rw [dk, dbl_take_succ x j hj, hb]; simp
    refine Hs.mono (Hs.seq (t2 := 3) hite (fun e ⟨re, ee, ek⟩ => ?_)) (by omega) (fun _ h => h)
    have e6 : e.env g6 = CanonicalBinary.bitsValue x / 2 ^ (j + 1) := by rw [ee, d6]
    have e0 : e.env g0 = j := by rw [ee, d0]
    refine hs_step (OpEx.copy g5 g6 e (by decide)) ?_
    refine Hs.op (OpEx.inc g0 _ (by rw [DS.set_env_ne _ _ (show g0 ≠ g5 by decide), e0]; omega)) ?_
    refine ⟨relSetg (relSetg re g5 _) g0 _,
      by simp [DS.set_env_ne _ _ (show g0 ≠ g5 by decide), e0], ?_, by simp [ek]⟩
    simp [DS.set_env_ne _ _ (show g5 ≠ g0 by decide), e6]
  refine Hs.mono (Hs.seq (t2 := 1) (Hs.loopN (c := .lt g0 (FL.uv vN)) hwf I x.length 10 hbody
    (fun b ⟨rb, b0, _, _⟩ => by simp only [Cnd.eval, b0, (rb.uv vN).trans hN, decide_eq_false_iff_not]; omega) a2 hI0)
    (fun b hb => ?_)) (by omega) (fun _ h => h)
  obtain ⟨rb, b0, b5, bk⟩ := hb
  have hkl : (a.kin ++ dbl x).length = a.kin.length + 2 * x.length := by rw [List.length_append, dbl_length]
  refine Hs.op (OpEx.kem false b (by rw [bk, List.take_length, hkl]; omega)) ⟨relKin rb _, ?_⟩
  show b.kin ++ [false] = _
  rw [bk, List.take_length, frame_dbl]; simp

/-- **The cons call**: `kin := false :: frame x ++ frame y` from `20, 21, 22, 23`, then `kcall`. -/
def callCons : St VV MM := .seq (.op (.kem false)) (.seq (kemFrame 20 21) (.seq (kemFrame 22 23) (.op .kcall)))

/-- The cost bound of `callCons`. -/
def callConsCost (C : Ctx) (nx ny : ℕ) : ℕ := 12 * nx + 12 * ny + C.Lk + C.Bk + 40

theorem callCons_spec (C : Ctx) (G : Glob) (s : FS) (a : DS VV MM) (r : Rel G s a) (hk : a.kin = [])
    (x y : List Bool) (hx1 : s.env 20 = CanonicalBinary.bitsValue x) (hx2 : s.env 21 = x.length)
    (hy1 : s.env 22 = CanonicalBinary.bitsValue y) (hy2 : s.env 23 = y.length)
    (q : C.K.Req) (hin : C.K.inw q = false :: (frame x ++ frame y)) (hbud : C.K.bud q ≤ C.Bk)
    (hLk : 2 * x.length + 2 * y.length + 3 < C.Lk) (hW : x.length + y.length + 4 < 2 ^ C.Wd) :
    Hs C callCons a (callConsCost C x.length y.length) (fun b => Rel G s b ∧ b = { b with kin := [] } ∧
      b.kout = C.K.outw q ∧ b.kc = 0) := by
  refine hs_step (OpEx.kem false a (by rw [hk]; simp; omega)) ?_
  have r1 : Rel G s { a with kin := a.kin ++ [false] } := relKin r _
  refine Hs.mono (Hs.seq (t2 := 12 * y.length + 10 + (1 + C.Lk + C.Bk) + 1)
    (kemFrame_spec C G s _ r1 20 21 x hx1 hx2 (by simp [hk]; omega) (by omega)) (fun b ⟨rb, bk⟩ => ?_))
    (by omega) (fun _ h => h)
  have hbk : b.kin.length = 1 + (2 * x.length + 1) := by rw [bk]; simp [hk, FL.frame_len]; omega
  refine Hs.seq (kemFrame_spec C G s b rb 22 23 y hy1 hy2 (by rw [hbk]; omega) (by omega)) (fun c ⟨rc, ck⟩ => ?_)
  refine Hs.op (OpEx.kcall q c (by rw [ck, bk, hin, hk]; simp) hbud) ⟨relCalled rc _, rfl, rfl, rfl⟩

/-! ## Copying the callee's framed output into the output -/

/-- `rdK`; while the marker is `1`: read the bit, emit `1 b`, read the next marker. -/
def copyOut : St VV MM :=
  .seq (.op (.rdK g4)) (.loop (.eq g4 r1) (.seq (.op (.rdK g4)) (.seq (.op (.emit true))
    (.seq (.ite (.eq g4 r1) (.op (.emit true)) (.op (.emit false))) (.op (.rdK g4))))))

theorem bitOf_frame_even (u : List Bool) (k : ℕ) : bitOf (frame u) (2 * k) = (decide (k < u.length)).toNat := by
  unfold bitOf; rw [FL.frame_getD_even]

theorem bitOf_frame_odd (u : List Bool) (k : ℕ) (hk : k < u.length) :
    bitOf (frame u) (2 * k + 1) = (u.getD k false).toNat := by
  unfold bitOf; rw [FL.frame_getD_odd u k hk]

theorem copyOut_spec (C : Ctx) (G : Glob) (s : FS) (a : DS VV MM) (r : Rel G s a) (u : List Bool)
    (ho : a.kout = frame u) (hc : a.kc = 0) :
    Hs C copyOut a (10 * u.length + 4) (fun b => Rel G { s with out := s.out ++ dbl u } b ∧ b.kin = a.kin) := by
  have hfl : (frame u).length = 2 * u.length + 1 := FL.frame_len u
  refine hs_step (OpEx.rdK g4 a (by rw [hc, ho, hfl]; omega)) ?_
  set a1 := ({ a.set g4 (bitOf a.kout a.kc) with kc := a.kc + 1 } : DS VV MM)
  let I : ℕ → DS VV MM → Prop := fun j b => Rel G { s with out := s.out ++ dbl (u.take j) } b ∧ b.kc = 2 * j + 1 ∧
    b.kout = frame u ∧ b.env g4 = (decide (j < u.length)).toNat ∧ b.kin = a.kin
  have hs0 : ({ s with out := s.out ++ dbl (u.take 0) } : FS) = s := by cases s; simp [dbl]
  have hI0 : I 0 a1 := ⟨by rw [hs0]; exact relKc r g4 (bitOf a.kout a.kc) (a.kc + 1) (by decide) (by decide),
    by simp [a1, hc], by simp [a1, ho], by simp [a1, ho, hc]; exact bitOf_frame_even u 0, by simp [a1]⟩
  have hbody : ∀ j < u.length, ∀ b, I j b → (Cnd.eq g4 r1).eval b = true ∧
      Hs C (.seq (.op (.rdK g4)) (.seq (.op (.emit true)) (.seq (.ite (.eq g4 r1) (.op (.emit true))
        (.op (.emit false))) (.op (.rdK g4))))) b 8 (I (j + 1)) := by
    rintro j hj b ⟨rb, bc, bo, b4, bk⟩
    refine ⟨by simp only [Cnd.eval, b4, rb.env.c1, decide_eq_true_eq]; simp [hj], ?_⟩
    refine hs_step (OpEx.rdK g4 b (by rw [bc, bo, hfl]; omega)) ?_
    set c := ({ b.set g4 (bitOf b.kout b.kc) with kc := b.kc + 1 } : DS VV MM)
    have rc : Rel G { s with out := s.out ++ dbl (u.take j) } c := relKc rb g4 _ _ (by decide) (by decide)
    have c4 : c.env g4 = (u.getD j false).toNat := by
      simp only [c, DS.set_env_self]; rw [bo, bc]; exact bitOf_frame_odd u j hj
    have c0 : c.kc = 2 * j + 2 := by simp [c, bc]
    have cko : c.kout = frame u := by simp [c, bo]
    have ckin : c.kin = a.kin := by simp [c, bk]
    refine hs_step (OpEx.emit true c) ?_
    set c1 := ({ c with out := c.out ++ [true] } : DS VV MM)
    have rc1 := relEmit rc true
    have c14 : c1.env g4 = (u.getD j false).toNat := c4
    have hite : Hs C (.ite (.eq g4 r1) (.op (.emit true)) (.op (.emit false))) c1 2 (fun e =>
        Rel G { s with out := s.out ++ dbl (u.take (j + 1)) } e ∧ e.env = c1.env ∧ e.kc = c1.kc ∧ e.kout = c1.kout ∧
          e.kin = c1.kin) := by
      have hfs : ∀ v : Bool, v = u.getD j false →
          ({ ({ s with out := s.out ++ dbl (u.take j) } : FS) with out := (s.out ++ dbl (u.take j)) ++ [true] ++ [v] } : FS)
            = { s with out := s.out ++ dbl (u.take (j + 1)) } := by
        intro v hv; rw [dbl_take_succ u j hj, ← hv]; simp
      refine Hs.ite (show g4 ≠ r1 by decide) (fun he => ?_) (fun he => ?_)
      · have hb : u.getD j false = true := by
          have h1 : (u.getD j false).toNat = 1 := by
            have := rc1.env.c1; simp only [Cnd.eval, decide_eq_true_eq] at he; rw [← c14, he]; exact this
          revert h1; cases u.getD j false <;> simp
        refine Hs.op (OpEx.emit true c1) ⟨?_, rfl, rfl, rfl, rfl⟩
        have := relEmit rc1 true
        rw [← hfs true hb.symm]; exact this
      · have hb : u.getD j false = false := by
          have h1 : (u.getD j false).toNat ≠ 1 := by
            have := rc1.env.c1; simp only [Cnd.eval, decide_eq_false_iff_not] at he; rw [← c14]; rwa [this] at he
          revert h1; cases u.getD j false <;> simp
        refine Hs.op (OpEx.emit false c1) ⟨?_, rfl, rfl, rfl, rfl⟩
        have := relEmit rc1 false
        rw [← hfs false hb.symm]; exact this
    refine Hs.mono (Hs.seq (t2 := 1) hite (fun e ⟨re, ee, ec, eo, ek⟩ => ?_)) (by omega) (fun _ h => h)
    have ec' : e.kc = 2 * (j + 1) := by rw [ec]; show c.kc = _; rw [c0]; ring
    have eo' : e.kout = frame u := by rw [eo]; exact cko
    refine Hs.op (OpEx.rdK g4 e (by rw [ec', eo', hfl]; omega)) ⟨relKc re g4 _ _ (by decide) (by decide), ?_, ?_, ?_, ?_⟩
    · simp [ec']
    · simp [eo']
    · simp only [DS.set_env_self]; rw [eo', ec']; exact bitOf_frame_even u (j + 1)
    · simp [ek]; exact ckin
  refine Hs.mono (Hs.loopN (c := .eq g4 r1) (show g4 ≠ r1 by decide) I u.length 8 hbody
    (fun b ⟨rb, _, _, b4, _⟩ => by simp [Cnd.eval, b4, rb.env.c1]) a1 hI0) (by omega)
    (fun b ⟨rb, _, _, _, bk⟩ => ⟨by rw [List.take_length] at rb; exact rb, bk⟩)

end NearCubicGates.Adapters.RAMACSP.Gen
