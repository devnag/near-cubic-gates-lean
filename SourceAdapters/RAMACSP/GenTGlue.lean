import SourceAdapters.RAMACSP.GenGlue

/-!
# The term printer's calls: cell glue (G5)

Paper: `lem:generator`. The term printer composes the coordinate array,
neighbor bank, routing items and machine items into the literal input of the
constraint-circuit printer.

The callee of the term printer is `sumWF Shoup (sumWF coordinates items)`:
- `kemNat vX vL`: append `natWord v` to `kin` (`v` in program variable `vX`, `natBitLength v` in `vL`);
- `callCoord`: `kin := false :: true :: natWord f ++ natWord irr ++ natWord m` from the program variables
  `36, 37, 35` (lengths in `41, 42, 43`), then `kcall` (`callCoord_spec`);
- `callItems`: `kin := false :: false :: frame x ++ frame y` from `20 … 23`, then `kcall` (`callItems_spec`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace NearCubicGates.Adapters.RAMACSP.Gen

open NearCubicGates.Close.Cells NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Adapters.ShortPCP NearCubicGates.Adapters.ShortPCP.Machines
open NearCubicGates.Adapters.ShortPCP.Machines.FL
open NearCubicGates.Adapters.Joins.FieldCells (vr)
open NearCubicWires.RepairRepresentation (natWord)

/-- Append `natWord v` to `kin` (`v` in `vX`, its length `natBitLength v` in `vL`): `1^L 0`, then the `L` bits of `v`,
least significant first. -/
def kemNat (vX vL : Var) : St VV MM :=
  .seq (.seq (.op (.zero g0)) (.loop (.lt g0 (FL.uv vL)) (.seq (.op (.kem true)) (.op (.inc g0)))))
  (.seq (.op (.kem false)) (.seq (.op (.copy g5 (FL.uv vX))) (.seq (.op (.zero g0))
  (.loop (.lt g0 (FL.uv vL)) (.seq (.op (.dm g5 r2 g6 g4)) (.seq (.ite (.eq g4 r1) (.op (.kem true))
    (.op (.kem false))) (.seq (.op (.copy g5 g6)) (.op (.inc g0)))))))))

theorem natWord_bits_take (v L j : ℕ) (hj : j < L) :
    (List.range (j + 1)).map (fun i => v / 2 ^ i % 2 == 1) =
      (List.range j).map (fun i => v / 2 ^ i % 2 == 1) ++ [v / 2 ^ j % 2 == 1] := by
  rw [List.range_succ, List.map_append]; rfl

/-- The unary part: `1^L` appended to `kin` (`L` in `vL`). -/
theorem kemUnary_spec (C : Ctx) (G : Glob) (s : FS) (a : DS VV MM) (r : Rel G s a) (vL : Var) (L : ℕ)
    (hL : s.env vL = L) (hLk : a.kin.length + L < C.Lk) (hW : L + 1 < 2 ^ C.Wd) :
    Hs C (.seq (.op (.zero g0)) (.loop (.lt g0 (FL.uv vL)) (.seq (.op (.kem true)) (.op (.inc g0))))) a
      (5 * L + 4) (fun b => Rel G s b ∧ b.kin = a.kin ++ List.replicate L true) := by
  have hwf : (Cnd.lt g0 (FL.uv vL)).wf := g_ne_uv vL (Or.inl rfl)
  let I1 : ℕ → DS VV MM → Prop := fun j b => Rel G s b ∧ b.env g0 = j ∧ b.kin = a.kin ++ List.replicate j true
  have hI0 : I1 0 (a.set g0 0) := ⟨relSetg r g0 0, by simp, by simp⟩
  refine Hs.mono (Hs.seq (Hs.op (R := fun b => b = a.set g0 0) (OpEx.zero g0 a) rfl) (fun b hb => hb ▸
    Hs.loopN (c := .lt g0 (FL.uv vL)) hwf I1 L 3 (fun j hj b ⟨rb, b0, bk⟩ => ⟨?_, ?_⟩)
    (fun b ⟨rb, b0, bk⟩ => ?_) _ hI0)) (by omega) (fun b ⟨rb, _, bk⟩ => ⟨rb, bk⟩)
  · simp only [Cnd.eval, b0, (rb.uv vL).trans hL, decide_eq_true_eq]; exact hj
  · have hkl : b.kin.length < C.Lk := by rw [bk]; simp; omega
    refine hs_step (OpEx.kem true b hkl) ?_
    refine Hs.op (OpEx.inc g0 _ (by show b.env g0 + 1 < _; rw [b0]; omega)) ?_
    refine ⟨relSetg (relKin rb _) g0 _, by rw [DS.set_env_self]; show b.env g0 + 1 = j + 1; rw [b0], ?_⟩
    show b.kin ++ [true] = _; rw [bk, List.replicate_succ', List.append_assoc]
  · simp only [Cnd.eval, b0, (rb.uv vL).trans hL, decide_eq_false_iff_not]; omega

/-- The bits: the `L` low bits of `v` (in `vX`), least significant first, appended to `kin`. -/
theorem kemBits_spec (C : Ctx) (G : Glob) (s : FS) (a : DS VV MM) (r : Rel G s a) (vX vL : Var) (v L : ℕ)
    (hX : s.env vX = v) (hL : s.env vL = L) (hLk : a.kin.length + L < C.Lk) (hW : L + 4 < 2 ^ C.Wd) :
    Hs C (.seq (.op (.copy g5 (FL.uv vX))) (.seq (.op (.zero g0))
      (.loop (.lt g0 (FL.uv vL)) (.seq (.op (.dm g5 r2 g6 g4)) (.seq (.ite (.eq g4 r1) (.op (.kem true))
        (.op (.kem false))) (.seq (.op (.copy g5 g6)) (.op (.inc g0)))))))) a (10 * L + 8)
      (fun b => Rel G s b ∧ b.kin = a.kin ++ (List.range L).map (fun i => v / 2 ^ i % 2 == 1)) := by
  have hwf : (Cnd.lt g0 (FL.uv vL)).wf := g_ne_uv vL (Or.inl rfl)
  have hXa : a.env (FL.uv vX) = v := (r.uv vX).trans hX
  refine hs_step (OpEx.copy g5 (FL.uv vX) a (g_ne_uv vX (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))) ?_
  refine hs_step (OpEx.zero g0 _) ?_
  set a2 := (a.set g5 (a.env (FL.uv vX))).set g0 0 with ha2
  have ra2 : Rel G s a2 := relSetg (relSetg r g5 _) g0 _
  let I : ℕ → DS VV MM → Prop := fun j b => Rel G s b ∧ b.env g0 = j ∧ b.env g5 = v / 2 ^ j ∧
    b.kin = a.kin ++ (List.range j).map (fun i => v / 2 ^ i % 2 == 1)
  have hI0' : I 0 a2 := ⟨ra2, by simp [a2], by simp [a2, DS.set_env_ne _ _ (show g5 ≠ g0 by decide), hXa],
    by simp [a2]⟩
  have hbody : ∀ j < L, ∀ b, I j b → (Cnd.lt g0 (FL.uv vL)).eval b = true ∧
      Hs C (.seq (.op (.dm g5 r2 g6 g4)) (.seq (.ite (.eq g4 r1) (.op (.kem true))
        (.op (.kem false))) (.seq (.op (.copy g5 g6)) (.op (.inc g0))))) b 8 (I (j + 1)) := by
    rintro j hj b ⟨rb, b0, b5, bk⟩
    refine ⟨by simp only [Cnd.eval, b0, (rb.uv vL).trans hL, decide_eq_true_eq]; exact hj, ?_⟩
    have hkl : (a.kin ++ (List.range j).map (fun i => v / 2 ^ i % 2 == 1)).length = a.kin.length + j := by simp
    have hW4 : 2 * 2 ≤ 2 ^ C.Wd := by omega
    refine hs_step (OpEx.dm g5 r2 g6 g4 b (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by rw [rb.env.c2]; omega) (by rw [rb.env.c2]; exact hW4)) ?_
    set d := (b.set g6 (b.env g5 / b.env r2)).set g4 (b.env g5 % b.env r2) with hd
    have rd : Rel G s d := relSetg (relSetg rb g6 _) g4 _
    have c2 : b.env r2 = 2 := rb.env.c2
    have d4 : d.env g4 = v / 2 ^ j % 2 := by simp only [d, DS.set_env_self, b5, c2]
    have d6 : d.env g6 = v / 2 ^ (j + 1) := by
      simp only [d, DS.set_env_ne _ _ (show g6 ≠ g4 by decide), DS.set_env_self, b5, c2, pow_succ,
        Nat.div_div_eq_div_mul]
    have d0 : d.env g0 = j := by
      simp only [d, DS.set_env_ne _ _ (show g0 ≠ g4 by decide), DS.set_env_ne _ _ (show g0 ≠ g6 by decide)]; exact b0
    have dk : d.kin = a.kin ++ (List.range j).map (fun i => v / 2 ^ i % 2 == 1) := by simp [d, bk]
    have hite : Hs C (.ite (.eq g4 r1) (.op (.kem true)) (.op (.kem false))) d 2 (fun e => Rel G s e ∧
        e.env = d.env ∧ e.kin = a.kin ++ (List.range (j + 1)).map (fun i => v / 2 ^ i % 2 == 1)) := by
      have hkl' : d.kin.length < C.Lk := by rw [dk, hkl]; omega
      rw [natWord_bits_take v L j hj]
      refine Hs.ite (show g4 ≠ r1 by decide) (fun he => ?_) (fun he => ?_)
      · have hb : (v / 2 ^ j % 2 == 1) = true := by
          simp only [Cnd.eval, d4, rd.env.c1, decide_eq_true_eq] at he; simp [he]
        refine Hs.op (OpEx.kem true d hkl') ⟨relKin rd _, rfl, ?_⟩
        show d.kin ++ [true] = _; rw [dk, hb]; simp
      · have hb : (v / 2 ^ j % 2 == 1) = false := by
          simp only [Cnd.eval, d4, rd.env.c1, decide_eq_false_iff_not] at he
          have := Nat.mod_two_eq_zero_or_one (v / 2 ^ j); simp; omega
        refine Hs.op (OpEx.kem false d hkl') ⟨relKin rd _, rfl, ?_⟩
        show d.kin ++ [false] = _; rw [dk, hb]; simp
    refine Hs.mono (Hs.seq (t2 := 3) hite (fun e ⟨re, ee, ek⟩ => ?_)) (by omega) (fun _ h => h)
    have e6 : e.env g6 = v / 2 ^ (j + 1) := by rw [ee, d6]
    have e0 : e.env g0 = j := by rw [ee, d0]
    refine hs_step (OpEx.copy g5 g6 e (by decide)) ?_
    refine Hs.op (OpEx.inc g0 _ (by rw [DS.set_env_ne _ _ (show g0 ≠ g5 by decide), e0]; omega)) ?_
    refine ⟨relSetg (relSetg re g5 _) g0 _,
      by simp [DS.set_env_ne _ _ (show g0 ≠ g5 by decide), e0], ?_, by simp [ek]⟩
    simp [DS.set_env_ne _ _ (show g5 ≠ g0 by decide), e6]
  refine Hs.mono (Hs.loopN (c := .lt g0 (FL.uv vL)) hwf I L 8 hbody
    (fun b ⟨rb, b0, _, _⟩ => by simp only [Cnd.eval, b0, (rb.uv vL).trans hL, decide_eq_false_iff_not]; omega) a2 hI0')
    (by omega) (fun b ⟨rb, _, _, bk⟩ => ⟨rb, bk⟩)

theorem kemNat_spec (C : Ctx) (G : Glob) (s : FS) (a : DS VV MM) (r : Rel G s a) (vX vL : Var) (v : ℕ)
    (hX : s.env vX = v) (hL : s.env vL = natBitLength v)
    (hLk : a.kin.length + 2 * natBitLength v + 1 < C.Lk) (hW : natBitLength v + 4 < 2 ^ C.Wd) :
    Hs C (kemNat vX vL) a (16 * natBitLength v + 16) (fun b => Rel G s b ∧ b.kin = a.kin ++ natWord v) := by
  set L := natBitLength v with hLdef
  unfold kemNat
  refine Hs.mono (Hs.seq (t2 := 1 + (10 * L + 8) + 1) (kemUnary_spec C G s a r vL L hL (by omega) (by omega))
    (fun b ⟨rb, bk⟩ => ?_)) (by omega) (fun _ h => h)
  have hkb : b.kin.length < C.Lk := by rw [bk]; simp; omega
  refine Hs.seq (Hs.op (R := fun c => c = { b with kin := b.kin ++ [false] }) (OpEx.kem false b hkb) rfl)
    (fun c hc => ?_)
  subst hc
  refine Hs.mono (kemBits_spec C G s _ (relKin rb _) vX vL v L hX hL (by simp [bk]; omega) (by omega)) le_rfl
    (fun d ⟨rd, dk⟩ => ⟨rd, ?_⟩)
  rw [dk, bk, natWord_eq_bits, ← hLdef]; simp

/-! ## The coordinate call -/

/-- **The coordinate call**: `kin := false :: true :: natWord f ++ natWord irr ++ natWord m` from `36, 37, 35` (lengths in
`41, 42, 43`), then `kcall`. -/
def callCoord : St VV MM :=
  .seq (.op (.kem false)) (.seq (.op (.kem true)) (.seq (kemNat 36 41) (.seq (kemNat 37 42) (.seq (kemNat 35 43)
    (.op .kcall)))))

/-- The cost bound of `callCoord`. -/
def callCoordCost (C : Ctx) (f i m : ℕ) : ℕ :=
  16 * natBitLength f + 16 * natBitLength i + 16 * natBitLength m + C.Lk + C.Bk + 70

theorem callCoord_spec (C : Ctx) (G : Glob) (s : FS) (a : DS VV MM) (r : Rel G s a) (hk : a.kin = [])
    (f i m : ℕ) (hf : s.env 36 = f) (hi : s.env 37 = i) (hm : s.env 35 = m) (hf' : s.env 41 = natBitLength f)
    (hi' : s.env 42 = natBitLength i) (hm' : s.env 43 = natBitLength m)
    (q : C.K.Req) (hin : C.K.inw q = false :: true :: (natWord f ++ natWord i ++ natWord m)) (hbud : C.K.bud q ≤ C.Bk)
    (hLk : 2 * natBitLength f + 2 * natBitLength i + 2 * natBitLength m + 6 < C.Lk)
    (hW : natBitLength f + natBitLength i + natBitLength m + 4 < 2 ^ C.Wd) :
    Hs C callCoord a (callCoordCost C f i m) (fun b => Rel G s b ∧ b = { b with kin := [] } ∧
      b.kout = C.K.outw q ∧ b.kc = 0) := by
  have nwl : ∀ v, (natWord v).length = 2 * natBitLength v + 1 := FL.natWord_len
  refine hs_step (OpEx.kem false a (by rw [hk]; simp; omega)) ?_
  have r1 : Rel G s { a with kin := a.kin ++ [false] } := relKin r _
  refine hs_step (OpEx.kem true _ (by simp [hk]; omega)) ?_
  set a2 := ({ ({ a with kin := a.kin ++ [false] } : DS VV MM) with
    kin := ({ a with kin := a.kin ++ [false] } : DS VV MM).kin ++ [true] } : DS VV MM) with ha2
  have r2' : Rel G s a2 := relKin r1 _
  have k2 : a2.kin = [false, true] := by simp [a2, hk]
  refine Hs.mono (Hs.seq (t2 := 16 * natBitLength i + 16 + (16 * natBitLength m + 16 + (1 + C.Lk + C.Bk) + 1) + 1)
    (kemNat_spec C G s a2 r2' 36 41 f hf hf' (by rw [k2]; simp; omega) (by omega)) (fun b ⟨rb, bk⟩ => ?_))
    (by omega) (fun _ h => h)
  refine Hs.seq (t2 := 16 * natBitLength m + 16 + (1 + C.Lk + C.Bk) + 1)
    (kemNat_spec C G s b rb 37 42 i hi hi' (by rw [bk, k2]; simp [nwl]; omega) (by omega)) (fun c ⟨rc, ck⟩ => ?_)
  refine Hs.seq (kemNat_spec C G s c rc 35 43 m hm hm' (by rw [ck, bk, k2]; simp [nwl]; omega) (by omega))
    (fun d ⟨rd, dk⟩ => ?_)
  refine Hs.op (OpEx.kcall q d (by rw [dk, ck, bk, k2, hin]; simp) hbud) ⟨relCalled rd _, rfl, rfl, rfl⟩

/-! ## The items call -/

/-- **The items call**: `kin := false :: false :: frame x ++ frame y` from `20, 21, 22, 23`, then `kcall`. -/
def callItems : St VV MM :=
  .seq (.op (.kem false)) (.seq (.op (.kem false)) (.seq (kemFrame 20 21) (.seq (kemFrame 22 23) (.op .kcall))))

/-- The cost bound of `callItems`. -/
def callItemsCost (C : Ctx) (nx ny : ℕ) : ℕ := 12 * nx + 12 * ny + C.Lk + C.Bk + 40

theorem callItems_spec (C : Ctx) (G : Glob) (s : FS) (a : DS VV MM) (r : Rel G s a) (hk : a.kin = [])
    (x y : List Bool) (hx1 : s.env 20 = CanonicalBinary.bitsValue x) (hx2 : s.env 21 = x.length)
    (hy1 : s.env 22 = CanonicalBinary.bitsValue y) (hy2 : s.env 23 = y.length)
    (q : C.K.Req) (hin : C.K.inw q = false :: false :: (frame x ++ frame y)) (hbud : C.K.bud q ≤ C.Bk)
    (hLk : 2 * x.length + 2 * y.length + 4 < C.Lk) (hW : x.length + y.length + 4 < 2 ^ C.Wd) :
    Hs C callItems a (callItemsCost C x.length y.length) (fun b => Rel G s b ∧ b = { b with kin := [] } ∧
      b.kout = C.K.outw q ∧ b.kc = 0) := by
  refine hs_step (OpEx.kem false a (by rw [hk]; simp; omega)) ?_
  have r1 : Rel G s { a with kin := a.kin ++ [false] } := relKin r _
  refine hs_step (OpEx.kem false _ (by simp [hk]; omega)) ?_
  set a2 := ({ ({ a with kin := a.kin ++ [false] } : DS VV MM) with
    kin := ({ a with kin := a.kin ++ [false] } : DS VV MM).kin ++ [false] } : DS VV MM) with ha2
  have r2' : Rel G s a2 := relKin r1 _
  have k2 : a2.kin = [false, false] := by simp [a2, hk]
  refine Hs.mono (Hs.seq (t2 := 12 * y.length + 10 + (1 + C.Lk + C.Bk) + 1)
    (kemFrame_spec C G s a2 r2' 20 21 x hx1 hx2 (by rw [k2]; simp; omega) (by omega)) (fun b ⟨rb, bk⟩ => ?_))
    (by omega) (fun _ h => h)
  have hbk : b.kin.length = 2 + (2 * x.length + 1) := by rw [bk, k2]; simp [FL.frame_len]; omega
  refine Hs.seq (kemFrame_spec C G s b rb 22 23 y hy1 hy2 (by rw [hbk]; omega) (by omega)) (fun c ⟨rc, ck⟩ => ?_)
  refine Hs.op (OpEx.kcall q c (by rw [ck, bk, k2, hin]; simp) hbud) ⟨relCalled rc _, rfl, rfl, rfl⟩

end NearCubicGates.Adapters.RAMACSP.Gen
