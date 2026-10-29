import SourceAdapters.Amplification.EncParse

/-!
# The parameters of the rounded STV code, computed in the cell language (`app:sources`, "Full-range amplification interface")

From `k` (variable `vK`) and `n` (`vN`): `h = k + 2 + size n`, `m = ⌈n/h⌉`, `t = h + 6k + 12 + size m + size C`,
`ℓ = (m+1)·t` (`Layout.lean`: `hParam`, `mParam`, `tParam`, `arityParam`), and the powers `2^t`, `2^h`, `2^n`,
`2^ℓ`, `2^t − 2` (`paramsP`); then the framed arity `frame (binary ℓ)` is written (`emitFrameP`).
-/

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Adapters.Amplification.Enc

open NearCubicGates.Close.Cells NearCubicWires NearCubicWires.RepairOrdinary

abbrev vK : Var := 14
abbrev vSX : Var := 86
abbrev vSS : Var := 87
abbrev vEE : Var := 88
abbrev vPD : Var := 89
abbrev vEJ : Var := 90
abbrev vT1 : Var := 91
abbrev vT2 : Var := 92

/-! ## Binary length -/

def sizeS : List Var := [vSX, vSS]

def sizeP : Sc := .seq (.op (.zero vSS)) (.loop (.lt vZ vSX) (.seq (.op (.half vSX)) (.op (.inc vSS))))

theorem sizeP_spec (C : Ctx) (a : Ds) (hc : Consts a) (x : ℕ) (hx : a.env vSX = x) (hW : x < 2 ^ C.Wd) :
    Runs C sizeP a (x.size * 5 + 4) sizeS [] (fun b => b.env vSS = x.size) := by
  have hsz : x.size ≤ x := by
    rcases Nat.eq_zero_or_pos x with rfl | hx0
    · simp
    · exact Nat.size_le.mpr (Nat.lt_two_pow_self)
  refine Runs.op1 (run_zero C sizeS a vSS (by decide)) ?_ (by omega)
  refine (Runs.loopN0 (C := C) (c := .lt vZ vSX) (body := .seq (.op (.half vSX)) (.op (.inc vSS))) (S := sizeS)
    (by unfold Cnd.wf; decide) x.size 3 (fun j b => Fr sizeS [] (a.set vSS 0) b ∧ b.env vSX = x / 2 ^ j ∧
      b.env vSS = j) ?step ?stop _ ?init).mono (by omega) (List.Subset.refl _) ?post
  case post => rintro b - ⟨-, -, h⟩; exact h
  case init => exact ⟨Fr.refl _ _, by simp (config := { decide := true }) [env_set, hx], by simp [env_set]⟩
  case stop =>
    rintro b ⟨hf, hX, -⟩
    have hz : b.env vZ = 0 := (hf.env vZ (by decide)).trans (by simp [env_set, hc.1])
    simp [Cnd.eval, hX, hz, Nat.div_eq_of_lt (Nat.lt_size_self x)]
  case step =>
    rintro j hj b ⟨hf, hX, hS⟩
    have hz : b.env vZ = 0 := (hf.env vZ (by decide)).trans (by simp [env_set, hc.1])
    have hpos : 0 < x / 2 ^ j := Nat.div_pos (Nat.lt_size.mp hj) (Nat.two_pow_pos j)
    refine ⟨by simp [Cnd.eval, hX, hz, hpos], ?_⟩
    refine Runs.op1 (run_half C sizeS b vSX (by decide)) ?_ (by omega)
    refine Runs.last (run_inc C sizeS _ vSS (by decide) (by norm_env; rw [hS]; omega)) ?_ (by omega)
    intro _
    refine ⟨(hf.set_right _ _ (by decide)).set_right _ _ (by decide), ?_, ?_⟩ <;> norm_env
    · rw [hX, Nat.div_div_eq_div_mul, ← pow_succ]
    · rw [hS]

/-! ## Powers of two -/

def pow2S : List Var := [vPD, vEJ]

def pow2P : Sc :=
  .seq (.op (.copy vPD vONE)) <| .seq (.op (.zero vEJ)) <| .loop (.lt vEJ vEE) (.seq (.op (.shl vPD)) (.op (.inc vEJ)))

theorem pow2P_spec (C : Ctx) (a : Ds) (hc : Consts a) (e : ℕ) (he : a.env vEE = e) (hW : e + 1 < C.Wd) :
    Runs C pow2P a (e * 5 + 6) pow2S [] (fun b => b.env vPD = 2 ^ e) := by
  have hpw : ∀ j ≤ e, 2 * 2 ^ j < 2 ^ C.Wd := fun j hj => by
    rw [← pow_succ']; exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  refine Runs.op1 (run_copy C pow2S a vPD vONE (by decide) (by decide)) ?_ (by omega)
  refine Runs.op1 (run_zero C pow2S _ vEJ (by decide)) ?_ (by omega)
  refine (Runs.loopN0 (C := C) (c := .lt vEJ vEE) (body := .seq (.op (.shl vPD)) (.op (.inc vEJ))) (S := pow2S)
    (by unfold Cnd.wf; decide) e 3 (fun j b => Fr pow2S [] a b ∧ b.env vPD = 2 ^ j ∧ b.env vEJ = j) ?step ?stop _
    ?init).mono (by omega) (List.Subset.refl _) ?post
  case post => rintro b - ⟨-, h, -⟩; exact h
  case init =>
    refine ⟨((Fr.refl _ _).set_right _ _ (by decide)).set_right _ _ (by decide), ?_, ?_⟩ <;> norm_env
    · simp [hc.2.1]
  case stop =>
    rintro b ⟨hf, -, hJ⟩
    simp [Cnd.eval, hJ, (hf.env vEE (by decide)).trans he]
  case step =>
    rintro j hj b ⟨hf, hD, hJ⟩
    refine ⟨by simp [Cnd.eval, hJ, (hf.env vEE (by decide)).trans he, hj], ?_⟩
    refine Runs.op1 (run_shl C pow2S b vPD (by decide) (by rw [hD]; exact hpw j hj.le)) ?_ (by omega)
    refine Runs.last (run_inc C pow2S _ vEJ (by decide) (by norm_env; rw [hJ]; have := hpw j hj.le; have := Nat.lt_two_pow_self (n := j); omega)) ?_
      (by omega)
    intro _
    refine ⟨(hf.set_right _ _ (by decide)).set_right _ _ (by decide), ?_, ?_⟩ <;> norm_env
    · rw [hD, pow_succ]; ring
    · rw [hJ]

/-! ## Constants by unary increments -/

/-- `x := x + c` by `c` increments (the scratch `vT2` is zeroed when `c = 0`). -/
def incN (x : Var) : ℕ → Sc
  | 0 => .op (.zero vT2)
  | c + 1 => .seq (.op (.inc x)) (incN x c)

theorem incN_spec (C : Ctx) (x : Var) (hx : x ≠ vT2) (S : List Var) (hxS : x ∈ S) (hT : vT2 ∈ S) :
    ∀ (c : ℕ) (a : Ds), a.env x + c < 2 ^ C.Wd →
      Runs C (incN x c) a (2 * c + 1) S [] (fun b => b.env x = a.env x + c) := by
  intro c
  induction c with
  | zero =>
    intro a _
    exact (run_zero C S a vT2 hT).mono le_rfl (List.Subset.refl _) (by rintro b - rfl; simp [env_set, hx])
  | succ c ih =>
    intro a hlt
    refine Runs.op1 (run_inc C S a x hxS (by omega)) ?_ (by omega)
    refine ((ih _ (by simp [env_set]; omega)).mono (by omega) (List.Subset.refl _) ?_)
    rintro b - hb; rw [hb]; simp [env_set]; ring

/-! ## The parameters -/

def paramsS : List Var :=
  [vH, vT1, vT2, vM, vT, vTB, vL, vPOWT, vPOWH, vPOWN, vPOWL, vEXP, vSX, vSS, vPD, vEJ, vEE]

/-- `h` and `m`. -/
def params1 : Sc :=
  .seq (.op (.copy vSX vN)) <| .seq sizeP <| .seq (.op (.copy vH vK)) <| .seq (.op (.add vH vTWO)) <|
  .seq (.op (.add vH vSS)) <| .seq (.op (.copy vT1 vN)) <| .seq (.op (.add vT1 vH)) <| .seq (.op (.sub vT1 vONE)) <|
  .op (.dm vT1 vH vM vT2)

theorem params1_spec (C : Ctx) (a : Ds) (hc : Consts a) (n k : ℕ) (hn : a.env vN = n) (hk : a.env vK = k)
    (hW : 2 * (n + k + 3) < 2 ^ C.Wd) :
    Runs C params1 a (n * 5 + 30) paramsS [] (fun b => b.env vH = hParam n k ∧ b.env vM = mParam n k) := by
  have hsn : n.size ≤ n := by
    rcases Nat.eq_zero_or_pos n with rfl | h0
    · simp
    · exact Nat.size_le.mpr Nat.lt_two_pow_self
  refine Runs.op1 (run_copy C paramsS a vSX vN (by decide) (by decide)) ?_ (by omega)
  refine Runs.callS (sizeP_spec C _ ⟨by norm_env; exact hc.1, by norm_env; exact hc.2.1, by norm_env; exact hc.2.2⟩
    n (by norm_env; exact hn) (by omega)) (by decide) ?_ (by omega)
  intro b hb hbS
  have hbc : Consts b := ⟨by rw [hb.env _ (by decide)]; norm_env; exact hc.1,
    by rw [hb.env _ (by decide)]; norm_env; exact hc.2.1, by rw [hb.env _ (by decide)]; norm_env; exact hc.2.2⟩
  have hbn : b.env vN = n := by rw [hb.env _ (by decide)]; norm_env; exact hn
  have hbk : b.env vK = k := by rw [hb.env _ (by decide)]; norm_env; exact hk
  refine Runs.op1 (run_copy C paramsS b vH vK (by decide) (by decide)) ?_ (by omega)
  refine Runs.op1 (run_add C paramsS _ vH vTWO (by decide) (by decide) (by norm_env; simp only [hbk, hbc.2.2, hbS, hbn, hbc.2.1]; omega))
    ?_ (by omega)
  refine Runs.op1 (run_add C paramsS _ vH vSS (by decide) (by decide)
    (by norm_env; simp only [hbk, hbc.2.2, hbS, hbn, hbc.2.1]; omega)) ?_ (by omega)
  refine Runs.op1 (run_copy C paramsS _ vT1 vN (by decide) (by decide)) ?_ (by omega)
  refine Runs.op1 (run_add C paramsS _ vT1 vH (by decide) (by decide)
    (by norm_env; simp only [hbk, hbc.2.2, hbS, hbn, hbc.2.1]; omega)) ?_ (by omega)
  refine Runs.op1 (run_sub C paramsS _ vT1 vONE (by decide) (by decide)
    (by norm_env; simp only [hbk, hbc.2.2, hbS, hbn, hbc.2.1]; omega)) ?_ (by omega)
  refine Runs.last (run_dm C paramsS _ vT1 vH vM vT2 (by decide) (by decide) (by decide)
    (by norm_env; simp only [hbk, hbc.2.2, hbS, hbn, hbc.2.1]; omega) (by norm_env; simp only [hbk, hbc.2.2, hbS, hbn, hbc.2.1]; omega)) ?_ (by omega)
  intro _
  norm_env
  rw [hbk, hbc.2.2, hbS, hbn, hbc.2.1]
  exact ⟨by unfold hParam; ring, by unfold mParam hParam; congr 1⟩

/-- `x := x + c·y` by `c` additions (the scratch `vT2` is zeroed when `c = 0`). -/
def addRep (x y : Var) : ℕ → Sc
  | 0 => .op (.zero vT2)
  | c + 1 => .seq (.op (.add x y)) (addRep x y c)

theorem addRep_spec (C : Ctx) (x y : Var) (hxy : x ≠ y) (hx : x ≠ vT2) (_hy : y ≠ vT2) (S : List Var) (hxS : x ∈ S)
    (hT : vT2 ∈ S) (_hyS : y ∉ S) : ∀ (c : ℕ) (a : Ds), a.env x + c * a.env y < 2 ^ C.Wd →
      Runs C (addRep x y c) a (2 * c + 1) S [] (fun b => b.env x = a.env x + c * a.env y) := by
  intro c
  induction c with
  | zero =>
    intro a _
    exact (run_zero C S a vT2 hT).mono le_rfl (List.Subset.refl _) (by rintro b - rfl; simp [env_set, hx])
  | succ c ih =>
    intro a hlt
    refine Runs.op1 (run_add C S a x y hxS hxy (by nlinarith)) ?_ (by omega)
    refine ((ih _ (by simp [env_set, hxy, Ne.symm hxy]; nlinarith)).mono (by omega) (List.Subset.refl _) ?_)
    rintro b - hb; rw [hb]; simp [env_set, Ne.symm hxy]; ring

/-- `t`, `t + 1`, `ℓ`. -/
def params2 (R : ℕ) : Sc :=
  .seq (.op (.copy vSX vM)) <| .seq sizeP <| .seq (.op (.copy vT vH)) <| .seq (addRep vT vK 6) <|
  .seq (addRep vT vTWO 6) <| .seq (.op (.add vT vSS)) <| .seq (incN vT R.size) <|
  .seq (.op (.copy vTB vT)) <| .seq (.op (.inc vTB)) <| .seq (.op (.copy vT2 vM)) <| .seq (.op (.inc vT2)) <|
  .op (.mul vT2 vT vL)

theorem params2_spec (C : Ctx) (R : ℕ) (a : Ds) (hc : Consts a) (n k : ℕ) (hk : a.env vK = k)
    (hh : a.env vH = hParam n k) (hm : a.env vM = mParam n k) (hW : 2 * (arityParam R n k + 4) < 2 ^ C.Wd) :
    Runs C (params2 R) a (n * 5 + 2 * R.size + 60) paramsS []
      (fun b => b.env vT = tParam R n k ∧ b.env vTB = tParam R n k + 1 ∧ b.env vL = arityParam R n k ∧
        b.env vH = hParam n k ∧ b.env vM = mParam n k) := by
  have hmn : mParam n k ≤ n := mParam_le n k
  have hsm : (mParam n k).size ≤ mParam n k := by
    rcases Nat.eq_zero_or_pos (mParam n k) with h0 | h0
    · rw [h0]; simp
    · exact Nat.size_le.mpr Nat.lt_two_pow_self
  have htL : tParam R n k ≤ arityParam R n k := by unfold arityParam; nlinarith
  have hmL : mParam n k ≤ arityParam R n k := by
    unfold arityParam; have : 1 ≤ tParam R n k := by unfold tParam; omega
    nlinarith
  have ht : tParam R n k = hParam n k + 6 * k + 12 + (mParam n k).size + R.size := rfl
  refine Runs.op1 (run_copy C paramsS a vSX vM (by decide) (by decide)) ?_ (by omega)
  refine Runs.callS (sizeP_spec C _ ⟨by norm_env; exact hc.1, by norm_env; exact hc.2.1, by norm_env; exact hc.2.2⟩
    _ (by norm_env; exact hm) (by omega)) (by decide) ?_ (by omega)
  intro b hb hbS
  have hbc : Consts b := ⟨by rw [hb.env _ (by decide)]; norm_env; exact hc.1,
    by rw [hb.env _ (by decide)]; norm_env; exact hc.2.1, by rw [hb.env _ (by decide)]; norm_env; exact hc.2.2⟩
  have hbk : b.env vK = k := by rw [hb.env _ (by decide)]; norm_env; exact hk
  have hbh : b.env vH = hParam n k := by rw [hb.env _ (by decide)]; norm_env; exact hh
  have hbm : b.env vM = mParam n k := by rw [hb.env _ (by decide)]; norm_env; exact hm
  refine Runs.op1 (run_copy C paramsS b vT vH (by decide) (by decide)) ?_ (by omega)
  refine Runs.callS (addRep_spec C vT vK (by decide) (by decide) (by decide) [vT, vT2] (by decide) (by decide)
    (by decide) 6 _ (by norm_env; rw [hbh, hbk]; omega)) (by decide) ?_ (by omega)
  intro b1 hb1 hb1T
  simp (config := { decide := true }) only [env_set, ite_true, ite_false] at hb1T
  have hb1c : Consts b1 := ⟨by rw [hb1.env _ (by decide)]; norm_env; exact hbc.1,
    by rw [hb1.env _ (by decide)]; norm_env; exact hbc.2.1, by rw [hb1.env _ (by decide)]; norm_env; exact hbc.2.2⟩
  refine Runs.callS (addRep_spec C vT vTWO (by decide) (by decide) (by decide) [vT, vT2] (by decide) (by decide)
    (by decide) 6 _ (by rw [hb1T, hb1c.2.2, hbh, hbk]; omega)) (by decide) ?_ (by omega)
  intro b2 hb2 hb2T
  have hb2c : Consts b2 := ⟨by rw [hb2.env _ (by decide)]; exact hb1c.1,
    by rw [hb2.env _ (by decide)]; exact hb1c.2.1, by rw [hb2.env _ (by decide)]; exact hb1c.2.2⟩
  have hb2S : b2.env vSS = (mParam n k).size := by
    rw [hb2.env _ (by decide), hb1.env _ (by decide)]; norm_env; exact hbS
  have hb2T' : b2.env vT = hParam n k + 6 * k + 12 := by rw [hb2T, hb1T, hb1c.2.2, hbh, hbk]; try ring
  refine Runs.op1 (run_add C paramsS b2 vT vSS (by decide) (by decide) (by rw [hb2T', hb2S]; omega)) ?_ (by omega)
  refine Runs.callS (incN_spec C vT (by decide) [vT, vT2] (by decide) (by decide) R.size _
    (by norm_env; rw [hb2T', hb2S]; omega)) (by decide) ?_ (by omega)
  intro b3 hb3 hb3T
  simp (config := { decide := true }) only [env_set, ite_true, ite_false] at hb3T
  rw [hb2T', hb2S] at hb3T
  have hb3c : Consts b3 := ⟨by rw [hb3.env _ (by decide)]; norm_env; exact hb2c.1,
    by rw [hb3.env _ (by decide)]; norm_env; exact hb2c.2.1, by rw [hb3.env _ (by decide)]; norm_env; exact hb2c.2.2⟩
  have hb3T' : b3.env vT = tParam R n k := by rw [hb3T, ht]
  have hb3m : b3.env vM = mParam n k := by
    rw [hb3.env _ (by decide)]; norm_env; rw [hb2.env _ (by decide), hb1.env _ (by decide)]; norm_env; exact hbm
  have hb3h : b3.env vH = hParam n k := by
    rw [hb3.env _ (by decide)]; norm_env; rw [hb2.env _ (by decide), hb1.env _ (by decide)]; norm_env; exact hbh
  refine Runs.op1 (run_copy C paramsS b3 vTB vT (by decide) (by decide)) ?_ (by omega)
  refine Runs.op1 (run_inc C paramsS _ vTB (by decide) (by norm_env; rw [hb3T']; omega)) ?_ (by omega)
  refine Runs.op1 (run_copy C paramsS _ vT2 vM (by decide) (by decide)) ?_ (by omega)
  refine Runs.op1 (run_inc C paramsS _ vT2 (by decide) (by norm_env; rw [hb3m]; omega)) ?_ (by omega)
  refine Runs.last (run_mul C paramsS _ vT2 vT vL (by decide) (by decide) (by decide) (by decide)
    (by norm_env; rw [hb3m, hb3T']; unfold arityParam at hW; omega)) ?_ (by omega)
  intro _
  norm_env
  rw [hb3T', hb3m, hb3h]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The powers `2^t`, `2^h`, `2^n`, `2^ℓ` and `2^t − 2`. -/
def pw2 (src dst : Var) : Sc := .seq (.op (.copy vEE src)) (.seq pow2P (.op (.copy dst vPD)))

def params3 : Sc :=
  .seq (pw2 vT vPOWT) <| .seq (pw2 vH vPOWH) <| .seq (pw2 vN vPOWN) <| .seq (pw2 vL vPOWL) <|
  .seq (.op (.copy vEXP vPOWT)) (.op (.sub vEXP vTWO))

/-- The values that `params3` reads stay in place. -/
structure PVal (g : Prm) (a : Ds) : Prop where
  c : Consts a
  t : a.env vT = g.t
  tb : a.env vTB = g.t + 1
  h : a.env vH = g.h
  m : a.env vM = g.m
  n : a.env vN = g.n
  L : a.env vL = g.L
  p : a.env vP = g.p

def pvars : List Var := [vZ, vONE, vTWO, vT, vTB, vH, vM, vN, vL, vP]

theorem PVal.of_fr {g : Prm} {S : List Var} {a b : Ds} (h : PVal g a) (hf : Fr S [] a b)
    (hS : ∀ x ∈ pvars, x ∉ S) : PVal g b := by
  have e : ∀ x ∈ pvars, b.env x = a.env x := fun x hx => hf.env x (hS x hx)
  obtain ⟨⟨h0, h1, h2⟩, ht, htb, hh, hm, hn, hL, hp⟩ := h
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (rw [e _ (by simp [pvars])]; assumption)

theorem PVal.of_env {g : Prm} {a b : Ds} (h : PVal g a) (he : ∀ x ∈ pvars, b.env x = a.env x) : PVal g b := by
  obtain ⟨⟨h0, h1, h2⟩, ht, htb, hh, hm, hn, hL, hp⟩ := h
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (rw [he _ (by simp [pvars])]; assumption)

theorem PVal.set {g : Prm} {a : Ds} (h : PVal g a) (x : Var) (v : ℕ) (hx : x ∉ pvars) : PVal g (a.set x v) :=
  h.of_fr (Fr.set [x] a x v (by simp)) (by intro y hy h'; simp at h'; subst h'; exact hx hy)

theorem params3_spec (C : Ctx) (g : Prm) (a : Ds) (hv : PVal g a) (hle : g.t ≤ g.L ∧ g.h ≤ g.L ∧ g.n ≤ g.L)
    (ht1 : 1 ≤ g.t) (hW : g.L + 4 ≤ C.Wd) :
    Runs C params3 a (g.L * 20 + 60) paramsS [] (fun b => Glob g b) := by
  have hWt : ∀ e ≤ g.L, e + 1 < C.Wd := fun e he => by omega
  have step : ∀ (b : Ds) (src dst : Var) (e : ℕ), PVal g b → b.env src = e → e ≤ g.L →
      src ∈ pvars → dst ∉ pvars → dst ≠ vEE → dst ≠ vPD → dst ≠ vEJ → dst ∈ paramsS →
      Runs C (pw2 src dst) b (e * 5 + 10) paramsS []
        (fun d => Fr paramsS [] b d ∧ (∀ x, x ≠ dst → x ∉ pow2S → x ≠ vEE → d.env x = b.env x) ∧ d.env dst = 2 ^ e) := by
    intro b src dst e hb hsrc he hsp hdp hdE hdD hdJ hdS
    have hsE : vEE ≠ src := fun h => (by decide : vEE ∉ pvars) (h ▸ hsp)
    refine Runs.op1 (run_copy C paramsS b vEE src (by decide) hsE) ?_ (by omega)
    refine Runs.callS (pow2P_spec C _ (by have := hb.c; exact ⟨by norm_env; exact this.1, by norm_env; exact this.2.1,
      by norm_env; exact this.2.2⟩) e (by norm_env; exact hsrc) (hWt e he)) (by decide) ?_ (by omega)
    intro d hd hdv
    refine Runs.last (run_copy C paramsS _ dst vPD hdS hdD) ?_ (by omega)
    intro _
    refine ⟨?_, ?_, ?_⟩
    · exact ((Fr.set paramsS b vEE _ (by decide)).trans0 (hd.mono (by decide))).set_right _ _ hdS
    · intro x hx1 hx2 hx3
      rw [env_set, if_neg hx1, hd.env x hx2, env_set, if_neg hx3]
    · rw [env_set, if_pos rfl, hdv]
  have hPV : ∀ x ∈ pvars, x ≠ vPOWT ∧ x ≠ vPOWH ∧ x ≠ vPOWN ∧ x ≠ vPOWL ∧ x ∉ pow2S ∧ x ≠ vEE := by decide
  refine Runs.call (step a vT vPOWT g.t hv hv.t hle.1 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)) ?_ (by omega)
  rintro b1 - ⟨-, he1, hp1⟩
  have hv1 : PVal g b1 := hv.of_env (fun x hx => he1 x (hPV x hx).1 (hPV x hx).2.2.2.2.1 (hPV x hx).2.2.2.2.2)
  refine Runs.call (step b1 vH vPOWH g.h hv1 hv1.h hle.2.1 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)) ?_ (by omega)
  rintro b2 - ⟨-, he2, hp2⟩
  have hv2 : PVal g b2 := hv1.of_env (fun x hx => he2 x (hPV x hx).2.1 (hPV x hx).2.2.2.2.1 (hPV x hx).2.2.2.2.2)
  refine Runs.call (step b2 vN vPOWN g.n hv2 hv2.n hle.2.2 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)) ?_ (by omega)
  rintro b3 - ⟨-, he3, hp3⟩
  have hv3 : PVal g b3 := hv2.of_env (fun x hx => he3 x (hPV x hx).2.2.1 (hPV x hx).2.2.2.2.1 (hPV x hx).2.2.2.2.2)
  refine Runs.call (step b3 vL vPOWL g.L hv3 hv3.L le_rfl (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)) ?_ (by omega)
  rintro b4 - ⟨-, he4, hp4⟩
  have hv4 : PVal g b4 := hv3.of_env (fun x hx => he4 x (hPV x hx).2.2.2.1 (hPV x hx).2.2.2.2.1 (hPV x hx).2.2.2.2.2)
  have h4t : b4.env vPOWT = 2 ^ g.t := by
    rw [he4 _ (by decide) (by decide) (by decide), he3 _ (by decide) (by decide) (by decide),
      he2 _ (by decide) (by decide) (by decide), hp1]
  have h4h : b4.env vPOWH = 2 ^ g.h := by
    rw [he4 _ (by decide) (by decide) (by decide), he3 _ (by decide) (by decide) (by decide), hp2]
  have h4n : b4.env vPOWN = 2 ^ g.n := by rw [he4 _ (by decide) (by decide) (by decide), hp3]
  have htW : 2 ≤ 2 ^ g.t := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ g.t := Nat.pow_le_pow_right (by norm_num) ht1
  refine Runs.op1 (run_copy C paramsS b4 vEXP vPOWT (by decide) (by decide)) ?_ (by omega)
  refine Runs.last (run_sub C paramsS _ vEXP vTWO (by decide) (by decide) (by
    norm_env; rw [hv4.c.2.2, h4t]; exact htW)) ?_ (by omega)
  intro _
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_env
  · exact hv4.c.1
  · exact hv4.c.2.1
  · exact hv4.c.2.2
  · exact hv4.t
  · exact hv4.tb
  · exact h4t
  · exact hv4.h
  · exact h4h
  · exact hv4.n
  · exact h4n
  · exact hv4.m
  · exact hv4.L
  · exact hp4
  · exact hv4.p
  · rw [h4t, hv4.c.2.2]

/-- The parameters before the modulus search (`p = 0`). -/
def prm0 (R n k : ℕ) : Prm := ⟨tParam R n k, 0, hParam n k, mParam n k, n, arityParam R n k⟩

theorem prm0_le (R n k : ℕ) : n + k ≤ arityParam R n k ∧ tParam R n k ≤ arityParam R n k ∧
    hParam n k ≤ tParam R n k ∧ mParam n k ≤ arityParam R n k ∧ 1 ≤ tParam R n k := by
  have h1 := le_mParam_mul n k
  have ht1 : 1 ≤ tParam R n k := by unfold tParam; omega
  have hht := hParam_le_tParam R n k
  have hmt : mParam n k * hParam n k ≤ mParam n k * tParam R n k := Nat.mul_le_mul_left _ hht
  have hkt : k ≤ tParam R n k := by unfold tParam; omega
  have hL : arityParam R n k = mParam n k * tParam R n k + tParam R n k := by unfold arityParam; ring
  refine ⟨by rw [hL]; omega, by rw [hL]; omega, hht, ?_, ht1⟩
  rw [hL]; nlinarith

def paramsP (R : ℕ) : Sc := .seq params1 (.seq (params2 R) params3)

def paramsCost (R n L : ℕ) : ℕ := n * 5 + 30 + (n * 5 + 2 * R.size + 60) + (L * 20 + 60) + 2

theorem paramsP_spec (C : Ctx) (R : ℕ) (a : Ds) (hc : Consts a) (n k : ℕ) (hn : a.env vN = n) (hk : a.env vK = k)
    (hp : a.env vP = 0) (hW : arityParam R n k + 5 ≤ C.Wd) :
    Runs C (paramsP R) a (paramsCost R n (arityParam R n k)) paramsS [] (fun b => Glob (prm0 R n k) b) := by
  obtain ⟨hnk, htL, hht, hmL, ht1⟩ := prm0_le R n k
  have hW2 : 2 * (arityParam R n k + 4) < 2 ^ C.Wd := by
    have h1 : 2 ^ (arityParam R n k + 5) ≤ 2 ^ C.Wd := Nat.pow_le_pow_right (by norm_num) hW
    have h2 := Nat.lt_two_pow_self (n := arityParam R n k + 4)
    rw [pow_succ] at h1; omega
  refine Runs.call (params1_spec C a hc n k hn hk (by omega)) ?_ (by unfold paramsCost; omega)
  rintro b hb ⟨hbh, hbm⟩
  have hbc : Consts b := hc.of_fr hb (by decide)
  have hbk : b.env vK = k := (hb.env vK (by decide)).trans hk
  refine Runs.call (params2_spec C R b hbc n k hbk hbh hbm hW2) ?_ (by unfold paramsCost; omega)
  rintro d hd ⟨hdt, hdtb, hdL, hdh, hdm⟩
  have hv : PVal (prm0 R n k) d :=
    ⟨hbc.of_fr hd (by decide), hdt, hdtb, hdh, hdm, by rw [hd.env vN (by decide), hb.env vN (by decide), hn]; rfl,
      hdL, by rw [hd.env vP (by decide), hb.env vP (by decide), hp]; rfl⟩
  exact (params3_spec C (prm0 R n k) d hv ⟨htL, le_trans hht htL, show n ≤ arityParam R n k by omega⟩ ht1
    (by show arityParam R n k + 4 ≤ C.Wd; omega)).mono
    (by show arityParam R n k * 20 + 60 ≤ _; unfold paramsCost; omega) (List.Subset.refl _) (fun _ _ h => h)

/-! ## The framed arity -/

abbrev vFX : Var := 93
abbrev vFQ : Var := 94
abbrev vFB : Var := 95

def emitS : List Var := [vFX, vFQ, vFB]

def emitBody : Sc :=
  .seq (.op (.emit true)) <| .seq (.op (.dm vFX vTWO vFQ vFB)) <| .seq (.op (.copy vFX vFQ)) <|
  .ite (.eq vFB vONE) (.op (.emit true)) (.op (.emit false))

def emitFrameP : Sc := .seq (.op (.copy vFX vL)) <| .seq (.loop (.lt vZ vFX) emitBody) (.op (.emit false))

theorem frame_eq_flatMap (l : List Bool) : frame l = l.flatMap (fun b => [true, b]) ++ [false] := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [frame, ih]

theorem bits_eq_map (x : ℕ) : x.bits = (List.range x.size).map x.testBit := by
  apply List.ext_getElem
  · simp [Nat.size_eq_bits_len]
  · intro i h1 h2
    have := getD_bits x i
    rw [List.getD_eq_getElem _ _ h1] at this
    simp [this]

theorem emitFrameP_spec (C : Ctx) (a : Ds) (hc : Consts a) (L : ℕ) (hL : a.env vL = L) (hW : 2 * 2 ≤ 2 ^ C.Wd) :
    Runs C emitFrameP a (L.size * 12 + 10) emitS (frame L.bits) (fun _ => True) := by
  have hsz : L.size ≤ L := by
    rcases Nat.eq_zero_or_pos L with rfl | h0
    · simp
    · exact Nat.size_le.mpr Nat.lt_two_pow_self
  refine Runs.op1 (run_copy C emitS a vFX vL (by decide) (by decide)) ?_ (by omega)
  have hstep : ∀ j < L.size, ∀ b : Ds, (Consts b ∧ b.env vFX = L / 2 ^ j) → (Cnd.lt vZ vFX).eval b = true ∧
      Runs C emitBody b 8 emitS [true, L.testBit j] (fun b' => Consts b' ∧ b'.env vFX = L / 2 ^ (j + 1)) := by
    rintro j hj b ⟨hcb, hX⟩
    have hpos : 0 < L / 2 ^ j := Nat.div_pos (Nat.lt_size.mp hj) (Nat.two_pow_pos j)
    refine ⟨by simp [Cnd.eval, hX, hcb.1, hpos], ?_⟩
    refine Runs.emit1 (run_emit C emitS b true) ?_ (by omega)
    refine Runs.op1 (run_dm C emitS _ vFX vTWO vFQ vFB (by decide) (by decide) (by decide)
      (by simp [hcb.2.2]) (by simp [hcb.2.2]; exact hW)) ?_ (by omega)
    refine Runs.op1 (run_copy C emitS _ vFX vFQ (by decide) (by decide)) ?_ (by omega)
    norm_env
    simp only [hcb.2.2, hX]
    have hbit : L / 2 ^ j % 2 = if L.testBit j then 1 else 0 := by
      rw [Nat.testBit_eq_decide_div_mod_eq]
      rcases Nat.mod_two_eq_zero_or_one (L / 2 ^ j) with h | h <;> simp [h]
    have hq : L / 2 ^ j / 2 = L / 2 ^ (j + 1) := by rw [Nat.div_div_eq_div_mul, ← pow_succ]
    cases hL : L.testBit j
    · refine Runs.iteF' (by unfold Cnd.wf; decide)
        (by simp (config := { decide := true }) [Cnd.eval, env_set, hbit, hL, hcb.2.1]) ?_ (by omega)
      refine Runs.last (run_emit C emitS _ false) ?_ (by omega)
      intro _
      refine ⟨⟨?_, ?_, ?_⟩, ?_⟩ <;> simp (config := { decide := true }) [env_set, hcb.1, hcb.2.1, hcb.2.2, hq]
    · refine Runs.iteT' (by unfold Cnd.wf; decide)
        (by simp (config := { decide := true }) [Cnd.eval, env_set, hbit, hL, hcb.2.1]) ?_ (by omega)
      refine Runs.last (run_emit C emitS _ true) ?_ (by omega)
      intro _
      refine ⟨⟨?_, ?_, ?_⟩, ?_⟩ <;> simp (config := { decide := true }) [env_set, hcb.1, hcb.2.1, hcb.2.2, hq]
  have hloop := Runs.loopN (C := C) (c := .lt vZ vFX) (body := emitBody) (S := emitS) (by unfold Cnd.wf; decide)
    L.size 8 (fun j => [true, L.testBit j]) (fun j b => Consts b ∧ b.env vFX = L / 2 ^ j) hstep
    (by rintro b ⟨hcb, hX⟩; simp [Cnd.eval, hX, hcb.1, Nat.div_eq_of_lt (Nat.lt_size_self L)])
    (a.set vFX (a.env vL))
    ⟨⟨by simp (config := { decide := true }) [env_set, hc.1], by simp (config := { decide := true }) [env_set, hc.2.1],
      by simp (config := { decide := true }) [env_set, hc.2.2]⟩, by simp [env_set, hL]⟩
  have e := Runs.seq hloop (fun b _ _ => (run_emit C emitS b false).mono le_rfl (List.Subset.refl _)
    (fun _ _ _ => trivial))
  rw [frame_eq_flatMap, bits_eq_map, List.flatMap_map]
  exact e.costLe (by omega)

end NearCubicGates.Adapters.Amplification.Enc
