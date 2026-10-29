import SourceAdapters.Amplification.EncXor
import SourceAdapters.Amplification.EncField

/-!
# Field multiplication and inversion of the X3 field in the cell language (proof of `thm:short-pcp-ours`; proof of `lem:small-bias`)

The globals `Glob g` (the field degree `t`, `2^t`, the modulus `p`, `h`, `2^h`, `n`, `2^n`, `m`, `ℓ`, `2^ℓ`,
`2^t − 2`) are set once by the encoder and never written by a routine. Routines:

* `lfsrP`: `FR := GF2.lfsr p t FA` (multiplication by `X`: double, and add `p` when bit `t` appears);
* `fmulP`: `MR := fmul p t MA MB` (`EncField.fmul`, shift-and-add over the `t` bits of `MB`);
* `finvP`: `IY := finv p t IA = IA^(2^t − 2)`.
-/

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Adapters.Amplification.Enc

open NearCubicGates.Close.Cells NearCubicWires.WireExponent3_5

abbrev vT : Var := 3
abbrev vPOWT : Var := 5
abbrev vH : Var := 6
abbrev vPOWH : Var := 7
abbrev vN : Var := 8
abbrev vPOWN : Var := 9
abbrev vM : Var := 10
abbrev vL : Var := 11
abbrev vPOWL : Var := 12
abbrev vP : Var := 13
abbrev vEXP : Var := 15

/-- The encoder's parameters. -/
structure Prm where
  t : ℕ
  p : ℕ
  h : ℕ
  m : ℕ
  n : ℕ
  L : ℕ

/-- The globals are in place. -/
structure Glob (g : Prm) (a : Ds) : Prop where
  c : Consts a
  t : a.env vT = g.t
  tb : a.env vTB = g.t + 1
  powt : a.env vPOWT = 2 ^ g.t
  h : a.env vH = g.h
  powh : a.env vPOWH = 2 ^ g.h
  n : a.env vN = g.n
  pown : a.env vPOWN = 2 ^ g.n
  m : a.env vM = g.m
  L : a.env vL = g.L
  powl : a.env vPOWL = 2 ^ g.L
  p : a.env vP = g.p
  exp : a.env vEXP = 2 ^ g.t - 2

def globs : List Var := [vZ, vONE, vTWO, vT, vTB, vPOWT, vH, vPOWH, vN, vPOWN, vM, vL, vPOWL, vP, vEXP]

theorem Glob.of_fr {g : Prm} {S : List Var} {w : List Bool} {a b : Ds} (h : Glob g a) (hf : Fr S w a b)
    (hS : ∀ x ∈ globs, x ∉ S) : Glob g b := by
  have e : ∀ x ∈ globs, b.env x = a.env x := fun x hx => hf.env x (hS x hx)
  obtain ⟨⟨h0, h1, h2⟩, ht, htb, hpt, hh, hph, hn, hpn, hm, hL, hpl, hp, he⟩ := h
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (rw [e _ (by simp [globs])]; assumption)

/-- The width suffices for the field words and the counters. -/
def WOk (g : Prm) (C : Ctx) : Prop := g.L + 4 ≤ C.Wd ∧ g.t ≤ g.L ∧ g.h ≤ g.t ∧ g.n ≤ g.L ∧ g.m ≤ g.L ∧ 1 ≤ g.t

theorem pow_lt_W {g : Prm} {C : Ctx} (hw : WOk g C) {x : ℕ} (hx : x ≤ g.L + 3) : 2 ^ x < 2 ^ C.Wd :=
  Nat.pow_lt_pow_right (by norm_num) (by have := hw.1; omega)

theorem lt_W {g : Prm} {C : Ctx} (hw : WOk g C) {x : ℕ} (hx : x < 2 ^ (g.L + 3)) : x < 2 ^ C.Wd :=
  lt_trans hx (pow_lt_W hw le_rfl)

theorem two_pow_mono {a b : ℕ} (h : a ≤ b) : 2 ^ a ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) h

/-! ## Multiplication by `X` -/

abbrev vFA : Var := 30
abbrev vFR : Var := 31

def lfsrS : List Var := [vFR, vXA, vXB, vXR, vXQ, vXRa, vXRb, vXPW, vXK]

def lfsrP : Sc :=
  .seq (.op (.copy vFR vFA)) <| .seq (.op (.shl vFR)) <|
  .ite (.lt vFR vPOWT) (.op (.zero vXQ))
    (.seq (.op (.copy vXA vFR)) <| .seq (.op (.copy vXB vP)) <| .seq xorP (.op (.copy vFR vXR)))

def lfsrCost (t : ℕ) : ℕ := 25 * t + 50

theorem lfsrP_spec (C : Ctx) (g : Prm) (hw : WOk g C) (hp : GF.ModulusOk g.p g.t) (a : Ds) (hg : Glob g a)
    (A : ℕ) (hA : a.env vFA = A) (hAlt : A < 2 ^ g.t) :
    Runs C lfsrP a (lfsrCost g.t) lfsrS [] (fun b => b.env vFR = GF2.lfsr g.p g.t A) := by
  have h2A : 2 * A < 2 ^ (g.t + 1) := by rw [pow_succ]; omega
  have hpl : g.p < 2 ^ (g.t + 1) := hp.2
  have hWt : 2 ^ (g.t + 1) < 2 ^ C.Wd := pow_lt_W hw (by have := hw.2.1; omega)
  refine Runs.op1 (run_copy C lfsrS a vFR vFA (by decide) (by decide)) ?_ (by unfold lfsrCost; omega)
  norm_env
  refine Runs.op1 (run_shl C lfsrS _ vFR (by decide) (by norm_env; rw [hA]; omega)) ?_ (by unfold lfsrCost; omega)
  norm_env
  by_cases hlt : 2 * A < 2 ^ g.t
  · refine Runs.iteT' (by unfold Cnd.wf; decide) (by simp (config := { decide := true }) [Cnd.eval, env_set, hA, hg.powt, hlt]) ?_
      (by unfold lfsrCost; omega)
    refine Runs.last (run_zero C lfsrS _ vXQ (by decide)) ?_ (by unfold lfsrCost; omega)
    intro _
    norm_env
    rw [hA]
    unfold GF2.lfsr
    rw [if_neg (by rw [Nat.testBit_lt_two_pow hlt]; simp)]
  · refine Runs.iteF' (by unfold Cnd.wf; decide) (by simp (config := { decide := true }) [Cnd.eval, env_set, hA, hg.powt, hlt]) ?_
      (by unfold lfsrCost; omega)
    refine Runs.op1 (run_copy C lfsrS _ vXA vFR (by decide) (by decide)) ?_ (by unfold lfsrCost; omega)
    norm_env
    refine Runs.op1 (run_copy C lfsrS _ vXB vP (by decide) (by decide)) ?_ (by unfold lfsrCost; omega)
    norm_env
    refine Runs.callS (xorP_spec C _ ⟨by norm_env; exact hg.c.1, by norm_env; exact hg.c.2.1, by norm_env; exact hg.c.2.2⟩
      (g.t + 1) (by norm_env; exact hg.tb) (2 * A) g.p (by norm_env; rw [hA]) (by norm_env; exact hg.p) h2A hpl
      (by have := hw.1; have := hw.2.1; omega)) (by decide) ?_ (by unfold lfsrCost; omega)
    intro b _ hb
    refine Runs.last (run_copy C lfsrS _ vFR vXR (by decide) (by decide)) ?_ (by unfold lfsrCost; omega)
    intro _
    norm_env
    rw [hb]
    unfold GF2.lfsr
    rw [if_pos (Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt (by omega) h2A)]

/-! ## Multiplication -/

abbrev vMA : Var := 33
abbrev vMB : Var := 34
abbrev vMR : Var := 35
abbrev vMX : Var := 36
abbrev vMBb : Var := 37
abbrev vMS : Var := 38
abbrev vMQ : Var := 39
abbrev vMRb : Var := 40

def fmulS : List Var :=
  [vMR, vMX, vMBb, vMS, vMQ, vMRb, vFA, vFR, vXA, vXB, vXR, vXQ, vXRa, vXRb, vXPW, vXK]

def fmulAdd : Sc := .seq (.op (.copy vXA vMR)) <| .seq (.op (.copy vXB vMX)) <| .seq xorP (.op (.copy vMR vXR))

def fmulBody : Sc :=
  .seq (.op (.dm vMBb vTWO vMQ vMRb)) <| .seq (.op (.copy vMBb vMQ)) <|
  .seq (.ite (.eq vMRb vONE) fmulAdd (.op (.zero vMQ))) <|
  .seq (.op (.copy vFA vMX)) <| .seq lfsrP <| .seq (.op (.copy vMX vFR)) (.op (.inc vMS))

def fmulP : Sc :=
  .seq (.op (.zero vMR)) <| .seq (.op (.copy vMX vMA)) <| .seq (.op (.copy vMBb vMB)) <| .seq (.op (.zero vMS)) <|
  .loop (.lt vMS vT) fmulBody

def fmulCost (t : ℕ) : ℕ := t * (50 * t + 120 + 2) + 10

/-- The state of `fmulP` before round `j`. -/
def FmulInv (g : Prm) (a0 : Ds) (A B j : ℕ) (b : Ds) : Prop :=
  Fr fmulS [] a0 b ∧ fmulGo g.p g.t (g.t - j) (b.env vMR) (b.env vMX) (b.env vMBb) = fmul g.p g.t A B ∧
    b.env vMR < 2 ^ g.t ∧ b.env vMX < 2 ^ g.t ∧ b.env vMBb = B / 2 ^ j ∧ b.env vMS = j

theorem fmulBody_spec (C : Ctx) (g : Prm) (hw : WOk g C) (hp : GF.ModulusOk g.p g.t) (a0 b : Ds)
    (hg : Glob g b) (A B j : ℕ) (hj : j < g.t) (hinv : FmulInv g a0 A B j b) :
    Runs C fmulBody b (50 * g.t + 120) fmulS [] (FmulInv g a0 A B (j + 1)) := by
  obtain ⟨hf, hgo, hR, hX, hBb, hS⟩ := hinv
  obtain ⟨r, hr⟩ : ∃ r, b.env vMR = r := ⟨_, rfl⟩
  obtain ⟨x, hx⟩ : ∃ x, b.env vMX = x := ⟨_, rfl⟩
  obtain ⟨bb, hbb⟩ : ∃ bb, b.env vMBb = bb := ⟨_, rfl⟩
  rw [hr, hx, hbb] at hgo
  rw [hr] at hR
  rw [hx] at hX
  rw [hbb] at hBb
  have hW4 : 2 * 2 ≤ 2 ^ C.Wd := by
    have := pow_lt_W hw (x := 2) (by omega); simpa using this.le
  have ht1 : 2 ^ g.t ≤ 2 ^ (g.t + 1) := two_pow_mono (by omega)
  have hjW : j + 1 < 2 ^ C.Wd := by
    have := Nat.lt_two_pow_self (n := C.Wd); have := hw.1; have := hw.2.1; omega
  refine Runs.op1 (run_dm C fmulS b vMBb vTWO vMQ vMRb (by decide) (by decide) (by decide)
    (by rw [hg.c.2.2]; norm_num) (by rw [hg.c.2.2]; exact hW4)) ?_ (by omega)
  norm_env
  refine Runs.op1 (run_copy C fmulS _ vMBb vMQ (by decide) (by decide)) ?_ (by omega)
  norm_env
  rw [hg.c.2.2, hbb]
  have hf2 : Fr fmulS [] b (((b.set vMQ (bb / 2)).set vMRb (bb % 2)).set vMBb (bb / 2)) :=
    (((Fr.refl fmulS b).set_right _ _ (by decide)).set_right _ _ (by decide)).set_right _ _ (by decide)
  have hg2 : Glob g (((b.set vMQ (bb / 2)).set vMRb (bb % 2)).set vMBb (bb / 2)) := hg.of_fr hf2 (by decide)
  -- the conditional addition
  have hite : Runs C (.ite (.eq vMRb vONE) fmulAdd (.op (.zero vMQ)))
      (((b.set vMQ (bb / 2)).set vMRb (bb % 2)).set vMBb (bb / 2)) (25 * g.t + 45) fmulS []
      (fun c => c.env vMR = (if bb % 2 = 1 then r ^^^ x else r) ∧ c.env vMX = x ∧ c.env vMBb = bb / 2 ∧
        c.env vMS = j) := by
    by_cases hbit : bb % 2 = 1
    · refine Runs.iteT' (by unfold Cnd.wf; decide)
        (by simp (config := { decide := true }) [Cnd.eval, env_set, hg.c.2.1, hbit]) ?_ (by omega)
      refine Runs.op1 (run_copy C fmulS _ vXA vMR (by decide) (by decide)) ?_ (by omega)
      norm_env
      refine Runs.op1 (run_copy C fmulS _ vXB vMX (by decide) (by decide)) ?_ (by omega)
      norm_env
      refine Runs.callS (xorP_spec C _ ⟨by norm_env; exact hg2.c.1, by norm_env; exact hg2.c.2.1,
          by norm_env; exact hg2.c.2.2⟩ (g.t + 1) (by norm_env; exact hg2.tb) r x (by norm_env; exact hr)
          (by norm_env; exact hx) (lt_of_lt_of_le hR ht1) (lt_of_lt_of_le hX ht1)
          (by have := hw.1; have := hw.2.1; omega)) (by decide) ?_ (by omega)
      intro c hc hcv
      refine Runs.last (run_copy C fmulS _ vMR vXR (by decide) (by decide)) ?_ (by omega)
      intro _
      norm_env
      refine ⟨by rw [hcv, if_pos hbit], ?_, ?_, ?_⟩
      · rw [hc.env vMX (by decide)]; norm_env; exact hx
      · rw [hc.env vMBb (by decide)]; norm_env
      · rw [hc.env vMS (by decide)]; norm_env; exact hS
    · refine Runs.iteF' (by unfold Cnd.wf; decide)
        (by simp (config := { decide := true }) [Cnd.eval, env_set, hg.c.2.1, hbit]) ?_ (by omega)
      refine Runs.last (run_zero C fmulS _ vMQ (by decide)) ?_ (by omega)
      intro _
      norm_env
      exact ⟨by rw [if_neg hbit, hr], hx, trivial, hS⟩
  refine Runs.call hite ?_ (by omega)
  rintro c hc ⟨hcR, hcX, hcB, hcS⟩
  have hgc : Glob g c := hg2.of_fr hc (by decide)
  refine Runs.op1 (run_copy C fmulS _ vFA vMX (by decide) (by decide)) ?_ (by omega)
  have hgc' : Glob g (c.set vFA (c.env vMX)) := hgc.of_fr (Fr.set fmulS c vFA _ (by decide)) (by decide)
  refine Runs.callS (lfsrP_spec C g hw hp _ hgc' x (by norm_env; exact hcX) hX) (by decide) ?_
    (by unfold lfsrCost; omega)
  intro d hd hdv
  refine Runs.op1 (run_copy C fmulS _ vMX vFR (by decide) (by decide)) ?_ (by unfold lfsrCost at *; omega)
  have hdS0 : d.env vMS = j := by rw [hd.env vMS (by decide)]; norm_env; exact hcS
  refine Runs.last (run_inc C fmulS _ vMS (by decide) (by norm_env; rw [hdS0]; exact hjW)) ?_ (by unfold lfsrCost at *; omega)
  intro _
  have hR' : (if bb % 2 = 1 then r ^^^ x else r) < 2 ^ g.t := by
    split_ifs
    · exact Nat.xor_lt_two_pow hR hX
    · exact hR
  have hdR : d.env vMR = (if bb % 2 = 1 then r ^^^ x else r) := by
    rw [hd.env vMR (by decide)]; norm_env; exact hcR
  have hdB : d.env vMBb = bb / 2 := by rw [hd.env vMBb (by decide)]; norm_env; exact hcB
  have hdS : d.env vMS = j := by rw [hd.env vMS (by decide)]; norm_env; exact hcS
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have e1 := (hf.trans0 hf2).trans0 hc
    have e2 := e1.trans0 (Fr.set fmulS c vFA (c.env vMX) (by decide))
    have e3 := e2.trans0 (hd.mono (by decide))
    exact (e3.set_right _ _ (by decide)).set_right _ _ (by decide)
  · norm_env
    rw [hdR, hdB, hdv]
    rw [← hgo, show g.t - j = (g.t - (j + 1)) + 1 by omega]
    rfl
  · norm_env; rw [hdR]; exact hR'
  · norm_env; rw [hdv]; exact (GF.lfsr_spec g.p g.t x hp hX).1
  · norm_env; rw [hdB, hBb, Nat.div_div_eq_div_mul, ← pow_succ]
  · norm_env; rw [hdS]

theorem fmulP_spec (C : Ctx) (g : Prm) (hw : WOk g C) (hp : GF.ModulusOk g.p g.t) (a : Ds) (hg : Glob g a)
    (A B : ℕ) (hA : a.env vMA = A) (hB : a.env vMB = B) (hAlt : A < 2 ^ g.t) :
    Runs C fmulP a (fmulCost g.t) fmulS [] (fun b => b.env vMR = fmul g.p g.t A B ∧ b.env vMR < 2 ^ g.t) := by
  refine Runs.op1 (run_zero C fmulS a vMR (by decide)) ?_ (by unfold fmulCost; omega)
  refine Runs.op1 (run_copy C fmulS _ vMX vMA (by decide) (by decide)) ?_ (by unfold fmulCost; omega)
  refine Runs.op1 (run_copy C fmulS _ vMBb vMB (by decide) (by decide)) ?_ (by unfold fmulCost; omega)
  refine Runs.op1 (run_zero C fmulS _ vMS (by decide)) ?_ (by unfold fmulCost; omega)
  norm_env
  rw [hA, hB]
  refine (Runs.loopN0 (C := C) (c := .lt vMS vT) (body := fmulBody) (S := fmulS) (by unfold Cnd.wf; decide)
    g.t (50 * g.t + 120) (FmulInv g a A B) ?step ?stop _ ?init).mono ?cost (List.Subset.refl _) ?post
  case cost => unfold fmulCost; omega
  case post =>
    rintro b - ⟨-, hgo, hR, -, -, -⟩
    rw [Nat.sub_self] at hgo
    exact ⟨by simpa [fmulGo] using hgo, hR⟩
  case step =>
    rintro j hj b hinv
    have hgb : Glob g b := hg.of_fr hinv.1 (by decide)
    refine ⟨by simp [Cnd.eval, hinv.2.2.2.2.2, hgb.t, hj], ?_⟩
    exact fmulBody_spec C g hw hp a b hgb A B j hj hinv
  case stop =>
    rintro b ⟨hf, -, -, -, -, hS⟩
    have hgb : Glob g b := hg.of_fr hf (by decide)
    simp [Cnd.eval, hS, hgb.t]
  case init =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (((((Fr.refl fmulS a).set_right _ _ (by decide)).set_right _ _ (by decide)).set_right _ _
        (by decide)).set_right _ _ (by decide))
    all_goals norm_env
    · simp [fmul]
    · exact Nat.two_pow_pos _
    · exact hAlt
    · simp

/-! ## Inversion -/

abbrev vIA : Var := 42
abbrev vIY : Var := 43
abbrev vIJ : Var := 44

def finvS : List Var := [vIY, vIJ, vMA, vMB] ++ fmulS

def finvBody : Sc :=
  .seq (.op (.copy vMA vIY)) <| .seq (.op (.copy vMB vIA)) <| .seq fmulP <| .seq (.op (.copy vIY vMR)) (.op (.inc vIJ))

def finvP : Sc := .seq (.op (.copy vIY vONE)) <| .seq (.op (.zero vIJ)) <| .loop (.lt vIJ vEXP) finvBody

def finvCost (t : ℕ) : ℕ := (2 ^ t - 2) * (fmulCost t + 10 + 2) + 10

/-- The state of `finvP` before round `j`. -/
def FinvInv (g : Prm) (a0 : Ds) (A j : ℕ) (b : Ds) : Prop :=
  Fr finvS [] a0 b ∧ fpow g.p g.t (2 ^ g.t - 2 - j) (b.env vIY) A = finv g.p g.t A ∧ b.env vIY < 2 ^ g.t ∧
    b.env vIJ = j

theorem finvP_spec (C : Ctx) (g : Prm) (hw : WOk g C) (hp : GF.ModulusOk g.p g.t) (a : Ds) (hg : Glob g a)
    (A : ℕ) (hA : a.env vIA = A) :
    Runs C finvP a (finvCost g.t) finvS [] (fun b => b.env vIY = finv g.p g.t A ∧ b.env vIY < 2 ^ g.t) := by
  have hone : 1 < 2 ^ g.t := Nat.one_lt_two_pow (by have := hw.2.2.2.2.2; omega)
  have hEW : 2 ^ g.t < 2 ^ C.Wd := pow_lt_W hw (by have := hw.2.1; omega)
  refine Runs.op1 (run_copy C finvS a vIY vONE (by decide) (by decide)) ?_ (by unfold finvCost; omega)
  refine Runs.op1 (run_zero C finvS _ vIJ (by decide)) ?_ (by unfold finvCost; omega)
  norm_env
  rw [hg.c.2.1]
  refine (Runs.loopN0 (C := C) (c := .lt vIJ vEXP) (body := finvBody) (S := finvS) (by unfold Cnd.wf; decide)
    (2 ^ g.t - 2) (fmulCost g.t + 10) (FinvInv g a A) ?step ?stop _ ?init).mono ?cost (List.Subset.refl _) ?post
  case cost => unfold finvCost; omega
  case post =>
    rintro b - ⟨-, hgo, hY, -⟩
    rw [Nat.sub_self] at hgo
    exact ⟨by simpa [fpow] using hgo, hY⟩
  case step =>
    rintro j hj b ⟨hf, hgo, hY, hJ⟩
    have hgb : Glob g b := hg.of_fr hf (by decide)
    have hbA : b.env vIA = A := (hf.env vIA (by decide)).trans hA
    refine ⟨by simp [Cnd.eval, hJ, hgb.exp, hj], ?_⟩
    refine Runs.op1 (run_copy C finvS b vMA vIY (by decide) (by decide)) ?_ (by omega)
    refine Runs.op1 (run_copy C finvS _ vMB vIA (by decide) (by decide)) ?_ (by omega)
    have hgb2 : Glob g ((b.set vMA (b.env vIY)).set vMB ((b.set vMA (b.env vIY)).env vIA)) :=
      hgb.of_fr (((Fr.refl finvS b).set_right _ _ (by decide)).set_right _ _ (by decide)) (by decide)
    refine Runs.callS (fmulP_spec C g hw hp _ hgb2 (b.env vIY) A (by norm_env) (by norm_env; exact hbA) hY)
      (by decide) ?_ (by omega)
    rintro c hc ⟨hcv, hclt⟩
    refine Runs.op1 (run_copy C finvS _ vIY vMR (by decide) (by decide)) ?_ (by omega)
    have hcJ : c.env vIJ = j := by rw [hc.env vIJ (by decide)]; norm_env; exact hJ
    refine Runs.last (run_inc C finvS _ vIJ (by decide) (by norm_env; rw [hcJ]; omega)) ?_ (by omega)
    intro _
    refine ⟨?_, ?_, ?_, ?_⟩
    · have e1 := (hf.trans0 (((Fr.refl finvS b).set_right _ _ (by decide)).set_right _ _ (by decide))).trans0
        (hc.mono (by decide))
      exact (e1.set_right _ _ (by decide)).set_right _ _ (by decide)
    · norm_env
      rw [hcv, ← hgo, show 2 ^ g.t - 2 - j = (2 ^ g.t - 2 - (j + 1)) + 1 by omega]
      rfl
    · norm_env; exact hclt
    · norm_env; rw [hcJ]
  case stop =>
    rintro b ⟨hf, -, -, hJ⟩
    have hgb : Glob g b := hg.of_fr hf (by decide)
    simp [Cnd.eval, hJ, hgb.exp]
  case init =>
    refine ⟨((Fr.refl finvS a).set_right _ _ (by decide)).set_right _ _ (by decide), ?_, ?_, ?_⟩
    all_goals norm_env
    · simp [finv]
    · exact hone

end NearCubicGates.Adapters.Amplification.Enc
