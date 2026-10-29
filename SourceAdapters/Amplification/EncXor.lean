import SourceAdapters.Amplification.EncCell

/-!
# Bitwise exclusive or in the cell language (field addition of X3, proof of `thm:short-pcp-ours`)

`xorP`: `XR := XA ^^^ XB` over the low `TB` bits (`TB` holds the bit count), by halving both operands and adding
`2^j` to `XR` when the `j`-th bits differ. `xorP_spec`; the operands and the scratch variables `xorS` are
overwritten.
-/

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Adapters.Amplification.Enc

open NearCubicGates.Close.Cells

/-! ## The variable bank (shared constants and globals) -/

abbrev vZ : Var := 0
abbrev vONE : Var := 1
abbrev vTWO : Var := 2
/-- The bit count of the field words plus one (`t + 1`). -/
abbrev vTB : Var := 4

/-- The constants are in place. -/
def Consts (a : Ds) : Prop := a.env vZ = 0 ∧ a.env vONE = 1 ∧ a.env vTWO = 2

theorem Consts.of_fr {S : List Var} {w : List Bool} {a b : Ds} (h : Consts a) (hf : Fr S w a b)
    (hS : vZ ∉ S ∧ vONE ∉ S ∧ vTWO ∉ S) : Consts b :=
  ⟨(hf.env _ hS.1).trans h.1, (hf.env _ hS.2.1).trans h.2.1, (hf.env _ hS.2.2).trans h.2.2⟩

/-! ## Exclusive or -/

abbrev vXA : Var := 20
abbrev vXB : Var := 21
abbrev vXR : Var := 22
abbrev vXQ : Var := 23
abbrev vXRa : Var := 24
abbrev vXRb : Var := 25
abbrev vXPW : Var := 26
abbrev vXK : Var := 27

/-- The variables `xorP` writes. -/
def xorS : List Var := [vXA, vXB, vXR, vXQ, vXRa, vXRb, vXPW, vXK]

def xorBody : Sc :=
  .seq (.op (.dm vXA vTWO vXQ vXRa)) <| .seq (.op (.copy vXA vXQ)) <|
  .seq (.op (.dm vXB vTWO vXQ vXRb)) <| .seq (.op (.copy vXB vXQ)) <|
  .seq (.ite (.eq vXRa vXRb) (.op (.zero vXQ)) (.op (.add vXR vXPW))) <|
  .seq (.op (.shl vXPW)) (.op (.inc vXK))

def xorP : Sc :=
  .seq (.op (.zero vXR)) <| .seq (.op (.zero vXK)) <| .seq (.op (.copy vXPW vONE)) <|
  .loop (.lt vXK vTB) xorBody

theorem xor_mod_succ (X Y j : ℕ) :
    (X ^^^ Y) % 2 ^ (j + 1) = (X ^^^ Y) % 2 ^ j + if X / 2 ^ j % 2 = Y / 2 ^ j % 2 then 0 else 2 ^ j := by
  rw [Nat.mod_pow_succ]
  have hb : (X ^^^ Y) / 2 ^ j % 2 = if X / 2 ^ j % 2 = Y / 2 ^ j % 2 then 0 else 1 := by
    have h := Nat.testBit_xor X Y j
    rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq] at h
    rcases Nat.mod_two_eq_zero_or_one (X / 2 ^ j) with hx | hx <;>
    rcases Nat.mod_two_eq_zero_or_one (Y / 2 ^ j) with hy | hy <;>
    rcases Nat.mod_two_eq_zero_or_one ((X ^^^ Y) / 2 ^ j) with hz | hz <;> simp_all
  rw [hb]; split_ifs <;> ring

/-- The state of `xorP` before round `j`. -/
def XorInv (a0 : Ds) (X Y j : ℕ) (b : Ds) : Prop :=
  Fr xorS [] a0 b ∧ b.env vXA = X / 2 ^ j ∧ b.env vXB = Y / 2 ^ j ∧ b.env vXR = (X ^^^ Y) % 2 ^ j ∧
    b.env vXPW = 2 ^ j ∧ b.env vXK = j

theorem two_pow_lt_two_pow {j N W : ℕ} (hj : j < N) (hW : N + 2 ≤ W) : 2 * 2 ^ j < 2 ^ W := by
  have : 2 ^ (j + 1) ≤ 2 ^ N := Nat.pow_le_pow_right (by norm_num) (by omega)
  have : 2 ^ N < 2 ^ W := Nat.pow_lt_pow_right (by norm_num) (by omega)
  rw [pow_succ] at *; omega

theorem xorBody_spec (C : Ctx) (a0 b : Ds) (X Y j NB : ℕ) (hj : j < NB) (hW : NB + 2 ≤ C.Wd)
    (hTWO : b.env vTWO = 2) (hinv : XorInv a0 X Y j b) : Runs C xorBody b 20 xorS [] (XorInv a0 X Y (j + 1)) := by
  obtain ⟨hf, hA, hB, hR, hPW, hK⟩ := hinv
  have hW4 : 2 * 2 ≤ 2 ^ C.Wd := by
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show 2 ≤ C.Wd by omega); simpa using this
  have hRlt : (X ^^^ Y) % 2 ^ j < 2 ^ j := Nat.mod_lt _ (Nat.two_pow_pos j)
  have hpj := two_pow_lt_two_pow hj hW
  have hjW : j + 1 < 2 ^ C.Wd := by
    have := Nat.lt_two_pow_self (n := C.Wd); omega
  refine Runs.op1 (run_dm C xorS b vXA vTWO vXQ vXRa (by decide) (by decide) (by decide) (by rw [hTWO]; norm_num)
    (by rw [hTWO]; exact hW4)) ?_ (by norm_num)
  norm_env
  refine Runs.op1 (run_copy C xorS _ vXA vXQ (by decide) (by decide)) ?_ (by norm_num)
  norm_env
  refine Runs.op1 (run_dm C xorS _ vXB vTWO vXQ vXRb (by decide) (by decide) (by decide)
    (by simp (config := { decide := true }) [DS.set, hTWO])
    (by simpa (config := { decide := true }) [DS.set, hTWO] using hW4)) ?_ (by norm_num)
  norm_env
  refine Runs.op1 (run_copy C xorS _ vXB vXQ (by decide) (by decide)) ?_ (by norm_num)
  norm_env
  by_cases hbit : X / 2 ^ j % 2 = Y / 2 ^ j % 2
  · refine Runs.call (Runs.iteT (by unfold Cnd.wf; decide)
      (by simp (config := { decide := true }) [Cnd.eval, DS.set, hA, hB, hTWO, hbit])
      (run_zero C xorS _ vXQ (by decide))) ?_ (by norm_num)
    rintro _ - rfl
    refine Runs.op1 (run_shl C xorS _ vXPW (by decide) (by simp (config := { decide := true }) [DS.set, hPW]; omega))
      ?_ (by norm_num)
    norm_env
    refine Runs.last (run_inc C xorS _ vXK (by decide) (by simp (config := { decide := true }) [DS.set, hK]; omega))
      ?_ (by norm_num)
    intro _
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · repeat (first | exact hf | refine Fr.set_right ?_ _ _ (by decide))
    all_goals simp (config := { decide := true }) [DS.set, hA, hB, hR, hPW, hK, hTWO, Nat.div_div_eq_div_mul,
      ← pow_succ, xor_mod_succ, hbit]
    all_goals ring
  · refine Runs.call (Runs.iteF (by unfold Cnd.wf; decide)
      (by simp (config := { decide := true }) [Cnd.eval, DS.set, hA, hB, hTWO, hbit])
      (run_add C xorS _ vXR vXPW (by decide) (by decide)
        (by simp (config := { decide := true }) [DS.set, hR, hPW]; omega))) ?_ (by norm_num)
    rintro _ - rfl
    refine Runs.op1 (run_shl C xorS _ vXPW (by decide) (by simp (config := { decide := true }) [DS.set, hPW]; omega))
      ?_ (by norm_num)
    norm_env
    refine Runs.last (run_inc C xorS _ vXK (by decide) (by simp (config := { decide := true }) [DS.set, hK]; omega))
      ?_ (by norm_num)
    intro _
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · repeat (first | exact hf | refine Fr.set_right ?_ _ _ (by decide))
    all_goals simp (config := { decide := true }) [DS.set, hA, hB, hR, hPW, hK, hTWO, Nat.div_div_eq_div_mul,
      ← pow_succ, xor_mod_succ, hbit]
    all_goals ring

theorem xorP_spec (C : Ctx) (a : Ds) (hc : Consts a) (NB : ℕ) (hNB : a.env vTB = NB) (X Y : ℕ)
    (hX : a.env vXA = X) (hY : a.env vXB = Y) (hXb : X < 2 ^ NB) (hYb : Y < 2 ^ NB) (hW : NB + 2 ≤ C.Wd) :
    Runs C xorP a (25 * NB + 10) xorS [] (fun b => b.env vXR = X ^^^ Y) := by
  obtain ⟨hz, h1, h2⟩ := hc
  have hW2 : 2 ^ (NB + 2) ≤ 2 ^ C.Wd := Nat.pow_le_pow_right (by norm_num) hW
  have hp : ∀ j ≤ NB, 2 ^ j ≤ 2 ^ NB := fun j hj => Nat.pow_le_pow_right (by norm_num) hj
  have hNB4 : 4 * 2 ^ NB = 2 ^ (NB + 2) := by rw [pow_add]; ring
  refine Runs.costLe ?_ (show 1 + (1 + (1 + (NB * (20 + 2) + 2) + 1) + 1) + 1 ≤ 25 * NB + 10 by omega)
  refine Runs.step0 (run_zero C xorS a vXR (by decide)) ?_
  refine Runs.step0 (run_zero C xorS _ vXK (by decide)) ?_
  refine Runs.step0 (run_copy C xorS _ vXPW vONE (by decide) (by decide)) ?_
  have hinit : XorInv a X Y 0 (((a.set vXR 0).set vXK 0).set vXPW (((a.set vXR 0).set vXK 0).env vONE)) := by
    refine ⟨((Fr.set xorS a vXR 0 (by decide)).trans (Fr.set xorS _ vXK 0 (by decide))).trans
      (Fr.set xorS _ vXPW _ (by decide)), ?_, ?_, ?_, ?_, ?_⟩ <;> simp (config := { decide := true }) [DS.set, hX, hY, h1, Nat.mod_one]
  have hloop := Runs.loopN0 (C := C) (c := .lt vXK vTB) (body := xorBody) (S := xorS) (by unfold Cnd.wf; decide)
    NB 20 (XorInv a X Y) ?_ ?_ _ hinit
  · refine hloop.mono le_rfl (List.Subset.refl _) ?_
    rintro b - ⟨-, -, -, hR, -, -⟩
    rw [hR, Nat.mod_eq_of_lt (Nat.xor_lt_two_pow hXb hYb)]
  · rintro j hj b ⟨hf, hA, hB, hR, hPW, hK⟩
    have hTB : b.env vTB = NB := (hf.env vTB (by decide)).trans hNB
    have hTWO : b.env vTWO = 2 := (hf.env vTWO (by decide)).trans h2
    refine ⟨by simp [Cnd.eval, hK, hTB, hj], ?_⟩
    exact xorBody_spec C a b X Y j NB hj hW hTWO ⟨hf, hA, hB, hR, hPW, hK⟩
  · rintro b ⟨hf, -, -, -, -, hK⟩
    have hTB : b.env vTB = NB := (hf.env vTB (by decide)).trans hNB
    simp [Cnd.eval, hK, hTB]

end NearCubicGates.Adapters.Amplification.Enc
