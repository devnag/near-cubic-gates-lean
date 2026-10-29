import SourceAdapters.Amplification.EncSearch

/-!
# Reading the request: the unary prefix and the framed numbers `k`, `n` (X9 input, `app:sources`, "Full-range amplification interface")

The cell program of X9 reads the word `1^L ++ false :: frame (binary k) ++ frame (binary n) ++ table`
(`skipP`: skip the prefix that sets the width; `parseP`: read one framed number, bits low first, into `PV`).
-/

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Adapters.Amplification.Enc

open NearCubicGates.Close.Cells NearCubicWires NearCubicWires.RepairOrdinary

/-! ## Binary digits -/

theorem bits_cons (x : ℕ) (hx : x ≠ 0) : x.bits = decide (x % 2 = 1) :: (x / 2).bits := by
  have e : Nat.bit (decide (x % 2 = 1)) (x / 2) = x := by
    rw [Nat.bit_val]; rcases Nat.mod_two_eq_zero_or_one x with h | h <;> simp [h] <;> omega
  conv_lhs => rw [← e]
  rw [Nat.bits_append_bit]
  intro h; by_contra h2; simp at h2; omega

theorem getD_bits (x j : ℕ) : x.bits.getD j false = x.testBit j := by
  induction x using Nat.strong_induction_on generalizing j with
  | _ x ih =>
    rcases Nat.eq_zero_or_pos x with rfl | hx
    · simp
    · rw [bits_cons x (by omega)]
      cases j with
      | zero => simp [Nat.testBit_zero]
      | succ j =>
        have := ih (x / 2) (by omega) j
        rw [List.getD_cons_succ, this, Nat.testBit_succ]

theorem frame_getD_even (l : List Bool) (j : ℕ) : (frame l).getD (2 * j) false = decide (j < l.length) := by
  induction l generalizing j with
  | nil => cases j <;> simp [frame]
  | cons b l ih =>
    cases j with
    | zero => simp [frame]
    | succ j =>
      have : 2 * (j + 1) = 2 * j + 2 := by ring
      rw [this]; simp only [frame, List.getD_cons_succ, ih, List.length_cons]; simp

theorem frame_getD_odd (l : List Bool) (j : ℕ) (hj : j < l.length) :
    (frame l).getD (2 * j + 1) false = l.getD j false := by
  induction l generalizing j with
  | nil => simp at hj
  | cons b l ih =>
    cases j with
    | zero => simp [frame]
    | succ j =>
      have : 2 * (j + 1) + 1 = 2 * j + 1 + 2 := by ring
      rw [this]; simp only [frame, List.getD_cons_succ]
      exact ih j (by simpa using hj)

theorem mod_two_pow_succ' (x j : ℕ) : x % 2 ^ (j + 1) = x % 2 ^ j + 2 ^ j * (if x.testBit j then 1 else 0) := by
  rw [Nat.mod_pow_succ, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ j) with h | h <;> simp [h]

/-! ## Skipping the unary prefix -/

abbrev vR0 : Var := 80

def skipP : Sc := .seq (.op (.rdI vR0)) (.loop (.eq vR0 vONE) (.op (.rdI vR0)))

theorem skipP_spec (C : Ctx) (L : ℕ) (rest : List Bool) (hin : C.inp = List.replicate L true ++ false :: rest)
    (a : Ds) (hc : Consts a) (hip : a.ip = 0) :
    ∃ b, Ex C skipP a b (L * 3 + 4) ∧ FrI [vR0] [] a b ∧ b.ip = L + 1 := by
  have hget : ∀ j, j ≤ L → C.inp.getD j false = decide (j < L) := by
    intro j hj
    rw [hin]
    rcases Nat.lt_or_ge j L with h | h
    · rw [List.getD_append _ _ _ _ (by simpa using h)]; simp [h]
    · have : j = L := by omega
      subst this; rw [List.getD_append_right _ _ _ _ (by simp)]; simp
  have hlen : L < C.inp.length := by rw [hin]; simp
  have e0 : Ex C (.op (.rdI vR0)) a { a.set vR0 (bitOf C.inp a.ip) with ip := a.ip + 1 } 1 :=
    Ex.op (OpEx.rdI vR0 a (by rw [hip]; omega))
  have hinit : FrI [vR0] [] a { a.set vR0 (bitOf C.inp a.ip) with ip := a.ip + 1 } ∧
      ({ a.set vR0 (bitOf C.inp a.ip) with ip := a.ip + 1 } : Ds).ip = 0 + 1 ∧
      ({ a.set vR0 (bitOf C.inp a.ip) with ip := a.ip + 1 } : Ds).env vR0 = if 0 < L then 1 else 0 := by
    refine ⟨FrI.rd _ a vR0 (by decide) _ _, by simp [hip], ?_⟩
    simp only [DS.set_env_self]
    rw [bitOf, hip, hget 0 (by omega)]
    by_cases h : 0 < L <;> simp [h]
  have hstop : ∀ b : Ds, (FrI [vR0] [] a b ∧ b.ip = L + 1 ∧ b.env vR0 = if L < L then 1 else 0) →
      (Cnd.eq vR0 vONE).eval b = false := by
    rintro b ⟨hf, -, hR⟩
    have hc1 : b.env vONE = 1 := (hf.env vONE (by decide)).trans hc.2.1
    simp [Cnd.eval, hR, hc1]
  have hstep : ∀ j < L, ∀ b : Ds, (FrI [vR0] [] a b ∧ b.ip = j + 1 ∧ b.env vR0 = if j < L then 1 else 0) →
      (Cnd.eq vR0 vONE).eval b = true ∧ ∃ b', Ex C (.op (.rdI vR0)) b b' 1 ∧
        (FrI [vR0] [] a b' ∧ b'.ip = (j + 1) + 1 ∧ b'.env vR0 = if j + 1 < L then 1 else 0) := by
    rintro j hj b ⟨hf, hbip, hR⟩
    have hc1 : b.env vONE = 1 := (hf.env vONE (by decide)).trans hc.2.1
    refine ⟨by simp [Cnd.eval, hR, hc1, hj], _, Ex.op (OpEx.rdI vR0 b (by rw [hbip]; omega)), ?_, ?_, ?_⟩
    · exact hf.trans0 (FrI.rd _ b vR0 (by decide) _ _)
    · simp [hbip]
    · simp only [DS.set_env_self]
      rw [bitOf, hbip, hget (j + 1) (by omega)]
      by_cases h : j + 1 < L <;> simp [h]
  obtain ⟨b, eb, hb⟩ := ex_loopN (C := C) (c := .eq vR0 vONE) (body := .op (.rdI vR0)) (by unfold Cnd.wf; decide)
    L 1 (fun j b => FrI [vR0] [] a b ∧ b.ip = j + 1 ∧ b.env vR0 = if j < L then 1 else 0) hstep hstop _ hinit
  exact ⟨b, (Ex.seq e0 eb).mono (by omega), hb.1, hb.2.1⟩

/-! ## Reading a framed number -/

abbrev vPV : Var := 81
abbrev vPW : Var := 82
abbrev vPM : Var := 83
abbrev vPB : Var := 84
abbrev vPQ : Var := 85

def parseS : List Var := [vPV, vPW, vPM, vPB, vPQ]

def parseBody : Sc :=
  .seq (.op (.rdI vPB)) <| .seq (.ite (.eq vPB vONE) (.op (.add vPV vPW)) (.op (.zero vPQ))) <|
  .seq (.op (.shl vPW)) (.op (.rdI vPM))

def parseP : Sc := .seq (.op (.zero vPV)) <| .seq (.op (.copy vPW vONE)) <| .seq (.op (.rdI vPM)) <|
  .loop (.eq vPM vONE) parseBody

theorem parseP_spec (C : Ctx) (x s : ℕ) (pre rest : List Bool) (hin : C.inp = pre ++ frame x.bits ++ rest)
    (hs : pre.length = s) (hW : x.size + 2 ≤ C.Wd) (a : Ds) (hc : Consts a) (hip : a.ip = s) :
    ∃ b, Ex C parseP a b (x.size * 10 + 10) ∧ FrI parseS [] a b ∧ b.ip = s + 2 * x.size + 1 ∧ b.env vPV = x := by
  have hlen : x.bits.length = x.size := Nat.size_eq_bits_len x
  have hget : ∀ i, i ≤ 2 * x.size → C.inp.getD (s + i) false = (frame x.bits).getD i false := by
    intro i hi
    rw [hin, List.append_assoc, List.getD_append_right _ _ _ _ (by omega), hs, Nat.add_sub_cancel_left,
      List.getD_append _ _ _ _ (by rw [frame_length]; omega)]
  have hinlen : s + 2 * x.size < C.inp.length := by
    rw [hin]; simp only [List.length_append, frame_length]; omega
  have hpw : ∀ j, j ≤ x.size → 2 ^ j < 2 ^ C.Wd := fun j hj => Nat.pow_lt_pow_right (by norm_num) (by omega)
  set Inv : ℕ → Ds → Prop := fun j b => FrI parseS [] a b ∧ b.ip = s + 2 * j + 1 ∧ b.env vPV = x % 2 ^ j ∧
      b.env vPW = 2 ^ j ∧ b.env vPM = if j < x.size then 1 else 0 with hInv
  set a1 : Ds := (a.set vPV 0).set vPW ((a.set vPV 0).env vONE) with ha1
  have ha1ip : a1.ip = s := by simp [a1, DS.set, hip]
  set a2 : Ds := { a1.set vPM (bitOf C.inp a1.ip) with ip := a1.ip + 1 } with ha2
  have hinit : Inv 0 a2 := by
    refine ⟨?_, by simp [a2, ha1ip], ?_, ?_, ?_⟩
    · exact ((((Fr.refl parseS a).set_right vPV 0 (by decide)).set_right vPW _ (by decide)).toI).trans0
        (FrI.rd parseS a1 vPM (by decide) _ _)
    · simp (config := { decide := true }) [a2, a1, env_set, Nat.mod_one]
    · simp (config := { decide := true }) [a2, a1, env_set, hc.2.1]
    · simp (config := { decide := true }) only [a2, env_set, ite_true]
      rw [bitOf, ha1ip, show s = s + 2 * 0 by simp, hget _ (by omega), frame_getD_even, hlen]
      by_cases h : 0 < x.size <;> simp [h]
  have hstop : ∀ b, Inv x.size b → (Cnd.eq vPM vONE).eval b = false := by
    rintro b ⟨hf, -, -, -, hM⟩
    have hc1 : b.env vONE = 1 := (hf.env vONE (by decide)).trans hc.2.1
    simp [Cnd.eval, hM, hc1]
  have hstep : ∀ j < x.size, ∀ b, Inv j b → (Cnd.eq vPM vONE).eval b = true ∧
      ∃ b', Ex C parseBody b b' 8 ∧ Inv (j + 1) b' := by
    rintro j hj b ⟨hf, hbip, hV, hW', hM⟩
    have hc1 : b.env vONE = 1 := (hf.env vONE (by decide)).trans hc.2.1
    refine ⟨by simp [Cnd.eval, hM, hc1, hj], ?_⟩
    have hbit : bitOf C.inp b.ip = if x.testBit j then 1 else 0 := by
      rw [bitOf, hbip, show s + 2 * j + 1 = s + (2 * j + 1) by ring, hget _ (by omega),
        frame_getD_odd _ _ (by omega), getD_bits]
      cases x.testBit j <;> rfl
    set b1 : Ds := { b.set vPB (bitOf C.inp b.ip) with ip := b.ip + 1 } with hb1
    have e1 : Ex C (.op (.rdI vPB)) b b1 1 := Ex.op (OpEx.rdI vPB b (by rw [hbip]; omega))
    have hVlt : x % 2 ^ j < 2 ^ j := Nat.mod_lt _ (Nat.two_pow_pos j)
    obtain ⟨b2, e2, hb2V, hb2f, hb2ip, hb2W⟩ : ∃ b2, Ex C (.ite (.eq vPB vONE) (.op (.add vPV vPW)) (.op (.zero vPQ)))
        b1 b2 2 ∧ b2.env vPV = x % 2 ^ (j + 1) ∧ FrI parseS [] b1 b2 ∧ b2.ip = b1.ip ∧ b2.env vPW = 2 ^ j := by
      by_cases hx : x.testBit j
      · refine ⟨_, Ex.iteT (by unfold Cnd.wf; decide)
          (by simp (config := { decide := true }) [Cnd.eval, b1, env_set, hbit, hx, hc1])
          (Ex.op (OpEx.add vPV vPW b1 (by decide) ?_)), ?_, ?_, ?_, ?_⟩
        · simp (config := { decide := true }) [b1, env_set, hV, hW']
          have := hpw (j + 1) (by omega); rw [pow_succ] at this; omega
        · simp (config := { decide := true }) [b1, env_set, hV, hW', mod_two_pow_succ', hx]
        · exact (Fr.set parseS b1 vPV _ (by decide)).toI
        · simp [DS.set]
        · simp (config := { decide := true }) [b1, env_set, hW']
      · refine ⟨_, Ex.iteF (by unfold Cnd.wf; decide)
          (by simp (config := { decide := true }) [Cnd.eval, b1, env_set, hbit, hx, hc1])
          (Ex.op (OpEx.zero vPQ b1)), ?_, ?_, ?_, ?_⟩
        · simp (config := { decide := true }) [b1, env_set, hV, mod_two_pow_succ', hx]
        · exact (Fr.set parseS b1 vPQ _ (by decide)).toI
        · simp [DS.set]
        · simp (config := { decide := true }) [b1, env_set, hW']
    have e3 : Ex C (.op (.shl vPW)) b2 (b2.set vPW (2 * b2.env vPW)) 1 :=
      Ex.op (OpEx.shl vPW b2 (by rw [hb2W]; have := hpw (j + 1) (by omega); rw [pow_succ] at this; omega))
    set b3 := b2.set vPW (2 * b2.env vPW) with hb3
    have hb3ip : b3.ip = s + 2 * j + 2 := by simp [b3, DS.set, hb2ip, b1, hbip]
    have e4 : Ex C (.op (.rdI vPM)) b3 { b3.set vPM (bitOf C.inp b3.ip) with ip := b3.ip + 1 } 1 :=
      Ex.op (OpEx.rdI vPM b3 (lt_of_eq_of_lt hb3ip (by omega)))
    refine ⟨_, (Ex.seq e1 (Ex.seq e2 (Ex.seq e3 e4))).mono (by omega), ?_, ?_, ?_, ?_, ?_⟩
    · exact (((hf.trans0 (FrI.rd parseS b vPB (by decide) _ _)).trans0 hb2f).trans0
        (Fr.set parseS b2 vPW _ (by decide)).toI).trans0 (FrI.rd parseS b3 vPM (by decide) _ _)
    · simp only; rw [hb3ip]; ring
    · simp (config := { decide := true }) [b3, env_set, hb2V]
    · simp (config := { decide := true }) [b3, env_set, hb2W, pow_succ]; ring
    · simp (config := { decide := true }) only [b3, env_set, ite_true, ite_false]
      rw [bitOf, hb3ip, show s + 2 * j + 2 = s + 2 * (j + 1) by ring, hget _ (by omega), frame_getD_even, hlen]
      by_cases h : j + 1 < x.size <;> simp [h]
  obtain ⟨b, eb, hb⟩ := ex_loopN (C := C) (c := .eq vPM vONE) (body := parseBody) (by unfold Cnd.wf; decide)
    x.size 8 Inv hstep hstop a2 hinit
  refine ⟨b, ?_, hb.1, hb.2.1, ?_⟩
  · have e := Ex.seq (Ex.op (OpEx.zero vPV a)) (Ex.seq (Ex.op (OpEx.copy vPW vONE _ (by decide)))
      (Ex.seq (Ex.op (OpEx.rdI vPM a1 (by rw [ha1ip]; omega))) eb))
    exact e.mono (by nlinarith)
  · rw [hb.2.2.1, Nat.mod_eq_of_lt (Nat.lt_size_self x)]

end NearCubicGates.Adapters.Amplification.Enc
