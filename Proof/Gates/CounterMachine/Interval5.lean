import Proof.Gates.CounterMachine.Interval4

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.CounterMachine
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Interfaces (ratWord outputWord)

variable {ns nr : ℕ}

/-! ## Cost class -/

/-- The class bound of the interval machine. -/
def ivlBound (W k n : ℕ) : ℕ := 2000 * (W + k + n + 1) ^ 2

theorem natReadCost_le (W v : ℕ) (hW : 1 ≤ W) (hv : v < 2 ^ W) : natReadCost W v ≤ 60 * (W + 1) := by
  have := NearCubicWires.WireExponent3_5.CompilerMachine.Pool.natBitLength_le v W hW hv
  unfold natReadCost NearCubicWires.WireExponent3_5.CompilerMachine.Pool.convCost; omega

theorem ivlReadCost_le (W S U : ℕ) (hS : S < 2 ^ W) (hU : U < 2 ^ W) (h1 : 1 < 2 ^ W) :
    readCost W S U ≤ 300 * (W + 1) := by
  have hW : 1 ≤ W := by
    rcases Nat.eq_zero_or_pos W with h0 | h0
    · subst h0; simp at h1
    · exact h0
  have a := natReadCost_le W 0 hW (by positivity)
  have b := natReadCost_le W S hW hS
  have c := natReadCost_le W 1 hW h1
  have d := natReadCost_le W U hW hU
  unfold readCost; omega

theorem arithCost_le (W k : ℕ) : arithCost W k ≤ 200 * (W + k + 1) ^ 2 := by
  unfold arithCost
  have : (k - 1) * (41 * W + 8 + 1 + 1 + 2) ≤ k * (41 * W + 12) := Nat.mul_le_mul_right _ (Nat.sub_le k 1)
  nlinarith

theorem redCost_le (W a e : ℕ) : redCost W a e ≤ 100 * (W + e + 1) ^ 2 := by
  unfold redCost
  have := steps_le a e
  have : steps a e * (34 * W + 20 + 2) ≤ (e + 1) * (34 * W + 22) := Nat.mul_le_mul_right _ this
  nlinarith

theorem ratCost_le (W e : ℕ) (he : e < W) : ratCost W e ≤ 300 * (W + 1) ^ 2 := by
  unfold ratCost powCost NearCubicWires.WireExponent3_5.FinalPass.Out.P5.pnCost
  have : e * (41 * W + 8 + 1 + 1 + 2) ≤ W * (41 * W + 12) := Nat.mul_le_mul_right _ he.le
  nlinarith

section IvlTop
variable (P : Fin 12 ↪ Fin (ns + 1)) (Q : Fin 20 ↪ Fin nr)

def ivlP : WMX ns nr :=
  .seq (readP P Q) (.seq (arithP P Q) (.seq (addR (Q 10) (Q 17) (Q 14)) (.seq (redP (P 1) (Q 17) (Q 19) (Q 16))
  (.seq (ratP P Q 1) (.seq (addR (Q 10) (Q 17) (Q 14)) (.seq (redP (P 2) (Q 17) (Q 19) (Q 16))
  (.seq (ratP P Q 2) (rewP P Q))))))))

/-- The interval machine at rest before the run. -/
structure IvlPre (cap W kc S U k n : ℕ) (rest : List Bool) (σ : WState ns nr) : Prop where
  hW : 1 ≤ W
  hkc : W ≤ kc
  fit : S + 2 ^ (k - 1) * U < 2 ^ W
  hn : n < W
  inp : σ.st (P 4) = ratWord (S : ℚ) ++ natWord U ++ rest
  inph : σ.sh (P 4) = 0
  ruler : σ.st (P 5) = false :: List.replicate kc true
  rulerh : σ.sh (P 5) = 0
  out : σ.st (P 0) = []
  outh : σ.sh (P 0) = 0
  w1 : NumOn σ (P 1) W 0
  w2 : NumOn σ (P 2) W 0
  w3 : NumOn σ (P 3) W 0
  w6 : NumOn σ (P 6) W 0
  w7 : NumOn σ (P 7) W 0
  pr : PrRegs Q W σ
  r10 : σ.val (Q 10) = n
  r11 : σ.val (Q 11) = k
  r12 : σ.val (Q 12) = 0
  r13 : σ.val (Q 13) = 2 * W + 1
  r14 : σ.val (Q 14) = 0
  r15 : σ.val (Q 15) = 0
  r16 : σ.val (Q 16) = 0
  r17 : σ.val (Q 17) = 0
  r18 : σ.val (Q 18) = 0
  r19 : σ.val (Q 19) = 0
  cap : 12 * W + 2 * k + n + 20 ≤ cap

theorem ivlP_run (cap W kc S U k n : ℕ) (rest : List Bool) (σ : WState ns nr) (h : IvlPre P Q cap W kc S U k n rest σ) :
    ∃ τ c, WXExec cap (ivlP P Q) σ τ c ∧ c ≤ ivlBound W k n ∧ τ.st (P 0) = outputWord (ivl S U k n) ∧ τ.sh (P 0) = 0 ∧
      τ.sh (P 4) = 0 ∧ τ.val = σ.val ∧
      (∀ j, (∀ i : Fin 12, i ∈ ([0, 1, 2, 3, 4, 6, 7] : List (Fin 12)) → P i ≠ j) → τ.st j = σ.st j ∧ τ.sh j = σ.sh j) ∧
      τ.st (P 4) = σ.st (P 4) ∧ τ.cell = σ.cell := by
  have pne : ∀ {a b : Fin 12}, a ≠ b → P a ≠ P b := fun h => P.injective.ne h
  have qne : ∀ {a b : Fin 20}, a ≠ b → Q a ≠ Q b := fun h => Q.injective.ne h
  set T := 2 ^ (k - 1) * U with hT
  have hSW : S < 2 ^ W := by have := h.fit; omega
  have hUW : U < 2 ^ W := by
    have h1 : U ≤ T := Nat.le_mul_of_pos_left _ (by positivity)
    have := h.fit; omega
  have hTW : T < 2 ^ W := by have := h.fit; omega
  have h1W : 1 < 2 ^ W := Nat.one_lt_two_pow (by have := h.hW; omega)
  -- read
  have e1 := readP_spec P Q cap W kc S U 0 rest σ h.hW hSW hUW h1W h.hkc h.inp h.inph h.ruler h.rulerh h.w1 h.w2 h.w6 h.w7
    h.r12 h.r13 h.r14 h.r15 h.r16 (by have := h.cap; omega)
  set σR := (((σ.sets (P 1) (frame (binary W S))).sets (P 6) (frame (binary W U))).sets (P 7)
      (frame (binary W 0))).seth (P 4) (ratWord (S : ℚ) ++ natWord U).length with hσR
  have vR : σR.val = σ.val := by simp [hσR]
  -- arithmetic
  have e2 := arithP_spec P Q cap W k S U 0 0 σR
    ⟨by simp [hσR, Function.update_of_ne (pne (show (1 : Fin 12) ≠ 7 by decide)),
      Function.update_of_ne (pne (show (1 : Fin 12) ≠ 6 by decide))], by simp [hσR, Function.update_of_ne
      (pne (show (1 : Fin 12) ≠ 4 by decide)), h.w1.2]⟩
    ⟨by simp [hσR, Function.update_of_ne (pne (show (2 : Fin 12) ≠ 7 by decide)),
      Function.update_of_ne (pne (show (2 : Fin 12) ≠ 6 by decide)), Function.update_of_ne
      (pne (show (2 : Fin 12) ≠ 1 by decide)), h.w2.1], by simp [hσR, Function.update_of_ne
      (pne (show (2 : Fin 12) ≠ 4 by decide)), h.w2.2]⟩
    ⟨by simp [hσR, Function.update_of_ne (pne (show (6 : Fin 12) ≠ 7 by decide))], by simp [hσR, Function.update_of_ne
      (pne (show (6 : Fin 12) ≠ 4 by decide)), h.w6.2]⟩
    ⟨by simp [hσR], by simp [hσR, Function.update_of_ne (pne (show (7 : Fin 12) ≠ 4 by decide)), h.w7.2]⟩
    (by rw [vR]; exact h.r11) (by rw [vR]; exact h.r14) (by rw [vR]; exact h.r15) (by rw [vR]; exact h.r16)
    (by rw [vR]; exact h.r18) h.fit (by have := h.cap; omega)
  set σA := ((σR.sets (P 6) (frame (binary W T))).sets (P 1) (frame (binary W (S + T)))).sets (P 2)
    (frame (binary W T)) with hσA
  have vA : σA.val = σ.val := by simp [hσA, vR]
  -- exponent, reduce the first numerator
  have e3 := addR_spec cap (A := Q 10) (B := Q 17) (T := Q 14) (qne (by decide)) (qne (by decide)) (qne (by decide))
    σA (by rw [vA]; exact h.r14) (by rw [vA, h.r10, h.r17]; have := h.cap; omega)
  rw [vA, h.r10, h.r17, Nat.zero_add] at e3
  have hA1 : NumOn (σA.setv (Q 17) n) (P 1) W (S + T) :=
    ⟨by simp [hσA, Function.update_of_ne (pne (show (1 : Fin 12) ≠ 2 by decide))], by simp [hσA, hσR,
      Function.update_of_ne (pne (show (1 : Fin 12) ≠ 4 by decide)), h.w1.2]⟩
  have e4 := redP_spec (P 1) (Q 17) (Q 19) (Q 16) cap W (qne (by decide)) (qne (by decide)) (qne (by decide))
    (σA.setv (Q 17) n) (S + T) n h.hW h.fit hA1 (by simp)
    (by simp [Function.update_of_ne (qne (show (19 : Fin 20) ≠ 17 by decide)), vA, h.r19])
    (by simp [Function.update_of_ne (qne (show (16 : Fin 20) ≠ 17 by decide)), vA, h.r16]) (by have := h.cap; omega)
  set a1 := (red (S + T) n).1
  set f1 := (red (S + T) n).2
  have ha1 : a1 ≤ S + T := (red_le (S + T) n).1
  have hf1 : f1 ≤ n := (red_le (S + T) n).2
  have hfitT : S + T < 2 ^ W := h.fit
  have ha1W : a1 < 2 ^ W := by omega
  have hf1W : f1 < W := by have := h.hn; omega
  set σ2 := ((σA.setv (Q 17) n).sets (P 1) (frame (binary W a1))).setv (Q 17) f1 with hσ2
  have v2 : σ2.val = Function.update σ.val (Q 17) f1 := by simp [hσ2, vA]
  -- print the first rational
  have e5 := ratP_spec P Q cap W a1 f1 1 (by decide) (by decide) (by decide) σ2 0 0 h.hW ha1W hf1W
    (by simp [hσ2, hσA, hσR, Function.update_of_ne (pne (show (0 : Fin 12) ≠ 4 by decide)),
      Function.update_of_ne (pne (show (0 : Fin 12) ≠ 1 by decide)), Function.update_of_ne
      (pne (show (0 : Fin 12) ≠ 2 by decide)), Function.update_of_ne (pne (show (0 : Fin 12) ≠ 6 by decide)),
      Function.update_of_ne (pne (show (0 : Fin 12) ≠ 7 by decide)), h.out, h.outh])
    ⟨by simp [hσ2], by simp [hσ2, hσA, hσR, Function.update_of_ne (pne (show (1 : Fin 12) ≠ 4 by decide)), h.w1.2]⟩
    ⟨by simp [hσ2, hσA, hσR, Function.update_of_ne (pne (show (3 : Fin 12) ≠ 1 by decide)), Function.update_of_ne
      (pne (show (3 : Fin 12) ≠ 2 by decide)), Function.update_of_ne (pne (show (3 : Fin 12) ≠ 6 by decide)),
      Function.update_of_ne (pne (show (3 : Fin 12) ≠ 7 by decide)), h.w3.1], by simp [hσ2, hσA, hσR,
      Function.update_of_ne (pne (show (3 : Fin 12) ≠ 4 by decide)), h.w3.2]⟩
    ⟨by simp [hσ2, hσA, hσR, Function.update_of_ne (pne (show (7 : Fin 12) ≠ 1 by decide)), Function.update_of_ne
      (pne (show (7 : Fin 12) ≠ 2 by decide)), Function.update_of_ne (pne (show (7 : Fin 12) ≠ 6 by decide))],
      by simp [hσ2, hσA, hσR, Function.update_of_ne (pne (show (7 : Fin 12) ≠ 4 by decide)), h.w7.2]⟩
    ⟨by rw [v2, q10_apply]; simp [Function.update_of_ne (qne (show (Fin.castLE (by norm_num) (2 : Fin 10) : Fin 20) ≠ 17 by decide))]
        exact h.pr.1,
      fun r hr => by
        have hr17 : (Fin.castLE (by norm_num) r : Fin 20) ≠ 17 := by revert r; decide
        rw [v2, q10_apply]; simp [Function.update_of_ne (qne hr17)]; exact h.pr.2 r hr⟩
    (by rw [v2]; simp [Function.update_of_ne (qne (show (12 : Fin 20) ≠ 17 by decide)), h.r12])
    (by rw [v2]; simp [Function.update_of_ne (qne (show (13 : Fin 20) ≠ 17 by decide)), h.r13])
    (by rw [v2]; simp [Function.update_of_ne (qne (show (14 : Fin 20) ≠ 17 by decide)), h.r14])
    (by rw [v2]; simp [Function.update_of_ne (qne (show (15 : Fin 20) ≠ 17 by decide)), h.r15])
    (by rw [v2]; simp [Function.update_of_ne (qne (show (16 : Fin 20) ≠ 17 by decide)), h.r16])
    (by rw [v2]; simp) (by have := h.cap; omega)
  set w1 := natWord 0 ++ natWord a1 ++ natWord (2 ^ f1) with hw1
  set σ3 := (((σ2.sets (P 0) (σ2.st (P 0) ++ w1)).seth (P 0) ((σ2.st (P 0)).length + w1.length)).sets (P 3)
    (frame (binary W 0))).setv (Q 17) 0 with hσ3
  have v3 : σ3.val = σ.val := by
    funext r; by_cases hr : r = Q 17
    · subst hr; simp [hσ3, h.r17]
    · simp [hσ3, hσ2, Function.update_of_ne hr, vA]
  have o3 : σ2.st (P 0) = [] := by
    simp [hσ2, hσA, hσR, Function.update_of_ne (pne (show (0 : Fin 12) ≠ 4 by decide)),
      Function.update_of_ne (pne (show (0 : Fin 12) ≠ 1 by decide)), Function.update_of_ne
      (pne (show (0 : Fin 12) ≠ 2 by decide)), Function.update_of_ne (pne (show (0 : Fin 12) ≠ 6 by decide)),
      Function.update_of_ne (pne (show (0 : Fin 12) ≠ 7 by decide)), h.out]
  -- exponent, reduce the second numerator
  have e6 := addR_spec cap (A := Q 10) (B := Q 17) (T := Q 14) (qne (by decide)) (qne (by decide)) (qne (by decide))
    σ3 (by rw [v3]; exact h.r14) (by rw [v3, h.r10, h.r17]; have := h.cap; omega)
  rw [v3, h.r10, h.r17, Nat.zero_add] at e6
  have hB2 : NumOn (σ3.setv (Q 17) n) (P 2) W T :=
    ⟨by simp [hσ3, hσ2, hσA, Function.update_of_ne (pne (show (2 : Fin 12) ≠ 0 by decide)),
      Function.update_of_ne (pne (show (2 : Fin 12) ≠ 3 by decide)), Function.update_of_ne
      (pne (show (2 : Fin 12) ≠ 1 by decide))],
     by simp [hσ3, hσ2, hσA, hσR, Function.update_of_ne (pne (show (2 : Fin 12) ≠ 0 by decide)),
      Function.update_of_ne (pne (show (2 : Fin 12) ≠ 4 by decide)), h.w2.2]⟩
  have e7 := redP_spec (P 2) (Q 17) (Q 19) (Q 16) cap W (qne (by decide)) (qne (by decide)) (qne (by decide))
    (σ3.setv (Q 17) n) T n h.hW hTW hB2 (by simp)
    (by simp [Function.update_of_ne (qne (show (19 : Fin 20) ≠ 17 by decide)), v3, h.r19])
    (by simp [Function.update_of_ne (qne (show (16 : Fin 20) ≠ 17 by decide)), v3, h.r16]) (by have := h.cap; omega)
  set a2 := (red T n).1
  set f2 := (red T n).2
  have ha2W : a2 < 2 ^ W := lt_of_le_of_lt (red_le T n).1 hTW
  have hf2W : f2 < W := by have := (red_le T n).2; have := h.hn; omega
  set σ5 := ((σ3.setv (Q 17) n).sets (P 2) (frame (binary W a2))).setv (Q 17) f2 with hσ5
  have v5 : σ5.val = Function.update σ.val (Q 17) f2 := by simp [hσ5, v3]
  -- print the second rational
  have e8 := ratP_spec P Q cap W a2 f2 2 (by decide) (by decide) (by decide) σ5 0 0 h.hW ha2W hf2W
    (by simp [hσ5, hσ3, Function.update_of_ne (pne (show (0 : Fin 12) ≠ 2 by decide)),
      Function.update_of_ne (pne (show (0 : Fin 12) ≠ 3 by decide)), o3])
    ⟨by simp [hσ5], by simp [hσ5, hσ3, hσ2, hσA, hσR, Function.update_of_ne (pne (show (2 : Fin 12) ≠ 0 by decide)),
      Function.update_of_ne (pne (show (2 : Fin 12) ≠ 4 by decide)), h.w2.2]⟩
    ⟨by simp [hσ5, hσ3, Function.update_of_ne (pne (show (3 : Fin 12) ≠ 2 by decide))],
     by simp [hσ5, hσ3, hσ2, hσA, hσR, Function.update_of_ne (pne (show (3 : Fin 12) ≠ 0 by decide)),
      Function.update_of_ne (pne (show (3 : Fin 12) ≠ 4 by decide)), h.w3.2]⟩
    ⟨by simp [hσ5, hσ3, hσ2, hσA, hσR, Function.update_of_ne (pne (show (7 : Fin 12) ≠ 1 by decide)),
      Function.update_of_ne (pne (show (7 : Fin 12) ≠ 2 by decide)), Function.update_of_ne
      (pne (show (7 : Fin 12) ≠ 6 by decide)), Function.update_of_ne (pne (show (7 : Fin 12) ≠ 0 by decide)),
      Function.update_of_ne (pne (show (7 : Fin 12) ≠ 3 by decide))],
     by simp [hσ5, hσ3, hσ2, hσA, hσR, Function.update_of_ne (pne (show (7 : Fin 12) ≠ 4 by decide)),
      Function.update_of_ne (pne (show (7 : Fin 12) ≠ 0 by decide)), h.w7.2]⟩
    ⟨by rw [v5, q10_apply]; simp [Function.update_of_ne (qne (show (Fin.castLE (by norm_num) (2 : Fin 10) : Fin 20) ≠ 17 by decide))]
        exact h.pr.1,
      fun r hr => by
        have hr17 : (Fin.castLE (by norm_num) r : Fin 20) ≠ 17 := by revert r; decide
        rw [v5, q10_apply]; simp [Function.update_of_ne (qne hr17)]; exact h.pr.2 r hr⟩
    (by rw [v5]; simp [Function.update_of_ne (qne (show (12 : Fin 20) ≠ 17 by decide)), h.r12])
    (by rw [v5]; simp [Function.update_of_ne (qne (show (13 : Fin 20) ≠ 17 by decide)), h.r13])
    (by rw [v5]; simp [Function.update_of_ne (qne (show (14 : Fin 20) ≠ 17 by decide)), h.r14])
    (by rw [v5]; simp [Function.update_of_ne (qne (show (15 : Fin 20) ≠ 17 by decide)), h.r15])
    (by rw [v5]; simp [Function.update_of_ne (qne (show (16 : Fin 20) ≠ 17 by decide)), h.r16])
    (by rw [v5]; simp) (by have := h.cap; omega)
  set w2 := natWord 0 ++ natWord a2 ++ natWord (2 ^ f2) with hw2
  set σ6 := (((σ5.sets (P 0) (σ5.st (P 0) ++ w2)).seth (P 0) ((σ5.st (P 0)).length + w2.length)).sets (P 3)
    (frame (binary W 0))).setv (Q 17) 0 with hσ6
  have v6 : σ6.val = σ.val := by
    funext r; by_cases hr : r = Q 17
    · subst hr; simp [hσ6, h.r17]
    · simp [hσ6, hσ5, Function.update_of_ne hr, v3]
  -- the lengths
  have nwlen : ∀ v, (natWord v).length = 2 * natBitLength v + 1 := fun v => by simp [natWord]
  have nbl : ∀ v, v < 2 ^ W → natBitLength v ≤ W := fun v hv =>
    NearCubicWires.WireExponent3_5.CompilerMachine.Pool.natBitLength_le v W h.hW hv
  have nb0 : natBitLength 0 = 1 := by simp [natBitLength]
  have h2f1 : 2 ^ f1 < 2 ^ W := Nat.pow_lt_pow_right (by norm_num) hf1W
  have h2f2 : 2 ^ f2 < 2 ^ W := Nat.pow_lt_pow_right (by norm_num) hf2W
  have l1 : w1.length ≤ 3 + 2 * (2 * W + 1) := by
    have := nbl a1 ha1W; have := nbl _ h2f1
    simp only [hw1, List.length_append, nwlen]; omega
  have l2 : w2.length ≤ 3 + 2 * (2 * W + 1) := by
    have := nbl a2 ha2W; have := nbl _ h2f2
    simp only [hw2, List.length_append, nwlen]; omega
  have s0 : σ6.sh (P 0) = w1.length + w2.length := by
    simp [hσ6, hσ5, hσ3, o3, Function.update_of_ne (pne (show (0 : Fin 12) ≠ 2 by decide)),
      Function.update_of_ne (pne (show (0 : Fin 12) ≠ 3 by decide))]
  have s4 : σ6.sh (P 4) = (ratWord (S : ℚ) ++ natWord U).length := by
    simp [hσ6, hσ5, hσ3, hσ2, hσA, hσR, Function.update_of_ne (pne (show (4 : Fin 12) ≠ 0 by decide)),
      Function.update_of_ne (pne (show (4 : Fin 12) ≠ 3 by decide)), Function.update_of_ne
      (pne (show (4 : Fin 12) ≠ 2 by decide)), Function.update_of_ne (pne (show (4 : Fin 12) ≠ 1 by decide)),
      Function.update_of_ne (pne (show (4 : Fin 12) ≠ 6 by decide)), Function.update_of_ne
      (pne (show (4 : Fin 12) ≠ 7 by decide))]
  have lI : (ratWord (S : ℚ) ++ natWord U).length ≤ 6 * (2 * W + 1) := by
    rw [ratWord_nat]; have := nbl S hSW; have := nbl U hUW; have := nbl 1 h1W
    simp only [List.length_append, nwlen]; omega
  have e9 := rewP_spec P Q cap W σ6 (by rw [v6]; exact h.r12) (by rw [v6]; exact h.r13) (by rw [v6]; exact h.r14)
    (by rw [s0]; have := h.hW; omega) (by rw [s4]; exact lI) (by have := h.cap; omega)
  refine ⟨_, _, WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4 (WXExec.seq e5 (WXExec.seq e6
    (WXExec.seq e7 (WXExec.seq e8 e9))))))), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have b1 := ivlReadCost_le W S U hSW hUW h1W
    have b2 := arithCost_le W k
    have b3 := redCost_le W (S + T) n
    have b4 := ratCost_le W f1 hf1W
    have b5 := redCost_le W T n
    have b6 := ratCost_le W f2 hf2W
    unfold ivlBound
    have hn := h.hn
    have hW := h.hW
    set X := W + k + n + 1 with hX
    have hX2 : X ≤ X ^ 2 := by nlinarith
    have q1 : (W + k + 1) ^ 2 ≤ X ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have q2 : (W + n + 1) ^ 2 ≤ X ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have q3 : (W + 1) ^ 2 ≤ X ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have q4 : 4 ≤ X ^ 2 := by nlinarith
    omega
  · simp only [WState.seth_st]
    simp [hσ6, hσ5, hσ3, o3, Function.update_of_ne (pne (show (0 : Fin 12) ≠ 2 by decide)),
      Function.update_of_ne (pne (show (0 : Fin 12) ≠ 3 by decide))]
    rw [outputWord_ivl]
  · simp [Function.update_of_ne (pne (show (0 : Fin 12) ≠ 4 by decide))]
  · simp
  · simp [v6]
  · intro j hj
    have n0 := hj 0 (by simp); have n1 := hj 1 (by simp); have n2 := hj 2 (by simp); have n3 := hj 3 (by simp)
    have n4 := hj 4 (by simp); have n6 := hj 6 (by simp); have n7 := hj 7 (by simp)
    simp [hσ6, hσ5, hσ3, hσ2, hσA, hσR, Function.update_of_ne n0.symm, Function.update_of_ne n1.symm,
      Function.update_of_ne n2.symm, Function.update_of_ne n3.symm, Function.update_of_ne n4.symm,
      Function.update_of_ne n6.symm, Function.update_of_ne n7.symm]
  · simp [hσ6, hσ5, hσ3, hσ2, hσA, hσR, Function.update_of_ne (pne (show (4 : Fin 12) ≠ 0 by decide)),
      Function.update_of_ne (pne (show (4 : Fin 12) ≠ 3 by decide)), Function.update_of_ne
      (pne (show (4 : Fin 12) ≠ 2 by decide)), Function.update_of_ne (pne (show (4 : Fin 12) ≠ 1 by decide)),
      Function.update_of_ne (pne (show (4 : Fin 12) ≠ 6 by decide)), Function.update_of_ne
      (pne (show (4 : Fin 12) ≠ 7 by decide))]
  · simp [hσ6, hσ5, hσ3, hσ2, hσA, hσR]
