import Proof.Gates.CounterMachine.Interval3

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

theorem ratWord_nat (S : ℕ) : ratWord (S : ℚ) = natWord 0 ++ natWord S ++ natWord 1 := by
  unfold ratWord NearCubicGates.Close.Interfaces.intWord
  simp

section Ivl
variable (P : Fin 12 ↪ Fin (ns + 1)) (Q : Fin 20 ↪ Fin nr)

/-- Read the three fields of `ratWord S` and the field `natWord U`. -/
def readP : WMX ns nr :=
  .seq (natRead (P 4) (P 5) (P 7) (Q 12) (Q 13) (Q 14))
  (.seq (natRead (P 4) (P 5) (P 1) (Q 12) (Q 13) (Q 14))
  (.seq (natRead (P 4) (P 5) (P 7) (Q 12) (Q 13) (Q 14))
  (.seq (BinW.zero (P 7) (P 2) (Q 15) (Q 16)) (natRead (P 4) (P 5) (P 6) (Q 12) (Q 13) (Q 14)))))

def readCost (W S U : ℕ) : ℕ :=
  natReadCost W 0 + 1 + (natReadCost W S + 1 + (natReadCost W 1 + 1 + (41 * W + 3 + 1 + natReadCost W U)))

theorem readP_spec (cap W kc S U b : ℕ) (rest : List Bool) (σ : WState ns nr) (hW : 1 ≤ W) (hS : S < 2 ^ W)
    (hU : U < 2 ^ W) (h1 : 1 < 2 ^ W) (hkc : W ≤ kc)
    (hI : σ.st (P 4) = ratWord (S : ℚ) ++ natWord U ++ rest) (hIh : σ.sh (P 4) = 0)
    (hK : σ.st (P 5) = false :: List.replicate kc true) (hKh : σ.sh (P 5) = 0)
    (hA : NumOn σ (P 1) W 0) (hB : NumOn σ (P 2) W b) (hT : NumOn σ (P 6) W 0) (hSc : NumOn σ (P 7) W 0)
    (h12 : σ.val (Q 12) = 0) (h13 : σ.val (Q 13) = 2 * W + 1) (h14 : σ.val (Q 14) = 0) (h15 : σ.val (Q 15) = 0)
    (h16 : σ.val (Q 16) = 0) (hcap : 4 * W + 4 ≤ cap) :
    WXExec cap (readP P Q) σ ((((σ.sets (P 1) (frame (binary W S))).sets (P 6) (frame (binary W U))).sets (P 7)
      (frame (binary W 0))).seth (P 4) (ratWord (S : ℚ) ++ natWord U).length) (readCost W S U) := by
  have pne : ∀ {a b : Fin 12}, a ≠ b → P a ≠ P b := fun h => P.injective.ne h
  have qne : ∀ {a b : Fin 20}, a ≠ b → Q a ≠ Q b := fun h => Q.injective.ne h
  have hbl : ∀ v, v < 2 ^ W → natBitLength v ≤ kc := fun v hv =>
    (NearCubicWires.WireExponent3_5.CompilerMachine.Pool.natBitLength_le v W hW hv).trans hkc
  rw [ratWord_nat] at hI ⊢
  -- field 1: the sign
  have e1 := natRead_spec cap W kc (I := P 4) (K := P 5) (X := P 7) (C := Q 12) (R2 := Q 13) (T := Q 14) (pne (by decide)) (pne (by decide)) (pne (by decide)) (qne (by decide))
    (qne (by decide)) (qne (by decide)) σ [] (natWord S ++ natWord 1 ++ natWord U ++ rest) 0 hW (by positivity)
    (by rw [hI]; simp) hIh hK hKh (hbl 0 (by positivity)) hSc.1 hSc.2 h12 h13 h14 hcap
  set σ1 := (σ.sets (P 7) (frame (binary W 0))).seth (P 4) (([] : List Bool).length + (natWord 0).length) with hσ1
  -- field 2: `S`
  have e2 := natRead_spec cap W kc (I := P 4) (K := P 5) (X := P 1) (C := Q 12) (R2 := Q 13) (T := Q 14) (pne (by decide)) (pne (by decide)) (pne (by decide)) (qne (by decide))
    (qne (by decide)) (qne (by decide)) σ1 (natWord 0) (natWord 1 ++ natWord U ++ rest) S hW hS
    (by simp [hσ1, Function.update_of_ne (pne (show (4 : Fin 12) ≠ 7 by decide)), hI])
    (by simp [hσ1]) (by simp [hσ1, Function.update_of_ne (pne (show (5 : Fin 12) ≠ 7 by decide)), hK])
    (by simp [hσ1, Function.update_of_ne (pne (show (5 : Fin 12) ≠ 4 by decide)), hKh]) (hbl S hS)
    (by simp [hσ1, Function.update_of_ne (pne (show (1 : Fin 12) ≠ 7 by decide)), hA.1])
    (by simp [hσ1, Function.update_of_ne (pne (show (1 : Fin 12) ≠ 4 by decide)), hA.2])
    (by simp [hσ1, h12]) (by simp [hσ1, h13]) (by simp [hσ1, h14]) hcap
  set σ2 := (σ1.sets (P 1) (frame (binary W S))).seth (P 4) ((natWord 0).length + (natWord S).length) with hσ2
  -- field 3: the denominator `1`
  have e3 := natRead_spec cap W kc (I := P 4) (K := P 5) (X := P 7) (C := Q 12) (R2 := Q 13) (T := Q 14) (pne (by decide)) (pne (by decide)) (pne (by decide)) (qne (by decide))
    (qne (by decide)) (qne (by decide)) σ2 (natWord 0 ++ natWord S) (natWord U ++ rest) 1 hW h1
    (by simp [hσ2, hσ1, Function.update_of_ne (pne (show (4 : Fin 12) ≠ 7 by decide)),
      Function.update_of_ne (pne (show (4 : Fin 12) ≠ 1 by decide)), hI])
    (by simp [hσ2]) (by simp [hσ2, hσ1, Function.update_of_ne (pne (show (5 : Fin 12) ≠ 7 by decide)),
      Function.update_of_ne (pne (show (5 : Fin 12) ≠ 1 by decide)), hK])
    (by simp [hσ2, hσ1, Function.update_of_ne (pne (show (5 : Fin 12) ≠ 4 by decide)), hKh]) (hbl 1 h1)
    (by simp [hσ2, hσ1, Function.update_of_ne (pne (show (7 : Fin 12) ≠ 1 by decide))])
    (by simp [hσ2, hσ1, Function.update_of_ne (pne (show (7 : Fin 12) ≠ 4 by decide)), hSc.2])
    (by simp [hσ2, hσ1, h12]) (by simp [hσ2, hσ1, h13]) (by simp [hσ2, hσ1, h14]) hcap
  set σ3 := (σ2.sets (P 7) (frame (binary W 1))).seth (P 4) ((natWord 0 ++ natWord S).length + (natWord 1).length)
    with hσ3
  -- zero the scratch word
  have e4 := BinW.zero_spec cap W (pne (show (7 : Fin 12) ≠ 2 by decide)) (qne (show (15 : Fin 20) ≠ 16 by decide)) σ3 1 b
    ⟨by simp [hσ3], by simp [hσ3, hσ2, hσ1, Function.update_of_ne (pne (show (7 : Fin 12) ≠ 4 by decide)), hSc.2]⟩
    ⟨by simp [hσ3, hσ2, hσ1, Function.update_of_ne (pne (show (2 : Fin 12) ≠ 7 by decide)),
      Function.update_of_ne (pne (show (2 : Fin 12) ≠ 1 by decide)), hB.1],
     by simp [hσ3, hσ2, hσ1, Function.update_of_ne (pne (show (2 : Fin 12) ≠ 4 by decide)), hB.2]⟩
    (by simp [hσ3, hσ2, hσ1, h15]) (by simp [hσ3, hσ2, hσ1, h16]) (by omega)
  set σ4 := σ3.sets (P 7) (frame (binary W 0)) with hσ4
  -- field 4: `U`
  have e5 := natRead_spec cap W kc (I := P 4) (K := P 5) (X := P 6) (C := Q 12) (R2 := Q 13) (T := Q 14) (pne (by decide)) (pne (by decide)) (pne (by decide)) (qne (by decide))
    (qne (by decide)) (qne (by decide)) σ4 (natWord 0 ++ natWord S ++ natWord 1) rest U hW hU
    (by simp [hσ4, hσ3, hσ2, hσ1, Function.update_of_ne (pne (show (4 : Fin 12) ≠ 7 by decide)),
      Function.update_of_ne (pne (show (4 : Fin 12) ≠ 1 by decide)), hI])
    (by simp [hσ4, hσ3]; ring) (by simp [hσ4, hσ3, hσ2, hσ1, Function.update_of_ne (pne (show (5 : Fin 12) ≠ 7 by decide)),
      Function.update_of_ne (pne (show (5 : Fin 12) ≠ 1 by decide)), hK])
    (by simp [hσ4, hσ3, hσ2, hσ1, Function.update_of_ne (pne (show (5 : Fin 12) ≠ 4 by decide)), hKh]) (hbl U hU)
    (by simp [hσ4, hσ3, hσ2, hσ1, Function.update_of_ne (pne (show (6 : Fin 12) ≠ 7 by decide)),
      Function.update_of_ne (pne (show (6 : Fin 12) ≠ 1 by decide)), hT.1])
    (by simp [hσ4, hσ3, hσ2, hσ1, Function.update_of_ne (pne (show (6 : Fin 12) ≠ 4 by decide)), hT.2])
    (by simp [hσ4, hσ3, hσ2, hσ1, h12]) (by simp [hσ4, hσ3, hσ2, hσ1, h13]) (by simp [hσ4, hσ3, hσ2, hσ1, h14]) hcap
  refine WXExec.cast cap (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4 e5)))) ?_ le_rfl
  apply WState.eq
  · funext j
    by_cases j4 : j = P 4
    · subst j4; simp; ring
    · simp [hσ4, hσ3, hσ2, hσ1, Function.update_of_ne j4]
  · funext j
    by_cases j7 : j = P 7
    · subst j7; simp [Function.update_of_ne (pne (show (7 : Fin 12) ≠ 4 by decide)),
        Function.update_of_ne (pne (show (7 : Fin 12) ≠ 6 by decide)), hσ4]
    · by_cases j6 : j = P 6
      · subst j6; simp [Function.update_of_ne (pne (show (6 : Fin 12) ≠ 4 by decide))]
      · by_cases j1 : j = P 1
        · subst j1; simp [hσ4, hσ3, hσ2, Function.update_of_ne (pne (show (1 : Fin 12) ≠ 4 by decide)),
            Function.update_of_ne (pne (show (1 : Fin 12) ≠ 6 by decide)),
            Function.update_of_ne (pne (show (1 : Fin 12) ≠ 7 by decide))]
        · simp [hσ4, hσ3, hσ2, hσ1, Function.update_of_ne j1, Function.update_of_ne j6, Function.update_of_ne j7]
  · simp [hσ4, hσ3, hσ2, hσ1]
  · simp [hσ4, hσ3, hσ2, hσ1]

/-- `X := 2^m·v` by `m` doublings (`C` counted down). -/
theorem shlLoop_spec (cap W : ℕ) {X Sc : Fin (ns + 1)} {C F R : Fin nr} (hXS : X ≠ Sc) (hFR : F ≠ R) (hCF : C ≠ F)
    (hCR : C ≠ R) (σ : WState ns nr) (m v c : ℕ) (hX : NumOn σ X W v) (hS : NumOn σ Sc W c) (hC : σ.val C = m)
    (hF : σ.val F = 0) (hR : σ.val R = 0) (hcap : 2 * W + 1 + m ≤ cap) :
    WXExec cap (.whr C (.seq (WMX.dec C) (BinW.shl X Sc F R))) σ
      ((σ.sets X (frame (binary W (2 ^ m * v)))).setv C 0) (m * (41 * W + 8 + 1 + 1 + 2) + 1) := by
  let st : ℕ → WState ns nr := fun j => (σ.sets X (frame (binary W (2 ^ (m - j) * v)))).setv C j
  have hl := Runs.whr (cap := cap) (r := C) (P := .seq (WMX.dec C) (BinW.shl X Sc F R))
    (fun j τ => j ≤ m ∧ τ = st j) (41 * W + 8 + 1 + 1)
    (fun τ => τ = (σ.sets X (frame (binary W (2 ^ m * v)))).setv C 0)
    (fun τ ⟨_, h⟩ => by subst h; exact ⟨by simp [st], by simp [st]⟩)
    (by
      rintro j τ ⟨hj, rfl⟩
      refine ⟨by simp [st], ?_⟩
      have d1 := WXExec.dec cap C (st (j + 1)) (by simp [st]; omega)
      have e1 : (st (j + 1)).val C = j + 1 := by simp [st]
      rw [e1] at d1
      have hX' : NumOn ((st (j + 1)).setv C (j + 1 - 1)) X W (2 ^ (m - (j + 1)) * v) :=
        ⟨by simp [st], by simp [st, hX.2]⟩
      have hS' : NumOn ((st (j + 1)).setv C (j + 1 - 1)) Sc W c :=
        ⟨by simp [st, Function.update_of_ne hXS.symm, hS.1], by simp [st, hS.2]⟩
      have s1 := BinW.shl_spec cap W hXS hFR ((st (j + 1)).setv C (j + 1 - 1)) _ c hX' hS'
        (by simp [st, Function.update_of_ne hCF.symm, hF]) (by simp [st, Function.update_of_ne hCR.symm, hR]) (by omega)
      refine Runs.of (WXExec.mono (WXExec.seq d1 s1) (by omega)) ⟨by omega, ?_⟩
      apply WState.eq
      · simp [st]
      · funext i; by_cases hi : i = X
        · subst hi; simp [st]
          congr 2
          rw [show m - j = (m - (j + 1)) + 1 by omega, pow_succ]; ring
        · simp [st, Function.update_of_ne hi]
      · simp [st]
      · simp [st])
    m (st m) ⟨le_rfl, rfl⟩
  have e0 : st m = σ := by
    apply WState.eq
    · simp [st, hX.2]
    · funext i; by_cases hi : i = X
      · subst hi; simp [st, hX.1]
      · simp [st, Function.update_of_ne hi]
    · funext r; by_cases hr : r = C
      · subst hr; simp [st, hC]
      · simp [st, Function.update_of_ne hr]
    · simp [st]
  rw [e0] at hl
  obtain ⟨τ, el, rfl⟩ := hl
  exact el

/-- `Tw := 2^{k−1}·U`, `A := S + Tw`, `B := Tw`. -/
def arithP : WMX ns nr :=
  .seq (addR (Q 11) (Q 18) (Q 14)) (.seq (WMX.dec (Q 18))
  (.seq (.whr (Q 18) (.seq (WMX.dec (Q 18)) (BinW.shl (P 6) (P 7) (Q 15) (Q 16))))
  (.seq (BinW.add (P 1) (P 6) (Q 15) (Q 16)) (BinW.copy (P 2) (P 6) (Q 15) (Q 16)))))

def arithCost (W k : ℕ) : ℕ :=
  18 * k + 3 + 1 + (1 + 1 + ((k - 1) * (41 * W + 8 + 1 + 1 + 2) + 1 + 1 + (41 * W + 3 + 1 + (41 * W + 3))))

theorem arithP_spec (cap W k S U b c : ℕ) (σ : WState ns nr) (hA : NumOn σ (P 1) W S) (hB : NumOn σ (P 2) W b)
    (hT : NumOn σ (P 6) W U) (hSc : NumOn σ (P 7) W c) (h11 : σ.val (Q 11) = k) (h14 : σ.val (Q 14) = 0)
    (h15 : σ.val (Q 15) = 0) (h16 : σ.val (Q 16) = 0) (h18 : σ.val (Q 18) = 0)
    (hfit : S + 2 ^ (k - 1) * U < 2 ^ W) (hcap : 2 * W + 1 + 2 * k ≤ cap) :
    WXExec cap (arithP P Q) σ (((σ.sets (P 6) (frame (binary W (2 ^ (k - 1) * U)))).sets (P 1)
      (frame (binary W (S + 2 ^ (k - 1) * U)))).sets (P 2) (frame (binary W (2 ^ (k - 1) * U)))) (arithCost W k) := by
  have pne : ∀ {a b : Fin 12}, a ≠ b → P a ≠ P b := fun h => P.injective.ne h
  have qne : ∀ {a b : Fin 20}, a ≠ b → Q a ≠ Q b := fun h => Q.injective.ne h
  have e1 := addR_spec cap (A := Q 11) (B := Q 18) (T := Q 14) (qne (by decide)) (qne (by decide)) (qne (by decide))
    σ h14 (by rw [h11, h18]; omega)
  rw [h11, h18, Nat.zero_add] at e1
  have e2 := WXExec.dec cap (Q 18) (σ.setv (Q 18) k) (by simp; omega)
  simp only [wsetv_val_self, wsetv_setv] at e2
  have e3 := shlLoop_spec cap W (X := P 6) (Sc := P 7) (C := Q 18) (F := Q 15) (R := Q 16) (pne (by decide))
    (qne (by decide)) (qne (by decide)) (qne (by decide)) (σ.setv (Q 18) (k - 1)) (k - 1) U c
    ⟨by simp [hT.1], by simp [hT.2]⟩ ⟨by simp [hSc.1], by simp [hSc.2]⟩ (by simp)
    (by simp [Function.update_of_ne (qne (show (15 : Fin 20) ≠ 18 by decide)), h15])
    (by simp [Function.update_of_ne (qne (show (16 : Fin 20) ≠ 18 by decide)), h16]) (by omega)
  set σ3 := ((σ.setv (Q 18) (k - 1)).sets (P 6) (frame (binary W (2 ^ (k - 1) * U)))).setv (Q 18) 0 with hσ3
  have hsub : 2 ^ (k - 1) * U < 2 ^ W := by omega
  have e4 := BinW.add_spec cap W (pne (show (1 : Fin 12) ≠ 6 by decide)) (qne (show (15 : Fin 20) ≠ 16 by decide)) σ3
    S (2 ^ (k - 1) * U)
    ⟨by simp [hσ3, Function.update_of_ne (pne (show (1 : Fin 12) ≠ 6 by decide)), hA.1], by simp [hσ3, hA.2]⟩
    ⟨by simp [hσ3], by simp [hσ3, hT.2]⟩
    (by simp [hσ3, Function.update_of_ne (qne (show (15 : Fin 20) ≠ 18 by decide)), h15])
    (by simp [hσ3, Function.update_of_ne (qne (show (16 : Fin 20) ≠ 18 by decide)), h16]) hfit (by omega)
  set σ4 := σ3.sets (P 1) (frame (binary W (S + 2 ^ (k - 1) * U))) with hσ4
  have e5 := BinW.copy_spec cap W (pne (show (2 : Fin 12) ≠ 6 by decide)) (qne (show (15 : Fin 20) ≠ 16 by decide)) σ4
    b (2 ^ (k - 1) * U)
    ⟨by simp [hσ4, hσ3, Function.update_of_ne (pne (show (2 : Fin 12) ≠ 6 by decide)),
      Function.update_of_ne (pne (show (2 : Fin 12) ≠ 1 by decide)), hB.1], by simp [hσ4, hσ3, hB.2]⟩
    ⟨by simp [hσ4, hσ3, Function.update_of_ne (pne (show (6 : Fin 12) ≠ 1 by decide))], by simp [hσ4, hσ3, hT.2]⟩
    (by simp [hσ4, hσ3, Function.update_of_ne (qne (show (15 : Fin 20) ≠ 18 by decide)), h15])
    (by simp [hσ4, hσ3, Function.update_of_ne (qne (show (16 : Fin 20) ≠ 18 by decide)), h16]) (by omega)
  refine WXExec.cast cap (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4 e5)))) ?_ (by unfold arithCost; omega)
  apply WState.eq
  · simp [hσ4, hσ3]
  · simp [hσ4, hσ3]
  · funext r; by_cases hr : r = Q 18
    · subst hr; simp [hσ4, hσ3, h18]
    · simp [hσ4, hσ3, Function.update_of_ne hr]
  · simp [hσ4, hσ3]

/-- `Q 12 := m·(2W + 1)` (`Q 13 = 2W + 1`). -/
def addN : ℕ → WMX ns nr
  | 0 => WMX.skip
  | m + 1 => .seq (addR (Q 13) (Q 12) (Q 14)) (addN m)

theorem addN_spec (cap W : ℕ) : ∀ (m : ℕ) (σ : WState ns nr) (v : ℕ), σ.val (Q 12) = v → σ.val (Q 13) = 2 * W + 1 →
    σ.val (Q 14) = 0 → v + m * (2 * W + 1) ≤ cap →
    WXExec cap (addN Q m) σ (σ.setv (Q 12) (v + m * (2 * W + 1))) (m * (18 * (2 * W + 1) + 4))
  | 0, σ, v, h12, _, _, _ => by
    simp only [addN, Nat.zero_mul, Nat.add_zero]
    rw [← h12, wsetv_same]; exact WXExec.skip cap σ
  | m + 1, σ, v, h12, h13, h14, hc => by
    have qne : ∀ {a b : Fin 20}, a ≠ b → Q a ≠ Q b := fun h => Q.injective.ne h
    have e1 := addR_spec cap (A := Q 13) (B := Q 12) (T := Q 14) (qne (by decide)) (qne (by decide))
      (qne (by decide)) σ h14 (by rw [h12, h13]; nlinarith)
    rw [h12, h13] at e1
    have e2 := addN_spec cap W m (σ.setv (Q 12) (v + (2 * W + 1))) (v + (2 * W + 1)) (by simp)
      (by simp [Function.update_of_ne (qne (show (13 : Fin 20) ≠ 12 by decide)), h13])
      (by simp [Function.update_of_ne (qne (show (14 : Fin 20) ≠ 12 by decide)), h14]) (by nlinarith)
    refine WXExec.cast cap (WXExec.seq e1 e2) ?_ (by ring_nf; omega)
    rw [wsetv_setv]; congr 1; ring

/-- Rewind the output and the input streams (heads at most `6(2W + 1)`). -/
def rewP : WMX ns nr :=
  .seq (addN Q 6) (.seq (.wm (WM.rewind (P 0) (Q 12))) (.seq (addN Q 6) (.wm (WM.rewind (P 4) (Q 12)))))

theorem rewP_spec (cap W : ℕ) (σ : WState ns nr) (h12 : σ.val (Q 12) = 0) (h13 : σ.val (Q 13) = 2 * W + 1)
    (h14 : σ.val (Q 14) = 0) (h0 : σ.sh (P 0) ≤ 6 * (2 * W + 1)) (h4 : σ.sh (P 4) ≤ 6 * (2 * W + 1))
    (hcap : 6 * (2 * W + 1) ≤ cap) :
    WXExec cap (rewP P Q) σ ((σ.seth (P 0) 0).seth (P 4) 0) (2 * (6 * (18 * (2 * W + 1) + 4)) + 2 * (5 * (6 * (2 * W + 1)) + 1) + 3) := by
  have pne : ∀ {a b : Fin 12}, a ≠ b → P a ≠ P b := fun h => P.injective.ne h
  have qne : ∀ {a b : Fin 20}, a ≠ b → Q a ≠ Q b := fun h => Q.injective.ne h
  have e1 := addN_spec Q cap W 6 σ 0 h12 h13 h14 (by omega)
  rw [Nat.zero_add] at e1
  have e2 := wrewind_spec (cap := cap) (P 0) (Q 12) (6 * (2 * W + 1)) (σ.setv (Q 12) (6 * (2 * W + 1))) (by simp)
    (by simp; omega)
  set σ2 := ((σ.setv (Q 12) (6 * (2 * W + 1))).setv (Q 12) 0).seth (P 0)
    ((σ.setv (Q 12) (6 * (2 * W + 1))).sh (P 0) - 6 * (2 * W + 1)) with hσ2
  have e3 := addN_spec Q cap W 6 σ2 0 (by simp [hσ2])
    (by simp [hσ2, Function.update_of_ne (qne (show (13 : Fin 20) ≠ 12 by decide)), h13])
    (by simp [hσ2, Function.update_of_ne (qne (show (14 : Fin 20) ≠ 12 by decide)), h14]) (by omega)
  rw [Nat.zero_add] at e3
  have e4 := wrewind_spec (cap := cap) (P 4) (Q 12) (6 * (2 * W + 1)) (σ2.setv (Q 12) (6 * (2 * W + 1))) (by simp)
    (by simp; omega)
  refine WXExec.cast cap (WXExec.seq e1 (WXExec.seq (WXExec.wm e2) (WXExec.seq e3 (WXExec.wm e4)))) ?_ (by omega)
  apply WState.eq
  · funext j
    by_cases j4 : j = P 4
    · subst j4; simp [hσ2, Function.update_of_ne (pne (show (4 : Fin 12) ≠ 0 by decide))]; omega
    · by_cases j0 : j = P 0
      · subst j0; simp [hσ2, Function.update_of_ne j4]; omega
      · simp [hσ2, Function.update_of_ne j4, Function.update_of_ne j0]
  · simp [hσ2]
  · funext r; by_cases hr : r = Q 12
    · subst hr; simp [hσ2, h12]
    · simp [hσ2, Function.update_of_ne hr]
  · simp [hσ2]

end Ivl

end NearCubicGates.Close.CounterMachine
