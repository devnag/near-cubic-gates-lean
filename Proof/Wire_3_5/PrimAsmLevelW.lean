import Proof.Wire_3_5.PrimAsmFiltRecW
import Proof.Wire_3_5.PrimAsmSymQM
import Proof.Wire_3_5.ListBase
import Proof.Wire_3_5.FinalPassListEvalRef

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.PrimAsm.LevelW
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.CanonicalFourfoldRowProgram (natCeilSqrt le_natCeilSqrt_sq sq_lt_of_lt_natCeilSqrt)

variable {ns nr : ℕ} (cap : ℕ)

theorem natCeilSqrt_le (X : ℕ) : natCeilSqrt X ≤ X + 1 := by
  unfold natCeilSqrt
  have := Nat.sqrt_le_self X
  dsimp only
  split_ifs <;> omega

theorem natCeilSqrt_step (X r : ℕ) (hr : r ≤ natCeilSqrt X) :
    (r * r < X ↔ r < natCeilSqrt X) := by
  constructor
  · intro h
    by_contra hc
    have hre : r = natCeilSqrt X := by omega
    have := le_natCeilSqrt_sq X
    rw [← hre] at this
    omega
  · exact sq_lt_of_lt_natCeilSqrt

theorem setv_eq_self {σ : WState ns nr} {r : Fin nr} {x : ℕ} (h : σ.val r = x) : σ.setv r x = σ := by
  rw [← h]; exact wsetv_same σ r

/-- The square-root registers: `0 X` (kept), `1 r`, `2 K`, `3 P`, `4 F`, `5 r2`, `6 t`, `7 w`, `8 u`, `9 w2`. -/
abbrev QReg (nr : ℕ) := Fin 10 ↪ Fin nr

def qMul : Fin 5 ↪ Fin 10 := ⟨![1, 5, 3, 6, 7], by decide⟩
def qGt : Fin 6 ↪ Fin 10 := ⟨![0, 3, 4, 6, 8, 9], by decide⟩

section Sqrt
variable (Q : QReg nr)

/-- One step: `P := r·r`; `r += [r·r < X]`; scratch back to `0`. -/
def sqrtStep : WM ns nr :=
  .seq (FinalPass.Hash4.wcopyR (Q 1) (Q 5) (Q 6))
  (.seq (UnaryArith.mulAddW (qMul.trans Q))
  (.seq (WM.clear (Q 5))
  (.seq (UnaryArith.gtFlagW (qGt.trans Q))
  (.seq (.ifr (Q 4) (.inc (Q 1)) .skip)
  (.seq (WM.clear (Q 4)) (WM.clear (Q 3)))))))

/-- `r := natCeilSqrt X`: `X + 1` steps from `r = 0`. -/
def sqrtW : WM ns nr :=
  .seq (FinalPass.Hash4.wcopyR (Q 0) (Q 2) (Q 6)) (.seq (.inc (Q 2)) (.whr (Q 2) (.seq (.dec (Q 2)) (sqrtStep Q))))

/-- The cost bound of one step at `r ≤ s`, `X`. -/
def stepCost (X s : ℕ) : ℕ :=
  (18 * s + 3) + 1 + (s * (18 * s + 8) + 18 * s + 10) + 1 + (3 * s + 1) + 1 + (30 * X + 30 * (s * s) + 20) + 1 + 4 + 1 +
    4 + 1 + (3 * (s * s) + 1)

theorem sqrtStep_spec (σ : WState ns nr) (X r : ℕ) (hX : σ.val (Q 0) = X) (hr : σ.val (Q 1) = r)
    (hr' : r ≤ natCeilSqrt X) (h3 : σ.val (Q 3) = 0) (h4 : σ.val (Q 4) = 0) (h5 : σ.val (Q 5) = 0)
    (h6 : σ.val (Q 6) = 0) (h7 : σ.val (Q 7) = 0) (h8 : σ.val (Q 8) = 0) (h9 : σ.val (Q 9) = 0)
    (hcap : (X + 2) * (X + 2) + X + 10 ≤ cap) :
    WExec cap (sqrtStep Q) σ (σ.setv (Q 1) (if r < natCeilSqrt X then r + 1 else r))
      (stepCost X (natCeilSqrt X)) := by
  have hR : ∀ i j : Fin 10, Q i = Q j ↔ i = j := fun i j => Q.injective.eq_iff
  have hne : ∀ {i j : Fin 10}, i ≠ j → Q i ≠ Q j := fun h => Q.injective.ne h
  have hs := natCeilSqrt_le X
  have hrX : r ≤ X + 1 := by omega
  have hrr : r * r ≤ (X + 2) * (X + 2) := Nat.mul_le_mul (by omega) (by omega)
  set s := natCeilSqrt X with hsdef
  have hss : r * r ≤ s * s := Nat.mul_le_mul hr' hr'
  have e1 := FinalPass.Hash4.wcopyR_spec cap (Q 1) (Q 5) (Q 6) (hne (by decide)) (hne (by decide)) (hne (by decide))
    σ h5 h6 (by omega)
  rw [hr] at e1
  have e2 := UnaryArith.mulAddW_spec cap (qMul.trans Q) (σ.setv (Q 5) r)
    (by simp [qMul, hR, h6]) (by simp [qMul, hR, h7]) (by simp [qMul, hR]; omega)
    (by simp [qMul, hR, h3, hr]; omega) (by simp [qMul, hR, hr]; omega)
  have v2 : (σ.setv (Q 5) r).setv ((qMul.trans Q) 2) ((σ.setv (Q 5) r).val ((qMul.trans Q) 2) +
      (σ.setv (Q 5) r).val ((qMul.trans Q) 0) * (σ.setv (Q 5) r).val ((qMul.trans Q) 1)) =
      (σ.setv (Q 5) r).setv (Q 3) (r * r) := by
    simp [qMul, hR, h3, hr]
  have c2 : (σ.setv (Q 5) r).val ((qMul.trans Q) 1) * (18 * (σ.setv (Q 5) r).val ((qMul.trans Q) 0) + 8) +
      18 * (σ.setv (Q 5) r).val ((qMul.trans Q) 1) + 10 = r * (18 * r + 8) + 18 * r + 10 := by
    simp [qMul, hR, hr]
  rw [v2, c2] at e2
  have e3 := wclear_spec cap (Q 5) r ((σ.setv (Q 5) r).setv (Q 3) (r * r)) (by simp [hR]) (by simp [hR]; omega)
  have v3 : ((σ.setv (Q 5) r).setv (Q 3) (r * r)).setv (Q 5) 0 = σ.setv (Q 3) (r * r) := by
    rw [wsetv_comm _ _ _ (hne (by decide)), wsetv_setv, ← h5, wsetv_same]
  rw [v3] at e3
  have e4 := UnaryArith.gtFlagW_spec cap (qGt.trans Q) (σ.setv (Q 3) (r * r))
    (by simp [qGt, hR, h4]) (by simp [qGt, hR, h6]) (by simp [qGt, hR, h8]) (by simp [qGt, hR, h9])
    (by simp [qGt, hR, hX]; omega) (by simp [qGt, hR]; omega) (by omega)
  have v4 : (σ.setv (Q 3) (r * r)).setv ((qGt.trans Q) 2)
      (if (σ.setv (Q 3) (r * r)).val ((qGt.trans Q) 1) < (σ.setv (Q 3) (r * r)).val ((qGt.trans Q) 0) then 1 else 0) =
      (σ.setv (Q 3) (r * r)).setv (Q 4) (if r * r < X then 1 else 0) := by
    simp [qGt, hR, hX]
  have c4 : 30 * (σ.setv (Q 3) (r * r)).val ((qGt.trans Q) 0) + 30 * (σ.setv (Q 3) (r * r)).val ((qGt.trans Q) 1) + 20 =
      30 * X + 30 * (r * r) + 20 := by simp [qGt, hR, hX]
  rw [v4, c4] at e4
  have hif : (if r * r < X then (1 : ℕ) else 0) = if r < s then 1 else 0 := by
    by_cases h : r < s
    · rw [if_pos h, if_pos ((natCeilSqrt_step X r hr').mpr h)]
    · rw [if_neg h, if_neg (fun h' => h ((natCeilSqrt_step X r hr').mp h'))]
  rw [hif] at e4
  have e5 : WExec cap (.ifr (Q 4) (.inc (Q 1)) .skip) ((σ.setv (Q 3) (r * r)).setv (Q 4) (if r < s then 1 else 0))
      ((((σ.setv (Q 3) (r * r)).setv (Q 4) (if r < s then 1 else 0))).setv (Q 1) (if r < s then r + 1 else r)) 4 := by
    by_cases hlt : r < s
    · simp only [hlt, if_true]
      have := WExec.inc (cap := cap) (Q 1) (((σ.setv (Q 3) (r * r)).setv (Q 4) 1)) (by simp [hR, hr]; omega)
      rw [show ((σ.setv (Q 3) (r * r)).setv (Q 4) 1).val (Q 1) + 1 = r + 1 by simp [hR, hr]] at this
      exact WExec.mono (WExec.ifrT (by simp) this) (by omega)
    · simp only [hlt, if_false]
      have h0 := WExec.skip (cap := cap) (((σ.setv (Q 3) (r * r)).setv (Q 4) 0))
      have h0' := WExec.cast cap h0 (setv_eq_self (r := Q 1) (x := r)
        (σ := ((σ.setv (Q 3) (r * r)).setv (Q 4) 0)) (by simp [hR, hr])).symm (le_refl 0)
      exact WExec.mono (WExec.ifrF (by simp) h0') (by omega)
  have e6 := wclear_spec cap (Q 4) (if r < s then 1 else 0)
    ((((σ.setv (Q 3) (r * r)).setv (Q 4) (if r < s then 1 else 0))).setv (Q 1) (if r < s then r + 1 else r))
    (by simp [hR]) (by simp [hR]; split_ifs <;> omega)
  have e7 := wclear_spec cap (Q 3) (r * r)
    (((((σ.setv (Q 3) (r * r)).setv (Q 4) (if r < s then 1 else 0))).setv (Q 1) (if r < s then r + 1 else r)).setv (Q 4) 0)
    (by simp [hR]) (by simp [hR]; omega)
  have hall := WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 (WExec.seq e6 e7)))))
  refine WExec.cast cap hall ?_ ?_
  · apply WState.eq
    · rfl
    · rfl
    · funext j
      simp only [WState.setv_val, Function.update_apply]
      by_cases j3 : j = Q 3
      · subst j3; simp [hR, h3]
      · by_cases j4 : j = Q 4
        · subst j4; simp [hR, h4]
        · by_cases j1 : j = Q 1
          · subst j1; simp [hR]
          · simp [j1, j3, j4]
    · rfl
  · have hc3 : 3 * (if r < s then 1 else 0) + 1 ≤ 4 := by split_ifs <;> omega
    have hk1 : r * (18 * r + 8) ≤ s * (18 * s + 8) := Nat.mul_le_mul hr' (by omega)
    unfold stepCost
    omega

theorem sqrtW_spec (σ : WState ns nr) (X : ℕ) (hX : σ.val (Q 0) = X) (h1 : σ.val (Q 1) = 0) (h2 : σ.val (Q 2) = 0)
    (h3 : σ.val (Q 3) = 0) (h4 : σ.val (Q 4) = 0) (h5 : σ.val (Q 5) = 0)
    (h6 : σ.val (Q 6) = 0) (h7 : σ.val (Q 7) = 0) (h8 : σ.val (Q 8) = 0) (h9 : σ.val (Q 9) = 0)
    (hcap : (X + 2) * (X + 2) + X + 10 ≤ cap) :
    WExec cap (sqrtW Q) σ (σ.setv (Q 1) (natCeilSqrt X))
      (18 * X + 3 + 1 + (3 + 1 + ((X + 1) * (stepCost X (natCeilSqrt X) + 4) + 1))) := by
  have hR : ∀ i j : Fin 10, Q i = Q j ↔ i = j := fun i j => Q.injective.eq_iff
  have hne : ∀ {i j : Fin 10}, i ≠ j → Q i ≠ Q j := fun h => Q.injective.ne h
  have hs := natCeilSqrt_le X
  set s := natCeilSqrt X with hsdef
  have e1 := FinalPass.Hash4.wcopyR_spec cap (Q 0) (Q 2) (Q 6) (hne (by decide)) (hne (by decide)) (hne (by decide))
    σ h2 h6 (by omega)
  rw [hX] at e1
  have e2 := WExec.inc (cap := cap) (Q 2) (σ.setv (Q 2) X) (by simp [hR]; omega)
  rw [wsetv_setv, show (σ.setv (Q 2) X).val (Q 2) + 1 = X + 1 by simp [hR]] at e2
  let T : ℕ → WState ns nr := fun k => (σ.setv (Q 1) (min k s)).setv (Q 2) (X + 1 - k)
  have hT0 : T 0 = σ.setv (Q 2) (X + 1) := by
    simp only [T, Nat.min_def, Nat.zero_le, if_true, Nat.sub_zero]
    rw [show (0 : ℕ) = σ.val (Q 1) from h1.symm, wsetv_same]
  have hloop := UnionMachine.Round.wloop cap (Q 2) (sqrtStep Q) (stepCost X s) (X + 1) T
    (fun k _ => by simp [T, hR])
    (by omega)
    (fun k hk => by
      have eT : (T k).setv (Q 2) (X + 1 - k - 1) = (σ.setv (Q 2) (X + 1 - k - 1)).setv (Q 1) (min k s) := by
        simp only [T, wsetv_setv]; rw [wsetv_comm _ _ _ (hne (by decide))]
      rw [eT]
      have hst := sqrtStep_spec cap Q ((σ.setv (Q 2) (X + 1 - k - 1)).setv (Q 1) (min k s)) X (min k s)
        (by simp [hR, hX]) (by simp [hR]) (by omega) (by simp [hR, h3]) (by simp [hR, h4]) (by simp [hR, h5])
        (by simp [hR, h6]) (by simp [hR, h7]) (by simp [hR, h8]) (by simp [hR, h9]) hcap
      refine WExec.cast cap hst ?_ le_rfl
      apply WState.eq
      · rfl
      · rfl
      · funext j
        simp only [T, WState.setv_val, Function.update_apply]
        by_cases j1 : j = Q 1
        · subst j1; simp [hR]; split_ifs <;> omega
        · by_cases j2 : j = Q 2
          · subst j2; simp [hR]; omega
          · simp [j1, j2]
      · rfl)
  rw [hT0] at hloop
  have hall := WExec.seq e1 (WExec.seq e2 hloop)
  refine WExec.cast cap hall ?_ le_rfl
  apply WState.eq
  · rfl
  · rfl
  · funext j
    simp only [T, WState.setv_val, Function.update_apply]
    by_cases j1 : j = Q 1
    · subst j1; simp [hR]; omega
    · by_cases j2 : j = Q 2
      · subst j2; simp [hR, h2]
      · simp [j1, j2]
  · rfl

end Sqrt

/-! ## One level's window and its power -/

/-- The level registers: `0 S`, `1 J`, `2 j` (kept); `3 W`, `4 P` (out); `5 A`, `6 B`, `7 Q1`, `8 P2`, `9 N`, `10 Q2`,
`11 F`, `12 X`, `13 C`, `14`–`23` scratch. -/
abbrev LVReg (nr : ℕ) := Fin 24 ↪ Fin nr

def lvD1 : Fin 9 ↪ Fin 24 := ⟨![5, 6, 7, 14, 15, 16, 17, 18, 19], by decide⟩
def lvP1 : Fin 4 ↪ Fin 24 := ⟨![7, 8, 14, 15], by decide⟩
def lvD2 : Fin 9 ↪ Fin 24 := ⟨![9, 8, 10, 14, 15, 16, 17, 18, 19], by decide⟩
def lvG : Fin 6 ↪ Fin 24 := ⟨![1, 2, 11, 14, 15, 16], by decide⟩
def lvC : Fin 10 ↪ Fin 24 := ⟨![12, 13, 14, 15, 16, 17, 18, 19, 20, 21], by decide⟩
def lvP2 : Fin 4 ↪ Fin 24 := ⟨![13, 4, 14, 15], by decide⟩

/-- The window at level `j` from `S = natCeilSqrt(64²B)`: `0` at the top level `J`, else `64 + ⌈S / 2^{⌊j/3⌋}⌉`. -/
def winAt (S J j : ℕ) : ℕ := if j = J then 0 else 64 + (S + 2 ^ (j / 3) - 1) / 2 ^ (j / 3)

section Level
variable (V : LVReg nr)

/-- Level phase A: `P2 := 2^{⌊j/3⌋}`. -/
def lvPhA : WM ns nr :=
  .seq (FinalPass.Hash4.wcopyR (V 2) (V 5) (V 14))
  (.seq (StarNums.incN (V 6) 3)
  (.seq (UnaryArith.divW (lvD1.trans V))
  (.seq (WM.clear (V 5))
  (.seq (WM.clear (V 6))
  (.seq (UnaryArith.pow2W (lvP1.trans V))
  (WM.clear (V 7)))))))

/-- Level phase B: `Q2 := ⌈S / P2⌉`, `P2 := 0`. -/
def lvPhB : WM ns nr :=
  .seq (FinalPass.Hash4.wcopyR (V 0) (V 9) (V 14))
  (.seq (ParseNat.addTo (V 8) (V 9) (V 14))
  (.seq (.dec (V 9))
  (.seq (UnaryArith.divW (lvD2.trans V))
  (.seq (WM.clear (V 9))
  (WM.clear (V 8))))))

/-- Level phase C: `W := winAt S J j` from `Q2`. -/
def lvPhC : WM ns nr :=
  .seq (WM.move (V 10) (V 3))
  (.seq (StarNums.incN (V 3) 64)
  (.seq (UnaryArith.gtFlagW (lvG.trans V))
  (.seq (.ifr (V 11) .skip (WM.clear (V 3)))
  (WM.clear (V 11)))))

/-- Level phase D: `P := 2^{⌈log₂(2W+1)⌉}`. -/
def lvPhD : WM ns nr :=
  .seq (ParseNat.addTo (V 3) (V 12) (V 14))
  (.seq (ParseNat.addTo (V 3) (V 12) (V 14))
  (.seq (.inc (V 12))
  (.seq (PrimAsm.SymQM.clogW (lvC.trans V))
  (.seq (WM.clear (V 12))
  (.seq (UnaryArith.pow2W (lvP2.trans V))
  (WM.clear (V 13)))))))

/-- **The level program**: `W := winAt S J j`, `P := 2^{⌈log₂(2W+1)⌉}`; scratch back to `0`. -/
def levelVals : WM ns nr := .seq (lvPhA V) (.seq (lvPhB V) (.seq (lvPhC V) (lvPhD V)))

/-- A uniform bound on a level phase's cost at register capacity `cap`. -/
def phBound (cap : ℕ) : ℕ := 2000 * (cap + 2) * (cap + 2) + 20 * UnaryPow.sq cap

theorem lvPhA_spec (σ : WState ns nr) (j : ℕ) (hj : σ.val (V 2) = j) (h5 : σ.val (V 5) = 0) (h6 : σ.val (V 6) = 0)
    (h7 : σ.val (V 7) = 0) (h8 : σ.val (V 8) = 0) (h14 : σ.val (V 14) = 0) (h15 : σ.val (V 15) = 0)
    (h16 : σ.val (V 16) = 0) (h17 : σ.val (V 17) = 0) (h18 : σ.val (V 18) = 0)
    (hcap : 2 ^ (j / 3 + 1) + j + 10 ≤ cap) :
    ∃ n, WExec cap (lvPhA V) σ (σ.setv (V 8) (2 ^ (j / 3))) n ∧ n ≤ phBound cap := by
  have hR : ∀ i k : Fin 24, V i = V k ↔ i = k := fun i k => V.injective.eq_iff
  have hne : ∀ {i k : Fin 24}, i ≠ k → V i ≠ V k := fun h => V.injective.ne h
  have hj3 : j / 3 ≤ j := Nat.div_le_self _ _
  have hp : j / 3 < 2 ^ (j / 3) := Nat.lt_two_pow_self
  have hpp : 2 ^ (j / 3 + 1) = 2 * 2 ^ (j / 3) := by rw [pow_succ]; ring
  have e1 := FinalPass.Hash4.wcopyR_spec cap (V 2) (V 5) (V 14) (hne (by decide)) (hne (by decide)) (hne (by decide))
    σ h5 h14 (by omega)
  rw [hj] at e1
  have e2 := StarNums.incN_spec cap (V 6) 3 (σ.setv (V 5) j) (by simp [hR, h6]; omega)
  rw [show (σ.setv (V 5) j).val (V 6) + 3 = 3 by simp [hR, h6]] at e2
  have e3 := UnaryArith.divW_spec cap (lvD1.trans V) ((σ.setv (V 5) j).setv (V 6) 3)
    (by simp [lvD1, hR]) (by simp [lvD1, hR, h14]) (by simp [lvD1, hR, h15]) (by simp [lvD1, hR, h16])
    (by simp [lvD1, hR, h17]) (by simp [lvD1, hR, h18]) (by simp [lvD1, hR]; omega) (by simp [lvD1, hR]; omega)
    (by simp [lvD1, hR, h7]; omega) (by omega)
  have v3 : (((σ.setv (V 5) j).setv (V 6) 3).setv ((lvD1.trans V) 0)
      (((σ.setv (V 5) j).setv (V 6) 3).val ((lvD1.trans V) 0) % ((σ.setv (V 5) j).setv (V 6) 3).val ((lvD1.trans V) 1))).setv
      ((lvD1.trans V) 2) (((σ.setv (V 5) j).setv (V 6) 3).val ((lvD1.trans V) 2) +
        ((σ.setv (V 5) j).setv (V 6) 3).val ((lvD1.trans V) 0) / ((σ.setv (V 5) j).setv (V 6) 3).val ((lvD1.trans V) 1)) =
      (((σ.setv (V 5) (j % 3)).setv (V 6) 3).setv (V 7) (j / 3)) := by
    simp only [lvD1, Function.Embedding.trans_apply, Function.Embedding.coeFn_mk]
    simp [hR, h7, wsetv_setv, wsetv_comm _ _ _ (hne (show (6 : Fin 24) ≠ 5 by decide))]
  have c3 : (((σ.setv (V 5) j).setv (V 6) 3).val ((lvD1.trans V) 0) + 2) *
      (90 * ((σ.setv (V 5) j).setv (V 6) 3).val ((lvD1.trans V) 0) + 90 * ((σ.setv (V 5) j).setv (V 6) 3).val ((lvD1.trans V) 1) + 60) =
      (j + 2) * (90 * j + 90 * 3 + 60) := by simp [lvD1, hR]
  rw [v3, c3] at e3
  have e4 := wclear_spec cap (V 5) (j % 3) (((σ.setv (V 5) (j % 3)).setv (V 6) 3).setv (V 7) (j / 3)) (by simp [hR])
    (by simp [hR]; omega)
  have e5 := wclear_spec cap (V 6) 3 ((((σ.setv (V 5) (j % 3)).setv (V 6) 3).setv (V 7) (j / 3)).setv (V 5) 0)
    (by simp [hR]) (by simp [hR]; omega)
  set τ := (((((σ.setv (V 5) (j % 3)).setv (V 6) 3).setv (V 7) (j / 3)).setv (V 5) 0).setv (V 6) 0) with hτ
  have e6 := UnaryArith.pow2W_spec cap (lvP1.trans V) τ (by simp [τ, lvP1, hR, h8]) (by simp [τ, lvP1, hR, h14])
    (by simp [τ, lvP1, hR, h15]) (by simp [τ, lvP1, hR]; omega)
  have v6 : τ.setv ((lvP1.trans V) 1) (2 ^ τ.val ((lvP1.trans V) 0)) = τ.setv (V 8) (2 ^ (j / 3)) := by
    simp [τ, lvP1, hR]
  have c6 : τ.val ((lvP1.trans V) 0) * (18 * 2 ^ τ.val ((lvP1.trans V) 0) + 7) + 18 * τ.val ((lvP1.trans V) 0) + 20 =
      j / 3 * (18 * 2 ^ (j / 3) + 7) + 18 * (j / 3) + 20 := by simp [τ, lvP1, hR]
  rw [v6, c6] at e6
  have e7 := wclear_spec cap (V 7) (j / 3) (τ.setv (V 8) (2 ^ (j / 3))) (by simp [τ, hR]) (by simp [τ, hR]; omega)
  refine ⟨_, WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 (WExec.seq e6 e7))))))
    ?_ le_rfl, ?_⟩
  · apply WState.eq
    · rfl
    · rfl
    · funext x
      simp only [τ, WState.setv_val, Function.update_apply]
      by_cases x5 : x = V 5
      · subst x5; simp [hR, h5]
      · by_cases x6 : x = V 6
        · subst x6; simp [hR, h6]
        · by_cases x7 : x = V 7
          · subst x7; simp [hR, h7]
          · by_cases x8 : x = V 8
            · subst x8; simp [hR]
            · simp [x5, x6, x7, x8]
    · rfl
  · unfold phBound
    have h2c : 2 ^ (j / 3) ≤ cap := by omega
    have hA : (j + 2) * (90 * j + 90 * 3 + 60) ≤ (cap + 2) * (300 * (cap + 2)) := Nat.mul_le_mul (by omega) (by omega)
    have hB : j / 3 * (18 * 2 ^ (j / 3) + 7) ≤ (cap + 2) * (25 * (cap + 2)) := Nat.mul_le_mul (by omega) (by omega)
    have hC : (cap + 2) * (300 * (cap + 2)) = 300 * ((cap + 2) * (cap + 2)) := by ring
    have hD : (cap + 2) * (25 * (cap + 2)) = 25 * ((cap + 2) * (cap + 2)) := by ring
    have hE : 2000 * (cap + 2) * (cap + 2) = 2000 * ((cap + 2) * (cap + 2)) := by ring
    have hF : cap + 2 ≤ (cap + 2) * (cap + 2) := Nat.le_mul_self _
    rw [hE]
    omega

theorem lvPhB_spec (τ : WState ns nr) (S p : ℕ) (hS : τ.val (V 0) = S) (hp : τ.val (V 8) = p) (hp1 : 1 ≤ p)
    (h9 : τ.val (V 9) = 0) (h10 : τ.val (V 10) = 0) (h14 : τ.val (V 14) = 0) (h15 : τ.val (V 15) = 0)
    (h16 : τ.val (V 16) = 0) (h17 : τ.val (V 17) = 0) (h18 : τ.val (V 18) = 0)
    (hcap : 2 * (S + p) + 10 ≤ cap) :
    ∃ n, WExec cap (lvPhB V) τ ((τ.setv (V 10) ((S + p - 1) / p)).setv (V 8) 0) n ∧ n ≤ phBound cap := by
  have hR : ∀ i k : Fin 24, V i = V k ↔ i = k := fun i k => V.injective.eq_iff
  have hne : ∀ {i k : Fin 24}, i ≠ k → V i ≠ V k := fun h => V.injective.ne h
  have hq : (S + p - 1) / p ≤ S + p := le_trans (Nat.div_le_self _ _) (by omega)
  have hr : (S + p - 1) % p < p := Nat.mod_lt _ (by omega)
  have e1 := FinalPass.Hash4.wcopyR_spec cap (V 0) (V 9) (V 14) (hne (by decide)) (hne (by decide)) (hne (by decide))
    τ h9 h14 (by omega)
  rw [hS] at e1
  have e2 := ParseNat.addTo_spec cap (V 8) (V 9) (V 14) (hne (by decide)) (hne (by decide)) (hne (by decide))
    (τ.setv (V 9) S) (by simp [hR, h14]) (by simp [hR, hp]; omega) (by simp [hR, hp]; omega)
  rw [wsetv_setv, show (τ.setv (V 9) S).val (V 9) + (τ.setv (V 9) S).val (V 8) = S + p by simp [hR, hp],
    show (τ.setv (V 9) S).val (V 8) = p by simp [hR, hp]] at e2
  have e3 := WExec.dec (cap := cap) (V 9) (τ.setv (V 9) (S + p)) (by simp; omega)
  rw [wsetv_setv, show (τ.setv (V 9) (S + p)).val (V 9) - 1 = S + p - 1 by simp] at e3
  have e4 := UnaryArith.divW_spec cap (lvD2.trans V) (τ.setv (V 9) (S + p - 1))
    (by simp [lvD2, hR, hp]; omega) (by simp [lvD2, hR, h14]) (by simp [lvD2, hR, h15]) (by simp [lvD2, hR, h16])
    (by simp [lvD2, hR, h17]) (by simp [lvD2, hR, h18]) (by simp [lvD2, hR]; omega) (by simp [lvD2, hR, hp]; omega)
    (by simp [lvD2, hR, h10]; omega) (by omega)
  have v4 : ((τ.setv (V 9) (S + p - 1)).setv ((lvD2.trans V) 0)
      ((τ.setv (V 9) (S + p - 1)).val ((lvD2.trans V) 0) % (τ.setv (V 9) (S + p - 1)).val ((lvD2.trans V) 1))).setv
      ((lvD2.trans V) 2) ((τ.setv (V 9) (S + p - 1)).val ((lvD2.trans V) 2) +
        (τ.setv (V 9) (S + p - 1)).val ((lvD2.trans V) 0) / (τ.setv (V 9) (S + p - 1)).val ((lvD2.trans V) 1)) =
      (τ.setv (V 9) ((S + p - 1) % p)).setv (V 10) ((S + p - 1) / p) := by
    simp only [lvD2, Function.Embedding.trans_apply, Function.Embedding.coeFn_mk]
    simp [hR, hp, h10, wsetv_setv]
  have c4 : ((τ.setv (V 9) (S + p - 1)).val ((lvD2.trans V) 0) + 2) *
      (90 * (τ.setv (V 9) (S + p - 1)).val ((lvD2.trans V) 0) + 90 * (τ.setv (V 9) (S + p - 1)).val ((lvD2.trans V) 1) + 60) =
      (S + p - 1 + 2) * (90 * (S + p - 1) + 90 * p + 60) := by simp [lvD2, hR, hp]
  rw [v4, c4] at e4
  have e5 := wclear_spec cap (V 9) ((S + p - 1) % p) ((τ.setv (V 9) ((S + p - 1) % p)).setv (V 10) ((S + p - 1) / p))
    (by simp [hR]) (by simp [hR]; omega)
  have e6 := wclear_spec cap (V 8) p ((((τ.setv (V 9) ((S + p - 1) % p)).setv (V 10) ((S + p - 1) / p))).setv (V 9) 0)
    (by simp [hR, hp]) (by simp [hR, hp]; omega)
  refine ⟨_, WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 e6))))) ?_ le_rfl, ?_⟩
  · apply WState.eq
    · rfl
    · rfl
    · funext x
      simp only [WState.setv_val, Function.update_apply]
      by_cases x9 : x = V 9
      · subst x9; simp [hR, h9]
      · by_cases x10 : x = V 10
        · subst x10; simp [hR]
        · by_cases x8 : x = V 8
          · subst x8; simp [hR]
          · simp [x9, x10, x8]
    · rfl
  · unfold phBound
    have hA : (S + p - 1 + 2) * (90 * (S + p - 1) + 90 * p + 60) ≤ (cap + 2) * (200 * (cap + 2)) :=
      Nat.mul_le_mul (by omega) (by omega)
    have hC : (cap + 2) * (200 * (cap + 2)) = 200 * ((cap + 2) * (cap + 2)) := by ring
    have hE : 2000 * (cap + 2) * (cap + 2) = 2000 * ((cap + 2) * (cap + 2)) := by ring
    have hF : cap + 2 ≤ (cap + 2) * (cap + 2) := Nat.le_mul_self _
    rw [hE]
    omega

theorem lvPhC_spec (τ : WState ns nr) (J j q : ℕ) (hJ : τ.val (V 1) = J) (hj : τ.val (V 2) = j) (hjJ : j ≤ J)
    (hq : τ.val (V 10) = q) (h3 : τ.val (V 3) = 0) (h11 : τ.val (V 11) = 0) (h14 : τ.val (V 14) = 0)
    (h15 : τ.val (V 15) = 0) (h16 : τ.val (V 16) = 0) (hcap : q + J + 70 ≤ cap) :
    ∃ n, WExec cap (lvPhC V) τ ((τ.setv (V 10) 0).setv (V 3) (if j < J then 64 + q else 0)) n ∧ n ≤ phBound cap := by
  have hR : ∀ i k : Fin 24, V i = V k ↔ i = k := fun i k => V.injective.eq_iff
  have hne : ∀ {i k : Fin 24}, i ≠ k → V i ≠ V k := fun h => V.injective.ne h
  have e1 := wmove_spec cap (V 10) (V 3) (hne (by decide)) q τ hq (by omega) (by rw [h3, hq]; omega)
  rw [h3, hq, Nat.zero_add] at e1
  have e2 := StarNums.incN_spec cap (V 3) 64 ((τ.setv (V 10) 0).setv (V 3) q) (by simp; omega)
  rw [wsetv_setv, show ((τ.setv (V 10) 0).setv (V 3) q).val (V 3) + 64 = q + 64 by simp] at e2
  have e3 := UnaryArith.gtFlagW_spec cap (lvG.trans V) ((τ.setv (V 10) 0).setv (V 3) (q + 64))
    (by simp [lvG, hR, h11]) (by simp [lvG, hR, h14]) (by simp [lvG, hR, h15]) (by simp [lvG, hR, h16])
    (by simp [lvG, hR, hJ]; omega) (by simp [lvG, hR, hj]; omega) (by omega)
  have v3 : ((τ.setv (V 10) 0).setv (V 3) (q + 64)).setv ((lvG.trans V) 2)
      (if ((τ.setv (V 10) 0).setv (V 3) (q + 64)).val ((lvG.trans V) 1) <
        ((τ.setv (V 10) 0).setv (V 3) (q + 64)).val ((lvG.trans V) 0) then 1 else 0) =
      ((τ.setv (V 10) 0).setv (V 3) (q + 64)).setv (V 11) (if j < J then 1 else 0) := by
    simp [lvG, hR, hJ, hj]
  have c3 : 30 * ((τ.setv (V 10) 0).setv (V 3) (q + 64)).val ((lvG.trans V) 0) +
      30 * ((τ.setv (V 10) 0).setv (V 3) (q + 64)).val ((lvG.trans V) 1) + 20 = 30 * J + 30 * j + 20 := by
    simp [lvG, hR, hJ, hj]
  rw [v3, c3] at e3
  set ρ := ((τ.setv (V 10) 0).setv (V 3) (q + 64)).setv (V 11) (if j < J then 1 else 0) with hρ
  have e4 : ∃ m, WExec cap (.ifr (V 11) .skip (WM.clear (V 3))) ρ (ρ.setv (V 3) (if j < J then 64 + q else 0)) m ∧
      m ≤ 3 * (q + 64) + 2 := by
    by_cases hlt : j < J
    · refine ⟨_, WExec.ifrT (by simp [ρ, hlt]) (WExec.cast cap (WExec.skip ρ) ?_ le_rfl), by omega⟩
      simp only [hlt, if_true]
      exact (setv_eq_self (by simp [ρ, hR]; omega)).symm
    · have hc := wclear_spec cap (V 3) (q + 64) ρ (by simp [ρ, hR]) (by simp [ρ, hR]; omega)
      simp only [hlt, if_false]
      exact ⟨_, WExec.ifrF (by simp [ρ, hlt]) hc, by omega⟩
  obtain ⟨m4, e4, b4⟩ := e4
  have e5 := wclear_spec cap (V 11) (if j < J then 1 else 0) (ρ.setv (V 3) (if j < J then 64 + q else 0))
    (by simp [ρ, hR]) (by simp [ρ, hR]; split_ifs <;> omega)
  refine ⟨_, WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 e5)))) ?_ le_rfl, ?_⟩
  · apply WState.eq
    · rfl
    · rfl
    · funext x
      simp only [ρ, WState.setv_val, Function.update_apply]
      by_cases x11 : x = V 11
      · subst x11; simp [hR, h11]
      · by_cases x3 : x = V 3
        · subst x3; simp [hR]
        · by_cases x10 : x = V 10
          · subst x10; simp [hR]
          · simp [x11, x3, x10]
    · rfl
  · unfold phBound
    have hF : cap + 2 ≤ (cap + 2) * (cap + 2) := Nat.le_mul_self _
    have hE : 2000 * (cap + 2) * (cap + 2) = 2000 * ((cap + 2) * (cap + 2)) := by ring
    rw [hE]
    have : 3 * (if j < J then 1 else 0) + 1 ≤ 4 := by split_ifs <;> omega
    omega

theorem lvPhD_spec (τ : WState ns nr) (w : ℕ) (hw : τ.val (V 3) = w) (h4 : τ.val (V 4) = 0)
    (h12 : τ.val (V 12) = 0) (h13 : τ.val (V 13) = 0)
    (hz : ∀ i : Fin 24, 14 ≤ i.val → i.val ≤ 21 → τ.val (V i) = 0)
    (hcap : 2 ^ (Nat.clog 2 (2 * w + 1) + 1) + 2 * w + 10 ≤ cap) :
    ∃ n, WExec cap (lvPhD V) τ (τ.setv (V 4) (2 ^ Nat.clog 2 (2 * w + 1))) n ∧ n ≤ phBound cap := by
  have hR : ∀ i k : Fin 24, V i = V k ↔ i = k := fun i k => V.injective.eq_iff
  have hne : ∀ {i k : Fin 24}, i ≠ k → V i ≠ V k := fun h => V.injective.ne h
  have h14 := hz 14 (by decide) (by decide)
  have h15 := hz 15 (by decide) (by decide)
  have hcl : Nat.clog 2 (2 * w + 1) < 2 ^ Nat.clog 2 (2 * w + 1) := Nat.lt_two_pow_self
  have hpp : 2 ^ (Nat.clog 2 (2 * w + 1) + 1) = 2 * 2 ^ Nat.clog 2 (2 * w + 1) := by rw [pow_succ]; ring
  have e1 := ParseNat.addTo_spec cap (V 3) (V 12) (V 14) (hne (by decide)) (hne (by decide)) (hne (by decide))
    τ h14 (by omega) (by rw [h12, hw]; omega)
  rw [h12, hw, Nat.zero_add] at e1
  have e2 := ParseNat.addTo_spec cap (V 3) (V 12) (V 14) (hne (by decide)) (hne (by decide)) (hne (by decide))
    (τ.setv (V 12) w) (by simp [hR, h14]) (by simp [hR, hw]; omega) (by simp [hR, hw]; omega)
  rw [wsetv_setv, show (τ.setv (V 12) w).val (V 12) + (τ.setv (V 12) w).val (V 3) = 2 * w by simp [hR, hw]; omega,
    show (τ.setv (V 12) w).val (V 3) = w by simp [hR, hw]] at e2
  have e3 := WExec.inc (cap := cap) (V 12) (τ.setv (V 12) (2 * w)) (by simp; omega)
  rw [wsetv_setv, show (τ.setv (V 12) (2 * w)).val (V 12) + 1 = 2 * w + 1 by simp] at e3
  have e4 := PrimAsm.SymQM.clogW_spec cap (lvC.trans V) (τ.setv (V 12) (2 * w + 1)) (2 * w + 1) (by simp [lvC])
    (fun i hi => by
      fin_cases i <;> simp [lvC, hR] at hi ⊢ <;> first | exact h13 | exact hz _ (by decide) (by decide))
    (by omega)
  simp only [lvC, Function.Embedding.trans_apply, Function.Embedding.coeFn_mk] at e4
  have e5 := wclear_spec cap (V 12) (2 * w + 1) ((τ.setv (V 12) (2 * w + 1)).setv (V ((![12, 13, 14, 15, 16, 17, 18, 19, 20, 21] : Fin 10 → Fin 24) 1)) (Nat.clog 2 (2 * w + 1)))
    (by simp [hR]) (by simp [hR]; omega)
  simp only [Matrix.cons_val_one, Matrix.head_cons] at e4 e5
  set ρ := ((τ.setv (V 12) (2 * w + 1)).setv (V 13) (Nat.clog 2 (2 * w + 1))).setv (V 12) 0 with hρ
  have e6 := UnaryArith.pow2W_spec cap (lvP2.trans V) ρ (by simp [ρ, lvP2, hR, h4]) (by simp [ρ, lvP2, hR, h14])
    (by simp [ρ, lvP2, hR, h15]) (by simp [ρ, lvP2, hR]; omega)
  have v6 : ρ.setv ((lvP2.trans V) 1) (2 ^ ρ.val ((lvP2.trans V) 0)) = ρ.setv (V 4) (2 ^ Nat.clog 2 (2 * w + 1)) := by
    simp [ρ, lvP2, hR]
  have c6 : ρ.val ((lvP2.trans V) 0) * (18 * 2 ^ ρ.val ((lvP2.trans V) 0) + 7) + 18 * ρ.val ((lvP2.trans V) 0) + 20 =
      Nat.clog 2 (2 * w + 1) * (18 * 2 ^ Nat.clog 2 (2 * w + 1) + 7) + 18 * Nat.clog 2 (2 * w + 1) + 20 := by
    simp [ρ, lvP2, hR]
  rw [v6, c6] at e6
  have e7 := wclear_spec cap (V 13) (Nat.clog 2 (2 * w + 1)) (ρ.setv (V 4) (2 ^ Nat.clog 2 (2 * w + 1)))
    (by simp [ρ, hR]) (by simp [ρ, hR]; omega)
  refine ⟨_, WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 (WExec.seq e6 e7))))))
    ?_ le_rfl, ?_⟩
  · apply WState.eq
    · rfl
    · rfl
    · funext x
      simp only [ρ, WState.setv_val, Function.update_apply]
      by_cases x12 : x = V 12
      · subst x12; simp [hR, h12]
      · by_cases x13 : x = V 13
        · subst x13; simp [hR, h13]
        · by_cases x4 : x = V 4
          · subst x4; simp [hR]
          · simp [x12, x13, x4]
    · rfl
  · unfold phBound
    have hsq := UnaryPow.sq_ge cap
    have hB : Nat.clog 2 (2 * w + 1) * (18 * 2 ^ Nat.clog 2 (2 * w + 1) + 7) ≤ (cap + 2) * (25 * (cap + 2)) :=
      Nat.mul_le_mul (by omega) (by omega)
    have hD : (cap + 2) * (25 * (cap + 2)) = 25 * ((cap + 2) * (cap + 2)) := by ring
    have hE : 2000 * (cap + 2) * (cap + 2) = 2000 * ((cap + 2) * (cap + 2)) := by ring
    have hF : cap + 2 ≤ (cap + 2) * (cap + 2) := Nat.le_mul_self _
    rw [hE]
    omega

/-- A sufficient register capacity for one level at `S`, `J`, `j`. -/
def lvCap (S J j : ℕ) : ℕ := 10 * 2 ^ (j / 3) + 10 * S + 2 * J + 700

theorem pow_clog_le (x : ℕ) (hx : 1 ≤ x) : 2 ^ Nat.clog 2 x ≤ 2 * x := by
  rcases Nat.lt_or_ge 1 x with h | h
  · have h1 := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) h
    have hpos : 1 ≤ Nat.clog 2 x := Nat.clog_pos (by norm_num) h
    have e : 2 ^ Nat.clog 2 x = 2 * 2 ^ (Nat.clog 2 x - 1) := by rw [← pow_succ']; congr 1; omega
    simp only [Nat.pred_eq_sub_one] at h1
    omega
  · have hx1 : x = 1 := by omega
    subst hx1; simp

theorem winAt_le (S J j : ℕ) : winAt S J j ≤ 64 + S + 2 ^ (j / 3) := by
  unfold winAt
  have h1 := Nat.div_le_self (S + 2 ^ (j / 3) - 1) (2 ^ (j / 3))
  have h2 : 1 ≤ 2 ^ (j / 3) := Nat.one_le_two_pow
  generalize (S + 2 ^ (j / 3) - 1) / 2 ^ (j / 3) = q at h1 ⊢
  generalize 2 ^ (j / 3) = p at h1 h2 ⊢
  split_ifs <;> omega

/-- **The level program's result**: `W := winAt S J j`, `P := 2^{⌈log₂(2W+1)⌉}`, all scratch back to `0`. -/
theorem levelVals_spec (σ : WState ns nr) (S J j : ℕ) (hS : σ.val (V 0) = S) (hJ : σ.val (V 1) = J)
    (hj : σ.val (V 2) = j) (hjJ : j ≤ J) (hz : ∀ i : Fin 24, 3 ≤ i.val → σ.val (V i) = 0) (hcap : lvCap S J j ≤ cap) :
    ∃ n, WExec cap (levelVals V) σ
      ((σ.setv (V 3) (winAt S J j)).setv (V 4) (2 ^ Nat.clog 2 (2 * winAt S J j + 1))) n ∧
      n ≤ 4 * phBound cap + 3 := by
  have hR : ∀ i k : Fin 24, V i = V k ↔ i = k := fun i k => V.injective.eq_iff
  have hp1 : 1 ≤ 2 ^ (j / 3) := Nat.one_le_two_pow
  have hpp : 2 ^ (j / 3 + 1) = 2 * 2 ^ (j / 3) := by rw [pow_succ]; ring
  have hq : (S + 2 ^ (j / 3) - 1) / 2 ^ (j / 3) ≤ S + 2 ^ (j / 3) := le_trans (Nat.div_le_self _ _) (by omega)
  have hwl := winAt_le S J j
  have hcl := pow_clog_le (2 * winAt S J j + 1) (by omega)
  have hcp : 2 ^ (Nat.clog 2 (2 * winAt S J j + 1) + 1) = 2 * 2 ^ Nat.clog 2 (2 * winAt S J j + 1) := by
    rw [pow_succ]; ring
  unfold lvCap at hcap
  obtain ⟨nA, eA, bA⟩ := lvPhA_spec cap V σ j hj (hz 5 (by decide)) (hz 6 (by decide)) (hz 7 (by decide))
    (hz 8 (by decide)) (hz 14 (by decide)) (hz 15 (by decide)) (hz 16 (by decide)) (hz 17 (by decide))
    (hz 18 (by decide)) (by omega)
  obtain ⟨nB, eB, bB⟩ := lvPhB_spec cap V (σ.setv (V 8) (2 ^ (j / 3))) S (2 ^ (j / 3)) (by simp [hR, hS]) (by simp)
    hp1 (by simp [hR, hz 9 (by decide)]) (by simp [hR, hz 10 (by decide)]) (by simp [hR, hz 14 (by decide)])
    (by simp [hR, hz 15 (by decide)]) (by simp [hR, hz 16 (by decide)]) (by simp [hR, hz 17 (by decide)])
    (by simp [hR, hz 18 (by decide)]) (by omega)
  obtain ⟨nC, eC, bC⟩ := lvPhC_spec cap V
    (((σ.setv (V 8) (2 ^ (j / 3))).setv (V 10) ((S + 2 ^ (j / 3) - 1) / 2 ^ (j / 3))).setv (V 8) 0) J j
    ((S + 2 ^ (j / 3) - 1) / 2 ^ (j / 3)) (by simp [hR, hJ]) (by simp [hR, hj]) hjJ (by simp [hR])
    (by simp [hR, hz 3 (by decide)]) (by simp [hR, hz 11 (by decide)]) (by simp [hR, hz 14 (by decide)])
    (by simp [hR, hz 15 (by decide)]) (by simp [hR, hz 16 (by decide)]) (by omega)
  have hw : (if j < J then 64 + (S + 2 ^ (j / 3) - 1) / 2 ^ (j / 3) else 0) = winAt S J j := by
    unfold winAt
    by_cases hjJ' : j = J
    · subst hjJ'; simp
    · rw [if_pos (by omega), if_neg hjJ']
  rw [hw] at eC
  obtain ⟨nD, eD, bD⟩ := lvPhD_spec cap V
    (((((σ.setv (V 8) (2 ^ (j / 3))).setv (V 10) ((S + 2 ^ (j / 3) - 1) / 2 ^ (j / 3))).setv (V 8) 0).setv
      (V 10) 0).setv (V 3) (winAt S J j)) (winAt S J j) (by simp) (by simp [hR, hz 4 (by decide)])
    (by simp [hR, hz 12 (by decide)]) (by simp [hR, hz 13 (by decide)])
    (fun i h1 h2 => by
      have n3 : i ≠ 3 := fun h => by rw [h] at h1; exact absurd h1 (by decide)
      have n8 : i ≠ 8 := fun h => by rw [h] at h1; exact absurd h1 (by decide)
      have n10 : i ≠ 10 := fun h => by rw [h] at h1; exact absurd h1 (by decide)
      simp [hR, n3, n8, n10, hz i (by omega)])
    (by omega)
  refine ⟨_, WExec.cast cap (WExec.seq eA (WExec.seq eB (WExec.seq eC eD))) ?_ le_rfl, by omega⟩
  apply WState.eq
  · rfl
  · rfl
  · funext x
    simp only [WState.setv_val, Function.update_apply]
    by_cases x4 : x = V 4
    · subst x4; simp [hR]
    · by_cases x3 : x = V 3
      · subst x3; simp [hR]
      · by_cases x10 : x = V 10
        · subst x10; simp [hR, hz 10 (by decide)]
        · by_cases x8 : x = V 8
          · subst x8; simp [hR, hz 8 (by decide)]
          · simp [x4, x3, x10, x8]
  · rfl

end Level

theorem winAt_eq (P : Lists.BaseListParams) (j : ℕ) :
    winAt (natCeilSqrt (64 ^ 2 * P.B)) P.J j = FinalPass.ListEval.topW P.J P.W j := by
  unfold winAt FinalPass.ListEval.topW Lists.BaseListParams.W
  split_ifs
  · rfl
  · rw [Nat.ceilDiv_eq_add_pred_div]

/-- **The computed power is the record's `pow W'_j`.** -/
theorem powAt_eq (P : Lists.BaseListParams) (j : ℕ) :
    2 ^ Nat.clog 2 (2 * winAt (natCeilSqrt (64 ^ 2 * P.B)) P.J j + 1) =
      FinalPass.ListEval.pow (FinalPass.ListEval.topW P.J P.W j) := by
  rw [winAt_eq]; rfl

end NearCubicWires.WireExponent3_5.PrimAsm.LevelW
