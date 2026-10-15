import Proof.Gates.OuterM.ARunW
import Proof.Gates.OuterM.WidthW

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicGates.Close.OuterM

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.Succinct

variable {ns nr : ℕ} (cap : ℕ)

/-! ## The field walk -/

/-- Skip `ELL` cells of `S`, counting in `P`; `ELL := 0`. -/
def payW (S : Fin (ns + 1)) (P ELL : Fin nr) : WM ns nr := .whr ELL (.seq (.dec ELL) (WM.fwdC S P))

theorem payW_spec (S : Fin (ns + 1)) (P ELL : Fin nr) (hPE : P ≠ ELL) :
    ∀ (n : ℕ) (σ : WState ns nr), σ.val ELL = n → σ.val P + n ≤ cap → n ≤ cap →
      WExec cap (payW S P ELL) σ (((σ.seth S (σ.sh S + n)).setv P (σ.val P + n)).setv ELL 0) (9 * n + 1)
  | 0, σ, hE, _, _ => by
    refine WExec.cast cap (WExec.whrF hE) ?_ (by omega)
    refine WState.eq ?_ rfl ?_ rfl
    · funext x; simp only [WState.setv_sh, WState.seth_sh, Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all
    · funext x; simp only [WState.setv_val, WState.seth_val, Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all
  | n + 1, σ, hE, hP, hn => by
    have e1 := WExec.dec (cap := cap) ELL σ (by omega)
    set σ1 := σ.setv ELL (σ.val ELL - 1) with hσ1
    have e2 := wfwdC_spec cap S P σ1 (by simp [σ1, Function.update_apply, hPE]; omega)
    set σ2 := (σ1.seth S (σ1.sh S + 1)).setv P (σ1.val P + 1) with hσ2
    have ih := payW_spec S P ELL hPE n σ2 (by simp [σ2, σ1, Function.update_apply, Ne.symm hPE, hE])
      (by simp [σ2, σ1, Function.update_apply, hPE]; omega) (by omega)
    refine WExec.cast cap (WExec.whrT (by omega) (WExec.seq e1 e2) ih) ?_ (by omega)
    refine WState.eq ?_ rfl ?_ rfl
    · funext x; simp only [σ2, σ1, WState.setv_sh, WState.seth_sh, Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all <;> omega
    · funext x; simp only [σ2, σ1, WState.setv_val, WState.seth_val, Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all <;> omega

/-- The walk over the fields of `S` (head position in `P`, field length scratch `ELL`). -/
def walkW (S : Fin (ns + 1)) (P ELL : Fin nr) : WM ns nr := .whs S (.seq (WM.readU S P ELL) (payW S P ELL))

/-- **The walk** (paper v2 §11.4, the guard on the description length): from `pos`, the head and `P` end at
`walkEnd (σ.st S) pos`, within `11` steps per cell walked. -/
theorem walkW_spec (S : Fin (ns + 1)) (P ELL : Fin nr) (hPE : P ≠ ELL) (d : List Bool) :
    ∀ (pos : ℕ) (σ : WState ns nr), σ.st S = d → σ.sh S = pos → σ.val P = pos → σ.val ELL = 0 →
      pos ≤ 2 * d.length + 1 → 2 * d.length + 2 ≤ cap →
      WExec cap (walkW S P ELL) σ ((σ.seth S (walkEnd d pos)).setv P (walkEnd d pos))
        (11 * (walkEnd d pos - pos) + 1) := by
  intro pos
  induction pos using walkEnd.induct d with
  | case1 pos h ih =>
    intro σ hst hsh hP hE hpos hcap
    have hw := walkEnd_true h
    have hl := readTapeBit_lt h
    have hones := ones_le_drop d pos
    have hle := le_walkEnd d (fieldEnd d pos)
    have hfe : fieldEnd d pos = pos + 2 * ones d pos + 1 := rfl
    have hb : wbit σ S = true := by unfold wbit; rw [hst, hsh]; exact h
    have e1 := wreadU_spec cap S P ELL hPE (ones d pos) σ
      (fun k hk => by rw [hst, hsh]; exact ones_true d pos k hk) (by rw [hst, hsh]; exact ones_false d pos)
      (by rw [hP]; omega) (by rw [hE]; omega)
    set σ1 := ((σ.seth S (σ.sh S + ones d pos + 1)).setv P (σ.val P + ones d pos + 1)).setv ELL
      (σ.val ELL + ones d pos) with hσ1
    have e2 := payW_spec cap S P ELL hPE (ones d pos) σ1 (by simp [σ1, hE])
      (by simp [σ1, Function.update_apply, hPE, hP]; omega) (by omega)
    set σ2 := ((σ1.seth S (σ1.sh S + ones d pos)).setv P (σ1.val P + ones d pos)).setv ELL 0 with hσ2
    have ih' := ih σ2 (by simp [σ2, σ1, hst]) (by simp [σ2, σ1, hsh, hfe]; omega)
      (by simp [σ2, σ1, Function.update_apply, hPE, hP, hfe]; omega) (by simp [σ2])
      (by rw [hfe]; omega) hcap
    refine WExec.cast cap (WExec.whsT hb (WExec.seq e1 e2) ih') ?_ (by rw [hw]; have := hfe; have := hle; omega)
    rw [hw]
    refine WState.eq ?_ rfl ?_ rfl
    · funext x; simp only [σ2, σ1, WState.setv_sh, WState.seth_sh, Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all
    · funext x; simp only [σ2, σ1, WState.setv_val, WState.seth_val, Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all
  | case2 pos h =>
    intro σ hst hsh hP hE _ _
    have h' : readTapeBit d pos = false := by simpa using h
    have hb : wbit σ S = false := by unfold wbit; rw [hst, hsh]; exact h'
    rw [walkEnd_false h']
    refine WExec.cast cap (WExec.whsF hb) ?_ (by omega)
    have e0 : σ.seth S pos = σ := by rw [← hsh]; exact wseth_same σ S
    rw [e0, ← hP, wsetv_same]

/-! ## The length of a raw binary word -/

/-- The count of trailing zeros. -/
def zstep (z : ℕ) (b : Bool) : ℕ := if b then 0 else z + 1

theorem foldl_zstep_le : ∀ (l : List Bool) (z : ℕ), l.foldl zstep z ≤ z + l.length
  | [], z => by simp
  | b :: l, z => by
    simp only [List.foldl_cons, List.length_cons]
    have := foldl_zstep_le l (zstep z b)
    unfold zstep at this ⊢
    split_ifs at this ⊢ <;> omega

theorem foldl_zstep_replicate (z k : ℕ) : (List.replicate k false).foldl zstep z = z + k := by
  induction k generalizing z with
  | zero => simp
  | succ k ih => rw [List.replicate_succ, List.foldl_cons]; simp [zstep, ih]; ring

theorem foldl_zstep_last (l : List Bool) (z : ℕ) : (l ++ [true]).foldl zstep z = 0 := by
  simp [List.foldl_append, zstep]

/-- The bits of a positive number end with `1`. -/
theorem bits_last (v : ℕ) (hv : v ≠ 0) : ∃ l, v.bits = l ++ [true] := by
  induction v using Nat.strong_induction_on with
  | _ v ih =>
    rw [bits_cons v hv]
    rcases Nat.eq_zero_or_pos (v / 2) with h0 | hpos
    · have hv1 : v = 1 := by omega
      subst hv1
      exact ⟨[], by simp⟩
    · obtain ⟨l, hl⟩ := ih (v / 2) (by omega) (by omega)
      exact ⟨decide (v % 2 = 1) :: l, by rw [hl]; rfl⟩

theorem cellsOf_append_zeros (w : List Bool) (B : ℕ) (hB : w.length ≤ B) :
    cellsOf w B = w ++ List.replicate (B - w.length) false := by
  apply List.ext_getElem
  · simp [cellsOf]; omega
  · intro i h1 h2
    simp only [cellsOf, List.getElem_ofFn]
    unfold readTapeBit
    by_cases hi : i < w.length
    · rw [List.getD_eq_getElem _ _ hi, List.getElem_append_left hi]
    · rw [List.getD_eq_default _ _ (by omega), List.getElem_append_right (by omega)]
      simp

/-- **The length of `T.bits`**: `B` minus the trailing zeros among the first `B` cells. -/
theorem len_of_trail (v B : ℕ) (hB : v.bits.length ≤ B) :
    B - (cellsOf v.bits B).foldl zstep 0 = v.bits.length := by
  rw [cellsOf_append_zeros _ _ hB, List.foldl_append]
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · simp [foldl_zstep_replicate]
  · obtain ⟨l, hl⟩ := bits_last v (by omega)
    rw [hl, foldl_zstep_last, foldl_zstep_replicate]
    rw [hl] at hB
    omega

theorem cellsOf_self (w : List Bool) : cellsOf w w.length = w := by
  rw [cellsOf_append_zeros w _ le_rfl]; simp

/-- Scan `n` cells of `TB` (from its head), counting trailing zeros in `ZR` and the head in `HP`; `CNT := 0`. -/
def scanW (TB : Fin (ns + 1)) (CNT ZR HP : Fin nr) : WM ns nr :=
  .whr CNT (.seq (.dec CNT) (.seq (.ifs TB (WM.clear ZR) (.inc ZR)) (WM.fwdC TB HP)))

theorem scanW_spec (TB : Fin (ns + 1)) (CNT ZR HP : Fin nr) (h1 : CNT ≠ ZR) (h2 : CNT ≠ HP) (h3 : ZR ≠ HP) :
    ∀ (n : ℕ) (σ : WState ns nr), σ.val CNT = n → σ.val ZR + n ≤ cap → σ.val HP + n ≤ cap → n ≤ cap →
      WExec cap (scanW TB CNT ZR HP) σ
        ((((σ.seth TB (σ.sh TB + n)).setv HP (σ.val HP + n)).setv ZR
          ((List.ofFn fun i : Fin n => readTapeBit (σ.st TB) (σ.sh TB + i.val)).foldl zstep (σ.val ZR))).setv CNT 0)
        (n * (3 * (σ.val ZR + n) + 15) + 1)
  | 0, σ, hC, _, _, _ => by
    refine WExec.cast cap (WExec.whrF hC) ?_ (by omega)
    refine WState.eq ?_ rfl ?_ rfl
    · funext x; simp only [WState.setv_sh, WState.seth_sh, Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all
    · funext x; simp only [WState.setv_val, WState.seth_val, Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all
  | n + 1, σ, hC, hZ, hH, hn => by
    have e1 := WExec.dec (cap := cap) CNT σ (by omega)
    set σ1 := σ.setv CNT (σ.val CNT - 1) with hσ1
    set b := readTapeBit (σ.st TB) (σ.sh TB) with hbdef
    have hb : wbit σ1 TB = b := rfl
    have hZ1 : σ1.val ZR = σ.val ZR := by simp [σ1, Function.update_apply, Ne.symm h1]
    obtain ⟨σ2, e2, hσ2, hc2⟩ : ∃ σ2, WExec cap (.ifs TB (WM.clear ZR) (.inc ZR)) σ1 σ2 (3 * σ.val ZR + 4) ∧
        σ2 = σ1.setv ZR (zstep (σ.val ZR) b) ∧ True := by
      cases hbv : b
      · refine ⟨_, WExec.mono (WExec.ifsF (by rw [hb, hbv]) (WExec.inc (cap := cap) ZR σ1 (by rw [hZ1]; omega)))
          (by omega), by simp [zstep, hZ1], trivial⟩
      · refine ⟨_, WExec.mono (WExec.ifsT (by rw [hb, hbv]) (wclear_spec cap ZR (σ1.val ZR) σ1 rfl (by rw [hZ1]; omega)))
          (by rw [hZ1]; omega), by simp [zstep], trivial⟩
    subst hσ2
    have e3 := wfwdC_spec cap TB HP (σ1.setv ZR (zstep (σ.val ZR) b))
      (by simp [σ1, Function.update_apply, Ne.symm h2, Ne.symm h3]; omega)
    set σ3 := ((σ1.setv ZR (zstep (σ.val ZR) b)).seth TB ((σ1.setv ZR (zstep (σ.val ZR) b)).sh TB + 1)).setv HP
      ((σ1.setv ZR (zstep (σ.val ZR) b)).val HP + 1) with hσ3
    have hz3 : σ3.val ZR = zstep (σ.val ZR) b := by simp [σ3, Function.update_apply, h3]
    have hzle : zstep (σ.val ZR) b ≤ σ.val ZR + 1 := by unfold zstep; split_ifs <;> omega
    have ih := scanW_spec TB CNT ZR HP h1 h2 h3 n σ3 (by simp [σ3, σ1, Function.update_apply, h1, h2, hC])
      (by rw [hz3]; omega) (by simp [σ3, σ1, Function.update_apply, Ne.symm h2, Ne.symm h3]; omega)
      (by omega)
    refine WExec.cast cap (WExec.whrT (by omega) (WExec.seq e1 (WExec.seq e2 e3)) ih) ?_ ?_
    · have hst : σ3.st TB = σ.st TB := by simp [σ3, σ1]
      have hsh : σ3.sh TB = σ.sh TB + 1 := by simp [σ3, σ1]
      have hfold : (List.ofFn fun i : Fin n => readTapeBit (σ3.st TB) (σ3.sh TB + i.val)).foldl zstep (σ3.val ZR) =
          (List.ofFn fun i : Fin (n + 1) => readTapeBit (σ.st TB) (σ.sh TB + i.val)).foldl zstep (σ.val ZR) := by
        rw [hst, hsh, hz3, ← ofFn_succ_read, List.foldl_cons]
      rw [hfold]
      refine WState.eq ?_ rfl ?_ rfl
      · funext x; simp only [σ3, σ1, WState.setv_sh, WState.seth_sh, Function.update_apply]
        split_ifs <;> subst_vars <;> simp_all <;> omega
      · funext x; simp only [σ3, σ1, WState.setv_val, WState.seth_val, Function.update_apply]
        split_ifs <;> subst_vars <;> simp_all <;> omega
    · rw [hz3]; nlinarith

end NearCubicGates.Close.OuterM
