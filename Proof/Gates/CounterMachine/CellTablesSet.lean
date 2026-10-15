import Proof.Gates.Cells.Run

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.CounterMachine.CellTablesProg

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat (readNatM readNatM_spec stp)
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Cells

/-- The lower bound `k'` of `k`, from `L = natBitLength n`. -/
def kLow (cT L : ℕ) : ℕ := (2 + cT + 3 * Nat.size (L - 2)) * (L - 1)

section Block
variable {ns nr : ℕ} (cap : ℕ) (R : Fin 12 ↪ Fin nr) (I : Fin (ns + 1)) (G B : Fin nr)

/-- `x := x / 2` through `h` (at `0`): pairs of decrements. -/
def halfL (x h : Fin nr) : WMX ns nr := .whr x (.seq (WMX.dec x) (.ifr x (.seq (WMX.dec x) (WMX.inc h)) WMX.skip))

def halfP (x h : Fin nr) : WMX ns nr := .seq (halfL x h) (.wm (WM.move h x))

/-- `m += size x`, `x := 0`. -/
def sizeL (x h m : Fin nr) : WMX ns nr := .whr x (.seq (WMX.inc m) (halfP x h))

/-- `D := D·F` with the counter `K` (spent) and the scratch `T`. -/
def mulL (K F D T : Fin nr) : WMX ns nr := .whr K (.seq (WMX.dec K) (addR F D T))

/-- `A := A − K` (truncated), `K := 0`. -/
def subL (K A : Fin nr) : WMX ns nr := .whr K (.seq (WMX.dec K) (WMX.dec A))

/-- Read `n` into `R 2` and rewind the input (count `4L + 2` in `R 5`). -/
def bkA : WMX ns nr :=
  .seq (.wm (readNatM true I (R 0) (R 1) (R 2) (R 3) (R 4)))
  (.seq (addR G (R 5) (R 6)) (.seq (addR G (R 5) (R 6)) (.seq (addR G (R 5) (R 6)) (.seq (addR G (R 5) (R 6))
  (.seq (Cells.incN (R 5) 2) (.wm (WM.rewind I (R 5))))))))

/-- `R 8 := size (L − 2)`, then the factor `R 9 := 2 + c_T + 3·R 8`. -/
def bkB (cT : ℕ) : WMX ns nr :=
  .seq (addR G (R 7) (R 6)) (.seq (WMX.dec (R 7)) (.seq (WMX.dec (R 7)) (.seq (sizeL (R 7) (R 6) (R 8))
  (.seq (Cells.incN (R 9) (2 + cT)) (.seq (addR (R 8) (R 9) (R 6)) (.seq (addR (R 8) (R 9) (R 6))
  (.seq (addR (R 8) (R 9) (R 6)) (Cells.clearR (R 8)))))))))

/-- `R 10 := k' = R 9·(L − 1)`, then `R 2 := n − k'`. -/
def bkC : WMX ns nr :=
  .seq (addR G (R 11) (R 6)) (.seq (WMX.dec (R 11)) (.seq (mulL (R 11) (R 9) (R 10) (R 6))
  (.seq (Cells.clearR (R 9)) (subL (R 10) (R 2)))))

/-- `B := 2^{R 2}·B`, then `R 2 := 0`. -/
def bkD : WMX ns nr := .seq (Cells.pw2 B (R 4) (R 3) (R 2) (R 1) 1) (Cells.clearR (R 2))

/-- **The block.** Registers: `R 0, R 1, R 3, R 4` reader scratch, `R 2` the value `n`, `R 5` the rewind count,
`R 6` scratch, `R 7` `L − 2` (spent), `R 8` the size, `R 9` the factor, `R 10` `k'`, `R 11` `L − 1` (spent). -/
def bkBlk (cT : ℕ) : WMX ns nr := .seq (bkA R I G) (.seq (bkB R G cT) (.seq (bkC R G) (bkD R B)))

theorem halfL_spec (x h : Fin nr) (hxh : x ≠ h) :
    ∀ (j : ℕ) (σ : WState ns nr), σ.val x = j → j ≤ cap → σ.val h + j ≤ cap →
      WXExec cap (halfL x h) σ ((σ.setv x 0).setv h (σ.val h + j / 2)) (6 * j + 1) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro σ hv hj hhj
    rcases j with _ | _ | j
    · have e : (σ.setv x 0).setv h (σ.val h + 0 / 2) = σ := by
        refine WState.eq rfl rfl ?_ rfl
        funext r; simp only [WState.setv_val, Function.update_apply]
        split_ifs with h1 h2 <;> subst_vars <;> simp_all
      rw [e]; exact WXExec.whrF hv
    · have h1 := WXExec.dec cap x σ (by omega)
      rw [hv] at h1
      have h2 : WXExec cap (.ifr x (.seq (WMX.dec x) (WMX.inc h)) WMX.skip) (σ.setv x (0 + 1 - 1))
          (σ.setv x (0 + 1 - 1)) (0 + 1) := WXExec.ifrF (by simp) (WXExec.skip cap _)
      have h3 : WXExec cap (halfL x h) (σ.setv x (0 + 1 - 1)) (σ.setv x (0 + 1 - 1)) 1 := WXExec.whrF (by simp)
      refine (WXExec.whrT (by omega) (WXExec.seq h1 h2) h3).cast cap ?_ (by omega)
      refine WState.eq rfl rfl ?_ rfl
      funext r; simp only [WState.setv_val, Function.update_apply]
      split_ifs with h1 h2 <;> subst_vars <;> simp_all
    · have h1 := WXExec.dec cap x σ (by omega)
      rw [hv] at h1
      set σ1 := σ.setv x (j + 1 + 1 - 1) with hσ1
      have h2a := WXExec.dec cap x σ1 (by simp [σ1]; omega)
      set σ2 := σ1.setv x (σ1.val x - 1) with hσ2
      have h2b := WXExec.inc cap h σ2 (by simp [σ2, σ1, Function.update_of_ne (Ne.symm hxh)]; omega)
      have h2 : WXExec cap (.ifr x (.seq (WMX.dec x) (WMX.inc h)) WMX.skip) σ1 (σ2.setv h (σ2.val h + 1)) _ :=
        WXExec.ifrT (by simp [σ1]) (WXExec.seq h2a h2b)
      have hσ2v : σ2.val x = j := by simp [σ2, σ1]
      have h3 := ih j (by omega) (σ2.setv h (σ2.val h + 1)) (by simp [Function.update_of_ne hxh, hσ2v]) (by omega)
        (by simp [σ2, σ1, Function.update_of_ne (Ne.symm hxh)]; omega)
      refine (WXExec.whrT (by omega) (WXExec.seq h1 h2) h3).cast cap ?_ (by omega)
      refine WState.eq rfl rfl ?_ rfl
      funext r
      simp only [σ2, σ1, WState.setv_val, Function.update_apply]
      have : (j + 1 + 1) / 2 = j / 2 + 1 := by omega
      by_cases rh : r = h
      · subst rh; simp [hxh.symm, this]; omega
      · by_cases rx : r = x
        · subst rx; simp [rh]
        · simp [rh, rx]

theorem halfP_spec (x h : Fin nr) (hxh : x ≠ h) (σ : WState ns nr) (j : ℕ) (hv : σ.val x = j) (hh : σ.val h = 0)
    (hj : 2 * j + 2 ≤ cap) : WXExec cap (halfP x h) σ (σ.setv x (j / 2)) (6 * j + 7 * (j / 2) + 3) := by
  have h1 := halfL_spec cap x h hxh j σ hv (by omega) (by rw [hh]; omega)
  rw [hh, zero_add] at h1
  set σ1 := (σ.setv x 0).setv h (j / 2) with hσ1
  have h2 := wmove_spec (cap := cap) h x (Ne.symm hxh) (j / 2) σ1 (by simp [σ1]) (by simp [σ1]; omega)
    (by simp [σ1, Function.update_of_ne hxh]; omega)
  refine (WXExec.seq h1 (WXExec.wm h2)).cast cap ?_ (by omega)
  refine WState.eq rfl rfl ?_ rfl
  funext r
  simp only [σ1, WState.setv_val, Function.update_apply]
  by_cases rx : r = x
  · subst rx; simp [hxh]
  · by_cases rh : r = h
    · subst rh; simp [rx, hh]
    · simp [rx, rh]

theorem size_half (x : ℕ) (h : 0 < x) : Nat.size x = Nat.size (x / 2) + 1 := by
  have h1 : Nat.size x ≤ Nat.size (x / 2) + 1 := by
    rw [Nat.size_le]
    have := Nat.lt_size_self (x / 2)
    rw [Nat.pow_succ]; omega
  have h2 : Nat.size (x / 2) + 1 ≤ Nat.size x := by
    rcases Nat.eq_zero_or_pos (x / 2) with h0 | h0
    · rw [h0, Nat.size_zero]; exact Nat.size_pos.mpr h
    · have hp := Nat.size_pos.mpr h0
      have h4 : 2 ^ (Nat.size (x / 2) - 1) ≤ x / 2 := by
        by_contra hc
        have : Nat.size (x / 2) ≤ Nat.size (x / 2) - 1 := Nat.size_le.mpr (by omega)
        omega
      by_contra hc
      have h5 : x < 2 ^ Nat.size (x / 2) := Nat.size_le.mp (by omega)
      have : 2 ^ (Nat.size (x / 2) - 1) * 2 = 2 ^ Nat.size (x / 2) := by
        rw [← Nat.pow_succ]; congr 1; omega
      omega
  omega

theorem sizeL_spec (x h m : Fin nr) (hxh : x ≠ h) (hxm : x ≠ m) (hhm : h ≠ m) :
    ∀ (j : ℕ) (σ : WState ns nr), σ.val x = j → σ.val h = 0 → 2 * j + 2 ≤ cap → σ.val m + Nat.size j ≤ cap →
      WXExec cap (sizeL x h m) σ ((σ.setv x 0).setv m (σ.val m + Nat.size j)) (20 * j + 20 * Nat.size j + 1) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro σ hv hh hc hm
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · subst h0
      have e : (σ.setv x 0).setv m (σ.val m + Nat.size 0) = σ := by
        refine WState.eq rfl rfl ?_ rfl
        funext r; simp only [WState.setv_val, Function.update_apply, Nat.size_zero]
        split_ifs with h1 h2 <;> subst_vars <;> simp_all
      rw [e]; exact WXExec.whrF hv
    · have hs := size_half j hpos
      have h1 := WXExec.inc cap m σ (by omega)
      set σ1 := σ.setv m (σ.val m + 1) with hσ1
      have h2 := halfP_spec cap x h hxh σ1 j (by simp [σ1, Function.update_of_ne hxm, hv])
        (by simp [σ1, Function.update_of_ne hhm, hh]) hc
      set σ2 := σ1.setv x (j / 2) with hσ2
      have h3 := ih (j / 2) (by omega) σ2 (by simp [σ2]) (by simp [σ2, σ1, Function.update_of_ne hxh.symm,
        Function.update_of_ne hhm, hh]) (by omega) (by simp [σ2, σ1, Function.update_of_ne hxm.symm]; omega)
      refine (WXExec.whrT (by omega) (WXExec.seq h1 h2) h3).cast cap ?_ ?_
      · refine WState.eq rfl rfl ?_ rfl
        funext r
        simp only [σ2, σ1, WState.setv_val, Function.update_apply]
        by_cases rx : r = x
        · subst rx; simp [hxm]
        · by_cases rm : r = m
          · subst rm; simp [rx, Function.update_of_ne hxm.symm]; omega
          · simp [rx, rm]
      · have : j / 2 ≤ j := Nat.div_le_self j 2
        omega

theorem mulL_spec (K F D T : Fin nr) (hKF : K ≠ F) (hKD : K ≠ D) (hKT : K ≠ T) (hFD : F ≠ D) (hFT : F ≠ T)
    (hDT : D ≠ T) :
    ∀ (j : ℕ) (σ : WState ns nr), σ.val K = j → σ.val T = 0 → j ≤ cap → σ.val D + j * σ.val F ≤ cap →
      WXExec cap (mulL K F D T) σ ((σ.setv K 0).setv D (σ.val D + j * σ.val F)) (j * (18 * σ.val F + 7) + 1) := by
  intro j
  induction j with
  | zero =>
    intro σ hv _ _ _
    have e : (σ.setv K 0).setv D (σ.val D + 0 * σ.val F) = σ := by
      refine WState.eq rfl rfl ?_ rfl
      funext r; simp only [WState.setv_val, Function.update_apply]
      split_ifs with h1 h2 <;> subst_vars <;> simp_all
    rw [e]; exact WXExec.mono (WXExec.whrF hv) (by omega)
  | succ j ih =>
    intro σ hv hT hj hc
    have h1 := WXExec.dec cap K σ (by omega)
    rw [hv, show j + 1 - 1 = j by omega] at h1
    set σ1 := σ.setv K j with hσ1
    have h2 := addR_spec cap hFD hFT hDT σ1 (by simp [σ1, Function.update_of_ne hKT.symm, hT])
      (by simp [σ1, Function.update_of_ne hKD.symm, Function.update_of_ne hKF.symm]; nlinarith)
    set σ2 := σ1.setv D (σ1.val D + σ1.val F) with hσ2
    have hF2 : σ2.val F = σ.val F := by simp [σ2, σ1, Function.update_of_ne hFD, Function.update_of_ne hKF.symm]
    have h3 := ih σ2 (by simp [σ2, σ1, Function.update_of_ne hKD]) (by
      simp [σ2, σ1, Function.update_of_ne hDT.symm, Function.update_of_ne hKT.symm, hT]) (by omega) (by
      rw [hF2]; simp [σ2, σ1, Function.update_of_ne hKD.symm, Function.update_of_ne hKF.symm]; nlinarith)
    rw [hF2] at h3
    refine (WXExec.whrT (by omega) (WXExec.seq h1 h2) h3).cast cap ?_ ?_
    · refine WState.eq rfl rfl ?_ rfl
      funext r
      simp only [σ2, σ1, WState.setv_val, Function.update_apply]
      by_cases rK : r = K
      · subst rK; simp [hKD]
      · by_cases rD : r = D
        · subst rD; simp [rK, Function.update_of_ne hKD.symm, Function.update_of_ne hKF.symm, Ne.symm hKF]; ring
        · simp [rK, rD]
    · simp only [σ1, WState.setv_val, Function.update_of_ne hKF.symm]
      nlinarith

theorem subL_spec (K A : Fin nr) (hKA : K ≠ A) :
    ∀ (j : ℕ) (σ : WState ns nr), σ.val K = j → j ≤ cap → σ.val A ≤ cap →
      WXExec cap (subL K A) σ ((σ.setv K 0).setv A (σ.val A - j)) (5 * j + 1) := by
  intro j
  induction j with
  | zero =>
    intro σ hv _ _
    have e : (σ.setv K 0).setv A (σ.val A - 0) = σ := by
      refine WState.eq rfl rfl ?_ rfl
      funext r; simp only [WState.setv_val, Function.update_apply]
      split_ifs with h1 h2 <;> subst_vars <;> simp_all
    rw [e]; exact WXExec.whrF hv
  | succ j ih =>
    intro σ hv hj hA
    have h1 := WXExec.dec cap K σ (by omega)
    rw [hv, show j + 1 - 1 = j by omega] at h1
    set σ1 := σ.setv K j with hσ1
    have h2 := WXExec.dec cap A σ1 (by simp [σ1, Function.update_of_ne hKA.symm]; omega)
    set σ2 := σ1.setv A (σ1.val A - 1) with hσ2
    have h3 := ih σ2 (by simp [σ2, σ1, Function.update_of_ne hKA]) (by omega)
      (by simp [σ2, σ1, Function.update_of_ne hKA.symm]; omega)
    refine (WXExec.whrT (by omega) (WXExec.seq h1 h2) h3).cast cap ?_ (by omega)
    refine WState.eq rfl rfl ?_ rfl
    funext r
    simp only [σ2, σ1, WState.setv_val, Function.update_apply]
    by_cases rK : r = K
    · subst rK; simp [hKA]
    · by_cases rA : r = A
      · subst rA; simp [rK, Function.update_of_ne hKA.symm]; omega
      · simp [rK, rA]

theorem frame_marks (l : List Bool) : RepairOrdinary.frame l = marks l ++ [false] := by
  induction l with
  | nil => rfl
  | cons b bs ih => simp [RepairOrdinary.frame, marks, ih]

theorem leadOnes_rep (L : ℕ) (w : List Bool) : leadOnes (List.replicate L true ++ false :: w) = L := by
  induction L with
  | zero => rfl
  | succ L ih => simp [List.replicate_succ, leadOnes, ih]

theorem leadOnes_natWord (n : ℕ) (rest : List Bool) : leadOnes (natWord n ++ rest) = natBitLength n := by
  unfold natWord WilliamsPublishedForm.framedNatBits
  rw [List.append_assoc, List.cons_append]
  exact leadOnes_rep _ _

/-- The cost of `bkA`. -/
def bkACost (L : ℕ) : ℕ := (L + 2) * (40 * 2 ^ L + 40) + 4 * (18 * L + 3) + 8 + (5 * (4 * L + 2) + 1) + 6

theorem bkA_spec (hRG : ∀ j, R j ≠ G) (σ : WState ns nr) (n0 : ℕ) (rest : List Bool)
    (hI : σ.st I = RepairOrdinary.frame (natWord n0 ++ rest)) (hh : σ.sh I = 0)
    (hG : σ.val G = natBitLength n0) (hz : ∀ j, σ.val (R j) = 0)
    (hcap : 2 ^ (natBitLength n0 + 2) + 8 * natBitLength n0 + 10 ≤ cap) :
    WXExec cap (bkA R I G) σ (σ.setv (R 2) n0) (bkACost (natBitLength n0)) := by
  set L := natBitLength n0 with hL
  have hR : ∀ {a b : Fin 12}, a ≠ b → R a ≠ R b := fun h => R.injective.ne h
  have hpow : 2 ^ (L + 2) = 2 ^ L * 4 := by rw [pow_add]; norm_num
  have hpow1 : 2 ^ (L + 1) = 2 ^ L * 2 := by rw [pow_add]; norm_num
  have hLp : L < 2 ^ L := Nat.lt_two_pow_self
  have hst : σ.st I = [] ++ NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.enc true (natWord n0) ++
      (marks rest ++ [false]) := by
    rw [hI, frame_marks]; simp [NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.enc, marks]
  have s1 := readNatM_spec (cap := cap) true I (R 0) (R 1) (R 2) (R 3) (R 4) (hR (by decide)) (hR (by decide))
    (hR (by decide)) (hR (by decide)) (hR (by decide)) (hR (by decide)) (hR (by decide)) (hR (by decide))
    (hR (by decide)) (hR (by decide)) n0 [] (marks rest ++ [false]) σ hst (by simp [hh]) (hz 0) (hz 1) (hz 3)
    (hz 4) (by rw [hz 2, ← hL]; omega)
  have hwl := NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.natWord_length n0
  rw [hz 2, zero_add, ← hL, List.length_nil, zero_add, hwl, ← hL] at s1
  have hstp : stp true = 2 := rfl
  rw [hstp] at s1
  set σ1 := (σ.seth I (2 * (2 * L + 1))).setv (R 2) n0 with hσ1
  have v1 : ∀ j, j ≠ 2 → σ1.val (R j) = 0 := fun j hj => by simp [σ1, hR hj, hz]
  have g1 : σ1.val G = L := by simp [σ1, Function.update_of_ne (hRG 2).symm, hG]
  have a1 := addR_spec cap (A := G) (B := R 5) (T := R 6) (hRG 5).symm (hRG 6).symm (hR (by decide)) σ1
    (v1 6 (by decide)) (by rw [v1 5 (by decide), g1]; omega)
  rw [v1 5 (by decide), g1, zero_add] at a1
  set σ2 := σ1.setv (R 5) L with hσ2
  have a2 := addR_spec cap (A := G) (B := R 5) (T := R 6) (hRG 5).symm (hRG 6).symm (hR (by decide)) σ2
    (by simp [σ2, hR (show (6 : Fin 12) ≠ 5 by decide), v1 6 (by decide)])
    (by simp [σ2, Function.update_of_ne (hRG 5).symm, g1]; omega)
  have e2a : σ2.val (R 5) = L := by simp [σ2]
  have e2b : σ2.val G = L := by simp [σ2, Function.update_of_ne (hRG 5).symm, g1]
  rw [e2a, e2b] at a2
  set σ3 := σ2.setv (R 5) (L + L) with hσ3
  have a3 := addR_spec cap (A := G) (B := R 5) (T := R 6) (hRG 5).symm (hRG 6).symm (hR (by decide)) σ3
    (by simp [σ3, σ2, hR (show (6 : Fin 12) ≠ 5 by decide), v1 6 (by decide)])
    (by simp [σ3, σ2, Function.update_of_ne (hRG 5).symm, g1]; omega)
  have e3a : σ3.val (R 5) = L + L := by simp [σ3]
  have e3b : σ3.val G = L := by simp [σ3, σ2, Function.update_of_ne (hRG 5).symm, g1]
  rw [e3a, e3b] at a3
  set σ4 := σ3.setv (R 5) (L + L + L) with hσ4
  have a4 := addR_spec cap (A := G) (B := R 5) (T := R 6) (hRG 5).symm (hRG 6).symm (hR (by decide)) σ4
    (by simp [σ4, σ3, σ2, hR (show (6 : Fin 12) ≠ 5 by decide), v1 6 (by decide)])
    (by simp [σ4, σ3, σ2, Function.update_of_ne (hRG 5).symm, g1]; omega)
  have e4a : σ4.val (R 5) = L + L + L := by simp [σ4]
  have e4b : σ4.val G = L := by simp [σ4, σ3, σ2, Function.update_of_ne (hRG 5).symm, g1]
  rw [e4a, e4b] at a4
  set σ5 := σ4.setv (R 5) (L + L + L + L) with hσ5
  have a5 := Cells.incN_spec cap (R 5) 2 σ5 (by simp [σ5]; omega)
  have e5 : σ5.val (R 5) = L + L + L + L := by simp [σ5]
  rw [e5] at a5
  set σ6 := σ5.setv (R 5) (L + L + L + L + 2) with hσ6
  have a6 := wrewind_spec (cap := cap) I (R 5) (L + L + L + L + 2) σ6 (by simp [σ6]) (by simp [σ6]; omega)
  have sh6 : σ6.sh I = 2 * (2 * L + 1) := by simp [σ6, σ5, σ4, σ3, σ2, σ1]
  rw [sh6] at a6
  refine (WXExec.seq (WXExec.wm s1) (WXExec.seq a1 (WXExec.seq a2 (WXExec.seq a3 (WXExec.seq a4 (WXExec.seq a5
    (WXExec.wm a6))))))).cast cap ?_ ?_
  · refine WState.eq ?_ rfl ?_ rfl
    · funext i
      simp only [σ6, σ5, σ4, σ3, σ2, σ1, WState.setv_sh, WState.seth_sh, Function.update_apply]
      split_ifs with h1
      · subst h1; rw [hh]; omega
      · rfl
    · funext r
      simp only [σ6, σ5, σ4, σ3, σ2, σ1, WState.seth_val, WState.setv_val, Function.update_apply]
      by_cases h5 : r = R 5
      · subst h5; simp [hR (show (5 : Fin 12) ≠ 2 by decide), hz]
      · simp [h5]
  · simp only [bkACost]; omega

end Block

end NearCubicGates.Close.CounterMachine.CellTablesProg
