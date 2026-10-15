import Proof.Gates.CounterAsm.Layout
import Proof.Gates.Recovery.HTParts3
import Proof.Gates.Recovery.HTLayout
import Proof.Gates.Recovery.TableSem

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicGates.Close.CounterAsm

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Recovery.HTParts
open NearCubicGates.Close.CheckedPCPP.ClauseFront (named)
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)

variable {ns : ℕ} (cap : ℕ)

/-! ## A counted constant emitter -/

theorem appendO_val_ne' (σ : WState ns 64) (o : Fin (ns + 1)) (OP r : Fin 64) (hr : r ≠ OP) (u : List Bool) :
    (appendO σ o OP u).val r = σ.val r := by simp [appendO, Function.update_apply, hr]

theorem repEmit_spec (dst : Fin (ns + 1)) {OP C : Fin 64} (hCO : C ≠ OP) (E : WM ns 64) (u : List Bool) (c : ℕ)
    (hE : ∀ τ : WState ns 64, τ.sh dst = (τ.st dst).length → τ.val OP + u.length ≤ cap →
      WExec cap E τ (appendO τ dst OP u) c) :
    ∀ (m : ℕ) (σ : WState ns 64), σ.val C = m → m ≤ cap → σ.sh dst = (σ.st dst).length →
      σ.val OP + m * u.length ≤ cap →
      WExec cap (Codec.repLoop C E) σ ((appendO σ dst OP (List.replicate m u).flatten).setv C 0) (m * (c + 4) + 1)
  | 0, σ, hC, _, _, _ => by
    simp only [List.replicate_zero, List.flatten_nil, appendO_nil, Nat.zero_mul, Nat.zero_add]
    rw [show σ.setv C 0 = σ by rw [← hC]; exact wsetv_same σ C]
    exact WExec.whrF hC
  | m + 1, σ, hC, hm, hd, hOc => by
    have e1 := WExec.dec (cap := cap) C σ (by omega)
    set σ1 := σ.setv C (σ.val C - 1) with hσ1
    have e2 := hE σ1 (by simpa [hσ1] using hd)
      (by simp [hσ1, Function.update_apply, Ne.symm hCO]; nlinarith)
    set σ2 := appendO σ1 dst OP u with hσ2
    have ih := repEmit_spec dst hCO E u c hE m σ2
      (by rw [hσ2, appendO_val_ne' _ _ _ _ hCO]; simp [hσ1, hC])
      (by omega) (by simp [hσ2, appendO, hσ1, hd])
      (by simp [hσ2, appendO, hσ1, Function.update_apply, Ne.symm hCO]; nlinarith)
    refine WExec.mono (WExec.cast cap (WExec.whrT (by rw [hC]; simp) (WExec.seq e1 e2) ih) ?_ le_rfl) (by ring_nf; omega)
    rw [hσ2, hσ1, Recovery.HTParts.appendO_setv _ _ _ _ hCO, Recovery.HTParts.appendO_setv _ _ _ _ hCO, wsetv_setv,
      appendO_append]
    simp [List.replicate_succ]

/-! ## Zero numbers and the ruler -/

theorem binary_zero : ∀ W : ℕ, binary W 0 = List.replicate W false
  | 0 => rfl
  | W + 1 => by simp [binary, binary_zero W, List.replicate_succ]

theorem frame_zero (W : ℕ) :
    RepairOrdinary.frame (binary W 0) = (List.replicate W [true, false]).flatten ++ [false] := by
  rw [binary_zero, Codec.frame_eq_marks]
  induction W with
  | zero => rfl
  | succ W ih => simp [List.replicate_succ, NearCubicWires.RepairOrdinary.Streaming.marks] at ih ⊢; exact ih

/-- A `W`-bit zero number on an empty stream. -/
def zeroNum (X : Fin (ns + 1)) : WMX ns 64 :=
  .seq (addR rW aC aT) (.seq (.wm (Codec.repLoop aC (emitPair X opZ false)))
    (.seq (.wm (emitC X opZ false)) (.wm (WM.rewind X opZ))))

theorem zeroNum_spec (X : Fin (ns + 1)) (W : ℕ) (σ : WState ns 64) (hX : σ.st X = []) (hXh : σ.sh X = 0)
    (hW : σ.val rW = W) (hC : σ.val aC = 0) (hT : σ.val aT = 0) (hO : σ.val opZ = 0) (hcap : 4 * W + 4 ≤ cap) :
    WXExec cap (zeroNum X) σ (σ.sets X (RepairOrdinary.frame (binary W 0))) (60 * W + 40) := by
  have e1 := addR_spec cap (A := rW) (B := aC) (T := aT) (by decide) (by decide) (by decide) σ hT (by omega)
  obtain ⟨s1, hs1, x1⟩ := named e1
  have e2 := repEmit_spec cap X (OP := opZ) (C := aC) (by decide) (emitPair X opZ false) [true, false] 15
    (fun τ hd hc => emitPair_spec cap X opZ false τ hd (by simpa using hc)) W s1
    (by rw [hs1]; simp [hC, hW]) (by omega) (by rw [hs1]; simp [hX, hXh])
    (by rw [hs1]; simp (config := { decide := true }) [Function.update_apply, hO]; omega)
  obtain ⟨s2, hs2, x2⟩ := named (WXExec.wm e2)
  have e3 := emitC_spec (cap := cap) X opZ false s2 (by rw [hs2]; simp [appendO, hs1, hX, hXh])
    (by rw [hs2]; simp (config := { decide := true }) [appendO, Function.update_apply, hs1, hO]; omega)
  obtain ⟨s3, hs3, x3⟩ := named (WXExec.wm e3)
  have hv3 : s3.val opZ = 2 * W + 1 := by
    rw [hs3, hs2]; simp (config := { decide := true }) [appendO, Function.update_apply, hs1, hO]; omega
  have e4 := wrewind_spec (cap := cap) X opZ (2 * W + 1) s3 hv3 (by omega)
  refine WXExec.mono (WXExec.cast cap (WXExec.seq x1 (WXExec.seq x2 (WXExec.seq x3 (WXExec.wm e4)))) ?_ le_rfl)
    (by omega)
  rw [hs3, hs2, hs1]
  apply WState.eq
  · funext y; by_cases hy : y = X
    · subst hy; simp [appendO, hXh, hX] <;> omega
    · simp [appendO, Function.update_apply, hy]
  · funext y; by_cases hy : y = X
    · subst hy; simp [appendO, hX, frame_zero]
    · simp [appendO, Function.update_apply, hy]
  · funext r
    by_cases r1 : r = opZ
    · subst r1; simp [hO]
    · by_cases r2 : r = aC
      · subst r2; simp (config := { decide := true }) [appendO, Function.update_apply, hC]
      · simp (config := { decide := true }) [appendO, Function.update_apply, r1, r2]
  · simp [appendO]

/-- The ruler `0 1^W` on an empty stream. -/
def rulerW (X : Fin (ns + 1)) : WMX ns 64 :=
  .seq (.wm (emitC X opZ false)) (.seq (addR rW aC aT) (.seq (.wm (Codec.repLoop aC (emitC X opZ true)))
    (.wm (WM.rewind X opZ))))

theorem ruler_spec (X : Fin (ns + 1)) (W : ℕ) (σ : WState ns 64) (hX : σ.st X = []) (hXh : σ.sh X = 0)
    (hW : σ.val rW = W) (hC : σ.val aC = 0) (hT : σ.val aT = 0) (hO : σ.val opZ = 0) (hcap : 4 * W + 4 ≤ cap) :
    WXExec cap (rulerW X) σ (σ.sets X (false :: List.replicate W true)) (60 * W + 40) := by
  have e1 := emitC_spec (cap := cap) X opZ false σ (by rw [hX, hXh]; rfl) (by omega)
  obtain ⟨s1, hs1, x1⟩ := named (WXExec.wm e1)
  have e2 := addR_spec cap (A := rW) (B := aC) (T := aT) (by decide) (by decide) (by decide) s1
    (by rw [hs1]; simp (config := { decide := true }) [Function.update_apply, hT])
    (by rw [hs1]; simp (config := { decide := true }) [Function.update_apply, hC, hW]; omega)
  obtain ⟨s2, hs2, x2⟩ := named e2
  have e3 := repEmit_spec cap X (OP := opZ) (C := aC) (by decide) (emitC X opZ true) [true] 7
    (fun τ hd hc => emitC_spec cap X opZ true τ hd (by simpa using hc)) W s2
    (by rw [hs2, hs1]; simp (config := { decide := true }) [Function.update_apply, hC, hW])
    (by omega) (by rw [hs2, hs1]; simp [hX, hXh])
    (by rw [hs2, hs1]; simp (config := { decide := true }) [Function.update_apply, hO]; omega)
  obtain ⟨s3, hs3, x3⟩ := named (WXExec.wm e3)
  have hw1 : s1.val rW = W := by rw [hs1]; simp (config := { decide := true }) [Function.update_apply, hW]
  have hv3 : s3.val opZ = W + 1 := by
    rw [hs3, hs2, hs1]; simp (config := { decide := true }) [appendO, Function.update_apply, hO]; omega
  have e4 := wrewind_spec (cap := cap) X opZ (W + 1) s3 hv3 (by omega)
  refine WXExec.mono (WXExec.cast cap (WXExec.seq x1 (WXExec.seq x2 (WXExec.seq x3 (WXExec.wm e4)))) ?_ le_rfl)
    (by omega)
  rw [hs3, hs2, hs1]
  apply WState.eq
  · funext y; by_cases hy : y = X
    · subst hy; simp [appendO, hXh, hX] <;> omega
    · simp [appendO, Function.update_apply, hy]
  · funext y; by_cases hy : y = X
    · subst hy; simp [appendO, hX]
    · simp [appendO, Function.update_apply, hy]
  · funext r
    by_cases r1 : r = opZ
    · subst r1; simp [hO]
    · by_cases r2 : r = aC
      · subst r2; simp (config := { decide := true }) [appendO, Function.update_apply, hC]
      · simp (config := { decide := true }) [appendO, Function.update_apply, r1, r2]
  · simp [appendO]

/-! ## `k` from `n` -/

theorem size_le_self (v : ℕ) : v.size ≤ v := Nat.size_le.mpr Nat.lt_two_pow_self

/-- `D := size (S − 1)` (`aX`, `aH`, `aB`, `aT` scratch at `0`). -/
def sizePhase (S D : Fin 64) : WMX ns 64 := .seq (addR S aX aT) (.seq (WMX.dec aX) (sizeW aX aH aB D))

theorem sizePhase_spec (S D : Fin 64) (hd : [S, D, aX, aH, aB, aT].Nodup) (v : ℕ) (σ : WState ns 64)
    (hS : σ.val S = v) (hD : σ.val D = 0) (hX : σ.val aX = 0) (hH : σ.val aH = 0) (hB : σ.val aB = 0)
    (hT : σ.val aT = 0) (hcap : 2 * v + 2 ≤ cap) :
    WXExec cap (sizePhase S D) σ (σ.setv D (v - 1).size) (v * (12 * v + 60) + 10) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true,
    not_false_eq_true] at hd
  obtain ⟨⟨sd, sx, sh, sb, st⟩, ⟨dx, dh, db, dt⟩, ⟨xh, xb, xt⟩, ⟨hb, ht⟩, bt⟩ := hd
  have hsz := size_le_self (v - 1)
  have e1 := addR_spec cap (A := S) (B := aX) (T := aT) sx st xt σ hT (by omega)
  rw [hX, hS, Nat.zero_add] at e1
  have e2 := WXExec.dec (cap := cap) aX (σ.setv aX v) (by simp; omega)
  simp only [WState.setv_val, Function.update_self, wsetv_setv] at e2
  have e3 := sizeW_exec (cap := cap) (X := aX) (H := aH) (B := aB) (C := D) (by simp [xh, xb, Ne.symm dx, hb,
    Ne.symm dh, Ne.symm db]) v (by omega) (v - 1) (σ.setv aX (v - 1)) (by omega) (by simp)
    (by simp [Function.update_apply, Ne.symm xh, hH]) (by simp [Function.update_apply, Ne.symm xb, hB])
    (by simp [Function.update_apply, dx, hD]; omega)
  refine WXExec.mono (WXExec.cast cap (WXExec.seq e1 (WXExec.seq e2 e3)) ?_ le_rfl) ?_
  · simp only [wsetv_setv, WState.setv_val, Function.update_apply, if_neg dx, hD, Nat.zero_add]
    rw [← hX, wsetv_same]
  · have : (v - 1).size * (12 * v + 30) ≤ v * (12 * v + 30) := Nat.mul_le_mul_right _ (by omega)
    nlinarith

/-- `λ = size (n − 1)`, `μ = size (λ − 1)`, `k = (3μ + c_T + 2)·λ`. -/
def kArith (cT : ℕ) : WMX ns 64 :=
  .seq (sizePhase rN aL) (.seq (sizePhase aL aM)
  (.seq (addR aM aA aT) (.seq (addR aM aA aT) (.seq (addR aM aA aT)
  (.seq (Recovery.HT.incN aA (cT + 2)) (mulR aA aA2 aL rK aT))))))

/-- `⌈lg n⌉` and `⌈lg ⌈lg n⌉⌉` as bit lengths. -/
def lamOf (n : ℕ) : ℕ := (n - 1).size
def muOf (n : ℕ) : ℕ := (lamOf n - 1).size
def kOf (cT n : ℕ) : ℕ := (3 * muOf n + cT + 2) * lamOf n

theorem lamOf_le (n : ℕ) : lamOf n ≤ n := by unfold lamOf; have := size_le_self (n - 1); omega
theorem muOf_le (n : ℕ) : muOf n ≤ lamOf n := by unfold muOf; have := size_le_self (lamOf n - 1); omega

theorem kcost (n cT la mu : ℕ) (hl : la ≤ n) (hm : mu ≤ la) :
    n * (12 * n + 60) + 10 + 1 + (la * (12 * la + 60) + 10 + 1 + (18 * mu + 3 + 1 + (18 * mu + 3 + 1 +
      (18 * mu + 3 + 1 + (4 * (cT + 2) + 1 + ((3 * mu + cT + 2) * (18 * la + 3 + 8) + 7 * (3 * mu + cT + 2) +
        3)))))) ≤ 200 * (n + cT + 10) ^ 2 := by
  have h1 : la * (12 * la + 60) ≤ n * (12 * n + 60) := Nat.mul_le_mul hl (by omega)
  have h2 : (3 * mu + cT + 2) * (18 * la + 3 + 8) ≤ (3 * n + cT + 2) * (18 * n + 11) :=
    Nat.mul_le_mul (by omega) (by omega)
  nlinarith

theorem kArith_spec (cT n : ℕ) (σ : WState ns 64) (hN : σ.val rN = n)
    (hX : σ.val aX = 0) (hH : σ.val aH = 0) (hB : σ.val aB = 0) (hL : σ.val aL = 0) (hM : σ.val aM = 0)
    (hA : σ.val aA = 0) (hA2 : σ.val aA2 = 0) (hT : σ.val aT = 0) (hK : σ.val rK = 0)
    (hcap : 100 * (n + cT + 10) ^ 2 ≤ cap) :
    WXExec cap (kArith cT) σ ((((σ.setv aL (lamOf n)).setv aM (muOf n)).setv aA (3 * muOf n + cT + 2)).setv rK
      (kOf cT n)) (200 * (n + cT + 10) ^ 2) := by
  have hl := lamOf_le n
  have hm := muOf_le n
  have hsq : n + cT + 10 ≤ (n + cT + 10) ^ 2 := Nat.le_self_pow (by norm_num) _
  have e1 := sizePhase_spec cap rN aL (by decide) n σ hN hL hX hH hB hT (by nlinarith)
  obtain ⟨s1, hs1⟩ : ∃ s, s = σ.setv aL (lamOf n) := ⟨_, rfl⟩
  rw [show σ.setv aL (n - 1).size = s1 from hs1.symm] at e1
  have e2 := sizePhase_spec cap aL aM (by decide) (lamOf n) s1 (by rw [hs1]; simp)
    (by rw [hs1]; simp (config := { decide := true }) [Function.update_apply, hM])
    (by rw [hs1]; simp (config := { decide := true }) [Function.update_apply, hX])
    (by rw [hs1]; simp (config := { decide := true }) [Function.update_apply, hH])
    (by rw [hs1]; simp (config := { decide := true }) [Function.update_apply, hB])
    (by rw [hs1]; simp (config := { decide := true }) [Function.update_apply, hT]) (by nlinarith)
  obtain ⟨s2, hs2⟩ : ∃ s, s = s1.setv aM (muOf n) := ⟨_, rfl⟩
  rw [show s1.setv aM (lamOf n - 1).size = s2 from hs2.symm] at e2
  have v2T : s2.val aT = 0 := by rw [hs2, hs1]; simp (config := { decide := true }) [Function.update_apply, hT]
  have v2M : s2.val aM = muOf n := by rw [hs2]; simp
  have v2A : s2.val aA = 0 := by rw [hs2, hs1]; simp (config := { decide := true }) [Function.update_apply, hA]
  have v2L : s2.val aL = lamOf n := by rw [hs2, hs1]; simp (config := { decide := true }) [Function.update_apply]
  have v2K : s2.val rK = 0 := by rw [hs2, hs1]; simp (config := { decide := true }) [Function.update_apply, hK]
  have v2A2 : s2.val aA2 = 0 := by rw [hs2, hs1]; simp (config := { decide := true }) [Function.update_apply, hA2]
  have step : ∀ x : ℕ, x + (muOf n) ≤ cap → WXExec cap (addR aM aA aT) (s2.setv aA x) (s2.setv aA (x + (muOf n))) (18 * (muOf n) + 3) := by
    intro x hx
    have h := addR_spec cap (A := aM) (B := aA) (T := aT) (by decide) (by decide) (by decide) (s2.setv aA x)
      (by rw [WState.setv_val, Function.update_of_ne (by decide)]; exact v2T)
      (by rw [WState.setv_val, Function.update_self, Function.update_of_ne (by decide), v2M]; omega)
    rwa [WState.setv_val, Function.update_self, Function.update_of_ne (by decide), v2M, wsetv_setv] at h
  have e3 := step 0 (by omega)
  rw [show s2.setv aA 0 = s2 by rw [← v2A]; exact wsetv_same s2 aA, Nat.zero_add] at e3
  have e4 := step (muOf n) (by omega)
  have e5 := step ((muOf n) + (muOf n)) (by omega)
  have e6 := Recovery.HT.incN_exec (cap := cap) aA (cT + 2) (s2.setv aA ((muOf n) + (muOf n) + (muOf n)))
    (by rw [WState.setv_val, Function.update_self]; omega)
  rw [WState.setv_val, Function.update_self, wsetv_setv,
    show (muOf n) + (muOf n) + (muOf n) + (cT + 2) = 3 * (muOf n) + cT + 2 by ring] at e6
  obtain ⟨s6, hs6⟩ : ∃ s, s = s2.setv aA (3 * (muOf n) + cT + 2) := ⟨_, rfl⟩
  rw [show s2.setv aA (3 * (muOf n) + cT + 2) = s6 from hs6.symm] at e6
  have hAL : (3 * (muOf n) + cT + 2) * lamOf n ≤ 3 * (n + cT + 10) ^ 2 := by
    rw [sq, ← Nat.mul_assoc]; exact Nat.mul_le_mul (by omega) (by omega)
  have v6A : s6.val aA = 3 * (muOf n) + cT + 2 := by rw [hs6]; simp
  have v6L : s6.val aL = lamOf n := by rw [hs6, WState.setv_val, Function.update_of_ne (by decide)]; exact v2L
  have v6K : s6.val rK = 0 := by rw [hs6, WState.setv_val, Function.update_of_ne (by decide)]; exact v2K
  have v6A2 : s6.val aA2 = 0 := by rw [hs6, WState.setv_val, Function.update_of_ne (by decide)]; exact v2A2
  have v6T : s6.val aT = 0 := by rw [hs6, WState.setv_val, Function.update_of_ne (by decide)]; exact v2T
  have e7 := mulR_spec cap (A := aA) (A2 := aA2) (B := aL) (C := rK) (T := aT) (by decide) s6 v6A2 v6T
    (by rw [v6K, v6A, v6L]; omega) (by rw [v6A]; nlinarith)
  rw [v6K, v6A, v6L, Nat.zero_add] at e7
  have hc7 : (3 * (muOf n) + cT + 2) * (18 * lamOf n + 3 + 8) + 7 * (3 * (muOf n) + cT + 2) + 3 ≤ 60 * (n + cT + 10) ^ 2 := by
    have : (3 * (muOf n) + cT + 2) * (18 * lamOf n + 3 + 8) ≤ (3 * n + cT + 2) * (18 * n + 11) :=
      Nat.mul_le_mul (by omega) (by omega)
    nlinarith
  have hc1 : n * (12 * n + 60) + 10 ≤ 20 * (n + cT + 10) ^ 2 := by nlinarith
  have hc2 : lamOf n * (12 * lamOf n + 60) + 10 ≤ 20 * (n + cT + 10) ^ 2 := by
    have h3 : lamOf n * (12 * lamOf n + 60) ≤ n * (12 * n + 60) := Nat.mul_le_mul hl (by omega)
    omega
  have hfin : s6.setv rK ((3 * (muOf n) + cT + 2) * lamOf n) = (((σ.setv aL (lamOf n)).setv aM (muOf n)).setv aA
      (3 * muOf n + cT + 2)).setv rK (kOf cT n) := by rw [hs6, hs2, hs1, kOf]
  rw [hfin] at e7
  have c67 := WXExec.seq e6 e7
  have c57 := WXExec.seq e5 c67
  have c47 := WXExec.seq e4 c57
  have c37 := WXExec.seq e3 c47
  have c27 := WXExec.seq e2 c37
  have c17 := WXExec.seq e1 c27
  exact WXExec.mono c17 (kcost n cT (lamOf n) (muOf n) hl hm)

end NearCubicGates.Close.CounterAsm
