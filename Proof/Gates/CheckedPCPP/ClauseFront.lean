import Proof.Gates.CheckedPCPP.LitDecode
import Proof.Gates.CheckedPCPP.ClauseAccess

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicGates.Close.CheckedPCPP.ClauseFront

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicWires.SourceInterfaces NearCubicGates.PublishedSources.PCPP
open NearCubicGates.Close.CheckedPCPP.LitDecode

variable {ns nr : ℕ} {cap : ℕ}

/-! ## Doubling and remainders in registers -/

/-- `M := M · 2^K`, `K := 0` (`Q`, `T` scratch). -/
def dblW (M K Q T : Fin nr) : WMX ns nr := .whr K (.seq (WMX.dec K) (.seq (addR M Q T) (.wm (WM.move Q M))))

theorem dblW_exec {M K Q T : Fin nr} (hR : [M, K, Q, T].Nodup) (Mx : ℕ) (hMx : 2 * Mx ≤ cap) :
    ∀ (k : ℕ) (σ : WState ns nr), σ.val K = k → k ≤ cap → σ.val Q = 0 → σ.val T = 0 → σ.val M * 2 ^ k ≤ Mx →
      WXExec cap (dblW M K Q T) σ ((σ.setv K 0).setv M (σ.val M * 2 ^ k)) (k * (25 * Mx + 10) + 1)
  | 0, σ, hK, _, _, _, _ => by
    rw [show (σ.setv K 0).setv M (σ.val M * 2 ^ 0) = σ by
      rw [pow_zero, Nat.mul_one, ← hK, wsetv_same, wsetv_same]]
    exact WXExec.mono (WXExec.whrF hK) (by simp)
  | k + 1, σ, hK, hKc, hQ, hT, hM => by
    have hR' := hR
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true,
      not_false_eq_true] at hR'
    obtain ⟨⟨mk, mq, mt⟩, ⟨kq, kt⟩, qt⟩ := hR'
    have km := Ne.symm mk; have qm := Ne.symm mq; have tm := Ne.symm mt
    have qk := Ne.symm kq; have tk := Ne.symm kt; have tq := Ne.symm qt
    have hp : σ.val M * 2 ^ k * 2 ≤ Mx := by rw [pow_succ] at hM; linarith
    have hMle : σ.val M ≤ σ.val M * 2 ^ k := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos k)
    have e1 := WXExec.dec (cap := cap) K σ (by omega)
    set σ1 := σ.setv K (σ.val K - 1) with hσ1
    have e2 := addR_spec cap mq mt qt σ1 (by simp [hσ1, Function.update_apply, tk, hT])
      (by simp [hσ1, Function.update_apply, qk, mk, hQ]; omega)
    set σ2 := σ1.setv Q (σ1.val Q + σ1.val M) with hσ2
    have hM1 : σ1.val M = σ.val M := by simp [hσ1, Function.update_apply, mk]
    have hQ1 : σ1.val Q = 0 := by simp [hσ1, Function.update_apply, Ne.symm kq, hQ]
    have e3 := wmove_spec (cap := cap) Q M (Ne.symm mq) (σ.val M) σ2 (by simp [hσ2, hM1, hQ1])
      (by simp [hσ2, hM1, hQ1]; omega) (by simp [hσ2, hM1, hQ1, Function.update_apply, mq]; omega)
    set σ3 := (σ2.setv Q 0).setv M (σ2.val M + σ2.val Q) with hσ3
    have ih := dblW_exec hR Mx hMx k σ3 (by simp [hσ3, hσ2, hσ1, Function.update_apply, km, kq, hK])
      (by omega) (by simp [hσ3, Function.update_apply, qm]) (by simp [hσ3, hσ2, hσ1, Function.update_apply,
        tm, tq, tk, hT])
      (by simp [hσ3, hσ2, hσ1, Function.update_apply, mq, qm, mk, qk, hQ]; nlinarith)
    refine WXExec.mono (WXExec.cast cap (WXExec.whrT (by omega) (WXExec.seq e1 (WXExec.seq e2 (WXExec.wm e3))) ih) ?_
      le_rfl) (by simp [hσ2, hM1, hQ1]; nlinarith)
    apply WState.eq <;> try rfl
    funext q
    simp only [hσ3, hσ2, hσ1, WState.setv_val, Function.update_apply]
    by_cases q1 : q = M
    · rw [q1]; simp [mq, mk, qm, qk, km, hQ, pow_succ]; ring
    · by_cases q2 : q = K
      · rw [q2]; simp [km]
      · by_cases q3 : q = Q
        · rw [q3]; simp [qm, qk, hQ]
        · simp [q1, q2, q3]

theorem mod_succ' (i m : ℕ) (hm : 0 < m) : (i + 1) % m = if i % m + 1 = m then 0 else i % m + 1 := by
  have h := Nat.mod_lt i hm
  rw [Nat.add_mod]
  rcases Nat.lt_or_ge 1 m with h1 | h1
  · rw [Nat.mod_eq_of_lt h1]
    split_ifs with he
    · rw [he, Nat.mod_self]
    · exact Nat.mod_eq_of_lt (by omega)
  · have : m = 1 := by omega
    subst this; simp [Nat.mod_one]

theorem setv3_congr {σ τ : WState ns nr} (K C D : Fin nr) (x y z : ℕ) (hsh : τ.sh = σ.sh) (hst : τ.st = σ.st)
    (hc : τ.cell = σ.cell) (hv : ∀ q, q ≠ K → q ≠ C → q ≠ D → τ.val q = σ.val q) :
    ((τ.setv K x).setv C y).setv D z = ((σ.setv K x).setv C y).setv D z := by
  apply WState.eq
  · simpa using hsh
  · simpa using hst
  · funext q
    by_cases q1 : q = D
    · simp [Function.update_apply, q1]
    · by_cases q2 : q = C
      · simp [Function.update_apply, q1, q2]
      · by_cases q3 : q = K
        · simp [Function.update_apply, q1, q2, q3]
        · simp [Function.update_apply, q1, q2, q3, hv q q3 q2 q1]
  · simpa using hc

/-- The remainder loop: per step `C += 1`, `D -= 1`, and at `D = 0` reset `C := 0`, `D := M`. -/
def modLoop (M C D K T : Fin nr) : WMX ns nr :=
  .whr K (.seq (WMX.dec K) (.seq (WMX.inc C) (.seq (WMX.dec D) (.ifr D WMX.skip
    (.seq (.wm (WM.clear C)) (addR M D T))))))

theorem modLoop_exec {M C D K T : Fin nr} (hR : [M, C, D, K, T].Nodup) (m : ℕ) (hm : 0 < m) (hmc : 2 * m + 2 ≤ cap) :
    ∀ (j i : ℕ) (σ : WState ns nr), σ.val K = j → j ≤ cap → σ.val M = m → σ.val T = 0 → σ.val C = i % m →
      σ.val D = m - i % m →
      WXExec cap (modLoop M C D K T) σ (((σ.setv K 0).setv C ((i + j) % m)).setv D (m - (i + j) % m))
        (j * (25 * m + 20) + 1)
  | 0, i, σ, hK, _, _, _, hC, hD => by
    rw [show ((σ.setv K 0).setv C ((i + 0) % m)).setv D (m - (i + 0) % m) = σ by
      rw [Nat.add_zero, ← hD, ← hC, ← hK, wsetv_same, wsetv_same, wsetv_same]]
    exact WXExec.mono (WXExec.whrF hK) (by simp)
  | j + 1, i, σ, hK, hKc, hM, hT, hC, hD => by
    have hR' := hR
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true,
      not_false_eq_true] at hR'
    obtain ⟨⟨mc, md, mk, mt⟩, ⟨cd, ck, ct⟩, ⟨dk, dt⟩, kt⟩ := hR'
    have cm := Ne.symm mc; have dm := Ne.symm md; have km := Ne.symm mk; have tm := Ne.symm mt
    have dc := Ne.symm cd; have kc := Ne.symm ck; have tc := Ne.symm ct; have kd := Ne.symm dk
    have td := Ne.symm dt; have tk := Ne.symm kt
    have hlt := Nat.mod_lt i hm
    have e1 := WXExec.dec (cap := cap) K σ (by omega)
    set σ1 := σ.setv K (σ.val K - 1) with hσ1
    have e2 := WXExec.inc (cap := cap) C σ1 (by simp [hσ1, Function.update_apply, mc, md, mk, mt, cd, ck, ct, dk, dt, kt, cm, dm, km, tm, dc, kc, tc, kd, td, tk, Ne.symm ck, hC]; omega)
    set σ2 := σ1.setv C (σ1.val C + 1) with hσ2
    have e3 := WXExec.dec (cap := cap) D σ2 (by simp [hσ2, hσ1, Function.update_apply, mc, md, mk, mt, cd, ck, ct, dk, dt, kt, cm, dm, km, tm, dc, kc, tc, kd, td, tk, Ne.symm dk, Ne.symm cd, hD]; omega)
    set σ3 := σ2.setv D (σ2.val D - 1) with hσ3
    have hC3 : σ3.val C = i % m + 1 := by simp [hσ3, hσ2, hσ1, Function.update_apply, mc, md, mk, mt, cd, ck, ct, dk, dt, kt, cm, dm, km, tm, dc, kc, tc, kd, td, tk, cd, Ne.symm ck, hC]
    have hD3 : σ3.val D = m - i % m - 1 := by simp [hσ3, hσ2, hσ1, Function.update_apply, mc, md, mk, mt, cd, ck, ct, dk, dt, kt, cm, dm, km, tm, dc, kc, tc, kd, td, tk, Ne.symm cd, Ne.symm dk, hD]
    have hK3 : σ3.val K = j := by simp [hσ3, hσ2, hσ1, Function.update_apply, mc, md, mk, mt, cd, ck, ct, dk, dt, kt, cm, dm, km, tm, dc, kc, tc, kd, td, tk, ck, dk, hK]
    have hM3 : σ3.val M = m := by simp [hσ3, hσ2, hσ1, Function.update_apply, mc, md, mk, mt, cd, ck, ct, dk, dt, kt, cm, dm, km, tm, dc, kc, tc, kd, td, tk, mc, md, mk, hM]
    have hT3 : σ3.val T = 0 := by simp [hσ3, hσ2, hσ1, Function.update_apply, mc, md, mk, mt, cd, ck, ct, dk, dt, kt, cm, dm, km, tm, dc, kc, tc, kd, td, tk, Ne.symm ct, Ne.symm dt, Ne.symm kt, hT]
    have hs := mod_succ' i m hm
    by_cases hz : i % m + 1 = m
    · -- reset
      have e4 := wclear_spec (cap := cap) C (i % m + 1) σ3 hC3 (by omega)
      set σ4 := σ3.setv C 0 with hσ4
      have e5 := addR_spec cap md mt dt σ4 (by simp [hσ4, Function.update_apply, mc, md, mk, mt, cd, ck, ct, dk, dt, kt, cm, dm, km, tm, dc, kc, tc, kd, td, tk, Ne.symm ct, hT3])
        (by simp [hσ4, Function.update_apply, mc, md, mk, mt, cd, ck, ct, dk, dt, kt, cm, dm, km, tm, dc, kc, tc, kd, td, tk, Ne.symm cd, cd, Ne.symm mc, mc, hD3, hM3]; omega)
      set σ5 := σ4.setv D (σ4.val D + σ4.val M) with hσ5
      have hif : WXExec cap (.ifr D WMX.skip (.seq (.wm (WM.clear C)) (addR M D T))) σ3 σ5
          (3 * (i % m + 1) + 1 + 1 + (18 * σ4.val M + 3) + 1) :=
        WXExec.ifrF (by rw [hD3]; omega) (WXExec.seq (WXExec.wm e4) e5)
      have ih := modLoop_exec hR m hm hmc j (i + 1) σ5
        (by simp [hσ5, hσ4, Function.update_apply, mc, md, mk, mt, cd, ck, ct, dk, dt, kt, cm, dm, km, tm, dc, kc, tc, kd, td, tk, Ne.symm dk, Ne.symm ck, hK3]) (by omega)
        (by simp [hσ5, hσ4, Function.update_apply, mc, md, mk, mt, cd, ck, ct, dk, dt, kt, cm, dm, km, tm, dc, kc, tc, kd, td, tk, md, mc, hM3])
        (by simp [hσ5, hσ4, Function.update_apply, mc, md, mk, mt, cd, ck, ct, dk, dt, kt, cm, dm, km, tm, dc, kc, tc, kd, td, tk, Ne.symm dt, Ne.symm ct, hT3])
        (by rw [hs, if_pos hz]; simp [hσ5, hσ4, Function.update_apply, mc, md, mk, mt, cd, ck, ct, dk, dt, kt, cm, dm, km, tm, dc, kc, tc, kd, td, tk])
        (by rw [hs, if_pos hz]; simp [hσ5, hσ4, Function.update_apply, mc, md, mk, mt, cd, ck, ct, dk, dt, kt, cm, dm, km, tm, dc, kc, tc, kd, td, tk, hD3, hM3]; omega)
      have hM4 : σ4.val M = m := by rw [hσ4]; simp only [WState.setv_val]; rw [Function.update_of_ne mc]; exact hM3
      refine WXExec.mono (WXExec.cast cap (WXExec.whrT (by omega) (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 hif)))
        ih) ?_ le_rfl) (by rw [hM4]; nlinarith)
      rw [show i + 1 + j = i + (j + 1) by ring]
      exact setv3_congr K C D _ _ _ rfl rfl rfl (fun q h1 h2 h3 => by
        simp [hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_apply, h1, h2, h3])
    · -- no reset
      have hif : WXExec cap (.ifr D WMX.skip (.seq (.wm (WM.clear C)) (addR M D T))) σ3 σ3 1 :=
        WXExec.mono (WXExec.ifrT (by rw [hD3]; omega) (WXExec.skip cap σ3)) le_rfl
      have ih := modLoop_exec hR m hm hmc j (i + 1) σ3 hK3 (by omega) hM3 hT3 (by rw [hC3, hs, if_neg hz])
        (by rw [hD3, hs, if_neg hz]; omega)
      refine WXExec.mono (WXExec.cast cap (WXExec.whrT (by omega) (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 hif)))
        ih) ?_ le_rfl) (by nlinarith)
      rw [show i + 1 + j = i + (j + 1) by ring]
      exact setv3_congr K C D _ _ _ rfl rfl rfl (fun q h1 h2 h3 => by
        simp [hσ3, hσ2, hσ1, Function.update_apply, h1, h2, h3])

/-- `C := a mod m`, `D := m − a mod m` (`A = a` kept, `K` and `T` scratch). -/
def modW (A M C D K T : Fin nr) : WMX ns nr := .seq (addR M D T) (.seq (addR A K T) (modLoop M C D K T))

theorem modW_exec {A M C D K T : Fin nr} (hR : [A, M, C, D, K, T].Nodup) (a m : ℕ) (hm : 0 < m)
    (hmc : 2 * m + 2 ≤ cap) (hac : a ≤ cap) (σ : WState ns nr) (hA : σ.val A = a) (hM : σ.val M = m)
    (hC : σ.val C = 0) (hD : σ.val D = 0) (hK : σ.val K = 0) (hT : σ.val T = 0) :
    WXExec cap (modW A M C D K T) σ ((σ.setv C (a % m)).setv D (m - a % m))
      (18 * m + 3 + 1 + (18 * a + 3 + 1 + (a * (25 * m + 20) + 1))) := by
  have hR' := hR
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true,
    not_false_eq_true] at hR'
  obtain ⟨⟨am, ac, ad, ak, aT⟩, ⟨mc, md, mk, mt⟩, ⟨cd, ck, ct⟩, ⟨dk, dt⟩, kt⟩ := hR'
  have ma := Ne.symm am; have ca := Ne.symm ac; have da := Ne.symm ad; have ka := Ne.symm ak
  have ta := Ne.symm aT
  have cm := Ne.symm mc; have dm := Ne.symm md; have km := Ne.symm mk; have tm := Ne.symm mt
  have dc := Ne.symm cd; have kc := Ne.symm ck; have tc := Ne.symm ct; have kd := Ne.symm dk
  have td := Ne.symm dt; have tk := Ne.symm kt
  have e1 := addR_spec cap md mt dt σ hT (by rw [hD, hM]; omega)
  rw [hD, hM, Nat.zero_add] at e1
  set σ1 := σ.setv D m with hσ1
  have e2 := addR_spec cap ak aT kt σ1 (by simp [hσ1, Function.update_apply, mc, md, mk, mt, cd, ck, ct, dk, dt, kt, cm, dm, km, tm, dc, kc, tc, kd, td, tk, am, ac, ad, ak, aT, ma, ca, da, ka, ta, Ne.symm dt, hT])
    (by simp [hσ1, Function.update_apply, mc, md, mk, mt, cd, ck, ct, dk, dt, kt, cm, dm, km, tm, dc, kc, tc, kd, td, tk, am, ac, ad, ak, aT, ma, ca, da, ka, ta, Ne.symm dk, Ne.symm ad, hK, hA]; omega)
  set σ2 := σ1.setv K (σ1.val K + σ1.val A) with hσ2
  have hA1 : σ1.val A = a := by simp [hσ1, Function.update_apply, mc, md, mk, mt, cd, ck, ct, dk, dt, kt, cm, dm, km, tm, dc, kc, tc, kd, td, tk, am, ac, ad, ak, aT, ma, ca, da, ka, ta, ad, hA]
  have e3 := modLoop_exec (M := M) (C := C) (D := D) (K := K) (T := T) (by simp [mc, md, mk, mt, cd, ck, ct, dk, dt, kt])
    m hm hmc a 0 σ2 (by simp [hσ2, hσ1, hA1, Function.update_apply, mc, md, mk, mt, cd, ck, ct, dk, dt, kt, cm, dm, km, tm, dc, kc, tc, kd, td, tk, am, ac, ad, ak, aT, ma, ca, da, ka, ta, Ne.symm dk, hK, hA])
    hac (by simp [hσ2, hσ1, Function.update_apply, mc, md, mk, mt, cd, ck, ct, dk, dt, kt, cm, dm, km, tm, dc, kc, tc, kd, td, tk, am, ac, ad, ak, aT, ma, ca, da, ka, ta, mk, md, hM]) (by simp [hσ2, hσ1, Function.update_apply, mc, md, mk, mt, cd, ck, ct, dk, dt, kt, cm, dm, km, tm, dc, kc, tc, kd, td, tk, am, ac, ad, ak, aT, ma, ca, da, ka, ta,
      Ne.symm kt, Ne.symm dt, hT]) (by simp [hσ2, hσ1, Function.update_apply, mc, md, mk, mt, cd, ck, ct, dk, dt, kt, cm, dm, km, tm, dc, kc, tc, kd, td, tk, am, ac, ad, ak, aT, ma, ca, da, ka, ta, ck, cd, hC])
    (by simp [hσ2, hσ1, Function.update_apply, mc, md, mk, mt, cd, ck, ct, dk, dt, kt, cm, dm, km, tm, dc, kc, tc, kd, td, tk, am, ac, ad, ak, aT, ma, ca, da, ka, ta, Ne.symm dk])
  rw [hA1] at e2
  refine WXExec.cast cap (WXExec.seq e1 (WXExec.seq e2 e3)) ?_ (by rfl)
  rw [Nat.zero_add]
  apply WState.eq <;> try rfl
  funext q
  by_cases q1 : q = D
  · simp [Function.update_apply, q1]
  · by_cases q2 : q = C
    · simp [Function.update_apply, q1, q2]
    · by_cases q3 : q = K
      · simp [Function.update_apply, q1, q2, q3, kd, kc, hK]
      · simp [hσ2, hσ1, Function.update_apply, q1, q2, q3]

/-! ## Skipping framed fields (counted) -/

/-- Skip the marked pairs of a frame (`SC` counts the cells). -/
def skipLoop (J : Fin (ns + 1)) (SC : Fin nr) : WM ns nr := .whs J (.seq (WM.fwdC J SC) (WM.fwdC J SC))

theorem skipLoop_exec (J : Fin (ns + 1)) (SC : Fin nr) (rest : List Bool) :
    ∀ (w pre : List Bool) (σ : WState ns nr), RdEq (σ.st J) (pre ++ frame w ++ rest) → σ.sh J = pre.length →
      σ.val SC + 2 * w.length ≤ cap →
      WExec cap (skipLoop J SC) σ ((σ.seth J (pre.length + 2 * w.length)).setv SC (σ.val SC + 2 * w.length))
        (13 * w.length + 1)
  | [], pre, σ, hst, hsh, _ => by
    have hw : wbit σ J = false := by unfold wbit; rw [hst, hsh]; simp [frame, rtb_off0]; rfl
    rw [show (σ.seth J (pre.length + 2 * ([] : List Bool).length)).setv SC (σ.val SC + 2 * ([] : List Bool).length)
      = σ by simp only [List.length_nil, Nat.mul_zero, Nat.add_zero]; rw [← hsh, wseth_same, wsetv_same]]
    exact WExec.mono (WExec.whsF hw) (by simp)
  | b :: w, pre, σ, hst, hsh, hSC => by
    have hw : wbit σ J = true := by unfold wbit; rw [hst, hsh]; simp [frame, rtb_off0]; rfl
    have hl : (b :: w).length = w.length + 1 := rfl
    have e1 := wfwdC_spec cap J SC σ (by rw [hl] at hSC; omega)
    set σ1 := (σ.seth J (σ.sh J + 1)).setv SC (σ.val SC + 1) with hσ1
    have e2 := wfwdC_spec cap J SC σ1 (by simp [hσ1]; rw [hl] at hSC; omega)
    set σ2 := (σ1.seth J (σ1.sh J + 1)).setv SC (σ1.val SC + 1) with hσ2
    have ih := skipLoop_exec J SC rest w (pre ++ [true, b]) σ2
      (by simp only [hσ2, hσ1, WState.setv_st, WState.seth_st]; rw [frame_cons] at hst; simpa using hst)
      (by simp [hσ2, hσ1, hsh]) (by simp [hσ2, hσ1]; rw [hl] at hSC; omega)
    refine WExec.mono (WExec.cast cap (WExec.whsT hw (WExec.seq e1 e2) ih) ?_ le_rfl) (by rw [hl]; omega)
    apply WState.eq
    · funext j; by_cases hj : j = J
      · simp [hj, hσ2, hσ1, hsh]; ring
      · simp [hσ2, hσ1, Function.update_apply, hj]
    · rfl
    · funext q; by_cases hq : q = SC
      · simp [hq, hσ2, hσ1]; ring
      · simp [hσ2, hσ1, Function.update_apply, hq]
    · rfl

/-- Skip one frame. -/
def skipF (J : Fin (ns + 1)) (SC : Fin nr) : WM ns nr := .seq (skipLoop J SC) (WM.fwdC J SC)

theorem skipF_exec (J : Fin (ns + 1)) (SC : Fin nr) (w pre rest : List Bool) (σ : WState ns nr)
    (hst : RdEq (σ.st J) (pre ++ frame w ++ rest)) (hsh : σ.sh J = pre.length)
    (hSC : σ.val SC + (frame w).length ≤ cap) :
    WExec cap (skipF J SC) σ ((σ.seth J (pre.length + (frame w).length)).setv SC (σ.val SC + (frame w).length))
      (13 * w.length + 7) := by
  have hfl := frame_length' w
  have e1 := skipLoop_exec (cap := cap) J SC rest w pre σ hst hsh (by omega)
  set σ1 := (σ.seth J (pre.length + 2 * w.length)).setv SC (σ.val SC + 2 * w.length) with hσ1
  have e2 := wfwdC_spec cap J SC σ1 (by simp [hσ1]; omega)
  refine WExec.cast cap (WExec.seq e1 e2) ?_ (by omega)
  apply WState.eq
  · funext j; by_cases hj : j = J
    · simp [hj, hσ1, hfl]; ring
    · simp [hσ1, Function.update_apply, hj]
  · rfl
  · funext q; by_cases hq : q = SC
    · simp [hq, hσ1, hfl]; ring
    · simp [hσ1, Function.update_apply, hq]
  · rfl

open ClauseAccess (tri) in
/-- Skip `C` clauses (three frames each), `C := 0`. -/
def skipT (J : Fin (ns + 1)) (SC C : Fin nr) : WM ns nr :=
  .whr C (.seq (.dec C) (.seq (skipF J SC) (.seq (skipF J SC) (skipF J SC))))

open ClauseAccess (tri) in
theorem skipT_exec (J : Fin (ns + 1)) {SC C : Fin nr} (hSCC : SC ≠ C) (rest : List Bool) :
    ∀ (ts : List (List Bool × List Bool × List Bool)) (pre : List Bool) (σ : WState ns nr),
      RdEq (σ.st J) (pre ++ (ts.map tri).flatten ++ rest) → σ.sh J = pre.length → σ.val C = ts.length →
      ts.length ≤ cap → σ.val SC + ((ts.map tri).flatten).length ≤ cap →
      WExec cap (skipT J SC C) σ (((σ.seth J (pre.length + ((ts.map tri).flatten).length)).setv SC
        (σ.val SC + ((ts.map tri).flatten).length)).setv C 0) (13 * ((ts.map tri).flatten).length + 40 * ts.length + 1)
  | [], pre, σ, _, hsh, hC, _, _ => by
    rw [show ((σ.seth J (pre.length + (([] : List (List Bool × List Bool × List Bool)).map tri).flatten.length)).setv
        SC (σ.val SC + (([] : List (List Bool × List Bool × List Bool)).map tri).flatten.length)).setv C 0 = σ by
      simp only [List.map_nil, List.flatten_nil, List.length_nil, Nat.add_zero]
      rw [← hsh, wseth_same, wsetv_same]
      have hC0 : σ.val C = 0 := by simpa using hC
      rw [← hC0, wsetv_same]]
    exact WExec.mono (WExec.whrF (by simpa using hC)) (by simp)
  | ⟨w0, w1, w2⟩ :: ts, pre, σ, hst, hsh, hC, hCc, hSC => by
    have hflat : ((⟨w0, w1, w2⟩ :: ts).map tri).flatten = frame w0 ++ frame w1 ++ frame w2 ++ (ts.map tri).flatten := by
      simp [tri, List.append_assoc]
    rw [hflat] at hst hSC ⊢
    have hl : (⟨w0, w1, w2⟩ :: ts : List (List Bool × List Bool × List Bool)).length = ts.length + 1 := rfl
    have f0 := frame_length' w0; have f1 := frame_length' w1; have f2 := frame_length' w2
    simp only [List.length_append] at hSC
    have e0 := WExec.dec (cap := cap) C σ (by rw [hC] at *; omega)
    set σ0 := σ.setv C (σ.val C - 1) with hσ0
    have hS0 : σ0.val SC = σ.val SC := by simp [hσ0, Function.update_apply, hSCC]
    have e1 := skipF_exec (cap := cap) J SC w0 pre (frame w1 ++ frame w2 ++ (ts.map tri).flatten ++ rest) σ0
      (by simpa [hσ0, List.append_assoc] using hst) (by simpa [hσ0] using hsh) (by rw [hS0]; omega)
    set σ1 := (σ0.seth J (pre.length + (frame w0).length)).setv SC (σ0.val SC + (frame w0).length) with hσ1
    have e2 := skipF_exec (cap := cap) J SC w1 (pre ++ frame w0) (frame w2 ++ (ts.map tri).flatten ++ rest) σ1
      (by simpa [hσ1, hσ0, List.append_assoc] using hst) (by simp [hσ1])
      (by simp only [hσ1, WState.setv_val, WState.seth_val, Function.update_self, hS0]; omega)
    set σ2 := (σ1.seth J ((pre ++ frame w0).length + (frame w1).length)).setv SC (σ1.val SC + (frame w1).length)
      with hσ2
    have e3 := skipF_exec (cap := cap) J SC w2 (pre ++ frame w0 ++ frame w1) ((ts.map tri).flatten ++ rest) σ2
      (by simpa [hσ2, hσ1, hσ0, List.append_assoc] using hst) (by simp [hσ2, hσ1]; omega)
      (by simp only [hσ2, hσ1, WState.setv_val, WState.seth_val, Function.update_self, hS0]; omega)
    set σ3 := (σ2.seth J ((pre ++ frame w0 ++ frame w1).length + (frame w2).length)).setv SC
      (σ2.val SC + (frame w2).length) with hσ3
    have ih := skipT_exec J hSCC rest ts (pre ++ frame w0 ++ frame w1 ++ frame w2) σ3
      (by simpa [hσ3, hσ2, hσ1, hσ0, List.append_assoc] using hst) (by simp [hσ3, hσ2, hσ1]; omega)
      (by simp [hσ3, hσ2, hσ1, hσ0, Function.update_apply, Ne.symm hSCC, hC])
      (by omega) (by simp only [hσ3, hσ2, hσ1, WState.setv_val, WState.seth_val, Function.update_self, hS0]; omega)
    refine WExec.mono (WExec.cast cap (WExec.whrT (by rw [hC]; simp) (WExec.seq e0 (WExec.seq e1 (WExec.seq e2 e3)))
      ih) ?_ le_rfl) (by simp only [List.length_append] at *; rw [hl]; omega)
    apply WState.eq
    · funext j; by_cases hj : j = J
      · simp [hj, hσ3, hσ2, hσ1, hσ0]; omega
      · simp [hσ3, hσ2, hσ1, hσ0, Function.update_apply, hj]
    · rfl
    · funext q; by_cases hq : q = SC
      · simp [hq, hσ3, hσ2, hσ1, hσ0, hSCC, hS0]; omega
      · by_cases hq2 : q = C
        · simp [hq2, hσ3, hσ2, hσ1, hσ0, Ne.symm hSCC]
        · simp [hσ3, hσ2, hσ1, hσ0, Function.update_apply, hq, hq2]
    · rfl

/-! ## The front end -/

/-- A state that differs from `σ` only in the head of `J` and in the registers. -/
def atJ (σ : WState ns nr) (J : Fin (ns + 1)) (h : ℕ) (v : Fin nr → ℕ) : WState ns nr :=
  ⟨Function.update σ.sh J h, σ.st, v, σ.cell⟩

@[simp] theorem atJ_setv (σ : WState ns nr) (J : Fin (ns + 1)) (h : ℕ) (v : Fin nr → ℕ) (r : Fin nr) (x : ℕ) :
    (atJ σ J h v).setv r x = atJ σ J h (Function.update v r x) := rfl
@[simp] theorem atJ_seth (σ : WState ns nr) (J : Fin (ns + 1)) (h : ℕ) (v : Fin nr → ℕ) (x : ℕ) :
    (atJ σ J h v).seth J x = atJ σ J x v := by
  unfold atJ; apply WState.eq <;> simp [WState.seth]
@[simp] theorem atJ_val (σ : WState ns nr) (J : Fin (ns + 1)) (h : ℕ) (v : Fin nr → ℕ) : (atJ σ J h v).val = v := rfl
@[simp] theorem atJ_st (σ : WState ns nr) (J : Fin (ns + 1)) (h : ℕ) (v : Fin nr → ℕ) : (atJ σ J h v).st = σ.st := rfl
@[simp] theorem atJ_shJ (σ : WState ns nr) (J : Fin (ns + 1)) (h : ℕ) (v : Fin nr → ℕ) : (atJ σ J h v).sh J = h := by
  simp [atJ]

theorem atJ_self (σ : WState ns nr) (J : Fin (ns + 1)) (hJ : σ.sh J = 0) : atJ σ J 0 σ.val = σ := by
  unfold atJ; apply WState.eq <;> try rfl
  funext j; by_cases hj : j = J
  · subst hj; simp [hJ]
  · simp [Function.update_apply, hj]

/-- **The clause front end.** Registers: `R 0 = a` (kept), `R 1, R 2, R 3` the variable indices and `R 4, R 5, R 6`
the signs of the three literals of clause `a mod 2^{rb}`, `R 7 = proofBits`, `R 8 = randomBits`, `R 9 … R 17`
scratch. -/
def frontA (J : Fin (ns + 1)) (R : Fin 18 ↪ Fin nr) : WMX ns nr :=
  .seq (binW J (R 7) (R 10) (R 11) (R 12) (R 13))
  (.seq (binW J (R 8) (R 10) (R 11) (R 12) (R 13))
  (.seq (WMX.inc (R 14))
  (.seq (addR (R 8) (R 17) (R 12))
  (.seq (dblW (R 14) (R 17) (R 11) (R 12))
  (.seq (modW (R 0) (R 14) (R 15) (R 16) (R 17) (R 12))
  (.seq (.wm (WM.clear (R 16))) (.wm (WM.clear (R 14)))))))))

/-- The second half: skip `c` clauses, decode three literals, rewind. -/
def frontB (J : Fin (ns + 1)) (R : Fin 18 ↪ Fin nr) : WMX ns nr :=
  .seq (.wm (skipT J (R 13) (R 15)))
  (.seq (litW J (R 9) (R 10) (R 11) (R 12) (R 13) (R 1) (R 4))
  (.seq (litW J (R 9) (R 10) (R 11) (R 12) (R 13) (R 2) (R 5))
  (.seq (litW J (R 9) (R 10) (R 11) (R 12) (R 13) (R 3) (R 6))
    (.wm (WM.rewind J (R 13))))))

/-- **The clause front end.** Registers: `R 0 = a` (kept), `R 1, R 2, R 3` the variable indices and `R 4, R 5, R 6`
the signs of the three literals of clause `a mod 2^{rb}`, `R 7 = proofBits`, `R 8 = randomBits`, `R 9 … R 17`
scratch. -/
def frontW (J : Fin (ns + 1)) (R : Fin 18 ↪ Fin nr) : WMX ns nr := .seq (frontA J R) (frontB J R)

/-- The state between the halves: the header read, `c = a mod 2^{rb}` in `R 15`. -/
def frontMid (J : Fin (ns + 1)) (R : Fin 18 ↪ Fin nr) (σ : WState ns nr) {m : ℕ} (raw : RawThreeQueryPCPP m)
    (a : ℕ) : WState ns nr :=
  ((((σ.seth J ((frame raw.proofBits.bits).length + (frame raw.randomBits.bits).length)).setv (R 7)
    raw.proofBits).setv (R 8) raw.randomBits).setv (R 13)
    ((frame raw.proofBits.bits).length + (frame raw.randomBits.bits).length)).setv (R 15) (a % 2 ^ raw.randomBits)

/-- The end state of the front end: the eight output registers set. -/
def frontState (R : Fin 18 ↪ Fin nr) (σ : WState ns nr) {m : ℕ} (raw : RawThreeQueryPCPP m) (a : ℕ) :
    WState ns nr :=
  let cl := raw.clause ⟨a % 2 ^ raw.randomBits, Nat.mod_lt _ (by positivity)⟩
  ((((((((σ.setv (R 1) (litVar (cl 0))).setv (R 2) (litVar (cl 1))).setv (R 3) (litVar (cl 2))).setv (R 4)
    (litNeg (cl 0))).setv (R 5) (litNeg (cl 1))).setv (R 6) (litNeg (cl 2))).setv (R 7) raw.proofBits).setv (R 8)
    raw.randomBits)

/-- The cost class of the front end, in `|raw.word| + a + m + proofBits`. -/
def frontCost (S : ℕ) : ℕ := 10000 * (S + 1) ^ 2

open ClauseAccess (tri triples) in
theorem flat_len_ge : ∀ ts : List (List Bool × List Bool × List Bool), 3 * ts.length ≤ ((ts.map tri).flatten).length
  | [] => by simp
  | ⟨w0, w1, w2⟩ :: ts => by
    have := flat_len_ge ts
    simp only [List.map_cons, List.flatten_cons, List.length_append, tri, frame_length', List.length_cons]
    omega

theorem litVar_lt {k : ℕ} (l : Literal k) : litVar l < k := by
  cases l with
  | positive i => exact i.isLt
  | negative i => exact i.isLt

theorem code_lt {k : ℕ} (l : Literal k) : RepairSource.literalCode l < 2 * k := by
  rw [literalCode_eq]; have := litVar_lt l; have : litNeg l ≤ 1 := by cases l <;> simp [litNeg]
  omega

theorem named {P : WMX ns nr} {σ τ : WState ns nr} {n : ℕ} (h : WXExec cap P σ τ n) :
    ∃ τ', τ' = τ ∧ WXExec cap P σ τ' n := ⟨τ, rfl, h⟩

theorem mul_le_sq (x y S k c : ℕ) (hx : x ≤ S + 1) (hy : y ≤ S + 1) :
    x * (k * y + c) ≤ (k + c) * (S + 1) ^ 2 := by
  have h1 : x * (k * y + c) ≤ (S + 1) * (k * (S + 1) + c) :=
    Nat.mul_le_mul hx (Nat.add_le_add_right (Nat.mul_le_mul_left k hy) c)
  have h3 : c * (S + 1) ≤ c * (S + 1) ^ 2 := Nat.mul_le_mul_left c (Nat.le_self_pow (by norm_num) _)
  have e1 : (S + 1) * (k * (S + 1) + c) = k * (S + 1) ^ 2 + c * (S + 1) := by ring
  have e2 : (k + c) * (S + 1) ^ 2 = k * (S + 1) ^ 2 + c * (S + 1) ^ 2 := by ring
  omega

theorem sq_le_four (x S : ℕ) (h : x + 1 ≤ 2 * (S + 1)) : (x + 1) ^ 2 ≤ 4 * (S + 1) ^ 2 := by nlinarith

open ClauseAccess (tri triples) in
theorem frontA_exec (J : Fin (ns + 1)) (R : Fin 18 ↪ Fin nr) {m : ℕ} (raw : RawThreeQueryPCPP m) (a : ℕ)
    (σ : WState ns nr) (hJ : RdEq (σ.st J) raw.word) (hJh : σ.sh J = 0) (hA : σ.val (R 0) = a)
    (hz : ∀ i : Fin 18, i ≠ 0 → σ.val (R i) = 0)
    (hcap : 16 * (raw.word.length + a + m + raw.proofBits + 2) ≤ cap) :
    WXExec cap (frontA J R) σ (frontMid J R σ raw a) (1000 * (raw.word.length + a + m + raw.proofBits + 1) ^ 2) := by
  have nd : ∀ l : List (Fin 18), l.Nodup → (l.map R).Nodup := fun l h => h.map R.injective
  have rne : ∀ i j : Fin 18, i ≠ j → R i ≠ R j := fun i j h => R.injective.ne h
  -- the word
  set pb := raw.proofBits with hpb
  set rb := raw.randomBits with hrb
  set W := raw.word.length with hW
  set ts := triples raw with hts
  have htl : ts.length = 2 ^ rb := by simp [hts, triples, hrb]
  have hw : raw.word = (frame pb.bits ++ frame rb.bits) ++ (ts.map tri).flatten := ClauseAccess.word_eq raw
  have hcl : a % 2 ^ rb < ts.length := by rw [htl]; exact Nat.mod_lt _ (by positivity)
  set c := a % 2 ^ rb with hc
  set cf : Fin (2 ^ raw.randomBits) := ⟨c, Nat.mod_lt _ (by positivity)⟩ with hcf
  set l0 := raw.clause cf 0 with hl0
  set l1 := raw.clause cf 1 with hl1
  set l2 := raw.clause cf 2 with hl2
  set b0 := (RepairSource.literalCode l0).bits with hb0
  set b1 := (RepairSource.literalCode l1).bits with hb1
  set b2 := (RepairSource.literalCode l2).bits with hb2
  have hget : ts[c] = (b0, b1, b2) := by simp [hts, triples, hb0, hb1, hb2, hl0, hl1, hl2, hcf]
  set fA := ((ts.take c).map tri).flatten with hfA
  set fB := ((ts.drop (c + 1)).map tri).flatten with hfB
  have hsplit := ClauseAccess.flatten_split ts c hcl
  rw [hget] at hsplit
  have hword : raw.word = frame pb.bits ++ frame rb.bits ++ fA ++ frame b0 ++ frame b1 ++ frame b2 ++ fB := by
    rw [hw, hsplit]; simp only [tri, List.append_assoc, hfA, hfB]
  have hWl : W = (frame pb.bits).length + (frame rb.bits).length + fA.length + (frame b0).length +
      (frame b1).length + (frame b2).length + fB.length := by rw [hW, hword]; simp only [List.length_append]
  have h3 := flat_len_ge ts
  have hflat : ((ts.map tri).flatten).length ≤ W := by rw [hW, hw]; simp only [List.length_append]; omega
  have hM : 2 ^ rb ≤ W := by omega
  have hrbl : rb < 2 ^ rb := Nat.lt_two_pow_self
  have hcm : c < 2 ^ rb := Nat.mod_lt _ (by positivity)
  have hfAc : (ts.take c).length = c := by simp [List.length_take]; omega
  have k0 := code_lt l0
  have k1 := code_lt l1
  have k2 := code_lt l2
  have fp := frame_length' pb.bits
  have fr := frame_length' rb.bits
  have pbl := two_pow_bits_le pb
  have rbl := two_pow_bits_le rb
  have pbL := bits_len_le pb
  -- the run
  obtain ⟨s1, hs1, e1⟩ := named (binW_exec (cap := cap) J (nd [7, 10, 11, 12, 13] (by decide)) pb.bits []
    (frame rb.bits ++ (ts.map tri).flatten) σ (by rw [hw] at hJ; simpa [List.append_assoc] using hJ) (by simp [hJh])
    (hz 10 (by decide)) (hz 11 (by decide)) (hz 12 (by decide)) (by rw [hz 7 (by decide)]; omega)
    (by rw [hz 13 (by decide)]; omega))
  obtain ⟨s2, hs2, e2⟩ := named (binW_exec (cap := cap) J (nd [8, 10, 11, 12, 13] (by decide)) rb.bits (frame pb.bits)
    ((ts.map tri).flatten) s1 (by rw [hs1]; simp only [WState.setv_st, WState.seth_st]; rw [hw] at hJ; exact hJ)
    (by rw [hs1]; simp)
    (by simp [hs1, Function.update_apply, R.injective.eq_iff, hz])
    (by simp [hs1, Function.update_apply, R.injective.eq_iff, hz])
    (by simp [hs1, Function.update_apply, R.injective.eq_iff, hz])
    (by simp [hs1, Function.update_apply, R.injective.eq_iff, hz]; omega)
    (by simp [hs1, Function.update_apply, R.injective.eq_iff, hz]; omega))
  obtain ⟨s3, hs3, e3⟩ := named (WXExec.inc (cap := cap) (R 14) s2
    (by simp [hs2, hs1, Function.update_apply, R.injective.eq_iff, hz]; omega))
  obtain ⟨s4, hs4, e4⟩ := named (addR_spec cap (rne 8 17 (by decide)) (rne 8 12 (by decide)) (rne 17 12 (by decide)) s3
    (by simp [hs3, hs2, hs1, Function.update_apply, R.injective.eq_iff, hz])
    (by simp [hs3, hs2, hs1, Function.update_apply, R.injective.eq_iff, hz, value_bits]; omega))
  obtain ⟨s5, hs5, e5⟩ := named (dblW_exec (cap := cap) (nd [14, 17, 11, 12] (by decide)) (2 ^ rb) (by omega) rb s4
    (by simp [hs4, hs3, hs2, hs1, Function.update_apply, R.injective.eq_iff, hz, value_bits]) (by omega)
    (by simp [hs4, hs3, hs2, hs1, Function.update_apply, R.injective.eq_iff, hz])
    (by simp [hs4, hs3, hs2, hs1, Function.update_apply, R.injective.eq_iff, hz])
    (by simp [hs4, hs3, hs2, hs1, Function.update_apply, R.injective.eq_iff, hz]))
  obtain ⟨s6, hs6, e6⟩ := named (modW_exec (cap := cap) (nd [0, 14, 15, 16, 17, 12] (by decide)) a (2 ^ rb)
    (by positivity) (by omega) (by omega) s5
    (by simp [hs5, hs4, hs3, hs2, hs1, Function.update_apply, R.injective.eq_iff, hA])
    (by simp [hs5, hs4, hs3, hs2, hs1, Function.update_apply, R.injective.eq_iff, hz])
    (by simp [hs5, hs4, hs3, hs2, hs1, Function.update_apply, R.injective.eq_iff, hz])
    (by simp [hs5, hs4, hs3, hs2, hs1, Function.update_apply, R.injective.eq_iff, hz])
    (by simp [hs5, hs4, hs3, hs2, hs1, Function.update_apply, R.injective.eq_iff, hz])
    (by simp [hs5, hs4, hs3, hs2, hs1, Function.update_apply, R.injective.eq_iff, hz]))
  obtain ⟨s7, hs7, e7⟩ := named (WXExec.wm (wclear_spec (cap := cap) (R 16) (2 ^ rb - c) s6
    (by simp [hs6, Function.update_apply, R.injective.eq_iff]; omega)
    (by simp [hs6, Function.update_apply, R.injective.eq_iff]; omega)))
  obtain ⟨s8, hs8, e8⟩ := named (WXExec.wm (wclear_spec (cap := cap) (R 14) (2 ^ rb) s7
    (by simp [hs7, hs6, hs5, hs4, hs3, hs2, hs1, Function.update_apply, R.injective.eq_iff, hz])
    (by simp [hs7, hs6, hs5, hs4, hs3, hs2, hs1, Function.update_apply, R.injective.eq_iff, hz]; omega)))
  have whole := WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4 (WXExec.seq e5 (WXExec.seq e6
    (WXExec.seq e7 e8))))))
  refine WXExec.mono (WXExec.cast cap whole ?_ le_rfl) ?_
  · apply WState.eq
    · funext j
      by_cases hj : j = J
      · rw [hj]; simp [hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1, frontMid, hJh, hpb, hrb]
      · simp [hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1, frontMid, Function.update_apply, hj]
    · simp [hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1, frontMid]
    · funext q
      by_cases hq : ∃ i, R i = q
      · obtain ⟨i, rfl⟩ := hq
        fin_cases i <;>
          simp [hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1, frontMid, Function.update_apply,
            R.injective.eq_iff, hz, hA, value_bits, hc, hrb, hpb]
      · have hq' : ∀ i, q ≠ R i := fun i h => hq ⟨i, h.symm⟩
        simp [hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1, frontMid, Function.update_apply, hq']
    · simp [hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1, frontMid]
  · have hR8 : s3.val (R 8) = rb := by
      simp [hs3, hs2, hs1, Function.update_apply, R.injective.eq_iff, hz, value_bits]
    rw [hR8]
    have hQ1 : W + a + m + pb + 1 ≤ (W + a + m + pb + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
    have p1 : binCost pb.bits.length ≤ 200 * (W + a + m + pb + 1) ^ 2 :=
      (binCost_le pb).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))
    have p2 : binCost rb.bits.length ≤ 200 * (W + a + m + pb + 1) ^ 2 :=
      (binCost_le rb).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))
    have p3 := mul_le_sq rb (2 ^ rb) (W + a + m + pb) 25 10 (by omega) (by omega)
    have p4 := mul_le_sq a (2 ^ rb) (W + a + m + pb) 25 20 (by omega) (by omega)
    omega

open ClauseAccess (tri triples) in
theorem frontB_exec (J : Fin (ns + 1)) (R : Fin 18 ↪ Fin nr) {m : ℕ} (raw : RawThreeQueryPCPP m) (a : ℕ)
    (σ : WState ns nr) (hJ : RdEq (σ.st J) raw.word) (hJh : σ.sh J = 0) (hA : σ.val (R 0) = a)
    (hz : ∀ i : Fin 18, i ≠ 0 → σ.val (R i) = 0)
    (hcap : 16 * (raw.word.length + a + m + raw.proofBits + 2) ≤ cap) :
    WXExec cap (frontB J R) (frontMid J R σ raw a) (frontState R σ raw a)
      (5000 * (raw.word.length + a + m + raw.proofBits + 1) ^ 2) := by
  have nd : ∀ l : List (Fin 18), l.Nodup → (l.map R).Nodup := fun l h => h.map R.injective
  have rne : ∀ i j : Fin 18, i ≠ j → R i ≠ R j := fun i j h => R.injective.ne h
  -- the word
  set pb := raw.proofBits with hpb
  set rb := raw.randomBits with hrb
  set W := raw.word.length with hW
  set ts := triples raw with hts
  have htl : ts.length = 2 ^ rb := by simp [hts, triples, hrb]
  have hw : raw.word = (frame pb.bits ++ frame rb.bits) ++ (ts.map tri).flatten := ClauseAccess.word_eq raw
  have hcl : a % 2 ^ rb < ts.length := by rw [htl]; exact Nat.mod_lt _ (by positivity)
  set c := a % 2 ^ rb with hc
  set cf : Fin (2 ^ raw.randomBits) := ⟨c, Nat.mod_lt _ (by positivity)⟩ with hcf
  set l0 := raw.clause cf 0 with hl0
  set l1 := raw.clause cf 1 with hl1
  set l2 := raw.clause cf 2 with hl2
  set b0 := (RepairSource.literalCode l0).bits with hb0
  set b1 := (RepairSource.literalCode l1).bits with hb1
  set b2 := (RepairSource.literalCode l2).bits with hb2
  have hget : ts[c] = (b0, b1, b2) := by simp [hts, triples, hb0, hb1, hb2, hl0, hl1, hl2, hcf]
  set fA := ((ts.take c).map tri).flatten with hfA
  set fB := ((ts.drop (c + 1)).map tri).flatten with hfB
  have hsplit := ClauseAccess.flatten_split ts c hcl
  rw [hget] at hsplit
  have hword : raw.word = frame pb.bits ++ frame rb.bits ++ fA ++ frame b0 ++ frame b1 ++ frame b2 ++ fB := by
    rw [hw, hsplit]; simp only [tri, List.append_assoc, hfA, hfB]
  have hWl : W = (frame pb.bits).length + (frame rb.bits).length + fA.length + (frame b0).length +
      (frame b1).length + (frame b2).length + fB.length := by rw [hW, hword]; simp only [List.length_append]
  have h3 := flat_len_ge ts
  have hflat : ((ts.map tri).flatten).length ≤ W := by rw [hW, hw]; simp only [List.length_append]; omega
  have hM : 2 ^ rb ≤ W := by omega
  have hrbl : rb < 2 ^ rb := Nat.lt_two_pow_self
  have hcm : c < 2 ^ rb := Nat.mod_lt _ (by positivity)
  have hfAc : (ts.take c).length = c := by simp [List.length_take]; omega
  have k0 := code_lt l0
  have k1 := code_lt l1
  have k2 := code_lt l2
  have fp := frame_length' pb.bits
  have fr := frame_length' rb.bits
  have pbl := two_pow_bits_le pb
  have rbl := two_pow_bits_le rb
  have pbL := bits_len_le pb
  set s8 := frontMid J R σ raw a with hs8
  have hfAlen : fA.length = (List.take c (List.map (List.length ∘ tri) ts)).sum := by simp [hfA]
  have hS8 : s8.val (R 13) = (frame pb.bits).length + (frame rb.bits).length := by
    simp [hs8, frontMid, Function.update_apply, R.injective.eq_iff, hpb, hrb]
  obtain ⟨s9, hs9, e9⟩ := named (WXExec.wm (skipT_exec (cap := cap) J (rne 13 15 (by decide))
    (frame b0 ++ frame b1 ++ frame b2 ++ fB) (ts.take c) (frame pb.bits ++ frame rb.bits) s8
    (by simp only [hs8, frontMid, WState.setv_st, WState.seth_st]
        rw [hword] at hJ; simpa [hfA, List.append_assoc] using hJ)
    (by simp [hs8, frontMid, hpb, hrb])
    (by rw [hfAc]; simp [hs8, frontMid, Function.update_apply, R.injective.eq_iff]; omega)
    (by omega)
    (by rw [hS8]; change _ + fA.length ≤ cap; omega)))
  have hs9J : s9.sh J = (frame pb.bits ++ frame rb.bits ++ fA).length := by
    rw [hs9]; simp [hs8, frontMid, hfA]; omega
  have hS9 : s9.val (R 13) = (frame pb.bits ++ frame rb.bits ++ fA).length := by
    rw [hs9]; simp [hS8, Function.update_apply, R.injective.eq_iff]; have := hfAlen; omega
  have z9 : ∀ i : Fin 18, i ∈ [9, 10, 11, 12, 1, 4, 2, 5, 3, 6] → s9.val (R i) = 0 := by
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with h | h | h | h | h | h | h | h | h | h <;> subst h <;>
      simp [hs9, hs8, frontMid, Function.update_apply, R.injective.eq_iff, hz]
  have hst9 : s9.st J = σ.st J := by simp [hs9, hs8, frontMid]
  obtain ⟨s10, hs10, e10⟩ := named (litW_exec (cap := cap) J (nd [9, 10, 11, 12, 13, 1, 4] (by decide)) l0
    (frame pb.bits ++ frame rb.bits ++ fA) (frame b1 ++ frame b2 ++ fB) s9
    (by rw [hst9]; rw [hword] at hJ; simpa [List.append_assoc] using hJ) hs9J
    (z9 9 (by simp)) (z9 10 (by simp)) (z9 11 (by simp)) (z9 12 (by simp)) (z9 1 (by simp)) (z9 4 (by simp))
    (by omega) (by rw [hS9, ← hb0]; simp only [List.length_append] at hWl ⊢; omega))
  have hs10J : s10.sh J = (frame pb.bits ++ frame rb.bits ++ fA ++ frame b0).length := by
    rw [hs10]; simp [hs9J, hb0] <;> omega
  have hS10 : s10.val (R 13) = (frame pb.bits ++ frame rb.bits ++ fA ++ frame b0).length := by
    rw [hs10]; simp [hS9, hb0, Function.update_apply, R.injective.eq_iff] <;> omega
  have z10 : ∀ i : Fin 18, i ∈ [9, 10, 11, 12, 2, 5, 3, 6] → s10.val (R i) = 0 := by
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with h | h | h | h | h | h | h | h <;> subst h <;>
      simp [hs10, Function.update_apply, R.injective.eq_iff, z9]
  obtain ⟨s11, hs11, e11⟩ := named (litW_exec (cap := cap) J (nd [9, 10, 11, 12, 13, 2, 5] (by decide)) l1
    (frame pb.bits ++ frame rb.bits ++ fA ++ frame b0) (frame b2 ++ fB) s10
    (by rw [hs10]; simp only [WState.setv_st, WState.seth_st, Function.update_apply]; rw [hst9]
        rw [hword] at hJ; simpa [List.append_assoc] using hJ) hs10J
    (z10 9 (by simp)) (z10 10 (by simp)) (z10 11 (by simp)) (z10 12 (by simp)) (z10 2 (by simp))
    (z10 5 (by simp)) (by omega) (by rw [hS10, ← hb1]; simp only [List.length_append] at hWl ⊢; omega))
  have hs11J : s11.sh J = (frame pb.bits ++ frame rb.bits ++ fA ++ frame b0 ++ frame b1).length := by
    rw [hs11]; simp [hs10J, hb1] <;> omega
  have hS11 : s11.val (R 13) = (frame pb.bits ++ frame rb.bits ++ fA ++ frame b0 ++ frame b1).length := by
    rw [hs11]; simp [hS10, hb1, Function.update_apply, R.injective.eq_iff] <;> omega
  have z11 : ∀ i : Fin 18, i ∈ [9, 10, 11, 12, 3, 6] → s11.val (R i) = 0 := by
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with h | h | h | h | h | h <;> subst h <;>
      simp [hs11, Function.update_apply, R.injective.eq_iff, z10]
  obtain ⟨s12, hs12, e12⟩ := named (litW_exec (cap := cap) J (nd [9, 10, 11, 12, 13, 3, 6] (by decide)) l2
    (frame pb.bits ++ frame rb.bits ++ fA ++ frame b0 ++ frame b1) fB s11
    (by rw [hs11, hs10]; simp only [WState.setv_st, WState.seth_st, Function.update_apply]; rw [hst9]
        rw [hword] at hJ; simpa [List.append_assoc] using hJ) hs11J
    (z11 9 (by simp)) (z11 10 (by simp)) (z11 11 (by simp)) (z11 12 (by simp)) (z11 3 (by simp))
    (z11 6 (by simp)) (by omega) (by rw [hS11, ← hb2]; simp only [List.length_append] at hWl ⊢; omega))
  have hS12 : s12.val (R 13) = (frame pb.bits ++ frame rb.bits ++ fA ++ frame b0 ++ frame b1 ++ frame b2).length := by
    rw [hs12]; simp [hS11, hb2, Function.update_apply, R.injective.eq_iff] <;> omega
  have hs12J : s12.sh J = (frame pb.bits ++ frame rb.bits ++ fA ++ frame b0 ++ frame b1 ++ frame b2).length := by
    rw [hs12]; simp [hs11J, hb2] <;> omega
  obtain ⟨s13, hs13, e13⟩ := named (WXExec.wm (wrewind_spec (cap := cap) J (R 13) _ s12 hS12
    (by rw [hS12]; simp only [List.length_append] at hWl ⊢; omega)))
  have whole := WXExec.seq e9 (WXExec.seq e10 (WXExec.seq e11 (WXExec.seq e12 e13)))
  refine WXExec.mono (WXExec.cast cap whole ?_ le_rfl) ?_
  · rw [hs13]
    apply WState.eq
    · funext j
      by_cases hj : j = J
      · rw [hj]; simp [hs12J, frontState, hJh]
      · simp [hs12, hs11, hs10, hs9, hs8, frontMid, frontState, Function.update_apply,
          hj]
    · simp [hs12, hs11, hs10, hs9, hs8, frontMid, frontState]
    · funext q
      by_cases hq : ∃ i, R i = q
      · obtain ⟨i, rfl⟩ := hq
        fin_cases i <;>
          simp [hs12, hs11, hs10, hs9, hs8, frontMid, frontState, Function.update_apply,
            R.injective.eq_iff, hz, hA, value_bits, hl0, hl1, hl2, hcf, hc, hrb, hpb]
      · have hq' : ∀ i, q ≠ R i := fun i h => hq ⟨i, h.symm⟩
        simp [hs12, hs11, hs10, hs9, hs8, frontMid, frontState, Function.update_apply,
          hq']
    · simp [hs12, hs11, hs10, hs9, hs8, frontMid, frontState]
  · have hpre : (frame pb.bits ++ frame rb.bits ++ fA ++ frame b0 ++ frame b1 ++ frame b2).length ≤ W := by
      simp only [List.length_append]; omega
    have hfAeq : (List.map tri (List.take c ts)).flatten.length = fA.length := rfl
    have hQ1 : W + a + m + pb + 1 ≤ (W + a + m + pb + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
    have pl : ∀ x : ℕ, x < 2 * (m + raw.proofBits) → litCost x ≤ 1200 * (W + a + m + pb + 1) ^ 2 := by
      intro x hx
      have h1 := sq_le_four x (W + a + m + pb) (by omega)
      have h2 := litCost_le x
      omega
    have p5 := pl _ k0
    have p6 := pl _ k1
    have p7 := pl _ k2
    omega

open ClauseAccess (tri triples) in

theorem front_exec (J : Fin (ns + 1)) (R : Fin 18 ↪ Fin nr) {m : ℕ} (raw : RawThreeQueryPCPP m) (a : ℕ)
    (σ : WState ns nr) (hJ : RdEq (σ.st J) raw.word) (hJh : σ.sh J = 0) (hA : σ.val (R 0) = a)
    (hz : ∀ i : Fin 18, i ≠ 0 → σ.val (R i) = 0)
    (hcap : 16 * (raw.word.length + a + m + raw.proofBits + 2) ≤ cap) :
    WXExec cap (frontW J R) σ (frontState R σ raw a) (frontCost (raw.word.length + a + m + raw.proofBits)) := by
  refine WXExec.mono (WXExec.seq (frontA_exec J R raw a σ hJ hJh hA hz hcap) (frontB_exec J R raw a σ hJ hJh hA hz hcap)) ?_
  unfold frontCost
  have : 1 ≤ (raw.word.length + a + m + raw.proofBits + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  omega

end NearCubicGates.Close.CheckedPCPP.ClauseFront
