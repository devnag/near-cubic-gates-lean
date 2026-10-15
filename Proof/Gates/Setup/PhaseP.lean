import Proof.Gates.Setup.Layout
import Proof.Gates.Recovery.HTParts3
import Proof.Gates.CheckedPCPP.ClauseFront

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.Setup

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP

noncomputable section

/-! ## The arithmetic -/

/-- `2^{clog₂ N} ≤ N` exactly when `N` is a power of two (`N = 2^{⌊log₂ N⌋}`), for `N ≥ 1`. -/
theorem pow2_iff (N : ℕ) : 2 ^ Nat.clog 2 N ≤ N ↔ N = 2 ^ Nat.log 2 N := by
  constructor
  · intro h
    have h1 : N ≤ 2 ^ Nat.clog 2 N := Nat.le_pow_clog (by norm_num) N
    have h2 : N = 2 ^ Nat.clog 2 N := le_antisymm h1 h
    conv_rhs => rw [h2]
    rw [Nat.log_pow (by norm_num)]
    exact h2
  · intro h
    rw [h, Nat.clog_pow 2 _ (by norm_num)]

/-- At `N = 2^ν`, `clog₂ N = log₂ N = ν`. -/
theorem clog_eq_log_of_pow (N : ℕ) (h : N = 2 ^ Nat.log 2 N) : Nat.clog 2 N = Nat.log 2 N := by
  rw [h, Nat.clog_pow 2 _ (by norm_num), Nat.log_pow (by norm_num)]

/-! ## The program -/

/-- **Phase P** (on the flag stream `FL`). -/
def powP {ns : ℕ} (FL : Fin (ns + 1)) : WMX ns nrW :=
  .seq (.wm (Codec.dupR rN pT1 dS))
  (.seq (WMX.dec pT1)
  (.seq (Recovery.HTParts.sizeW pT1 pH pB rNu)
  (.seq (WMX.inc pT2)
  (.seq (.wm (Codec.dupR rNu pT3 dS))
  (.seq (ClauseFront.dblW pT2 pT3 pH pB)
  (.seq (Recovery.HTParts.leW pT2 rN pU pK pT pF)
  (.seq (.ifr pF (WMX.wr FL true) WMX.skip)
  (.wm (.seq (WM.clear pT2) (WM.clear pF))))))))))

/-- The cost class of phase P. -/
def powCostP (N : ℕ) : ℕ := 1000 * (N + 1) ^ 2

/-- The flag phase P writes. -/
def powFlag (N : ℕ) : List Bool := if 2 ^ Nat.clog 2 N ≤ N then [true] else []

theorem powP_exec {ns cap : ℕ} (FL : Fin (ns + 1)) (N : ℕ) (σ : WState ns nrW) (hN : σ.val rN = N) (h1 : 1 ≤ N)
    (hz : ∀ r ∈ ([rNu, pT1, pT2, pT3, pH, pB, pF, pU, pK, pT, dS] : List (Fin nrW)), σ.val r = 0)
    (hFL : σ.st FL = []) (hFLh : σ.sh FL = 0) (hcap : 4 * N + 4 ≤ cap) :
    WXExec cap (powP FL) σ ((σ.setv rNu (Nat.clog 2 N)).sets FL (powFlag N)) (powCostP N) := by
  have z : ∀ r ∈ ([rNu, pT1, pT2, pT3, pH, pB, pF, pU, pK, pT, dS] : List (Fin nrW)), σ.val r = 0 := hz
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at z
  obtain ⟨zNu, z1, z2, z3, zH, zB, zF, zU, zK, zT, zd⟩ := z
  set ν := Nat.clog 2 N with hν
  have hνs : ν = (N - 1).size := Recovery.TableSem.clog_eq_size N
  have hνN : ν ≤ N := by
    rw [hνs, Nat.size_le]
    have := Nat.lt_two_pow_self (n := N)
    omega
  have hpow : 2 ^ ν ≤ 2 * N + 1 := Outer.two_pow_clog_le N

  have e1 := Codec.dupR_spec cap rN pT1 dS (by decide) (by decide) (by decide) σ zd (by rw [hN, z1]; omega)
  rw [z1, hN, Nat.zero_add] at e1
  set σ1 := σ.setv pT1 N with hσ1

  have e2 := WXExec.dec (cap := cap) pT1 σ1 (by simp [hσ1]; omega)
  rw [show σ1.setv pT1 (σ1.val pT1 - 1) = σ.setv pT1 (N - 1) by simp [hσ1, LitDecode.setv_setv]] at e2
  set σ2 := σ.setv pT1 (N - 1) with hσ2
  -- 3. `ν := size (N − 1)`
  have e3 := Recovery.HTParts.sizeW_exec (cap := cap) (X := pT1) (H := pH) (B := pB) (C := rNu) (by decide) N
    (by omega) (N - 1) σ2 (by omega) (by simp (config := { decide := true }) [Function.update_apply, hσ2]) (by simp (config := { decide := true }) [Function.update_apply, hσ2, zH]) (by simp (config := { decide := true }) [Function.update_apply, hσ2, zB])
    (by simp (config := { decide := true }) [Function.update_apply, hσ2, zNu]; rw [← hνs]; omega)
  rw [show (σ2.setv pT1 0).setv rNu (σ2.val rNu + (N - 1).size) = σ.setv rNu ν by
    clear e1 e2 e3
    apply WState.eq <;> try rfl
    funext r; simp only [hσ2, WState.setv_val, Function.update_apply]
    wregs] at e3
  set σ3 := σ.setv rNu ν with hσ3

  have e4 := WXExec.inc (cap := cap) pT2 σ3 (by simp (config := { decide := true }) [Function.update_apply, hσ3, z2]; omega)
  rw [show σ3.setv pT2 (σ3.val pT2 + 1) = σ3.setv pT2 1 by simp (config := { decide := true }) [Function.update_apply, hσ3, z2]] at e4
  set σ4 := σ3.setv pT2 1 with hσ4

  have e5 := Codec.dupR_spec cap rNu pT3 dS (by decide) (by decide) (by decide) σ4 (by simp (config := { decide := true }) [Function.update_apply, hσ4, hσ3, zd])
    (by simp (config := { decide := true }) [Function.update_apply, hσ4, hσ3, z3]; omega)
  rw [show σ4.setv pT3 (σ4.val pT3 + σ4.val rNu) = σ4.setv pT3 ν by simp (config := { decide := true }) [Function.update_apply, hσ4, hσ3, z3]] at e5
  set σ5 := σ4.setv pT3 ν with hσ5

  have e6 := ClauseFront.dblW_exec (cap := cap) (M := pT2) (K := pT3) (Q := pH) (T := pB) (by decide) (2 * N + 1)
    (by omega) ν σ5 (by simp (config := { decide := true }) [Function.update_apply, hσ5]) (by omega) (by simp (config := { decide := true }) [Function.update_apply, hσ5, hσ4, hσ3, zH]) (by simp (config := { decide := true }) [Function.update_apply, hσ5, hσ4, hσ3, zB])
    (by simp (config := { decide := true }) [Function.update_apply, hσ5, hσ4]; omega)
  rw [show (σ5.setv pT3 0).setv pT2 (σ5.val pT2 * 2 ^ ν) = σ3.setv pT2 (2 ^ ν) by
    clear e1 e2 e3 e4 e5 e6
    apply WState.eq <;> try rfl
    funext r; simp only [hσ5, hσ4, hσ3, WState.setv_val, Function.update_apply]
    wregs] at e6
  set σ6 := σ3.setv pT2 (2 ^ ν) with hσ6
  -- 7. `F := [2^ν ≤ N]`
  have e7 := Recovery.HTParts.leW_exec (cap := cap) (A := pT2) (B := rN) (U := pU) (K := pK) (T := pT) (F := pF)
    (by decide) (2 ^ ν) N (by omega) σ6 (by simp (config := { decide := true }) [Function.update_apply, hσ6]) (by simp (config := { decide := true }) [Function.update_apply, hσ6, hσ3, hN]) (by simp (config := { decide := true }) [Function.update_apply, hσ6, hσ3, zU])
    (by simp (config := { decide := true }) [Function.update_apply, hσ6, hσ3, zK]) (by simp (config := { decide := true }) [Function.update_apply, hσ6, hσ3, zT]) (by simp (config := { decide := true }) [Function.update_apply, hσ6, hσ3, zF])
  set σ7 := σ6.setv pF (if 2 ^ ν ≤ N then 1 else 0) with hσ7
  -- 8. the flag stream
  have hFL7 : σ7.st FL = [] := by simp [hσ7, hσ6, hσ3, hFL]
  have hFLh7 : σ7.sh FL = 0 := by simp [hσ7, hσ6, hσ3, hFLh]
  have hF7 : σ7.val pF = if 2 ^ ν ≤ N then 1 else 0 := by simp [hσ7]
  have e8 : WXExec cap (.ifr pF (WMX.wr FL true) WMX.skip) σ7 (σ7.sets FL (powFlag N)) 2 := by
    by_cases hp : 2 ^ ν ≤ N
    · have := WXExec.ifrT (Q := WMX.skip) (by rw [hF7, if_pos hp]; omega) (WXExec.wr (cap := cap) FL true σ7)
      refine WXExec.cast cap this ?_ le_rfl
      rw [hFL7, hFLh7]; simp [powFlag, ← hν, hp]; rfl
    · have := WXExec.ifrF (P := WMX.wr FL true) (by rw [hF7, if_neg hp]) (WXExec.skip cap σ7)
      refine WXExec.cast cap this ?_ (by omega)
      simp only [powFlag, ← hν, hp, if_false]
      apply WState.eq <;> try rfl
      funext i; by_cases hi : i = FL
      · subst hi; simp [hFL7]
      · simp [Function.update_of_ne hi]
  set σ8 := σ7.sets FL (powFlag N) with hσ8
  -- 9. clear the scratch
  have e9 := wclear_spec (cap := cap) pT2 (2 ^ ν) σ8 (by simp (config := { decide := true }) [Function.update_apply, hσ8, hσ7, hσ6]) (by simp (config := { decide := true }) [Function.update_apply, hσ8, hσ7, hσ6]; omega)
  have e10 := wclear_spec (cap := cap) pF (if 2 ^ ν ≤ N then 1 else 0) (σ8.setv pT2 0) (by simp (config := { decide := true }) [Function.update_apply, hσ8, hσ7])
    (by simp (config := { decide := true }) [Function.update_apply, hσ8, hσ7]; split_ifs <;> omega)
  refine WXExec.cast cap (WXExec.seq (WXExec.wm e1) (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4 (WXExec.seq
    (WXExec.wm e5) (WXExec.seq e6 (WXExec.seq e7 (WXExec.seq e8 (WXExec.wm (WExec.seq e9 e10)))))))))) ?_ ?_
  · clear e1 e2 e3 e4 e5 e6 e7 e8 e9 e10
    apply WState.eq
    · rfl
    · rfl
    · funext r
      simp only [hσ8, hσ7, hσ6, hσ3, WState.setv_val, WState.sets_val, Function.update_apply]
      wregs
    · rfl
  · -- the cost
    have hsz : (N - 1).size ≤ N := by rw [← hνs]; exact hνN
    have hc3 : (N - 1).size * (12 * N + 30) ≤ N * (12 * N + 30) := Nat.mul_le_mul_right _ hsz
    have hc6 : ν * (25 * (2 * N + 1) + 10) ≤ N * (25 * (2 * N + 1) + 10) := Nat.mul_le_mul_right _ hνN
    have hf : (if 2 ^ ν ≤ N then 1 else 0) ≤ 1 := by split_ifs <;> omega
    have h4 : σ4.val rNu = ν := by simp (config := { decide := true }) [hσ4, hσ3, Function.update_apply]
    rw [h4]
    unfold powCostP
    nlinarith

end

end NearCubicGates.Close.Setup
