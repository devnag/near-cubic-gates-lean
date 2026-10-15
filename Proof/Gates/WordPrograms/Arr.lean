import Proof.Gates.WordPrograms.Hoare
import Proof.Gates.WordPrograms.RecLoop

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.WordPrograms
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm

variable {ns nr : ℕ}

/-- `Wk := ` record `n` of `A` (`n` in `N`). -/
def getAt (A Wk : Fin (ns + 1)) (CA CW N K2 : Fin nr) : WMX ns nr :=
  .seq (repK N K2 (.wm (copyRec A Wk CA CW))) (.seq (.wm (copyRec A Wk CA CW)) (.wm (WM.rewind A CA)))

/-- The state after copying `k` records. -/
def getSt (σ : WState ns nr) (A Wk : Fin (ns + 1)) (CA : Fin nr) (L : ℕ) (xs : List ℕ) (k : ℕ) : WState ns nr :=
  ((σ.sets Wk (if k = 0 then σ.st Wk else frame (binary L (xs.getD (k - 1) 0)))).seth A (k * (2 * L + 1))).setv CA
    (k * (2 * L + 1))

theorem getAt_spec (cap : ℕ) {A Wk : Fin (ns + 1)} {CA CW N K2 : Fin nr} (hAW : A ≠ Wk)
    (hR : [CA, CW, N, K2].Nodup) (L : ℕ) (hL : 1 ≤ L) (xs : List ℕ) (n : ℕ) (hn : n < xs.length) (σ : WState ns nr)
    (junk : List Bool) (hA : σ.st A = recStream (xs.map (binary L)) ++ junk) (hAh : σ.sh A = 0) (hCA : σ.val CA = 0) (hWh : σ.sh Wk = 0)
    (hWl : (σ.st Wk).length ≤ 2 * L + 1) (hCW : σ.val CW = 0) (hN : σ.val N = n) (hK2 : σ.val K2 = 0)
    (hcap : (xs.length + 1) * (2 * L + 1) + 2 * n ≤ cap) :
    WXExec cap (getAt A Wk CA CW N K2) σ (σ.sets Wk (frame (binary L xs[n]))) ((n + 1) * (40 * L + 40) + 10 * (n + 1) * (2 * L + 1) + 10) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, not_false_eq_true, List.nodup_nil,
    and_true] at hR
  obtain ⟨⟨hCACW, hCAN, hCAK⟩, ⟨hCWN, hCWK⟩, hNK⟩ := hR
  set ws := xs.map (binary L) with hws
  have hwl : ∀ w ∈ ws, w.length = L := by intro w hw; obtain ⟨x, _, rfl⟩ := List.mem_map.mp hw; simp
  have hwsl : ws.length = xs.length := by simp [hws]
  -- one record copy from `getSt k`
  have hcopy : ∀ k < xs.length, ∀ (τ : WState ns nr), τ.st A = σ.st A → τ.sh A = k * (2 * L + 1) →
      τ.val CA = k * (2 * L + 1) → τ.sh Wk = 0 → (τ.st Wk).length ≤ 2 * L + 1 → τ.val CW = 0 →
      WXExec cap (.wm (copyRec A Wk CA CW)) τ
        (((τ.sets Wk (frame (binary L (xs.getD k 0)))).seth A ((k + 1) * (2 * L + 1))).setv CA
          ((k + 1) * (2 * L + 1))) (40 * L + 22) := by
    intro k hk τ hτA hτAh hτCA hτWh hτWl hτCW
    have hk' : k < ws.length := by rw [hwsl]; exact hk
    obtain ⟨hsplit, hpre⟩ := recStream_split L ws hwl k hk'
    have hwk : ws[k] = binary L (xs.getD k 0) := by rw [List.getD_eq_getElem _ _ hk]; simp [hws]
    rw [hwk] at hsplit
    have h := copyRec_spec cap hAW hCACW τ ((ws.take k).flatMap frame) (binary L (xs.getD k 0))
      ((ws.drop (k + 1)).flatMap frame ++ false :: junk) (by rw [hτA, hA, hsplit]; simp [List.append_assoc])
      (by rw [hpre]; exact hτAh) (by rw [hpre]; exact hτCA) hτWh hτCW (by rw [binary_length]; exact hτWl)
      (by rw [hpre, binary_length]; nlinarith)
    have e : ((ws.take k).flatMap frame).length + 2 * (binary L (xs.getD k 0)).length + 1 =
        (k + 1) * (2 * L + 1) := by
      rw [hpre, binary_length]; ring
    rw [e] at h
    exact WXExec.wm (WExec.mono h (by simp))
  have hst : ∀ k ≤ n, ∀ v1 v2 : ℕ, k < n →
      WXExec cap (.wm (copyRec A Wk CA CW)) (((getSt σ A Wk CA L xs k).setv N v1).setv K2 v2)
        (((getSt σ A Wk CA L xs (k + 1)).setv N v1).setv K2 v2) (40 * L + 22) := by
    intro k _ v1 v2 hk
    have h := hcopy k (by omega) (((getSt σ A Wk CA L xs k).setv N v1).setv K2 v2)
      (by simp [getSt, Function.update_of_ne hAW]) (by simp [getSt]) (by
        simp [getSt, Function.update_of_ne hCAN, Function.update_of_ne hCAK])
      (by simp [getSt, Function.update_of_ne (Ne.symm hAW), hWh])
      (by by_cases hk0 : k = 0
          · simp [getSt, hk0, hWl]
          · simp [getSt, hk0, frame_length])
      (by simp [getSt, Function.update_of_ne hCWN, Function.update_of_ne hCWK, Function.update_of_ne (Ne.symm hCACW),
          hCW])
    refine h.cast cap ?_ le_rfl
    apply WState.eq
    · funext i; by_cases hi : i = A
      · subst hi; simp [getSt]
      · simp [getSt, Function.update_of_ne hi]
    · funext i; by_cases hi : i = Wk
      · subst hi; simp [getSt]
      · simp [getSt, Function.update_of_ne hi]
    · funext r
      simp only [getSt, WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply]
      split_ifs <;> simp_all
    · rfl
  have h0 : getSt σ A Wk CA L xs 0 = σ := by
    apply WState.eq
    · funext i; by_cases hi : i = A
      · subst hi; simp [getSt, hAh]
      · simp [getSt, Function.update_of_ne hi]
    · funext i; by_cases hi : i = Wk
      · subst hi; simp [getSt]
      · simp [getSt, Function.update_of_ne hi]
    · funext r; by_cases hr : r = CA
      · subst hr; simp [getSt, hCA]
      · simp [getSt, Function.update_of_ne hr]
    · rfl
  have hloop := Runs.repE (cap := cap) (body := .wm (copyRec A Wk CA CW)) hNK (40 * L + 22) n
    (getSt σ A Wk CA L xs) (by omega) (fun k => by simp [getSt, Function.update_of_ne (Ne.symm hCAN), h0])
    (fun k => by simp [getSt, Function.update_of_ne (Ne.symm hCAK), h0])
    (fun k hk v1 v2 => hst k hk.le v1 v2 hk) (by rw [h0, hN]) (by rw [h0, hK2])
  rw [h0] at hloop
  -- the record `n` itself
  have hlast := hcopy n hn (getSt σ A Wk CA L xs n) (by simp [getSt, Function.update_of_ne hAW])
    (by simp [getSt]) (by simp [getSt]) (by simp [getSt, Function.update_of_ne (Ne.symm hAW), hWh])
    (by by_cases hn0 : n = 0
        · simp [getSt, hn0, hWl]
        · simp [getSt, hn0, frame_length])
    (by simp [getSt, Function.update_of_ne (Ne.symm hCACW), hCW])
  have hgn : xs.getD n 0 = xs[n] := List.getD_eq_getElem _ _ hn
  rw [hgn] at hlast
  set τ := ((getSt σ A Wk CA L xs n).sets Wk (frame (binary L xs[n]))).seth A ((n + 1) * (2 * L + 1)) |>.setv CA
    ((n + 1) * (2 * L + 1)) with hτ
  have hrw := WXExec.wm (wrewind_spec cap A CA ((n + 1) * (2 * L + 1)) τ (by simp [hτ])
    (by simp [hτ]; nlinarith))
  refine (WXExec.seq hloop (WXExec.seq hlast hrw)).cast cap ?_ (by ring_nf; omega)
  apply WState.eq
  · funext i; by_cases hi : i = A
    · subst hi; simp [hτ, getSt, hAh]
    · simp [hτ, getSt, Function.update_of_ne hi]
  · funext i; by_cases hi : i = Wk
    · subst hi; simp [hτ, getSt]
    · simp [hτ, getSt, Function.update_of_ne hi]
  · funext r; by_cases hr : r = CA
    · subst hr; simp [hτ, getSt, hCA]
    · simp [hτ, getSt, Function.update_of_ne hr]
  · rfl

/-! Programs are opaque to consumers: use the spec theorems. -/
attribute [irreducible] getAt

end NearCubicGates.Close.WordPrograms
