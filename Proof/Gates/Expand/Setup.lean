import Proof.Gates.Expand.Pass

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.Expand

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicGates.Close.WordPrograms.BinW (numOn_sets_ne numOn_sets_self numOn_setv)

variable {ns nr : ℕ}

theorem writeTapeBit_mid : ∀ (p q : List Bool) (b : Bool), writeTapeBit (p ++ q) p.length b = p ++ b :: q.drop 1
  | [], [], b => rfl
  | [], _ :: q, b => rfl
  | a :: p, q, b => by
    show a :: writeTapeBit (p ++ q) p.length b = a :: (p ++ b :: q.drop 1)
    rw [writeTapeBit_mid p q b]

/-- `[true, false]` repeated: the marks of `j` zero bits. -/
def zpfx (j : ℕ) : List Bool := (List.replicate j [true, false]).flatten

theorem zpfx_length (j : ℕ) : (zpfx j).length = 2 * j := by
  induction j with
  | zero => rfl
  | succ j ih => simp [zpfx, List.replicate_succ', List.flatten_append] at ih ⊢; omega

theorem zpfx_succ (j : ℕ) : zpfx (j + 1) = zpfx j ++ [true, false] := by
  simp [zpfx, List.replicate_succ', List.flatten_append]

theorem frame_binary_zero (k : ℕ) : frame (binary k 0) = zpfx k ++ [false] := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have : binary (k + 1) 0 = false :: binary k 0 := by simp [binary]
    rw [this, frame, ih]
    simp [zpfx, List.replicate_succ]

section Init
variable (X : Fin (ns + 1)) (K K2 : Fin nr)

def initNum : WMX ns nr :=
  .seq (repK K K2 (.seq (WMX.wr X true) (.seq (WMX.fwd X) (.seq (WMX.wr X false) (WMX.fwd X)))))
    (.seq (WMX.wr X false) (repK K K2 (.seq (WMX.bwd X) (WMX.bwd X))))

def initCost (k : ℕ) : ℕ := (k * (7 + 8) + 7 * k + 3) + 1 + (1 + 1 + (k * (3 + 8) + 7 * k + 3))

variable {X K K2}

theorem initNum_spec (cap : ℕ) (hK : K ≠ K2) (σ : WState ns nr) (k : ℕ) (hlen : (σ.st X).length ≤ 2 * k + 1)
    (hXh : σ.sh X = 0) (hKv : σ.val K = k) (hK2 : σ.val K2 = 0) (hcap : 2 * k ≤ cap) :
    WXExec cap (initNum X K K2) σ (σ.sets X (frame (binary k 0))) (initCost k) := by
  set old := σ.st X with hold
  have h1 := Runs.repE (cap := cap) (body := .seq (WMX.wr X true) (.seq (WMX.fwd X) (.seq (WMX.wr X false)
    (WMX.fwd X)))) hK 7 k (fun j => (σ.sets X (zpfx j ++ old.drop (2 * j))).seth X (2 * j)) hcap
    (fun j => by simp) (fun j => by simp)
    (fun j _ v1 v2 => by
      set τ := (((σ.sets X (zpfx j ++ old.drop (2 * j))).seth X (2 * j)).setv K v1).setv K2 v2 with hτ
      have e1 := WXExec.wr cap X true τ
      have hp1 : writeTapeBit (τ.st X) (τ.sh X) true = zpfx j ++ true :: (old.drop (2 * j)).drop 1 := by
        rw [hτ]; simp only [WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh,
          Function.update_self]
        rw [← zpfx_length j, writeTapeBit_mid]
      rw [hp1] at e1
      set τ1 := τ.sets X (zpfx j ++ true :: (old.drop (2 * j)).drop 1) with hτ1
      have e2 := WXExec.fwd cap X τ1
      set τ2 := τ1.seth X (τ1.sh X + 1) with hτ2
      have e3 := WXExec.wr cap X false τ2
      have hp3 : writeTapeBit (τ2.st X) (τ2.sh X) false =
          zpfx (j + 1) ++ (old.drop (2 * (j + 1))) := by
        rw [hτ2, hτ1, hτ]
        simp only [WState.seth_st, WState.sets_st, WState.setv_st, WState.seth_sh, WState.sets_sh, WState.setv_sh,
          Function.update_self]
        have : 2 * j + 1 = (zpfx j ++ [true]).length := by simp [zpfx_length]
        rw [this, show zpfx j ++ true :: (old.drop (2 * j)).drop 1 = (zpfx j ++ [true]) ++ (old.drop (2 * j)).drop 1
          by simp, writeTapeBit_mid, zpfx_succ]
        simp only [List.drop_drop, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append]
        rw [show 2 * j + 1 + 1 = 2 * (j + 1) by ring]
      rw [hp3] at e3
      have e4 := WXExec.fwd cap X (τ2.sets X (zpfx (j + 1) ++ old.drop (2 * (j + 1))))
      refine (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 e4))).cast cap ?_ (by omega)
      apply WState.eq
      · funext i; by_cases hi : i = X
        · subst hi; simp [hτ2, hτ1, hτ]; ring
        · simp [hτ2, hτ1, hτ, Function.update_of_ne hi]
      · funext i; by_cases hi : i = X
        · subst hi; simp [hτ2, hτ1, hτ]
        · simp [hτ2, hτ1, hτ, Function.update_of_ne hi]
      · simp [hτ2, hτ1, hτ]
      · simp [hτ2, hτ1, hτ]) (by simp [hKv]) (by simp [hK2])
  have e0 : (σ.sets X (zpfx 0 ++ old.drop (2 * 0))).seth X (2 * 0) = σ := by
    apply WState.eq
    · funext i; by_cases hi : i = X
      · subst hi; simp [hXh]
      · simp [Function.update_of_ne hi]
    · funext i; by_cases hi : i = X
      · subst hi; simp [zpfx, hold]
      · simp [Function.update_of_ne hi]
    · rfl
    · rfl
  rw [e0] at h1
  -- the final `false`
  set ρ := (σ.sets X (zpfx k ++ old.drop (2 * k))).seth X (2 * k) with hρ
  have hw := WXExec.wr cap X false ρ
  have hfin : writeTapeBit (ρ.st X) (ρ.sh X) false = frame (binary k 0) := by
    rw [hρ]; simp only [WState.seth_st, WState.sets_st, WState.seth_sh, Function.update_self]
    rw [← zpfx_length k, writeTapeBit_mid, frame_binary_zero]
    have : (old.drop (zpfx k).length).drop 1 = [] := by
      rw [List.drop_drop, zpfx_length]; exact List.drop_eq_nil_of_le (by omega)
    rw [this]
  rw [hfin] at hw
  -- back to the start
  have h2 := Runs.repE (cap := cap) (body := .seq (WMX.bwd X) (WMX.bwd X)) hK 3 k
    (fun j => (σ.sets X (frame (binary k 0))).seth X (2 * k - 2 * j)) hcap (fun j => by simp) (fun j => by simp)
    (fun j _ v1 v2 => by
      refine (WXExec.seq (WXExec.bwd cap X _) (WXExec.bwd cap X _)).cast cap ?_ (by omega)
      apply WState.eq
      · funext i; by_cases hi : i = X
        · subst hi; simp; omega
        · simp [Function.update_of_ne hi]
      · rfl
      · rfl
      · rfl) (by simp [hKv]) (by simp [hK2])
  have e5 : (σ.sets X (frame (binary k 0))).seth X (2 * k - 2 * 0) = ρ.sets X (frame (binary k 0)) := by
    apply WState.eq
    · funext i; by_cases hi : i = X
      · subst hi; simp [hρ]
      · simp [hρ, Function.update_of_ne hi]
    · funext i; by_cases hi : i = X
      · subst hi; simp [hρ]
      · simp [hρ, Function.update_of_ne hi]
    · rfl
    · rfl
  have e6 : (σ.sets X (frame (binary k 0))).seth X (2 * k - 2 * k) = σ.sets X (frame (binary k 0)) := by
    apply WState.eq
    · funext i; by_cases hi : i = X
      · subst hi; simp [hXh]
      · simp [Function.update_of_ne hi]
    · rfl
    · rfl
    · rfl
  rw [e5, e6] at h2
  exact (WXExec.seq h1 (WXExec.seq hw h2)).mono (by unfold initCost; omega)

end Init

end NearCubicGates.Close.Expand
