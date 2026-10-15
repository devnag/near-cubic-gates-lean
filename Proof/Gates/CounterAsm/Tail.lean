import Proof.Gates.CounterAsm.InK

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicGates.Close.CounterAsm

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.CounterMachine
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Interfaces (ratWord outputWord)

variable {ns : ℕ} (cap : ℕ)

/-- `Q 10 := n`, `Q 11 := k`, `rW := n + 1`, `Q 2 := W`, `Q 13 := 2W + 1`. -/
def regs : WMX ns 64 :=
  .seq (addR rN (Q 10) aT) (.seq (addR rK (Q 11) aT) (.seq (addR rN rW aT) (.seq (WMX.inc rW)
  (.seq (addR rW (Q 2) aT) (.seq (addR rW (Q 13) aT) (.seq (addR rW (Q 13) aT) (WMX.inc (Q 13))))))))

theorem regs_run (σ : WState ns 64) (n k : ℕ) (hN : σ.val rN = n) (hK : σ.val rK = k) (h10 : σ.val (Q 10) = 0)
    (h11 : σ.val (Q 11) = 0) (h2 : σ.val (Q 2) = 0) (h13 : σ.val (Q 13) = 0) (hW : σ.val rW = 0)
    (hT : σ.val aT = 0) (hcap : 4 * (n + k) + 10 ≤ cap) :
    ∃ τ : WState ns 64, WXExec cap regs σ τ (100 * (n + k) + 100) ∧ τ.st = σ.st ∧ τ.sh = σ.sh ∧
      τ.val = Function.update (Function.update (Function.update (Function.update (Function.update σ.val (Q 10) n)
        (Q 11) k) rW (n + 1)) (Q 2) (n + 1)) (Q 13) (2 * (n + 1) + 1) := by
  have e1 := addR_spec cap (A := rN) (B := Q 10) (T := aT) (by decide) (by decide) (by decide) σ hT
    (by rw [h10, hN]; omega)
  obtain ⟨s1, hs1⟩ : ∃ s, s = σ.setv (Q 10) n := ⟨_, rfl⟩
  rw [h10, hN, Nat.zero_add, ← hs1] at e1
  have v1 : ∀ r, r ≠ Q 10 → s1.val r = σ.val r := fun r hr => by rw [hs1]; simp [Function.update_apply, hr]
  have e2 := addR_spec cap (A := rK) (B := Q 11) (T := aT) (by decide) (by decide) (by decide) s1
    (by rw [v1 _ (by decide), hT]) (by rw [v1 _ (by decide), v1 _ (by decide), h11, hK]; omega)
  obtain ⟨s2, hs2⟩ : ∃ s, s = s1.setv (Q 11) k := ⟨_, rfl⟩
  rw [v1 _ (by decide), v1 _ (by decide), h11, hK, Nat.zero_add, ← hs2] at e2
  have v2 : ∀ r, r ≠ Q 11 → r ≠ Q 10 → s2.val r = σ.val r := fun r h1 h2 => by
    rw [hs2]; simp [Function.update_apply, h1]; exact v1 r h2
  have e3 := addR_spec cap (A := rN) (B := rW) (T := aT) (by decide) (by decide) (by decide) s2
    (by rw [v2 _ (by decide) (by decide), hT])
    (by rw [v2 _ (by decide) (by decide), v2 _ (by decide) (by decide), hW, hN]; omega)
  obtain ⟨s3, hs3⟩ : ∃ s, s = s2.setv rW n := ⟨_, rfl⟩
  rw [v2 _ (by decide) (by decide), v2 _ (by decide) (by decide), hW, hN, Nat.zero_add, ← hs3] at e3
  have e4 := WXExec.inc (cap := cap) rW s3 (by rw [hs3]; simp; omega)
  obtain ⟨s4, hs4⟩ : ∃ s, s = s2.setv rW (n + 1) := ⟨_, rfl⟩
  have e4' : WXExec cap (WMX.inc rW) s3 s4 3 := by
    refine e4.cast cap ?_ le_rfl; rw [hs4, hs3]; simp [wsetv_setv]
  have v4 : ∀ r, r ≠ rW → r ≠ Q 11 → r ≠ Q 10 → s4.val r = σ.val r := fun r h0 h1 h2 => by
    rw [hs4]; simp [Function.update_apply, h0]; exact v2 r h1 h2
  have w4 : s4.val rW = n + 1 := by rw [hs4]; simp
  have e5 := addR_spec cap (A := rW) (B := Q 2) (T := aT) (by decide) (by decide) (by decide) s4
    (by rw [v4 _ (by decide) (by decide) (by decide), hT])
    (by rw [v4 _ (by decide) (by decide) (by decide), w4, h2]; omega)
  obtain ⟨s5, hs5⟩ : ∃ s, s = s4.setv (Q 2) (n + 1) := ⟨_, rfl⟩
  rw [v4 _ (by decide) (by decide) (by decide), w4, h2, Nat.zero_add, ← hs5] at e5
  have v5 : ∀ r, r ≠ Q 2 → r ≠ rW → r ≠ Q 11 → r ≠ Q 10 → s5.val r = σ.val r := fun r h0 h1 h2 h3 => by
    rw [hs5]; simp [Function.update_apply, h0]; exact v4 r h1 h2 h3
  have w5 : s5.val rW = n + 1 := by rw [hs5]; simp only [WState.setv_val]; rw [Function.update_of_ne (by decide)]; exact w4
  have e6 := addR_spec cap (A := rW) (B := Q 13) (T := aT) (by decide) (by decide) (by decide) s5
    (by rw [v5 _ (by decide) (by decide) (by decide) (by decide), hT])
    (by rw [v5 _ (by decide) (by decide) (by decide) (by decide), w5, h13]; omega)
  obtain ⟨s6, hs6⟩ : ∃ s, s = s5.setv (Q 13) (n + 1) := ⟨_, rfl⟩
  rw [v5 _ (by decide) (by decide) (by decide) (by decide), w5, h13, Nat.zero_add, ← hs6] at e6
  have w6 : s6.val rW = n + 1 := by rw [hs6]; simp only [WState.setv_val]; rw [Function.update_of_ne (by decide)]; exact w5
  have t6 : s6.val aT = 0 := by
    rw [hs6]; simp only [WState.setv_val]; rw [Function.update_of_ne (by decide)]
    rw [v5 _ (by decide) (by decide) (by decide) (by decide), hT]
  have e7 := addR_spec cap (A := rW) (B := Q 13) (T := aT) (by decide) (by decide) (by decide) s6 t6
    (by rw [w6, hs6]; simp; omega)
  obtain ⟨s7, hs7⟩ : ∃ s, s = s5.setv (Q 13) (2 * (n + 1)) := ⟨_, rfl⟩
  have e7' : WXExec cap (addR rW (Q 13) aT) s6 s7 (18 * (n + 1) + 3) := by
    rw [w6] at e7; refine e7.cast cap ?_ le_rfl; rw [hs7, hs6]; simp [wsetv_setv]; ring_nf
  have e8 := WXExec.inc (cap := cap) (Q 13) s7 (by rw [hs7]; simp; omega)
  obtain ⟨s8, hs8⟩ : ∃ s, s = s5.setv (Q 13) (2 * (n + 1) + 1) := ⟨_, rfl⟩
  have e8' : WXExec cap (WMX.inc (Q 13)) s7 s8 3 := by
    refine e8.cast cap ?_ le_rfl; rw [hs8, hs7]; simp [wsetv_setv]
  refine ⟨s8, ?_, ?_, ?_, ?_⟩
  · refine WXExec.mono (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4' (WXExec.seq e5
      (WXExec.seq e6 (WXExec.seq e7' e8'))))))) ?_
    nlinarith
  · rw [hs8, hs5, hs4, hs2, hs1]; rfl
  · rw [hs8, hs5, hs4, hs2, hs1]; rfl
  · rw [hs8, hs5, hs4, hs2, hs1]; simp only [WState.setv_val]

/-! ## Zero numbers and the ruler -/

/-- Five `W`-bit zero numbers (`P 1, P 2, P 3, P 6, P 7`) and the ruler `0 1^W` (`P 5`). -/
def nums (P : Fin 12 ↪ Fin (ns + 1)) : WMX ns 64 :=
  .seq (zeroNum (P 1)) (.seq (zeroNum (P 2)) (.seq (zeroNum (P 3)) (.seq (zeroNum (P 6)) (.seq (zeroNum (P 7))
    (rulerW (P 5))))))

theorem nums_run (P : Fin 12 ↪ Fin (ns + 1)) (W : ℕ) (σ : WState ns 64)
    (hP : ∀ i : Fin 12, i ∈ ([1, 2, 3, 5, 6, 7] : List (Fin 12)) → σ.st (P i) = [] ∧ σ.sh (P i) = 0)
    (hW : σ.val rW = W) (hC : σ.val aC = 0) (hT : σ.val aT = 0) (hO : σ.val opZ = 0) (hcap : 4 * W + 4 ≤ cap) :
    WXExec cap (nums P) σ ((((((σ.sets (P 1) (frame (binary W 0))).sets (P 2) (frame (binary W 0))).sets (P 3)
      (frame (binary W 0))).sets (P 6) (frame (binary W 0))).sets (P 7) (frame (binary W 0))).sets (P 5)
      (false :: List.replicate W true)) (400 * W + 300) := by
  have pne : ∀ {a b : Fin 12}, a ≠ b → P a ≠ P b := fun h => P.injective.ne h
  have g := fun (i : Fin 12) (hi : i ∈ ([1, 2, 3, 5, 6, 7] : List (Fin 12))) => hP i hi
  have e1 := zeroNum_spec cap (P 1) W σ (g 1 (by decide)).1 (g 1 (by decide)).2 hW hC hT hO hcap
  obtain ⟨z, hz⟩ : ∃ z, z = frame (binary W 0) := ⟨_, rfl⟩
  rw [← hz] at e1 ⊢
  have e2 := zeroNum_spec cap (P 2) W (σ.sets (P 1) z) (by simp [Function.update_apply, pne (show (2 : Fin 12) ≠ 1 by decide),
    (g 2 (by decide)).1]) (by simp [(g 2 (by decide)).2]) hW hC hT hO hcap
  rw [← hz] at e2
  have e3 := zeroNum_spec cap (P 3) W ((σ.sets (P 1) z).sets (P 2) z) (by simp [Function.update_apply,
    pne (show (3 : Fin 12) ≠ 1 by decide), pne (show (3 : Fin 12) ≠ 2 by decide), (g 3 (by decide)).1])
    (by simp [(g 3 (by decide)).2]) hW hC hT hO hcap
  rw [← hz] at e3
  have e4 := zeroNum_spec cap (P 6) W (((σ.sets (P 1) z).sets (P 2) z).sets (P 3) z) (by simp [Function.update_apply,
    pne (show (6 : Fin 12) ≠ 1 by decide), pne (show (6 : Fin 12) ≠ 2 by decide),
    pne (show (6 : Fin 12) ≠ 3 by decide), (g 6 (by decide)).1]) (by simp [(g 6 (by decide)).2]) hW hC hT hO hcap
  rw [← hz] at e4
  have e5 := zeroNum_spec cap (P 7) W ((((σ.sets (P 1) z).sets (P 2) z).sets (P 3) z).sets (P 6) z)
    (by simp [Function.update_apply, pne (show (7 : Fin 12) ≠ 1 by decide),
    pne (show (7 : Fin 12) ≠ 2 by decide), pne (show (7 : Fin 12) ≠ 3 by decide),
    pne (show (7 : Fin 12) ≠ 6 by decide), (g 7 (by decide)).1])
    (by simp [(g 7 (by decide)).2]) hW hC hT hO hcap
  rw [← hz] at e5
  have e6 := ruler_spec cap (P 5) W (((((σ.sets (P 1) z).sets (P 2) z).sets (P 3) z).sets (P 6) z).sets (P 7) z)
    (by simp [Function.update_apply, pne (show (5 : Fin 12) ≠ 1 by decide),
    pne (show (5 : Fin 12) ≠ 2 by decide), pne (show (5 : Fin 12) ≠ 3 by decide),
    pne (show (5 : Fin 12) ≠ 6 by decide), pne (show (5 : Fin 12) ≠ 7 by decide), (g 5 (by decide)).1])
    (by simp [(g 5 (by decide)).2]) hW hC hT hO hcap
  exact WXExec.mono (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4 (WXExec.seq e5 e6))))) (by omega)

/-! ## The tail -/

def tail (cT : ℕ) (P : Fin 12 ↪ Fin (ns + 1)) : WMX ns 64 :=
  .seq (kArith cT) (.seq regs (.seq (nums P) (ivlP P Q)))

/-- The tail's cost class. -/
def tailCost (cT n : ℕ) : ℕ := 10000 * (n + kOf cT n + cT + 10) ^ 2

theorem tail_run (cT n S U : ℕ) (P : Fin 12 ↪ Fin (ns + 1)) (σ : WState ns 64) (hN : σ.val rN = n)
    (hz : ∀ r, r ≠ rN → r ≠ scW → σ.val r = 0) (hP4 : σ.st (P 4) = ratWord (S : ℚ) ++ natWord U)
    (hP4h : σ.sh (P 4) = 0)
    (hP : ∀ i : Fin 12, i ∈ ([0, 1, 2, 3, 5, 6, 7] : List (Fin 12)) → σ.st (P i) = [] ∧ σ.sh (P i) = 0)
    (hfit : S + 2 ^ (kOf cT n - 1) * U < 2 ^ (n + 1)) (hcap : 100 * (n + kOf cT n + cT + 10) ^ 2 ≤ cap) :
    ∃ τ : WState ns 64, WXExec cap (tail cT P) σ τ (tailCost cT n) ∧
      τ.st (P 0) = outputWord (ivl S U (kOf cT n) n) := by
  have pne : ∀ {a b : Fin 12}, a ≠ b → P a ≠ P b := fun h => P.injective.ne h
  obtain ⟨k, hk⟩ : ∃ k, k = kOf cT n := ⟨_, rfl⟩
  rw [← hk] at hfit hcap ⊢
  have hsq : n + k + cT + 10 ≤ (n + k + cT + 10) ^ 2 := Nat.le_self_pow (by norm_num) _
  -- k
  have e1 := kArith_spec cap cT n σ hN (hz _ (by decide) (by decide)) (hz _ (by decide) (by decide))
    (hz _ (by decide) (by decide)) (hz _ (by decide) (by decide)) (hz _ (by decide) (by decide))
    (hz _ (by decide) (by decide)) (hz _ (by decide) (by decide)) (hz _ (by decide) (by decide))
    (hz _ (by decide) (by decide)) (by nlinarith)
  rw [← hk] at e1
  obtain ⟨s1, hs1⟩ : ∃ s, s = (((σ.setv aL (lamOf n)).setv aM (muOf n)).setv aA (3 * muOf n + cT + 2)).setv rK k :=
    ⟨_, rfl⟩
  rw [← hs1] at e1
  have v1 : ∀ r, r ≠ aL → r ≠ aM → r ≠ aA → r ≠ rK → s1.val r = σ.val r := fun r h1 h2 h3 h4 => by
    rw [hs1]; simp [Function.update_apply, h1, h2, h3, h4]

  have z1 : ∀ r, r ≠ aL → r ≠ aM → r ≠ aA → r ≠ rK → r ≠ rN → r ≠ scW → s1.val r = 0 :=
    fun r h1 h2 h3 h4 h5 h6 => by rw [v1 r h1 h2 h3 h4]; exact hz r h5 h6
  have n1 : s1.val rN = n := by rw [v1 _ (by decide) (by decide) (by decide) (by decide)]; exact hN
  have k1 : s1.val rK = k := by rw [hs1]; simp
  obtain ⟨s2, e2, s2st, s2sh, s2val⟩ := regs_run cap s1 n k n1 k1
    (z1 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (z1 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (z1 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (z1 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (z1 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (z1 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by nlinarith)
  have v2 : ∀ r, r ≠ Q 10 → r ≠ Q 11 → r ≠ rW → r ≠ Q 2 → r ≠ Q 13 → s2.val r = s1.val r :=
    fun r h1 h2 h3 h4 h5 => by rw [s2val]; simp [Function.update_apply, h1, h2, h3, h4, h5]
  -- numbers and ruler
  have hs2P : ∀ i : Fin 12, i ∈ ([0, 1, 2, 3, 5, 6, 7] : List (Fin 12)) → s2.st (P i) = [] ∧ s2.sh (P i) = 0 := by
    intro i hi; rw [s2st, s2sh, hs1]; exact hP i hi
  have e3 := nums_run cap P (n + 1) s2 (fun i hi => hs2P i (by simp at hi ⊢; omega))
    (by rw [s2val]; simp (config := { decide := true }) [Function.update_apply])
    (by rw [v2 _ (by decide) (by decide) (by decide) (by decide) (by decide),
      v1 _ (by decide) (by decide) (by decide) (by decide)]; exact hz _ (by decide) (by decide))
    (by rw [v2 _ (by decide) (by decide) (by decide) (by decide) (by decide),
      v1 _ (by decide) (by decide) (by decide) (by decide)]; exact hz _ (by decide) (by decide))
    (by rw [v2 _ (by decide) (by decide) (by decide) (by decide) (by decide),
      v1 _ (by decide) (by decide) (by decide) (by decide)]; exact hz _ (by decide) (by decide))
    (by nlinarith)
  obtain ⟨s3, hs3⟩ : ∃ s, s = (((((s2.sets (P 1) (frame (binary (n + 1) 0))).sets (P 2) (frame (binary (n + 1) 0))).sets
      (P 3) (frame (binary (n + 1) 0))).sets (P 6) (frame (binary (n + 1) 0))).sets (P 7)
      (frame (binary (n + 1) 0))).sets (P 5) (false :: List.replicate (n + 1) true) := ⟨_, rfl⟩
  rw [← hs3] at e3
  have s3val : s3.val = s2.val := by rw [hs3]; rfl
  have s3sh : s3.sh = s2.sh := by rw [hs3]; rfl
  have zst : ∀ i : Fin 12, i ∈ ([1, 2, 3, 6, 7] : List (Fin 12)) → s3.st (P i) = frame (binary (n + 1) 0) := by
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rw [hs3]
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      simp [Function.update_apply, pne (show (1 : Fin 12) ≠ 2 by decide), pne (show (1 : Fin 12) ≠ 3 by decide),
        pne (show (1 : Fin 12) ≠ 5 by decide), pne (show (1 : Fin 12) ≠ 6 by decide),
        pne (show (1 : Fin 12) ≠ 7 by decide), pne (show (2 : Fin 12) ≠ 3 by decide),
        pne (show (2 : Fin 12) ≠ 5 by decide), pne (show (2 : Fin 12) ≠ 6 by decide),
        pne (show (2 : Fin 12) ≠ 7 by decide), pne (show (3 : Fin 12) ≠ 5 by decide),
        pne (show (3 : Fin 12) ≠ 6 by decide), pne (show (3 : Fin 12) ≠ 7 by decide),
        pne (show (6 : Fin 12) ≠ 5 by decide), pne (show (6 : Fin 12) ≠ 7 by decide),
        pne (show (7 : Fin 12) ≠ 5 by decide)]
  have zsh : ∀ i : Fin 12, i ∈ ([0, 1, 2, 3, 5, 6, 7] : List (Fin 12)) → s3.sh (P i) = 0 := by
    intro i hi; rw [s3sh]; exact (hs2P i hi).2
  have hW1 : 1 ≤ n + 1 := by omega
  have pre : IvlPre P Q cap (n + 1) (n + 1) S U k n [] s3 := by
    refine ⟨hW1, le_rfl, hfit, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ⟨zst 1 (by decide), zsh 1 (by decide)⟩,
      ⟨zst 2 (by decide), zsh 2 (by decide)⟩, ⟨zst 3 (by decide), zsh 3 (by decide)⟩,
      ⟨zst 6 (by decide), zsh 6 (by decide)⟩, ⟨zst 7 (by decide), zsh 7 (by decide)⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_⟩
    · rw [hs3]; simp [Function.update_apply, pne (show (4 : Fin 12) ≠ 1 by decide),
        pne (show (4 : Fin 12) ≠ 2 by decide), pne (show (4 : Fin 12) ≠ 3 by decide),
        pne (show (4 : Fin 12) ≠ 5 by decide), pne (show (4 : Fin 12) ≠ 6 by decide),
        pne (show (4 : Fin 12) ≠ 7 by decide)]
      rw [s2st, hs1]; simpa using hP4
    · rw [s3sh, s2sh, hs1]; exact hP4h
    · rw [hs3]; simp
    · exact zsh 5 (by decide)
    · rw [hs3]; simp [Function.update_apply, pne (show (0 : Fin 12) ≠ 1 by decide),
        pne (show (0 : Fin 12) ≠ 2 by decide), pne (show (0 : Fin 12) ≠ 3 by decide),
        pne (show (0 : Fin 12) ≠ 5 by decide), pne (show (0 : Fin 12) ≠ 6 by decide),
        pne (show (0 : Fin 12) ≠ 7 by decide)]
      exact (hs2P 0 (by decide)).1
    · exact zsh 0 (by decide)
    · refine ⟨?_, fun r hr => ?_⟩
      · rw [s3val, s2val]; simp [q10_apply]
      · rw [s3val, q10_apply]
        have hr' : (Fin.castLE (by norm_num) r : Fin 20) ≠ 2 := by
          intro h; apply hr; apply Fin.ext; have := congrArg Fin.val h; simpa using this
        have hv : (r : ℕ) < 10 := r.isLt
        rw [v2 _ (fun h => by have := congrArg Fin.val h; simp at this; omega)
          (fun h => by have := congrArg Fin.val h; simp at this; omega)
          (fun h => by have := congrArg Fin.val h; simp [rW] at this; omega)
          (fun h => by apply hr'; exact Q.injective h)
          (fun h => by have := congrArg Fin.val h; simp at this; omega),
          v1 _ (fun h => by have := congrArg Fin.val h; simp [aL] at this; omega)
          (fun h => by have := congrArg Fin.val h; simp [aM] at this; omega)
          (fun h => by have := congrArg Fin.val h; simp [aA] at this; omega)
          (fun h => by have := congrArg Fin.val h; simp [rK] at this; omega)]
        exact hz _ (fun h => by have := congrArg Fin.val h; simp [rN] at this; omega)
          (fun h => by have := congrArg Fin.val h; simp [scW] at this; omega)
    · rw [s3val, s2val]; simp (config := { decide := true }) [Function.update_apply]
    · rw [s3val, s2val]; simp (config := { decide := true }) [Function.update_apply]
    · rw [s3val, v2 _ (by decide) (by decide) (by decide) (by decide) (by decide),
        v1 _ (by decide) (by decide) (by decide) (by decide)]; exact hz _ (by decide) (by decide)
    · rw [s3val, s2val]; simp (config := { decide := true }) [Function.update_apply]
    all_goals first
      | (rw [s3val, v2 _ (by decide) (by decide) (by decide) (by decide) (by decide),
          v1 _ (by decide) (by decide) (by decide) (by decide)]; exact hz _ (by decide) (by decide))
      | nlinarith
  obtain ⟨s4, c4, e4, hc4, hout, -⟩ := ivlP_run P Q cap (n + 1) (n + 1) S U k n [] s3 pre
  refine ⟨s4, WXExec.mono (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 e4))) ?_, hout⟩
  have hb : ivlBound (n + 1) k n ≤ 8000 * (n + k + cT + 10) ^ 2 := by
    unfold ivlBound
    have h2 : (n + 1 + k + n + 1) ^ 2 ≤ (2 * (n + k + cT + 10)) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    nlinarith
  unfold tailCost; rw [← hk]; nlinarith

end NearCubicGates.Close.CounterAsm
