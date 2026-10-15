import Proof.Gates.WorkerArith.TermA

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.WorkerArith

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat NearCubicWires.RepairOrdinary.Streaming
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP
open NearCubicGates.Close.Interfaces (Counter Call callWord outputWord bitWord ratWord NCircuit)
open NearCubicGates.Close.Codec (rowPrefix)

variable {ns nr : ℕ}

/-- The inverted exact entry: `(F ≠ 0, (1/2 if H = 0 else 0, 0))`. -/
theorem exactEntryNW_spec (cap : ℕ) (o : Fin (ns + 1)) (OP F H : Fin nr) (hOH : OP ≠ H)
    (σ : WState ns nr) (ho : σ.sh o = (σ.st o).length) (hc : σ.val OP + 46 ≤ cap) :
    WXExec cap (exactEntryNW o OP F H) σ
      (appendO σ o OP (marks (bitWord (decide (σ.val F ≠ 0)) ++ outputWord (halfIf (decide (σ.val H = 0)), 0))))
      400 := by
  have hb : WXExec cap (.ifr F (.wm (Codec.emitMarks o OP (bitWord true)))
      (.wm (Codec.emitMarks o OP (bitWord false)))) σ (appendO σ o OP (marks (bitWord (decide (σ.val F ≠ 0))))) 49 := by
    by_cases hF : σ.val F = 0
    · have e := Codec.emitMarks_spec cap o OP (bitWord false) σ ho (by rw [bitWord_len]; omega)
      rw [bitWord_len] at e
      simpa [hF] using (WXExec.ifrF hF (WXExec.wm e)).mono (by omega)
    · have e := Codec.emitMarks_spec cap o OP (bitWord true) σ ho (by rw [bitWord_len]; omega)
      rw [bitWord_len] at e
      simpa [hF] using (WXExec.ifrT hF (WXExec.wm e)).mono (by omega)
  set τ := appendO σ o OP (marks (bitWord (decide (σ.val F ≠ 0)))) with hτ
  have hτo : τ.sh o = (τ.st o).length := by simp [hτ, appendO, ho]
  have hτH : τ.val H = σ.val H := by simp [hτ, appendO, Function.update_of_ne (Ne.symm hOH)]
  have hτc : τ.val OP = σ.val OP + 6 := by
    simp [hτ, appendO, Codec.marks_length, bitWord_len]
  have e2 : WXExec cap (.ifr H (.wm (Codec.emitMarks o OP (outputWord (0, 0))))
      (.wm (Codec.emitMarks o OP (outputWord (1 / 2, 0))))) τ
      (appendO τ o OP (marks (outputWord (halfIf (decide (σ.val H = 0)), 0)))) 330 := by
    by_cases hH : σ.val H = 0
    · have e := Codec.emitMarks_spec cap o OP (outputWord (1 / 2, 0)) τ hτo (by rw [outputWord_half_len]; omega)
      rw [outputWord_half_len] at e
      simpa [hH, halfIf] using (WXExec.ifrF (by rw [hτH]; exact hH) (WXExec.wm e)).mono (by omega)
    · have e := Codec.emitMarks_spec cap o OP (outputWord (0, 0)) τ hτo (by rw [outputWord_zero_len]; omega)
      rw [outputWord_zero_len] at e
      simpa [hH, halfIf] using (WXExec.ifrT (by rw [hτH]; exact hH) (WXExec.wm e)).mono (by omega)
  refine (WXExec.seq hb e2).cast cap ?_ (by omega)
  rw [hτ, appendO_append, Codec.marksApp]

/-- `F := [A ≠ 0] xor [B ≠ 0]`. -/
theorem xorW_spec (cap : ℕ) (A B F : Fin nr) (σ : WState ns nr) (hF : σ.val F = 0)
    (hc : 1 ≤ cap) :
    WExec cap (xorW A B F) σ (σ.setv F (xor (decide (σ.val A ≠ 0)) (decide (σ.val B ≠ 0))).toNat) 5 := by
  have hi := WExec.inc (cap := cap) F σ (by omega)
  rw [hF] at hi
  by_cases hA : σ.val A = 0
  · by_cases hB : σ.val B = 0
    · have e := WExec.ifrF (P := .ifr B .skip (.inc F)) hA (WExec.ifrF (P := .inc F) hB (WExec.skip (cap := cap) σ))
      refine WExec.mono (WExec.cast cap e ?_ le_rfl) (by omega)
      simp [hA, hB, setv_self σ F 0 hF]
    · have e := WExec.ifrF (P := .ifr B .skip (.inc F)) hA (WExec.ifrT (Q := .skip) hB hi)
      refine WExec.cast cap e ?_ (by omega)
      simp [hA, hB]
  · by_cases hB : σ.val B = 0
    · have e := WExec.ifrT (Q := .ifr B (.inc F) .skip) hA (WExec.ifrF (P := .skip) hB hi)
      refine WExec.cast cap e ?_ (by omega)
      simp [hA, hB]
    · have e := WExec.ifrT (Q := .ifr B (.inc F) .skip) hA (WExec.ifrT (Q := .inc F) hB (WExec.skip (cap := cap) σ))
      refine WExec.mono (WExec.cast cap e ?_ le_rfl) (by omega)
      simp [hA, hB, setv_self σ F 0 hF]

/-- The cost of `sysFlagW`. -/
def sysFlagCost (u q Lb rb : ℕ) : ℕ := 100 * (u + q + Lb + 1) + (u + 1) * (rb + 30)

theorem rwC_z (E : TermEnv ns nr) (τ : WState ns nr) (hz : ∀ i : Fin 40, 10 ≤ i.val → i.val ≤ 21 → τ.val (E.R i) = 0) :
    ∀ k : Fin 16, k ≠ 7 → k ≠ 12 → k ≠ 13 → k ≠ 14 → k ≠ 15 → τ.val (rwC E.R k) = 0 := by
  intro k h7 h12 h13 h14 h15
  rw [rwC_apply]
  apply hz <;> fin_cases k <;> simp_all [cIdx]

/-- **`R 37 := [sysList q rows u ≠ []]`** (`u` in `R xi`). -/
theorem sysFlagW_spec (cap : ℕ) (E : TermEnv ns nr) (xi : Fin 40) (hxi : xi = 2 ∨ xi = 5) {q : ℕ}
    (rows : ℕ → List ℕ) (Rn rb : ℕ) (restS : List Bool) (τ : WState ns nr)
    (hsup : τ.st E.SUP = rowPrefix rows Rn ++ restS) (hsuph : τ.sh E.SUP = 0)
    (hsupL : (rowPrefix rows Rn).length ≤ τ.val (E.R 8)) (hq : τ.val (E.R 6) = q)
    (hz : ∀ i : Fin 40, 10 ≤ i.val → i.val < 39 → τ.val (E.R i) = 0) (hu : τ.val (E.R xi) < q + Rn)
    (hrb : ∀ j < Rn, Codec.rowCost (rows j) ≤ rb)
    (hfit : ∀ j < Rn, 2 ^ (natBitLength (rows j).length + 1) ≤ cap ∧ (rows j).length ≤ cap ∧
      ∀ x ∈ rows j, natBitLength x + 1 ≤ cap)
    (hc : τ.val (E.R 8) + q + τ.val (E.R xi) + 1 ≤ cap) :
    WExec cap (sysFlagW E (E.R xi)) τ (τ.setv (E.R 37) (decide (sysList q rows (τ.val (E.R xi)) ≠ [])).toNat)
      (sysFlagCost (τ.val (E.R xi)) q (τ.val (E.R 8)) rb) := by
  set u := τ.val (E.R xi) with hu'
  have hxn : ∀ k : Fin 40, 10 ≤ k.val → xi ≠ k := fun k hk h => by rcases hxi with rfl | rfl <;> subst h <;> simp at hk
  have e1 := Worker.ltSubW_spec (cap := cap) (E.R xi) (E.R 6) (E.R 24) (E.R 34) (E.R 35) (E.R 36)
    (by simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true]
        refine ⟨⟨R_ne E ?_, R_ne E (hxn 24 (by decide)), R_ne E (hxn 34 (by decide)), R_ne E (hxn 35 (by decide)),
          R_ne E (hxn 36 (by decide))⟩, ⟨R_ne E (by decide), R_ne E (by decide), R_ne E (by decide), R_ne E (by decide)⟩,
          ⟨R_ne E (by decide), R_ne E (by decide), R_ne E (by decide)⟩, ⟨R_ne E (by decide), R_ne E (by decide)⟩,
          R_ne E (by decide), fun h => h⟩
        rcases hxi with rfl | rfl <;> decide)
    τ (hz 24 (by decide) (by decide)) (hz 34 (by decide) (by decide)) (hz 35 (by decide) (by decide))
    (hz 36 (by decide) (by decide)) (by omega)
  rw [hq] at e1
  set τ1 := (τ.setv (E.R 24) (u - q)).setv (E.R 34) (q - u) with hτ1
  have v1 : ∀ k : Fin 40, k ≠ 24 → k ≠ 34 → τ1.val (E.R k) = τ.val (E.R k) := fun k h1 h2 => by
    simp [hτ1, Function.update_of_ne (R_ne E h1), Function.update_of_ne (R_ne E h2)]
  have hRne : E.R 24 ≠ E.R 34 := R_ne E (by decide)
  have hfl : sysList q rows u ≠ [] ↔ (u < q ∨ rows (u - q) ≠ []) := by
    unfold sysList; split_ifs with h <;> simp [h]
  by_cases hlt : u < q
  · -- the systematic coordinate: flag 1
    have e2 := WExec.inc (cap := cap) (E.R 37) τ1 (by rw [v1 37 (by decide) (by decide), hz 37 (by decide) (by decide)]; omega)
    rw [v1 37 (by decide) (by decide), hz 37 (by decide) (by decide)] at e2
    have e2' := WExec.ifrT (r := E.R 34) (Q := rowNonemptyW E.SUP (rwC E.R) (E.R 8) (E.R 37))
      (by simp [hτ1]; omega) e2
    set τ2 := τ1.setv (E.R 37) (0 + 1) with hτ2
    have e3 := wclear_spec (cap := cap) (E.R 34) (q - u) τ2
      (by simp [hτ2, Function.update_of_ne (R_ne E (show (34 : Fin 40) ≠ 37 by decide)), hτ1]) (by
        simp [hτ2, Function.update_of_ne (R_ne E (show (34 : Fin 40) ≠ 37 by decide)), hτ1]; omega)
    have e4 := wclear_spec (cap := cap) (E.R 24) (u - q) ((τ2.setv (E.R 34) 0))
      (by simp [hτ2, Function.update_of_ne (R_ne E (show (24 : Fin 40) ≠ 37 by decide)), Function.update_of_ne hRne, hτ1])
      (by simp [hτ2, Function.update_of_ne (R_ne E (show (24 : Fin 40) ≠ 37 by decide)), Function.update_of_ne hRne, hτ1]
          omega)
    refine WExec.cast cap (WExec.seq e1 (WExec.seq e2' (WExec.seq e3 e4))) ?_ ?_
    · refine WState.eq ?h1 ?h2 ?h3 ?h4
      case h1 => rfl
      case h2 => rfl
      case h4 => rfl
      funext r
      have hflag : decide (sysList q rows u ≠ []) = true := by simp [hfl, hlt]
      rw [hflag]
      simp only [WState.setv, hτ2, hτ1]
      by_cases r24 : r = E.R 24
      · subst r24; simp [Function.update_of_ne hRne, Function.update_of_ne (R_ne E (show (24 : Fin 40) ≠ 37 by decide)),
          hz 24 (by decide) (by decide)]
      by_cases r34 : r = E.R 34
      · subst r34; simp [Function.update_of_ne (Ne.symm hRne), Function.update_of_ne (R_ne E (show (34 : Fin 40) ≠ 37 by decide)),
          hz 34 (by decide) (by decide)]
      simp [Function.update_apply, r24, r34]
    · unfold sysFlagCost; have : q - u ≤ q := Nat.sub_le _ _; have : u - q = 0 := by omega
      nlinarith
  · -- a row: the row-nonempty test
    have hge : q ≤ u := by omega
    have hr : u - q < Rn := by omega
    have e2 := rowNonemptyW_spec cap E.SUP (rwC E.R) (E.R 8) (E.R 37)
      (fun k => by rw [rwC_apply]; apply R_ne; fin_cases k <;> decide)
      (fun k => by rw [rwC_apply]; apply R_ne; fin_cases k <;> decide) (R_ne E (by decide)) rows Rn (u - q) hr rb hrb hfit
      (τ.val (E.R 8)) (by omega) restS τ1 (by simp [hτ1, hsup]) (by simp [hτ1, hsuph])
      hsupL
      (rwC_z E τ1 (fun i h1 h2 => by
        rw [v1 i (fun h => by subst h; simp at h2) (fun h => by subst h; simp at h2)]; exact hz i h1 (by omega)))
      (by rw [rwC_apply]; simp [hτ1, Function.update_of_ne hRne, cIdx])
      (v1 8 (by decide) (by decide)) (by rw [v1 37 (by decide) (by decide)]; exact hz 37 (by decide) (by decide))
    have e2' := WExec.ifrF (r := E.R 34) (P := .inc (E.R 37)) (by simp [hτ1]; omega) e2
    set τ2 := (τ1.seth E.SUP 0).setv (E.R 37) (decide (rows (u - q) ≠ [])).toNat with hτ2
    have e3 := wclear_spec (cap := cap) (E.R 34) (q - u) τ2
      (by simp [hτ2, Function.update_of_ne (R_ne E (show (34 : Fin 40) ≠ 37 by decide)), hτ1]) (by
        simp [hτ2, Function.update_of_ne (R_ne E (show (34 : Fin 40) ≠ 37 by decide)), hτ1]; omega)
    have e4 := wclear_spec (cap := cap) (E.R 24) (u - q) ((τ2.setv (E.R 34) 0))
      (by simp [hτ2, Function.update_of_ne (R_ne E (show (24 : Fin 40) ≠ 37 by decide)), Function.update_of_ne hRne, hτ1])
      (by simp [hτ2, Function.update_of_ne (R_ne E (show (24 : Fin 40) ≠ 37 by decide)), Function.update_of_ne hRne, hτ1]
          omega)
    refine WExec.cast cap (WExec.seq e1 (WExec.seq e2' (WExec.seq e3 e4))) ?_ ?_
    · have hflag : decide (sysList q rows u ≠ []) = decide (rows (u - q) ≠ []) := by
        unfold sysList; rw [if_neg hlt]
      rw [hflag]
      refine WState.eq ?k1 ?k2 ?k3 ?k4
      case k2 => rfl
      case k4 => rfl
      · funext i; simp only [WState.setv, WState.seth, hτ2, hτ1]
        by_cases hi : i = E.SUP
        · subst hi; simp [hsuph]
        · simp [Function.update_of_ne hi]
      · funext r
        simp only [WState.setv, WState.seth, hτ2, hτ1]
        by_cases r24 : r = E.R 24
        · subst r24; simp [Function.update_of_ne hRne, Function.update_of_ne (R_ne E (show (24 : Fin 40) ≠ 37 by decide)),
            hz 24 (by decide) (by decide)]
        by_cases r34 : r = E.R 34
        · subst r34; simp [Function.update_of_ne (Ne.symm hRne), Function.update_of_ne (R_ne E (show (34 : Fin 40) ≠ 37 by decide)),
            hz 34 (by decide) (by decide)]
        simp [Function.update_apply, r24, r34]
    · unfold sysFlagCost
      have h1 : (u - q + 1) * (rb + 30) ≤ (u + 1) * (rb + 30) := Nat.mul_le_mul_right _ (by omega)
      have : q - u = 0 := by omega
      nlinarith

end NearCubicGates.Close.WorkerArith
