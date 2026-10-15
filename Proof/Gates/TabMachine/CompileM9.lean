import Proof.Gates.TabMachine.CompileM8

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.TabMachine
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicGates.Close.WordPrograms.SInt (encS sval SNumOn)
open StablePartition.Workspace (overlay)

variable {ns nr : ℕ}

theorem size_half (x : ℕ) (h : x ≠ 0) : Nat.size x = Nat.size (x / 2) + 1 := by
  have e := Nat.bit_decide_mod_two_eq_one_shiftRight_one x
  rw [Nat.shiftRight_one] at e
  conv_lhs => rw [← e]
  rw [Nat.size_bit (by rw [e]; exact h)]

theorem div_pow_ne_zero_iff (x k : ℕ) : x / 2 ^ k ≠ 0 ↔ k < Nat.size x := by
  rw [Ne, Nat.div_eq_zero_iff_lt (Nat.pow_pos (by norm_num)), not_lt, ← Nat.lt_size]

theorem min_size_succ (x k : ℕ) :
    min (k + 1) (Nat.size x) = min k (Nat.size x) + if x / 2 ^ k = 0 then 0 else 1 := by
  have := div_pow_ne_zero_iff x k
  split_ifs with h <;> omega

theorem min_size_succ' (x k : ℕ) :
    (min k (Nat.size x) + if x < 2 ^ k then 0 else 1) = min (k + 1) (Nat.size x) := by
  by_cases hx : x < 2 ^ k
  · have := Nat.size_le.mpr hx; simp [hx]; omega
  · have : k < Nat.size x := Nat.lt_size.mpr (by omega); simp [hx]; omega

section Size
variable (S : Fin 24 ↪ Fin (ns + 1)) (R : Fin 24 ↪ Fin nr)

/-- One halving step of the size count. -/
def sizeStep : WMX ns nr :=
  .seq (.wm (SInt.zTestW (S 6) (S 20) (R 2) (R 3)))
    (.ifr (R 2) (WMX.dec (R 2)) (.seq (BinW.half (S 6) (R 3)) (WMX.inc (R 9))))

theorem sizeStep_spec (cap W : ℕ) (σ : WState ns nr) (x : ℕ) (hX : NumOn σ (S 6) (W + 1) x)
    (hZR : NumOn σ (S 20) (W + 1) 0) (hF : σ.val (R 2) = 0) (hR : σ.val (R 3) = 0) (hx : x < 2 ^ (W + 1))
    (hLR : σ.val (R 9) + 1 ≤ cap) (hcap : 2 * (W + 1) + 1 ≤ cap) :
    WXExec cap (sizeStep S R) σ ((σ.sets (S 6) (frame (binary (W + 1) (x / 2)))).setv (R 9)
      (σ.val (R 9) + if x = 0 then 0 else 1)) (80 * W + 140) := by
  have hne : ∀ {a b : Fin 24}, a ≠ b → S a ≠ S b := fun h => emb_ne S h
  have hner : ∀ {a b : Fin 24}, a ≠ b → R a ≠ R b := fun h => emb_ne R h
  have h1 := WXExec.wm (SInt.zTestW_spec cap (W + 1) (hne (show (6 : Fin 24) ≠ 20 by decide))
    (hner (show (2 : Fin 24) ≠ 3 by decide)) σ x 0 hX hZR hF hR hx (by omega))
  by_cases h0 : x = 0
  · have hv : (σ.setv (R 2) (decide (x = 0)).toNat).val (R 2) ≠ 0 := by simp [h0]
    have hd := WXExec.dec cap (R 2) (σ.setv (R 2) (decide (x = 0)).toNat) (by simp [h0]; omega)
    refine (WXExec.seq h1 (WXExec.ifrT hv hd)).mono (by omega) |>.cast cap ?_ le_rfl
    apply WState.eq <;> try rfl
    · funext i; by_cases hi : i = S 6
      · subst hi; simp [h0, hX.1]
      · simp [Function.update_of_ne hi]
    · funext r; by_cases h2 : r = R 2
      · subst h2; simp [h0, hF, Function.update_of_ne (hner (show (2 : Fin 24) ≠ 9 by decide))]
      · by_cases h9 : r = R 9
        · subst h9; simp [h0, Function.update_of_ne (hner (show (9 : Fin 24) ≠ 2 by decide))]
        · simp [Function.update_of_ne h2, Function.update_of_ne h9]
  · have hv : (σ.setv (R 2) (decide (x = 0)).toNat).val (R 2) = 0 := by simp [h0]
    have hh := BinW.half_spec (A := S 6) (R := R 3) cap (W + 1) (σ.setv (R 2) (decide (x = 0)).toNat) x
      (BinW.numOn_setv hX _ _) (by simp [Function.update_of_ne (hner (show (3 : Fin 24) ≠ 2 by decide)), hR]) hx
      (by omega)
    have hi := WXExec.inc cap (R 9) ((σ.setv (R 2) (decide (x = 0)).toNat).sets (S 6) (frame (binary (W + 1) (x / 2))))
      (by simp [Function.update_of_ne (hner (show (9 : Fin 24) ≠ 2 by decide))]; omega)
    refine (WXExec.seq h1 (WXExec.ifrF hv (WXExec.seq hh hi))).mono (by omega) |>.cast cap ?_ le_rfl
    apply WState.eq <;> try rfl
    funext r; by_cases h2 : r = R 2
    · subst h2; simp [h0, hF, Function.update_of_ne (hner (show (2 : Fin 24) ≠ 9 by decide))]
    · by_cases h9 : r = R 9
      · subst h9; simp [h0, Function.update_of_ne (hner (show (9 : Fin 24) ≠ 2 by decide))]
      · simp [Function.update_of_ne h2, Function.update_of_ne h9]

/-- `LR := max 1 (size MM)`. -/
def sizeP : WMX ns nr :=
  .seq (BinW.copy (S 6) (S 22) (R 2) (R 3))
  (.seq (BinW.width (S 20) (R 18) (R 19))
  (.seq (repK (R 18) (R 19) (sizeStep S R))
  (.seq (.wm (WM.clear (R 18))) (.ifr (R 9) WMX.skip (WMX.inc (R 9))))))

theorem sizeP_spec (cap W : ℕ) (σ : WState ns nr) (mm x0 : ℕ) (hMM : NumOn σ (S 22) (W + 1) mm)
    (hX : NumOn σ (S 6) (W + 1) x0) (hZR : NumOn σ (S 20) (W + 1) 0) (hF : σ.val (R 2) = 0) (hR : σ.val (R 3) = 0)
    (hLR : σ.val (R 9) = 0) (hKW : σ.val (R 18) = 0) (hK3 : σ.val (R 19) = 0) (hmm : mm < 2 ^ (W + 1))
    (hcap : 4 * (W + 1) + 4 ≤ cap) :
    WXExec cap (sizeP S R) σ ((σ.sets (S 6) (frame (binary (W + 1) 0))).setv (R 9) (max 1 (Nat.size mm)))
      ((W + 1) * (80 * W + 150) + 300 * W + 400) := by
  have hne : ∀ {a b : Fin 24}, a ≠ b → S a ≠ S b := fun h => emb_ne S h
  have hner : ∀ {a b : Fin 24}, a ≠ b → R a ≠ R b := fun h => emb_ne R h
  have h1 := BinW.copy_spec (A := S 6) (B := S 22) (F := R 2) (R := R 3) cap (W + 1) (hne (by decide))
    (hner (by decide)) σ x0 mm hX hMM hF hR (by omega)
  set σ1 := σ.sets (S 6) (frame (binary (W + 1) mm)) with hσ1
  have h2 := BinW.width_spec (A := S 20) (K := R 18) (T := R 19) cap (hner (by decide)) (W + 1) 0 σ1
    (BinW.numOn_sets_ne hZR (hne (by decide)) _) (by simp [hσ1, hKW]) (by simp [hσ1, hK3]) (by omega)
  set σ2 := σ1.setv (R 18) (W + 1) with hσ2
  have hloop := Runs.repE (cap := cap) (K := R 18) (K2 := R 19) (body := sizeStep S R) (hner (by decide))
    (80 * W + 140) (W + 1)
    (fun k => (σ2.sets (S 6) (frame (binary (W + 1) (mm / 2 ^ k)))).setv (R 9) (min k (Nat.size mm))) (by omega)
    (fun k => by simp [Function.update_of_ne (hner (show (18 : Fin 24) ≠ 9 by decide))])
    (fun k => by simp [Function.update_of_ne (hner (show (19 : Fin 24) ≠ 9 by decide))])
    (fun k hk v1 v2 => by
      have hs := sizeStep_spec S R cap W
        ((((σ2.sets (S 6) (frame (binary (W + 1) (mm / 2 ^ k)))).setv (R 9) (min k (Nat.size mm))).setv (R 18) v1).setv
          (R 19) v2) (mm / 2 ^ k) ⟨by simp, by simp [hσ2, hσ1, hX.2]⟩
        ⟨by simp [hσ2, hσ1, emb_eq_iff, hZR.1], by simp [hσ2, hσ1, hZR.2]⟩
        (by simp [Function.update_apply, emb_eq_iff, hσ2, hσ1, hF])
        (by simp [Function.update_apply, emb_eq_iff, hσ2, hσ1, hR])
        (lt_of_le_of_lt (Nat.div_le_self _ _) hmm)
        (by simp [Function.update_apply, emb_eq_iff]; omega) (by omega)
      refine hs.cast cap ?_ le_rfl
      have e1 : mm / 2 ^ k / 2 = mm / 2 ^ (k + 1) := by rw [Nat.div_div_eq_div_mul, pow_succ]
      have e2 : min k (Nat.size mm) + (if mm / 2 ^ k = 0 then 0 else 1) = min (k + 1) (Nat.size mm) :=
        (min_size_succ mm k).symm
      rw [e1]
      apply WState.eq <;> try rfl
      · funext i; by_cases hi : i = S 6
        · subst hi; simp
        · simp [Function.update_of_ne hi]
      · funext r
        by_cases r9 : r = R 9
        · subst r9; simp [Function.update_of_ne (hner (show (9 : Fin 24) ≠ 18 by decide)),
            Function.update_of_ne (hner (show (9 : Fin 24) ≠ 19 by decide)), e2, min_size_succ']
        · by_cases r18 : r = R 18
          · subst r18; simp [Function.update_of_ne (hner (show (18 : Fin 24) ≠ 19 by decide))]
          · by_cases r19 : r = R 19
            · subst r19; simp
            · simp [Function.update_of_ne r9, Function.update_of_ne r18, Function.update_of_ne r19])
    (by simp [hσ2]) (by simp [hσ2, hσ1, Function.update_of_ne (hner (show (19 : Fin 24) ≠ 18 by decide)), hK3])
  have hst0 : (σ2.sets (S 6) (frame (binary (W + 1) (mm / 2 ^ 0)))).setv (R 9) (min 0 (Nat.size mm)) = σ2 := by
    apply WState.eq <;> try rfl
    · funext i; by_cases hi : i = S 6
      · subst hi; simp [hσ2, hσ1]
      · simp [Function.update_of_ne hi]
    · funext r; by_cases r9 : r = R 9
      · subst r9; simp [hσ2, hσ1, Function.update_of_ne (hner (show (9 : Fin 24) ≠ 18 by decide)), hLR]
      · simp [Function.update_of_ne r9]
  rw [hst0] at hloop
  have hsz : Nat.size mm ≤ W + 1 := Nat.size_le.mpr hmm
  have hdz : mm / 2 ^ (W + 1) = 0 := Nat.div_eq_of_lt hmm
  rw [hdz, Nat.min_eq_right hsz] at hloop
  set σ3 := (σ2.sets (S 6) (frame (binary (W + 1) 0))).setv (R 9) (Nat.size mm) with hσ3
  have hKW3 : σ3.val (R 18) = W + 1 := by
    simp [hσ3, hσ2, Function.update_of_ne (hner (show (18 : Fin 24) ≠ 9 by decide))]
  have h4 := WXExec.wm (wclear_spec (cap := cap) (R 18) (W + 1) σ3 hKW3 (by rw [hKW3]; omega))
  have h5 : WXExec cap (.ifr (R 9) WMX.skip (WMX.inc (R 9))) (σ3.setv (R 18) 0)
      ((σ3.setv (R 18) 0).setv (R 9) (max 1 (Nat.size mm))) 4 := by
    have hv : (σ3.setv (R 18) 0).val (R 9) = Nat.size mm := by
      simp [hσ3, Function.update_of_ne (hner (show (9 : Fin 24) ≠ 18 by decide))]
    by_cases h0 : Nat.size mm = 0
    · have hi := WXExec.inc cap (R 9) (σ3.setv (R 18) 0) (by rw [hv, h0]; omega)
      refine (WXExec.ifrF (by rw [hv, h0]) hi).cast cap ?_ (by omega)
      rw [hv, h0]; simp
    · exact (WXExec.ifrT (by rw [hv]; exact h0) (WXExec.skip cap _)).cast cap
        (BinW.setv_same (by rw [hv]; omega)).symm (by omega)
  refine (WXExec.seq h1 (WXExec.seq h2 (WXExec.seq hloop (WXExec.seq h4 h5)))).cast cap ?_ (by nlinarith)
  apply WState.eq <;> try rfl
  · funext i; by_cases hi : i = S 6
    · subst hi; simp [hσ3]
    · simp [hσ3, hσ2, hσ1, Function.update_of_ne hi]
  · funext r
    by_cases r9 : r = R 9
    · subst r9; simp
    · by_cases r18 : r = R 18
      · subst r18; simp [Function.update_of_ne (hner (show (18 : Fin 24) ≠ 9 by decide)), hKW]
      · simp [hσ3, hσ2, hσ1, Function.update_of_ne r9, Function.update_of_ne r18]

def powP : WMX ns nr :=
  .seq (BinW.one (S 12) (S 20) (R 2) (R 3))
  (.seq (repK (R 9) (R 19) (BinW.shl (S 12) (S 20) (R 2) (R 3)))
  (.seq (BinW.copy (S 13) (S 12) (R 2) (R 3)) (BinW.shl (S 13) (S 20) (R 2) (R 3))))

theorem powP_spec (cap W : ℕ) (σ : WState ns nr) (L p0 p1 : ℕ) (hPW : NumOn σ (S 12) (W + 1) p0)
    (hPW2 : NumOn σ (S 13) (W + 1) p1) (hZR : NumOn σ (S 20) (W + 1) 0) (hF : σ.val (R 2) = 0)
    (hR : σ.val (R 3) = 0) (hLR : σ.val (R 9) = L) (hK3 : σ.val (R 19) = 0) (hL : L + 1 ≤ W)
    (hcap : 2 * (W + 1) + 1 + 2 * L ≤ cap) :
    WXExec cap (powP S R) σ ((σ.sets (S 12) (frame (binary (W + 1) (2 ^ L)))).sets (S 13)
      (frame (binary (W + 1) (2 ^ (L + 1))))) (L * (41 * (W + 1) + 16) + 200 * W + 300) := by
  have hne : ∀ {a b : Fin 24}, a ≠ b → S a ≠ S b := fun h => emb_ne S h
  have hner : ∀ {a b : Fin 24}, a ≠ b → R a ≠ R b := fun h => emb_ne R h
  have h1 := BinW.one_spec (A := S 12) (B := S 20) (F := R 2) (R := R 3) cap (W + 1) (hne (by decide))
    (hner (by decide)) σ p0 0 hPW hZR hF hR (by omega) (by omega)
  set σ1 := σ.sets (S 12) (frame (binary (W + 1) 1)) with hσ1
  have hloop := Runs.repE (cap := cap) (K := R 9) (K2 := R 19) (body := BinW.shl (S 12) (S 20) (R 2) (R 3))
    (hner (by decide)) (41 * (W + 1) + 8) L (fun k => σ.sets (S 12) (frame (binary (W + 1) (2 ^ k)))) (by omega)
    (fun k => by simp) (fun k => by simp)
    (fun k hk v1 v2 => by
      have hs := BinW.shl_spec (A := S 12) (B := S 20) (F := R 2) (R := R 3) cap (W + 1) (hne (by decide))
        (hner (by decide)) (((σ.sets (S 12) (frame (binary (W + 1) (2 ^ k)))).setv (R 9) v1).setv (R 19) v2) (2 ^ k) 0
        ⟨by simp, by simp [hPW.2]⟩ ⟨by simp [emb_eq_iff, hZR.1], by simp [hZR.2]⟩
        (by simp [Function.update_apply, emb_eq_iff, hF]) (by simp [Function.update_apply, emb_eq_iff, hR]) (by omega)
      refine hs.cast cap ?_ le_rfl
      rw [show 2 * 2 ^ k = 2 ^ (k + 1) by ring]
      apply WState.eq <;> try rfl
      funext i; by_cases hi : i = S 12
      · subst hi; simp
      · simp [Function.update_of_ne hi])
    (by simp [hLR]) (by simp [hK3])
  have e0 : σ.sets (S 12) (frame (binary (W + 1) (2 ^ 0))) = σ1 := by simp [hσ1]
  rw [e0] at hloop
  set σ2 := σ.sets (S 12) (frame (binary (W + 1) (2 ^ L))) with hσ2
  have h3 := BinW.copy_spec (A := S 13) (B := S 12) (F := R 2) (R := R 3) cap (W + 1) (hne (by decide))
    (hner (by decide)) σ2 p1 (2 ^ L) (BinW.numOn_sets_ne hPW2 (hne (by decide)) _)
    (BinW.numOn_sets_self _ _ _ _ hPW.2) (by simp [hσ2, hF]) (by simp [hσ2, hR]) (by omega)
  have h4 := BinW.shl_spec (A := S 13) (B := S 20) (F := R 2) (R := R 3) cap (W + 1) (hne (by decide))
    (hner (by decide)) (σ2.sets (S 13) (frame (binary (W + 1) (2 ^ L)))) (2 ^ L) 0
    (BinW.numOn_sets_self _ _ _ _ (by simp [hσ2, hPW2.2]))
    (BinW.numOn_sets_ne (BinW.numOn_sets_ne hZR (hne (by decide)) _) (hne (by decide)) _) (by simp [hσ2, hF])
    (by simp [hσ2, hR]) (by omega)
  refine (WXExec.seq h1 (WXExec.seq hloop (WXExec.seq h3 h4))).cast cap ?_ (by nlinarith)
  rw [show 2 * 2 ^ L = 2 ^ (L + 1) by ring, hσ2, BinW.sets_sets]

end Size

end NearCubicGates.Close.TabMachine
