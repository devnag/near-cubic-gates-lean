import Proof.Gates.WordPrograms.SInt
import Proof.Gates.WordPrograms.BinWDiv

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicGates.Close.Solve

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicGates.Close.WordPrograms.SInt

variable {ns nr : ℕ}

theorem tdiv_sval (x y : ℤ) : x.tdiv y = sval (x.natAbs / y.natAbs) (decide (x < 0) ^^ decide (y < 0)) := by
  obtain ⟨a, rfl | rfl⟩ := Int.eq_nat_or_neg x <;> obtain ⟨b, rfl | rfl⟩ := Int.eq_nat_or_neg y
  · have h1 : ¬ ((a : ℤ) < 0) := by omega
    have h2 : ¬ ((b : ℤ) < 0) := by omega
    simp [sval, h1, h2]
  · have h1 : ¬ ((a : ℤ) < 0) := by omega
    rw [Int.tdiv_neg]
    rcases Nat.eq_zero_or_pos b with hb | hb
    · subst hb; simp [sval]
    · have h2 : (-(b : ℤ)) < 0 := by omega
      simp [sval, h1, h2, hb.ne']
  · have h2 : ¬ ((b : ℤ) < 0) := by omega
    rw [Int.neg_tdiv]
    rcases Nat.eq_zero_or_pos a with ha | ha
    · subst ha; simp [sval]
    · have h1 : (-(a : ℤ)) < 0 := by omega
      simp [sval, h1, h2, ha.ne']
  · rw [Int.neg_tdiv, Int.tdiv_neg, neg_neg]
    rcases Nat.eq_zero_or_pos a with ha | ha
    · subst ha; simp [sval]
    rcases Nat.eq_zero_or_pos b with hb | hb
    · subst hb; simp [sval]
    have h1 : (-(a : ℤ)) < 0 := by omega
    have h2 : (-(b : ℤ)) < 0 := by omega
    simp [sval, h1, h2, ha.ne', hb.ne', ha, hb]

def sdiv (X Y M N Q Rm E : Fin (ns + 1)) (S T F R K T2 : Fin nr) : WMX ns nr :=
  .seq (split X M S F R) (.seq (split Y N T F R)
    (.seq (BinW.divmod M N Q Rm E F R K T2)
      (.seq (.ifr T (.seq (WMX.dec T) (flip S)) WMX.skip) (join Q X S F R))))

/-- The cost bound of `sdiv`. -/
def sdivCost (W : ℕ) : ℕ := 400 * (W + 2) ^ 2 + 300 * W + 600

section Div
variable (cap W : ℕ) {X Y M N Q Rm E : Fin (ns + 1)} {S T F R K T2 : Fin nr}

theorem sdiv_spec (hS7 : [X, Y, M, N, Q, Rm, E].Nodup) (hR6 : [S, T, F, R, K, T2].Nodup) (σ : WState ns nr)
    (x y : ℤ) (m0 n0 q0 r0 e0 : ℕ) (hX : SNumOn σ X W x) (hY : SNumOn σ Y W y) (hM : NumOn σ M (W + 1) m0)
    (hN : NumOn σ N (W + 1) n0) (hQ : NumOn σ Q (W + 1) q0) (hRm : NumOn σ Rm (W + 1) r0)
    (hE : NumOn σ E (W + 1) e0) (hS : σ.val S = 0) (hT : σ.val T = 0) (hF : σ.val F = 0) (hR : σ.val R = 0)
    (hK : σ.val K = 0) (hT2 : σ.val T2 = 0) (hy : y ≠ 0) (hcap : 2 * (W + 1) + 1 ≤ cap) :
    Runs cap (sdiv X Y M N Q Rm E S T F R K T2) σ (sdivCost W)
      (fun τ => SNumOn τ X W (x.tdiv y) ∧ (∃ a, NumOn τ M (W + 1) a) ∧ (∃ b, NumOn τ N (W + 1) b) ∧
        (∃ c, NumOn τ Q (W + 1) c) ∧ (∃ d, NumOn τ Rm (W + 1) d) ∧ (∃ e, NumOn τ E (W + 1) e) ∧
        SameExcept σ τ [X, M, N, Q, Rm, E] []) := by
  have hS7' := hS7
  have hR6' := hR6
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, not_false_eq_true, List.nodup_nil,
    and_true] at hS7' hR6'
  obtain ⟨⟨hXY, hXM, hXN, hXQ, hXR, hXE⟩, ⟨hYM, hYN, hYQ, hYR, hYE⟩, ⟨hMN, hMQ, hMR, hME⟩, ⟨hNQ, hNR, hNE⟩,
    ⟨hQR, hQE⟩, hRE⟩ := hS7'
  obtain ⟨⟨hST, hSF, hSR, hSK, hST2⟩, ⟨hTF, hTR, hTK, hTT2⟩, ⟨hFR, hFK, hFT2⟩, ⟨hRK, hRT2⟩, hKT2⟩ := hR6'
  have hS4 : [X, Y, M, N].Nodup := by simp [hXY, hXM, hXN, hYM, hYN, hMN]
  have hR4 : [S, T, F, R].Nodup := by simp [hST, hSF, hSR, hTF, hTR, hFR]
  have hxW : x.natAbs < 2 ^ W := hX.2
  have hyW : y.natAbs < 2 ^ W := hY.2
  have hpow : 2 ^ (W + 1) = 2 * 2 ^ W := by rw [pow_succ]; ring
  refine (split2 cap W hS4 hR4 σ x y m0 n0 hX hY hM hN hS hT hF hR hcap _
    (BinW.divCost (W + 1) + 1 + (7 + 1 + (130 * W + 160))) _ (fun τ hXτ _ hMτ hNτ hSτ hTτ hFτ hRτ hfr => ?_)).cost (by
      unfold sdivCost; have := BinW.divCost_le (W + 1); nlinarith)
  have hQτ : NumOn τ Q (W + 1) q0 := hfr.numOn (by simp [Ne.symm hMQ, Ne.symm hNQ]) hQ
  have hRτ' : NumOn τ Rm (W + 1) r0 := hfr.numOn (by simp [Ne.symm hMR, Ne.symm hNR]) hRm
  have hEτ : NumOn τ E (W + 1) e0 := hfr.numOn (by simp [Ne.symm hME, Ne.symm hNE]) hE
  have hKτ : τ.val K = 0 := by rw [hfr.val (by simp [Ne.symm hSK, Ne.symm hTK])]; exact hK
  have hT2τ : τ.val T2 = 0 := by rw [hfr.val (by simp [Ne.symm hST2, Ne.symm hTT2])]; exact hT2
  have hy0 : 0 < y.natAbs := Int.natAbs_pos.mpr hy
  have hd := BinW.divmod_spec cap (W + 1) hMQ hMR hME hNQ hNR hNE hQR hQE hRE hFR hFK hRK hKT2 τ x.natAbs y.natAbs
    q0 r0 e0 hMτ hNτ hQτ hRτ' hEτ hFτ hRτ hKτ hT2τ (by omega) hy0 (by omega) hcap
  set τ1 := ((τ.sets Q (frame (binary (W + 1) (x.natAbs / y.natAbs)))).sets Rm
    (frame (binary (W + 1) (x.natAbs % y.natAbs)))).sets E (frame (binary (W + 1) 0)) with hτ1
  have hsg : WXExec cap (.ifr T (.seq (WMX.dec T) (flip S)) WMX.skip) τ1
      ((τ1.setv S (decide (x < 0) ^^ decide (y < 0)).toNat).setv T 0) 7 := by
    by_cases hyn : y < 0
    · have hv : τ1.val T ≠ 0 := by simp [hτ1, hTτ, hyn]
      have hdd := WXExec.dec cap T τ1 (by simp [hτ1, hTτ, hyn]; omega)
      have hf := flip_spec cap S (τ1.setv T (τ1.val T - 1)) (decide (x < 0))
        (by simp [hτ1, Function.update_of_ne hST, hSτ]) (by omega)
      refine (WXExec.ifrT hv (WXExec.seq hdd hf)).cast cap ?_ (by omega)
      apply WState.eq <;> try rfl
      funext r; simp only [WState.setv_val, Function.update_apply]
      by_cases h1 : r = S
      · subst h1; simp [hST, hyn]
      · by_cases h2 : r = T
        · subst h2; simp [h1, hτ1, hTτ, hyn]
        · simp [h1, h2]
    · have hv : τ1.val T = 0 := by simp [hτ1, hTτ, hyn]
      refine (WXExec.ifrF hv (WXExec.skip cap τ1)).cast cap ?_ (by omega)
      apply WState.eq <;> try rfl
      funext r; simp only [WState.setv_val, Function.update_apply]
      by_cases h1 : r = S
      · subst h1; simp [hST, hyn, hτ1, hSτ]
      · by_cases h2 : r = T
        · subst h2; simp [hv]
        · simp [h1, h2]
  set τ2 := (τ1.setv S (decide (x < 0) ^^ decide (y < 0)).toNat).setv T 0 with hτ2
  have hq : x.natAbs / y.natAbs < 2 ^ W := lt_of_le_of_lt (Nat.div_le_self _ _) hxW
  have hj := join_spec cap W hXQ hFR hSF hSR τ2 _ (encS x) (decide (x < 0) ^^ decide (y < 0))
    (by simp only [hτ2, hτ1]
        exact BinW.numOn_setv (BinW.numOn_setv (BinW.numOn_sets_ne (BinW.numOn_sets_ne (BinW.numOn_sets_self τ Q _ _
          hQτ.2) hQR _) hQE _) _ _) _ _) hq
    (by simp only [hτ2, hτ1]
        exact BinW.numOn_setv (BinW.numOn_setv (BinW.numOn_sets_ne (BinW.numOn_sets_ne (BinW.numOn_sets_ne hXτ.1
          hXQ _) hXR _) hXE _) _ _) _ _)
    (by simp [hτ2, Function.update_of_ne hST]) (by simp [hτ2, hτ1, Function.update_of_ne (Ne.symm hTF),
      Function.update_of_ne (Ne.symm hSF), hFτ]) (by simp [hτ2, hτ1, Function.update_of_ne (Ne.symm hTR),
      Function.update_of_ne (Ne.symm hSR), hRτ]) hcap
  rw [← tdiv_sval] at hj
  refine (Runs.seqE hd (Runs.seqE hsg (Runs.of hj ?_))).cost le_rfl
  refine ⟨⟨?_, ?_⟩, ⟨x.natAbs, ?_⟩, ⟨y.natAbs, ?_⟩, ⟨x.natAbs / y.natAbs, ?_⟩, ⟨x.natAbs % y.natAbs, ?_⟩, ⟨0, ?_⟩, ?_⟩
  · exact BinW.numOn_setv (BinW.numOn_sets_self _ X _ _ (by simp [hτ2, hτ1, hXτ.1.2])) _ _
  · rw [Int.natAbs_tdiv]; exact lt_of_le_of_lt (Nat.div_le_self _ _) hxW
  · exact BinW.numOn_setv (BinW.numOn_sets_ne (BinW.numOn_setv (BinW.numOn_setv (BinW.numOn_sets_ne
      (BinW.numOn_sets_ne (BinW.numOn_sets_ne hMτ hMQ _) hMR _) hME _) _ _) _ _) (Ne.symm hXM) _) _ _
  · exact BinW.numOn_setv (BinW.numOn_sets_ne (BinW.numOn_setv (BinW.numOn_setv (BinW.numOn_sets_ne
      (BinW.numOn_sets_ne (BinW.numOn_sets_ne hNτ hNQ _) hNR _) hNE _) _ _) _ _) (Ne.symm hXN) _) _ _
  · exact BinW.numOn_setv (BinW.numOn_sets_ne (BinW.numOn_setv (BinW.numOn_setv (BinW.numOn_sets_ne
      (BinW.numOn_sets_ne (BinW.numOn_sets_self τ Q _ _ hQτ.2) hQR _) hQE _) _ _) _ _) (Ne.symm hXQ) _) _ _
  · exact BinW.numOn_setv (BinW.numOn_sets_ne (BinW.numOn_setv (BinW.numOn_setv (BinW.numOn_sets_ne
      (BinW.numOn_sets_self _ Rm _ _ (by simp [Function.update_of_ne (Ne.symm hQR), hRτ'.2])) hRE _) _ _) _ _)
      (Ne.symm hXR) _) _ _
  · exact BinW.numOn_setv (BinW.numOn_sets_ne (BinW.numOn_setv (BinW.numOn_setv
      (BinW.numOn_sets_self _ E _ _ (by simp [Function.update_of_ne (Ne.symm hQE), Function.update_of_ne (Ne.symm hRE),
        hEτ.2])) _ _) _ _) (Ne.symm hXE) _) _ _
  · refine ⟨fun z hz => ?_, fun r _ => ?_, by simp [hτ2, hτ1, hfr.cell]⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hz
      simp [hτ2, hτ1, Function.update_of_ne h1, Function.update_of_ne h4, Function.update_of_ne h5,
        Function.update_of_ne h6, hfr.st (x := z) (by simp [h2, h3]), hfr.sh (x := z) (by simp [h2, h3])]
    · by_cases h1 : r = S
      · subst h1; simp [hS]
      · by_cases h2 : r = T
        · subst h2; simp [Function.update_of_ne (Ne.symm hST), hτ2, hT]
        · simp [hτ2, hτ1, Function.update_of_ne h1, Function.update_of_ne h2, hfr.val (r := r) (by simp [h1, h2])]

end Div

attribute [irreducible] sdiv

end NearCubicGates.Close.Solve
