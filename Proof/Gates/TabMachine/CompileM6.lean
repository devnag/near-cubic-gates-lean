import Proof.Gates.TabMachine.CompileM5

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
open NearCubicGates.Close.WordPrograms.SInt (encS sval SNumOn split split_spec)
open StablePartition.Workspace (overlay)

variable {ns nr : ℕ}

/-- `Σ_{w<0} |w|` as a natural number. -/
def negN (ws : List ℤ) : ℕ := (ws.map fun z => if z < 0 then z.natAbs else 0).sum

theorem negN_cast (ws : List ℤ) : (negN ws : ℤ) = negMassL ws := by
  unfold negN negMassL; rw [Nat.cast_list_sum, List.map_map]; congr 1
  apply List.map_congr_left; intro z _; simp only [Function.comp_apply]; split <;> simp

theorem negN_snoc (l : List ℤ) (z : ℤ) : negN (l ++ [z]) = negN l + if z < 0 then z.natAbs else 0 := by
  simp [negN]

theorem totalL_snoc (l : List ℤ) (z : ℤ) : totalL (l ++ [z]) = totalL l + z.natAbs := by simp [totalL]

theorem maxL_snoc (l : List ℤ) (z : ℤ) : maxL (l ++ [z]) = max (maxL l) z.natAbs := by
  unfold maxL
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.foldr_cons, List.cons_append, List.map_append] at ih ⊢
                   rw [ih]; omega

section Stats
variable (S : Fin 24 ↪ Fin (ns + 1)) (R : Fin 24 ↪ Fin nr)

/-- One weight record: the three statistics updated. -/
def statBody : WMX ns nr :=
  .seq (split (S 3) (S 4) (R 4) (R 2) (R 3))
  (.seq (BinW.add (S 9) (S 4) (R 2) (R 3))
  (.seq (.ifr (R 4) (.seq (BinW.add (S 8) (S 4) (R 2) (R 3)) (WMX.dec (R 4))) WMX.skip)
  (.seq (BinW.lt (S 10) (S 4) (R 2) (R 3))
  (.ifr (R 2) (.seq (WMX.dec (R 2)) (BinW.copy (S 10) (S 4) (R 2) (R 3))) WMX.skip))))

theorem statBody_spec (cap W : ℕ) (σ : WState ns nr) (z : ℤ) (nm tm mx m0 : ℕ)
    (hWk : NumOn σ (S 3) (W + 1) (encS z)) (hM : NumOn σ (S 4) (W + 1) m0) (hNM : NumOn σ (S 8) (W + 1) nm)
    (hTM : NumOn σ (S 9) (W + 1) tm) (hMX : NumOn σ (S 10) (W + 1) mx) (hSg : σ.val (R 4) = 0)
    (hF : σ.val (R 2) = 0) (hR : σ.val (R 3) = 0) (hz : z.natAbs < 2 ^ W) (hmx : mx < 2 ^ (W + 1))
    (hnm : nm + z.natAbs < 2 ^ (W + 1)) (htm : tm + z.natAbs < 2 ^ (W + 1)) (hcap : 2 * (W + 1) + 1 ≤ cap) :
    Runs cap (statBody S R) σ (450 * W + 600) (fun τ =>
      NumOn τ (S 8) (W + 1) (nm + if z < 0 then z.natAbs else 0) ∧ NumOn τ (S 9) (W + 1) (tm + z.natAbs) ∧
      NumOn τ (S 10) (W + 1) (max mx z.natAbs) ∧ (∃ v, NumOn τ (S 4) (W + 1) v) ∧
      SameExcept σ τ [S 4, S 8, S 9, S 10] []) := by
  have hne : ∀ {a b : Fin 24}, a ≠ b → S a ≠ S b := fun h => emb_ne S h
  have hner : ∀ {a b : Fin 24}, a ≠ b → R a ≠ R b := fun h => emb_ne R h
  set a := z.natAbs with ha
  have h1 := split_spec (X := S 3) (M := S 4) (S := R 4) (F := R 2) (R := R 3) cap W (hne (by decide))
    (hner (by decide)) σ z m0 ⟨hWk, hz⟩ hM hSg hF hR hcap
  set σ1 := (σ.sets (S 4) (frame (binary (W + 1) a))).setv (R 4) (decide (z < 0)).toNat with hσ1
  have hM1 : NumOn σ1 (S 4) (W + 1) a := BinW.numOn_setv (BinW.numOn_sets_self _ _ _ _ hM.2) _ _
  have hl1 : ∀ (k : Fin 24) (v : ℕ), k ≠ 4 → NumOn σ (S k) (W + 1) v → NumOn σ1 (S k) (W + 1) v :=
    fun k v hk h => BinW.numOn_setv (BinW.numOn_sets_ne h (hne hk) _) _ _
  have h2 := BinW.add_spec (A := S 9) (B := S 4) (F := R 2) (R := R 3) cap (W + 1) (hne (by decide)) (hner (by decide))
    σ1 tm a (hl1 _ _ (by decide) hTM) hM1 (by simp [hσ1, emb_eq_iff, hF]) (by simp [hσ1, emb_eq_iff, hR]) htm hcap
  set σ2 := σ1.sets (S 9) (frame (binary (W + 1) (tm + a))) with hσ2
  set nm' := nm + if z < 0 then a else 0 with hnm'
  have h3 : WXExec cap (.ifr (R 4) (.seq (BinW.add (S 8) (S 4) (R 2) (R 3)) (WMX.dec (R 4))) WMX.skip) σ2
      ((σ2.sets (S 8) (frame (binary (W + 1) nm'))).setv (R 4) 0) (41 * W + 50) := by
    by_cases hneg : z < 0
    · have hv : σ2.val (R 4) ≠ 0 := by simp [hσ2, hσ1, hneg]
      have hadd := BinW.add_spec (A := S 8) (B := S 4) (F := R 2) (R := R 3) cap (W + 1) (hne (by decide))
        (hner (by decide)) σ2 nm a (BinW.numOn_sets_ne (hl1 _ _ (by decide) hNM) (hne (by decide)) _)
        (BinW.numOn_sets_ne hM1 (hne (by decide)) _) (by simp [hσ2, hσ1, emb_eq_iff, hF])
        (by simp [hσ2, hσ1, emb_eq_iff, hR]) hnm hcap
      have hd := WXExec.dec cap (R 4) (σ2.sets (S 8) (frame (binary (W + 1) (nm + a))))
        (by simp [hσ2, hσ1, hneg]; omega)
      refine (WXExec.ifrT hv (WXExec.seq hadd hd)).cast cap ?_ (by omega)
      rw [hnm', if_pos hneg]; simp [hσ2, hσ1, hneg]
    · have hv : σ2.val (R 4) = 0 := by simp [hσ2, hσ1, hneg]
      refine (WXExec.ifrF hv (WXExec.skip cap σ2)).cast cap ?_ (by omega)
      have e : nm' = nm := by rw [hnm', if_neg hneg]; rfl
      rw [e]
      apply WState.eq <;> try rfl
      · funext i; by_cases hi : i = S 8
        · subst hi; simp [hσ2, hσ1, emb_eq_iff, hNM.1]
        · simp [Function.update_of_ne hi]
      · funext r; by_cases hr : r = R 4
        · subst hr; simp [hσ2, hσ1, hneg]
        · simp [Function.update_of_ne hr]
  set σ3 := (σ2.sets (S 8) (frame (binary (W + 1) nm'))).setv (R 4) 0 with hσ3
  have hMX3 : NumOn σ3 (S 10) (W + 1) mx :=
    BinW.numOn_setv (BinW.numOn_sets_ne (BinW.numOn_sets_ne (hl1 _ _ (by decide) hMX) (hne (by decide)) _)
      (hne (by decide)) _) _ _
  have hM3 : NumOn σ3 (S 4) (W + 1) a :=
    BinW.numOn_setv (BinW.numOn_sets_ne (BinW.numOn_sets_ne hM1 (hne (by decide)) _) (hne (by decide)) _) _ _
  have hR3 : ∀ k : Fin 24, k ≠ 4 → σ3.val (R k) = σ.val (R k) := fun k hk => by
    simp [hσ3, hσ2, hσ1, Function.update_of_ne (hner hk)]
  have h4 := BinW.lt_spec (A := S 10) (B := S 4) (F := R 2) (R := R 3) cap (W + 1) (hne (by decide)) (hner (by decide))
    σ3 mx a hMX3 hM3 (by rw [hR3 2 (by decide), hF]) (by rw [hR3 3 (by decide), hR]) hmx (by omega) hcap
  have h5 : WXExec cap (.ifr (R 2) (.seq (WMX.dec (R 2)) (BinW.copy (S 10) (S 4) (R 2) (R 3))) WMX.skip)
      (σ3.setv (R 2) (decide (mx < a)).toNat) (σ3.sets (S 10) (frame (binary (W + 1) (max mx a)))) (41 * W + 50) := by
    by_cases hlt : mx < a
    · have hv : (σ3.setv (R 2) (decide (mx < a)).toNat).val (R 2) ≠ 0 := by simp [hlt]
      have hd := WXExec.dec cap (R 2) (σ3.setv (R 2) (decide (mx < a)).toNat) (by simp [hlt]; omega)
      have e : (σ3.setv (R 2) (decide (mx < a)).toNat).setv (R 2)
          ((σ3.setv (R 2) (decide (mx < a)).toNat).val (R 2) - 1) = σ3 := by
        apply WState.eq <;> try rfl
        funext r; by_cases hr : r = R 2
        · subst hr; simp [hlt, hR3 2 (by decide), hF]
        · simp [Function.update_of_ne hr]
      rw [e] at hd
      have hc := BinW.copy_spec (A := S 10) (B := S 4) (F := R 2) (R := R 3) cap (W + 1) (hne (by decide))
        (hner (by decide)) σ3 mx a hMX3 hM3 (by rw [hR3 2 (by decide), hF]) (by rw [hR3 3 (by decide), hR]) hcap
      refine (WXExec.ifrT hv (WXExec.seq hd hc)).cast cap ?_ (by omega)
      rw [max_eq_right hlt.le]
    · have hv : (σ3.setv (R 2) (decide (mx < a)).toNat).val (R 2) = 0 := by simp [hlt]
      refine (WXExec.ifrF hv (WXExec.skip cap _)).cast cap ?_ (by omega)
      rw [max_eq_left (by omega)]
      apply WState.eq <;> try rfl
      · funext i; by_cases hi : i = S 10
        · subst hi; simp [hMX3.1]
        · simp [Function.update_of_ne hi]
      · funext r; by_cases hr : r = R 2
        · subst hr; simp [hlt, hR3 2 (by decide), hF]
        · simp [Function.update_of_ne hr]
  refine ⟨_, WXExec.mono (WXExec.seq h1 (WXExec.seq h2 (WXExec.seq h3 (WXExec.seq h4 h5)))) (by omega), ?_, ?_, ?_,
    ⟨a, BinW.numOn_sets_ne hM3 (hne (by decide)) _⟩, ?_⟩
  · exact BinW.numOn_sets_ne (BinW.numOn_setv (BinW.numOn_sets_self _ _ _ _ (by simp [hσ2, hσ1, hNM.2])) _ _)
      (hne (by decide)) _
  · exact BinW.numOn_sets_ne (BinW.numOn_setv (BinW.numOn_sets_ne (BinW.numOn_sets_self _ _ _ _
      (by simp [hσ1, hTM.2])) (hne (by decide)) _) _ _) (hne (by decide)) _
  · exact BinW.numOn_sets_self _ _ _ _ (by simp [hσ3, hσ2, hσ1, hMX.2])
  · refine ⟨fun y hy => ?_, fun r _ => ?_, rfl⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
      simp [hσ3, hσ2, hσ1, Function.update_of_ne hy.1, Function.update_of_ne hy.2.1, Function.update_of_ne hy.2.2.1,
        Function.update_of_ne hy.2.2.2]
    · by_cases hr : r = R 4
      · subst hr; simp [hσ3, hSg]
      · simp [hσ3, hσ2, hσ1, Function.update_of_ne hr]

end Stats

end NearCubicGates.Close.TabMachine
