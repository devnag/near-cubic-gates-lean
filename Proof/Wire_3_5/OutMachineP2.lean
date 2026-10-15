import Proof.Wire_3_5.OutMachineP1

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.Out.P2
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.Out
open NearCubicWires.WireExponent3_5.FinalPass.Out.Half NearCubicWires.WireExponent3_5.FinalPass.Out.P1
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)

variable {ns nr : ℕ} (cap : ℕ)

/-- **One round**: if `U` is even, halve it; `K -= 1`. -/
def oddBody (U : Fin (ns + 1)) (R K : Fin nr) : WM ns nr :=
  .seq (.fwd U) (.seq (.ifs U (.bwd U) (.seq (.bwd U) (halfW U R))) (.dec K))

theorem oddBody_spec (U : Fin (ns + 1)) (R K : Fin nr) (W u k : ℕ) (σ : WState ns nr) (hW : 1 ≤ W)
    (hU : NumOn σ U W u) (hu : u < 2 ^ W) (hR : σ.val R = 0) (hK : σ.val K = k + 1) (hk : k + 1 ≤ cap)
    (hc : 2 * W ≤ cap) :
    WExec cap (oddBody U R K) σ ((σ.sets U (frame (binary W (oddStep u)))).setv K k) (34 * W + 10) := by
  have s1 : WExec cap (.fwd U) σ (σ.seth U 1) 1 := by
    have h := WExec.fwd (cap := cap) U σ
    rwa [hU.2] at h
  have bU : wbit (σ.seth U 1) U = (u % 2 == 1) := by
    unfold wbit
    simp only [WState.seth_st, WState.seth_sh, Function.update_self, hU.1]
    exact bit0_frame W u hW
  have bk : WExec cap (.bwd U) (σ.seth U 1) σ 1 := by
    have h := WExec.bwd (cap := cap) U (σ.seth U 1)
    rwa [wseth_sh_self, Nat.sub_self, wseth_seth, ← hU.2, wseth_same] at h
  have hbr : WExec cap (.ifs U (.bwd U) (.seq (.bwd U) (halfW U R))) (σ.seth U 1)
      (σ.sets U (frame (binary W (oddStep u)))) (34 * W + 6) := by
    by_cases h2 : u % 2 = 0
    · have e : oddStep u = u / 2 := by simp [oddStep, h2]
      rw [e]
      have b' : wbit (σ.seth U 1) U = false := by rw [bU]; simp [h2]
      exact WExec.mono (WExec.ifsF b' (WExec.seq bk (halfW_spec cap U R W u σ hU hR hu hc))) (by omega)
    · have e : oddStep u = u := by simp [oddStep, h2]
      rw [e, ← hU.1, wsets_same]
      have b' : wbit (σ.seth U 1) U = true := by rw [bU]; simp; omega
      exact WExec.mono (WExec.ifsT b' bk) (by omega)
  have hdec := WExec.dec (cap := cap) K (σ.sets U (frame (binary W (oddStep u)))) (by simp [hK]; omega)
  simp only [WState.sets_val, hK, Nat.add_sub_cancel] at hdec
  exact WExec.cast cap (WExec.seq s1 (WExec.seq hbr hdec)) rfl (by omega)

theorem oddLoop_spec (U : Fin (ns + 1)) (R K : Fin nr) (hRK : R ≠ K) (W : ℕ) (hc : 2 * W ≤ cap) (hWc : W ≤ cap) :
    ∀ (k u : ℕ) (σ : WState ns nr), k ≤ W → NumOn σ U W u → u < 2 ^ W → σ.val R = 0 → σ.val K = k →
      WExec cap (.whr K (oddBody U R K)) σ ((σ.sets U (frame (binary W (oddStep^[k] u)))).setv K 0)
        (k * (34 * W + 12) + 1)
  | 0, u, σ, _, hU, _, _, hK => by
    refine WExec.cast cap (WExec.whrF hK) ?_ (by omega)
    have e := wsetv_same σ K
    rw [hK] at e
    simp only [Function.iterate_zero, id]
    rw [← hU.1, wsets_same, e]
  | k + 1, u, σ, hkW, hU, hu, hR, hK => by
    have body := oddBody_spec cap U R K W u k σ (by omega) hU hu hR hK (by omega) hc
    have hlt : oddStep u < 2 ^ W := lt_of_le_of_lt (Val.oddStep_le u) hu
    have ih := oddLoop_spec U R K hRK W hc hWc k (oddStep u) ((σ.sets U (frame (binary W (oddStep u)))).setv K k)
      (by omega)
      (numOn_setv _ _ _ _ _ _ (numOn_sets_self σ U W _ hU.2)) hlt (by simp [hR, Function.update_of_ne hRK])
      (by simp)
    refine WExec.cast cap (WExec.whrT (by omega) body ih) ?_ (by ring_nf; omega)
    rw [Function.iterate_succ_apply]
    refine WState.eq rfl ?_ ?_ rfl
    · funext j; simp only [WState.setv_st, WState.sets_st, Function.update_apply]; split_ifs <;> rfl
    · funext j; simp only [WState.setv_val, WState.sets_val, Function.update_apply]; split_ifs <;> rfl

/-! ## P2 -/

/-- **P2's program**: `U := b`, `rK := W`, `W` rounds towards the odd part, `V := a`. -/
def p2P : WM nsO nrO :=
  .seq (UnionMachine.RegRat.copyB sU sD rF rR) (.seq (UnionMachine.BinW.dupR rW rK (rg 0))
    (.seq (.whr rK (oddBody sU rR rK)) (UnionMachine.RegRat.copyB sV sN rF rR)))

/-- P2's cost. -/
def p2Cost (W : ℕ) : ℕ := 41 * W + 3 + 1 + (18 * W + 3 + 1 + (W * (34 * W + 12) + 1 + 1 + (41 * W + 3)))

theorem p2Cost_le (W : ℕ) : p2Cost W ≤ 200 * (W + 1) ^ 2 := by
  unfold p2Cost
  nlinarith [Nat.zero_le W]

theorem p2_run (W a b u v : ℕ) (σ : St) (h : Words σ W a b u v) (_ha : a < 2 ^ W) (hb : b < 2 ^ W) :
    ∃ τ, WExec (capO W) p2P σ τ (p2Cost W) ∧ Words τ W a b (oddPart W b) a := by
  have hc : 2 * W + 1 ≤ capO W := by unfold capO; omega
  have hF : σ.val rF = 0 := h.bd.regs rF (by decide)
  have hR : σ.val rR = 0 := h.bd.regs rR (by decide)
  have sA := UnionMachine.RegRat.copyB_spec (capO W) W (show sU ≠ sD by decide) (show rF ≠ rR by decide) σ u b
    h.hu h.hd hF hR hc
  have sB := UnionMachine.BinW.dupR_spec (capO W) rW rK (rg 0) (by decide) (by decide) (by decide)
    (σ.sets sU (frame (binary W b))) W h.bd.hw (h.bd.regs rK (by decide)) (h.bd.regs (rg 0) (by decide))
    (by unfold capO; omega)
  have sC := oddLoop_spec (capO W) sU rR rK (by decide) W (by unfold capO; omega) (by unfold capO; omega) W b
    ((σ.sets sU (frame (binary W b))).setv rK W) le_rfl
    (numOn_setv _ _ _ _ _ _ (numOn_sets_self σ sU W b (h.bd.heads _))) hb
    (by simp [Function.update_of_ne (show rR ≠ rK by decide), hR]) (by simp)
  set σC := (((σ.sets sU (frame (binary W b))).setv rK W).sets sU (frame (binary W (oddStep^[W] b)))).setv rK 0
    with hσC
  have hvC : NumOn σC sV W v := numOn_setv _ _ _ _ _ _ (numOn_sets_ne _ _ _ _ (by decide)
    (numOn_setv _ _ _ _ _ _ (numOn_sets_ne _ _ _ _ (by decide) h.hv)))
  have hnC : NumOn σC sN W a := numOn_setv _ _ _ _ _ _ (numOn_sets_ne _ _ _ _ (by decide)
    (numOn_setv _ _ _ _ _ _ (numOn_sets_ne _ _ _ _ (by decide) h.hn)))
  have sD' := UnionMachine.RegRat.copyB_spec (capO W) W (show sV ≠ sN by decide) (show rF ≠ rR by decide) σC v a
    hvC hnC (by simp [hσC, Function.update_of_ne (show rF ≠ rK by decide), hF])
    (by simp [hσC, Function.update_of_ne (show rR ≠ rK by decide), hR]) hc
  refine ⟨σC.sets sV (frame (binary W a)), WExec.cast (capO W) (WExec.seq sA (WExec.seq sB (WExec.seq sC sD'))) rfl
    (by unfold p2Cost; omega), ?_⟩
  have up : ∀ (X : Fin (nsO + 1)) (x : ℕ), X ≠ sU → X ≠ sV → NumOn σ X W x →
      NumOn (σC.sets sV (frame (binary W a))) X W x := fun X x h1 h2 hX =>
    numOn_sets_ne σC _ W x h2 (numOn_setv _ _ _ _ _ _ (numOn_sets_ne _ _ W x h1
      (numOn_setv _ _ _ _ _ _ (numOn_sets_ne σ _ W x h1 hX))))
  refine ⟨⟨h.bd.heads, h.bd.cell, ?_, fun r hr => ?_⟩, ?_, up sN a (by decide) (by decide) h.hn,
    up sD b (by decide) (by decide) h.hd, ?_, ?_, ?_, fun j => up (sX j) 0 ?_ ?_ (h.hx j)⟩
  · simp [hσC, Function.update_of_ne (show rW ≠ rK by decide), h.bd.hw]
  · by_cases hk : r = rK
    · subst hk; simp [hσC]
    · simp [hσC, Function.update_of_ne hk, h.bd.regs r hr]
  · simp [hσC, Function.update_of_ne (show sO ≠ sV by decide), Function.update_of_ne (show sO ≠ sU by decide), h.ho]
  · refine ⟨?_, by simp [hσC, h.bd.heads]⟩
    simp [hσC, Function.update_of_ne (show sU ≠ sV by decide), oddPart]
  · exact numOn_sets_self _ sV W a (by simp [hσC, h.bd.heads])
  · obtain ⟨x, hx⟩ := h.ht
    exact ⟨x, up sT x (by decide) (by decide) hx⟩
  · fin_cases j <;> decide
  · fin_cases j <;> decide

/-- **P2**. -/
def ph2 : Ph2 := ⟨p2P, p2Cost, 200, p2Cost_le, p2_run⟩

end NearCubicWires.WireExponent3_5.FinalPass.Out.P2
