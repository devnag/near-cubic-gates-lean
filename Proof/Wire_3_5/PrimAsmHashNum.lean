import Proof.Wire_3_5.PrimAsmHashBank
import Proof.Wire_3_5.PrimAsmGapNums0

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimAsm.SymDec
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.PrimAsm.CellState
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat NearCubicWires.WireExponent3_5.PrimAsm.SparseNum
open NearCubicWires.WireExponent3_5.PrimAsm.FiltNum NearCubicWires.WireExponent3_5.PrimAsm.CapNum
open NearCubicWires.WireExponent3_5.PrimAsm.UnaryArith

section HN
variable (cap : ℕ) (x : ℕ)

/-- The aux filter's numbers: `GapNums.gapNumsW`, or its empty-population twin when `len = 0` (no named atoms). -/
def hGW : WM (LNS x) LNR := .ifr (G 1) (GapNums.gapNumsW (KG.trans G)) (GapNums.gapNums0W (KG.trans G))

/-- **The HASH decode's numbers and index split.** -/
def hNW (cr : ℕ) : WM (LNS x) LNR :=
  .seq (.seq (hAW x cr) (.seq (hC1W x) (hC2W x))) (.seq (.seq (hD1W x) (.seq (hGW x) (hD3W x))) (idxW x))

/-- Its cost bound. -/
def hNCost (n wl cr cap : ℕ) : ℕ :=
  hACost n wl cr cap + 1 + (34 * UnaryPow.sq cap + 1 + (8 * UnaryPow.sq cap + 1 + (28 * UnaryPow.sq cap + 1 +
    (110 * UnaryPow.sq cap + 1 + 1 + (34 * UnaryPow.sq cap + 1 + (30 * UnaryPow.sq cap + 1 + 26 * UnaryPow.sq cap))))))

theorem hAC_run (cr : ℕ) (P : Shared.StarParams) (hrP : P.r = Ledger.rowBr cr P.n) (w out : List Bool) (j : ℕ)
    (codes cc : List ℕ) (tl : List Bool) (hw : w = Data.reqW P.n true codes cc tl)
    (hs xs : List ℕ) (tg : ℕ) (hhs : hs.length = 16) (hxs : xs.length ≤ 2) (h0v : hs.getD 0 0 = xs.length)
    (hc1 : 2 * w.length + 2 ≤ cap) (hc2 : 2 ^ (natBitLength P.n + 1) ≤ cap) (hc3 : (0 + 4) * (P.n + 3) + 2 * cr + 20 ≤ cap)
    (hcl : ∀ k, (hs ++ (xs ++ [tg])).getD k 0 ≤ cap) (hcs : xs.sum + tg + 4 ≤ cap) :
    ∃ τ c, WExec cap (.seq (hAW x cr) (.seq (hC1W x) (hC2W x)))
        (CellLoopD.blankCellD x w out j (Data.unaryList (hs ++ (xs ++ [tg])))) τ c ∧
      c ≤ hACost P.n w.length cr cap + 1 + (34 * UnaryPow.sq cap + 1 + 8 * UnaryPow.sq cap) ∧
      τ.val (Hb 0) = xs.length ∧ τ.val (Hb 1) = hs.getD 1 0 ∧ τ.val (Hb 8) = hs.getD 8 0 ∧
      τ.val (Hb 13) = hs.getD 13 0 ∧ τ.val XA = xs.sum ∧
      τ.val XB = tg ∧ τ.val (SGb 8) = P.s * (P.r / 2) ∧
      (∀ r : Fin LNR, (r.val < 250 ∨ 400 ≤ r.val ∨ r.val = 322 ∨ r.val = 374) → τ.val r = 0) ∧
      τ.st = (CellLoopD.blankCellD x w out j (Data.unaryList (hs ++ (xs ++ [tg])))).st ∧
      (∀ s, s ≠ sk x 113 → τ.sh s = (CellLoopD.blankCellD x w out j (Data.unaryList (hs ++ (xs ++ [tg])))).sh s) ∧
      τ.cell = false ∧ (∀ q, τ.val q ≤ cap) := by
  have hsq := UnaryPow.sq_ge cap
  have hl := UnaryPow.lin_le_sq cap
  set σ₀ := CellLoopD.blankCellD x w out j (Data.unaryList (hs ++ (xs ++ [tg]))) with hσ₀
  have hv0 : ∀ r, σ₀.val r = 0 := fun r => rfl
  have n0B : sk x 0 ≠ sk x 113 := fun e => absurd (sk_inj x e) (by decide)
  have n01 : sk x 0 ≠ sk x 1 := fun e => absurd (sk_inj x e) (by decide)
  have st0 : σ₀.st (sk x 0) = frame w := by rw [hσ₀]; simp [CellLoopD.blankCellD, blankCell, n0B]
  have sh0 : σ₀.sh (sk x 0) = 0 := by rw [hσ₀]; simp [CellLoopD.blankCellD, blankCell, n01]
  have st113 : σ₀.st (sk x 113) = Data.unaryList (hs ++ (xs ++ [tg])) ++ [] := by
    rw [hσ₀, List.append_nil]; simp [CellLoopD.blankCellD]
  have sh113 : σ₀.sh (sk x 113) = 0 := by
    have n1B : sk x 113 ≠ sk x 1 := fun e => absurd (sk_inj x e) (by decide)
    rw [hσ₀]; simp [CellLoopD.blankCellD, blankCell, n1B]
  -- A
  have eA := hA_run cap x cr P hrP σ₀ w true codes cc tl hw st0 sh0 (hv0 _) (hv0 _) (hv0 _) (hv0 _) (hv0 _) (hv0 _)
    (hv0 _) (hv0 _) (hv0 _) (fun _ => hv0 _) hc1 hc2 hc3
  set σA := hAOut x σ₀ w P with hσA
  have vA : ∀ r : Fin LNR, (r.val < 250 ∨ 270 ≤ r.val) → r.val ≠ 369 → r.val ≠ 320 → σA.val r = 0 := by
    intro r h1 h2 h3
    rw [hσA]
    unfold hAOut StarNums.starOut
    have ns : ∀ i : Fin 20, r ≠ SGb i := fun i e => by
      have := congrArg Fin.val e; rw [SGb_val] at this; have := i.isLt; omega
    have nL : r ≠ LEN := fun e => h2 (by rw [e]; rfl)
    have nN : r ≠ dN := fun e => h3 (by rw [e]; rfl)
    simp only [WState.setv_val, WState.seth_val, Function.update_of_ne (ns _), Function.update_of_ne nL,
      Function.update_of_ne nN]
    exact hv0 r
  have v8 : σA.val (SGb 8) = P.s * (P.r / 2) := by
    rw [hσA]; unfold hAOut; exact (StarNums.starOut_val _ _ _ _).2.2.2.2.2.2.1
  have stA : σA.st = σ₀.st := by rw [hσA]; unfold hAOut StarNums.starOut; simp
  have shA0 : σA.sh (sk x 0) = 0 := by rw [hσA]; unfold hAOut StarNums.starOut; simp
  have shA : ∀ s, s ≠ sk x 0 → σA.sh s = σ₀.sh s := fun s hs => by
    rw [hσA]; unfold hAOut StarNums.starOut; simp [Function.update_apply, hs]
  have clA : σA.cell = σ₀.cell := by rw [hσA]; unfold hAOut StarNums.starOut; simp
  have hBA : ∀ q, σA.val q ≤ cap := wexec_le cap eA (fun q => by rw [hv0]; omega)
  -- C1
  have eC1 := hC1_run cap x σA (hs ++ (xs ++ [tg])) [] (by simp [hhs]) (by rw [stA]; exact st113)
    (by rw [shA _ (Ne.symm n0B)]; exact sh113)
    (fun i => vA _ (by rw [Hb_val]; omega) (by rw [Hb_val]; have := i.isLt; omega) (by rw [Hb_val]; omega)) hcl
  set σC1 := hC1Out x σA (hs ++ (xs ++ [tg])) with hσC1
  have kC1 : ∀ r : Fin LNR, (r.val < 337 ∨ 353 ≤ r.val) → σC1.val r = σA.val r := by
    intro r hr
    have e0 : r.val ≠ 337 := by omega
    have e1 : r.val ≠ 338 := by omega
    have e2 : r.val ≠ 339 := by omega
    have e3 : r.val ≠ 340 := by omega
    have e4 : r.val ≠ 341 := by omega
    have e5 : r.val ≠ 342 := by omega
    have e6 : r.val ≠ 343 := by omega
    have e7 : r.val ≠ 344 := by omega
    have e8 : r.val ≠ 345 := by omega
    have e9 : r.val ≠ 346 := by omega
    have e10 : r.val ≠ 347 := by omega
    have e11 : r.val ≠ 348 := by omega
    have e12 : r.val ≠ 349 := by omega
    have e13 : r.val ≠ 350 := by omega
    have e14 : r.val ≠ 351 := by omega
    have e15 : r.val ≠ 352 := by omega
    rw [hσC1]; unfold hC1Out
    simp [Function.update_apply, Fin.ext_iff, Hb_val, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  have c10 : σC1.val (Hb 0) = xs.length := by
    rw [hσC1]; unfold hC1Out
    simp [Function.update_apply, Fin.ext_iff, Hb_val, -List.getD_eq_getElem?_getD]
    rw [List.getD_append _ _ _ _ (by omega)]; exact h0v
  have c11 : σC1.val (Hb 1) = hs.getD 1 0 := by
    rw [hσC1]; unfold hC1Out
    simp [Function.update_apply, Fin.ext_iff, Hb_val, -List.getD_eq_getElem?_getD]
    rw [List.getD_append _ _ _ _ (by omega)]
  have c18 : σC1.val (Hb 8) = hs.getD 8 0 := by
    rw [hσC1]; unfold hC1Out
    simp [Function.update_apply, Fin.ext_iff, Hb_val, -List.getD_eq_getElem?_getD]
    rw [List.getD_append _ _ _ _ (by omega)]
  have c113 : σC1.val (Hb 13) = hs.getD 13 0 := by
    rw [hσC1]; unfold hC1Out
    simp [Function.update_apply, Fin.ext_iff, Hb_val, -List.getD_eq_getElem?_getD]
    rw [List.getD_append _ _ _ _ (by omega)]
  have stC1 : σC1.st = σ₀.st := by rw [hσC1]; unfold hC1Out; simp [stA]
  have shC1 : σC1.sh (sk x 113) = (Data.unaryList ((hs ++ (xs ++ [tg])).take 16)).length := by
    rw [hσC1]; unfold hC1Out; simp
  have shC1o : ∀ s, s ≠ sk x 113 → σC1.sh s = σA.sh s := fun s hs => by
    rw [hσC1]; unfold hC1Out; simp [Function.update_apply, hs]
  have clC1 : σC1.cell = σ₀.cell := by rw [hσC1]; unfold hC1Out; simp [clA]
  have hBC1 : ∀ q, σC1.val q ≤ cap := wexec_le cap eC1 hBA
  -- C2
  obtain ⟨τ, c2, eC2, c2le, tA, tB, kC2, stC2, shC2, clC2⟩ := hC2_run cap x σC1 hs xs tg [] hhs hxs
    (by rw [stC1]; exact st113) shC1 c10
    (by rw [kC1 _ (by rw [rv_dK]; omega)]; exact vA _ (by rw [rv_dK]; omega) (by rw [rv_dK]; omega) (by rw [rv_dK]; omega))
    (by rw [kC1 _ (by rw [rv_XA]; omega)]; exact vA _ (by rw [rv_XA]; omega) (by rw [rv_XA]; omega) (by rw [rv_XA]; omega))
    (by rw [kC1 _ (by rw [rv_XB]; omega)]; exact vA _ (by rw [rv_XB]; omega) (by rw [rv_XB]; omega) (by rw [rv_XB]; omega))
    (by rw [kC1 _ (by rw [rv_TM]; omega)]; exact vA _ (by rw [rv_TM]; omega) (by rw [rv_TM]; omega) (by rw [rv_TM]; omega))
    hcl hcs
  have nKH : ∀ i : Fin 32, i.val < 16 → dK ≠ Hb i := fun i hi e => by
    have := congrArg Fin.val e; rw [Hb_val, rv_dK] at this; omega
  refine ⟨τ, _, WExec.seq eA (WExec.seq eC1 eC2), ?_, ?_, ?_, ?_, ?_, tA, tB, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · omega
  · rw [kC2 _ (nKH 0 (by decide)).symm (by decide) (by decide)]; exact c10
  · rw [kC2 _ (nKH 1 (by decide)).symm (by decide) (by decide)]; exact c11
  · rw [kC2 _ (nKH 8 (by decide)).symm (by decide) (by decide)]; exact c18
  · rw [kC2 _ (nKH 13 (by decide)).symm (by decide) (by decide)]; exact c113
  · have n1 : SGb 8 ≠ dK := by decide
    have n2 : SGb 8 ≠ XA := by decide
    have n3 : SGb 8 ≠ XB := by decide
    rw [kC2 _ n1 n2 n3, kC1 _ (by rw [SGb_val]; omega)]; exact v8
  · intro r hr
    have n1 : r ≠ dK := fun e => by rw [e, rv_dK] at hr; omega
    have n2 : r ≠ XA := fun e => by rw [e, rv_XA] at hr; omega
    have n3 : r ≠ XB := fun e => by rw [e, rv_XB] at hr; omega
    rw [kC2 _ n1 n2 n3, kC1 _ (by omega)]
    exact vA _ (by omega) (by omega) (by omega)
  · rw [stC2, stC1]
  · intro s hs
    rw [shC2 s hs, shC1o s hs]
    by_cases h0 : s = sk x 0
    · subst h0; rw [shA0, sh0]
    · exact shA s h0
  · rw [clC2, clC1]; rfl
  · exact wexec_le cap eC2 hBC1

/-- Phases D1, the aux numbers and D3, run: the aux filter's parameters and numbers, the index layout. -/
theorem hD_run (σ : WState (LNS x) LNR) (nc capT ee sx mo kh : ℕ) (Pa : GapParams)
    (h0 : σ.val (Hb 0) = nc) (h1 : σ.val (Hb 1) = capT) (h13 : σ.val (Hb 13) = ee) (hA : σ.val XA = sx)
    (hMo : σ.val (Hb 8) = mo) (h8 : σ.val (SGb 8) = kh)
    (hz : ∀ r : Fin LNR, (r.val < 250 ∨ 400 ≤ r.val ∨ r.val = 322 ∨ r.val = 374) → σ.val r = 0)
    (hPl : Pa.len = 2 * sx) (hPc : Pa.cap = (nc + 1) * 4096 * capT) (hPe : Pa.errExp = ee) (hPc1 : 1 ≤ Pa.cap)
    (hcD1 : ee + 2 * sx + (nc + 1) * 4096 * capT + (nc + 1) * 4096 + capT + 10 ≤ cap)
    (hcG1 : Pa.cap * 32 + 2 ≤ cap) (hcG2 : Pa.len + 8 ≤ cap) (hcG3 : Pa.errExp + 4 ≤ cap)
    (hcG4 : 2 ^ (Pa.seedBits + 1) ≤ cap) (hcG5 : Pa.labelBits + Pa.fieldBits + Pa.walkLen + 512 ≤ cap)
    (hcD3 : 2 * sx + mo + 2 ^ Pa.seedBits + 2 ^ (2 * kh + 1) + 2 ^ Pa.seedBits * 2 ^ (2 * kh) * 5 + 10 ≤ cap) :
    ∃ τ, WExec cap (.seq (hD1W x) (.seq (hGW x) (hD3W x))) σ τ
        (28 * UnaryPow.sq cap + 1 + (110 * UnaryPow.sq cap + 1 + 1 + 34 * UnaryPow.sq cap)) ∧
      τ.val (G 0) = Pa.cap ∧ τ.val (G 1) = Pa.len ∧ τ.val (G 2) = Pa.errExp ∧ τ.val (G 7) = 2 * sx + mo ∧
      τ.val (G 56) = 2 ^ Pa.seedBits * 2 ^ (2 * kh) * 5 ∧ τ.val (G 55) = 5 ∧ τ.val (G 32) = 0 ∧
      τ.val (G 53) = 2 ^ Pa.seedBits ∧ τ.val (G 52) = 1 ∧ τ.val (G 41) = 1 ∧ τ.val dNC = 1 ∧
      (∀ k, τ.val (H k) = 0) ∧ (∀ r : Fin LNR, (r.val < 250 ∨ (400 ≤ r.val ∧ r.val < 408) ∨ r.val = 374) → τ.val r = 0) ∧
      τ.st = σ.st ∧ τ.sh = σ.sh ∧ τ.cell = σ.cell := by
  have hsq := UnaryPow.sq_ge cap
  have zG : ∀ i : Fin 64, σ.val (G i) = 0 := fun i => hz _ (Or.inr (Or.inl (by rw [G_val]; omega)))
  have zT : σ.val TM = 0 := hz _ (by rw [rv_TM]; omega)
  have e1 := hD1_run cap x σ ee sx nc capT h13 hA h0 h1 zG zT hcD1
  set σ1 := hD1Out x σ ee sx nc capT with hσ1
  have k1G : ∀ i : Fin 64, 3 ≤ i.val → σ1.val (G i) = 0 := fun i hi => by
    rw [hσ1]; unfold hD1Out
    have a0 : i.val ≠ 0 := by omega
    have a1 : i.val ≠ 1 := by omega
    have a2 : i.val ≠ 2 := by omega
    by_cases h58 : i.val = 58
    · simp [Function.update_apply, Fin.ext_iff, G_val, h58]
    · simp [Function.update_apply, Fin.ext_iff, G_val, a0, a1, a2, h58, zG]
  have g0 : σ1.val (G 0) = Pa.cap := by
    rw [hσ1]; unfold hD1Out; simp [Function.update_apply, Fin.ext_iff, G_val, hPc]
  have g1 : σ1.val (G 1) = Pa.len := by
    rw [hσ1]; unfold hD1Out; simp [Function.update_apply, Fin.ext_iff, G_val, hPl]
  have g2 : σ1.val (G 2) = Pa.errExp := by
    rw [hσ1]; unfold hD1Out; simp [Function.update_apply, Fin.ext_iff, G_val, hPe]
  have hzK : ∀ i : Fin 32, 3 ≤ i.val → σ1.val ((KG.trans G) i) = 0 := fun i hi => by
    simp only [Function.Embedding.trans_apply]
    apply k1G
    fin_cases i <;> simp at hi ⊢
  obtain ⟨σ2, hσ2⟩ : ∃ y, y = (((((σ1.setv ((KG.trans G) 3) Pa.prefixBits).setv ((KG.trans G) 4) Pa.labelBits).setv
      ((KG.trans G) 5) Pa.fieldBits).setv ((KG.trans G) 6) Pa.walkLen).setv ((KG.trans G) 20) Pa.seedBits).setv
      ((KG.trans G) 21) (2 ^ Pa.seedBits) := ⟨_, rfl⟩
  have e2 : WExec cap (hGW x) σ1 σ2 (110 * UnaryPow.sq cap + 1) := by
    rw [hσ2]
    unfold hGW
    by_cases hsx : sx = 0
    · have hl0 : Pa.len = 0 := by rw [hPl, hsx]
      exact WExec.ifrF (by rw [g1, hl0]) (GapNums.gapNums0_spec cap (KG.trans G) σ1 Pa
        (by simpa [KG_apply, Function.Embedding.trans_apply] using g0) hl0
        (by simpa [KG_apply, Function.Embedding.trans_apply] using g2) hzK hPc1 (by omega) hcG1 hcG3 hcG4 hcG5)
    · exact WExec.ifrT (by rw [g1, hPl]; omega) (GapNums.gapNums_spec cap (KG.trans G) σ1 Pa
        (by simpa [KG_apply, Function.Embedding.trans_apply] using g0)
        (by simpa [KG_apply, Function.Embedding.trans_apply] using g1)
        (by simpa [KG_apply, Function.Embedding.trans_apply] using g2) hzK hPc1 (by rw [hPl]; omega) (by omega)
        hcG1 hcG2 hcG3 hcG4 hcG5)
  have k1 : ∀ r : Fin LNR, (∀ i : Fin 64, r ≠ G i) → σ1.val r = σ.val r := by
    intro r hr
    rw [hσ1]; unfold hD1Out
    simp [Function.update_apply, hr]
  have k2 : ∀ r : Fin LNR, (∀ i : Fin 64, r ≠ G i) → σ2.val r = σ1.val r := by
    intro r hr
    rw [hσ2]
    simp [Function.update_apply, hr]
  have zs : ∀ i : Fin 64, 3 ≤ i.val → i.val ≠ 20 → i.val ≠ 21 → i.val ≠ 3 → i.val ≠ 4 → i.val ≠ 5 → i.val ≠ 6 →
      σ2.val (G i) = 0 := by
    intro i hi a20 a21 a3 a4 a5 a6
    rw [hσ2]
    simp [Function.update_apply, Function.Embedding.trans_apply, KG_apply, Fin.ext_iff, G_val, a20, a21, a3, a4, a5, a6]
    exact k1G i hi
  have g21 : σ2.val (G 21) = 2 ^ Pa.seedBits := by
    rw [hσ2]; simp [Function.Embedding.trans_apply, KG_apply]
  have g1' : σ2.val (G 1) = Pa.len := by
    rw [hσ2]; simp [Function.update_apply, Function.Embedding.trans_apply, KG_apply, Fin.ext_iff, G_val, g1]
  have g0' : σ2.val (G 0) = Pa.cap := by
    rw [hσ2]; simp [Function.update_apply, Function.Embedding.trans_apply, KG_apply, Fin.ext_iff, G_val, g0]
  have g2' : σ2.val (G 2) = Pa.errExp := by
    rw [hσ2]; simp [Function.update_apply, Function.Embedding.trans_apply, KG_apply, Fin.ext_iff, G_val, g2]
  have nGr : ∀ r : Fin LNR, r.val < 408 → ∀ i : Fin 64, r ≠ G i := fun r h i e => by rw [e, G_val] at h; omega
  have v2 : ∀ r : Fin LNR, r.val < 408 → σ2.val r = σ.val r := fun r h => by
    rw [k2 r (nGr r h), k1 r (nGr r h)]
  have e3 := hD3_run cap x σ2 sx mo (2 ^ Pa.seedBits) kh (by rw [g1', hPl]) (by rw [v2 _ (by rw [Hb_val]; omega)]; exact hMo)
    g21 (by rw [v2 _ (by rw [SGb_val]; omega)]; exact h8)
    (zs 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (zs 52 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (zs 53 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (zs 41 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (zs 55 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (zs 57 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (zs 54 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (zs 56 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (zs 58 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (zs 59 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (zs 60 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (by rw [v2 _ (by rw [rv_TM]; omega)]; exact zT)
    (by rw [v2 _ (by rw [rv_dNC]; omega)]; exact hz _ (by rw [rv_dNC]; omega)) hcD3
  set σ3 := hD3Out x σ2 sx mo (2 ^ Pa.seedBits) kh with hσ3
  have k3 : ∀ r : Fin LNR, (∀ i : Fin 64, r ≠ G i) → r ≠ dNC → σ3.val r = σ2.val r := by
    intro r hr hd
    rw [hσ3]; unfold hD3Out
    simp [Function.update_apply, hbT1_apply, hbT2_apply, hbP_apply, hr, hd]
  have gv3 : ∀ i : Fin 64, i.val ≠ 7 → i.val ≠ 52 → i.val ≠ 53 → i.val ≠ 41 → i.val ≠ 55 → i.val ≠ 57 →
      i.val ≠ 54 → i.val ≠ 56 → σ3.val (G i) = σ2.val (G i) := by
    intro i a1 a2 a3 a4 a5 a6 a7 a8
    rw [hσ3]; unfold hD3Out
    simp [Function.update_apply, hbT1_apply, hbT2_apply, hbP_apply, Fin.ext_iff, G_val, rv_dNC, a1, a2, a3, a4, a5,
      a6, a7, a8]
    omega
  refine ⟨σ3, WExec.seq e1 (WExec.seq e2 e3), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [gv3 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact g0'
  · rw [gv3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact g1'
  · rw [gv3 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact g2'
  · rw [hσ3]; unfold hD3Out; simp [Function.update_apply, Fin.ext_iff, G_val, rv_dNC]
  · rw [hσ3]; unfold hD3Out; simp [Function.update_apply, hbT1_apply, hbT2_apply, Fin.ext_iff, G_val, rv_dNC]
  · rw [hσ3]; unfold hD3Out; simp [Function.update_apply, Fin.ext_iff, G_val, rv_dNC]
  · rw [gv3 32 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact zs 32 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · rw [hσ3]; unfold hD3Out; simp [Function.update_apply, Fin.ext_iff, G_val, rv_dNC]
  · rw [hσ3]; unfold hD3Out; simp [Function.update_apply, Fin.ext_iff, G_val, rv_dNC]
  · rw [hσ3]; unfold hD3Out; simp [Function.update_apply, Fin.ext_iff, G_val, rv_dNC]
  · rw [hσ3]; unfold hD3Out; simp
  · intro k
    have nk : ∀ i : Fin 64, H k ≠ G i := fun i => HG i k
    rw [k3 _ nk (ndNC_H k).symm, k2 _ nk, k1 _ nk]
    exact hz _ (Or.inr (Or.inl (by rw [H_val]; omega)))
  · intro r hr
    have nG : ∀ i : Fin 64, r ≠ G i := fun i e => by rw [e, G_val] at hr; omega
    have nD : r ≠ dNC := fun e => by rw [e, rv_dNC] at hr; omega
    rw [k3 _ nG nD, k2 _ nG, k1 _ nG]
    exact hz r (by omega)
  · rw [hσ3]; unfold hD3Out; simp [hσ2, hσ1, hD1Out]
  · rw [hσ3]; unfold hD3Out; simp [hσ2, hσ1, hD1Out]
  · rw [hσ3]; unfold hD3Out; simp [hσ2, hσ1, hD1Out]

/-- **The HASH decode's numbers and index split, run** from the unit's entry: the index split (`HVals` at `EU = 5`,
`M = 0`, `N2 = nE`, `nSt = nFlat = nc = 1`), the aux bank's inputs, the streams as at the entry but the data tape's head,
the pipeline registers zero. -/
theorem hN_run (cr : ℕ) (P : Shared.StarParams) (hrP : P.r = Ledger.rowBr cr P.n) (w out : List Bool) (j : ℕ)
    (codes cc : List ℕ) (tl : List Bool) (hw : w = Data.reqW P.n true codes cc tl)
    (hs xs : List ℕ) (tg : ℕ) (hhs : hs.length = 16) (hxs : xs.length ≤ 2) (h0v : hs.getD 0 0 = xs.length)
    (Pa : GapParams) (hPl : Pa.len = 2 * xs.sum) (hPc : Pa.cap = (xs.length + 1) * 4096 * hs.getD 1 0)
    (hPe : Pa.errExp = hs.getD 13 0) (hPc1 : 1 ≤ Pa.cap)
    (hc1 : 2 * w.length + 2 ≤ cap) (hc2 : 2 ^ (natBitLength P.n + 1) ≤ cap) (hc3 : (0 + 4) * (P.n + 3) + 2 * cr + 20 ≤ cap)
    (hcl : ∀ k, (hs ++ (xs ++ [tg])).getD k 0 ≤ cap) (hcs : xs.sum + tg + 4 ≤ cap)
    (hcD1 : hs.getD 13 0 + 2 * xs.sum + (xs.length + 1) * 4096 * hs.getD 1 0 + (xs.length + 1) * 4096 +
      hs.getD 1 0 + 10 ≤ cap)
    (hcG1 : Pa.cap * 32 + 2 ≤ cap) (hcG2 : Pa.len + 8 ≤ cap) (hcG3 : Pa.errExp + 4 ≤ cap)
    (hcG4 : 2 ^ (Pa.seedBits + 1) ≤ cap) (hcG5 : Pa.labelBits + Pa.fieldBits + Pa.walkLen + 512 ≤ cap)
    (hcD3 : 2 * xs.sum + hs.getD 8 0 + 2 ^ Pa.seedBits + 2 ^ (2 * (P.s * (P.r / 2)) + 1) +
      2 ^ Pa.seedBits * 2 ^ (2 * (P.s * (P.r / 2))) * 5 + 10 ≤ cap)
    (hcI : j + 2 ^ Pa.seedBits * 2 ^ (2 * (P.s * (P.r / 2))) * 5 + 2 ^ Pa.seedBits + 30 ≤ cap) :
    ∃ τ c, WExec cap (hNW x cr) (CellLoopD.blankCellD x w out j (Data.unaryList (hs ++ (xs ++ [tg])))) τ c ∧
      c ≤ hNCost P.n w.length cr cap ∧
      HVals x τ j (2 ^ Pa.seedBits * 2 ^ (2 * (P.s * (P.r / 2))) * 5) 5 0 (2 ^ Pa.seedBits) 1 1 1 ∧
      τ.val (G 0) = Pa.cap ∧ τ.val (G 1) = Pa.len ∧ τ.val (G 2) = Pa.errExp ∧ τ.val (G 7) = 2 * xs.sum + hs.getD 8 0 ∧
      τ.st = (CellLoopD.blankCellD x w out j (Data.unaryList (hs ++ (xs ++ [tg])))).st ∧
      (∀ s, s ≠ sk x 113 → τ.sh s = (CellLoopD.blankCellD x w out j (Data.unaryList (hs ++ (xs ++ [tg])))).sh s) ∧
      τ.cell = false ∧ (∀ q : Fin LNR, q.val < 250 → τ.val q = 0) ∧
      (∀ q : Fin LNR, 400 ≤ q.val → q.val < 408 → τ.val q = 0) ∧ τ.val TM = 0 ∧ (∀ q, τ.val q ≤ cap) := by
  have hsq := UnaryPow.sq_ge cap
  obtain ⟨τ1, c1, e1, c1le, t0, t1, t8m, t13, tA, tB, t8, tz, st1, sh1, cl1, bd1⟩ :=
    hAC_run cap x cr P hrP w out j codes cc tl hw hs xs tg hhs hxs h0v hc1 hc2 hc3 hcl hcs
  obtain ⟨τ2, e2, g0, g1, g2, g7, g56, g55, g32, g53, g52, g41, gNC, gH, gz, st2, sh2, cl2⟩ :=
    hD_run cap x τ1 xs.length (hs.getD 1 0) (hs.getD 13 0) xs.sum (hs.getD 8 0) (P.s * (P.r / 2)) Pa t0 t1 t13 tA t8m t8 tz
      hPl hPc hPe hPc1 hcD1 hcG1 hcG2 hcG3 hcG4 hcG5 hcD3
  have n2B : sk x 2 ≠ sk x 113 := fun e => absurd (sk_inj x e) (by decide)
  have n20 : sk x 2 ≠ sk x 0 := fun e => absurd (sk_inj x e) (by decide)
  have n21 : sk x 2 ≠ sk x 1 := fun e => absurd (sk_inj x e) (by decide)
  have hs2 : τ2.st (sk x 2) = List.replicate j true := by
    rw [st2, st1]; simp [CellLoopD.blankCellD, blankCell, n2B, n20, n21]
  have hh2 : τ2.sh (sk x 2) = 0 := by
    rw [sh2, sh1 _ n2B]; simp [CellLoopD.blankCellD, blankCell, n21]
  have hbd2 : ∀ q, τ2.val q ≤ cap := wexec_le cap e2 bd1
  obtain ⟨τ3, e3, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, az, k3, st3, sh3a, sh3, cl3⟩ :=
    idxA_spec x cap τ2 j (2 ^ Pa.seedBits * 2 ^ (2 * (P.s * (P.r / 2))) * 5) 5 0 hs2 hh2 g56 g55 g32 gH (by omega)
      (by omega)
  simp only [Nat.zero_add] at a0 a2 a3 a4 a6 a7 a9
  have hw5 : j % 5 < 5 := Nat.mod_lt _ (by omega)
  have hv3 : (j % 5 - 1) % (0 + 3) < 3 := Nat.mod_lt _ (by omega)
  have hr3 : (j % 5 - 1) / (0 + 3) ≤ j % 5 - 1 := Nat.div_le_self _ _
  have he5 : j / 5 ≤ j := Nat.div_le_self _ _
  obtain ⟨τ4, e4, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, kLow, bz, k4, st4, sh4, cl4⟩ :=
    idxB_spec x cap τ3 (j / 5) ((j % 5 - 1) % (0 + 3)) ((j % 5 - 1) / (0 + 3)) 0 (2 ^ Pa.seedBits) 1 1 1 a4 a7 a8 a9
      (by rw [k3 _ (fun k => HG 53 k)]; exact g53) (by rw [k3 _ (fun k => HG 52 k)]; exact g52)
      (by rw [k3 _ (fun k => HG 41 k)]; exact g41) (by rw [k3 _ (fun k => (ndNC_H k).symm)]; exact gNC) az
      (Nat.one_le_two_pow) le_rfl le_rfl (by omega)
  have kτ : ∀ r : Fin LNR, (∀ k, H k ≠ r) → τ4.val r = τ2.val r := fun r h => by rw [k4 r h, k3 r h]
  refine ⟨τ4, _, WExec.seq e1 (WExec.seq e2 (WExec.seq e3 e4)), ?_,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, bz⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold hNCost; omega
  · rw [kLow 0 (by decide)]; exact a0
  · rw [kLow 1 (by decide)]; exact a1
  · rw [kLow 2 (by decide)]; exact a2
  · rw [kLow 3 (by decide)]; exact a3
  · rw [kLow 4 (by decide)]; exact a4
  · rw [kLow 5 (by decide)]; exact a5
  · rw [kLow 6 (by decide)]; exact a6
  · rw [kLow 7 (by decide)]; exact a7
  · rw [kLow 8 (by decide)]; exact a8
  · rw [kLow 9 (by decide)]; exact a9
  · rw [kτ _ (fun k => HG 0 k)]; exact g0
  · rw [kτ _ (fun k => HG 1 k)]; exact g1
  · rw [kτ _ (fun k => HG 2 k)]; exact g2
  · rw [kτ _ (fun k => HG 7 k)]; exact g7
  · rw [st4, st3, st2, st1]
  · intro s hs
    rw [sh4]
    by_cases h2 : s = sk x 2
    · subst h2; rw [sh3a]; simp [CellLoopD.blankCellD, blankCell, n21]
    · rw [sh3 s h2, sh2, sh1 s hs]
  · rw [cl4, cl3, cl2, cl1]
  · intro q hq
    rw [kτ _ (fun k => H_ne k q (by omega) |>.symm)]
    exact gz q (Or.inl hq)
  · intro q h1 h2
    rw [kτ _ (fun k => H_ne k q (by omega) |>.symm)]
    exact gz q (Or.inr (Or.inl ⟨h1, h2⟩))
  · rw [kτ _ (fun k => H_ne k TM (by rw [rv_TM]; omega) |>.symm)]
    exact gz TM (by rw [rv_TM]; omega)
  · exact wexec_le cap e4 (wexec_le cap e3 hbd2)

end HN

end NearCubicWires.WireExponent3_5.PrimAsm.SymDec
