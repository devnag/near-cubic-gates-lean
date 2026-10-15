import Proof.Gates.Expand.PolyTabCls3

/-! # PolyTab cost classes: the head (**`headCost_cls`**: `TabCls (headCost E)`), phase by phase -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8000

namespace NearCubicGates.Close.Expand.PolyTab

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.WordPrograms
open NearCubicGates.Close.CounterMachine NearCubicGates.Close.TabMachine

variable (E : ExpandMachine)

/-- The atoms of the head's costs, as hypotheses for `lcs`. -/
structure HAt : Prop where
  n : LCls 0 (fun r : TabReq => r.n)
  k : LCls 0 (fun r : TabReq => r.k)
  s : LCls 0 (fun r : TabReq => r.s)
  B : LCls 0 (fun r : TabReq => r.B)
  G : LCls 0 (fun r : TabReq => r.G)
  V : LCls 0 (fun r : TabReq => r.V)
  pk : LCls 1 (fun r : TabReq => 2 ^ r.k)
  P : LCls 1 (fun r => (E.expand ⟨r.V, r.F⟩).length)
  ts : LCls 1 (fun r => (ts9 E r).length)
  bud : LCls 4 (fun r => E.budget ⟨r.V, r.F⟩)
  wk : LCls 0 (Wk E)
  wdk : LCls 0 (Wdk E)
  pre : LCls 1 (fun r => (preN r).length)
  Lt : LCls 1 Lt
  tw : LCls 1 (fun r => (tabWord r).length)
  fw : LCls 0 (fun r : TabReq => (formulaWord ⟨r.V, r.F⟩).length)
  tm : LCls 1 (fun r => (termsWord (E.expand ⟨r.V, r.F⟩)).length)
  lk : LCls 1 (ℓk E)
  nm : LCls 0 (fun r => ((preN r).map natBitLength).foldr max 0)
  vt : LCls 0 (fun r => (VTn E r).length)
  o46 : LCls 1 (fun r => ((ts9 E r).flatMap (blk46 (Wk E r + 1) (r.k + r.s + 2) (VTn E r))).length)
  o56 : LCls 1 (fun r => ((ts9 E r).flatMap (blk56 (Wdk E r + 1))).length)
  vr : LCls 0 (fun r => (vtRecs (Wk E r + 1) E r r.V).length)
  cp : LCls 1 (fun r => (((E.expand ⟨r.V, r.F⟩).map cpMonoCost).map fun c => c + 4).sum)

theorem hat : HAt E := ⟨lc_n, lc_k, lc_s, lc_B, lc_G, lc_V, lc_two_pow_k, lc_P E, lc_ts9 E, lc_budget E, lc_Wk E,
  lc_Wdk E, lc_preN, lc_Lt, lc_tabWord, lc_fw, lc_terms E, lc_lk E, lc_nblmax, lc_VTn E, lc_O46 E, lc_O56 E,
  lc_vtRecs E, lc_cpSum E⟩

macro "hats" E:term : tactic => `(tactic| (
  have h := hat $E
  have := h.n; have := h.k; have := h.s; have := h.B; have := h.G; have := h.V; have := h.pk; have := h.P
  have := h.ts; have := h.bud; have := h.wk; have := h.wdk; have := h.pre; have := h.Lt; have := h.tw; have := h.fw
  have := h.tm; have := h.lk; have := h.nm; have := h.vt; have := h.o46; have := h.o56; have := h.vr; have := h.cp))

theorem lc_A1 : LCls 10 (fun r => phA1Cost E r) := by
  hats E
  simp only [phA1Cost, cpRWCost, cpFormCost, Cst, Mh, cpTermsCost, Codec.copyListCost]
  lcs_to

theorem lc_A2 : LCls 10 (fun r => phA2Cost E r) := by
  hats E
  simp only [phA2Cost, Cst, Mh, C4, c8, Ctm, pk, pN, ps]
  lcs_to

theorem lc_vblock : LCls 10 (fun r => vBlockCost (Wk E r + 1) (preN r).length r.G r.n r.k r.s) := by
  hats E
  simp only [vBlockCost, vA1Cost, vA2Cost, vBCost, vC1Cost, vC2Cost, fetchCost, gaCost, emitCost, coordCost]
  lcs_to

theorem lc_B1 : LCls 10 (fun r => phBCost E r) := by
  hats E
  have := lc_vblock E
  simp only [phBCost, initCost, tcCost, hCost, readBinCost, binStepCost]
  lcs_to

theorem lc_mn : LCls 10 (fun r => mnCost (Wk E r + 1) (Wdk E r + 1) (ℓk E r) r.V r.V (r.k + r.s + 2) (VTn E r).length) := by
  hats E
  simp only [mnCost, mACost, mBCost, mCCost, vCost, revCost, readBinCost, binStepCost, copyStep]
  lcs_to

theorem lc_C : LCls 20 (fun r => phCCost E r) := by
  hats E
  have := lc_mn E
  simp only [phCCost, initCost, st9Cost, readBinCost, binStepCost]
  lcs_to

theorem lc_D : LCls 10 (fun r => phD1Cost (Wk E r + 1) (Wdk E r + 1) + 1 + phD2Cost r.s r.k (Wdk E r)) := by
  hats E
  simp only [phD1Cost, phD2Cost, initCost, w1List, wcList, List.length_cons, List.length_nil]
  lcs_to

theorem headCost_lcls : LCls 20 (fun r => headCost E r) := by
  have := lc_A1 E; have := lc_A2 E; have := lc_B1 E; have := lc_C E; have := lc_D E
  simp only [headCost, headABCCost]
  lcs_to

/-- **The head's cost class.** -/
theorem headCost_cls : TabCls (headCost E) := tabCls_of_lcls (headCost_lcls E) (by norm_num)

end NearCubicGates.Close.Expand.PolyTab
