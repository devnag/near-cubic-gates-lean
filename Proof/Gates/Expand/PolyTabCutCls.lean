import Proof.Gates.Expand.PolyTabTail4b
import Proof.Gates.Expand.PolyTabCls4

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8000

namespace NearCubicGates.Close.Expand.PolyTab

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.WordPrograms
open NearCubicGates.Close.CounterMachine NearCubicGates.Close.TabMachine
open NearCubicWires.WireExponent3_5.UnionMachine.RegRat (mulCost)
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)

variable (E : ExpandMachine)

/-! ## Atoms -/

theorem lc_XD : LCls 1 (fun r => Xr r ^ r.F.degree) :=
  lc_mono lc_lam (fun r => by unfold Lam; exact Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _))

theorem lc_xsK : LCls 1 (fun r => (xsK E r).length) := by
  refine lc_mono (f := fun r => (E.expand ⟨r.V, r.F⟩).length * (1 + r.V * (r.k + r.s + 2))) ?_
    (fun r => codeRecs_len E r)
  have := lc_P E; have := lc_V; have := lc_k; have := lc_s; lcs_to

theorem lc_hsK : LCls 1 (fun r => (hsK E r).length) := lc_mono lc_two_pow_k (fun r => hsK_len_le E r)

theorem lc_tsK : LCls 1 (fun r => (tsK E r).length) := lc_mono (lc_P E) (fun r => (tsK_len E r).le)

theorem cuts_leX (r : TabReq) : (tabT E r).exactCuts.length ≤ Lam r :=
  (tabT E r).exactCuts_length_le_pow r.B r.F.degree (fun i => r.hB i) (E.ok ⟨r.V, r.F⟩).nodup
    (E.ok ⟨r.V, r.F⟩).degree

theorem lc_cutsX : LCls 1 (fun r => (tabT E r).exactCuts.length) := lc_mono lc_lam (cuts_leX E)

theorem stream_lenX (r : TabReq) : (EquationRowCuts.stream (Wdk E r) (tabT E r).exactCuts).length ≤
    (tabT E r).exactCuts.length * ((r.s + 2) * (2 * (Wdk E r + 1) + 1)) := by
  unfold EquationRowCuts.stream
  rw [List.length_flatMap]
  refine sum_le_len_mul _ _ _ (fun c hc => ?_)
  have hl := (tabT E r).exactCuts_lengths c hc
  unfold MatrixScoreBatch.cutWord MatrixScoreBatch.fields
  rw [flatMap_len_const _ _ (2 * (Wdk E r + 1) + 1) (fun z _ => by
    simp [frame_length, MatrixScoreBatch.signMagnitude, binary_length])]
  simp only [List.length_append, List.length_cons, List.length_nil, hl.1, hl.2]
  have : (r.s + 1) / 2 + r.s / 2 + (0 + 1 + 1) ≤ r.s + 2 := by omega
  exact Nat.mul_le_mul_right _ this

theorem lc_stream : LCls 1 (fun r => (EquationRowCuts.stream (Wdk E r) (tabT E r).exactCuts).length) := by
  refine lc_mono (f := fun r => (tabT E r).exactCuts.length * ((r.s + 2) * (2 * (Wdk E r + 1) + 1))) ?_
    (stream_lenX E)
  have := lc_cutsX E; have := lc_s; have := lc_Wdk E; lcs_to

theorem lc_marks : LCls 1 (fun r => (marks (srcHdr ((r.s + 1) / 2) (Wdk E r) (tabT E r).exactCuts.length
    (decide (r.s % 2 = 1)))).length) := by
  refine lc_mono (f := fun r => 2 * ((2 * ((r.s + 1) / 2 + 1) + 1) + (2 * (Wdk E r + 1) + 1) +
    (2 * ((tabT E r).exactCuts.length + 1) + 1) + 1)) ?_ (fun r => ?_)
  · have := lc_cutsX E; have := lc_s; have := lc_Wdk E; lcs_to
  simp only [marks, srcHdr, List.length_flatMap, List.length_cons, List.length_nil, Nat.zero_add, List.map_const',
    List.sum_replicate, smul_eq_mul, List.length_append, natWord_len]
  have h1 := nbl_le ((r.s + 1) / 2)
  have h2 := nbl_le (Wdk E r)
  have h3 := nbl_le (tabT E r).exactCuts.length
  omega
theorem lc_deg : LCls 0 (fun r : TabReq => r.F.degree) := lc_le_tabSz le_tabSz_D

/-! ## The per-step bounds -/

theorem lc_SBf : LCls 10 (fun r => SBf E r) := by
  have := lc_xsK E; have := lc_mTr; have := lc_XD; have := lc_deg; have := lc_s; have := lc_k; have := lc_Wk E
  simp only [SBf, occACost, restrictCost, dotBodyCost, copyStep, compileCost, preCost, mainCost, lvlCost,
    TabMachine.headCost, visitCost, childCost, TabMachine.bodyCost, BinW.divCost, mulCost, occBCost, occB1Cost,
    exBodyCost, exInnerCost, tupleCost, tOuterCost, tInnerCost, occB2Cost, occB3Cost]
  lcs_to

theorem lc_CSk : LCls 10 (fun r => CSk E r) := lc_mono (lc_SBf E) (fun r => CSk_le E r)

theorem lc_BBk : LCls 10 (fun r => BBk E r) := by
  refine lc_mono (f := fun r => BBf r) ?_ (fun r => BBk_le' E r)
  have := lc_XD; have := lc_deg; have := lc_s
  simp only [BBf]
  lcs_to

theorem lc_MBf : LCls 30 (fun r => MBf E r) := by
  have := lc_xsK E; have := lc_mTr; have := lc_XD; have := lc_deg; have := lc_s; have := lc_k; have := lc_Wk E
  have := lc_Wdk E; have := lc_CSk E; have := lc_BBk E
  simp only [MBf, monoStepCost, monoPreCost, monoStackCost, stackAllCost, stackOneCost, baseCost, sumBodyCost,
    oneFieldCost, fieldBodyCost, SInt.smulCost]
  lcs_to

theorem lc_CMk : LCls 30 (fun r => CMk E r) := lc_mono (lc_MBf E) (fun r => CMk_le E r)

/-- **The cut machine's cost class.** -/
theorem cutCls : TabCls (fun r => cutMCost (Wk E r) r.s (hsK E r).length (tsK E r).length (xsK E r).length (CMk E r)
    (EquationRowCuts.stream (Wdk E r) (tabT E r).exactCuts).length ((r.s + 1) / 2) (Wdk E r)
    (tabT E r).exactCuts.length) := by
  refine tabCls_of_lcls (a := 60) ?_ (by norm_num)
  have := lc_xsK E; have := lc_hsK E; have := lc_tsK E; have := lc_CMk E; have := lc_stream E; have := lc_cutsX E
  have := lc_marks E; have := lc_s; have := lc_Wk E; have := lc_Wdk E
  simp only [cutMCost, pointCost, srcHeadCost, wnCost, srcTailCost]
  lcs_to

end NearCubicGates.Close.Expand.PolyTab
