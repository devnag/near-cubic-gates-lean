import Proof.Gates.Expand.PolyTabTail3
import Proof.Gates.Expand.PolyTabCls2
import Proof.Supplier.EquationRowProducer
import Proof.Hierarchy.CompetitorCountTableBounds

set_option autoImplicit false

namespace NearCubicGates.Close.Expand.PolyTab

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.CounterMachine NearCubicGates.Close.TabMachine

/-! ## `TabCls` closure -/

theorem tc_mono {f g : TabReq → ℕ} (hg : TabCls g) (h : ∀ r, f r ≤ g r) : TabCls f := by
  obtain ⟨C, e, hC⟩ := hg; exact ⟨C, e, fun r => (h r).trans (hC r)⟩

theorem tc_add {f g : TabReq → ℕ} (hf : TabCls f) (hg : TabCls g) : TabCls (fun r => f r + g r) := by
  obtain ⟨C1, e1, h1⟩ := hf
  obtain ⟨C2, e2, h2⟩ := hg
  refine ⟨C1 + C2, e1 + e2, fun r => ?_⟩
  have ht := tabSz_pos r
  have t1 : tabSz r ^ e1 ≤ tabSz r ^ (e1 + e2) := Nat.pow_le_pow_right ht (by omega)
  have t2 : tabSz r ^ e2 ≤ tabSz r ^ (e1 + e2) := Nat.pow_le_pow_right ht (by omega)
  calc f r + g r ≤ C1 * 2 ^ r.s * tabSz r ^ e1 + C2 * 2 ^ r.s * tabSz r ^ e2 := Nat.add_le_add (h1 r) (h2 r)
    _ ≤ C1 * 2 ^ r.s * tabSz r ^ (e1 + e2) + C2 * 2 ^ r.s * tabSz r ^ (e1 + e2) := by gcongr
    _ = (C1 + C2) * 2 ^ r.s * tabSz r ^ (e1 + e2) := by ring

theorem tc_lcls {a : ℕ} {f : TabReq → ℕ} (h : LCls a f) (ha : a ≤ 100) : TabCls f := tabCls_of_lcls h ha

/-- `2^s` times a polynomial in `tabSz`. -/
theorem tc_pow_mul {g : TabReq → ℕ} (hg : LCls 0 g) : TabCls (fun r => 2 ^ r.s * g r) := by
  obtain ⟨C, e, hC⟩ := hg
  refine ⟨C, e, fun r => ?_⟩
  have := hC r
  simp only [pow_zero, Nat.mul_one] at this
  calc 2 ^ r.s * g r ≤ 2 ^ r.s * (C * tabSz r ^ e) := Nat.mul_le_mul_left _ this
    _ = C * 2 ^ r.s * tabSz r ^ e := by ring

/-! ## Atoms -/

theorem lc_d : LCls 0 (fun r : TabReq => (r.s + 1) / 2) :=
  lc_le_tabSz (fun r => by have := le_tabSz_s r; have := tabSz_pos r; omega)

section Back
variable (E : ExpandMachine)

theorem cuts_le_lam (r : TabReq) : (tabT E r).exactCuts.length ≤ Lam r :=
  (tabT E r).exactCuts_length_le_pow r.B r.F.degree (tabT_bounds E r).gates (tabT_bounds E r).nodup
    (tabT_bounds E r).degree

theorem lc_cuts : LCls 1 (fun r => (tabT E r).exactCuts.length) := lc_mono lc_lam (cuts_le_lam E)

theorem cutWord_len (r : TabReq) (p : ℕ) (c : MatrixScoreBatch.Cut) (hc : c ∈ (tabT E r).exactCuts) :
    (MatrixScoreBatch.cutWord p c).length = (r.s + 2) * (2 * p + 3) := by
  obtain ⟨hl, hr⟩ := (tabT E r).exactCuts_lengths c hc
  unfold MatrixScoreBatch.cutWord MatrixScoreBatch.fields
  rw [List.length_flatMap]
  simp only [frame_length, MatrixScoreBatch.signMagnitude_length]
  simp [hl, hr]
  have hs : (r.s + 1) / 2 + r.s / 2 = r.s := by omega
  calc (r.s + 1) / 2 * (2 * (p + 1) + 1) + (r.s / 2 * (2 * (p + 1) + 1) + (2 * (p + 1) + 1 + (2 * (p + 1) + 1)))
      = ((r.s + 1) / 2 + r.s / 2 + 2) * (2 * p + 3) := by ring
    _ = (r.s + 2) * (2 * p + 3) := by rw [hs]

theorem stream_len (r : TabReq) (p : ℕ) :
    (EquationRowCuts.stream p (tabT E r).exactCuts).length = (tabT E r).exactCuts.length * ((r.s + 2) * (2 * p + 3)) := by
  unfold EquationRowCuts.stream
  exact flatMap_len_const _ _ _ (fun c hc => cutWord_len E r p c hc)

theorem natWord_le' (v : ℕ) : (natWord v).length ≤ 2 * v + 3 := by
  rw [natWord_len]; have := Nat.log_le_self 2 v; unfold natBitLength; omega

theorem source_le (r : TabReq) :
    (EquationRowRaw.source (inp E r)).length ≤
      2 * ((r.s + 1) / 2) + 2 * Wdk E r + 2 * (tabT E r).exactCuts.length + 10 +
        (tabT E r).exactCuts.length * ((r.s + 2) * (2 * Wdk E r + 3)) := by
  unfold EquationRowRaw.source EquationHeaderRead.word EquationHeaderRead.header
  simp only [List.length_append, List.length_cons]
  rw [inp_cuts, inp_d, inp_p, stream_len]
  have := natWord_le' ((r.s + 1) / 2)
  have := natWord_le' (Wdk E r)
  have := natWord_le' (tabT E r).exactCuts.length
  omega

/-- The non-exponential part of the back end and the register program. -/
def backPoly (r : TabReq) : ℕ :=
  100 * ((r.s + 1) / 2 + Wdk E r + 10) +
    (600000 * ((r.s + 1) / 2 + Wdk E r + (tabT E r).exactCuts.length + 1) ^ 3 +
      24 * (2 * ((r.s + 1) / 2) + 2 * Wdk E r + 2 * (tabT E r).exactCuts.length + 10 +
        (tabT E r).exactCuts.length * ((r.s + 2) * (2 * Wdk E r + 3))) + 7) +
    34 * ((r.s + 1) / 2 + 2 * Wdk E r + 5) + 100

theorem lc_backPoly : LCls 3 (backPoly E) := by
  have h1 := lc_d
  have h2 := lc_Wdk E
  have h3 := lc_cuts E
  have h4 := lc_s
  unfold backPoly
  lcs_to

theorem two_pow_2d (r : TabReq) : 2 ^ (2 * ((r.s + 1) / 2)) ≤ 2 * 2 ^ r.s := by
  calc 2 ^ (2 * ((r.s + 1) / 2)) ≤ 2 ^ (r.s + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ = 2 * 2 ^ r.s := by ring

theorem nOf_le (r : TabReq) : nOf (inp E r) ≤ 2 ^ (2 * ((r.s + 1) / 2)) := by
  unfold nOf
  rw [inp_d, two_mul, pow_add]
  split_ifs
  · exact Nat.mul_le_mul_left _ (Nat.div_le_self _ _)
  · exact le_rfl

/-- The printer's budget (the shared `CompetitorCountTable.budget_bound`). -/
theorem printer_le (a : WilliamsAlgorithm) (r : TabReq) :
    CompetitorCountTable.budget a (EquationRow.request (inp E r)) (qOf (inp E r)) + 1 ≤
      2 ^ r.s * (8 * CompetitorCountTable.coefficient a *
        ((r.s + 1) / 2 + Wdk E r + 2) ^ CompetitorCrossScheduler.exponent a) := by
  have hw : qOf (inp E r) ≤ CompetitorSameBucketColdDense.width (EquationRow.request (inp E r)) := by
    rw [CompetitorSameBucketColdDense.width_eq]; unfold qOf; simp [EquationRow.request]; omega
  have h := CompetitorCountTable.budget_bound a (EquationRow.request (inp E r)) (qOf (inp E r)) hw
  unfold CompetitorCountTable.envelope at h
  have hU : (EquationRow.request (inp E r)).U = 2 ^ ((r.s + 1) / 2) := rfl
  have hd : (EquationRow.request (inp E r)).d + (EquationRow.request (inp E r)).p + 1 = (r.s + 1) / 2 + Wdk E r + 2 := by
    simp [EquationRow.request, inp_d, inp_p]; omega
  rw [hU, hd] at h
  have h1 : 1 ≤ 2 ^ ((r.s + 1) / 2) := Nat.one_le_two_pow
  have h2 : (2 ^ ((r.s + 1) / 2) + 1) ^ 2 ≤ 4 * 2 ^ (2 * ((r.s + 1) / 2)) := by
    have : 2 ^ ((r.s + 1) / 2) + 1 ≤ 2 * 2 ^ ((r.s + 1) / 2) := by omega
    calc (2 ^ ((r.s + 1) / 2) + 1) ^ 2 ≤ (2 * 2 ^ ((r.s + 1) / 2)) ^ 2 := Nat.pow_le_pow_left this 2
      _ = 4 * 2 ^ (2 * ((r.s + 1) / 2)) := by rw [mul_pow, ← pow_mul, mul_comm ((r.s + 1) / 2) 2]; norm_num
  have h3 : (2 ^ ((r.s + 1) / 2) + 1) ^ 2 ≤ 8 * 2 ^ r.s := by have := two_pow_2d r; omega
  calc _ ≤ CompetitorCountTable.coefficient a * (2 ^ ((r.s + 1) / 2) + 1) ^ 2 *
        ((r.s + 1) / 2 + Wdk E r + 2) ^ CompetitorCrossScheduler.exponent a := h
    _ ≤ CompetitorCountTable.coefficient a * (8 * 2 ^ r.s) *
        ((r.s + 1) / 2 + Wdk E r + 2) ^ CompetitorCrossScheduler.exponent a := by gcongr
    _ = _ := by ring

theorem decode_le' (N q P : ℕ) (hN : N ≤ 2 * P) (hP : 1 ≤ P) : decodeCost N q ≤ P * (2 * (100 * q + 100) + 30) := by
  unfold decodeCost
  have h1 : N * (100 * q + 100) ≤ (2 * P) * (100 * q + 100) := Nat.mul_le_mul_right _ hN
  have e : P * (2 * (100 * q + 100) + 30) = (2 * P) * (100 * q + 100) + 30 * P := by ring
  omega

theorem qOf_inp (r : TabReq) : qOf (inp E r) = (r.s + 1) / 2 + 2 * Wdk E r + 5 := by unfold qOf; rw [inp_d, inp_p]

/-- **The back part of the tail's cost is in the tabulation class.** -/
theorem backCls (a : WilliamsAlgorithm) :
    TabCls (fun r => bregsCost ((r.s + 1) / 2) (Wdk E r) + 1 + backCost a (inp E r)) := by
  have hP := tc_lcls (lc_backPoly E) (by norm_num)
  have hd := lc_d
  have hW := lc_Wdk E
  have hE1 : TabCls (fun r => 2 ^ r.s * (70 * (2 * ((r.s + 1) / 2) + 1))) := tc_pow_mul (by lcs_to)
  have hE2 : TabCls (fun r => 2 ^ r.s * (8 * CompetitorCountTable.coefficient a *
      ((r.s + 1) / 2 + Wdk E r + 2) ^ CompetitorCrossScheduler.exponent a)) := tc_pow_mul (by lcs_to)
  have hQ : LCls 0 (fun r => qOf (inp E r)) :=
    lc_mono (by lcs_to : LCls 0 (fun r => (r.s + 1) / 2 + 2 * Wdk E r + 5)) (fun r => (qOf_inp E r).le)
  have hE3 : TabCls (fun r => 2 ^ r.s * (2 * (100 * qOf (inp E r) + 100) + 30)) :=
    tc_pow_mul (by lcs_to)
  refine tc_mono (tc_add hP (tc_add hE1 (tc_add hE2 hE3))) (fun r => ?_)
  have hb := two_pow_2d r
  have hn := (nOf_le E r).trans hb
  have hpr := printer_le E a r
  have hsrc := source_le E r
  have hs1 : 1 ≤ 2 ^ r.s := Nat.one_le_two_pow
  have hq := qOf_inp E r
  have hm : EquationRowRaw.mass (inp E r) = (r.s + 1) / 2 + Wdk E r + (tabT E r).exactCuts.length + 1 := by
    unfold EquationRowRaw.mass; rw [inp_d, inp_p, inp_cuts]
  -- the register program
  have hB : bregsCost ((r.s + 1) / 2) (Wdk E r) ≤ 100 * ((r.s + 1) / 2 + Wdk E r + 10) +
      2 ^ r.s * (70 * (2 * ((r.s + 1) / 2) + 1)) := by
    unfold bregsCost
    have : (2 * ((r.s + 1) / 2) + 1) * (25 * 2 ^ (2 * ((r.s + 1) / 2)) + 20) ≤
        (2 * ((r.s + 1) / 2) + 1) * (70 * 2 ^ r.s) := Nat.mul_le_mul_left _ (by omega)
    have e : (2 * ((r.s + 1) / 2) + 1) * (70 * 2 ^ r.s) = 2 ^ r.s * (70 * (2 * ((r.s + 1) / 2) + 1)) := by ring
    omega
  -- the decoder
  have hD : decodeCost (nOf (inp E r)) (qOf (inp E r)) ≤ 2 ^ r.s * (2 * (100 * qOf (inp E r) + 100) + 30) :=
    decode_le' _ _ _ hn hs1
  -- the back end
  have hU : EquationRowFramed.uniformBudget (inp E r) ≤
      600000 * ((r.s + 1) / 2 + Wdk E r + (tabT E r).exactCuts.length + 1) ^ 3 +
      24 * (2 * ((r.s + 1) / 2) + 2 * Wdk E r + 2 * (tabT E r).exactCuts.length + 10 +
        (tabT E r).exactCuts.length * ((r.s + 2) * (2 * Wdk E r + 3))) + 7 := by
    unfold EquationRowFramed.uniformBudget
    rw [hm]
    gcongr
  unfold backCost backPoly
  omega

end Back

end NearCubicGates.Close.Expand.PolyTab
