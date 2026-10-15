import Proof.Gates.Dispatch.WitnessE

/-!
# Fragment (W), part F: the number of roles, the coefficient-window length `LC`, and its walk
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxRecDepth 4000

namespace NearCubicGates.Close.Dispatch

open NearCubicGates NearCubicGates.Close.Counter NearCubicWires NearCubicWires.RepairRepresentation
  NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats

variable {C : Ctx}

/-- Every variable the fragment touches (all in `WitVar`). -/
def wT : List (Fin VV) := [vJ, vPOS, t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, vWF, vBM, vPK, xI, xX, xP, xC, xB, xT,
  xQ, xR, xSum, xS, xRo, xNR, xM, xIc, xA, xW, xV, xRem, xT2, xLC, xT3, xP2]

theorem wT_witVar : ∀ y ∈ wT, WitVar y := by decide

/-! ## The number of roles -/

def setNR : St VV := .ite (.eq vTAG v1) (setK xNR 2) (setK xNR 1)

theorem setNR_spec (a : DS VV) (hc : Cst a) (c : Call) (htag : a.env vTAG = kindTag c.kind) (hW : 2 ≤ C.Wd) :
    Hs C setNR a 8 (fun b => b.env xNR = roleCount c.kind ∧ b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧
      Fr a b [xNR, vJ]) := by
  have h4 : (2 : ℕ) < 2 ^ C.Wd := by
    calc (2 : ℕ) < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ C.Wd := Nat.pow_le_pow_right (by norm_num) hW
  refine Hs.ite (c := .eq vTAG v1) (show vTAG ≠ v1 by decide) (fun he => ?_) (fun he => ?_)
  · have hk : kindTag c.kind = 1 := by simp only [Cnd.eval, decide_eq_true_eq] at he; rw [htag, hc.one] at he; exact he
    have hr : roleCount c.kind = 2 := by cases hck : c.kind <;> simp_all [kindTag, roleCount]
    refine Hs.mono (setK_spec xNR (by decide) 2 a h4) (by norm_num) ?_
    rintro b ⟨b1, b2, b3, b4, b5⟩
    exact ⟨by rw [b1, hr], b2, b3, b4, Cst.of_fr hc b5 (by decide) (by rw [b5 vPOS (by decide), hc.pos, b2]), b5⟩
  · have hk : kindTag c.kind ≠ 1 := by
      simp only [Cnd.eval, decide_eq_false_iff_not] at he; rw [htag, hc.one] at he; exact he
    have hr : roleCount c.kind = 1 := by cases hck : c.kind <;> simp_all [kindTag, roleCount]
    refine Hs.mono (setK_spec xNR (by decide) 1 a (by omega)) (by norm_num) ?_
    rintro b ⟨b1, b2, b3, b4, b5⟩
    exact ⟨by rw [b1, hr], b2, b3, b4, Cst.of_fr hc b5 (by decide) (by rw [b5 vPOS (by decide), hc.pos, b2]), b5⟩

/-! ## The coefficient-window length -/

/-- `LC`: the total width of the coefficient fields. -/
def LCof (c : Call) (p : Params) : ℕ := ((segmentWidths c p).map List.sum).sum

/-- The prefix sum of the first `g` segments. -/
def segSum (c : Call) (p : Params) (g : ℕ) : ℕ := (((segmentWidths c p).take g).map List.sum).sum

theorem segSum_succ (c : Call) (p : Params) (s r : ℕ) (hs : s < p.J) (hr : r < roleCount c.kind) :
    segSum c p (s * roleCount c.kind + r + 1) =
      segSum c p (s * roleCount c.kind + r) + ((circ c r).coeffs.map coefWidth).sum := by
  unfold segSum
  have hg : s * roleCount c.kind + r < (segmentWidths c p).length := by rw [segW_length]; nlinarith
  rw [take_succ_getD _ [] _ hg, List.map_append, List.sum_append, segW_get c p s r hs hr]; simp

theorem segSum_all (c : Call) (p : Params) : segSum c p (p.J * roleCount c.kind) = LCof c p := by
  unfold segSum LCof; rw [← segW_length, List.take_length]

theorem coefWidth_le_int (z : ℤ) : coefWidth z ≤ (Interfaces.intWord z).length := by
  have h := coefWidth_le z
  simp only [Interfaces.intWord, List.length_append, natWord_length]; omega

theorem widths_le (cs : List ℤ) : (cs.map coefWidth).sum ≤ (listWord Interfaces.intWord cs).length := by
  simp only [listWord, List.length_append]
  have : (cs.map coefWidth).sum ≤ (cs.flatMap Interfaces.intWord).length := by
    induction cs with
    | nil => simp
    | cons z cs ih => simp only [List.map_cons, List.sum_cons, List.flatMap_cons, List.length_append]
                      have := coefWidth_le_int z; omega
  omega

theorem roleSum_le (c : Call) :
    ((List.range (roleCount c.kind)).map fun r => ((circ c r).coeffs.map coefWidth).sum).sum ≤
      (callWord c).length := by
  have h1 := widths_le c.first.coeffs
  have h2 := widths_le c.second.coeffs
  have hcw : (listWord Interfaces.intWord c.first.coeffs).length + (listWord Interfaces.intWord c.second.coeffs).length ≤
      (callWord c).length := by
    rw [callWord_eq]; simp only [circuitWord, List.length_append]; omega
  cases hk : c.kind <;> simp [roleCount, hk, circ, List.range_succ] <;> omega

theorem sum_flatMap_const (J : ℕ) (X : List ℕ) : ((List.range J).flatMap fun _ => X).sum = J * X.sum := by
  induction J with
  | zero => simp
  | succ J ih => rw [List.range_succ, List.flatMap_append, List.sum_append, ih]; simp; ring

theorem LCof_eq (c : Call) (p : Params) :
    LCof c p = p.J * ((List.range (roleCount c.kind)).map fun r => ((circ c r).coeffs.map coefWidth).sum).sum := by
  unfold LCof segmentWidths
  rw [List.map_flatMap, sum_flatMap_const, List.map_map]; rfl

theorem LCof_le (c : Call) (p : Params) : LCof c p ≤ p.J * (callWord c).length := by
  rw [LCof_eq]; exact Nat.mul_le_mul_left _ (roleSum_le c)

theorem prefixLength_eq (c : Call) (p : Params) : prefixLength c p = p.k * Target.lambda c.n + LCof c p := by
  rw [LCof_eq]; rfl

theorem segSum_mono (c : Call) (p : Params) {g h : ℕ} (hgh : g ≤ h) : segSum c p g ≤ segSum c p h := by
  unfold segSum
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hgh
  rw [← List.take_append_drop g ((segmentWidths c p).take (g + d)), List.take_take, Nat.min_eq_left (by omega),
    List.map_append, List.sum_append]
  omega

theorem coPos_of (c : Call) (r : ℕ) : coPos c r = if r = 0 then coPos c 0 else coPos c 1 := by
  by_cases hr : r = 0 <;> simp [coPos, hr]

theorem co_at (c : Call) (a : DS VV) (hco1 : a.env vCO1 = coPos c 0) (hco2 : a.env vCO2 = coPos c 1) (r : ℕ) :
    a.env (if r = 0 then vCO1 else vCO2) = coPos c r := by
  rw [coPos_of]; split_ifs <;> assumption

/-! ## The walk computing `LC` -/

def lcAct : St VV := .op (.add xSum xW)

def lcT : List (Fin VV) := [vJ, vPOS, t0, t1, t2, t3, t4, t8, xS, xRo, xM, xIc, xA, xT2, xW, xP, xSum]

theorem lcW_spec (c : Call) (p : Params) (a0 : DS VV) (hc : Cst a0) (hcwc : C.cw = callWord c)
    (hco1 : a0.env vCO1 = coPos c 0) (hco2 : a0.env vCO2 = coPos c 1) (hNR : a0.env xNR = roleCount c.kind)
    (hJ : a0.env pJ = p.J) (hSum : a0.env xSum = 0) (hW : C.cw.length + 4 ≤ C.Wd)
    (hL : 2 ^ (C.cw.length + 2) ≤ 2 ^ C.Wd) (hLC : LCof c p + 1 < 2 ^ C.Wd) (hJW : p.J + 1 < 2 ^ C.Wd) :
    Hs C (allW skipS lcAct) a0 (p.J * (roleCount c.kind * (roleCost C.cw.length 1 1 + 5) + 8) + 4)
      (fun b => b.env xSum = LCof c p ∧ b.wq = a0.wq ∧ b.out = a0.out ∧ Cst b ∧ Fr a0 b lcT) := by
  set R := roleCount c.kind with hRd
  have hR2 : R ≤ 2 := by rw [hRd]; cases c.kind <;> simp [roleCount]
  have h4 : 4 ≤ 2 ^ (C.cw.length + 2) := by
    rw [pow_add]; have := Nat.one_le_two_pow (n := C.cw.length); omega
  let A : ℕ → DS VV → Prop := fun g b => Fr a0 b lcT ∧ b.env xSum = segSum c p g ∧ b.wq = a0.wq ∧ b.out = a0.out
  refine Hs.mono (allW_spec skipS lcAct R p.J A (roleCost C.cw.length 1 1) ?_ ?_ a0
    ⟨Fr.refl _ _, by rw [hSum]; simp [segSum], rfl, rfl⟩ hc hNR hJ (by omega) hJW) le_rfl ?_
  · intro g b v ⟨h1, h2, h3, h4⟩
    exact ⟨⟨Fr.trans h1 (Fr.set b _ (by decide)), by vsimp [h2], h3, h4⟩,
      ⟨Fr.trans h1 (Fr.set b _ (by decide)), by vsimp [h2], h3, h4⟩⟩
  · intro s hs r hr b hA hcb hS hRo hNRb hJb
    obtain ⟨rest, hrest⟩ := coeffs_at c r
    set cs := (circ c r).coeffs with hcs
    set g := s * R + r with hg
    have hco : b.env (if r = 0 then vCO1 else vCO2) = coPos c r := by
      have h1 : b.env vCO1 = coPos c 0 := by rw [hA.1 vCO1 (by decide), hco1]
      have h2 : b.env vCO2 = coPos c 1 := by rw [hA.1 vCO2 (by decide), hco2]
      exact co_at c b h1 h2 r
    have hsg : segSum c p (g + 1) = segSum c p g + (cs.map coefWidth).sum := segSum_succ c p s r hs hr
    have hle : segSum c p (g + 1) ≤ LCof c p := by
      rw [← segSum_all]; exact segSum_mono c p (by rw [hg]; nlinarith)
    refine Hs.mono (seg_of_role skipS lcAct [vJ] [xSum] (by decide) (by decide) s r R p.J cs (coPos c r) rest
      (A g) (A (g + 1)) (fun k e => Fr a0 e lcT ∧ e.env xSum = segSum c p g + ((cs.map coefWidth).take k).sum ∧
        e.wq = a0.wq ∧ e.out = a0.out) ?_ 1 ?_ ?_ 1 ?_ ?_ b hA hcb ⟨hS, hRo, hNRb, hJb⟩ hco
      (by rw [hcwc]; exact hrest) hW hL) le_rfl (fun e h => h)
    · intro d e ⟨h1, h2, h3, h4⟩ hf ho hw
      exact ⟨Fr.trans h1 (Fr.weaken hf (by decide)), by rw [hf xSum (by decide), h2], by rw [hw, h3], by rw [ho, h4]⟩
    · intro d ⟨h1, h2, h3, h4⟩ hcd _ _
      refine Hs.mono (skip_spec d) le_rfl ?_
      rintro e rfl
      exact ⟨⟨Fr.trans h1 (Fr.set d _ (by decide)), by vsimp [h2], h3, h4⟩, rfl,
        Cst.of_fr hcd (Fr.set d _ (show vJ ∈ [vJ] by decide)) (by decide) (by vsimp [hcd.pos]),
        Fr.set d _ (by decide)⟩
    · intro k d e ⟨h1, h2, h3, h4⟩ hf ho hw
      exact ⟨Fr.trans h1 (Fr.weaken hf (by decide)), by rw [hf xSum (by decide), h2], by rw [hw, h3], by rw [ho, h4]⟩
    · intro k hk d ⟨h1, h2, h3, h4⟩ hcd _ hW'
      have hkw : (cs.map coefWidth).take (k + 1) = (cs.map coefWidth).take k ++ [coefWidth cs[k]] := by
        rw [List.take_add_one, List.getElem?_map, List.getElem?_eq_getElem hk]; rfl
      have hbound : segSum c p g + ((cs.map coefWidth).take (k + 1)).sum ≤ LCof c p := by
        have : ((cs.map coefWidth).take (k + 1)).sum ≤ (cs.map coefWidth).sum :=
          (List.take_sublist _ _).sum_le_sum (fun _ _ => Nat.zero_le _)
        omega
      have hb2 : segSum c p g + ((cs.map coefWidth).take k).sum + coefWidth cs[k] ≤ LCof c p := by
        rw [hkw, List.sum_append] at hbound; simpa [Nat.add_assoc] using hbound
      refine Hs.mono (hs_add C xSum xW d (by decide) (by rw [h2, hW']; omega)) le_rfl ?_
      rintro e rfl
      refine ⟨⟨Fr.trans h1 (Fr.set d _ (by decide)), by vsimp [h2, hW', hkw]; ring, h3, h4⟩, rfl,
        Cst.of_fr hcd (Fr.set d _ (show xSum ∈ [xSum] by decide)) (by decide) (by vsimp [hcd.pos]),
        Fr.set d _ (by decide)⟩
    · intro e ⟨h1, h2, h3, h4⟩
      refine ⟨h1, ?_, h3, h4⟩
      rw [h2, List.take_of_length_le (by simp), hsg]
  · rintro b ⟨⟨h1, h2, h3, h4⟩, h5⟩
    refine ⟨by rw [h2, segSum_all], h3, h4, h5, h1⟩

end NearCubicGates.Close.Dispatch
