import SourceAdapters.ShortPCP.MaskMachineSearch
import SourceAdapters.ShortPCP.MaskMachineTable

/-!
# The mask machine: listing the multiset `S`

 (proof of `lem:small-bias`): "For `a, b ∈ 𝔽_{2^m}` let `σ_{a,b} ∈ {0,1}^r` have coordinates `a^j·b`";
proof of `thm:short-pcp-ours`: `|S| = 2^{2m}`; the listing order of Step 3 is `a` outer, `b` inner, over the masks
`< 2^m` (`Field6.masksOf`). For each pair the machine prints `frame σ_{a,b}`: coordinate `j` is the inner product
(`dotS`) of the power word `w_j` (`w_0 = 1`, `w_{j+1} = fmulShift p m w_j a`, `fmulS`) with `b`; `sigma_eq_bits`
identifies this with `Amplified.sigma m r a b` through `MasksSpec.sigma_eq_words` and `GF.fmulShift_spec`.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.ShortPCP.MaskMachine

open NearCubicGates.Close.Cells NearCubicWires.WireExponent3_5 NearCubicWires
open NearCubicGates.Adapters.Joins NearCubicGates.Adapters.Joins.SingleRun
open NearCubicGates.Adapters.ShortPCP.OracleCircuitPCP

/-! ## The reference: power words and `σ_{a,b}` -/

/-- The power words `w_j = a^j` by iterated `fmulShift` from `w_0 = 1`. -/
def powW (p m a : ℕ) : ℕ → ℕ
  | 0 => 1
  | j + 1 => GF2.fmulShift p m (powW p m a j) a

theorem powW_spec {p m a : ℕ} (hp : GF.ModulusOk p m) (hm : 1 ≤ m) (ha : a < 2 ^ m) :
    ∀ j, powW p m a j < 2 ^ m ∧ GF.rep p (powW p m a j) = GF.rep p a ^ j
  | 0 => ⟨Nat.one_lt_two_pow (by omega), by simp [powW]⟩
  | j + 1 => by
    obtain ⟨h1, h2⟩ := powW_spec hp hm ha j
    obtain ⟨h3, h4⟩ := GF.fmulShift_spec p m _ a hp h1 ha
    exact ⟨h3, by rw [powW, h4, h2, pow_succ]⟩

theorem wordDot_eq (m x y : ℕ) : wordDot m x y = decide (dotPar x y m = 1) := by
  unfold wordDot dotPar
  rw [Fin.sum_univ_eq_sum_range (fun i => (x.testBit i && y.testBit i).toNat) m]

theorem ofFn_eq_range {α : Type} (r : ℕ) (g : ℕ → α) : List.ofFn (fun j : Fin r => g j.val) = (List.range r).map g := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp

/-- **`σ_{a,b}` as the machine prints it.** -/
theorem sigma_eq_bits (m r a b : ℕ) (ha : a < 2 ^ m) (hb : b < 2 ^ m) :
    Amplified.sigma m r a b =
      (List.range r).map fun j => decide (dotPar (powW (Amplified.modulus m) m a j) b m = 1) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · unfold Amplified.sigma
    rw [← ofFn_eq_range r (fun j => decide (dotPar (powW (Amplified.modulus 0) 0 a j) b 0 = 1))]
    congr 1
  · rw [sigma_eq_words (powW (Amplified.modulus m) m a)
      (fun j _ => powW_spec (firstPrimitive_ok hm) hm ha j) hb]
    rw [← ofFn_eq_range r (fun j => decide (dotPar (powW (Amplified.modulus m) m a j) b m = 1))]
    congr 1
    funext j
    rw [wordDot_eq]

theorem frame_eq_flatMap (l : List Bool) : RepairOrdinary.frame l = l.flatMap (fun b => [true, b]) ++ [false] := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [RepairOrdinary.frame, ih]

/-- The printed multiset: `a` outer, `b` inner, each `frame σ_{a,b}`. -/
theorem masks_flatten (Z r m : ℕ) :
    (((List.range Z).flatMap fun a => (List.range Z).map fun b => Amplified.sigma m r a b).map
        RepairOrdinary.frame).flatten =
      (List.range Z).flatMap fun a => (List.range Z).flatMap fun b => RepairOrdinary.frame (Amplified.sigma m r a b) := by
  simp [List.flatMap, List.map_flatten, List.flatten_flatten, List.map_map, Function.comp_def]

/-! ## Variables -/

def eA : Var := ⟨84, by decide⟩
def eB : Var := ⟨85, by decide⟩
def eW : Var := ⟨86, by decide⟩
def eJ : Var := ⟨87, by decide⟩

/-! ## One mask: `frame σ_{a,b}` -/

/-- Print the bit held (as `0`/`1`) in `dB`. -/
def emitDB : Sc := .ite (.eq dB v1) (.op (.emit true)) (.op (.emit false))

theorem emitDB_spec (C : Ctx) (a : Ds) (hone : a.env v1 = 1) :
    Runs C emitDB a 2 [] [decide (a.env dB = 1)] (fun _ => True) := by
  by_cases h : a.env dB = 1
  · refine Runs.iteT (wf_eq (by decide)) (by simp [h, hone]) ?_ (by norm_num)
    exact (r_emit C [] a true).mono le_rfl (List.Subset.refl _) (fun _ _ _ => trivial) |>.wout (by simp [h])
  · refine Runs.iteF (wf_eq (by decide)) (by simp [h, hone]) ?_ (by norm_num)
    exact (r_emit C [] a false).mono le_rfl (List.Subset.refl _) (fun _ _ _ => trivial) |>.wout (by simp [h])

/-- One coordinate: `[true, w_j · b]`, then `w_{j+1} := w_j · a`. -/
def sigBody : Sc :=
  .seq (.op (.emit true)) (.seq (.op (.copy dX eW)) (.seq (.op (.copy dY eB)) (.seq dotS (.seq emitDB
  (.seq (.op (.copy mX eW)) (.seq (.op (.copy mY eA)) (.seq fmulS (.seq (.op (.copy eW mZ)) (.op (.inc eJ))))))))))

/-- **One mask.** `frame σ_{a,b}` for `a = eA`, `b = eB`, `r = vR`. -/
def sigS (vr : Var) : Sc :=
  .seq (.op (.copy eW v1)) (.seq (.op (.zero eJ)) (.seq (.loop (.lt eJ vr) sigBody) (.op (.emit false))))

def sigSet : List Var := [eW, eJ, dX, dY, mX, mY] ++ dotSet ++ fmulSet

def sigPass (m : ℕ) : ℕ := dotCost m + fmulCost m + 30

def sigCost (m r : ℕ) : ℕ := r * (sigPass m + 2) + 10

/-- The bits of `σ_{a,b}` as printed. -/
def sigBits (p m r a b : ℕ) : List Bool := (List.range r).map fun j => decide (dotPar (powW p m a j) b m = 1)

theorem sigS_spec (C : Ctx) (vr : Var) (hvr : vr ∉ sigSet) (a : Ds) (m p r : ℕ) (hc : FCtx a m p)
    (hp : 1 ≤ m → GF.ModulusOk p m) (hA : a.env eA < 2 ^ m) (hR : a.env vr = r) (hm : m + 1 < C.Wd)
    (hW : 2 ≤ C.Wd) (hr : r < 2 ^ C.Wd) :
    Runs C (sigS vr) a (sigCost m r) sigSet (RepairOrdinary.frame (sigBits p m r (a.env eA) (a.env eB)))
      (fun _ => True) := by
  set A := a.env eA with hAdef
  set B := a.env eB with hBdef
  let Inv : ℕ → Ds → Prop := fun j b => b.env eW = powW p m A j ∧ b.env eJ = j
  have hloop : ∀ s, Fx sigSet [] a s → Inv 0 s → Runs C (.loop (.lt eJ vr) sigBody) s (r * (sigPass m + 2) + 2)
      sigSet ((List.range r).flatMap fun j => [true, decide (dotPar (powW p m A j) B m = 1)]) (Inv r) := by
    intro s fs hs
    refine Runs.loopNF (wf_lt (fun h => hvr (by rw [← h]; decide))) r (sigPass m) _ Inv s
      (fun j hj b hfb ⟨b1, b2⟩ => ?_) (fun b hfb ⟨_, b2⟩ => ?_) hs
    · have hfa := fs.trans hfb
      have bc : FCtx b m p := hc.of_fx hfa (by decide)
      have bR : b.env vr = r := by rw [hfa.env vr hvr, hR]
      have bA : b.env eA = A := by rw [hfa.env eA (by decide)]
      have bB : b.env eB = B := by rw [hfa.env eB (by decide)]
      refine ⟨by simp [b2, bR, hj], ?_⟩
      have hwlt : 1 ≤ m → powW p m A j < 2 ^ m := fun h1 => (powW_spec (hp h1) h1 hA j).1
      refine Runs.wout (w := true :: ([decide (dotPar (powW p m A j) B m = 1)] ++ [])) ?_ (by simp)
      unfold sigBody
      have f0 := Fx.refl sigSet b
      refine Runs.emit1B f0 (r_emit C sigSet b true) (fun f0 => ?_) (by unfold sigPass; omega)
      refine Runs.op1B f0 (r_copy C sigSet _ dX eW (by decide) (by decide)) (fun f0 => ?_) (by unfold sigPass; omega)
      refine Runs.op1B f0 (r_copy C sigSet _ dY eB (by decide) (by decide)) (fun f0 => ?_) (by unfold sigPass; omega)
      refine Runs.callS0B f0 (dotS_spec C _ m p (bc.of_fx f0 (by decide)) hm hW) (by decide)
        (fun c dl f1 hq => ?_) (by unfold sigPass; omega)
      have cdot : c.env dB = dotPar (powW p m A j) B m := by
        rw [hq]; norm_env; rw [b1, bB]
      have cW : c.env eW = powW p m A j := by rw [dl.env eW (by decide)]; norm_env; exact b1
      have cJ : c.env eJ = j := by rw [dl.env eJ (by decide)]; norm_env; exact b2
      have cc : FCtx c m p := bc.of_fx f1 (by decide)
      have hem := emitDB_spec C c cc.one
      rw [cdot] at hem
      refine Runs.callSB (n := 2) f1 hem (List.nil_subset _) (fun d el f2 _ => ?_) (by unfold sigPass; omega)
      have dW : d.env eW = powW p m A j := by rw [el.env eW (by simp), cW]
      have dJ : d.env eJ = j := by rw [el.env eJ (by simp), cJ]
      have dA : d.env eA = A := by rw [f2.env eA (by decide), bA]
      refine Runs.op1B f2 (r_copy C sigSet _ mX eW (by decide) (by decide)) (fun f2 => ?_) (by unfold sigPass; omega)
      refine Runs.op1B f2 (r_copy C sigSet _ mY eA (by decide) (by decide)) (fun f2 => ?_) (by unfold sigPass; omega)
      refine Runs.callS0B f2 (fmulS_spec C _ m p (bc.of_fx f2 (by decide)) hp (fun h1 => by
          norm_env; rw [dW]; exact hwlt h1) hm hW) (by decide)
        (fun e fl f3 he => ?_) (by unfold sigPass; omega)
      have eZ : e.env mZ = powW p m A (j + 1) := by
        rw [he]; norm_env; rw [dW, dA]; rfl
      have eJ' : e.env eJ = j := by rw [fl.env eJ (by decide)]; norm_env; exact dJ
      refine Runs.op1B f3 (r_copy C sigSet _ eW mZ (by decide) (by decide)) (fun f3 => ?_) (by unfold sigPass; omega)
      refine Runs.lastB f3 (r_inc C sigSet _ eJ (by decide) (by norm_env; rw [eJ']; omega)) (fun _ => ?_)
        (by unfold sigPass; omega)
      exact ⟨by norm_env; exact eZ, by norm_env; rw [eJ']⟩
    · have hfa := fs.trans hfb
      have bR : b.env vr = r := by rw [hfa.env vr hvr, hR]
      simp [b2, bR]
  unfold sigS
  have f0 := Fx.refl sigSet a
  refine Runs.op1B f0 (r_copy C sigSet a eW v1 (by decide) (by decide)) (fun f0 => ?_) (by unfold sigCost; omega)
  refine Runs.op1B f0 (r_zero C sigSet _ eJ (by decide)) (fun f0 => ?_) (by unfold sigCost; omega)
  refine Runs.wout (Runs.callSB f0 (hloop _ f0 ⟨by norm_env; exact hc.one, by norm_env⟩) (List.Subset.refl _)
    (fun b _ _ _ => Runs.last (r_emit C sigSet b false) (fun _ => trivial) (by unfold sigCost; omega))
    (by unfold sigCost; omega)) ?_
  rw [frame_eq_flatMap, sigBits, List.flatMap_map]

/-! ## All masks: `a` outer, `b` inner -/

def rowS : Sc := .seq (.op (.zero eB)) (.loop (.lt eB vT) (.seq (sigS vR) (.op (.inc eB))))

def rowSet : List Var := eB :: sigSet

def rowPass (m r : ℕ) : ℕ := sigCost m r + 4

def rowCost (m r : ℕ) : ℕ := 2 ^ m * (rowPass m r + 2) + 6

theorem rowS_spec (C : Ctx) (a : Ds) (m p r : ℕ) (hc : FCtx a m p) (hp : 1 ≤ m → GF.ModulusOk p m)
    (hA : a.env eA < 2 ^ m) (hR : a.env vR = r) (hm : m + 1 < C.Wd) (hW : 2 ≤ C.Wd) (hr : r < 2 ^ C.Wd) :
    Runs C rowS a (rowCost m r) rowSet
      ((List.range (2 ^ m)).flatMap fun b => RepairOrdinary.frame (sigBits p m r (a.env eA) b)) (fun _ => True) := by
  have hpw : 2 ^ m < 2 ^ C.Wd := Nat.pow_lt_pow_right (by norm_num) (by omega)
  set A := a.env eA with hAdef
  unfold rowS
  have f0 := Fx.refl rowSet a
  refine Runs.op1B f0 (r_zero C rowSet a eB (by decide)) (fun f0 => ?_) (by unfold rowCost; omega)
  refine (Runs.loopNF (wf_lt (by decide)) (2 ^ m) (rowPass m r)
    (fun b => RepairOrdinary.frame (sigBits p m r A b)) (fun j b => b.env eB = j) _
    (fun j hj b hfb hb => ?_) (fun b hfb hb => ?_) (by norm_env)).mono (by unfold rowCost; omega)
    (List.Subset.refl _) (fun _ _ _ => trivial)
  · have hfa := f0.trans hfb
    have bc : FCtx b m p := hc.of_fx hfa (by decide)
    refine ⟨by simp [hb, bc.T, hj], ?_⟩
    refine Runs.wout (Runs.callSB (Fx.refl rowSet b) (sigS_spec C vR (by decide) b m p r bc hp
      (by rw [hfa.env eA (by decide)]; exact hA) (by rw [hfa.env vR (by decide), hR]) hm hW hr) (by decide)
      (fun d dl _ _ => Runs.last (r_inc C rowSet d eB (by decide) (by rw [dl.env eB (by decide), hb]; omega))
        (fun _ => (by norm_env; rw [dl.env eB (by decide), hb])) (by unfold rowPass; omega))
      (by unfold rowPass; omega)) ?_
    rw [hb, hfa.env eA (by decide), List.append_nil]
  · have bc : FCtx b m p := hc.of_fx (f0.trans hfb) (by decide)
    simp [hb, bc.T]

def allS : Sc := .seq (.op (.zero eA)) (.loop (.lt eA vT) (.seq rowS (.op (.inc eA))))

def allSet : List Var := eA :: rowSet

def allPass (m r : ℕ) : ℕ := rowCost m r + 4

def allCost (m r : ℕ) : ℕ := 2 ^ m * (allPass m r + 2) + 6

/-- The printed list of all masks. -/
def allBits (p m r : ℕ) : List Bool :=
  (List.range (2 ^ m)).flatMap fun a => (List.range (2 ^ m)).flatMap fun b => RepairOrdinary.frame (sigBits p m r a b)

theorem allS_spec (C : Ctx) (a : Ds) (m p r : ℕ) (hc : FCtx a m p) (hp : 1 ≤ m → GF.ModulusOk p m)
    (hR : a.env vR = r) (hm : m + 1 < C.Wd) (hW : 2 ≤ C.Wd) (hr : r < 2 ^ C.Wd) :
    Runs C allS a (allCost m r) allSet (allBits p m r) (fun _ => True) := by
  have hpw : 2 ^ m < 2 ^ C.Wd := Nat.pow_lt_pow_right (by norm_num) (by omega)
  unfold allS
  have f0 := Fx.refl allSet a
  refine Runs.op1B f0 (r_zero C allSet a eA (by decide)) (fun f0 => ?_) (by unfold allCost; omega)
  refine (Runs.loopNF (wf_lt (by decide)) (2 ^ m) (allPass m r)
    (fun a => (List.range (2 ^ m)).flatMap fun b => RepairOrdinary.frame (sigBits p m r a b))
    (fun j b => b.env eA = j) _
    (fun j hj b hfb hb => ?_) (fun b hfb hb => ?_) (by norm_env)).mono (by unfold allCost; omega)
    (List.Subset.refl _) (fun _ _ _ => trivial)
  · have hfa := f0.trans hfb
    have bc : FCtx b m p := hc.of_fx hfa (by decide)
    refine ⟨by simp [hb, bc.T, hj], ?_⟩
    refine Runs.wout (Runs.callSB (Fx.refl allSet b) (rowS_spec C b m p r bc hp (by rw [hb]; exact hj)
      (by rw [hfa.env vR (by decide), hR]) hm hW hr) (by decide)
      (fun d dl _ _ => Runs.last (r_inc C allSet d eA (by decide) (by rw [dl.env eA (by decide), hb]; omega))
        (fun _ => (by norm_env; rw [dl.env eA (by decide), hb])) (by unfold allPass; omega))
      (by unfold allPass; omega)) ?_
    rw [hb, List.append_nil]
  · have bc : FCtx b m p := hc.of_fx (f0.trans hfb) (by decide)
    simp [hb, bc.T]

/-- **The printed list is the multiset `S` of Step 3**: with `p = Amplified.modulus m`, `allBits` is the flattened
list of the framed `σ_{a,b}` of `masksOf`. -/
theorem allBits_eq (r f n K1 b1 : ℕ) :
    let m := Amplified.mDeg (r ^ 2 * n * K1 * f ^ b1)
    allBits (Amplified.modulus m) m r = ((masksOf r f n K1 b1).map RepairOrdinary.frame).flatten := by
  intro m
  unfold masksOf allBits
  rw [masks_flatten]
  apply List.flatMap_congr
  intro a ha
  apply List.flatMap_congr
  intro b hb
  rw [sigma_eq_bits m r a b (List.mem_range.1 ha) (List.mem_range.1 hb)]
  rfl

end NearCubicGates.Adapters.ShortPCP.MaskMachine
