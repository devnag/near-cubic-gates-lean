import Proof.Wire_3_5.FinalPassFlatRows

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary

variable {ns nr : ℕ} (cap : ℕ)

/-- Read a unary count into `r` and bring the head back: only `r` changes. -/
theorem wreadRew_spec (i : Fin (ns + 1)) (c r : Fin nr) (hcr : c ≠ r) (n : ℕ) (σ : WState ns nr)
    (hones : ∀ k < n, readTapeBit (σ.st i) (σ.sh i + k) = true) (hend : readTapeBit (σ.st i) (σ.sh i + n) = false)
    (hc0 : σ.val c = 0) (hc : n + 1 ≤ cap) (hr : σ.val r + n ≤ cap) :
    WExec cap (.seq (WM.readU i c r) (WM.rewind i c)) σ (σ.setv r (σ.val r + n)) (16 * n + 14) := by
  have s1 := wreadU_spec cap i c r hcr n σ hones hend (by omega) hr
  have s2 := wrewind_spec cap i c (n + 1)
    (((σ.seth i (σ.sh i + n + 1)).setv c (σ.val c + n + 1)).setv r (σ.val r + n))
    (by simp [Function.update_of_ne hcr, hc0]) (by simp [Function.update_of_ne hcr, hc0]; omega)
  refine WExec.cast cap (WExec.seq s1 s2) ?_ (by omega)
  refine WState.eq ?_ rfl ?_ rfl
  · funext j
    by_cases h : j = i
    · subst h; simp
    · simp [Function.update_of_ne h]
  · funext q
    by_cases hq : q = c
    · subst hq; simp [Function.update_of_ne hcr, hc0]
    · by_cases hq' : q = r
      · subst hq'; simp [Function.update_of_ne hq]
      · simp [Function.update_of_ne hq, Function.update_of_ne hq']

theorem readTapeBit_unary_lt (n k : ℕ) (rest : List Bool) (hk : k < n) :
    readTapeBit (List.replicate n true ++ false :: rest) k = true := by
  unfold readTapeBit
  rw [List.getD_append _ _ _ _ (by simpa using hk)]
  simp [hk]

theorem readTapeBit_unary_end (n : ℕ) (rest : List Bool) :
    readTapeBit (List.replicate n true ++ false :: rest) n = false := by
  have h := readTapeBit_mid (List.replicate n true) rest false
  simpa using h

end NearCubicWires.WireExponent3_5.FinalPass.Tm

namespace NearCubicWires.WireExponent3_5.FinalPass.Flat
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.Filt

variable (cap : ℕ)

section Upd
variable (x : LSt)

theorem l_a (n : ℕ) : x.w.setv gA n = { x with a := n }.w := by lst_eq
theorem l_o_emit (b : Bool) :
    ((x.w.sets qO (x.w.st qO ++ [b])).seth qO (x.w.sh qO + 1)).setv gOP (x.w.val gOP + 1) =
      { x with ow := x.ow ++ [b] }.w := by lst_eq

end Upd

/-! ## The visit's words -/

/-- The seed bits `N[pad, 2s)` of the vertex `(x, y)`, from `binary s y ++ binary s x`. -/
def swOf (tf : ℕ) (yb xb : List Bool) : List Bool := (yb ++ xb).drop tf

/-- The diagonal word: the main and lower diagonals reversed, then the upper diagonals. -/
def epOfSw (lb : ℕ) (sw : List Bool) : List Bool := (sw.take lb).reverse ++ (sw.drop lb).take (lb - 1)

/-- The translation word. -/
def bwOfSw (lb : ℕ) (sw : List Bool) : List Bool := (sw.drop (2 * lb - 1)).take lb

theorem epOfSw_length (lb : ℕ) (sw : List Bool) (h : 2 * lb - 1 ≤ sw.length) :
    (epOfSw lb sw).length = lb + (lb - 1) := by
  simp [epOfSw]; omega

theorem bwOfSw_length (lb : ℕ) (sw : List Bool) (h : 2 * lb - 1 + lb ≤ sw.length) : (bwOfSw lb sw).length = lb := by
  simp [bwOfSw]; omega

/-! ## One visit -/

/-- **One visit**: the visit marker, the seed words, `A := J+1`, the level rows. -/
def visitL : TProg :=
  .seq (emitC qO gOP true) (.seq mkSeed (.seq mkEP (.seq mkBW (.seq (.seq (WM.readU qFV gCK gA)
    (WM.rewind qFV gCK)) levelLoop))))

def visitLCost (m lb L n : ℕ) : ℕ :=
  7 + 1 + (mkSeedCost m + 1 + (mkEPCost lb + 1 + (mkBWCost lb + 1 + (16 * n + 14 + 1 +
    (n * (levelCost lb lb L + 4) + 1)))))

/-- The visit's record after the visit. -/
def visitOut (x : LSt) (yb xb restP : List Bool) (n : ℕ) : LSt :=
  { x with ow := x.ow ++ true :: levelRows (epOfSw x.lb (swOf x.tf yb xb)) (bwOfSw x.lb (swOf x.tf yb xb)) x.lb x.L n,
           pmw := frameP (swOf x.tf yb xb) ++ restP, ep := frameP (epOfSw x.lb (swOf x.tf yb xb)) ++ [false],
           bw := frameP (bwOfSw x.lb (swOf x.tf yb xb)) ++ [false] }

theorem visitL_spec (x : LSt) (yb xb pmOld epOld bwOld restY restX restP restF : List Bool) (n : ℕ)
    (hty : x.tauw = frameP yb ++ restY) (htx : x.vw = frameP xb ++ restX) (hpm : x.pmw = frameP pmOld ++ restP)
    (hep : x.ep = frameP epOld ++ [false]) (hbw : x.bw = frameP bwOld ++ [false]) (hk : x.kw = frame (binary x.lb 0))
    (hfv : x.fv = List.replicate n true ++ false :: restF)
    (hyl : yb.length = x.m) (hxl : xb.length = x.m) (hpl : pmOld.length = 2 * x.m - x.tf) (hpad : x.tf ≤ 1)
    (hps : x.tf ≤ x.m) (hepl : epOld.length = x.lb + (x.lb - 1)) (hbwl : bwOld.length = x.lb)
    (hsd : 2 * x.lb - 1 + x.lb ≤ 2 * x.m - x.tf) (hlb : 1 ≤ x.lb) (hn : n ≤ x.lb + 1)
    (htauh : x.tauh = 0) (hpmh : x.pmh = 0) (hvh : x.vh = 0) (hbwh : x.bwh = 0) (heph : x.eph = 0)
    (hg1 : x.g1 = 0) (hg3 : x.g3 = 0) (hs : x.s = 0) (hj : x.j = 0) (hf : x.f = 0) (hns : x.ns = 0) (hck : x.ck = 0)
    (ha : x.a = 0) (hcap : 8 * x.m + 8 * x.lb + 8 ≤ cap) (hO : x.ow.length + 1 + n * (2 * x.L + 1) + 4 < cap) :
    WExec cap visitL x.w (visitOut x yb xb restP n).w (visitLCost x.m x.lb x.L n) := by
  have hswl : (swOf x.tf yb xb).length = 2 * x.m - x.tf := by simp [swOf, hyl, hxl]; omega
  -- the visit marker
  have s0 := emitC_spec cap qO gOP true x.w rfl (by show x.ow.length < cap; omega)
  rw [l_o_emit] at s0
  obtain ⟨y0, hy0⟩ : ∃ y : LSt, y = { x with ow := x.ow ++ [true] } := ⟨_, rfl⟩
  rw [← hy0] at s0
  -- the seed words
  have s1 := mkSeed_spec cap y0 yb xb pmOld restY restX restP (by rw [hy0]; exact hty) (by rw [hy0]; exact htx)
    (by rw [hy0]; exact hpm) (by rw [hy0]; exact hyl) (by rw [hy0]; exact hxl) (by rw [hy0]; exact hpl)
    (by rw [hy0]; exact hpad) (by rw [hy0]; exact hps) (by rw [hy0]; exact htauh) (by rw [hy0]; exact hpmh)
    (by rw [hy0]; exact hvh) (by rw [hy0]; exact hg1) (by rw [hy0]; exact hg3) (by rw [hy0]; exact hs)
    (by rw [hy0]; show 8 * x.m + 8 ≤ cap; omega)
  obtain ⟨y1, hy1⟩ : ∃ y : LSt, y = { x with ow := x.ow ++ [true], pmw := frameP (swOf x.tf yb xb) ++ restP } :=
    ⟨_, rfl⟩
  have e1 : ({ y0 with pmw := frameP ((yb ++ xb).drop y0.tf) ++ restP } : LSt) = y1 := by rw [hy0, hy1]; rfl
  rw [e1] at s1
  have s2 := mkEP_spec cap y1 (swOf x.tf yb xb) epOld restP (by rw [hy1]) (by rw [hy1, hswl]; show 2 * x.lb - 1 ≤ 2 * x.m - x.tf; omega)
    (by rw [hy1]; exact hep) (by rw [hy1]; exact hepl) (by rw [hy1]; exact hlb) (by rw [hy1]; exact hpmh)
    (by rw [hy1]; exact heph) (by rw [hy1]; exact hg1) (by rw [hy1]; exact hg3) (by rw [hy1]; exact hs)
    (by rw [hy1]; show 8 * x.lb + 8 ≤ cap; omega)
  obtain ⟨y2, hy2⟩ : ∃ y : LSt, y = { x with ow := x.ow ++ [true], pmw := frameP (swOf x.tf yb xb) ++ restP, ep := frameP (epOfSw x.lb (swOf x.tf yb xb)) ++ [false] } :=
    ⟨_, rfl⟩
  have e2 : ({ y1 with ep := frameP (((swOf x.tf yb xb).take y1.lb).reverse ++ ((swOf x.tf yb xb).drop y1.lb).take (y1.lb - 1)) ++ [false] } : LSt) = y2 := by
    rw [hy1, hy2]; rfl
  rw [e2] at s2
  have s3 := mkBW_spec cap y2 (swOf x.tf yb xb) bwOld restP (by rw [hy2]) (by rw [hy2, hswl]; show 2 * x.lb - 1 + x.lb ≤ 2 * x.m - x.tf; omega)
    (by rw [hy2]; exact hbw) (by rw [hy2]; exact hbwl) (by rw [hy2]; exact hlb) (by rw [hy2]; exact hpmh)
    (by rw [hy2]; exact hbwh) (by rw [hy2]; exact hg1) (by rw [hy2]; exact hs)
    (by rw [hy2]; show 8 * x.lb + 8 ≤ cap; omega)
  obtain ⟨y3, hy3⟩ : ∃ y : LSt, y = { x with ow := x.ow ++ [true], pmw := frameP (swOf x.tf yb xb) ++ restP, ep := frameP (epOfSw x.lb (swOf x.tf yb xb)) ++ [false], bw := frameP (bwOfSw x.lb (swOf x.tf yb xb)) ++ [false] } :=
    ⟨_, rfl⟩
  have e3 : ({ y2 with bw := frameP (((swOf x.tf yb xb).drop (2 * y2.lb - 1)).take y2.lb) ++ [false] } : LSt) = y3 := by
    rw [hy2, hy3]; rfl
  rw [e3] at s3
  -- the level count
  have s4 := wreadRew_spec cap qFV gCK gA (by decide) n y3.w
    (fun k hk => by rw [hy3]; show readTapeBit x.fv (0 + k) = true; rw [hfv, Nat.zero_add]; exact readTapeBit_unary_lt n k restF hk)
    (by rw [hy3]; show readTapeBit x.fv (0 + n) = false; rw [hfv, Nat.zero_add]; exact readTapeBit_unary_end n restF)
    (by rw [hy3]; exact hck) (by omega) (by rw [hy3]; show x.a + n ≤ cap; omega)
  rw [l_a] at s4
  obtain ⟨y4, hy4⟩ : ∃ y : LSt, y = { x with ow := x.ow ++ [true], pmw := frameP (swOf x.tf yb xb) ++ restP, ep := frameP (epOfSw x.lb (swOf x.tf yb xb)) ++ [false], bw := frameP (bwOfSw x.lb (swOf x.tf yb xb)) ++ [false], a := n } :=
    ⟨_, rfl⟩
  have e4 : ({ y3 with a := y3.w.val gA + n } : LSt) = y4 := by
    rw [hy3, hy4]; simp [ha]
  rw [e4] at s4
  -- the levels
  have hw4 : y4.w = y4.toTSt.w := LSt.w_eq y4 (by rw [hy4]; exact htauh) (by rw [hy4]; exact hpmh)
    (by rw [hy4]; exact hg1) (by rw [hy4]; exact hg3)
  have hepL := epOfSw_length x.lb (swOf x.tf yb xb) (by omega)
  have s5 := levelLoop_spec cap (epOfSw x.lb (swOf x.tf yb xb)) (bwOfSw x.lb (swOf x.tf yb xb)) (by omega) n y4.toTSt
    (by rw [hy4]; show x.lb = _; omega) (by rw [hy4]; exact bwOfSw_length _ _ (by omega))
    (by rw [hy4]; exact hk) (by rw [hy4]) (by rw [hy4]) (by rw [hy4]) (by rw [hy4]; exact hn)
    (by rw [hy4]; exact hs) (by rw [hy4]; exact hj) (by rw [hy4]; exact heph) (by rw [hy4]; exact hbwh)
    (by rw [hy4]; exact hf) (by rw [hy4]; exact hns) (by rw [hy4]; exact hck)
    (by rw [hy4]; show 4 * x.lb + 4 ≤ cap; omega)
    (by rw [hy4]; show (x.ow ++ [true]).length + n * (2 * x.L + 1) + 4 < cap; simp; omega)
    (by omega)
  rw [← hw4] at s5
  have e5 : ({ y4.toTSt with a := 0, ow := y4.toTSt.ow ++ levelRows (epOfSw x.lb (swOf x.tf yb xb)) (bwOfSw x.lb (swOf x.tf yb xb)) y4.toTSt.lb y4.toTSt.L n } : TSt).w = (visitOut x yb xb restP n).w := by
    rw [LSt.w_eq (visitOut x yb xb restP n) htauh hpmh hg1 hg3, hy4]
    unfold visitOut
    congr 1
    cases x
    simp_all
  rw [e5] at s5
  refine WExec.cast cap (WExec.seq s0 (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 s5))))) rfl ?_
  have e : y0.m = x.m ∧ y1.lb = x.lb ∧ y2.lb = x.lb ∧ y4.toTSt.lb = x.lb ∧ y4.toTSt.L = x.L := by
    rw [hy0, hy1, hy2, hy4]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  rw [e.1, e.2.1, e.2.2.1, e.2.2.2.1, e.2.2.2.2]
  unfold visitLCost; omega

end NearCubicWires.WireExponent3_5.FinalPass.Flat
