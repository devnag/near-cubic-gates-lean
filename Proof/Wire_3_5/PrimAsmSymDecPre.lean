import Proof.Wire_3_5.PrimAsmSymDecReq2

/-! # PA (d)-SYM decode, part 9: the request's rewinds and the carriers' counts

The decode's prefix around `reqParse`: measure the framed request and rewind it (`preA`), rewind it again after the parse
(`preB`, by `2|w| + 1 ≥` the parse's head), read the carriers' counts `cx₀, cx₁` (at most two carriers) from the data
stream and rewind it (`carPass`).

* registers `LEN XA XB CR TT TM` (`369 … 374`, the decode's scratch range);
* `preAW` / **`preA_spec`**, `preBW` / **`preB_spec`**, `carW` / **`car_spec`**.

Paper quantities of the main type: the request word's length and the carriers' sizes (the SYM pool's carrier slices,
`Records.symSlices`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.PrimAsm.SymDec
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicWires.WireExponent3_5.PrimAsm.SparseNum NearCubicWires.WireExponent3_5.PrimAsm.FiltNum

def LEN : Fin LNR := ⟨369, by decide⟩
def XA : Fin LNR := ⟨370, by decide⟩
def XB : Fin LNR := ⟨371, by decide⟩
def CR : Fin LNR := ⟨372, by decide⟩
def TT : Fin LNR := ⟨373, by decide⟩
def TM : Fin LNR := ⟨374, by decide⟩

section Pre
variable (cap : ℕ) (x : ℕ)

/-- Measure the request and rewind it. -/
def preAW : WM (LNS x) LNR :=
  .seq (measW (sk x 0) LEN) (.seq (FinalPass.Hash4.wcopyR LEN CR TM) (.seq (dbl CR TM) (WM.rewind (sk x 0) CR)))

theorem preA_spec (w : List Bool) (σ : WState (LNS x) LNR) (hst : σ.st (sk x 0) = frame w) (hsh : σ.sh (sk x 0) = 0)
    (hL : σ.val LEN = 0) (hC : σ.val CR = 0) (hT : σ.val TM = 0) (hcap : 2 * w.length + 2 ≤ cap) :
    WExec cap (preAW x) σ (σ.setv LEN w.length) (4 * UnaryPow.sq cap) := by
  have d1 : CR ≠ LEN := by decide
  have d2 : TM ≠ LEN := by decide
  have d3 : TM ≠ CR := by decide
  have hl := UnaryPow.lin_le_sq cap
  have e1 := meas_spec cap (sk x 0) LEN w 0 σ hst hsh hL (by omega)
  refine WExec.cast cap (WExec.seq e1 (WExec.seq (SparseNum.copy1 cap LEN CR TM (by decide) (by decide) (by decide)
    (0 + w.length) _ (by simp) (by simp [Function.update_apply, hC, d1]) (by simp [Function.update_apply, hT, d2])
    (by omega)) (WExec.seq (FiltNum.dbl1 cap CR TM (by decide) (0 + w.length) _ (by simp)
    (by simp [Function.update_apply, hT, d2, d3]) (by omega)) (wrewind_spec cap (sk x 0) CR (2 * (0 + w.length)) _
    (by simp) (by simp; omega))))) ?_ (by omega)
  apply WState.eq
  · funext i; by_cases hi : i = sk x 0
    · subst hi; simp [hsh]
    · simp [Function.update_apply, hi]
  · rfl
  · funext r
    by_cases hr : r = CR
    · subst hr; simp [Function.update_apply, hC, d1]
    · by_cases hr' : r = LEN
      · subst hr'; simp [Function.update_apply, Ne.symm d1]
      · simp [Function.update_apply, hr, hr']
  · rfl

/-- Rewind the request after the parse (its head within `2|w| + 1`). -/
def preBW : WM (LNS x) LNR :=
  .seq (FinalPass.Hash4.wcopyR LEN CR TM) (.seq (dbl CR TM) (.seq (.inc CR) (WM.rewind (sk x 0) CR)))

theorem preB_spec (wl : ℕ) (σ : WState (LNS x) LNR) (hL : σ.val LEN = wl) (hC : σ.val CR = 0) (hT : σ.val TM = 0)
    (hh : σ.sh (sk x 0) ≤ 2 * wl + 1) (hcap : 2 * wl + 2 ≤ cap) :
    WExec cap (preBW x) σ (σ.seth (sk x 0) 0) (5 * UnaryPow.sq cap) := by
  have d1 : CR ≠ LEN := by decide
  have d2 : TM ≠ LEN := by decide
  have d3 : TM ≠ CR := by decide
  have hl := UnaryPow.lin_le_sq cap
  refine WExec.cast cap (WExec.seq (SparseNum.copy1 cap LEN CR TM (by decide) (by decide) (by decide) wl σ hL hC hT
    (by omega)) (WExec.seq (FiltNum.dbl1 cap CR TM (by decide) wl _ (by simp)
    (by simp [Function.update_apply, hT, d3]) (by omega)) (WExec.seq (SparseNum.inc1 cap CR (2 * wl) _ (by simp)
    (by omega)) (wrewind_spec cap (sk x 0) CR (2 * wl + 1) _ (by simp) (by simp; omega))))) ?_ (by omega)
  apply WState.eq
  · funext i; by_cases hi : i = sk x 0
    · subst hi; simp; omega
    · simp [Function.update_apply, hi]
  · rfl
  · funext r
    by_cases hr : r = CR
    · subst hr; simp [hC]
    · simp [Function.update_apply, hr]
  · rfl

/-- Read the carriers' counts (at most two) into `XA`, `XB`, then rewind the data stream. -/
def carW : WM (LNS x) LNR :=
  .seq (FinalPass.Hash4.wcopyR dNC TT TM) (.seq (.ifr TT (.seq (.dec TT) (.seq (readItemW (sk x 113) XA)
    (.ifr TT (.seq (.dec TT) (readItemW (sk x 113) XB)) .skip))) .skip)
    (.seq (FinalPass.Hash4.wcopyR XA CR TM) (.seq (addTo XB CR TM) (.seq (addTo dNC CR TM)
      (WM.rewind (sk x 113) CR)))))

theorem unaryList_cons' (c : ℕ) (cs : List ℕ) :
    Data.unaryList (c :: cs) = List.replicate c true ++ false :: Data.unaryList cs := by
  simp [Data.unaryList]

/-- **The carriers' counts**: `XA = cx₀`, `XB = cx₁` (`0` past the carriers), the data stream's head back at `0`. -/
theorem car_spec (cx cy : List ℕ) (hcx : cx.length ≤ 2) (σ : WState (LNS x) LNR)
    (hst : σ.st (sk x 113) = Data.unaryList (cx ++ cy)) (hsh : σ.sh (sk x 113) = 0) (hNC : σ.val dNC = cx.length)
    (zA : σ.val XA = 0) (zB : σ.val XB = 0) (zC : σ.val CR = 0) (zT : σ.val TT = 0) (zM : σ.val TM = 0)
    (hcap : cx.sum + cx.length + 4 ≤ cap) :
    WExec cap (carW x) σ ((σ.setv XA (cx.getD 0 0)).setv XB (cx.getD 1 0)) (30 * UnaryPow.sq cap) := by
  have hl := UnaryPow.lin_le_sq cap
  have hsq := UnaryPow.sq_ge cap
  have n1 : TT ≠ dNC := by decide
  have n2 : TM ≠ dNC := by decide
  have n3 : TM ≠ TT := by decide
  have n4 : XA ≠ TT := by decide
  have n5 : XB ≠ TT := by decide
  have n6 : XA ≠ XB := by decide
  have n7 : CR ≠ XA := by decide
  have n8 : CR ≠ XB := by decide
  have n9 : CR ≠ dNC := by decide
  have n10 : TM ≠ XA := by decide
  have n11 : TM ≠ XB := by decide
  have n12 : TM ≠ CR := by decide
  have n13 : CR ≠ TT := by decide
  have n14 : XA ≠ dNC := by decide
  have n15 : XB ≠ dNC := by decide
  rcases cx with _ | ⟨c0, _ | ⟨c1, _ | ⟨c2, rest⟩⟩⟩
  · -- no carrier
    simp only [List.length_nil] at hNC
    refine WExec.cast cap (WExec.seq (SparseNum.copy1 cap dNC TT TM (by decide) (by decide) (by decide) 0 σ hNC zT zM
      (by omega)) (WExec.seq (WExec.ifrF (by simp) (WExec.skip _)) (WExec.seq (SparseNum.copy1 cap XA CR TM (by decide)
      (by decide) (by decide) 0 _ (by simp [Function.update_apply, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n1.symm, n2.symm, n3.symm, n4.symm, n5.symm, n6.symm, n7.symm, n8.symm, n9.symm, n10.symm, n11.symm, n12.symm, n13.symm, n14.symm, n15.symm, zA, zB, zC, zT, zM, zA, n4]) (by simp [Function.update_apply, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n1.symm, n2.symm, n3.symm, n4.symm, n5.symm, n6.symm, n7.symm, n8.symm, n9.symm, n10.symm, n11.symm, n12.symm, n13.symm, n14.symm, n15.symm, zA, zB, zC, zT, zM, zC, n13])
      (by simp [Function.update_apply, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n1.symm, n2.symm, n3.symm, n4.symm, n5.symm, n6.symm, n7.symm, n8.symm, n9.symm, n10.symm, n11.symm, n12.symm, n13.symm, n14.symm, n15.symm, zA, zB, zC, zT, zM, zM, n3]) (by omega)) (WExec.seq (CapNum.add1 cap XB CR TM (by decide) (by decide)
      (by decide) 0 0 _ (by simp [Function.update_apply, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n1.symm, n2.symm, n3.symm, n4.symm, n5.symm, n6.symm, n7.symm, n8.symm, n9.symm, n10.symm, n11.symm, n12.symm, n13.symm, n14.symm, n15.symm, zA, zB, zC, zT, zM, zB, n5, n8.symm]) (by simp)
      (by simp [Function.update_apply, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n1.symm, n2.symm, n3.symm, n4.symm, n5.symm, n6.symm, n7.symm, n8.symm, n9.symm, n10.symm, n11.symm, n12.symm, n13.symm, n14.symm, n15.symm, zA, zB, zC, zT, zM, zM, n3, n12]) (by omega) (by omega)) (WExec.seq (CapNum.add1 cap dNC CR TM
      (by decide) (by decide) (by decide) 0 (0 + 0) _ (by simp [Function.update_apply, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n1.symm, n2.symm, n3.symm, n4.symm, n5.symm, n6.symm, n7.symm, n8.symm, n9.symm, n10.symm, n11.symm, n12.symm, n13.symm, n14.symm, n15.symm, zA, zB, zC, zT, zM, hNC, n1.symm, n9.symm])
      (by simp) (by simp [Function.update_apply, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n1.symm, n2.symm, n3.symm, n4.symm, n5.symm, n6.symm, n7.symm, n8.symm, n9.symm, n10.symm, n11.symm, n12.symm, n13.symm, n14.symm, n15.symm, zA, zB, zC, zT, zM, zM, n3, n12]) (by omega) (by omega))
      (wrewind_spec cap (sk x 113) CR (0 + 0 + 0) _ (by simp) (by simp <;> omega))))))) ?_ (by omega)
    apply WState.eq
    · funext i; by_cases hi : i = sk x 113
      · subst hi; simp [hsh]
      · simp [Function.update_apply, hi]
    · rfl
    · funext r
      by_cases hr : r = CR
      · subst hr; simp [Function.update_apply, zC, n7, n8]
      · by_cases hr1 : r = TT
        · subst hr1; simp [Function.update_apply, zT, n4.symm, n5.symm, n13.symm]
        · by_cases hr2 : r = XA
          · subst hr2; simp [Function.update_apply, zA, n6, n7.symm, n4]
          · by_cases hr3 : r = XB
            · subst hr3; simp [Function.update_apply, zB, n6.symm, n8.symm, n5]
            · simp [Function.update_apply, hr, hr1, hr2, hr3]
    · rfl
  · -- one carrier
    simp only [List.length_cons, List.length_nil] at hNC
    have hst' : σ.st (sk x 113) = [] ++ List.replicate c0 true ++ false :: Data.unaryList cy := by
      rw [hst]; simp [unaryList_cons']
    simp only [List.sum_cons, List.sum_nil, List.length_cons, List.length_nil] at hcap
    refine WExec.cast cap (WExec.seq (SparseNum.copy1 cap dNC TT TM (by decide) (by decide) (by decide) (0 + 1) σ
      (by rw [hNC]) zT zM (by omega)) (WExec.seq (WExec.ifrT (by simp)
      (WExec.seq (SparseNum.dec1 cap TT (0 + 1) _ (by simp) (by omega))
      (WExec.seq (readItem_spec cap (sk x 113) XA [] (Data.unaryList cy) c0 _ (by simp [hst']) (by simp [hsh])
        (by simp [Function.update_apply, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n1.symm, n2.symm, n3.symm, n4.symm, n5.symm, n6.symm, n7.symm, n8.symm, n9.symm, n10.symm, n11.symm, n12.symm, n13.symm, n14.symm, n15.symm, zA, zB, zC, zT, zM, zA, n4]; omega))
      (WExec.ifrF (by simp [Function.update_apply, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n1.symm, n2.symm, n3.symm, n4.symm, n5.symm, n6.symm, n7.symm, n8.symm, n9.symm, n10.symm, n11.symm, n12.symm, n13.symm, n14.symm, n15.symm, zA, zB, zC, zT, zM, n4.symm]) (WExec.skip _)))))
      (WExec.seq (SparseNum.copy1 cap XA CR TM (by decide) (by decide) (by decide) c0 _
        (by simp [Function.update_apply, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n1.symm, n2.symm, n3.symm, n4.symm, n5.symm, n6.symm, n7.symm, n8.symm, n9.symm, n10.symm, n11.symm, n12.symm, n13.symm, n14.symm, n15.symm, zA, zB, zC, zT, zM, zA]) (by simp [Function.update_apply, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n1.symm, n2.symm, n3.symm, n4.symm, n5.symm, n6.symm, n7.symm, n8.symm, n9.symm, n10.symm, n11.symm, n12.symm, n13.symm, n14.symm, n15.symm, zA, zB, zC, zT, zM, zC, n7, n13])
        (by simp [Function.update_apply, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n1.symm, n2.symm, n3.symm, n4.symm, n5.symm, n6.symm, n7.symm, n8.symm, n9.symm, n10.symm, n11.symm, n12.symm, n13.symm, n14.symm, n15.symm, zA, zB, zC, zT, zM, zM, n3, n10]) (by omega))
      (WExec.seq (CapNum.add1 cap XB CR TM (by decide) (by decide) (by decide) 0 c0 _
        (by simp [Function.update_apply, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n1.symm, n2.symm, n3.symm, n4.symm, n5.symm, n6.symm, n7.symm, n8.symm, n9.symm, n10.symm, n11.symm, n12.symm, n13.symm, n14.symm, n15.symm, zA, zB, zC, zT, zM, zB, n5, n8.symm, n6.symm]) (by simp)
        (by simp [Function.update_apply, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n1.symm, n2.symm, n3.symm, n4.symm, n5.symm, n6.symm, n7.symm, n8.symm, n9.symm, n10.symm, n11.symm, n12.symm, n13.symm, n14.symm, n15.symm, zA, zB, zC, zT, zM, zM, n3, n12, n10]) (by omega) (by omega))
      (WExec.seq (CapNum.add1 cap dNC CR TM (by decide) (by decide) (by decide) (0 + 1) (c0 + 0) _
        (by simp [Function.update_apply, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n1.symm, n2.symm, n3.symm, n4.symm, n5.symm, n6.symm, n7.symm, n8.symm, n9.symm, n10.symm, n11.symm, n12.symm, n13.symm, n14.symm, n15.symm, zA, zB, zC, zT, zM, hNC, n1.symm, n9.symm, n14.symm]) (by simp)
        (by simp [Function.update_apply, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n1.symm, n2.symm, n3.symm, n4.symm, n5.symm, n6.symm, n7.symm, n8.symm, n9.symm, n10.symm, n11.symm, n12.symm, n13.symm, n14.symm, n15.symm, zA, zB, zC, zT, zM, zM, n3, n12, n10]) (by omega) (by omega))
      (wrewind_spec cap (sk x 113) CR (c0 + 0 + (0 + 1)) _ (by simp) (by simp <;> omega))))))) ?_ (by omega)
    apply WState.eq
    · funext i; by_cases hi : i = sk x 113
      · subst hi; simp; omega
      · simp [Function.update_apply, hi]
    · rfl
    · funext r
      by_cases hr : r = CR
      · subst hr; simp [Function.update_apply, zC, n7, n8]
      · by_cases hr1 : r = TT
        · subst hr1; simp [Function.update_apply, zT, n4.symm, n5.symm, n13.symm]
        · by_cases hr2 : r = XA
          · subst hr2; simp [Function.update_apply, zA, n6, n7.symm, n4]
          · by_cases hr3 : r = XB
            · subst hr3; simp [Function.update_apply, zB, n6.symm, n8.symm, n5]
            · simp [Function.update_apply, hr, hr1, hr2, hr3]
    · rfl
  · -- two carriers
    simp only [List.length_cons, List.length_nil] at hNC
    have hst' : σ.st (sk x 113) = [] ++ List.replicate c0 true ++ false :: Data.unaryList (c1 :: cy) := by
      rw [hst]; simp [unaryList_cons']
    have hst'' : σ.st (sk x 113) = (List.replicate c0 true ++ [false]) ++ List.replicate c1 true ++ false ::
        Data.unaryList cy := by
      rw [hst]; simp [unaryList_cons']
    simp only [List.sum_cons, List.sum_nil, List.length_cons, List.length_nil] at hcap
    refine WExec.cast cap (WExec.seq (SparseNum.copy1 cap dNC TT TM (by decide) (by decide) (by decide) (0 + 1 + 1) σ
      (by rw [hNC]) zT zM (by omega)) (WExec.seq (WExec.ifrT (by simp)
      (WExec.seq (SparseNum.dec1 cap TT (0 + 1 + 1) _ (by simp) (by omega))
      (WExec.seq (readItem_spec cap (sk x 113) XA [] (Data.unaryList (c1 :: cy)) c0 _ (by simp [hst']) (by simp [hsh])
        (by simp [Function.update_apply, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n1.symm, n2.symm, n3.symm, n4.symm, n5.symm, n6.symm, n7.symm, n8.symm, n9.symm, n10.symm, n11.symm, n12.symm, n13.symm, n14.symm, n15.symm, zA, zB, zC, zT, zM, zA, n4]; omega))
      (WExec.ifrT (by simp [Function.update_apply, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n1.symm, n2.symm, n3.symm, n4.symm, n5.symm, n6.symm, n7.symm, n8.symm, n9.symm, n10.symm, n11.symm, n12.symm, n13.symm, n14.symm, n15.symm, zA, zB, zC, zT, zM, n4.symm])
        (WExec.seq (SparseNum.dec1 cap TT (0 + 1 + 1 - 1) _ (by simp [Function.update_apply, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n1.symm, n2.symm, n3.symm, n4.symm, n5.symm, n6.symm, n7.symm, n8.symm, n9.symm, n10.symm, n11.symm, n12.symm, n13.symm, n14.symm, n15.symm, zA, zB, zC, zT, zM, n4.symm]) (by omega))
          (readItem_spec cap (sk x 113) XB (List.replicate c0 true ++ [false]) (Data.unaryList cy) c1 _
            (by simp [hst'']) (by simp) (by simp [Function.update_apply, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n1.symm, n2.symm, n3.symm, n4.symm, n5.symm, n6.symm, n7.symm, n8.symm, n9.symm, n10.symm, n11.symm, n12.symm, n13.symm, n14.symm, n15.symm, zA, zB, zC, zT, zM, zB, n5, n6.symm]; omega)))))))
      (WExec.seq (SparseNum.copy1 cap XA CR TM (by decide) (by decide) (by decide) c0 _
        (by simp [Function.update_apply, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n1.symm, n2.symm, n3.symm, n4.symm, n5.symm, n6.symm, n7.symm, n8.symm, n9.symm, n10.symm, n11.symm, n12.symm, n13.symm, n14.symm, n15.symm, zA, zB, zC, zT, zM, zA, n6]) (by simp [Function.update_apply, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n1.symm, n2.symm, n3.symm, n4.symm, n5.symm, n6.symm, n7.symm, n8.symm, n9.symm, n10.symm, n11.symm, n12.symm, n13.symm, n14.symm, n15.symm, zA, zB, zC, zT, zM, zC, n7, n8, n13])
        (by simp [Function.update_apply, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n1.symm, n2.symm, n3.symm, n4.symm, n5.symm, n6.symm, n7.symm, n8.symm, n9.symm, n10.symm, n11.symm, n12.symm, n13.symm, n14.symm, n15.symm, zA, zB, zC, zT, zM, zM, n3, n10, n11]) (by omega))
      (WExec.seq (CapNum.add1 cap XB CR TM (by decide) (by decide) (by decide) c1 c0 _
        (by simp [Function.update_apply, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n1.symm, n2.symm, n3.symm, n4.symm, n5.symm, n6.symm, n7.symm, n8.symm, n9.symm, n10.symm, n11.symm, n12.symm, n13.symm, n14.symm, n15.symm, zA, zB, zC, zT, zM, zB, n8.symm, n6.symm]) (by simp)
        (by simp [Function.update_apply, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n1.symm, n2.symm, n3.symm, n4.symm, n5.symm, n6.symm, n7.symm, n8.symm, n9.symm, n10.symm, n11.symm, n12.symm, n13.symm, n14.symm, n15.symm, zA, zB, zC, zT, zM, zM, n3, n12, n10, n11]) (by omega) (by omega))
      (WExec.seq (CapNum.add1 cap dNC CR TM (by decide) (by decide) (by decide) (0 + 1 + 1) (c0 + c1) _
        (by simp [Function.update_apply, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n1.symm, n2.symm, n3.symm, n4.symm, n5.symm, n6.symm, n7.symm, n8.symm, n9.symm, n10.symm, n11.symm, n12.symm, n13.symm, n14.symm, n15.symm, zA, zB, zC, zT, zM, hNC, n1.symm, n9.symm, n14.symm, n15.symm]) (by simp)
        (by simp [Function.update_apply, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n1.symm, n2.symm, n3.symm, n4.symm, n5.symm, n6.symm, n7.symm, n8.symm, n9.symm, n10.symm, n11.symm, n12.symm, n13.symm, n14.symm, n15.symm, zA, zB, zC, zT, zM, zM, n3, n12, n10, n11]) (by omega) (by omega))
      (wrewind_spec cap (sk x 113) CR (c0 + c1 + (0 + 1 + 1)) _ (by simp) (by simp <;> omega))))))) ?_ (by omega)
    apply WState.eq
    · funext i; by_cases hi : i = sk x 113
      · subst hi; simp; omega
      · simp [Function.update_apply, hi]
    · rfl
    · funext r
      by_cases hr : r = CR
      · subst hr; simp [Function.update_apply, zC, n7, n8]
      · by_cases hr1 : r = TT
        · subst hr1; simp [Function.update_apply, zT, n4.symm, n5.symm, n13.symm]
        · by_cases hr2 : r = XA
          · subst hr2; simp [Function.update_apply, zA, n6, n7.symm, n4]
          · by_cases hr3 : r = XB
            · subst hr3; simp [Function.update_apply, zB, n6.symm, n8.symm, n5]
            · simp [Function.update_apply, hr, hr1, hr2, hr3]
    · rfl
  · simp at hcx

end Pre

end NearCubicWires.WireExponent3_5.PrimAsm.SymDec
