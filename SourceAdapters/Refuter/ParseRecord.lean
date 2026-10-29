import SourceAdapters.Refuter.ParsePrims
import SourceAdapters.Refuter.Assembly

/-!
# Parsing the outer record in `c_0·N` steps (input 7, the record codec, part 2)

proof of `cor:framed-refuter`: "On the record `x_i`, the hierarchy verifier prepares `fr(x_1)` and `fr(w_i)` for the
first simulation … Parsing the outer record … writing these frames, and returning their heads to zero
cost at most `c_0N` steps, for an absolute constant `c_0`. … Their bit representation is independent
of `M`." The record is CLW20's `⟨M,N,z⟩ = 1^M 0 1^{N−M−2−|z|} 0 z` (`record`, `Assembly.lean`).

`parse` reads `fr(x)` once: it counts the leading ones into `A` (the enumeration index `M`), skips the
middle ones, and copies the witness field `z`; it writes `XS := fr(x)` with `z` replaced by `0^g`
(that is `fr(x_1)`, `x_1 = ⟨M,N,0^g⟩`) and `YS := fr(z)`; `TE := N`, `S := g = |z|`; all heads return
to `0`. `parse_spec` gives the exact end state and the cost `≤ 300(N+1)`, with no machine-dependent
coefficient. `record_list` shows the records have this shape whenever `M + 2 + ⌊N/16⌋ ≤ N`.
-/

namespace NearCubicGates.Adapters.Refuter.Mach

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairSource
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms
open NearCubicGates.Adapters.Refuter

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable (cap : ℕ)

/-- The machine index `A`. -/
@[simp] abbrev rAI : Fin NR := 38
/-- The last-record flag. -/
@[simp] abbrev rLS : Fin NR := 39

/-! ## The records as lists -/

theorem getElem_rep_cons (a : ℕ) (rest : List Bool) (j : ℕ) (h : j < (List.replicate a true ++ false :: rest).length) :
    (List.replicate a true ++ false :: rest)[j] =
      if hj : j < a then true else if ha : j = a then false else rest[j - a - 1]'(by simp at h; omega) := by
  by_cases hj : j < a
  · rw [List.getElem_append_left (by simpa using hj)]; simp [hj]
  · rw [List.getElem_append_right (by simp; omega)]
    simp only [List.length_replicate, hj, dite_false]
    by_cases ha : j = a
    · subst ha; simp
    · simp only [ha, dite_false]
      rw [List.getElem_cons]
      split
      · omega
      · first | rfl | (congr 1; omega) | congr 1

/-- **The record of `M` as a list** (CLW20 §4.1 `⟨M,n,z⟩ = 1^M 0 1^{n−M−2−|z|} 0 z`). -/
theorem record_list (M : OrdinaryWeakMachine) (N i : ℕ) (h : machineIndex M + 2 + N / 16 ≤ N) :
    List.ofFn (record M N i) = List.replicate (machineIndex M) true ++
      false :: (List.replicate (N - N / 16 - machineIndex M - 2) true ++ false ::
        List.ofFn (unrank (N / 16) i)) := by
  apply List.ext_getElem
  · simp; omega
  · intro j h1 h2
    rw [getElem_rep_cons]
    simp only [List.getElem_ofFn, record]
    by_cases hj : j < machineIndex M
    · simp [hj]
    · by_cases ha : j = machineIndex M
      · simp [ha]
      · simp only [hj, ha, dite_false]
        rw [getElem_rep_cons]
        by_cases hb : j - machineIndex M - 1 < N - N / 16 - machineIndex M - 2
        · simp only [hb, dite_true]
          have : j + 1 < N - N / 16 := by omega
          simp [this]
        · simp only [hb, dite_false]
          by_cases hc : j - machineIndex M - 1 = N - N / 16 - machineIndex M - 2
          · have : ¬ j + 1 < N - N / 16 := by omega
            have h2 : j + 1 = N - N / 16 := by omega
            simp [hc, this, h2]
          · have : ¬ j + 1 < N - N / 16 := by omega
            have h2 : ¬ j + 1 = N - N / 16 := by omega
            simp only [hc, this, h2, dite_false, List.getElem_ofFn]
            exact congrArg (unrank (N / 16) i) (Fin.ext (by simp; omega))

/-! ## The program -/

/-- Copy a run of ones: `XS ← 1 1`, `C += 1`, two cells on. -/
def onesLoop (C : Fin NR) : Pg :=
  .whs sIN (.seq (pairW sXS true) (.seq (WMX.inc C) (.seq (WMX.fwd sIN) (WMX.fwd sIN))))

def zeroA : Pg := .seq (pairW sXS false) (.seq (WMX.fwd sIN) (WMX.fwd sIN))

def zeroB : Pg := .seq (pairW sXS false) (WMX.fwd sIN)

def zBody : Pg :=
  .seq (WMX.fwd sIN) (.seq (.ifs sIN (.seq (pairW sXS false) (pairW sYS true)) (.seq (pairW sXS false) (pairW sYS false)))
    (.seq (WMX.inc rS) (WMX.fwd sIN)))

def zLoop : Pg := .whs sIN zBody

def term : Pg := .seq (WMX.wr sXS false) (WMX.wr sYS false)

def countN : Pg :=
  .seq (addR rAI rTE rTA) (.seq (addR rTD rTE rTA) (.seq (addR rS rTE rTA) (.seq (WMX.inc rTE) (.seq (WMX.inc rTE) (clr rTD)))))

def rewindP : Pg :=
  .seq (bwdK sIN rTE rTB) (.seq (bwdK sIN rTE rTB) (.seq (bwdK sXS rTE rTB) (.seq (bwdK sXS rTE rTB)
    (.seq (bwdK sYS rTE rTB) (bwdK sYS rTE rTB)))))

def parse : Pg :=
  .seq (WMX.fwd sIN) (.seq (onesLoop rAI) (.seq zeroA (.seq (onesLoop rTD) (.seq zeroB (.seq zLoop
    (.seq term (.seq countN rewindP)))))))

/-! ## The loops -/

/-- The state after `k` ones. -/
def onesSt (σ : St) (C : Fin NR) (P Q : List Bool) (k : ℕ) : St :=
  (((σ.seth sIN (2 * P.length + 1 + 2 * k)).sets sXS (fpre (Q ++ List.replicate k true))).seth sXS
    (2 * (Q.length + k))).setv C (σ.val C + k)

theorem onesLoop_spec (C : Fin NR) (σ : St) (P Q rest : List Bool) (a : ℕ)
    (hX : σ.st sIN = fpre (P ++ List.replicate a true) ++ (true :: false :: rest))
    (hXh : σ.sh sIN = 2 * P.length + 1) (hXS : σ.st sXS = fpre Q) (hXSh : σ.sh sXS = 2 * Q.length)
    (hcap : σ.val C + a < cap) :
    WXExec cap (onesLoop C) σ (onesSt σ C P Q a) (a * 17 + 1) := by
  have h0 : onesSt σ C P Q 0 = σ := by
    apply WState.eq
    · funext j; by_cases a1 : j = sXS
      · subst a1; simp [onesSt, hXSh]
      · by_cases a2 : j = sIN
        · subst a2; simp [onesSt, hXh]
        · simp [onesSt, Function.update_apply, a1, a2]
    · funext j; by_cases a1 : j = sXS
      · subst a1; simp [onesSt, hXS]
      · simp [onesSt, Function.update_apply, a1]
    · funext r; by_cases a1 : r = C
      · subst a1; simp [onesSt]
      · simp [onesSt, Function.update_apply, a1]
    · rfl
  have hl : (P ++ List.replicate a true).length = P.length + a := by simp
  have e := whsE cap (i := sIN) (body := .seq (pairW sXS true) (.seq (WMX.inc C) (.seq (WMX.fwd sIN) (WMX.fwd sIN))))
    (onesSt σ C P Q) a 15
    (fun k hk => by
      have hs : (onesSt σ C P Q k).st sIN = σ.st sIN := by simp [onesSt, Function.update_apply]
      have hh : (onesSt σ C P Q k).sh sIN = 2 * (P.length + k) + 1 := by
        simp [onesSt, Function.update_apply]; try ring
      simp only [wbit]; rw [hs, hh, hX, rd_fpre_data _ _ (by simp; omega)]
      rw [List.getElem_append_right (by omega)]; simp)
    (by
      have hs : (onesSt σ C P Q a).st sIN = σ.st sIN := by simp [onesSt, Function.update_apply]
      have hh : (onesSt σ C P Q a).sh sIN = 2 * (P ++ List.replicate a true).length + 1 := by
        simp [onesSt, Function.update_apply]; try ring
      simp only [wbit]; rw [hs, hh, hX, rd_fpre_after]
      rfl)
    (fun k hk => by
      have e1 := pairW_spec cap sXS true (onesSt σ C P Q k) (by simp [onesSt]; try ring)
      have e2 := WXExec.inc cap C (((onesSt σ C P Q k).sets sXS ((onesSt σ C P Q k).st sXS ++ [true, true])).seth sXS
        ((onesSt σ C P Q k).sh sXS + 2)) (by simp [onesSt]; omega)
      refine (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq (WXExec.fwd cap sIN _) (WXExec.fwd cap sIN _)))).cast cap ?_
        (by omega)
      have hl2 : fpre (Q ++ List.replicate k true) ++ [true, true] = fpre (Q ++ List.replicate (k + 1) true) := by
        rw [List.replicate_succ', ← List.append_assoc, fpre_snoc]
      apply WState.eq
      · funext j; by_cases a1 : j = sXS
        · subst a1; simp [onesSt]; try ring
        · by_cases a2 : j = sIN
          · subst a2; simp [onesSt]; try ring
          · simp [onesSt, Function.update_apply, a1, a2]
      · funext j; by_cases a1 : j = sXS
        · subst a1; simp [onesSt, hl2]
        · simp [onesSt, Function.update_apply, a1]
      · funext r; by_cases a1 : r = C
        · subst a1; simp [onesSt]; try ring
        · simp [onesSt, Function.update_apply, a1]
      · rfl)
  rw [h0] at e
  exact e.mono (by ring_nf; omega)

/-- The state after `k` witness-field bits. -/
def zSt (σ : St) (P Q z : List Bool) (k : ℕ) : St :=
  (((((σ.seth sIN (2 * P.length + 2 * k)).sets sXS (fpre (Q ++ List.replicate k false))).seth sXS
    (2 * (Q.length + k))).sets sYS (fpre (z.take k))).seth sYS (2 * k)).setv rS (σ.val rS + k)

theorem zLoop_spec (σ : St) (P Q z : List Bool)
    (hX : σ.st sIN = fpre P ++ RepairOrdinary.frame z) (hXh : σ.sh sIN = 2 * P.length)
    (hXS : σ.st sXS = fpre Q) (hXSh : σ.sh sXS = 2 * Q.length) (hYS : σ.st sYS = []) (hYSh : σ.sh sYS = 0)
    (hcap : σ.val rS + z.length < cap) :
    WXExec cap zLoop σ (zSt σ P Q z z.length) (z.length * 26 + 1) := by
  have h0 : zSt σ P Q z 0 = σ := by
    apply WState.eq
    · funext j; by_cases a1 : j = sXS
      · subst a1; simp [zSt, hXSh]
      · by_cases a2 : j = sIN
        · subst a2; simp [zSt, hXh]
        · by_cases a3 : j = sYS
          · subst a3; simp [zSt, hYSh]
          · simp [zSt, Function.update_apply, a1, a2, a3]
    · funext j; by_cases a1 : j = sXS
      · subst a1; simp [zSt, hXS]
      · by_cases a3 : j = sYS
        · subst a3; simp [zSt, hYS]
        · simp [zSt, Function.update_apply, a1, a3]
    · funext r; by_cases a1 : r = rS
      · subst a1; simp [zSt]
      · simp [zSt, Function.update_apply, a1]
    · rfl
  have hfz := frame_eq_fpre z
  have e := whsE cap (i := sIN) (body := zBody) (zSt σ P Q z) z.length 24
    (fun k hk => by
      have hs : (zSt σ P Q z k).st sIN = σ.st sIN := by simp [zSt, Function.update_apply]
      have hh : (zSt σ P Q z k).sh sIN = (fpre P).length + 2 * k := by simp [zSt, Function.update_apply]
      simp only [wbit]; rw [hs, hh, hX, rd_append_right, hfz, rd_fpre_mark _ _ hk])
    (by
      have hs : (zSt σ P Q z z.length).st sIN = σ.st sIN := by simp [zSt, Function.update_apply]
      have hh : (zSt σ P Q z z.length).sh sIN = (fpre P).length + (2 * z.length + 0) := by
        simp [zSt, Function.update_apply]
      simp only [wbit]; rw [hs, hh, hX, rd_append_right, hfz, rd_fpre_after]
      rfl)
    (fun k hk => by
      set τ := zSt σ P Q z k with hτ
      have hb : readTapeBit (σ.st sIN) (2 * P.length + 2 * k + 1) = z[k] := by
        rw [hX, show 2 * P.length + 2 * k + 1 = (fpre P).length + (2 * k + 1) by simp; ring, rd_append_right, hfz,
          rd_fpre_data _ _ hk]
      have f1 := WXExec.fwd cap sIN τ
      set τ1 := τ.seth sIN (τ.sh sIN + 1) with hτ1
      have hw : wbit τ1 sIN = z[k] := by
        have hs : τ1.st sIN = σ.st sIN := by simp [τ1, τ, zSt, Function.update_apply]
        have hh : τ1.sh sIN = 2 * P.length + 2 * k + 1 := by simp [τ1, τ, zSt, Function.update_apply]
        simp only [wbit]; rw [hs, hh, hb]
      have hxsl : τ1.sh sXS = (τ1.st sXS).length := by simp [τ1, τ, zSt]; try ring
      have hysl : τ1.sh sYS = (τ1.st sYS).length := by
        simp [τ1, τ, zSt, List.length_take]; omega
      -- the two branches
      have br : ∀ b : Bool, b = z[k] → WXExec cap (.seq (pairW sXS false) (pairW sYS b)) τ1
          ((((τ1.sets sXS (τ1.st sXS ++ [true, false])).seth sXS (τ1.sh sXS + 2)).sets sYS
            (τ1.st sYS ++ [true, b])).seth sYS (τ1.sh sYS + 2)) 15 := by
        intro b _
        have p1 := pairW_spec cap sXS false τ1 hxsl
        have p2 := pairW_spec cap sYS b ((τ1.sets sXS (τ1.st sXS ++ [true, false])).seth sXS (τ1.sh sXS + 2))
          (by simpa using hysl)
        exact (WXExec.seq p1 p2).cast cap (by simp) (by omega)
      have eIf : WXExec cap (.ifs sIN (.seq (pairW sXS false) (pairW sYS true)) (.seq (pairW sXS false) (pairW sYS false)))
          τ1 ((((τ1.sets sXS (τ1.st sXS ++ [true, false])).seth sXS (τ1.sh sXS + 2)).sets sYS
            (τ1.st sYS ++ [true, z[k]])).seth sYS (τ1.sh sYS + 2)) 16 := by
        cases hz : z[k]
        · exact WXExec.ifsF (by rw [hw, hz]) (br false hz.symm)
        · exact WXExec.ifsT (by rw [hw, hz]) (br true hz.symm)
      set τ2 := (((τ1.sets sXS (τ1.st sXS ++ [true, false])).seth sXS (τ1.sh sXS + 2)).sets sYS
            (τ1.st sYS ++ [true, z[k]])).seth sYS (τ1.sh sYS + 2) with hτ2
      have i1 := WXExec.inc cap rS τ2 (by simp [τ2, τ1, τ, zSt]; lomega)
      have f2 := WXExec.fwd cap sIN (τ2.setv rS (τ2.val rS + 1))
      refine (WXExec.seq f1 (WXExec.seq eIf (WXExec.seq i1 f2))).cast cap ?_ (by omega)
      have hl1 : fpre (Q ++ List.replicate k false) ++ [true, false] = fpre (Q ++ List.replicate (k + 1) false) := by
        rw [List.replicate_succ', ← List.append_assoc, fpre_snoc]
      have hl2 : fpre (z.take k) ++ [true, z[k]] = fpre (z.take (k + 1)) := by
        rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, fpre_snoc]
      apply WState.eq
      · funext j; by_cases a1 : j = sXS
        · subst a1; simp [τ2, τ1, τ, zSt]; try ring
        · by_cases a2 : j = sIN
          · subst a2; simp [τ2, τ1, τ, zSt]; try ring
          · by_cases a3 : j = sYS
            · subst a3; simp [τ2, τ1, τ, zSt]; try ring
            · simp [τ2, τ1, τ, zSt, Function.update_apply, a1, a2, a3]
      · funext j; by_cases a1 : j = sXS
        · subst a1; simp [τ2, τ1, τ, zSt, hl1]
        · by_cases a3 : j = sYS
          · subst a3; simp [τ2, τ1, τ, zSt, hl2]
          · simp [τ2, τ1, τ, zSt, Function.update_apply, a1, a3]
      · funext r; by_cases a1 : r = rS
        · subst a1; simp [τ2, τ1, τ, zSt]; try ring
        · simp [τ2, τ1, τ, zSt, Function.update_apply, a1]
      · rfl)
  rw [h0] at e
  exact e

/-! ## The whole parse -/

/-- `fr(x_1)` for a record `x`: the witness field replaced by zeros. -/
def zeroField (a b g : ℕ) : List Bool :=
  List.replicate a true ++ false :: (List.replicate b true ++ false :: List.replicate g false)

theorem frame_ones_zero (a : ℕ) (rest : List Bool) :
    RepairOrdinary.frame (List.replicate a true ++ false :: rest) =
      fpre (List.replicate a true) ++ (true :: false :: RepairOrdinary.frame rest) := by
  rw [frame_append]; rfl

/-- The parse states: `b` with the input head, the two output streams and four counters set. -/
def pst (b : St) (xh : ℕ) (XS : List Bool) (xsh : ℕ) (YS : List Bool) (ysh A D S E : ℕ) : St :=
  ⟨Function.update (Function.update (Function.update b.sh sIN xh) sXS xsh) sYS ysh,
   Function.update (Function.update b.st sXS XS) sYS YS,
   Function.update (Function.update (Function.update (Function.update b.val rAI A) rTD D) rS S) rTE E,
   b.cell⟩

section PstLemmas
variable (b : St) (xh : ℕ) (XS : List Bool) (xsh : ℕ) (YS : List Bool) (ysh A D S E : ℕ)

@[simp] theorem pst_sh_in : (pst b xh XS xsh YS ysh A D S E).sh sIN = xh := by simp [pst, Function.update_apply]
@[simp] theorem pst_sh_xs : (pst b xh XS xsh YS ysh A D S E).sh sXS = xsh := by simp [pst, Function.update_apply]
@[simp] theorem pst_sh_ys : (pst b xh XS xsh YS ysh A D S E).sh sYS = ysh := by simp [pst]
@[simp] theorem pst_st_in : (pst b xh XS xsh YS ysh A D S E).st sIN = b.st sIN := by simp [pst, Function.update_apply]
@[simp] theorem pst_st_xs : (pst b xh XS xsh YS ysh A D S E).st sXS = XS := by simp [pst, Function.update_apply]
@[simp] theorem pst_st_ys : (pst b xh XS xsh YS ysh A D S E).st sYS = YS := by simp [pst]
@[simp] theorem pst_val_a : (pst b xh XS xsh YS ysh A D S E).val rAI = A := by simp [pst, Function.update_apply]
@[simp] theorem pst_val_d : (pst b xh XS xsh YS ysh A D S E).val rTD = D := by simp [pst, Function.update_apply]
@[simp] theorem pst_val_s : (pst b xh XS xsh YS ysh A D S E).val rS = S := by simp [pst, Function.update_apply]
@[simp] theorem pst_val_e : (pst b xh XS xsh YS ysh A D S E).val rTE = E := by simp [pst]
@[simp] theorem pst_val_ta : (pst b xh XS xsh YS ysh A D S E).val rTA = b.val rTA := by simp [pst, Function.update_apply]
@[simp] theorem pst_val_tb : (pst b xh XS xsh YS ysh A D S E).val rTB = b.val rTB := by simp [pst, Function.update_apply]

theorem pst_seth_in (h : ℕ) : (pst b xh XS xsh YS ysh A D S E).seth sIN h = pst b h XS xsh YS ysh A D S E := by
  apply WState.eq <;> try rfl
  funext j; simp only [pst, WState.seth_sh, Function.update_apply]; split_ifs <;> simp_all
theorem pst_seth_xs (h : ℕ) : (pst b xh XS xsh YS ysh A D S E).seth sXS h = pst b xh XS h YS ysh A D S E := by
  apply WState.eq <;> try rfl
  funext j; simp only [pst, WState.seth_sh, Function.update_apply]; split_ifs <;> simp_all
theorem pst_seth_ys (h : ℕ) : (pst b xh XS xsh YS ysh A D S E).seth sYS h = pst b xh XS xsh YS h A D S E := by
  apply WState.eq <;> try rfl
  funext j; simp only [pst, WState.seth_sh, Function.update_apply]; split_ifs <;> simp_all
theorem pst_sets_xs (L : List Bool) : (pst b xh XS xsh YS ysh A D S E).sets sXS L = pst b xh L xsh YS ysh A D S E := by
  apply WState.eq <;> try rfl
  funext j; simp only [pst, WState.sets_st, Function.update_apply]; split_ifs <;> simp_all
theorem pst_sets_ys (L : List Bool) : (pst b xh XS xsh YS ysh A D S E).sets sYS L = pst b xh XS xsh L ysh A D S E := by
  apply WState.eq <;> try rfl
  funext j; simp only [pst, WState.sets_st, Function.update_apply]; split_ifs <;> simp_all
theorem pst_setv_a (v : ℕ) : (pst b xh XS xsh YS ysh A D S E).setv rAI v = pst b xh XS xsh YS ysh v D S E := by
  apply WState.eq <;> try rfl
  funext j; simp only [pst, WState.setv_val, Function.update_apply]; split_ifs <;> simp_all
theorem pst_setv_d (v : ℕ) : (pst b xh XS xsh YS ysh A D S E).setv rTD v = pst b xh XS xsh YS ysh A v S E := by
  apply WState.eq <;> try rfl
  funext j; simp only [pst, WState.setv_val, Function.update_apply]; split_ifs <;> simp_all
theorem pst_setv_s (v : ℕ) : (pst b xh XS xsh YS ysh A D S E).setv rS v = pst b xh XS xsh YS ysh A D v E := by
  apply WState.eq <;> try rfl
  funext j; simp only [pst, WState.setv_val, Function.update_apply]; split_ifs <;> simp_all
theorem pst_setv_e (v : ℕ) : (pst b xh XS xsh YS ysh A D S E).setv rTE v = pst b xh XS xsh YS ysh A D S v := by
  apply WState.eq <;> try rfl
  funext j; simp only [pst, WState.setv_val, Function.update_apply]; split_ifs <;> simp_all

theorem onesSt_pst_a (P Q : List Bool) (k : ℕ) :
    onesSt (pst b xh XS xsh YS ysh A D S E) rAI P Q k =
      pst b (2 * P.length + 1 + 2 * k) (fpre (Q ++ List.replicate k true)) (2 * (Q.length + k)) YS ysh (A + k) D S E := by
  unfold onesSt; rw [pst_seth_in, pst_sets_xs, pst_seth_xs, pst_val_a, pst_setv_a]
theorem onesSt_pst_d (P Q : List Bool) (k : ℕ) :
    onesSt (pst b xh XS xsh YS ysh A D S E) rTD P Q k =
      pst b (2 * P.length + 1 + 2 * k) (fpre (Q ++ List.replicate k true)) (2 * (Q.length + k)) YS ysh A (D + k) S E := by
  unfold onesSt; rw [pst_seth_in, pst_sets_xs, pst_seth_xs, pst_val_d, pst_setv_d]
theorem zSt_pst (P Q z : List Bool) (k : ℕ) :
    zSt (pst b xh XS xsh YS ysh A D S E) P Q z k =
      pst b (2 * P.length + 2 * k) (fpre (Q ++ List.replicate k false)) (2 * (Q.length + k)) (fpre (z.take k)) (2 * k)
        A D (S + k) E := by
  unfold zSt; rw [pst_seth_in, pst_sets_xs, pst_seth_xs, pst_sets_ys, pst_seth_ys, pst_val_s, pst_setv_s]

end PstLemmas

theorem fpre_P2 (a b g : ℕ) :
    fpre ((List.replicate a true ++ [false] ++ List.replicate b true ++ [false]) ++ List.replicate g false) ++ [false] =
      RepairOrdinary.frame (zeroField a b g) := by
  rw [frame_eq_fpre, zeroField]; congr 2; simp

set_option maxHeartbeats 400000 in
/-- **The parse** (proof of `cor:framed-refuter`): exact end state, cost `≤ 300(N+1)`, coefficient independent of `M`. -/
theorem parse_spec (σ : St) (a b : ℕ) (z : List Bool)
    (hX : σ.st sIN = RepairOrdinary.frame (List.replicate a true ++ false :: (List.replicate b true ++ false :: z)))
    (hXh : σ.sh sIN = 0) (hXS : σ.st sXS = []) (hXSh : σ.sh sXS = 0) (hYS : σ.st sYS = []) (hYSh : σ.sh sYS = 0)
    (hA : σ.val rAI = 0) (hTE : σ.val rTE = 0) (hS : σ.val rS = 0) (hTD : σ.val rTD = 0) (hTA : σ.val rTA = 0)
    (hTB : σ.val rTB = 0) (hcap : 4 * (a + b + z.length + 4) ≤ cap) :
    ∃ c, WXExec cap parse σ
      ((((((σ.sets sXS (RepairOrdinary.frame (zeroField a b z.length))).sets sYS (RepairOrdinary.frame z)).setv rAI a).setv
        rTE (a + b + z.length + 2)).setv rS z.length)) c ∧ c ≤ 300 * (a + b + z.length + 3) := by
  generalize hg : z.length = g at hcap ⊢
  have h0 : σ = pst σ 0 [] 0 [] 0 0 0 0 0 := by
    apply WState.eq <;> try rfl
    · funext j; simp only [pst, Function.update_apply]; split_ifs <;> simp_all
    · funext j; simp only [pst, Function.update_apply]; split_ifs <;> simp_all
    · funext j; simp only [pst, Function.update_apply]; split_ifs <;> simp_all
  have hx1 : σ.st sIN = fpre ([] ++ List.replicate a true) ++
      (true :: false :: RepairOrdinary.frame (List.replicate b true ++ false :: z)) := by
    rw [hX, frame_ones_zero]; rfl
  have hx2 : σ.st sIN = fpre ((List.replicate a true ++ [false]) ++ List.replicate b true) ++
      (true :: false :: RepairOrdinary.frame z) := by
    rw [hX, show List.replicate a true ++ false :: (List.replicate b true ++ false :: z) =
      (List.replicate a true ++ [false]) ++ (List.replicate b true ++ false :: z) by simp, frame_append,
      frame_ones_zero]
    simp only [fpre_append, List.append_assoc]
  have hx3 : σ.st sIN = fpre (List.replicate a true ++ [false] ++ List.replicate b true ++ [false]) ++
      RepairOrdinary.frame z := by
    rw [hX, show List.replicate a true ++ false :: (List.replicate b true ++ false :: z) =
      (List.replicate a true ++ [false] ++ List.replicate b true ++ [false]) ++ z by simp, frame_append]
  have l1 : (List.replicate a true ++ [false]).length = a + 1 := by simp
  have l2 : (List.replicate a true ++ [false] ++ List.replicate b true ++ [false]).length = a + b + 2 := by simp; omega
  -- 1–2. the machine index
  have e1 := WXExec.fwd cap sIN (pst σ 0 [] 0 [] 0 0 0 0 0)
  rw [pst_sh_in, pst_seth_in] at e1
  have e2 := onesLoop_spec cap rAI (pst σ 1 [] 0 [] 0 0 0 0 0) [] [] _ a (by simpa using hx1) (by simp)
    (by simp) (by simp) (by simp; omega)
  rw [onesSt_pst_a] at e2
  simp only [List.nil_append, List.length_nil, Nat.mul_zero, Nat.zero_add, Nat.zero_add] at e2
  -- 3. the first zero
  have e3a := pairW_spec cap sXS false (pst σ (1 + 2 * a) (fpre (List.replicate a true)) (2 * a) [] 0 a 0 0 0)
    (by simp)
  rw [pst_st_xs, pst_sh_xs, pst_sets_xs, pst_seth_xs] at e3a
  have e3b := WXExec.fwd cap sIN (pst σ (1 + 2 * a) (fpre (List.replicate a true) ++ [true, false]) (2 * a + 2) [] 0 a 0 0 0)
  rw [pst_sh_in, pst_seth_in] at e3b
  have e3c := WXExec.fwd cap sIN (pst σ (1 + 2 * a + 1) (fpre (List.replicate a true) ++ [true, false]) (2 * a + 2) [] 0 a 0 0 0)
  rw [pst_sh_in, pst_seth_in] at e3c
  have e3 : WXExec cap zeroA _ _ _ := WXExec.seq e3a (WXExec.seq e3b e3c)
  rw [← fpre_snoc] at e3
  -- 4. the middle ones
  have e4 := onesLoop_spec cap rTD (pst σ (1 + 2 * a + 1 + 1) (fpre (List.replicate a true ++ [false])) (2 * a + 2) [] 0 a 0 0 0)
    (List.replicate a true ++ [false]) (List.replicate a true ++ [false]) _ b (by simpa using hx2)
    (by simp; omega) (by simp) (by simp; omega) (by simp; lomega)
  rw [onesSt_pst_d, l1] at e4
  simp only [Nat.zero_add] at e4
  -- 5. the second zero
  have e5a := pairW_spec cap sXS false (pst σ (2 * (a + 1) + 1 + 2 * b)
    (fpre (List.replicate a true ++ [false] ++ List.replicate b true)) (2 * (a + 1 + b)) [] 0 a b 0 0) (by simp; omega)
  rw [pst_st_xs, pst_sh_xs, pst_sets_xs, pst_seth_xs] at e5a
  have e5b := WXExec.fwd cap sIN (pst σ (2 * (a + 1) + 1 + 2 * b)
    (fpre (List.replicate a true ++ [false] ++ List.replicate b true) ++ [true, false]) (2 * (a + 1 + b) + 2) [] 0 a b 0 0)
  rw [pst_sh_in, pst_seth_in] at e5b
  have e5 : WXExec cap zeroB _ _ _ := WXExec.seq e5a e5b
  rw [← fpre_snoc] at e5
  -- 6. the witness field
  have e6 := zLoop_spec cap (pst σ (2 * (a + 1) + 1 + 2 * b + 1)
    (fpre (List.replicate a true ++ [false] ++ List.replicate b true ++ [false])) (2 * (a + 1 + b) + 2) [] 0 a b 0 0)
    (List.replicate a true ++ [false] ++ List.replicate b true ++ [false])
    (List.replicate a true ++ [false] ++ List.replicate b true ++ [false]) z (by simpa using hx3)
    (by simp; omega) (by simp) (by simp; omega) (by simp) (by simp) (by simp; lomega)
  rw [zSt_pst, l2, hg, ← hg, List.take_length, hg] at e6
  simp only [Nat.zero_add] at e6
  -- 7. terminators
  have w1 : writeTapeBit (fpre (List.replicate a true ++ [false] ++ List.replicate b true ++ [false] ++
      List.replicate g false)) (2 * (a + b + 2 + g)) false = RepairOrdinary.frame (zeroField a b g) := by
    rw [show 2 * (a + b + 2 + g) = (fpre (List.replicate a true ++ [false] ++ List.replicate b true ++ [false] ++
      List.replicate g false)).length by simp; omega, wtb_append, fpre_P2]
  have w2 : writeTapeBit (fpre z) (2 * g) false = RepairOrdinary.frame z := by
    rw [show 2 * g = (fpre z).length by simp [hg], wtb_append, ← frame_eq_fpre]
  have e7a := WXExec.wr cap sXS false (pst σ (2 * (a + b + 2) + 2 * g)
    (fpre (List.replicate a true ++ [false] ++ List.replicate b true ++ [false] ++ List.replicate g false))
    (2 * (a + b + 2 + g)) (fpre z) (2 * g) a b g 0)
  rw [pst_st_xs, pst_sh_xs, w1, pst_sets_xs] at e7a
  have e7b := WXExec.wr cap sYS false (pst σ (2 * (a + b + 2) + 2 * g) (RepairOrdinary.frame (zeroField a b g))
    (2 * (a + b + 2 + g)) (fpre z) (2 * g) a b g 0)
  rw [pst_st_ys, pst_sh_ys, w2, pst_sets_ys] at e7b
  have e7 : WXExec cap term _ _ _ := WXExec.seq e7a e7b
  -- 8. N
  set B0 := pst σ (2 * (a + b + 2) + 2 * g) (RepairOrdinary.frame (zeroField a b g))
    (2 * (a + b + 2 + g)) (RepairOrdinary.frame z) (2 * g) with hB0
  have e8a := addR_spec cap (A := rAI) (B := rTE) (T := rTA) (by decide) (by decide) (by decide) (B0 a b g 0)
    (by simp [hB0, hTA]) (by simp [hB0]; lomega)
  rw [hB0, pst_val_e, pst_val_a, pst_setv_e] at e8a
  have e8b := addR_spec cap (A := rTD) (B := rTE) (T := rTA) (by decide) (by decide) (by decide) (B0 a b g (0 + a))
    (by simp [hB0, hTA]) (by simp [hB0]; lomega)
  rw [hB0, pst_val_e, pst_val_d, pst_setv_e] at e8b
  have e8c := addR_spec cap (A := rS) (B := rTE) (T := rTA) (by decide) (by decide) (by decide) (B0 a b g (0 + a + b))
    (by simp [hB0, hTA]) (by simp [hB0]; lomega)
  rw [hB0, pst_val_e, pst_val_s, pst_setv_e] at e8c
  have e8d := WXExec.inc cap rTE (B0 a b g (0 + a + b + g)) (by simp [hB0]; lomega)
  rw [hB0, pst_val_e, pst_setv_e] at e8d
  have e8e := WXExec.inc cap rTE (B0 a b g (0 + a + b + g + 1)) (by simp [hB0]; lomega)
  rw [hB0, pst_val_e, pst_setv_e] at e8e
  have e8f := clr_spec cap rTD (B0 a b g (0 + a + b + g + 1 + 1)) (by simp [hB0]; lomega)
  rw [hB0, pst_setv_d] at e8f
  have e8 : WXExec cap countN _ _ _ := WXExec.seq e8a (WXExec.seq e8b (WXExec.seq e8c (WXExec.seq e8d
    (WXExec.seq e8e e8f))))
  -- 9. rewind
  set N := 0 + a + b + g + 1 + 1 with hN
  have hNv : N = a + b + g + 2 := by omega
  set C0 := fun (xh xsh ysh : ℕ) => pst σ xh (RepairOrdinary.frame (zeroField a b g)) xsh (RepairOrdinary.frame z) ysh
    a 0 g N with hC0
  have bw : ∀ (S : Fin (NS + 1)) (xh xsh ysh : ℕ), WXExec cap (bwdK S rTE rTB) (C0 xh xsh ysh)
      ((C0 xh xsh ysh).seth S ((C0 xh xsh ysh).sh S - N)) (16 * N + 3) := by
    intro S xh xsh ysh
    have := bwdK_spec cap (S := S) (K := rTE) (K2 := rTB) (by decide) (C0 xh xsh ysh) (by simp [hC0, hTB])
      (by simp [hC0]; lomega)
    simpa [hC0] using this
  have b1 := bw sIN (2 * (a + b + 2) + 2 * g) (2 * (a + b + 2 + g)) (2 * g)
  have b2 := bw sIN (2 * (a + b + 2) + 2 * g - N) (2 * (a + b + 2 + g)) (2 * g)
  have b3 := bw sXS 0 (2 * (a + b + 2 + g)) (2 * g)
  have b4 := bw sXS 0 (2 * (a + b + 2 + g) - N) (2 * g)
  have b5 := bw sYS 0 0 (2 * g)
  have b6 := bw sYS 0 0 (2 * g - N)
  simp only [hC0, pst_sh_in, pst_sh_xs, pst_sh_ys, pst_seth_in, pst_seth_xs, pst_seth_ys] at b1 b2 b3 b4 b5 b6
  have z1 : 2 * (a + b + 2) + 2 * g - N - N = 0 := by omega
  have z2 : 2 * (a + b + 2 + g) - N - N = 0 := by omega
  have z3 : 2 * g - N - N = 0 := by omega
  rw [z1] at b2
  rw [z2] at b4
  rw [z3] at b6
  have e9 : WXExec cap rewindP _ _ _ := WXExec.seq b1 (WXExec.seq b2 (WXExec.seq b3 (WXExec.seq b4
    (WXExec.seq b5 b6))))
  have E : WXExec cap parse _ _ _ := WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4 (WXExec.seq e5
    (WXExec.seq e6 (WXExec.seq e7 (WXExec.seq e8 e9)))))))
  rw [← h0] at E
  refine ⟨_, E.cast cap ?_ le_rfl, ?_⟩
  · conv_rhs => rw [h0]
    rw [pst_sets_xs, pst_sets_ys, pst_setv_a, pst_setv_e, pst_setv_s, hNv]
  · simp only [pst_val_d, pst_val_e, pst_val_a, pst_val_s, l1, l2]
    omega

end NearCubicGates.Adapters.Refuter.Mach
