import Proof.Wire_3_5.PrimAsmCellState
import Proof.Wire_3_5.BlockJoin

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.PrimAsm.CellUnit
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.WireExponent3_5.PrimAsm.UnitReady NearCubicWires.WireExponent3_5.PrimAsm.PopPipe
open NearCubicWires.WireExponent3_5.PrimAsm.FiltPipe NearCubicWires.WireExponent3_5.PrimT.WalkBank

/-! ## The counter increment -/

section Inc
variable (cap : ℕ) {x : ℕ}

variable (x) in
/-- **The counter increment**: to the counter's end, one more mark. -/
def incW : WM (LNS x) LNR := .seq (.whs (sk x 2) (.fwd (sk x 2))) (.wr (sk x 2) true)

theorem rep_true_lt (j h : ℕ) (hh : h < j) : readTapeBit (List.replicate j true) h = true := by
  unfold readTapeBit
  rw [List.getD_eq_getElem _ _ (by simpa using hh)]
  simp

theorem rep_true_ge (j h : ℕ) (hh : j ≤ h) : readTapeBit (List.replicate j true) h = false := by
  unfold readTapeBit
  rw [List.getD_eq_default _ _ (by simpa using hh)]

theorem wtb_end (l : List Bool) (v : Bool) : writeTapeBit l l.length v = l ++ [v] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [writeTapeBit, ih]

theorem incLoop (j : ℕ) : ∀ (m : ℕ) (σ : WState (LNS x) LNR), σ.st (sk x 2) = List.replicate j true →
    σ.sh (sk x 2) + m = j → WExec cap (.whs (sk x 2) (.fwd (sk x 2))) σ (σ.seth (sk x 2) j) (3 * m + 1)
  | 0, σ, hc, hh => by
    have hb : wbit σ (sk x 2) = false := by
      unfold wbit
      rw [hc]
      exact rep_true_ge j _ (by omega)
    have e : σ.seth (sk x 2) j = σ := by
      apply WState.eq
      · funext i
        by_cases hi : i = sk x 2
        · subst hi
          simp
          omega
        · simp [Function.update_apply, hi]
      · rfl
      · rfl
      · rfl
    rw [e]
    exact WExec.whsF hb
  | m + 1, σ, hc, hh => by
    have hb : wbit σ (sk x 2) = true := by
      unfold wbit
      rw [hc]
      exact rep_true_lt j _ (by omega)
    have h1 := WExec.fwd (cap := cap) (sk x 2) σ
    have h2 := incLoop j m (σ.seth (sk x 2) (σ.sh (sk x 2) + 1)) (by simp [hc]) (by simp; omega)
    have e : (σ.seth (sk x 2) (σ.sh (sk x 2) + 1)).seth (sk x 2) j = σ.seth (sk x 2) j := by
      apply WState.eq
      · funext i
        by_cases hi : i = sk x 2
        · subst hi
          simp
        · simp [Function.update_apply, hi]
      · rfl
      · rfl
      · rfl
    rw [e] at h2
    have h3 := WExec.whsT hb h1 h2
    rw [show 1 + 2 + (3 * m + 1) = 3 * (m + 1) + 1 by ring] at h3
    exact h3

/-- **The counter increment's run**: `1^j` at head `0` becomes `1^(j+1)`, the head at `j`; nothing else changes. -/
theorem incW_spec (σ : WState (LNS x) LNR) (j : ℕ) (hc : σ.st (sk x 2) = List.replicate j true)
    (hh : σ.sh (sk x 2) = 0) :
    WExec cap (incW x) σ ((σ.seth (sk x 2) j).sets (sk x 2) (List.replicate (j + 1) true)) (3 * j + 3) := by
  have h1 := incLoop cap j j σ hc (by omega)
  have h2 := WExec.wr (cap := cap) (sk x 2) true (σ.seth (sk x 2) j)
  have e : writeTapeBit ((σ.seth (sk x 2) j).st (sk x 2)) ((σ.seth (sk x 2) j).sh (sk x 2)) true =
      List.replicate (j + 1) true := by
    simp only [WState.seth_st, WState.seth_sh, Function.update_self, hc]
    have hw := wtb_end (List.replicate j true) true
    rw [List.length_replicate] at hw
    rw [hw, List.replicate_succ']
  rw [e] at h2
  have h3 := WExec.seq h1 h2
  rw [show 3 * j + 1 + 1 + 1 = 3 * j + 3 by ring] at h3
  exact h3

end Inc

/-! ## The unit machine -/

section Unit
open NearCubicWires.WireExponent3_5.Lists NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.FinalPass.Filt NearCubicWires.WireExponent3_5.ListMachine.Row
open NearCubicWires.WireExponent3_5.PrimAsm.Emit
variable (cap : ℕ) (W : WalkBankProducer)

/-- **The unit machine** of a writer: its decode, the branch on the flags, the counter increment. -/
noncomputable def unitM (decW : WM (LNS W.x) LNR) :=
  Composition.machine (Composition.machine decW.toProg.compile
    (Block.branchM (sTape (nr := LNR) (sk W.x 150)) (popPipeM W)
      (Block.branchM (sTape (nr := LNR) (sk W.x 151)) (filtPipeM W) (Block.idle (LNS W.x + 2 + LNR)))))
    (incW W.x).toProg.compile

def DecOK (σ : WState (LNS W.x) LNR) (out e : List Bool) (Bp : ℕ) : Prop :=
  (σ.st (sk W.x 150) = [] ∧ σ.sh (sk W.x 150) = 0 ∧ σ.st (sk W.x 151) = [] ∧ σ.sh (sk W.x 151) = 0 ∧
    σ.st (sk W.x 1) = out ++ e ++ [false] ∧ σ.sh (sk W.x 1) = (out ++ e).length) ∨
  (σ.st (sk W.x 150) = [true] ∧ σ.sh (sk W.x 150) = 0 ∧
    ∃ (Pl : FlatListParams) (e' : Pl.FlatSeed) (L r4 G off Mlab lw CAP LL R cp RW LW : ℕ) (sgn : Bool)
      (s : Fin (Pl.M + 1)) (hlabs : 4 * L ≤ (sliceLabs r4 G off L).length),
      PopReady cap W σ out Pl e' L r4 G off Mlab lw CAP LL R cp RW LW sgn s hlabs ∧
      e = (popRefC Pl e' L sgn (sliceLabs r4 G off L) s).flatMap (fun t => true :: ListMachine.Rec.termWord t) ∧
      popPipeBound cap Pl e' L r4 G off Mlab lw R cp RW LW sgn s hlabs ≤ Bp) ∨
  (σ.st (sk W.x 150) = [] ∧ σ.sh (sk W.x 150) = 0 ∧ σ.st (sk W.x 151) = [true] ∧ σ.sh (sk W.x 151) = 0 ∧
    ∃ (P : GapParams) (e' : GapSeed P) (L r4 G off Mlab RW LW : ℕ)
      (sample : SupplierWalk.MargulisWalkSample (2 ^ (wOf P.fieldBits P.labelBits * 128)) (2 * (P.errExp / 4) + 1)),
      FiltReady cap W σ out P e' L r4 G off Mlab RW LW sample ∧
      e = (filtRefC (filterTable P e' L) (SupplierWalk.majorityThreshold P.walkLen) L true
        (sliceLabs r4 G off L)).flatMap (fun t => true :: ListMachine.Rec.termWord t) ∧
      filtPipeBound P e' L r4 G off RW LW ≤ Bp)

theorem bit_empty (σ : WState (LNS W.x) LNR) (k : Fin 161) (h1 : σ.st (sk W.x k) = []) :
    readTapeBit ((wenc cap σ).A (sTape (sk W.x k))) ((wenc cap σ).H (sTape (sk W.x k))) = false := by
  rw [wenc_A_s, h1]
  rfl

theorem bit_one (σ : WState (LNS W.x) LNR) (k : Fin 161) (h1 : σ.st (sk W.x k) = [true])
    (h2 : σ.sh (sk W.x k) = 0) :
    readTapeBit ((wenc cap σ).A (sTape (sk W.x k))) ((wenc cap σ).H (sTape (sk W.x k))) = true := by
  rw [wenc_A_s, wenc_H_s, h1, h2]
  rfl

/-- The state after the counter increment. -/
def incSt (σ : WState (LNS W.x) LNR) (j : ℕ) : WState (LNS W.x) LNR :=
  (σ.seth (sk W.x 2) j).sets (sk W.x 2) (List.replicate (j + 1) true)

theorem incSt_st (σ : WState (LNS W.x) LNR) (j : ℕ) (k : Fin 161) (hk : k ≠ 2) :
    (incSt W σ j).st (sk W.x k) = σ.st (sk W.x k) := by
  simp [incSt, Function.update_apply, sk_ne (x := W.x) k 2 hk]

theorem incSt_sh (σ : WState (LNS W.x) LNR) (j : ℕ) (k : Fin 161) (hk : k ≠ 2) :
    (incSt W σ j).sh (sk W.x k) = σ.sh (sk W.x k) := by
  simp [incSt, Function.update_apply, sk_ne (x := W.x) k 2 hk]

theorem incSt_ctr (σ : WState (LNS W.x) LNR) (j : ℕ) :
    (incSt W σ j).st (sk W.x 2) = List.replicate (j + 1) true := by
  simp [incSt]

/-- **One unit**: from the decode's run to a `DecOK` state (request and counter kept), the unit machine prints the
unit's body `e` on the output and increments the counter. -/
theorem unit_step (decW : WM (LNS W.x) LNR) (σ0 σD : WState (LNS W.x) LNR) (m j Bp : ℕ) (out e w : List Bool)
    (hdec : WExec cap decW σ0 σD m) (hok : DecOK cap W σD out e Bp) (hIN : σD.st (sk W.x 0) = frame w)
    (hCTR : σD.st (sk W.x 2) = List.replicate j true) (hCTRh : σD.sh (sk W.x 2) = 0) :
    ∃ σE, Step (unitM W decW) (m + 1 + (Bp + 4) + 1 + (3 * j + 3)) (wenc cap σ0).H (wenc cap σ0).A
        (wenc cap σE).H (wenc cap σE).A ∧
      σE.st (sk W.x 0) = frame w ∧ σE.st (sk W.x 1) = out ++ e ++ [false] ∧ σE.sh (sk W.x 1) = (out ++ e).length ∧
      σE.st (sk W.x 2) = List.replicate (j + 1) true := by
  have s1 := (WExec.exec cap hdec).step
  have n02 : (0 : Fin 161) ≠ 2 := by decide
  have n12 : (1 : Fin 161) ≠ 2 := by decide
  rcases hok with ⟨f0, -, f1, -, ho, hoh⟩ | ⟨f0, f0h, Pl, e', L, r4, G, off, Mlab, lw, CAP, LL, R, cp, RW, LW, sgn, s,
      hlabs, hR, he, hb⟩ | ⟨f0, -, f1, f1h, P, e', L, r4, G, off, Mlab, RW, LW, sample, hR, he, hb⟩
  · have hbr := Block.branch_false (sTape (nr := LNR) (sk W.x 150)) (popPipeM W)
      (Block.branch_false (sTape (nr := LNR) (sk W.x 151)) (filtPipeM W)
        (ListMachine.Print.idle_step (wenc cap σD).H (wenc cap σD).A) (bit_empty cap W σD 151 f1))
      (bit_empty cap W σD 150 f0)
    have si := (WExec.exec cap (incW_spec cap σD j hCTR hCTRh)).step
    refine ⟨incSt W σD j, Step.seq (Step.seq s1 (hbr.enlarge (by omega))) si, ?_, ?_, ?_, incSt_ctr W σD j⟩
    · rw [incSt_st W σD j 0 n02, hIN]
    · rw [incSt_st W σD j 1 n12, ho]
    · rw [incSt_sh W σD j 1 n12, hoh]
  · obtain ⟨σF, mF, sF, oF, ohF, kF, bF⟩ := popPipe_ready cap W σD out Pl e' L r4 G off Mlab lw CAP LL R cp RW LW
      sgn s hlabs hR
    have hbr := Block.branch_true (sTape (nr := LNR) (sk W.x 150))
      (Block.branchM (sTape (nr := LNR) (sk W.x 151)) (filtPipeM W) (Block.idle (LNS W.x + 2 + LNR))) sF
      (bit_one cap W σD 150 f0 f0h)
    obtain ⟨c1, c2⟩ := kF 2 (Or.inr rfl)
    obtain ⟨i1, -⟩ := kF 0 (Or.inl rfl)
    have si := (WExec.exec cap (incW_spec cap σF j (c1.trans hCTR) (c2.trans hCTRh))).step
    refine ⟨incSt W σF j, Step.seq (Step.seq s1 (hbr.enlarge (by omega))) si, ?_, ?_, ?_, incSt_ctr W σF j⟩
    · rw [incSt_st W σF j 0 n02, i1, hIN]
    · rw [incSt_st W σF j 1 n12, oF, he]
    · rw [incSt_sh W σF j 1 n12, ohF, he]
  · obtain ⟨σF, mF, sF, oF, ohF, kF, bF⟩ := filtPipe_ready cap W σD out P e' L r4 G off Mlab RW LW sample hR
    have hbr := Block.branch_false (sTape (nr := LNR) (sk W.x 150)) (popPipeM W)
      (Block.branch_true (sTape (nr := LNR) (sk W.x 151)) (Block.idle (LNS W.x + 2 + LNR)) sF
        (bit_one cap W σD 151 f1 f1h)) (bit_empty cap W σD 150 f0)
    obtain ⟨c1, c2⟩ := kF 2 (Or.inr rfl)
    obtain ⟨i1, -⟩ := kF 0 (Or.inl rfl)
    have si := (WExec.exec cap (incW_spec cap σF j (c1.trans hCTR) (c2.trans hCTRh))).step
    refine ⟨incSt W σF j, Step.seq (Step.seq s1 (hbr.enlarge (by omega))) si, ?_, ?_, ?_, incSt_ctr W σF j⟩
    · rw [incSt_st W σF j 0 n02, i1, hIN]
    · rw [incSt_st W σF j 1 n12, oF, he]
    · rw [incSt_sh W σF j 1 n12, ohF, he]

end Unit

end NearCubicWires.WireExponent3_5.PrimAsm.CellUnit
