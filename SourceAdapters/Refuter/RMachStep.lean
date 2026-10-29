import SourceAdapters.Refuter.RMachPose

/-!
# The round machine STEP of R (input 7, R)

Paper context: `lem:multitape-refuter`, Steps 3–4, and `cor:framed-refuter`. Each search round poses
one adaptive query, whose full word is written by the machine. At termination it outputs the diagonal
record `x_p`.

`STEP f = clrQO; arith; if FIN then OUTPUT else POSE f`:

* `outP`: the record `x_p` (`p` in `LO`) is written framed on the output stream, `DONE := 1` (`out_spec`);
* `poseP f`: `Q := (lo+hi)/2`, the framed request word on the compiler's input stream, the compiler call, the
  ruler and the cleanup (`pose_spec`): the compiler's output stream holds `frame (query r).bits` + blanks.
-/

namespace NearCubicGates.Adapters.Refuter.RM

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicGates.Close.WordPrograms NearCubicGates.Adapters.Refuter NearCubicGates.Adapters.Compile
open NearCubicGates.Close.CheckedPCPP (clearPrefix)
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {tc tT : ℕ} (cap : ℕ)

local notation "WS" => WState (NS tc tT) NR

/-! ## The output -/

/-- Write the record `x_p` (`p` in `LO`) framed on `OUT`, rewind, set `DONE`. -/
def outP : WMX (NS tc tT) NR :=
  .seq (emRec (em1 sOUT rO) sLO sMU sXU r1) (.seq (WMX.wr sOUT false) (.seq (rew sOUT rO) (WMX.wr sDONE true)))

theorem out_spec (σ : WS) (mi xr g p : ℕ) (hOUT : σ.st sOUT = []) (hMU : σ.st sMU = List.replicate mi true)
    (hXU : σ.st sXU = List.replicate xr true) (hLO : σ.st sLO = num (g + 2) p) (hDONE : σ.st sDONE = [false])
    (hsh : ∀ i, σ.sh i = 0) (hr1 : σ.val r1 = 0) (hrO : σ.val rO = 0)
    (hcap : 8 * (mi + xr + g + 10) ≤ cap) :
    WXExec cap outP σ ((σ.sets sOUT (RepairOrdinary.frame (recList mi xr g p))).sets sDONE [true])
      ((mi + xr + g + 5) * 60 + 10 * (mi + xr + g + 5) + 10) := by
  have nMU : sMU ≠ (sOUT : Fin (NS tc tT + 1)) := by ds
  have nXU : sXU ≠ (sOUT : Fin (NS tc tT + 1)) := by ds
  have nLO : sLO ≠ (sOUT : Fin (NS tc tT + 1)) := by ds
  have hD : σ.sh sOUT = (σ.st sOUT).length := by rw [hsh, hOUT]; rfl
  have e1 := emRec_spec cap (em1_act cap sOUT rO) (fun b => by simp) sLO sMU sXU r1 nLO nMU nXU (by decide) σ mi xr g p
    hMU (hsh _) hXU (hsh _) hLO (hsh _) hr1 hD (by rw [hrO]; omega) (by omega)
  set A := (recList mi xr g p).flatMap (fun b => [true, b]) with hA
  have hAl : A.length = 2 * (mi + xr + g + 2) := by
    have : (recList mi xr g p).length = mi + xr + g + 2 := by simp [recList, wbits]; omega
    rw [hA, ← fpre.eq_def, fpre_length, this]
  have e2 := WXExec.wr cap sOUT false (app σ sOUT rO A)
  have w : writeTapeBit ((app σ sOUT rO A).st sOUT) ((app σ sOUT rO A).sh sOUT) false =
      RepairOrdinary.frame (recList mi xr g p) := by
    simp only [app_st_D, app_sh_D, hOUT, hsh, List.nil_append, Nat.zero_add]
    rw [wtb_append, frame_eq_fpre]; rfl
  rw [w] at e2
  have e3 := rew_spec cap sOUT rO ((app σ sOUT rO A).sets sOUT (RepairOrdinary.frame (recList mi xr g p))) A.length
    (by simp [hrO]) (by omega)
  set ρ := (((app σ sOUT rO A).sets sOUT (RepairOrdinary.frame (recList mi xr g p))).setv rO 0).seth sOUT
    (((app σ sOUT rO A).sets sOUT (RepairOrdinary.frame (recList mi xr g p))).sh sOUT - A.length) with hρ
  have e4 := wr1 (cap := cap) sDONE true false ρ (by simp [ρ, Function.update_apply, Fin.ext_iff,
    app_st_ne _ _ _ _ _ (show (sDONE : Fin (NS tc tT + 1)) ≠ sOUT by ds), hDONE])
    (by simp [ρ, Function.update_apply, Fin.ext_iff, app_sh_ne _ _ _ _ _ (show (sDONE : Fin (NS tc tT + 1)) ≠ sOUT by ds),
      hsh])
  refine (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 e4))).cast cap ?_ (by omega)
  simp only [ρ]
  unfold app
  have h1 := hsh sOUT
  clear e1 e2 e3 e4 w
  wst

/-! ## Posing a query -/

section Pose
variable {budget : CNFCompilationRequest → ℕ} {query : CNFCompilationRequest → ℕ}
variable (f : WordFunction CNFCompilationRequest CNFCompilationRequest.word
  (fun r => RepairOrdinary.frame (query r).bits) budget)

local notation "WSf" => WState (NS f.program.tapeCount tT) NR

/-- The compiler's input stream. -/
def cin : Fin (NS f.program.tapeCount tT + 1) := sC (NearCubicGates.Close.WorkerArith.inTape f.program)
/-- The compiler's output stream = R's query tape. -/
def qo : Fin (NS f.program.tapeCount tT + 1) := sC f.program.outputTape

/-- **Pose the query of the stored state.** -/
noncomputable def poseP : WMX (NS f.program.tapeCount tT) NR :=
  .seq (.seq (cp sQ sLO) (.seq (ad sQ sHI) (hf sQ))) (.seq (emitReq (cin (tT := tT) f)) (.seq (rcG (cin (tT := tT) f))
    (callP (tT := tT) f)))

theorem memWord_len (code : List Bool) (mi xr g TN q : ℕ) :
    (memWord code mi xr g TN q).length ≤ 6 * (code.length + mi + xr + g + TN) + 13 := by
  simp [memWord, frame_len, recList, wbits]; omega

theorem intWord_len (code : List Bool) (mi xr g TN q : ℕ) (hq : q < 2 ^ (g + 2)) :
    (intWord code mi xr g TN q).length ≤ 6 * (code.length + mi + xr + g + TN) + 13 := by
  have := Nat.size_eq_bits_len q; have := Nat.size_le.mpr hq
  simp [intWord, frame_len, recList, wbits]; omega

theorem inTape_ne_out : NearCubicGates.Close.WorkerArith.inTape f.program ≠ f.program.outputTape := by
  intro h; have := f.program.outputFresh; rw [← h] at this; exact this rfl

theorem pose_spec (σ : WSf) (code : List Bool) (mi xr g TN lo hi Lc : ℕ) (p3 : Bool) (req : CNFCompilationRequest)
    (hs : ReqSrc σ code mi xr g TN) (hLO : σ.st sLO = num (g + 2) lo) (hHI : σ.st sHI = num (g + 2) hi)
    (hlh : lo + hi < 2 ^ (g + 2)) (hQ : ∃ v, σ.st sQ = num (g + 2) v) (hXH : ∃ v, σ.st sXH = num (g + 2) v)
    (hP3 : σ.st sP3 = [p3])
    (hw : req.word = if p3 then intWord code mi xr g TN ((lo + hi) / 2) else memWord code mi xr g TN ((lo + hi) / 2))
    (hcs : ∀ j, j ≠ f.program.outputTape → σ.st (sC j) = []) (hqo : ∀ q, readTapeBit (σ.st (qo (tT := tT) f)) q = false)
    (hTL : σ.st sTL = []) (hG : σ.st sG = []) (hLOG : σ.st sLOG = List.replicate Lc false)
    (hLc : budget req + 1 ≤ Lc) (hvals : ∀ r, σ.val r = 0)
    (hcap : 40 * (code.length + mi + xr + g + TN + Lc + 10) ≤ cap) :
    ∃ τ : WSf, WXExec cap (poseP (tT := tT) f) σ τ
        ((f.program.tapeCount + 3) * 1000 * (code.length + mi + xr + g + TN + Lc + 10) ^ 2) ∧
      (∃ z, τ.st (qo (tT := tT) f) = ZeroPadding.pad z (RepairOrdinary.frame (query req).bits)) ∧
      (∀ j, j ≠ f.program.outputTape → ∀ q, readTapeBit (τ.st (sC j)) q = false) ∧
      (∀ q, readTapeBit (τ.st sTL) q = false) ∧ (∀ q, readTapeBit (τ.st sG) q = false) ∧
      τ.st sQ = num (g + 2) ((lo + hi) / 2) ∧ (∃ v, τ.st sXH = num (g + 2) v) ∧
      (∀ i, (∀ j, sC j ≠ i) → i ≠ sTL → i ≠ sG → i ≠ sQ → i ≠ sXH → τ.st i = σ.st i) ∧
      (∀ i, τ.sh i = 0) ∧ (∀ r, τ.val r = 0) ∧ τ.cell = σ.cell := by
  set j0 := NearCubicGates.Close.WorkerArith.inTape f.program with hj0
  set D := cin (tT := tT) f with hD
  set L := code.length + mi + xr + g + TN with hL
  obtain ⟨vq, hQv⟩ := hQ
  obtain ⟨xa, hXHv⟩ := hXH
  set q := (lo + hi) / 2 with hq
  have hqW : q < 2 ^ (g + 2) := lt_of_le_of_lt (Nat.div_le_self _ _) hlh
  have e1 := qcomp_spec cap (g + 2) σ lo hi vq hLO hHI hQv hs.sh (hvals _) (hvals _) hlh (by omega)
  set σ1 := σ.sets sQ (num (g + 2) q) with hσ1
  have hQne : ∀ X : Fin (NS f.program.tapeCount tT + 1), X ≠ sQ → σ1.st X = σ.st X := fun X h => by
    simp [σ1, Function.update_of_ne h]
  have hs1 : ReqSrc σ1 code mi xr g TN :=
    ⟨by rw [hQne _ (by ds), hs.code], by rw [hQne _ (by ds), hs.mu], by rw [hQne _ (by ds), hs.xu],
      by rw [hQne _ (by ds), hs.gu], by rw [hQne _ (by ds), hs.tu], by rw [hQne _ (by ds), hs.z],
      fun i => by simp [σ1, hs.sh], by simp [σ1, hvals], by simp [σ1, hvals], by simp [σ1, hvals],
      by simp [σ1, hvals], by simp [σ1, hvals]⟩
  have hDne : D ≠ sQ := by simp only [D, cin]; exact (sC_ne _ _ (by simp)).symm
  have hD0 : σ1.st D = [] := by rw [hQne _ hDne]; exact hcs _ (inTape_ne_out f)
  set w := if p3 then intWord code mi xr g TN q else memWord code mi xr g TN q with hwdef
  have hwl : w.length ≤ 6 * L + 13 := by
    simp only [w]; split_ifs
    · exact intWord_len code mi xr g TN q hqW
    · exact memWord_len code mi xr g TN q
  set xh := if p3 then num (g + 2) 0 else σ.st sXH with hxh
  have hXHD : sXH ≠ D := sC_ne _ _ (by simp)
  have hGD : sG ≠ D := sC_ne _ _ (by simp)
  have e2 : WXExec cap (emitReq D) σ1 (((app σ1 D rC (fpre w)).sets D (RepairOrdinary.frame w)).sets sXH xh)
      (200 * (L + 10) ^ 2) := by
    cases p3
    · have := emitReq_mem cap j0 σ1 code mi xr g TN q hs1 (by simp [σ1]) (by rw [hQne _ (by ds), hP3]) hD0
        (by omega)
      refine this.cast cap ?_ le_rfl
      simp only [w, xh, Bool.false_eq_true, if_false]
      symm; apply BinW.sets_same
      rw [WState.sets_st, Function.update_of_ne hXHD, app_st_ne _ _ _ _ _ hXHD, hQne _ (by ds)]
    · exact emitReq_int cap j0 σ1 code mi xr g TN q xa hs1 (by simp [σ1]) hqW (by rw [hQne _ (by ds), hXHv])
        (by rw [hQne _ (by ds), hP3]) hD0 (by omega)
  set n := (fpre w).length with hn
  set σ2 := ((app σ1 D rC (fpre w)).sets D (RepairOrdinary.frame w)).sets sXH xh with hσ2
  have e3 := rcG_spec cap D hGD.symm σ2 n
    (by simp [σ2, Function.update_of_ne hXHD.symm, σ1, hs.sh, n])
    (by simp [σ2, σ1, hvals, n])
    (by simp only [σ2, WState.sets_st, Function.update_of_ne (show (sG : Fin (NS f.program.tapeCount tT + 1)) ≠ sXH by ds),
          Function.update_of_ne hGD]
        rw [app_st_ne _ _ _ _ _ hGD, hQne _ (by ds), hG])
    (by simp [σ2, Function.update_apply, Fin.ext_iff, app_sh_ne _ _ _ _ _ hGD, σ1, hs.sh]; try omega)
    (by simp [σ2, app_val_ne _ _ _ _ _ (show rG ≠ rC by decide), σ1, hvals])
    (by simp [n, fpre_length]; omega)
  set σ3 := ((((σ2.sets sG (List.replicate n true)).seth sG n).seth D 0).setv rG n).setv rC 0 with hσ3
  have hnw : n = 2 * w.length := by simp [n]
  have hout0 : f.program.outputTape.val ≠ 0 := f.program.outputFresh
  have hj00 : j0.val = 0 := rfl
  -- what the pieces leave on the compiler's streams
  have h3st : ∀ X, X ≠ sG → X ≠ sXH → X ≠ D → X ≠ sQ → σ3.st X = σ.st X := by
    intro X h1 h2 h3 h4
    simp only [σ3, σ2, WState.setv_st, WState.seth_st, WState.sets_st, Function.update_of_ne h1,
      Function.update_of_ne h2, Function.update_of_ne h3]
    rw [app_st_ne _ _ _ _ _ h3, hQne _ h4]
  have hCne : ∀ j : Fin f.program.tapeCount, sC (tT := tT) j ≠ sG ∧ sC (tT := tT) j ≠ sXH ∧ sC (tT := tT) j ≠ sQ := fun j =>
    ⟨(sC_ne j _ (by simp)).symm, (sC_ne j _ (by simp)).symm, (sC_ne j _ (by simp)).symm⟩
  set z : Fin f.program.tapeCount → ℕ := fun j => if j = f.program.outputTape then (σ.st (qo (tT := tT) f)).length else 0
    with hz
  have hin : ∀ j, σ3.st (sC j) = ZeroPadding.pad (z j) (f.program.inputTapes (CNFCompilationRequest.word req) j) := by
    intro j
    by_cases hj : j = j0
    · subst hj
      have hne : j0 ≠ f.program.outputTape := inTape_ne_out f
      simp only [z, hne, if_false, ZeroPadding.pad_zero, Program.inputTapes, hj00, if_true, hw]
      simp only [σ3, σ2, WState.setv_st, WState.seth_st, WState.sets_st, Function.update_of_ne (hCne j0).1,
        Function.update_of_ne (hCne j0).2.1]
      show Function.update (app σ1 D rC (fpre w)).st D (RepairOrdinary.frame w) D = _
      rw [Function.update_self]
    · have hjD : sC (tT := tT) j ≠ D := fun h => hj (sC_inj h)
      rw [h3st _ (hCne j).1 (hCne j).2.1 hjD (hCne j).2.2]
      have hv : j.val ≠ 0 := fun h => hj (Fin.ext (by rw [h]; rfl))
      by_cases ho : j = f.program.outputTape
      · subst ho
        simp only [z, if_true, Program.inputTapes, hv, if_false]
        have := eq_replicate_of_blank _ hqo
        simp only [qo] at this
        rw [this]; simp [ZeroPadding.pad, qo]
      · simp only [z, ho, if_false, ZeroPadding.pad_zero, Program.inputTapes, hv, if_false]
        exact hcs j ho
  have hext : ∀ j q, n < q → readTapeBit (f.program.inputTapes (CNFCompilationRequest.word req) j) q = false := by
    intro j q hq
    simp only [Program.inputTapes]
    split_ifs
    · unfold readTapeBit; rw [List.getD_eq_default _ _ (by rw [frame_len, hw]; omega)]
    · rfl
  have e4 := callP_spec cap f req σ3 z n Lc hin hext
    (by rw [h3st _ (by ds) (by ds) (sC_ne _ _ (by simp)) (by ds), hTL])
    (by rw [h3st _ (by ds) (by ds) (sC_ne _ _ (by simp)) (by ds), hLOG]) (by omega)
    (by simp [σ3]) (by simp [σ3, Function.update_of_ne hGD]) (by simp [σ3, Function.update_apply, Fin.ext_iff])
    (by
      intro i hi
      simp only [σ3, σ2, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_of_ne hi]
      by_cases hiD : i = D
      · subst hiD; simp
      · rw [Function.update_of_ne hiD, Function.update_of_ne hi, app_sh_ne _ _ _ _ _ hiD]; simp [σ1, hs.sh])
    (by simp [σ3, Function.update_apply, Fin.ext_iff, σ2, app_val_ne, σ1, hvals])
    (by simp [σ3, Function.update_apply, Fin.ext_iff, σ2, app_val_ne, σ1, hvals])
    (by rw [hnw]; omega)
  obtain ⟨τ, e4, hqo', hcs', htl', hg', hoth', hsh', hval', hvalG', hcell'⟩ := e4
  refine ⟨τ, (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 e4))).mono ?_, ⟨z f.program.outputTape, hqo'⟩, hcs', htl',
    hg', ?_, ?_, ?_, hsh', ?_, ?_⟩
  · -- cost
    have hn' : n ≤ 12 * L + 26 := by omega
    have hb : budget req ≤ Lc := by omega
    have hX : 10 ≤ L + Lc + 10 := by omega
    have hgL : g ≤ L := by omega
    have h1 : (f.program.tapeCount + 3) * 50 * (n + budget req + 2) ≤
        (f.program.tapeCount + 3) * 600 * (L + Lc + 10) := by
      have : n + budget req + 2 ≤ 12 * (L + Lc + 10) := by omega
      calc (f.program.tapeCount + 3) * 50 * (n + budget req + 2)
          ≤ (f.program.tapeCount + 3) * 50 * (12 * (L + Lc + 10)) := Nat.mul_le_mul_left _ this
        _ = (f.program.tapeCount + 3) * 600 * (L + Lc + 10) := by ring
    have h2 : 200 * (L + 10) ^ 2 ≤ 200 * (L + Lc + 10) ^ 2 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
    have hLX : L + 10 ≤ L + Lc + 10 := by omega
    have hbX : budget req ≤ L + Lc + 10 := by omega
    have hT : 3 ≤ f.program.tapeCount + 3 := by omega
    generalize f.program.tapeCount + 3 = T3 at h1 hT ⊢
    generalize L + Lc + 10 = X at hX h1 h2 hLX hbX ⊢
    generalize budget req = b at hb h1 hbX ⊢
    clear * - hn' hX h1 h2 hgL hLX hbX hT
    have a1 : 120 * (g + 2) + 13 + 13 * n + 3 + 2 * b ≤ 300 * X := by omega
    have a2 : 300 * X ≤ 30 * (X * X) := by nlinarith
    have a3 : T3 * 600 * X ≤ T3 * 60 * (X * X) := by
      have : 600 * X ≤ 60 * (X * X) := by nlinarith
      calc T3 * 600 * X = T3 * (600 * X) := by ring
        _ ≤ T3 * (60 * (X * X)) := Nat.mul_le_mul_left _ this
        _ = T3 * 60 * (X * X) := by ring
    have a4 : 3 * (X * X) ≤ T3 * (X * X) := Nat.mul_le_mul_right _ hT
    have h2' : 200 * (L + 10) ^ 2 ≤ 200 * (X * X) := by rw [← sq]; exact h2
    rw [sq]
    nlinarith
  · rw [hoth' sQ (fun j => (hCne j).2.2) (by ds) (by ds)]
    simp only [σ3, σ2, WState.setv_st, WState.seth_st, WState.sets_st,
      Function.update_of_ne (show (sQ : Fin (NS f.program.tapeCount tT + 1)) ≠ sG by ds),
      Function.update_of_ne (show (sQ : Fin (NS f.program.tapeCount tT + 1)) ≠ sXH by ds),
      Function.update_of_ne hDne.symm]
    rw [app_st_ne _ _ _ _ _ hDne.symm]; simp [σ1]
  · refine ⟨if p3 then 0 else xa, ?_⟩
    rw [hoth' sXH (fun j => (hCne j).2.1) (by ds) (by ds)]
    simp only [σ3, σ2, WState.setv_st, WState.seth_st, WState.sets_st,
      Function.update_of_ne (show (sXH : Fin (NS f.program.tapeCount tT + 1)) ≠ sG by ds), Function.update_self]
    cases p3 <;> simp [xh, hXHv]
  · intro i hi1 hi2 hi3 hi4 hi5
    rw [hoth' i hi1 hi2 hi3]
    exact h3st i hi3 hi5 (fun h => hi1 j0 h.symm) hi4
  · intro r
    by_cases hr : r = rG
    · subst hr; exact hvalG'
    · rw [hval' r hr]
      simp only [σ3, σ2, WState.setv_val, WState.seth_val, WState.sets_val]
      by_cases hc : r = rC
      · subst hc; simp
      · rw [Function.update_of_ne hc, Function.update_of_ne hr, app_val_ne _ _ _ _ _ hc]; simp [σ1, hvals]
  · rw [hcell']; simp [σ3, σ2, σ1]

end Pose

end NearCubicGates.Adapters.Refuter.RM
