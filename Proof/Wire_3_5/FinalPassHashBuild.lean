import Proof.Wire_3_5.FinalPassHashTable
import Proof.Wire_3_5.FinalPassListEvalBridge

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Hash4
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.SignedSortKey
open NearCubicWires.WireExponent3_5.GF2 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.FinalPass.ListEval

variable (cap : ℕ)

/-- One record of the input stream: the decoder modulus and the window of level `j`. -/
def winRec (J : ℕ) (Wf : ℕ → ℕ) (j : ℕ) : List Bool := true :: (unary (pow (topW J Wf j)) ++ unary (topW J Wf j))

/-- The input stream: `M`, `L`, `J`, then the records of levels `J, …, 0`. -/
def winWord (M L J : ℕ) (Wf : ℕ → ℕ) : List Bool :=
  unary M ++ unary L ++ unary J ++ (levels J).flatMap (winRec J Wf) ++ [false]

/-- The rows the builder writes. -/
def rowF (p ℓ M L : ℕ) (all : List ℕ) (j : ℕ) : List Bool := (List.range L).map (fun i => rowBit p ℓ M j i all)

/-- Set up a row: `T1 := L`, `T2 := M`, the label `X := 0`. -/
def setupRow : HProg := .seq (wcopyR rLC rT1 rIC) (.seq (wcopyR rMR rT2 rIC) (mapPass zeroOut keepS sX sP rF rR))

/-- One level record: copy the marker, the modulus and the window, then write the row. -/
def levelRec : HProg :=
  .seq (WM.fwdC sWIN rWC) (.seq (emit true) (.seq (copyUR rTC) (.seq (WM.clear rTC) (.seq (copyUR rTC)
    (.seq (WM.clear rTC) (.seq setupRow (.seq (.whr rT1 rowStep) (.seq (WM.clear rT2) (.dec rJC)))))))))

/-- The invariant of the level loop after `k` records. -/
def LInv (p ℓ M L J : ℕ) (Wf : ℕ → ℕ) (all : List ℕ) (k : ℕ) (preO : List Bool) (σ : HState) : Prop :=
  σ.st sWIN = winWord M L J Wf ∧ (σ.st sWIN).drop (σ.sh sWIN) = ((levels J).drop k).flatMap (winRec J Wf) ++ [false] ∧
  σ.val rWC = σ.sh sWIN ∧
  σ.st sO = preO ∧ σ.sh sO = preO.length ∧ σ.val rOC = preO.length ∧
  σ.val rMR = M ∧ σ.val rLC = L ∧ σ.val rJC = J - k ∧
  σ.st sSEED = seedWord ℓ all ∧ σ.sh sSEED = 0 ∧ σ.val rSC = 0 ∧
  (∃ v, σ.st sACC = frame (binary ℓ v)) ∧ σ.sh sACC = 0 ∧ (∃ v, σ.st sNEW = frame (binary ℓ v)) ∧ σ.sh sNEW = 0 ∧
  (∃ v, σ.st sST = frame (binary ℓ v)) ∧ σ.sh sST = 0 ∧ (∃ v, σ.st sX = frame (binary ℓ v)) ∧ σ.sh sX = 0 ∧
  σ.st sP = frame (binary ℓ p) ∧ σ.sh sP = 0 ∧
  σ.val rF = 0 ∧ σ.val rG = 0 ∧ σ.val rR = 0 ∧ σ.val rRY = 0 ∧
  σ.val rT1 = 0 ∧ σ.val rT2 = 0 ∧ σ.val rBAD = 0 ∧ σ.val rTC = 0 ∧ σ.val rIC = 0 ∧ σ.val rK = 0

theorem levels_drop (J k : ℕ) (hk : k ≤ J) : (levels J).drop k = (J - k) :: (levels J).drop (k + 1) := by
  unfold levels
  rw [List.drop_eq_getElem_cons (by simp; omega)]
  congr 1
  simp [List.getElem_reverse]

/-- The cost of one level record. -/
def levelCost (ℓ L M n j pw w : ℕ) : ℕ :=
  5 + 7 + (pw * 19 + 15) + (3 * pw + 1) + (w * 19 + 15) + (3 * w + 1) + (18 * L + 3) + (18 * M + 3) + (ℓ * 41 + 3) +
    (L * (stepCost ℓ n j + ℓ * 41 + 27) + 1) + (3 * M + 1) + 1 + 20

theorem winWord_length_ge (M L J : ℕ) (Wf : ℕ → ℕ) (k : ℕ) (σ : HState) (hW : σ.st sWIN = winWord M L J Wf)
    (hd : (σ.st sWIN).drop (σ.sh sWIN) = ((levels J).drop k).flatMap (winRec J Wf) ++ [false]) :
    σ.sh sWIN + (((levels J).drop k).flatMap (winRec J Wf)).length + 1 = (winWord M L J Wf).length := by
  have h := congrArg List.length hd
  rw [List.length_drop, hW] at h
  simp only [List.length_append, List.length_singleton] at h
  have hpos : σ.sh sWIN < (winWord M L J Wf).length := by
    by_contra hc
    rw [List.drop_eq_nil_of_le (by rw [hW]; omega)] at hd
    simp at hd
  omega

theorem levelRec_spec (p ℓ M L J : ℕ) (Wf : ℕ → ℕ) (all : List ℕ) (k : ℕ) (preO : List Bool) (σ : HState)
    (j w pw : ℕ) (hjk : J - k = j) (hw : topW J Wf j = w) (hpw : pow w = pw)
    (hk : k ≤ J) (hℓ : 1 ≤ ℓ) (hcapS : (seedWord ℓ all).length + 2 * ℓ + 2 ≤ cap)
    (hcapW : (winWord M L J Wf).length ≤ cap) (hL : L ≤ cap) (hM : M ≤ cap) (hJ : J ≤ cap)
    (hO : preO.length + (ListEval.record J Wf (rowF p ℓ M L all) j).length ≤ cap)
    (hI : LInv p ℓ M L J Wf all k preO σ) :
    ∃ τ, WExec cap levelRec σ τ (levelCost ℓ L M all.length j pw w) ∧
      LInv p ℓ M L J Wf all (k + 1) (preO ++ ListEval.record J Wf (rowF p ℓ M L all) j) τ := by
  obtain ⟨hW, hWd, hWC, hO1, hO2, hOC, hMR, hLC, hJC, hSD, hhSD, hSC, hA, hhA, hN, hhN, hS, hhS, ⟨vX, hX⟩, hhX, hP, hhP,
    hF, hG, hR, hRY, hT1, hT2, hB, hTC, hIC, hK⟩ := hI
  have hWd' : (σ.st sWIN).drop (σ.sh sWIN) = true :: (List.replicate pw true ++ false :: (List.replicate w true ++
      false :: (((levels J).drop (k + 1)).flatMap (winRec J Wf) ++ [false]))) := by
    rw [hWd, levels_drop J k hk, List.flatMap_cons, hjk]; simp [winRec, unary, hw, hpw]
  have hWlen := winWord_length_ge M L J Wf k σ hW hWd
  rw [levels_drop J k hk, List.flatMap_cons, hjk] at hWlen
  simp only [winRec, unary, List.length_append, List.length_cons, List.length_replicate, hw, hpw] at hWlen
  have hRec : (ListEval.record J Wf (rowF p ℓ M L all) j).length = 1 + (pw + 1) + (w + 1) + L := by
    simp [ListEval.record, unary, rowF, hw, hpw]; omega
  rw [hRec] at hO
  rw [hjk] at hJC
  -- 1, 2: the record marker
  have r1 := wfwdC_spec cap sWIN rWC σ (by omega)
  obtain ⟨σ1, hσ1⟩ : ∃ τ : HState, τ = (σ.seth sWIN (σ.sh sWIN + 1)).setv rWC (σ.val rWC + 1) := ⟨_, rfl⟩
  rw [← hσ1] at r1
  have r2 := emit_spec cap true σ1 (by rw [hσ1]; simp [hO1, hO2]) (by rw [hσ1]; simp [hOC]; omega)
  obtain ⟨σ2, hσ2⟩ : ∃ τ : HState, τ = ((σ1.sets sO ((σ1.st sO) ++ [true])).seth sO (σ1.sh sO + 1)).setv rOC
      (σ1.val rOC + 1) := ⟨_, rfl⟩
  rw [← hσ2] at r2
  -- 3, 4: the modulus
  have hd2 : (σ2.st sWIN).drop (σ2.sh sWIN) = List.replicate pw true ++ false :: (List.replicate w true ++ false ::
      (((levels J).drop (k + 1)).flatMap (winRec J Wf) ++ [false])) := by
    rw [hσ2, hσ1]; simp; exact dropSucc (a := true) hWd'
  have r3 := copyUR_spec cap rTC (by decide) (by decide) _ pw σ2 hd2 (by rw [hσ2, hσ1]; simp [hO1, hO2])
    (by rw [hσ2, hσ1]; simp [hOC]; omega) (by rw [hσ2, hσ1]; simp [hWC]; omega) (by rw [hσ2, hσ1]; simp [hTC]; omega)
  have r4 := wclear_spec cap rTC pw (copyState' rTC pw σ2) (by unfold copyState'; rw [hσ2, hσ1]; simp [hTC])
    (by unfold copyState'; rw [hσ2, hσ1]; simp [hTC]; omega)
  obtain ⟨σ4, hσ4⟩ : ∃ τ : HState, τ = (copyState' rTC pw σ2).setv rTC 0 := ⟨_, rfl⟩
  rw [← hσ4] at r4
  -- 5, 6: the window
  have hd4 : (σ4.st sWIN).drop (σ4.sh sWIN) = List.replicate w true ++ false ::
      (((levels J).drop (k + 1)).flatMap (winRec J Wf) ++ [false]) := by
    rw [hσ4]; unfold copyState'; simp
    have := dropAppend (a := List.replicate pw true ++ [false])
      (t := List.replicate w true ++ false :: (((levels J).drop (k + 1)).flatMap (winRec J Wf) ++ [false])) (by rw [hd2]; simp)
    simp at this; rw [hσ2, hσ1] at this ⊢; simpa [Nat.add_assoc] using this
  have r5 := copyUR_spec cap rTC (by decide) (by decide) _ w σ4 hd4 (by rw [hσ4]; unfold copyState'; simp; rw [hσ2, hσ1]; simp [hO1, hO2]; omega)
    (by rw [hσ4]; unfold copyState'; rw [hσ2, hσ1]; simp [hOC]; omega)
    (by rw [hσ4]; unfold copyState'; rw [hσ2, hσ1]; simp [hWC]; omega) (by rw [hσ4]; simp; omega)
  have r6 := wclear_spec cap rTC w (copyState' rTC w σ4) (by unfold copyState'; rw [hσ4]; simp)
    (by unfold copyState'; rw [hσ4]; simp; omega)
  obtain ⟨σ6, hσ6⟩ : ∃ τ : HState, τ = (copyState' rTC w σ4).setv rTC 0 := ⟨_, rfl⟩
  rw [← hσ6] at r6
  -- 7: set up the row
  have h6T1 : σ6.val rT1 = 0 := by rw [hσ6]; unfold copyState'; rw [hσ4]; unfold copyState'; rw [hσ2, hσ1]; simp [hT1]
  have h6IC : σ6.val rIC = 0 := by rw [hσ6]; unfold copyState'; rw [hσ4]; unfold copyState'; rw [hσ2, hσ1]; simp [hIC]
  have h6LC : σ6.val rLC = L := by rw [hσ6]; unfold copyState'; rw [hσ4]; unfold copyState'; rw [hσ2, hσ1]; simp [hLC]
  have h6MR : σ6.val rMR = M := by rw [hσ6]; unfold copyState'; rw [hσ4]; unfold copyState'; rw [hσ2, hσ1]; simp [hMR]
  have h6T2 : σ6.val rT2 = 0 := by rw [hσ6]; unfold copyState'; rw [hσ4]; unfold copyState'; rw [hσ2, hσ1]; simp [hT2]
  have r7a := wcopyR_spec cap rLC rT1 rIC (by decide) (by decide) (by decide) σ6 h6T1 h6IC (by rw [h6LC]; exact hL)
  rw [h6LC] at r7a
  have r7b := wcopyR_spec cap rMR rT2 rIC (by decide) (by decide) (by decide) (σ6.setv rT1 L) (by simp [h6T2])
    (by simp [h6IC]) (by simp [h6MR]; exact hM)
  have e7b : (σ6.setv rT1 L).val rMR = M := by simp [h6MR]
  rw [e7b] at r7b
  obtain ⟨σ7b, hσ7b⟩ : ∃ τ : HState, τ = (σ6.setv rT1 L).setv rT2 M := ⟨_, rfl⟩
  rw [← hσ7b] at r7b
  have hfr6 : ∀ q : Fin 8, q ≠ sO → q ≠ sWIN → σ6.st q = σ.st q ∧ σ6.sh q = σ.sh q := by
    intro q h1 h2
    rw [hσ6]; unfold copyState'; rw [hσ4]; unfold copyState'; rw [hσ2, hσ1]
    simp [Function.update_of_ne h1, Function.update_of_ne h2]
  have h7X : σ7b.st sX = frameP (binary ℓ vX) ++ false :: [] := by
    rw [hσ7b]; simp; rw [(hfr6 sX (by decide) (by decide)).1, hX, frame_eq_frameP]
  have r7c := mapPass_spec cap zeroOut keepS sX sP rF rR (by decide) (by decide) (by omega) (binary ℓ vX) (binary ℓ p)
    [] [false] false σ7b (by simp) h7X (by rw [hσ7b]; simp; rw [(hfr6 sX (by decide) (by decide)).2, hhX])
    (by rw [hσ7b]; simp; rw [(hfr6 sP (by decide) (by decide)).1, hP, frame_eq_frameP])
    (by rw [hσ7b]; simp; rw [(hfr6 sP (by decide) (by decide)).2, hhP])
    (by rw [hσ7b, hσ6]; unfold copyState'; rw [hσ4]; unfold copyState'; rw [hσ2, hσ1]; simp [hF])
    (by rw [hσ7b, hσ6]; unfold copyState'; rw [hσ4]; unfold copyState'; rw [hσ2, hσ1]; simp [hR]) (by simp; omega)
  rw [mapS_zero _ _ _ (by simp)] at r7c
  obtain ⟨σ7, hσ7⟩ : ∃ τ : HState, τ = (σ7b.sets sX (frameP (List.replicate (binary ℓ vX).length false) ++ false :: [])).setv
      rF (false).toNat := ⟨_, rfl⟩
  rw [← hσ7] at r7c
  -- 8: the row
  obtain ⟨preO', hpreO'⟩ : ∃ l : List Bool, l = preO ++ [true] ++ (List.replicate pw true ++ [false]) ++
      (List.replicate w true ++ [false]) := ⟨_, rfl⟩
  have h7O : σ7.st sO = preO' := by
    rw [hσ7, hσ7b, hσ6]; unfold copyState'; rw [hσ4]; unfold copyState'; rw [hσ2, hσ1]; simp [hO1, hpreO']
  have h7Osh : σ7.sh sO = preO'.length := by
    rw [hσ7, hσ7b, hσ6]; unfold copyState'; rw [hσ4]; unfold copyState'; rw [hσ2, hσ1]; simp [hO2, hpreO']; omega
  have h7OC : σ7.val rOC = preO'.length := by
    rw [hσ7, hσ7b, hσ6]; unfold copyState'; rw [hσ4]; unfold copyState'; rw [hσ2, hσ1]; simp [hOC, hpreO']; omega
  have hRI : RowInv p ℓ M L j all 0 preO' σ7 := by
    have f7 : ∀ q : Fin 8, q ≠ sO → q ≠ sWIN → q ≠ sX → σ7.st q = σ.st q ∧ σ7.sh q = σ.sh q := by
      intro q h1 h2 h3
      rw [hσ7, hσ7b]; simp [Function.update_of_ne h3]; exact hfr6 q h1 h2
    have fv : ∀ r : Fin 16, r ≠ rOC → r ≠ rWC → r ≠ rTC → r ≠ rT1 → r ≠ rT2 → r ≠ rF → σ7.val r = σ.val r := by
      intro r h1 h2 h3 h4 h5 h6
      rw [hσ7, hσ7b, hσ6]; unfold copyState'; rw [hσ4]; unfold copyState'; rw [hσ2, hσ1]
      simp [Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3, Function.update_of_ne h4,
        Function.update_of_ne h5, Function.update_of_ne h6]
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, h7O, h7Osh, h7OC, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_⟩
    · rw [(f7 sSEED (by decide) (by decide) (by decide)).1, hSD]
    · rw [(f7 sSEED (by decide) (by decide) (by decide)).2, hhSD]
    · rw [fv rSC (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hSC]
    · rw [(f7 sACC (by decide) (by decide) (by decide)).1]; exact hA
    · rw [(f7 sACC (by decide) (by decide) (by decide)).2, hhA]
    · rw [(f7 sNEW (by decide) (by decide) (by decide)).1]; exact hN
    · rw [(f7 sNEW (by decide) (by decide) (by decide)).2, hhN]
    · rw [(f7 sST (by decide) (by decide) (by decide)).1]; exact hS
    · rw [(f7 sST (by decide) (by decide) (by decide)).2, hhS]
    · rw [hσ7]; simp [frame_eq_frameP, binary_zero]
    · rw [hσ7, hσ7b]; simp; rw [(hfr6 sX (by decide) (by decide)).2, hhX]
    · rw [(f7 sP (by decide) (by decide) (by decide)).1, hP]
    · rw [(f7 sP (by decide) (by decide) (by decide)).2, hhP]
    · rw [hσ7]; simp
    · rw [fv rG (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hG]
    · rw [fv rR (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hR]
    · rw [fv rRY (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hRY]
    · rw [hσ7, hσ7b]; simp
    · rw [hσ7, hσ7b]; simp
    · rw [fv rJC (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hJC]
    · rw [fv rBAD (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hB]
    · rw [hσ7, hσ7b, hσ6]; simp
    · rw [fv rIC (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hIC]
    · rw [fv rK (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hK]
  obtain ⟨τ8, r8, hRI8, hF8⟩ := rowLoop_spec cap p ℓ M L j all hℓ hcapS (by omega) hL hM L 0 preO' σ7 (by omega)
    (by simp [hpreO']; omega) hRI
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17⟩ := hRI8.1
  obtain ⟨_, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10⟩ := hRI8
  -- 9, 10: clear `T2`, next level
  have r9 := wclear_spec cap rT2 (M - L) τ8 c5 (by omega)
  have r10 := WExec.dec (cap := cap) rJC (τ8.setv rT2 0) (by simp [c6]; omega)
  refine ⟨_, WExec.mono (WExec.seq r1 (WExec.seq r2 (WExec.seq r3 (WExec.seq r4 (WExec.seq r5 (WExec.seq r6
    (WExec.seq (WExec.seq r7a (WExec.seq r7b r7c)) (WExec.seq r8 (WExec.seq r9 r10)))))))))
    (by unfold levelCost; simp only [binary_length]; omega), ?_⟩
  have fW := hF8.1 sWIN (by simp [rowS])
  have h7W : σ7.st sWIN = σ.st sWIN ∧ σ7.sh sWIN = σ.sh sWIN + 1 + (pw + 1) + (w + 1) := by
    rw [hσ7, hσ7b, hσ6]; unfold copyState'; rw [hσ4]; unfold copyState'; rw [hσ2, hσ1]; simp; omega
  have h7WC : σ7.val rWC = σ.val rWC + 1 + (pw + 1) + (w + 1) := by
    rw [hσ7, hσ7b, hσ6]; unfold copyState'; rw [hσ4]; unfold copyState'; rw [hσ2, hσ1]; simp; omega
  have fWC := hF8.2.1 rWC (by simp [rowR])
  have fMR := hF8.2.1 rMR (by simp [rowR])
  have fLC := hF8.2.1 rLC (by simp [rowR])
  have h7MR : σ7.val rMR = M := by rw [hσ7, hσ7b]; simp [h6MR]
  have h7LC : σ7.val rLC = L := by rw [hσ7, hσ7b]; simp [h6LC]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · simp; rw [fW.1, h7W.1, hW]
  · simp only [WState.setv_st, WState.setv_sh]; rw [fW.1, fW.2, h7W.1, h7W.2]
    have := dropAppend (a := true :: (List.replicate pw true ++ false :: (List.replicate w true ++ [false]))) (t := ((levels J).drop (k + 1)).flatMap (winRec J Wf) ++ [false])
      (p := σ.sh sWIN) (l := σ.st sWIN) (by rw [hWd']; simp)
    simp only [List.length_cons, List.length_append, List.length_replicate, List.length_nil] at this
    convert this using 2
    omega
  · simp only [WState.setv_val, WState.setv_sh]
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), fWC, h7WC, fW.2, h7W.2, hWC]
  · simp; rw [c1]; simp [hpreO', ListEval.record, unary, rowF, List.range_eq_range', hw, hpw]
  · simp; rw [c2]; simp [hpreO', ListEval.record, unary, rowF, hw, hpw]
  · simp only [WState.setv_val]
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), c3]
    simp [hpreO', ListEval.record, unary, rowF, hw, hpw]
  · simp only [WState.setv_val]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), fMR, h7MR]
  · simp only [WState.setv_val]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), fLC, h7LC]
  · simp [c6]; omega
  · simp [b1]
  · simp [b2]
  · simp [b3]
  · simpa using b4
  · simp [b5]
  · simpa using b6
  · simp [b7]
  · simpa using b8
  · simp [b9]
  · exact ⟨L, by simpa using b10⟩
  · simp [b11]
  · simp [b12]
  · simp [b13]
  · simp [b14]
  · simp [b15]
  · simp [b16]
  · simp [b17]
  · simp [c4]
  · simp
  · simp [c7]
  · simp [c8]
  · simp [c9]
  · simp [c10]

/-! ## The loop over the level records -/

theorem record_length_rowF (p ℓ M L J : ℕ) (Wf : ℕ → ℕ) (all : List ℕ) (j : ℕ) :
    (ListEval.record J Wf (rowF p ℓ M L all) j).length = 3 + pow (topW J Wf j) + topW J Wf j + L := by
  simp [ListEval.record, unary, rowF]; omega

theorem levelLoop_spec (p ℓ M L J : ℕ) (Wf : ℕ → ℕ) (all : List ℕ) (hℓ : 1 ≤ ℓ)
    (hcapS : (seedWord ℓ all).length + 2 * ℓ + 2 ≤ cap) (hcapW : (winWord M L J Wf).length ≤ cap) (hL : L ≤ cap)
    (hM : M ≤ cap) (hJ : J ≤ cap) (C : ℕ) (hC : ∀ j ≤ J, levelCost ℓ L M all.length j (pow (topW J Wf j)) (topW J Wf j) ≤ C) :
    ∀ (n k : ℕ) (preO : List Bool) (σ : HState), k + n = J + 1 →
      preO.length + (((levels J).drop k).flatMap (ListEval.record J Wf (rowF p ℓ M L all))).length ≤ cap →
      LInv p ℓ M L J Wf all k preO σ →
      ∃ τ, WExec cap (.whs sWIN levelRec) σ τ (n * (C + 2) + 1) ∧
        LInv p ℓ M L J Wf all (J + 1) (preO ++ ((levels J).drop k).flatMap (ListEval.record J Wf (rowF p ℓ M L all))) τ
  | 0, k, preO, σ, hn, _, hI => by
    have hk : k = J + 1 := by omega
    subst hk
    have hdrop : (levels J).drop (J + 1) = [] := by simp [levels]
    refine ⟨σ, WExec.mono (WExec.whsF ?_) (by omega), ?_⟩
    · unfold wbit
      have := readDrop (σ.st sWIN) (σ.sh sWIN) 0
      simp only [Nat.add_zero] at this
      rw [this, hI.2.1, hdrop]; rfl
    · rw [hdrop]; simpa using hI
  | n + 1, k, preO, σ, hn, hO, hI => by
    have hk : k ≤ J := by omega
    have hread : wbit σ sWIN = true := by
      unfold wbit
      have := readDrop (σ.st sWIN) (σ.sh sWIN) 0
      simp only [Nat.add_zero] at this
      rw [this, hI.2.1, levels_drop J k hk]; rfl
    rw [levels_drop J k hk, List.flatMap_cons, List.length_append] at hO
    obtain ⟨τ1, s1, hI1⟩ := levelRec_spec cap p ℓ M L J Wf all k preO σ (J - k) _ _ rfl rfl rfl hk hℓ hcapS hcapW hL hM hJ
      (by omega) hI
    obtain ⟨τ, s2, hI2⟩ := levelLoop_spec p ℓ M L J Wf all hℓ hcapS hcapW hL hM hJ C hC n (k + 1) _ τ1 (by omega)
      (by simp only [List.length_append]; omega) hI1
    refine ⟨τ, WExec.mono (WExec.whsT hread s1 s2) (by have := hC (J - k) (by omega); ring_nf; nlinarith), ?_⟩
    rw [levels_drop J k hk, List.flatMap_cons, ← List.append_assoc]
    exact hI2

/-! ## The whole builder -/

theorem onesDrop {l t : List Bool} {p n : ℕ} (h : l.drop p = List.replicate n true ++ false :: t) :
    (∀ k < n, readTapeBit l (p + k) = true) ∧ readTapeBit l (p + n) = false := by
  refine ⟨fun k hk => ?_, ?_⟩
  · rw [readDrop, h]
    unfold readTapeBit
    rw [List.getD_append _ _ _ _ (by simpa using hk)]
    simp [hk]
  · rw [readDrop, h]
    unfold readTapeBit
    rw [List.getD_append_right _ _ _ _ (by simp)]
    simp

/-- Clear the counts and return the input and output heads. -/
def cleanup4 : HProg :=
  .seq (WM.clear rMR) (.seq (WM.clear rLC) (.seq (WM.clear rJC) (.seq (WM.rewind sWIN rWC) (WM.rewind sO rOC))))

/-- **The table builder.** -/
def build : HProg :=
  .seq (copyUR rMR) (.seq (WM.readU sWIN rWC rLC) (.seq (WM.readU sWIN rWC rJC) (.seq (.whs sWIN levelRec)
    (.seq (emit false) cleanup4))))

/-- The ready state of the builder. -/
def BReady (p ℓ M L J : ℕ) (Wf : ℕ → ℕ) (all : List ℕ) (σ : HState) : Prop :=
  σ.st sWIN = winWord M L J Wf ∧ σ.sh sWIN = 0 ∧ σ.val rWC = 0 ∧ σ.st sO = [] ∧ σ.sh sO = 0 ∧ σ.val rOC = 0 ∧
  σ.val rMR = 0 ∧ σ.val rLC = 0 ∧ σ.val rJC = 0 ∧
  σ.st sSEED = seedWord ℓ all ∧ σ.sh sSEED = 0 ∧ σ.val rSC = 0 ∧
  (∃ v, σ.st sACC = frame (binary ℓ v)) ∧ σ.sh sACC = 0 ∧ (∃ v, σ.st sNEW = frame (binary ℓ v)) ∧ σ.sh sNEW = 0 ∧
  (∃ v, σ.st sST = frame (binary ℓ v)) ∧ σ.sh sST = 0 ∧ (∃ v, σ.st sX = frame (binary ℓ v)) ∧ σ.sh sX = 0 ∧
  σ.st sP = frame (binary ℓ p) ∧ σ.sh sP = 0 ∧
  σ.val rF = 0 ∧ σ.val rG = 0 ∧ σ.val rR = 0 ∧ σ.val rRY = 0 ∧
  σ.val rT1 = 0 ∧ σ.val rT2 = 0 ∧ σ.val rBAD = 0 ∧ σ.val rTC = 0 ∧ σ.val rIC = 0 ∧ σ.val rK = 0

theorem winWord_eq (M L J : ℕ) (Wf : ℕ → ℕ) : winWord M L J Wf = List.replicate M true ++ false ::
    (List.replicate L true ++ false :: (List.replicate J true ++ false :: ((levels J).flatMap (winRec J Wf) ++ [false]))) := by
  simp [winWord, unary]

/-- The step count of the builder. -/
def buildCost (M L J C Wn On : ℕ) : ℕ :=
  (M * 19 + 15) + (11 * L + 7) + (11 * J + 7) + ((J + 1) * (C + 2) + 1) + 7 + (3 * M + 1) + (3 * L + 1) + 1 +
    (5 * Wn + 1) + (5 * On + 1) + 20

theorem build_spec (p ℓ M L J : ℕ) (Wf : ℕ → ℕ) (all : List ℕ) (σ : HState) (hℓ : 1 ≤ ℓ)
    (hcapS : (seedWord ℓ all).length + 2 * ℓ + 2 ≤ cap) (hcapW : (winWord M L J Wf).length ≤ cap)
    (hcapO : (levelWord M J Wf (rowF p ℓ M L all)).length + 1 ≤ cap) (hL : L ≤ cap) (hM : M ≤ cap) (hJ : J ≤ cap)
    (C : ℕ) (hC : ∀ j ≤ J, levelCost ℓ L M all.length j (pow (topW J Wf j)) (topW J Wf j) ≤ C)
    (hR : BReady p ℓ M L J Wf all σ) :
    ∃ τ, WExec cap build σ τ (buildCost M L J C (winWord M L J Wf).length (levelWord M J Wf (rowF p ℓ M L all)).length) ∧
      τ.st sO = levelWord M J Wf (rowF p ℓ M L all) ∧ τ.sh sO = 0 ∧ τ.st sWIN = winWord M L J Wf ∧ τ.sh sWIN = 0 ∧
      τ.st sSEED = seedWord ℓ all ∧ τ.st sP = frame (binary ℓ p) ∧ τ.val rMR = 0 ∧ τ.val rLC = 0 ∧ τ.val rJC = 0 ∧
      τ.val rWC = 0 ∧ τ.val rOC = 0 := by
  obtain ⟨hW, hhW, hWC, hO, hhO, hOC, hMR, hLC, hJC, hSD, hhSD, hSC, hA, hhA, hN, hhN, hS, hhS, hX, hhX, hP, hhP,
    hF, hG, hRr, hRY, hT1, hT2, hB, hTC, hIC, hK⟩ := hR
  have hWlen : (winWord M L J Wf).length = M + 1 + (L + 1) + (J + 1) + ((levels J).flatMap (winRec J Wf)).length + 1 := by
    simp [winWord, unary]; omega
  have hOlen : (levelWord M J Wf (rowF p ℓ M L all)).length =
      M + 1 + ((levels J).flatMap (ListEval.record J Wf (rowF p ℓ M L all))).length + 1 := by
    simp [levelWord, unary]; omega
  -- 1: `M`
  have hd0 : (σ.st sWIN).drop (σ.sh sWIN) = List.replicate M true ++ false ::
      (List.replicate L true ++ false :: (List.replicate J true ++ false :: ((levels J).flatMap (winRec J Wf) ++ [false]))) := by
    rw [hW, hhW, List.drop_zero, winWord_eq]
  have b1 := copyUR_spec cap rMR (by decide) (by decide) _ M σ hd0 (by rw [hhO, hO]; rfl) (by rw [hOC]; omega)
    (by rw [hWC]; omega) (by rw [hMR]; omega)
  obtain ⟨σ1, hσ1⟩ : ∃ τ : HState, τ = copyState' rMR M σ := ⟨_, rfl⟩
  rw [← hσ1] at b1
  -- 2, 3: `L`, `J`
  have hd1 : (σ1.st sWIN).drop (σ1.sh sWIN) = List.replicate L true ++ false ::
      (List.replicate J true ++ false :: ((levels J).flatMap (winRec J Wf) ++ [false])) := by
    rw [hσ1]; unfold copyState'; simp
    have := dropAppend (a := List.replicate M true ++ [false]) (t := List.replicate L true ++ false ::
      (List.replicate J true ++ false :: ((levels J).flatMap (winRec J Wf) ++ [false]))) (by rw [hd0]; simp)
    rw [hhW] at this ⊢; simpa using this
  obtain ⟨o1, e1⟩ := onesDrop hd1
  have b2 := wreadU_spec cap sWIN rWC rLC (by decide) L σ1 o1 e1 (by rw [hσ1]; unfold copyState'; simp [hWC]; omega)
    (by rw [hσ1]; unfold copyState'; simp [hLC]; omega)
  obtain ⟨σ2, hσ2⟩ : ∃ τ : HState, τ = ((σ1.seth sWIN (σ1.sh sWIN + L + 1)).setv rWC (σ1.val rWC + L + 1)).setv rLC
      (σ1.val rLC + L) := ⟨_, rfl⟩
  rw [← hσ2] at b2
  have hd2 : (σ2.st sWIN).drop (σ2.sh sWIN) = List.replicate J true ++ false :: ((levels J).flatMap (winRec J Wf) ++ [false]) := by
    rw [hσ2]; simp
    have := dropAppend (a := List.replicate L true ++ [false]) (t := List.replicate J true ++ false ::
      ((levels J).flatMap (winRec J Wf) ++ [false])) (by rw [hd1]; simp)
    simpa [Nat.add_assoc] using this
  obtain ⟨o2, e2⟩ := onesDrop hd2
  have b3 := wreadU_spec cap sWIN rWC rJC (by decide) J σ2 o2 e2 (by rw [hσ2, hσ1]; unfold copyState'; simp [hWC]; omega)
    (by rw [hσ2, hσ1]; unfold copyState'; simp [hJC]; omega)
  obtain ⟨σ3, hσ3⟩ : ∃ τ : HState, τ = ((σ2.seth sWIN (σ2.sh sWIN + J + 1)).setv rWC (σ2.val rWC + J + 1)).setv rJC
      (σ2.val rJC + J) := ⟨_, rfl⟩
  rw [← hσ3] at b3
  -- the loop
  have hI3 : LInv p ℓ M L J Wf all 0 (List.replicate M true ++ [false]) σ3 := by
    have hd3 : (σ3.st sWIN).drop (σ3.sh sWIN) = (levels J).flatMap (winRec J Wf) ++ [false] := by
      rw [hσ3]; simp
      have := dropAppend (a := List.replicate J true ++ [false]) (t := (levels J).flatMap (winRec J Wf) ++ [false])
        (by rw [hd2]; simp)
      simpa [Nat.add_assoc] using this
    refine ⟨?_, by simpa using hd3, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [hσ3, hσ2, hσ1] <;> unfold copyState' <;>
      simpo [hW, hhW, hWC, hO, hhO, hOC, hMR, hLC, hJC, hSD, hhSD, hSC, hA, hhA, hN, hhN, hS, hhS, hX, hhX, hP, hhP, hF,
        hG, hRr, hRY, hT1, hT2, hB, hTC, hIC, hK]
  obtain ⟨τ4, b4, hI4⟩ := levelLoop_spec cap p ℓ M L J Wf all hℓ hcapS hcapW hL hM hJ C hC (J + 1) 0 _ σ3 (by omega)
    (by simp; rw [hOlen] at hcapO; simp at hcapO; omega) hI3
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24,
    g25, g26, g27, g28, g29, g30, g31, g32⟩ := hI4
  simp only [List.drop_zero] at g4 g5 g6
  -- the final `false`
  have b5 := emit_spec cap false τ4 (by rw [g4, g5]) (by rw [g6]; rw [hOlen] at hcapO; simp at hcapO ⊢; omega)
  obtain ⟨τ5, hτ5⟩ : ∃ τ : HState, τ = ((τ4.sets sO ((τ4.st sO) ++ [false])).seth sO (τ4.sh sO + 1)).setv rOC
      (τ4.val rOC + 1) := ⟨_, rfl⟩
  rw [← hτ5] at b5
  -- cleanup
  have c1 := wclear_spec cap rMR M τ5 (by rw [hτ5]; simp [g7]) (by rw [hτ5]; simp [g7]; omega)
  have c2 := wclear_spec cap rLC L (τ5.setv rMR 0) (by rw [hτ5]; simp [g8]) (by rw [hτ5]; simp [g8]; omega)
  have c3 := wclear_spec cap rJC 0 ((τ5.setv rMR 0).setv rLC 0) (by rw [hτ5]; simp [g9]) (by rw [hτ5]; simp [g9])
  have hWsh : τ4.sh sWIN + 1 = (winWord M L J Wf).length := by
    have := winWord_length_ge M L J Wf (J + 1) τ4 g1 g2
    have hd : (levels J).drop (J + 1) = [] := by simp [levels]
    rw [hd] at this; simpa using this
  have c4 := wrewind_spec cap sWIN rWC (τ4.sh sWIN) (((τ5.setv rMR 0).setv rLC 0).setv rJC 0) (by rw [hτ5]; simp [g3])
    (by rw [hτ5]; simp [g3]; omega)
  have c5 := wrewind_spec cap sO rOC (τ4.sh sO + 1) (((((τ5.setv rMR 0).setv rLC 0).setv rJC 0).setv rWC 0).seth sWIN
    ((((τ5.setv rMR 0).setv rLC 0).setv rJC 0).sh sWIN - τ4.sh sWIN)) (by rw [hτ5]; simp [g6, g5])
    (by rw [hτ5]; simp [g6]; rw [hOlen] at hcapO; simp at hcapO; omega)
  refine ⟨_, WExec.mono (WExec.seq b1 (WExec.seq b2 (WExec.seq b3 (WExec.seq b4 (WExec.seq b5 (WExec.seq c1
    (WExec.seq c2 (WExec.seq c3 (WExec.seq c4 c5))))))))) ?_, ?_⟩
  · unfold buildCost
    rw [hOlen]; simp only [g5, List.length_append, List.length_replicate, List.length_singleton]
    omega
  · rw [hτ5]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simpo [g1, g4, g5, g10, g21, levelWord, unary, List.append_assoc]

/-! ## The builder writes the majorant's list table -/

open NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Lists in

theorem rowBit_eq (MP : MajorantParams) (s : Fin (2 * MP.t * MP.ell0) → Bool) (j i : ℕ) :
    rowBit MP.refMod MP.ell0 MP.M j i (coefsRev (MajorantBits.coefVal MP s)) = MajorantBits.inLevelBits MP s j i := by
  unfold rowBit MajorantBits.inLevelBits MajorantBits.valueBits
  rw [hornerBits_fold]

open NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Lists in
/-- **The builder's rows are the list's rows** at the hash seed. -/
theorem rowF_eq (MP : MajorantParams) (s : Fin (2 * MP.t * MP.ell0) → Bool) (L : ℕ) :
    rowF MP.refMod MP.ell0 MP.M L (coefsRev (MajorantBits.coefVal MP s)) = rowsOf (MajorantBits.dataBits MP s) L := by
  funext j
  unfold rowF rowsOf
  congr 1
  funext i
  exact rowBit_eq MP s j i

end NearCubicWires.WireExponent3_5.FinalPass.Hash4
