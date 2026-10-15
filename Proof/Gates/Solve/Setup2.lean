import Proof.Gates.Solve.Setup

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicGates.Close.Solve

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicGates.Close.WordPrograms.SInt
open StablePartition.Workspace (overlay)
open NearCubicGates.Close.Interfaces (startState)
open NearCubicGates.Close.Codec (copyRW copyRW_spec)

/-! ## Stage 1: unframe -/

def unframeP : WMX NS NR :=
  .seq (.wm (.whs sIN ufBody)) (.seq (addR rOP rLL rTa) (.seq (.wm (WM.rewind sRAW rOP)) (.wm (WM.rewind sIN rP2))))

theorem unframe_spec (cap : ℕ) (word : List Bool) (hcap : 2 * word.length + 2 ≤ cap) :
    WXExec cap unframeP (startState NS NR word) (((startState NS NR word).sets sRAW word).setv rLL word.length)
      (30 * word.length + 1 + 1 + (18 * word.length + 3 + 1 + (5 * word.length + 1 + 1 + (5 * (2 * word.length) + 1)))) := by
  set S0 := startState NS NR word with hS0
  have h0st : S0.st sIN = [] ++ frame word ++ [] := by simp [hS0, startState]
  have e1 := uf_loop cap [] word [] S0 h0st (by simp [hS0, startState]) (by simp (config := {decide := true}) [hS0, startState])
    (by simp [hS0, startState]; omega) (by simp [hS0, startState]; omega)
  set S1 := ufSt S0 word [] with hS1
  have hOP : S1.val rOP = word.length := by simp (config := {decide := true}) [hS1, ufSt, hS0, startState]
  have hLL : S1.val rLL = 0 := by simp (config := {decide := true}) [hS1, ufSt, hS0, startState]
  have hTa : S1.val rTa = 0 := by simp (config := {decide := true}) [hS1, ufSt, hS0, startState]
  have e2 := addR_spec cap (A := rOP) (B := rLL) (T := rTa) (by decide) (by decide) (by decide) S1 hTa
    (by rw [hOP, hLL]; omega)
  rw [hOP, hLL, Nat.zero_add] at e2
  set S2 := S1.setv rLL word.length with hS2
  have e3 := wrewind_spec (cap := cap) sRAW rOP word.length S2 (by simp (config := {decide := true}) [hS2, hOP])
    (by simp (config := {decide := true}) [hS2, hOP]; omega)
  set S3 := (S2.setv rOP 0).seth sRAW (S2.sh sRAW - word.length) with hS3
  have hP2 : S3.val rP2 = 2 * word.length := by simp (config := {decide := true}) [hS3, hS2, hS1, ufSt, hS0, startState]
  have e4 := wrewind_spec (cap := cap) sIN rP2 (2 * word.length) S3 hP2 (by rw [hP2]; omega)
  refine WXExec.cast cap (WXExec.seq (WXExec.wm e1) (WXExec.seq e2 (WXExec.seq (WXExec.wm e3) (WXExec.wm e4)))) ?_ le_rfl
  apply WState.eq
  · funext y; by_cases hy : y = sIN
    · subst hy; simp (config := {decide := true}) [hS3, hS2, hS1, ufSt, hS0, startState]
    · by_cases hyr : y = sRAW
      · subst hyr; simp (config := {decide := true}) [hS3, hS2, hS1, ufSt, hS0, startState]
      · simp [hS3, hS2, hS1, ufSt, hS0, startState, Function.update_of_ne hy, Function.update_of_ne hyr]
  · funext y; by_cases hyr : y = sRAW
    · subst hyr; simp (config := {decide := true}) [hS3, hS2, hS1, ufSt, hS0, startState]
    · simp [hS3, hS2, hS1, ufSt, hS0, startState, Function.update_of_ne hyr]
  · funext r
    by_cases h1 : r = rOP
    · subst h1; simp (config := {decide := true}) [hS3, hS2, hS1, ufSt, hS0, startState]
    · by_cases h2 : r = rP2
      · subst h2; simp (config := {decide := true}) [hS3, hS2, hS1, ufSt, hS0, startState]
      · by_cases h3 : r = rLL
        · subst h3; simp (config := {decide := true}) [hS3, hS2, hS1, ufSt, hS0, startState]
        · simp [hS3, hS2, hS1, ufSt, hS0, startState, Function.update_of_ne h1, Function.update_of_ne h2,
            Function.update_of_ne h3]
  · rfl

/-! ## Stage 2: the width registers -/

/-- `B := B + k·A`. -/
def addN (A B : Reg) : ℕ → WMX NS NR
  | 0 => WMX.skip
  | k + 1 => .seq (addR A B rTa) (addN A B k)

theorem addN_spec (cap : ℕ) {A B : Reg} (hAB : A ≠ B) (hAT : A ≠ rTa) (hBT : B ≠ rTa) :
    ∀ (k : ℕ) (σ : MS), σ.val rTa = 0 → σ.val B + k * σ.val A ≤ cap →
      WXExec cap (addN A B k) σ (σ.setv B (σ.val B + k * σ.val A)) (k * (18 * σ.val A + 4))
  | 0, σ, _, _ => by simp only [addN, Nat.zero_mul, Nat.add_zero, wsetv_same]; exact WXExec.skip cap σ
  | k + 1, σ, hT, hc => by
    have e1 := addR_spec cap hAB hAT hBT σ hT (by nlinarith)
    have e2 := addN_spec cap hAB hAT hBT k (σ.setv B (σ.val B + σ.val A)) (by simp [Function.update_of_ne hBT.symm, hT])
      (by simp [Function.update_of_ne hAB]; nlinarith)
    refine WXExec.cast cap (WXExec.seq e1 e2) ?_ (by simp [Function.update_of_ne hAB]; ring_nf; omega)
    apply WState.eq <;> try rfl
    funext r; by_cases hr : r = B
    · subst hr; simp [Function.update_of_ne hAB]; ring
    · simp [Function.update_of_ne hr]

def widthP : WMX NS NR :=
  .seq (addR rLL rT1 rTa) (.seq (WMX.inc rT1) (.seq (addN rT1 rT3 8) (.seq (mulR rT1 rK2 rT3 rWL rTa)
    (.seq (WMX.inc rWL) (.seq (addN rWL rR2 2) (.seq (WMX.inc rR2) (.seq (.wm (WM.clear rT1)) (.wm (WM.clear rT3)))))))))

theorem widthP_spec (cap : ℕ) (σ : MS) (ℓ : ℕ) (hLL : σ.val rLL = ℓ) (h0 : ∀ r ∈ [rT1, rT3, rWL, rR2, rTa, rK2], σ.val r = 0)
    (hcap : 100 * (ℓ + 2) ^ 2 ≤ cap) :
    WXExec cap widthP σ ((σ.setv rWL (wOf ℓ + 1)).setv rR2 (2 * (wOf ℓ + 1) + 1)) (1000 * (ℓ + 2) ^ 2) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at h0
  obtain ⟨hT1, hT3, hWL, hR2, hTa, hK2⟩ := h0
  have hsq : ℓ + 2 ≤ (ℓ + 2) ^ 2 := by rw [pow_two]; exact Nat.le_mul_of_pos_left _ (by omega)
  have e1 := addR_spec cap (A := rLL) (B := rT1) (T := rTa) (by decide) (by decide) (by decide) σ hTa
    (by rw [hT1, hLL]; omega)
  rw [hT1, hLL, Nat.zero_add] at e1
  set σ1 := σ.setv rT1 ℓ with hσ1
  have e2 := WXExec.inc cap rT1 σ1 (by simp [hσ1]; omega)
  set σ2 := σ1.setv rT1 (σ1.val rT1 + 1) with hσ2
  have h2T1 : σ2.val rT1 = ℓ + 1 := by simp [hσ2, hσ1]
  have e3 := addN_spec cap (A := rT1) (B := rT3) (by decide) (by decide) (by decide) 8 σ2
    (by simp (config := {decide := true}) [hσ2, hσ1, hTa]) (by rw [h2T1]; simp (config := {decide := true}) [hσ2, hσ1, hT3]; nlinarith)
  rw [h2T1] at e3
  set σ3 := σ2.setv rT3 (σ2.val rT3 + 8 * (ℓ + 1)) with hσ3
  have h3T3 : σ3.val rT3 = 8 * (ℓ + 1) := by simp (config := {decide := true}) [hσ3, hσ2, hσ1, hT3]
  have h3T1 : σ3.val rT1 = ℓ + 1 := by simp (config := {decide := true}) [hσ3, h2T1]
  have e4 := mulR_spec cap (A := rT1) (A2 := rK2) (B := rT3) (C := rWL) (T := rTa) (by decide) σ3
    (by simp (config := {decide := true}) [hσ3, hσ2, hσ1, hK2]) (by simp (config := {decide := true}) [hσ3, hσ2, hσ1, hTa])
    (by rw [h3T1, h3T3]; simp (config := {decide := true}) [hσ3, hσ2, hσ1, hWL]; nlinarith)
    (by rw [h3T1]; omega)
  rw [h3T1, h3T3] at e4
  set σ4 := σ3.setv rWL (σ3.val rWL + (ℓ + 1) * (8 * (ℓ + 1))) with hσ4
  have h4WL : σ4.val rWL = wOf ℓ := by simp (config := {decide := true}) [hσ4, hσ3, hσ2, hσ1, hWL, wOf]; ring
  have e5 := WXExec.inc cap rWL σ4 (by rw [h4WL]; unfold wOf; nlinarith)
  set σ5 := σ4.setv rWL (σ4.val rWL + 1) with hσ5
  have h5WL : σ5.val rWL = wOf ℓ + 1 := by simp [hσ5, h4WL]
  have e6 := addN_spec cap (A := rWL) (B := rR2) (by decide) (by decide) (by decide) 2 σ5
    (by simp (config := {decide := true}) [hσ5, hσ4, hσ3, hσ2, hσ1, hTa])
    (by rw [h5WL]; simp (config := {decide := true}) [hσ5, hσ4, hσ3, hσ2, hσ1, hR2]; unfold wOf; nlinarith)
  rw [h5WL] at e6
  set σ6 := σ5.setv rR2 (σ5.val rR2 + 2 * (wOf ℓ + 1)) with hσ6
  have e7 := WXExec.inc cap rR2 σ6 (by simp (config := {decide := true}) [hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, hR2]; unfold wOf; nlinarith)
  set σ7 := σ6.setv rR2 (σ6.val rR2 + 1) with hσ7
  have e8 := wclear_spec (cap := cap) rT1 (ℓ + 1) σ7 (by simp (config := {decide := true}) [hσ7, hσ6, hσ5, hσ4, h3T1])
    (by simp (config := {decide := true}) [hσ7, hσ6, hσ5, hσ4, h3T1]; omega)
  set σ8 := σ7.setv rT1 0 with hσ8
  have e9 := wclear_spec (cap := cap) rT3 (8 * (ℓ + 1)) σ8
    (by simp (config := {decide := true}) [hσ8, hσ7, hσ6, hσ5, hσ4, h3T3])
    (by simp (config := {decide := true}) [hσ8, hσ7, hσ6, hσ5, hσ4, h3T3]; omega)
  refine WXExec.cast cap (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4 (WXExec.seq e5 (WXExec.seq e6
    (WXExec.seq e7 (WXExec.seq (WXExec.wm e8) (WXExec.wm e9))))))))) ?_ ?_
  · apply WState.eq <;> try rfl
    funext r
    simp only [WState.setv_val]
    by_cases h1 : r = rR2
    · subst h1; simp (config := {decide := true}) [hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, hR2] <;> ring
    · by_cases h2 : r = rWL
      · subst h2; simp (config := {decide := true}) [hσ8, hσ7, hσ6, hσ5, h4WL]
      · by_cases h3 : r = rT1
        · subst h3; simp (config := {decide := true}) [hσ8, hT1]
        · by_cases h4 : r = rT3
          · subst h4; simp (config := {decide := true}) [hT3]
          · simp [hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_of_ne h1, Function.update_of_ne h2,
              Function.update_of_ne h3, Function.update_of_ne h4]
  · unfold wOf; nlinarith

/-! ## Stage 3: the zero word, the other words, the ruler, the word `2` -/

def zwP : WMX NS NR :=
  .seq (addR rWL rT1 rTa) (.seq (.wm (emitLoop rT1 wZ rOP [true, false])) (.seq (.wm (emitsW wZ rOP [false]))
    (.wm (WM.rewind wZ rOP))))

theorem zwP_spec (cap : ℕ) (σ : MS) (L : ℕ) (hWL : σ.val rWL = L) (hT1 : σ.val rT1 = 0) (hTa : σ.val rTa = 0)
    (hOP : σ.val rOP = 0) (hZ : σ.st wZ = []) (hZh : σ.sh wZ = 0) (hcap : 4 * L + 4 ≤ cap) :
    WXExec cap zwP σ (σ.sets wZ (frame (binary L 0))) (50 * L + 50) := by
  have e1 := addR_spec cap (A := rWL) (B := rT1) (T := rTa) (by decide) (by decide) (by decide) σ hTa
    (by rw [hT1, hWL]; omega)
  rw [hT1, hWL, Nat.zero_add] at e1
  set σ1 := σ.setv rT1 L with hσ1
  have e2 := emitLoop_spec cap rT1 wZ rOP (by decide) [true, false] L σ1 (by simp [hσ1])
    (by simp [hσ1, hZ, hZh]) (by simp (config := {decide := true}) [hσ1, hOP]; omega) (by omega)
  set σ2 := (appS σ1 wZ rOP (List.replicate L [true, false]).flatten).setv rT1 0 with hσ2
  have hl : ((List.replicate L [true, false]).flatten).length = 2 * L := by
    induction L with
    | zero => rfl
    | succ L ih => simp [List.replicate_succ, ih]; omega
  have e3 := emitsW_spec cap wZ rOP [false] σ2 (by simp (config := {decide := true}) [hσ2, appS, hσ1, hZ, hZh, hl])
    (by simp (config := {decide := true}) [hσ2, appS, hσ1, hOP, hl]; omega)
  set σ3 := appS σ2 wZ rOP [false] with hσ3
  have h3OP : σ3.val rOP = 2 * L + 1 := by simp (config := {decide := true}) [hσ3, hσ2, appS, hσ1, hOP, hl]
  have e4 := wrewind_spec (cap := cap) wZ rOP (2 * L + 1) σ3 h3OP (by rw [h3OP]; omega)
  refine WXExec.cast cap (WXExec.seq e1 (WXExec.seq (WXExec.wm e2) (WXExec.seq (WXExec.wm e3) (WXExec.wm e4)))) ?_
    (by simp; omega)
  apply WState.eq
  · funext y; by_cases hy : y = wZ
    · subst hy; simp (config := {decide := true}) [hσ3, hσ2, appS, hσ1, hZh, hl]
    · simp [hσ3, hσ2, appS, hσ1, Function.update_of_ne hy]
  · funext y; by_cases hy : y = wZ
    · subst hy; simp (config := {decide := true}) [hσ3, hσ2, appS, hσ1, hZ, frame_binary_zero]
    · simp [hσ3, hσ2, appS, hσ1, Function.update_of_ne hy]
  · funext r; by_cases h1 : r = rOP
    · subst h1; simp (config := {decide := true}) [hσ3, hσ2, appS, hσ1, hOP]
    · by_cases h2 : r = rT1
      · subst h2; simp (config := {decide := true}) [hσ3, hσ2, appS, hσ1, hT1]
      · simp [hσ3, hσ2, appS, hσ1, Function.update_of_ne h1, Function.update_of_ne h2]
  · rfl

/-- The words other than `wZ`. -/
def wList : List Str := [8, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]

def initWords : List Str → WMX NS NR
  | [] => WMX.skip
  | X :: Xs => .seq (.wm (copyRW wZ X rOP rP2 rTa)) (initWords Xs)

def setWords (σ : MS) (L : ℕ) : List Str → MS
  | [] => σ
  | X :: Xs => setWords (σ.sets X (frame (binary L 0))) L Xs

theorem initWords_spec (cap L : ℕ) (hcap : 4 * L + 4 ≤ cap) : ∀ (Xs : List Str) (σ : MS), Xs.Nodup → wZ ∉ Xs →
    σ.st wZ = frame (binary L 0) → σ.sh wZ = 0 → (∀ X ∈ Xs, σ.st X = [] ∧ σ.sh X = 0) → σ.val rOP = 0 →
    σ.val rP2 = 0 → σ.val rTa = 0 → WXExec cap (initWords Xs) σ (setWords σ L Xs) (Xs.length * (100 * L + 100))
  | [], σ, _, _, _, _, _, _, _, _ => by simpa [initWords, setWords] using WXExec.skip cap σ
  | X :: Xs, σ, hnd, hZ, hst, hsh, hX, hOP, hP2, hTa => by
    have hXZ : wZ ≠ X := fun e => hZ (by simp [e])
    have e1 := copyRW_spec (cap := cap) wZ X hXZ rOP rP2 rTa (by decide) (by decide) (by decide) (binary L 0) []
      σ (by simp [hst]) hsh (hX X (by simp)).1 (hX X (by simp)).2 hOP hP2 hTa (by simp; omega)
    have hnd' := List.nodup_cons.mp hnd
    have ih := initWords_spec cap L hcap Xs (σ.sets X (frame (binary L 0))) hnd'.2 (fun m => hZ (by simp [m]))
      (by simp [Function.update_of_ne hXZ, hst]) (by simp [hsh])
      (fun Y hY => by
        have hYX : Y ≠ X := fun e => hnd'.1 (e ▸ hY)
        simp [Function.update_of_ne hYX, hX Y (by simp [hY])]) (by simp [hOP]) (by simp [hP2]) (by simp [hTa])
    refine WXExec.mono (WXExec.seq (WXExec.wm e1) ih) ?_
    simp only [List.length_cons, binary_length]; ring_nf; omega

def rulP : WMX NS NR :=
  .seq (.wm (emitsW sRUL rOP [false])) (.seq (addR rWL rT1 rTa) (.seq (.wm (emitLoop rT1 sRUL rOP [true]))
    (.wm (WM.rewind sRUL rOP))))

theorem rulP_spec (cap : ℕ) (σ : MS) (L : ℕ) (hWL : σ.val rWL = L) (hT1 : σ.val rT1 = 0) (hTa : σ.val rTa = 0)
    (hOP : σ.val rOP = 0) (hU : σ.st sRUL = []) (hUh : σ.sh sRUL = 0) (hcap : 4 * L + 4 ≤ cap) :
    WXExec cap rulP σ (σ.sets sRUL (false :: List.replicate L true)) (50 * L + 50) := by
  have e1 := emitsW_spec cap sRUL rOP [false] σ (by simp [hU, hUh]) (by simp [hOP]; omega)
  set σ1 := appS σ sRUL rOP [false] with hσ1
  have e2 := addR_spec cap (A := rWL) (B := rT1) (T := rTa) (by decide) (by decide) (by decide) σ1
    (by simp (config := {decide := true}) [hσ1, appS, hTa]) (by simp (config := {decide := true}) [hσ1, appS, hT1, hWL]; omega)
  have h1WL : σ1.val rWL = L := by simp (config := {decide := true}) [hσ1, appS, hWL]
  rw [h1WL] at e2
  set σ2 := σ1.setv rT1 (σ1.val rT1 + L) with hσ2
  have e3 := emitLoop_spec cap rT1 sRUL rOP (by decide) [true] L σ2
    (by simp (config := {decide := true}) [hσ2, hσ1, appS, hT1, hWL]) (by simp [hσ2, hσ1, appS, hU, hUh])
    (by simp (config := {decide := true}) [hσ2, hσ1, appS, hOP]; omega) (by omega)
  set σ3 := (appS σ2 sRUL rOP (List.replicate L [true]).flatten).setv rT1 0 with hσ3
  have hl : ((List.replicate L [true]).flatten) = List.replicate L true := by
    induction L with
    | zero => rfl
    | succ L ih => simp [List.replicate_succ, ih]
  have h3OP : σ3.val rOP = L + 1 := by simp (config := {decide := true}) [hσ3, hσ2, hσ1, appS, hOP, hl]; omega
  have e4 := wrewind_spec (cap := cap) sRUL rOP (L + 1) σ3 h3OP (by rw [h3OP]; omega)
  refine WXExec.cast cap (WXExec.seq (WXExec.wm e1) (WXExec.seq e2 (WXExec.seq (WXExec.wm e3) (WXExec.wm e4)))) ?_
    (by simp; omega)
  apply WState.eq
  · funext y; by_cases hy : y = sRUL
    · subst hy; simp (config := {decide := true}) [hσ3, hσ2, hσ1, appS, hUh, hl] <;> omega
    · simp [hσ3, hσ2, hσ1, appS, Function.update_of_ne hy]
  · funext y; by_cases hy : y = sRUL
    · subst hy; simp (config := {decide := true}) [hσ3, hσ2, hσ1, appS, hU, hl]
    · simp [hσ3, hσ2, hσ1, appS, Function.update_of_ne hy]
  · funext r; by_cases h1 : r = rOP
    · subst h1; simp (config := {decide := true}) [hσ3, hσ2, hσ1, appS, hOP]
    · by_cases h2 : r = rT1
      · subst h2; simp (config := {decide := true}) [hσ3, hT1]
      · simp [hσ3, hσ2, hσ1, appS, Function.update_of_ne h1, Function.update_of_ne h2]
  · rfl

def twoP : WMX NS NR := .seq (BinW.inc wTWO wZ rF rR) (BinW.inc wTWO wZ rF rR)

theorem twoP_spec (cap : ℕ) (σ : MS) (L : ℕ) (hL : 2 ≤ L) (hT : NumOn σ wTWO L 0) (hZ : NumOn σ wZ L 0)
    (hF : σ.val rF = 0) (hR : σ.val rR = 0) (hcap : 2 * L + 1 ≤ cap) :
    WXExec cap twoP σ (σ.sets wTWO (frame (binary L 2))) (82 * L + 15) := by
  have h4 : 4 ≤ 2 ^ L := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) hL
  have e1 := BinW.inc_spec cap L (A := wTWO) (B := wZ) (F := rF) (R := rR) (by decide) (by decide) σ 0 0 hT hZ hF hR
    (by omega) hcap
  have e2 := BinW.inc_spec cap L (A := wTWO) (B := wZ) (F := rF) (R := rR) (by decide) (by decide)
    (σ.sets wTWO (frame (binary L (0 + 1)))) (0 + 1) 0 (BinW.numOn_sets_self σ wTWO L _ hT.2)
    (BinW.numOn_sets_ne hZ (by decide) _) (by simp [hF]) (by simp [hR]) (by omega) hcap
  refine WXExec.cast cap (WXExec.seq e1 e2) ?_ (by omega)
  rw [BinW.sets_sets]

end NearCubicGates.Close.Solve
