import Proof.Gates.Solve.Setup2

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

theorem setWords_st (L : ℕ) : ∀ (Xs : List Str) (σ : MS) (Y : Str),
    (setWords σ L Xs).st Y = if Y ∈ Xs then frame (binary L 0) else σ.st Y
  | [], σ, Y => by simp [setWords]
  | X :: Xs, σ, Y => by
    rw [setWords, setWords_st L Xs]
    by_cases h1 : Y ∈ Xs
    · simp [h1]
    · by_cases h2 : Y = X
      · subst h2; simp [h1]
      · simp [h1, h2, Function.update_of_ne h2]

theorem setWords_sh (L : ℕ) : ∀ (Xs : List Str) (σ : MS), (setWords σ L Xs).sh = σ.sh
  | [], σ => rfl
  | X :: Xs, σ => by rw [setWords, setWords_sh L Xs]; rfl

theorem setWords_val (L : ℕ) : ∀ (Xs : List Str) (σ : MS), (setWords σ L Xs).val = σ.val
  | [], σ => rfl
  | X :: Xs, σ => by rw [setWords, setWords_val L Xs]; rfl

theorem setWords_cell (L : ℕ) : ∀ (Xs : List Str) (σ : MS), (setWords σ L Xs).cell = σ.cell
  | [], σ => rfl
  | X :: Xs, σ => by rw [setWords, setWords_cell L Xs]; rfl

/-- The whole setup. -/
def setupP : WMX NS NR := .seq unframeP (.seq widthP (.seq zwP (.seq (initWords wList) (.seq rulP twoP))))

/-- The state after the setup. -/
def setS (word : List Bool) : MS :=
  ((setWords (((((startState NS NR word).sets sRAW word).setv rLL word.length).setv rWL (wOf word.length + 1)).setv rR2
    (2 * (wOf word.length + 1) + 1) |>.sets wZ (frame (binary (wOf word.length + 1) 0))) (wOf word.length + 1)
    wList).sets sRUL (false :: List.replicate (wOf word.length + 1) true)).sets wTWO
    (frame (binary (wOf word.length + 1) 2))

/-- The cost bound of the setup. -/
def setupCost (ℓ : ℕ) : ℕ := 30000 * (ℓ + 2) ^ 2

/-- The cap the setup needs. -/
def setupCap (ℓ : ℕ) : ℕ := 100 * (ℓ + 2) ^ 2

theorem setup_spec (cap : ℕ) (word : List Bool) (hcap : setupCap word.length ≤ cap) :
    WXExec cap setupP (startState NS NR word) (setS word) (setupCost word.length) := by
  set ℓ := word.length with hℓ
  set L := wOf ℓ + 1 with hL
  have hsq : ℓ + 2 ≤ (ℓ + 2) ^ 2 := by rw [pow_two]; exact Nat.le_mul_of_pos_left _ (by omega)
  have hLb : L ≤ 9 * (ℓ + 2) ^ 2 := by
    rw [hL]; unfold wOf
    have : (ℓ + 1) ^ 2 ≤ (ℓ + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  unfold setupCap at hcap
  have e1 := unframe_spec cap word (by omega)
  set S1 := ((startState NS NR word).sets sRAW word).setv rLL ℓ with hS1
  have e2 := widthP_spec cap S1 ℓ (by simp [hS1]) (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp (config := {decide := true}) [hS1, startState])
    (by omega)
  set S2 := (S1.setv rWL L).setv rR2 (2 * L + 1) with hS2
  have e3 := zwP_spec cap S2 L (by simp (config := {decide := true}) [hS2]) (by simp (config := {decide := true}) [hS2, hS1, startState])
    (by simp (config := {decide := true}) [hS2, hS1, startState]) (by simp (config := {decide := true}) [hS2, hS1, startState])
    (by simp (config := {decide := true}) [hS2, hS1, startState]) (by simp [hS2, hS1, startState]) (by omega)
  set S3 := S2.sets wZ (frame (binary L 0)) with hS3
  have e4 := initWords_spec cap L (by omega) wList S3 (by decide) (by decide) (by simp [hS3]) (by simp [hS3, hS2, hS1, startState])
    (by
      intro X hX
      have hX9 : X ≠ wZ := fun e => by subst e; revert hX; decide
      have hX2 : X ≠ sRAW := fun e => by subst e; revert hX; decide
      have hX0 : X.val ≠ 0 := fun e => by
        have : X = sIN := Fin.ext e
        subst this; revert hX; decide
      have hX0' : X ≠ (0 : Str) := fun e => hX0 (by rw [e]; rfl)
      simp [hS3, hS2, hS1, startState, Function.update_of_ne hX9, Function.update_of_ne hX2, hX0, hX0'])
    (by simp (config := {decide := true}) [hS3, hS2, hS1, startState])
    (by simp (config := {decide := true}) [hS3, hS2, hS1, startState])
    (by simp (config := {decide := true}) [hS3, hS2, hS1, startState])
  set S4 := setWords S3 L wList with hS4
  have e5 := rulP_spec cap S4 L (by rw [hS4, setWords_val]; simp (config := {decide := true}) [hS3, hS2])
    (by rw [hS4, setWords_val]; simp (config := {decide := true}) [hS3, hS2, hS1, startState])
    (by rw [hS4, setWords_val]; simp (config := {decide := true}) [hS3, hS2, hS1, startState])
    (by rw [hS4, setWords_val]; simp (config := {decide := true}) [hS3, hS2, hS1, startState])
    (by rw [hS4, setWords_st]; simp (config := {decide := true}) [wList, hS3, hS2, hS1, startState])
    (by rw [hS4, setWords_sh]; simp [hS3, hS2, hS1, startState]) (by omega)
  set S5 := S4.sets sRUL (false :: List.replicate L true) with hS5
  have hL2 : 2 ≤ L := by rw [hL]; unfold wOf; have : 1 ≤ (ℓ + 1) ^ 2 := Nat.one_le_pow _ _ (by omega); omega
  have e6 := twoP_spec cap S5 L hL2
    ⟨by rw [hS5]; simp (config := {decide := true}); rw [hS4, setWords_st]; simp (config := {decide := true}) [wList],
      by rw [hS5]; simp (config := {decide := true}); rw [hS4, setWords_sh]; simp [hS3, hS2, hS1, startState]⟩
    ⟨by rw [hS5]; simp (config := {decide := true}); rw [hS4, setWords_st]; simp (config := {decide := true}) [wList, hS3],
      by rw [hS5]; simp (config := {decide := true}); rw [hS4, setWords_sh]; simp [hS3, hS2, hS1, startState]⟩
    (by rw [hS5]; simp only [WState.sets_val]; rw [hS4, setWords_val]; simp (config := {decide := true}) [hS3, hS2, hS1, startState])
    (by rw [hS5]; simp only [WState.sets_val]; rw [hS4, setWords_val]; simp (config := {decide := true}) [hS3, hS2, hS1, startState])
    (by omega)
  refine WXExec.mono (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4 (WXExec.seq e5 e6))))) ?_
  unfold setupCost
  simp only [wList, List.length_cons, List.length_nil]
  omega

/-- The word values after the setup. -/
def v0 : Str → ℕ := fun X => if X = wTWO then 2 else 0

theorem setS_val (word : List Bool) (r : Reg) : (setS word).val r =
    if r = rR2 then 2 * (wOf word.length + 1) + 1 else if r = rWL then wOf word.length + 1 else
      if r = rLL then word.length else 0 := by
  simp only [setS, WState.sets_val, setWords_val, WState.setv_val, Function.update_apply]
  by_cases h1 : r = rR2 <;> by_cases h2 : r = rWL <;> by_cases h3 : r = rLL <;> simp_all [startState]

theorem setS_sh (word : List Bool) (X : Str) : (setS word).sh X = 0 := by
  simp [setS, setWords_sh, startState]

theorem setS_st_word (word : List Bool) {X : Str} (hX : X ∈ wset) :
    (setS word).st X = frame (binary (wOf word.length + 1) (v0 X)) := by
  simp only [setS, WState.sets_st, Function.update_apply, v0]
  by_cases h1 : X = wTWO
  · simp [h1]
  · have h2 : X ≠ sRUL := fun e => by subst e; revert hX; decide
    simp only [h1, h2, if_false, setWords_st]
    by_cases h3 : X ∈ wList
    · simp [h3]
    · have : X = wZ := by
        revert hX h3; generalize X = Y; revert Y; decide
      subst this; simp

theorem setup_at (word : List Bool) : At (setS word) (setS word) (wOf word.length) v0 := by
  refine ⟨fun X hX => ⟨setS_st_word word hX, setS_sh word X⟩, fun r hr => ?_, SameExcept.refl _ _ _⟩
  rw [setS_val]
  have h1 : r ≠ rR2 := fun e => by subst e; revert hr; decide
  have h2 : r ≠ rWL := fun e => by subst e; revert hr; decide
  have h3 : r ≠ rLL := fun e => by subst e; revert hr; decide
  simp [h1, h2, h3]

theorem setS_st_data (word : List Bool) :
    (setS word).st sIN = frame word ∧ (setS word).st sRAW = word ∧
      (setS word).st sRUL = false :: List.replicate (wOf word.length + 1) true ∧
      ∀ X ∈ [sOUT, sPT, sSG, sMAT, sNEW, sWR, (29 : Str), (30 : Str), (31 : Str)], (setS word).st X = [] := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp (config := {decide := true}) [setS, setWords_st, wList, startState]
  · simp (config := {decide := true}) [setS, setWords_st, wList, startState]
  · simp (config := {decide := true}) [setS]
  · intro X hX
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hX
    rcases hX with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (config := {decide := true}) [setS, setWords_st, wList, startState]

end NearCubicGates.Close.Solve
