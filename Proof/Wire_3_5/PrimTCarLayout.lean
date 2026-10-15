import Proof.Wire_3_5.PrimTCarBounds
import Proof.Wire_3_5.PrimTTabSymStages
import Proof.CaseAnalysis.WitnessCanonicalFields

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.PrimT.CarTable
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.PrimT NearCubicWires.WireExponent3_5.PrimT.CarWM
open NearCubicWires.WireExponent3_5.PrimT.CarStages NearCubicWires.WireExponent3_5.PrimT.CarFold
open NearCubicWires.WireExponent3_5.PrimT.CarBounds NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)

/-! ## Slot maps -/

def cellSl : Fin 1 → Fin 1357 := fun _ => 6
def prepSl : Fin 13 → Fin 1357 := ![0, 6, 1, 2, 7, 8, 9, 10, 11, 12, 13, 14, 15]
def ctSl (j : Fin 174) : Fin 1357 := ⟨if j.val = 0 then 7 else 15 + j.val, by split_ifs <;> omega⟩
def powSl (j : Fin 114) : Fin 1357 := ⟨if j.val = 0 then 8 else 188 + j.val, by split_ifs <;> omega⟩
def initSl : Fin 3 → Fin 1357 := ![304, 6, 1344]
def eraseSl (j : Fin (1039 + 1 + 1)) : Fin 1357 :=
  ⟨if j.val = 0 then 303 else if j.val = 1039 then 291 else if j.val = 1040 then 1343 else 304 + j.val,
    by split_ifs <;> omega⟩
def foldSl (j : Fin (1041 + 2 + 1)) : Fin 1357 :=
  ⟨if j.val = 0 then 45 else if j.val = 1041 then 291 else if j.val = 1042 then 1343 else if j.val = 1043 then 56
    else 302 + j.val, by split_ifs <;> omega⟩
def scan1Sl : Fin 9 → Fin 1357 := ![304, 6, 1345, 1346, 1347, 5, 1348, 12, 1349]
def scan2Sl : Fin 9 → Fin 1357 := ![304, 6, 1350, 1351, 1352, 1353, 1354, 12, 1355]
def maskSl : Fin 13 → Fin 1357 := ![1345, 6, 1346, 1, 1347, 3, 4, 1350, 1351, 12, 13, 14, 1356]

theorem cellSl_inj : Function.Injective cellSl := fun a b _ => Subsingleton.elim a b
theorem prepSl_inj : Function.Injective prepSl := by decide
theorem initSl_inj : Function.Injective initSl := by decide
theorem scan1Sl_inj : Function.Injective scan1Sl := by decide
theorem scan2Sl_inj : Function.Injective scan2Sl := by decide
theorem maskSl_inj : Function.Injective maskSl := by decide
theorem ctSl_inj : Function.Injective ctSl := by
  intro a b h; have hv := congrArg Fin.val h; simp only [ctSl] at hv; apply Fin.ext; split_ifs at hv <;> omega
theorem powSl_inj : Function.Injective powSl := by
  intro a b h; have hv := congrArg Fin.val h; simp only [powSl] at hv; apply Fin.ext; split_ifs at hv <;> omega
theorem eraseSl_inj : Function.Injective eraseSl := by
  intro a b h; have hv := congrArg Fin.val h; simp only [eraseSl] at hv
  have := a.isLt; have := b.isLt; apply Fin.ext; split_ifs at hv <;> omega
theorem foldSl_inj : Function.Injective foldSl := by
  intro a b h; have hv := congrArg Fin.val h; simp only [foldSl] at hv
  have := a.isLt; have := b.isLt; apply Fin.ext; split_ifs at hv <;> omega

theorem prepSl_val (j : Fin 13) : (prepSl j).val = [0, 6, 1, 2, 7, 8, 9, 10, 11, 12, 13, 14, 15].getD j.val 0 := by
  fin_cases j <;> rfl
theorem initSl_val (j : Fin 3) : (initSl j).val = [304, 6, 1344].getD j.val 0 := by fin_cases j <;> rfl
theorem scan1Sl_val (j : Fin 9) : (scan1Sl j).val = [304, 6, 1345, 1346, 1347, 5, 1348, 12, 1349].getD j.val 0 := by
  fin_cases j <;> rfl
theorem scan2Sl_val (j : Fin 9) : (scan2Sl j).val = [304, 6, 1350, 1351, 1352, 1353, 1354, 12, 1355].getD j.val 0 :=
  by fin_cases j <;> rfl
theorem maskSl_val (j : Fin 13) :
    (maskSl j).val = [1345, 6, 1346, 1, 1347, 3, 4, 1350, 1351, 12, 13, 14, 1356].getD j.val 0 := by
  fin_cases j <;> rfl

/-! ## Misses -/

section Miss
variable (A : Fin 1357 → List Bool) (t : Fin 1357)

theorem miss_cell (h : t.val ≠ 6) (o : Fin 1 → List Bool) : install cellSl A o t = A t :=
  install_other _ _ _ _ (fun _ e => h (by rw [← e]; rfl))
theorem miss_prep (h : 16 ≤ t.val ∨ (3 ≤ t.val ∧ t.val ≤ 5)) (o : Fin 13 → List Bool) : install prepSl A o t = A t :=
  install_other _ _ _ _ (fun j e => by
    have hv := congrArg Fin.val e; rw [prepSl_val] at hv; fin_cases j <;> simp at hv <;> omega)
theorem miss_ct (h : t.val ≠ 7 ∧ (t.val < 16 ∨ 189 ≤ t.val)) (o : Fin 174 → List Bool) : install ctSl A o t = A t :=
  install_other _ _ _ _ (fun j e => by
    have hv := congrArg Fin.val e; simp only [ctSl] at hv; have := j.isLt; split_ifs at hv <;> omega)
theorem miss_pow (h : t.val ≠ 8 ∧ (t.val < 189 ∨ 302 ≤ t.val)) (o : Fin 114 → List Bool) : install powSl A o t = A t :=
  install_other _ _ _ _ (fun j e => by
    have hv := congrArg Fin.val e; simp only [powSl] at hv; have := j.isLt; split_ifs at hv <;> omega)
theorem miss_init (h : t.val ≠ 304 ∧ t.val ≠ 6 ∧ t.val ≠ 1344) (o : Fin 3 → List Bool) : install initSl A o t = A t :=
  install_other _ _ _ _ (fun j e => by
    have hv := congrArg Fin.val e; rw [initSl_val] at hv; fin_cases j <;> simp at hv <;> omega)
theorem miss_erase (h : t.val ≠ 303 ∧ t.val ≠ 291 ∧ t.val ≠ 1343 ∧ (t.val < 305 ∨ 1343 ≤ t.val))
    (o : Fin (1039 + 1 + 1) → List Bool) : install eraseSl A o t = A t :=
  install_other _ _ _ _ (fun j e => by
    have hv := congrArg Fin.val e; simp only [eraseSl] at hv; have := j.isLt; split_ifs at hv <;> omega)
theorem miss_fold (h : t.val ≠ 45 ∧ t.val ≠ 56 ∧ t.val ≠ 291 ∧ t.val ≠ 1343 ∧ (t.val < 303 ∨ 1343 ≤ t.val))
    (o : Fin (1041 + 2 + 1) → List Bool) : install foldSl A o t = A t :=
  install_other _ _ _ _ (fun j e => by
    have hv := congrArg Fin.val e; simp only [foldSl] at hv; have := j.isLt; split_ifs at hv <;> omega)
theorem miss_scan1 (h : ∀ j, (scan1Sl j).val ≠ t.val) (o : Fin 9 → List Bool) : install scan1Sl A o t = A t :=
  install_other _ _ _ _ (fun j e => h j (congrArg Fin.val e))
theorem miss_scan2 (h : ∀ j, (scan2Sl j).val ≠ t.val) (o : Fin 9 → List Bool) : install scan2Sl A o t = A t :=
  install_other _ _ _ _ (fun j e => h j (congrArg Fin.val e))
theorem miss_mask (h : ∀ j, (maskSl j).val ≠ t.val) (o : Fin 13 → List Bool) : install maskSl A o t = A t :=
  install_other _ _ _ _ (fun j e => h j (congrArg Fin.val e))

end Miss

/-! ## The machines -/

noncomputable def cellC := RecoveryFocus.machine cellSl cellM
noncomputable def prepC := RecoveryFocus.machine prepSl (Rewind.machine (prepW (nr := 0) SymTab.spP).toProg.compile)
noncomputable def ctC := RecoveryFocus.machine ctSl CloseoutWitness.CanonicalTest.machine
noncomputable def powC := RecoveryFocus.machine powSl (PCPSerializerCapacity.Power.machine 50 cC2)
noncomputable def initC := RecoveryFocus.machine initSl (Rewind.machine initW.toProg.compile)
noncomputable def eraseC := RecoveryFocus.machine eraseSl (RecoveryScratchErase.resetMachine 1039)
noncomputable def foldC := RecoveryFocus.machine foldSl foldM
noncomputable def scan1C := RecoveryFocus.machine scan1Sl (Rewind.machine (scanW SymTab.scS SymTab.rgS).toProg.compile)
noncomputable def scan2C := RecoveryFocus.machine scan2Sl (Rewind.machine (scanW SymTab.scS SymTab.rgS).toProg.compile)
noncomputable def maskC := RecoveryFocus.machine maskSl (Rewind.machine mskW2.toProg.compile)

/-- **The carrier table machine.** -/
noncomputable def carTableM :=
  Composition.machine cellC (Composition.machine prepC (Composition.machine ctC (Composition.machine powC
    (Composition.machine initC (Composition.machine eraseC (Composition.machine foldC (Composition.machine scan1C
      (Composition.machine scan2C maskC))))))))

/-- The machine's entry: the call's framed code, `1^n`, `1^L`; every other tape blank. -/
def carIn (code n L : ℕ) : Fin 1357 → List Bool := fun t =>
  if t.val = 0 then frame (natWord code) else if t.val = 1 then List.replicate n true
  else if t.val = 2 then List.replicate L true else []

theorem carIn_blank (code n L : ℕ) (t : Fin 1357) (h : 3 ≤ t.val) : carIn code n L t = [] := by
  unfold carIn; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-! ## The erase's banks -/

def erIn (T : ℕ) : Fin (1039 + 1 + 1) → List Bool :=
  Fin.addCases (m := 1039 + 1) (n := 1) (motive := fun _ => List Bool)
    (Fin.addCases (m := 1039) (n := 1) (motive := fun _ => List Bool) (fun _ => ([] : List Bool))
      (fun _ => List.replicate T true)) (fun _ => List.replicate 0 false)
def erOut (T : ℕ) : Fin (1039 + 1 + 1) → List Bool :=
  Fin.addCases (m := 1039 + 1) (n := 1) (motive := fun _ => List Bool)
    (Fin.addCases (m := 1039) (n := 1) (motive := fun _ => List Bool) (fun _ => List.replicate T false)
      (fun _ => List.replicate T true)) (fun _ => List.replicate (max 0 (T + 1)) false)

theorem erIn_val (T : ℕ) (j : Fin (1039 + 1 + 1)) : erIn T j = if j.val = 1039 then List.replicate T true else [] := by
  refine Fin.addCases (m := 1039 + 1) (n := 1) (fun a => ?_) (fun b => ?_) j
  · refine Fin.addCases (m := 1039) (n := 1) (fun a' => ?_) (fun b' => ?_) a
    · simp only [erIn, Fin.addCases_left]; rw [if_neg (by simp; omega)]
    · simp only [erIn, Fin.addCases_left, Fin.addCases_right]; rw [if_pos (by simp)]
  · simp only [erIn, Fin.addCases_right]; rw [if_neg (by simp)]; rfl

theorem erOut_val (T : ℕ) (j : Fin (1039 + 1 + 1)) : erOut T j = if j.val < 1039 then List.replicate T false
    else if j.val = 1039 then List.replicate T true else List.replicate (T + 1) false := by
  refine Fin.addCases (m := 1039 + 1) (n := 1) (fun a => ?_) (fun b => ?_) j
  · refine Fin.addCases (m := 1039) (n := 1) (fun a' => ?_) (fun b' => ?_) a
    · simp only [erOut, Fin.addCases_left]; rw [if_pos (by simp)]
    · simp only [erOut, Fin.addCases_left, Fin.addCases_right]; rw [if_neg (by simp), if_pos (by simp)]
  · simp only [erOut, Fin.addCases_right]; rw [if_neg (by simp), if_neg (by simp)]; simp

/-! ## The atom loop's banks -/

theorem addCases_val {m k : ℕ} {β : Type} (f : Fin m → β) (g : Fin k → β) (j : Fin (m + k)) :
    Fin.addCases (motive := fun _ => β) f g j = if h : j.val < m then f ⟨j.val, h⟩ else g ⟨j.val - m, by omega⟩ := by
  refine Fin.addCases (fun a => ?_) (fun b => ?_) j
  · simp [a.isLt]
  · simp

/-- The loop's entry and exit at atom `i`, by tape. -/
theorem foldBank_val {n : ℕ} (W T : ℕ) (X : List (NormalizedThresholdGate n)) (i c : ℕ) (j : Fin (1041 + 2 + 1)) :
    Fin.addCases (m := 1041 + 2) (n := 1) (motive := fun _ => List Bool)
      (roundTapes (padScratch CarFold.scr T (Qc W T X i)) T (T + 1))
      (fun _ => RepairSource.VerifierDecoding.CompareMachine.word c) j =
    if j.val = 0 then (CarRound.rawAtoms W X).flatMap frame
    else if j.val = 1 then ZeroPadding.pad T (List.replicate i true)
    else if j.val = 2 then accHdr ++ tabSeg (X.take i)
    else if j.val < 1041 then List.replicate T false
    else if j.val = 1041 then List.replicate T true
    else if j.val = 1042 then List.replicate (T + 1) false
    else RepairSource.VerifierDecoding.CompareMachine.word c := by
  rw [addCases_val]
  by_cases h1 : j.val < 1041 + 2
  · rw [dif_pos h1]; unfold roundTapes; rw [addCases_val]
    by_cases h2 : j.val < 1041
    · rw [dif_pos h2]
      unfold padScratch scratchCap
      by_cases h3 : 3 ≤ j.val
      · rw [if_pos ((CarFold.scr_iff ⟨j.val, h2⟩).mpr h3)]
        simp only [Qc, CarRound.roundIn]
        have e0 : j.val ≠ 0 := by omega
        have e1 : j.val ≠ 1 := by omega
        have e2 : j.val ≠ 2 := by omega
        simp [e0, e1, e2, h2, ZeroPadding.pad]
      · rw [if_neg (fun hh => h3 ((CarFold.scr_iff ⟨j.val, h2⟩).mp hh))]
        simp only [Qc, CarRound.roundIn, ZeroPadding.pad_zero]
        have : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 := by omega
        rcases this with e | e | e <;> simp [e]
    · rw [dif_neg h2]
      have : j.val = 1041 ∨ j.val = 1042 := by omega
      rcases this with e | e <;> simp [e]
  · rw [dif_neg h1]
    have e : j.val = 1043 := by omega
    simp [e]

end NearCubicWires.WireExponent3_5.PrimT.CarTable
