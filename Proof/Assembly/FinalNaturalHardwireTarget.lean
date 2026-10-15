import Proof.Assembly.FinalNaturalHardwireScore
import Proof.Assembly.RowsPoolSignedNative
import Proof.Amplification.RecoveryLiteralSignFrame
import Proof.CaseAnalysis.CaseTwoNativeCopy
import Proof.CaseAnalysis.RowsSignedAppend
import Proof.CaseAnalysis.FinalSelectorLoadMasks
import Proof.CaseAnalysis.WitnessGcdPolicy

/-! Physical target preparation for an exact hardwired child. The signed
target is read from the original native stream; the two resident score halves
are added on opposite sides of its positive/negative pair. The serialization
below writes the actual sign and magnitude to the live output cursor.
-/
namespace NearCubicWires.RepairSource.CloseoutFinal.C10NaturalHardwireTarget

open LocalBitMultitape RepairOrdinary RecoveryRootRound RecoveryExecution ExtDecompositionBatch
open RepairRepresentation SignedSortKey CloseoutFinalSelector

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

private theorem absorbed_signed_word (p n : ℕ) :
    intWord ((p : ℤ)-(n : ℤ))=
      (!decide (n≤p))::natWord (RowCoefficientNormalize.magnitude p n):=by
  rw [RowCoefficientNormalize.magnitude_eq]
  unfold intWord
  congr 1
  by_cases h:n≤p
  · simp only [h,decide_true,Bool.not_true]
    exact decide_eq_false (by omega)
  · simp only [h,decide_false,Bool.not_false]
    exact decide_eq_true (by omega)

def pPart (target : ℤ) (negativeScore : ℕ) := target.toNat + negativeScore
def nPart (target : ℤ) (positiveScore : ℕ) := (-target).toNat + positiveScore

theorem pair_value (target : ℤ) (positiveScore negativeScore : ℕ) :
    (pPart target negativeScore : ℤ) - (nPart target positiveScore : ℤ) =
      target - positiveScore + negativeScore := by
  unfold pPart nPart
  omega

private theorem dock_zero {t u s n : ℕ} {p : Machine t s} {input output : Fin t → List Bool}
    (h : Step p n (fun _ => 0) input (fun _ => 0) output)
    (slots : Fin t → Fin u) (hi : Function.Injective slots) (H : Fin u → ℕ) (A : Fin u → List Bool)
    (hh : ∀ j, H (slots j) = 0) (ht : ∀ j, A (slots j) = input j) :
    Step (RecoveryFocus.machine slots p) n H A H (install slots A output) :=
  (h.dock slots hi H A hh ht).congr (dockH_existing slots H (fun _ => 0) hh) rfl

def pairHeads (pos : ℕ) : Fin 21 → ℕ := fun i => if i = 0 then pos else 0
def pairExtra (w C positiveScore negativeScore : ℕ) : Fin 8 → List Bool :=
  ![MatrixScoreWeight.scalar C w positiveScore, MatrixScoreWeight.scalar C w negativeScore,
    List.replicate C false, List.replicate C false, List.replicate C false,
    List.replicate C false, List.replicate C false, List.replicate C false]
def pairInput (source : List Bool) (w C positiveScore negativeScore : ℕ) : Fin 21 → List Bool :=
  fun i => Fin.addCases (motive := fun _ => List Bool) (CloseoutRowsPoolMagnitude.input source w C)
    (pairExtra w C positiveScore negativeScore) i
def plusSlots : Fin 5 → Fin 21 := ![10, 14, 15, 16, 17]
def minusSlots : Fin 5 → Fin 21 := ![11, 13, 18, 19, 20]
noncomputable def reader := TapeEmbedding.machine 8 CloseoutRowsPoolMagnitude.machine
noncomputable def plus := RecoveryFocus.machine plusSlots MatrixScoreAccumulate.machine
noncomputable def minus := RecoveryFocus.machine minusSlots MatrixScoreAccumulate.machine
noncomputable def pairMachine := Composition.machine (Composition.machine reader plus) minus
def pairBudget (target : ℤ) (w : ℕ) := CloseoutRowsPoolMagnitude.budget target w + 1 + (12*w+13) + 1 + (12*w+13)

/-- The P/N input of the signed serializer is physically produced from the
original target field and the two supplied fixed-width score scalars. -/
theorem pair_run (pre tail : List Bool) (target : ℤ) (w C positiveScore negativeScore : ℕ)
    (hw : natBitLength target.natAbs ≤ w) (hc : 8*w+12 ≤ C)
    (hp : pPart target negativeScore < 2^w) (hn : nPart target positiveScore < 2^w) :
    ∃ out : Fin 21 → List Bool,
      Step pairMachine (pairBudget target w) (pairHeads pre.length)
        (pairInput (pre ++ intWord target ++ tail) w C positiveScore negativeScore)
        (pairHeads (pre.length + (intWord target).length)) out ∧
      out 0 = pre ++ intWord target ++ tail ∧
      out 14 = MatrixScoreWeight.scalar C w (pPart target negativeScore) ∧
      out 13 = MatrixScoreWeight.scalar C w (nPart target positiveScore) := by
  have hC : RowPowerNativeReset.rawTime target w + 1 ≤ C := by
    unfold RowPowerNativeReset.rawTime
    omega
  let source := pre ++ intWord target ++ tail
  let pos := pre.length + (intWord target).length
  let A : Fin 21 → List Bool := fun i => Fin.addCases (motive := fun _ => List Bool)
    (CloseoutRowsPoolMagnitude.output source pos w C target) (pairExtra w C positiveScore negativeScore) i
  have first := (CloseoutRowsPoolMagnitude.native_run pre tail w C target hC).embed
    (fun _ : Fin 8 => 0) (pairExtra w C positiveScore negativeScore)
  have read : Step reader (CloseoutRowsPoolMagnitude.budget target w) (pairHeads pre.length)
      (pairInput source w C positiveScore negativeScore) (pairHeads pos) A := by
    refine (first.congr_in ?_ rfl).congr ?_ rfl
    all_goals funext i; fin_cases i <;> rfl
  have second := dock_zero (Step.of_ready
    (MatrixScoreWeight.padded_accumulate C w target.toNat negativeScore (by omega) hp))
    plusSlots (by decide) (pairHeads pos) A (by intro j; fin_cases j <;> rfl) (by
      intro j; fin_cases j
      · exact (CloseoutRowsPoolMagnitude.parts source pos w C target hw).1
      all_goals rfl)
  let B := install plusSlots A
    (CloseoutRowsPoolMinimum.addOutput C w target.toNat negativeScore)
  have third := dock_zero (Step.of_ready
    (MatrixScoreWeight.padded_accumulate C w (-target).toNat positiveScore (by omega) hn))
    minusSlots (by decide) (pairHeads pos) B (by intro j; fin_cases j <;> rfl) (by
      intro j; fin_cases j
      · exact (install_other plusSlots _ _ _ (by decide)).trans
          (CloseoutRowsPoolMagnitude.parts source pos w C target hw).2
      all_goals exact (install_other plusSlots _ _ _ (by decide)).trans rfl)
  refine ⟨_, (read.seq second).seq third, ?_, ?_, ?_⟩
  · exact (install_other minusSlots _ _ _ (by decide)).trans
      ((install_other plusSlots _ _ _ (by decide)).trans (CloseoutRowsPoolMagnitude.source source pos w C target))
  · exact (install_other minusSlots _ _ _ (by decide)).trans (install_slot plusSlots (by decide) _ _ 1)
  · exact install_slot minusSlots (by decide) _ _ 1

def normalInput (w C p n : ℕ) : Fin 15 → List Bool :=
  fun i => ZeroPadding.pad C (CloseoutRowsPoolSigned.input w p n C i)
def writerExtra (C : ℕ) (out : List Bool) : Fin 5 → List Bool :=
  ![out, List.replicate C false, List.replicate C false, List.replicate C false, List.replicate C false]
def writerInput (w C p n : ℕ) (out : List Bool) : Fin 20 → List Bool :=
  fun i => Fin.addCases (motive := fun _ => List Bool) (normalInput w C p n) (writerExtra C out) i
def writerHeads (out : List Bool) : Fin 20 → ℕ := fun i => if i = 15 then out.length else 0
def frameSlots : Fin 3 → Fin 20 := ![2, 17, 18]
def signSlots : Fin 4 → Fin 20 := ![17, 9, 16, 15]
def copySlots : Fin 4 → Fin 20 := ![9, 16, 15, 19]
noncomputable def normalize := TapeEmbedding.machine 5 CloseoutRowsPoolSigned.machine
noncomputable def signFrame := RecoveryFocus.machine frameSlots RecoveryLiteralSignFrame.machine
noncomputable def sign := RecoveryFocus.machine signSlots CloseoutRowsSignedAppend.sign
noncomputable def copy := RecoveryFocus.machine copySlots CloseoutCaseTwo.NativeCopy.machine
noncomputable def writer := Composition.machine (Composition.machine (Composition.machine normalize signFrame) sign) copy
def writerBudget (w : ℕ) := (32*w+48)+1+8+1+2+1+(4*w+8)

private theorem sign_heads (out next : List Bool) :
    dockH signSlots (writerHeads out) ![0, 0, 0, next.length] = writerHeads next := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot signSlots (by decide) _ _ 0
    | exact dockH_slot signSlots (by decide) _ _ 1
    | exact dockH_slot signSlots (by decide) _ _ 2
    | exact dockH_slot signSlots (by decide) _ _ 3
    | exact dockH_other signSlots _ _ _ (by decide)

private theorem copy_heads (out next : List Bool) :
    dockH copySlots (writerHeads out) (CloseoutCaseTwo.NativeCopy.heads next) = writerHeads next := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot copySlots (by decide) _ _ 0
    | exact dockH_slot copySlots (by decide) _ _ 1
    | exact dockH_slot copySlots (by decide) _ _ 2
    | exact dockH_slot copySlots (by decide) _ _ 3
    | exact dockH_other copySlots _ _ _ (by decide)

/-- The comparison bit is physically complemented, then the actual sign bit
and native magnitude are appended. Zero follows the existing native branch. -/
theorem writer_run (w C p n : ℕ) (out : List Bool) (hw : 1 ≤ w) (hc : 8*w+12 ≤ C)
    (hp : p < 2^w) (hn : n < 2^w) :
    ∃ result : Fin 20 → List Bool,
      Step writer (writerBudget w) (writerHeads out) (writerInput w C p n out)
        (writerHeads (out ++ intWord ((p : ℤ) - n))) result ∧
      result 15 = out ++ intWord ((p : ℤ) - n) := by
  let magnitude := RowCoefficientNormalize.magnitude p n
  let flag := decide (n ≤ p)
  obtain ⟨raw, hraw, hm, hf⟩ := CloseoutRowsPoolSigned.native_run w p n C hp hn
  let A : Fin 20 → List Bool := fun i => Fin.addCases (motive := fun _ => List Bool)
    (fun j => ZeroPadding.pad C (raw j)) (writerExtra C out) i
  have actual := ((step_of_clock hraw).pad (fun _ => C)).embed
    (![out.length, 0, 0, 0, 0] : Fin 5 → ℕ) (writerExtra C out)
  have first : Step normalize (32*w+48) (writerHeads out) (writerInput w C p n out)
      (writerHeads out) A := by
    refine (actual.congr_in ?_ rfl).congr ?_ rfl
    all_goals funext i; fin_cases i <;> rfl
  have a2 : A 2 = ZeroPadding.pad C [flag] := congrArg (ZeroPadding.pad C) hf
  have a9 : A 9 = ZeroPadding.pad C (natWord magnitude) := congrArg (ZeroPadding.pad C) hm
  have hz : ZeroPadding.pad C (List.replicate 3 false) = List.replicate C false := by
    rw [ZeroPadding.pad, List.length_replicate, ← List.replicate_add]
    congr 1
    omega
  have framed : Step RecoveryLiteralSignFrame.machine 8 (fun _ => 0)
      ![ZeroPadding.pad C [flag], List.replicate C false, List.replicate C false] (fun _ => 0)
      ![ZeroPadding.pad C [flag], ZeroPadding.pad C (RepairOrdinary.frame [!flag]), List.replicate C false] := by
    have h := (step_of_clock (RecoveryLiteralSignFrame.sign_ready flag)).pad (fun _ => C)
    refine (h.congr_in rfl ?_).congr rfl ?_
    all_goals funext i; fin_cases i <;> first | rfl | exact hz
  have second := dock_zero framed frameSlots (by decide) (writerHeads out) A
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> first | exact a2 | rfl)
  let B := install frameSlots A
    (![ZeroPadding.pad C [flag], ZeroPadding.pad C (RepairOrdinary.frame [!flag]), List.replicate C false])
  let signSource := ZeroPadding.pad C (RepairOrdinary.frame [!flag])
  let next := out ++ [!flag]
  have hsign : readTapeBit signSource 1 = !flag := by
    change readTapeBit (ZeroPadding.pad C (RepairOrdinary.frame [!flag])) 1 = !flag
    rw [ZeroPadding.read_pad]
    rfl
  obtain ⟨sr, hs, hsf, hss⟩ := CloseoutRowsSignedAppend.sign_run signSource
    (ZeroPadding.pad C (natWord magnitude)) (List.replicate C false) out
  have signed : Step CloseoutRowsSignedAppend.sign 2 ![0, 0, 0, out.length]
      ![signSource, ZeroPadding.pad C (natWord magnitude), List.replicate C false, out]
      ![0, 0, 0, next.length]
      ![signSource, ZeroPadding.pad C (natWord magnitude), List.replicate C false, next] := by
    refine ⟨sr, hs, ?_, ?_, hss.le⟩
    · rw [hsf]; simp only [CloseoutRowsSignedAppend.signResult, CloseoutRowsSignedAppend.signed, hsign]; rfl
    · rw [hsf]; simp only [CloseoutRowsSignedAppend.signResult, CloseoutRowsSignedAppend.signed, hsign]; rfl
  have third := (signed.dock signSlots (by decide) (writerHeads out) B
    (by intro j; fin_cases j <;> rfl) (by
      intro j; fin_cases j
      · exact install_slot frameSlots (by decide) _ _ 1
      · exact (install_other frameSlots _ _ _ (by decide)).trans a9
      all_goals exact (install_other frameSlots _ _ _ (by decide)).trans rfl)).congr (sign_heads out next) rfl
  let D := install signSlots B
    (![signSource, ZeroPadding.pad C (natWord magnitude), List.replicate C false, next])
  have hbits : natBitLength magnitude ≤ w :=
    (CloseoutWitness.GcdGuard.bits_iff w magnitude hw).2 (CloseoutRowsPoolSigned.magnitude_fit w p n hp hn)
  obtain ⟨r, hr, rt, rh, rs⟩ := CloseoutCaseTwo.NativeCopy.append_run magnitude C next (by omega)
  have copied : Step CloseoutCaseTwo.NativeCopy.machine (4*w+8)
      (CloseoutCaseTwo.NativeCopy.heads next) (CloseoutCaseTwo.NativeCopy.input magnitude C next)
      (CloseoutCaseTwo.NativeCopy.heads (next ++ natWord magnitude))
      (CloseoutCaseTwo.NativeCopy.output magnitude C next) :=
    (Step.of_run hr rh rt).enlarge (by unfold CloseoutCaseTwo.NativeCopy.budget; omega)
  have fourth := (copied.dock copySlots (by decide) (writerHeads next) D
    (by intro j; fin_cases j <;> rfl) (by
      intro j; fin_cases j
      · exact install_slot signSlots (by decide) _ _ 1
      · exact install_slot signSlots (by decide) _ _ 2
      · exact install_slot signSlots (by decide) _ _ 3
      · exact (install_other signSlots _ _ _ (by decide)).trans
          ((install_other frameSlots _ _ _ (by decide)).trans rfl))).congr
            (copy_heads next (next ++ natWord magnitude)) rfl
  have hword : next ++ natWord magnitude = out ++ intWord ((p : ℤ) - n) := by
    rw [absorbed_signed_word]
    simp [next, magnitude, flag, List.append_assoc]
  refine ⟨install copySlots D (CloseoutCaseTwo.NativeCopy.output magnitude C next), ?_, ?_⟩
  · have whole := ((first.seq second).seq third).seq fourth
    exact whole.congr (congrArg writerHeads hword) rfl
  · exact (install_slot copySlots (by decide) D _ 2).trans hword

def writerSlots : Fin 20 → Fin 39 :=
  ![14,13,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38]
def extra (C : ℕ) (out : List Bool) : Fin 18 → List Bool :=
  fun i => if i = 13 then out else List.replicate C false
def heads (pos : ℕ) (out : List Bool) : Fin 39 → ℕ :=
  fun i => if i = 0 then pos else if i = 34 then out.length else 0
def input (source out : List Bool) (w C positiveScore negativeScore : ℕ) : Fin 39 → List Bool :=
  fun i => Fin.addCases (motive := fun _ => List Bool)
    (pairInput source w C positiveScore negativeScore) (extra C out) i
noncomputable def machine := Composition.machine (TapeEmbedding.machine 18 pairMachine)
  (RecoveryFocus.machine writerSlots writer)
def budget (target : ℤ) (w : ℕ) := pairBudget target w + 1 + writerBudget w

theorem budget_le (target : ℤ) (w : ℕ) (hw : natBitLength target.natAbs ≤ w) :
    budget target w ≤ 76*w+122 := by
  unfold budget pairBudget writerBudget CloseoutRowsPoolMagnitude.budget RowPowerNativeReset.rawTime
  omega

private theorem dock_heads (pos : ℕ) (out next : List Bool) :
    dockH writerSlots (heads pos out) (writerHeads next) = heads pos next := by
  classical
  funext i
  by_cases h : ∃ j, writerSlots j = i
  · obtain ⟨j, rfl⟩ := h
    rw [dockH_slot writerSlots (by decide)]
    fin_cases j <;> rfl
  · rw [dockH_other writerSlots _ _ i (by simpa using h)]
    have hi : i ≠ 34 := by
      intro hi
      exact h ⟨15, hi.symm⟩
    simp only [heads, if_neg hi]

/-- One fixed local machine reads the original target and appends its exact
hardwired value. Score scalars and padded workspace are physical inputs;
the original stream is preserved, with its head advanced past the target. -/
theorem target_run (pre tail out : List Bool) (target : ℤ) (w C positiveScore negativeScore : ℕ)
    (hw : natBitLength target.natAbs ≤ w) (hc : 8*w+12 ≤ C)
    (hp : pPart target negativeScore < 2^w) (hn : nPart target positiveScore < 2^w) :
    ∃ result : Fin 39 → List Bool,
      Step machine (budget target w) (heads pre.length out)
        (input (pre ++ intWord target ++ tail) out w C positiveScore negativeScore)
        (heads (pre.length + (intWord target).length)
          (out ++ intWord (target - positiveScore + negativeScore))) result ∧
      result 0 = pre ++ intWord target ++ tail ∧
      result 34 = out ++ intWord (target - positiveScore + negativeScore) := by
  obtain ⟨paired, hr, hsource, hP, hN⟩ := pair_run pre tail target w C positiveScore negativeScore hw hc hp hn
  let pos := pre.length + (intWord target).length
  let A : Fin 39 → List Bool := fun i => Fin.addCases (motive := fun _ => List Bool) paired (extra C out) i
  have embedded := hr.embed (fun i : Fin 18 => if i = 13 then out.length else 0) (extra C out)
  have first : Step (TapeEmbedding.machine 18 pairMachine) (pairBudget target w) (heads pre.length out)
      (input (pre ++ intWord target ++ tail) out w C positiveScore negativeScore) (heads pos out) A := by
    refine (embedded.congr_in ?_ rfl).congr ?_ rfl
    all_goals funext i; fin_cases i <;> rfl
  have hwidth : 1 ≤ w := by unfold natBitLength at hw; omega
  obtain ⟨written, hs, hword⟩ := writer_run w C (pPart target negativeScore) (nPart target positiveScore)
    out hwidth hc hp hn
  have hz : ZeroPadding.pad C [false] = List.replicate C false := by
    change ZeroPadding.pad C (List.replicate 1 false) = _
    rw [ZeroPadding.pad, List.length_replicate, ← List.replicate_add]
    congr 1
    omega
  have second := (hs.dock writerSlots (by decide) (heads pos out) A
    (by intro j; fin_cases j <;> rfl) (by
      intro j; fin_cases j
      all_goals first
        | exact hP
        | exact hN
        | rfl
        | exact hz.symm
        | change List.replicate C false = ZeroPadding.pad C (List.replicate C false)
          simp [ZeroPadding.pad])).congr (dock_heads pos out _) rfl
  have hfinal : out ++ intWord ((pPart target negativeScore : ℤ) - nPart target positiveScore) =
      out ++ intWord (target - positiveScore + negativeScore) := by rw [pair_value]
  refine ⟨install writerSlots A written, (first.seq second).congr (congrArg (heads pos) hfinal) rfl, ?_, ?_⟩
  · exact (install_other writerSlots _ _ _ (by decide)).trans hsource
  · exact (install_slot writerSlots (by decide) _ _ 15).trans (hword.trans hfinal)

open SupplierPipeline SupplierEstimator ThresholdCompiler

/-- This is the literal target of the paper's exact hardwired child. The
two score inputs are precisely the physical workers' selected natural sums. -/
theorem hardwire_run {q : ℕ} (live : Finset (Fin q)) (g : ExactThresholdGate q)
    (y : BitInput live.card) (pre tail out : List Bool) (w C : ℕ)
    (hw : natBitLength g.target.natAbs ≤ w) (hc : 8*w+12 ≤ C)
    (hp : pPart g.target (CloseoutRowsPoolMinimum.liveSum (C10NaturalHardwireScore.items live g y)) < 2^w)
    (hn : nPart g.target (C10NaturalHardwireScore.selectedSum (C10NaturalHardwireScore.items live g y)) < 2^w) :
    ∃ result : Fin 39 → List Bool,
      Step machine (budget g.target w) (heads pre.length out)
        (input (pre ++ intWord g.target ++ tail) out w C
          (C10NaturalHardwireScore.selectedSum (C10NaturalHardwireScore.items live g y))
          (CloseoutRowsPoolMinimum.liveSum (C10NaturalHardwireScore.items live g y)))
        (heads (pre.length + (intWord g.target).length)
          (out ++ intWord (C10SupplierRowInput.hardwire live g y).target)) result ∧
      result 0 = pre ++ intWord g.target ++ tail ∧
      result 34 = out ++ intWord (C10SupplierRowInput.hardwire live g y).target := by
  rw [C10NaturalHardwireScore.hardwire_target_parts]
  exact target_run pre tail out g.target w C _ _ hw hc hp hn

end NearCubicWires.RepairSource.CloseoutFinal.C10NaturalHardwireTarget
