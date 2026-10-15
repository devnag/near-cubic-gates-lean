import Proof.Assembly.FinalNaturalHardwireTarget
import Proof.Assembly.FinalPoolJoin
import Proof.Hierarchy.HierarchyAllocation

/-! Physical positive and negative frozen-score producers on one native
signed weight source and one raw assignment mask. The positive pass pays a
masked head reset; the negative pass leaves the source at its original target.
The source view starts at head zero. Zero scalars, width, padded scratch,
driver/log tapes, and repeat template are explicit physical inputs. This file
does not initialize them or identify a membership mask with an assignment mask.
-/
namespace NearCubicWires.RepairSource.CloseoutFinal.C10NaturalHardwireScoreInputs

open LocalBitMultitape RepairOrdinary RecoveryRootRound RecoveryExecution ExtDecompositionBatch
open RepairRepresentation VerifierDecoding CloseoutRowsPoolWeight

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-- The existing two native loops with exact preserved scratch and template. -/
theorem loop_steps (xs : List Item) (tail mtail : List Bool) (w C : ℕ)
    (hw : ∀ x ∈ xs, natBitLength x.1.natAbs ≤ w) (hc : 8*w+12 ≤ C)
    (hp : C10NaturalHardwireScore.positiveSum xs < 2^w)
    (hn : CloseoutRowsPoolMinimum.negSum xs < 2^w) :
Step C10NaturalHardwireScore.loop (C10NaturalHardwireScore.loopBudget xs w C) (CloseoutFinalPool.mH 0 0) (CloseoutFinalPool.mT (CloseoutRowsPoolWeight.word xs ++ tail) (CloseoutRowsPoolWeight.mask xs ++ mtail) w C 0 xs.length) (CloseoutFinalPool.mH (CloseoutRowsPoolWeight.word xs).length xs.length) (CloseoutFinalPool.mT (CloseoutRowsPoolWeight.word xs ++ tail) (CloseoutRowsPoolWeight.mask xs ++ mtail) w C (C10NaturalHardwireScore.selectedSum xs) xs.length) ∧ Step CloseoutRowsPoolMinimum.loop (CloseoutRowsPoolMinimum.loopBudget xs w C) (CloseoutFinalPool.mH 0 0) (CloseoutFinalPool.mT (CloseoutRowsPoolWeight.word xs ++ tail) (CloseoutRowsPoolWeight.mask xs ++ mtail) w C 0 xs.length) (CloseoutFinalPool.mH (CloseoutRowsPoolWeight.word xs).length xs.length) (CloseoutFinalPool.mT (CloseoutRowsPoolWeight.word xs ++ tail) (CloseoutRowsPoolWeight.mask xs ++ mtail) w C (CloseoutRowsPoolMinimum.liveSum xs) xs.length) := by
  constructor
  · obtain ⟨r, hr, hf, _⟩ := C10NaturalHardwireScore.score_run xs [] tail [] mtail w C 0 hw hc (by simpa using hp)
    have actual := CloseoutFinalPool.step_of_repeat C10NaturalHardwireScore.body (fun _ _ => true) (C10NaturalHardwireScore.loopBudget xs w C)
      ⟨C10NaturalHardwireScore.body.start, CloseoutRowsPoolMinimum.heads 0 0, CloseoutRowsPoolMinimum.data (CloseoutRowsPoolWeight.word xs ++ tail) (CloseoutRowsPoolWeight.mask xs ++ mtail) w C 0⟩
      ⟨C10NaturalHardwireScore.body.start, CloseoutRowsPoolMinimum.heads (CloseoutRowsPoolWeight.word xs).length xs.length,
        CloseoutRowsPoolMinimum.data (CloseoutRowsPoolWeight.word xs ++ tail) (CloseoutRowsPoolWeight.mask xs ++ mtail) w C (C10NaturalHardwireScore.selectedSum xs)⟩ xs.length 1 1 r
      (by simpa only [C10NaturalHardwireScore.loop, C10NaturalHardwireScore.cfg, List.nil_append, List.length_nil] using hr)
      (by simpa only [C10NaturalHardwireScore.cfg, List.nil_append, List.length_nil, Nat.zero_add] using hf)
    exact actual
  · obtain ⟨r, hr, hf, _⟩ := CloseoutRowsPoolMinimum.minimum_run xs [] tail [] mtail w C 0 hw hc (by simpa using hn)
    have actual := CloseoutFinalPool.step_of_repeat CloseoutRowsPoolMinimum.body (fun _ _ => true) (CloseoutRowsPoolMinimum.loopBudget xs w C)
      ⟨CloseoutRowsPoolMinimum.body.start, CloseoutRowsPoolMinimum.heads 0 0, CloseoutRowsPoolMinimum.data (CloseoutRowsPoolWeight.word xs ++ tail) (CloseoutRowsPoolWeight.mask xs ++ mtail) w C 0⟩
      ⟨CloseoutRowsPoolMinimum.body.start, CloseoutRowsPoolMinimum.heads (CloseoutRowsPoolWeight.word xs).length xs.length,
        CloseoutRowsPoolMinimum.data (CloseoutRowsPoolWeight.word xs ++ tail) (CloseoutRowsPoolWeight.mask xs ++ mtail) w C (CloseoutRowsPoolMinimum.liveSum xs)⟩ xs.length 1 1 r
      (by simpa only [CloseoutRowsPoolMinimum.loop, CloseoutRowsPoolMinimum.cfg, List.nil_append, List.length_nil] using hr)
      (by simpa only [CloseoutRowsPoolMinimum.cfg, List.nil_append, List.length_nil, Nat.zero_add] using hf)
    exact actual

def positiveSlots : Fin 22 → Fin 44 :=
  ![0,1,2,3,4,5,6,7,8,9,10,11,12,39,13,15,16,17,40,41,42,43]
def negativeSlots : Fin 21 → Fin 44 :=
  ![0,1,2,3,4,5,6,7,8,9,10,11,12,39,14,15,16,17,40,41,42]
def resetSelected : Fin 21 → Bool := fun i => decide (i=0 ∨ i=13)
def heads (out : List Bool) (pos mpos : ℕ) : Fin 44 → ℕ :=
  fun i => if i=0 then pos else if i=34 then out.length else if i=39 then mpos else if i=42 then 1 else 0

def extra (membership : List Bool) (C D total : ℕ) : Fin 5 → List Bool :=
  ![membership, List.replicate C true, List.replicate (C+1) false,
    CompareMachine.word total, List.replicate D false]

def data (source membership out : List Bool) (w C D total positive negative : ℕ) : Fin 44 → List Bool :=
  Fin.addCases (motive := fun _ => List Bool)
    (C10NaturalHardwireTarget.input source out w C positive negative) (extra membership C D total)

noncomputable def positive := RecoveryFocus.machine positiveSlots
  (MaskedReset.machine C10NaturalHardwireScore.loop resetSelected)
noncomputable def negative := RecoveryFocus.machine negativeSlots CloseoutRowsPoolMinimum.loop
noncomputable def machine := Composition.machine positive negative

def budget (xs : List Item) (w C : ℕ) :=
  2*C10NaturalHardwireScore.loopBudget xs w C+2+1+CloseoutRowsPoolMinimum.loopBudget xs w C

/-- Both input scalars of the target worker are physically produced. The
same original native stream and raw mask are preserved. The first pass's
reset log is preserved at its padded capacity; there is no second rewind. -/
theorem run (xs : List Item) (tail mtail out : List Bool) (w C D : ℕ)
    (hw : ∀ x ∈ xs, natBitLength x.1.natAbs ≤ w) (hc : 8*w+12 ≤ C)
    (hp : C10NaturalHardwireScore.positiveSum xs < 2^w)
    (hn : CloseoutRowsPoolMinimum.negSum xs < 2^w)
    (hD : C10NaturalHardwireScore.loopBudget xs w C ≤ D) :
    Step machine (budget xs w C) (heads out 0 0)
      (data (word xs++tail) (mask xs++mtail) out w C D xs.length 0 0)
      (heads out (word xs).length xs.length)
      (data (word xs++tail) (mask xs++mtail) out w C D xs.length
        (C10NaturalHardwireScore.selectedSum xs) (CloseoutRowsPoolMinimum.liveSum xs)) := by
  classical
  have hloops := loop_steps xs tail mtail w C hw hc hp hn
  let source := word xs++tail
  let membership := mask xs++mtail
  let posSlots := positiveSlots
  let negSlots := negativeSlots
  let selected := resetSelected
  let H := heads out
  let T := data source membership out w C D xs.length
  let first := positive
  let second := negative
  have hiP : Function.Injective posSlots := by decide
  have hiN : Function.Injective negSlots := by decide
  have firstLocal := hloops.1.mask selected (by intro j hj; fin_cases j <;> first | rfl | contradiction) hD
  have positive := firstLocal.focus posSlots hiP (H 0 0) (T 0 0)
  have firstStep : Step first (2*C10NaturalHardwireScore.loopBudget xs w C+2)
      (H 0 0) (T 0 0) (H 0 0) (T (C10NaturalHardwireScore.selectedSum xs) 0) := by
    refine (positive.congr_in (dockH_existing posSlots _ _ (by intro j; fin_cases j <;> rfl))
      (install_existing posSlots _ _ (by intro j; fin_cases j <;> rfl))).congr ?_ ?_
    · exact dockH_existing posSlots _ _ (by intro j; fin_cases j <;> rfl)
    · apply HierarchyAllocation.install_eq posSlots hiP
      · intro j; fin_cases j <;> rfl
      · intro i hi; fin_cases i <;> first | rfl | exact False.elim (hi 14 rfl)
  have negative := hloops.2.focus negSlots hiN (H 0 0) (T (C10NaturalHardwireScore.selectedSum xs) 0)
  have secondStep : Step second (CloseoutRowsPoolMinimum.loopBudget xs w C)
      (H 0 0) (T (C10NaturalHardwireScore.selectedSum xs) 0)
      (H (CloseoutRowsPoolWeight.word xs).length xs.length) (T (C10NaturalHardwireScore.selectedSum xs) (CloseoutRowsPoolMinimum.liveSum xs)) := by
    refine (negative.congr_in (dockH_existing negSlots _ _ (by intro j; fin_cases j <;> rfl))
      (install_existing negSlots _ _ (by intro j; fin_cases j <;> rfl))).congr ?_ ?_
    · funext i
      by_cases hi : ∃ j, negSlots j=i
      · obtain ⟨j,rfl⟩ := hi
        rw [dockH_slot negSlots hiN]
        fin_cases j <;> rfl
      · rw [dockH_other negSlots _ _ i (by simpa using hi)]
        have h0 : i ≠ 0 := fun h => hi ⟨0,h.symm⟩
        have h39 : i ≠ 39 := fun h => hi ⟨13,h.symm⟩
        simp only [H,heads,if_neg h0,if_neg h39]
    · apply HierarchyAllocation.install_eq negSlots hiN
      · intro j; fin_cases j <;> rfl
      · intro i hi; fin_cases i <;> first | rfl | exact False.elim (hi 14 rfl)
  exact firstStep.seq secondStep

/-- The first 39 tapes are literally the existing target consumer's input. -/
theorem target_input (source membership out : List Bool) (w C D total p n : ℕ) (i : Fin 39) :
    data source membership out w C D total p n (i.castAdd 5) =
      C10NaturalHardwireTarget.input source out w C p n i := by
  simp only [data, Fin.addCases_left]

theorem target_heads (out : List Bool) (pos mpos : ℕ) (i : Fin 39) :
    heads out pos mpos (i.castAdd 5) = C10NaturalHardwireTarget.heads pos out i := by
  fin_cases i <;> rfl

open SupplierPipeline SupplierEstimator ThresholdCompiler

/-- Actual hardwired-child specialization. Its input contains the original
signed weights and target, and the exact frozen assignment mask. -/
theorem hardwire_scores {q : ℕ} (live : Finset (Fin q)) (g : ExactThresholdGate q)
    (y : BitInput live.card) (tail mtail out : List Bool) (w C D : ℕ)
    (hw : ∀ x ∈ C10NaturalHardwireScore.items live g y, natBitLength x.1.natAbs ≤ w)
    (hc : 8*w+12 ≤ C)
    (hp : C10NaturalHardwireScore.positiveSum (C10NaturalHardwireScore.items live g y) < 2^w)
    (hn : CloseoutRowsPoolMinimum.negSum (C10NaturalHardwireScore.items live g y) < 2^w)
    (hD : C10NaturalHardwireScore.loopBudget (C10NaturalHardwireScore.items live g y) w C ≤ D) :
    Step machine (budget (C10NaturalHardwireScore.items live g y) w C) (heads out 0 0)
      (data (exactWord g++tail) (List.ofFn (C10NaturalHardwireScore.frozenMask live y)++mtail)
        out w C D q 0 0)
      (heads out ((List.ofFn g.weight).flatMap intWord).length q)
      (data (exactWord g++tail) (List.ofFn (C10NaturalHardwireScore.frozenMask live y)++mtail)
        out w C D q (C10NaturalHardwireScore.selectedSum (C10NaturalHardwireScore.items live g y))
          (CloseoutRowsPoolMinimum.liveSum (C10NaturalHardwireScore.items live g y))) := by
  have actual := run (C10NaturalHardwireScore.items live g y) (intWord g.target++tail) mtail out w C D hw hc hp hn hD
  have hlen : (C10NaturalHardwireScore.items live g y).length = q := List.length_ofFn
  simpa only [C10NaturalHardwireScore.items_word, C10NaturalHardwireScore.items_mask,
    hlen, exactWord, List.append_assoc] using actual

end NearCubicWires.RepairSource.CloseoutFinal.C10NaturalHardwireScoreInputs
