import Proof.MachineModel.CanonicalConditionalTouchProgram
import Proof.Circuits.CanonicalRoundCall

/-!
# The greedy touching sweep on the counted round controller

`CanonicalConditionalTouchProgram` §9 records the one sequential obligation of
the symmetric counting path: `SupplierTouching.touchingSelect` walks
`List.finRange q` in order and each round's two conditional numerators depend on
the previous round's selection.  `CanonicalRoundCall` supplies the missing
state-threading harness; this module supplies the semantic bridge between the
harness's pure fold and the ledger's greedy recursion, and composes the two.

The carried state is `pair context (pair selectedMask stepCount)`: `context` is
the round callee's fixed data (the occurrence pool's support masks and the
coordinate count), copied unchanged through every round, while `selectedMask`
and `stepCount` are the sweep's two mutable fields.  With the counter descending
from `q` to `1`, the round at counter `c` processes the coordinate list
`(List.finRange q).drop (q - c)`, whose head is coordinate `q - c` and whose
tail is exactly the `rest` of `touchingSelectAux`.
-/

open Finset

namespace NearCubicWires.CanonicalTouchingSweepProgram

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalConditionalTouchProgram
open NearCubicWires.CanonicalRoundCall
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.SupplierTouching
open NearCubicWires.VerifiedLinker

/-! ## §1 The coordinate order, one suffix at a time -/

theorem finRange_drop_cons (q d : ℕ) (hd : d < q) :
    (List.finRange q).drop d =
      (⟨d, hd⟩ : Fin q) :: (List.finRange q).drop (d + 1) := by
  have hlength : d < (List.finRange q).length := by
    simpa using hd
  rw [List.drop_eq_getElem_cons hlength]
  congr 1
  simp

@[simp] theorem finRange_drop_self (q : ℕ) :
    (List.finRange q).drop q = [] := by
  simp

/-! ## §2 The sweep as a round-indexed fold -/

/-- One greedy round on the explicit remaining-coordinate list.  The empty list
and an exhausted step budget both leave the state untouched, exactly as
`touchingSelectAux` does. -/
def sweepRound {Gate : Type} [Fintype Gate] {q : ℕ}
    (support : Gate → Finset (Fin q)) :
    List (Fin q) → Finset (Fin q) × ℕ → Finset (Fin q) × ℕ
  | [], state => state
  | coordinate :: rest, state =>
      if state.2 = 0 then
        state
      else if
          conditionalTouchNumerator support (insert coordinate state.1)
                rest.toFinset (state.2 - 1) *
              Nat.choose rest.length state.2 ≤
            conditionalTouchNumerator support state.1 rest.toFinset state.2 *
              Nat.choose rest.length (state.2 - 1) then
        (insert coordinate state.1, state.2 - 1)
      else
        state

/-- The whole sweep, as the iteration of `sweepRound` over the suffixes. -/
def sweepFold {Gate : Type} [Fintype Gate] {q : ℕ}
    (support : Gate → Finset (Fin q)) :
    List (Fin q) → Finset (Fin q) × ℕ → Finset (Fin q) × ℕ
  | [], state => state
  | coordinate :: rest, state =>
      sweepFold support rest (sweepRound support (coordinate :: rest) state)

theorem sweepFold_cons {Gate : Type} [Fintype Gate] {q : ℕ}
    (support : Gate → Finset (Fin q)) (coordinate : Fin q)
    (rest : List (Fin q)) (state : Finset (Fin q) × ℕ) :
    sweepFold support (coordinate :: rest) state =
      sweepFold support rest (sweepRound support (coordinate :: rest) state) :=
  rfl

theorem touchingSelectAux_zero {Gate : Type} [Fintype Gate] {q : ℕ}
    (support : Gate → Finset (Fin q)) (selected : Finset (Fin q))
    (coordinates : List (Fin q)) :
    touchingSelectAux support selected 0 coordinates = selected := by
  cases coordinates with
  | nil => rfl
  | cons coordinate rest => simp [touchingSelectAux]

theorem sweepRound_snd_le {Gate : Type} [Fintype Gate] {q : ℕ}
    (support : Gate → Finset (Fin q)) (coordinates : List (Fin q))
    (state : Finset (Fin q) × ℕ) :
    (sweepRound support coordinates state).2 ≤ state.2 := by
  cases coordinates with
  | nil => exact Nat.le_refl _
  | cons coordinate rest =>
      by_cases hzero : state.2 = 0
      · simp only [sweepRound, if_pos hzero]
        exact Nat.le_refl _
      · by_cases hchoice :
            conditionalTouchNumerator support (insert coordinate state.1)
                  rest.toFinset (state.2 - 1) *
                Nat.choose rest.length state.2 ≤
              conditionalTouchNumerator support state.1 rest.toFinset state.2 *
                Nat.choose rest.length (state.2 - 1)
        · simp only [sweepRound, if_neg hzero, if_pos hchoice]
          omega
        · simp only [sweepRound, if_neg hzero, if_neg hchoice]
          exact Nat.le_refl _

/-- The greedy recursion's selected set is exactly the fold's first
component. -/
theorem sweepFold_fst {Gate : Type} [Fintype Gate] {q : ℕ}
    (support : Gate → Finset (Fin q)) :
    ∀ (coordinates : List (Fin q)) (selected : Finset (Fin q)) (stepCount : ℕ),
      (sweepFold support coordinates (selected, stepCount)).1 =
        touchingSelectAux support selected stepCount coordinates := by
  intro coordinates
  induction coordinates with
  | nil => intro selected stepCount; rfl
  | cons coordinate rest inductionHypothesis =>
      intro selected stepCount
      rw [sweepFold_cons]
      by_cases hzero : stepCount = 0
      · subst stepCount
        rw [show sweepRound support (coordinate :: rest) (selected, 0) =
            (selected, 0) by simp [sweepRound]]
        rw [inductionHypothesis selected 0]
        rw [touchingSelectAux_zero support selected rest,
          touchingSelectAux_zero support selected (coordinate :: rest)]
      · by_cases hchoice :
            conditionalTouchNumerator support (insert coordinate selected)
                  rest.toFinset (stepCount - 1) *
                Nat.choose rest.length stepCount ≤
              conditionalTouchNumerator support selected rest.toFinset
                  stepCount *
                Nat.choose rest.length (stepCount - 1)
        · rw [show sweepRound support (coordinate :: rest)
              (selected, stepCount) =
              (insert coordinate selected, stepCount - 1) by
            simp [sweepRound, hzero, hchoice]]
          rw [inductionHypothesis (insert coordinate selected) (stepCount - 1)]
          simp [touchingSelectAux, hzero, hchoice]
        · rw [show sweepRound support (coordinate :: rest)
              (selected, stepCount) = (selected, stepCount) by
            simp [sweepRound, hzero, hchoice]]
          rw [inductionHypothesis selected stepCount]
          simp [touchingSelectAux, hzero, hchoice]

/-! ## §3 The carried-state encoding -/

/-- Carried state ABI: `pair context (pair selectedMask stepCount)`. -/
def sweepCode (context selectedMask stepCount : ℕ) : ℕ :=
  Nat.pair context (Nat.pair selectedMask stepCount)

def sweepStateCode {q : ℕ} (context : ℕ) (state : Finset (Fin q) × ℕ) : ℕ :=
  sweepCode context (coordinateMask state.1) state.2

/-- Reachable carried states of the sweep: some coordinate set and some step
budget below the live count, at a counter that has not passed `q`. -/
def SweepReachable (q context bound carried counter : ℕ) : Prop :=
  counter ≤ q ∧
    ∃ (selected : Finset (Fin q)) (stepCount : ℕ), stepCount ≤ bound ∧
      carried = sweepStateCode context (selected, stepCount)

/-- **The round controller's fold is the greedy sweep.** -/
theorem roundFold_sweepFold {Gate : Type} [Fintype Gate] {q : ℕ}
    (support : Gate → Finset (Fin q)) (context : ℕ) (step : ℕ → ℕ → ℕ)
    (hstep : ∀ (selected : Finset (Fin q)) (stepCount counter : ℕ),
      counter + 1 ≤ q →
      step (sweepStateCode context (selected, stepCount)) (counter + 1) =
        sweepStateCode context
          (sweepRound support ((List.finRange q).drop (q - (counter + 1)))
            (selected, stepCount))) :
    ∀ (counter : ℕ), counter ≤ q → ∀ (state : Finset (Fin q) × ℕ),
      roundFold step (sweepStateCode context state) counter =
        sweepStateCode context
          (sweepFold support ((List.finRange q).drop (q - counter)) state) := by
  intro counter
  induction counter with
  | zero =>
      intro _hcounter state
      rw [roundFold_zero, Nat.sub_zero, finRange_drop_self]
      rfl
  | succ count inductionHypothesis =>
      intro hcounter state
      have hindex : q - (count + 1) < q := by omega
      have hshift : q - (count + 1) + 1 = q - count := by omega
      have hlist :
          (List.finRange q).drop (q - (count + 1)) =
            (⟨q - (count + 1), hindex⟩ : Fin q) ::
              (List.finRange q).drop (q - count) := by
        rw [finRange_drop_cons q (q - (count + 1)) hindex, hshift]
      rw [roundFold_succ]
      rw [show state = (state.1, state.2) from rfl]
      rw [hstep state.1 state.2 count hcounter]
      rw [inductionHypothesis (by omega)
        (sweepRound support ((List.finRange q).drop (q - (count + 1)))
          (state.1, state.2))]
      rw [hlist, sweepFold_cons, ← hlist]

/-! ## §4 The sweep, executed on the counted round controller -/

theorem run_touchingSweepProgram {Gate : Type} [Fintype Gate] {q : ℕ}
    (support : Gate → Finset (Fin q)) (roundProgram : NPOracleProgram)
    (inputLength context liveCount maximumBits : ℕ)
    (calleeFuel step : ℕ → ℕ → ℕ)
    (hpositive : 1 ≤ maximumBits)
    (hinputBits :
      natBitLength
          (roundCallInput q
            (sweepStateCode context ((∅ : Finset (Fin q)), liveCount))) ≤
        maximumBits)
    (hcarriedBits : ∀ carried counter,
      SweepReachable q context liveCount carried counter →
      natBitLength (Nat.pair carried counter) ≤ maximumBits)
    (hreturnBits : ∀ carried counter,
      SweepReachable q context liveCount carried (counter + 1) →
      natBitLength
          (Nat.pair (Nat.pair carried (counter + 1))
            (step carried (counter + 1))) ≤ maximumBits)
    (hstep : ∀ (selected : Finset (Fin q)) (stepCount counter : ℕ),
      counter + 1 ≤ q →
      step (sweepStateCode context (selected, stepCount)) (counter + 1) =
        sweepStateCode context
          (sweepRound support ((List.finRange q).drop (q - (counter + 1)))
            (selected, stepCount)))
    (hexec : ∀ carried counter,
      SweepReachable q context liveCount carried (counter + 1) →
      runNPOracleProgram roundProgram maximumBits
          (calleeFuel carried (counter + 1))
          (initialNPOracleState carried (Nat.pair carried (counter + 1))) =
        some (step carried (counter + 1))) :
    runNPOracleProgram (roundCallProgram roundProgram) maximumBits
        (roundCallFuel roundProgram calleeFuel step
          (sweepStateCode context ((∅ : Finset (Fin q)), liveCount)) q)
        (initialNPOracleState inputLength
          (roundCallInput q
            (sweepStateCode context ((∅ : Finset (Fin q)), liveCount)))) =
      some
        (sweepCode context
          (coordinateMask (touchingSelect support liveCount))
          (sweepFold support (List.finRange q)
            ((∅ : Finset (Fin q)), liveCount)).2) := by
  have hstart :
      SweepReachable q context liveCount
        (sweepStateCode context ((∅ : Finset (Fin q)), liveCount)) q :=
    ⟨Nat.le_refl q, ∅, liveCount, Nat.le_refl liveCount, rfl⟩
  have hadvance : ∀ carried counter,
      SweepReachable q context liveCount carried (counter + 1) →
      SweepReachable q context liveCount (step carried (counter + 1)) counter := by
    intro carried counter hreachable
    obtain ⟨hcounter, selected, stepCount, hstepCount, hcarried⟩ := hreachable
    refine ⟨by omega, ?_⟩
    refine
      ⟨(sweepRound support ((List.finRange q).drop (q - (counter + 1)))
          (selected, stepCount)).1,
        (sweepRound support ((List.finRange q).drop (q - (counter + 1)))
          (selected, stepCount)).2, ?_, ?_⟩
    · exact le_trans (sweepRound_snd_le support _ (selected, stepCount))
        hstepCount
    · rw [hcarried, hstep selected stepCount counter hcounter]
  have hrun :=
    run_roundCallProgram (callee := roundProgram) (maximumBits := maximumBits)
      inputLength q (sweepStateCode context ((∅ : Finset (Fin q)), liveCount))
      calleeFuel step (SweepReachable q context liveCount) hpositive hinputBits
      hstart hcarriedBits hreturnBits hadvance hexec
  rw [hrun]
  have hfold :=
    roundFold_sweepFold support context step hstep q (Nat.le_refl q)
      ((∅ : Finset (Fin q)), liveCount)
  rw [Nat.sub_self, List.drop_zero] at hfold
  rw [hfold]
  rw [show sweepStateCode context
        (sweepFold support (List.finRange q)
          ((∅ : Finset (Fin q)), liveCount)) =
      sweepCode context
        (coordinateMask
          (sweepFold support (List.finRange q)
            ((∅ : Finset (Fin q)), liveCount)).1)
        (sweepFold support (List.finRange q)
          ((∅ : Finset (Fin q)), liveCount)).2 from rfl]
  rw [sweepFold_fst support (List.finRange q) ∅ liveCount]
  rfl

/-! ## §5 The single remaining sweep obligation

Everything above is unconditional in the sweep's control flow: the counted
controller, its exact clock, and the identification of its fold with
`SupplierTouching.touchingSelectAux` are proved.  What an owning module must
still supply is one *round* program, i.e. a fixed oracle-free
`touchingSweepRoundProgram` together with

```text
theorem run_touchingSweepRoundProgram
    (occurrences : List (SupportedNormalizedGate q))
    (selected : Finset (Fin q)) (stepCount counter maximumBits : ℕ)
    (hcounter : counter + 1 ≤ q)
    (hbits : touchingSweepRoundBits … ≤ maximumBits) :
    runNPOracleProgram touchingSweepRoundProgram maximumBits
        (touchingSweepRoundFuel …)
        (initialNPOracleState
          (sweepStateCode (touchingSweepContext occurrences q) (selected, stepCount))
          (Nat.pair
            (sweepStateCode (touchingSweepContext occurrences q) (selected, stepCount))
            (counter + 1))) =
      some
        (sweepStateCode (touchingSweepContext occurrences q)
          (sweepRound (occurrenceSupport occurrences)
            ((List.finRange q).drop (q - (counter + 1))) (selected, stepCount)))
```

Its body is fixed by `sweepRound`'s definition and is assembled entirely from
compiled pieces:

* the coordinate of the round is `q - counter`, and the remaining-coordinate
  set is the interval `{i : q - counter < i}`, whose `coordinateMask` is
  `2 ^ q - 2 ^ (q - counter)` — one `binaryTwoPowProgram` difference;
* the two numerators are `run_conditionalTouchNumeratorProgram` at
  `(insert coordinate selected, rest, stepCount - 1)` and
  `(selected, rest, stepCount)`; their census request lists are the
  shared-context broadcast of `pair (pair selectedMask restMask)` over the
  pool's support-mask list, which the round-call ABI makes available because
  the carried state is installed in the callee's preserved context register;
* the branch test is `run_touchingStepProgram`;
* the mask update is `coordinateMask_insert` (`+ 2 ^ coordinate`) on the taken
  branch and the identity otherwise.

Composing that theorem with `run_touchingSweepProgram` above and with
`CanonicalConditionalTouchProgram.run_touchingCostProgram` gives
`CanonicalOccurrencePopulationProgram`'s §6 target
`run_symmetricOccurrenceTouchingCostProgram`. -/

end NearCubicWires.CanonicalTouchingSweepProgram
