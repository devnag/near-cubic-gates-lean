import Proof.Circuits.CanonicalBalancedCall
import Proof.MachineModel.CanonicalBalancedNatSumProgram
import Proof.MachineModel.CanonicalOccurrencePopulationProgram
import Proof.MachineModel.CanonicalTouchingStepProgram

/-!
# The conditional touch numerator, executed

`SupplierTouching.conditionalTouchNumerator` is the only quantity the greedy
touching sweep ever sums: one closed binomial score per retained occurrence.
`CanonicalTouchingStepProgram.run_gateTouchProgram` already executes a single
gate's score from the *numeric* triple `(meets, undecidedCard, residualCard)`.
This module supplies the missing half — turning coordinate sets into machine
data and folding the per-gate program across the whole occurrence pool.

Coordinate sets travel as bitmasks: `coordinateMask` is the little-endian
`Nat.ofBits` numeral of a `Finset (Fin q)`, so membership is one `testBit`
instruction.  A single counted loop over the `q` coordinate positions then
computes all three per-gate numbers at once, using only saturating arithmetic:

```text
undecidedCard += undecidedBit
residualCard  += undecidedBit - supportBit          -- AND NOT
meets         += selectedBit + supportBit - 1       -- AND
```

Saturating subtraction on single bits is exactly Boolean `AND NOT`, and
`x + y - 1` on single bits is exactly Boolean `AND`, so the loop never
branches on data.  Only `meets = 0` is ever observed, and that happens exactly
when the selected set and the gate's support are disjoint.

The pool-level score is then one canonical balanced call of the per-gate
program followed by the existing balanced natural-number sum.
-/

open Finset
open scoped BigOperators

namespace NearCubicWires.CanonicalConditionalTouchProgram

open NearCubicWires
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBalancedNatSumProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalOccurrencePopulationProgram
open NearCubicWires.CanonicalTouchingStepProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierTouching
open NearCubicWires.VerifiedLinker

private theorem bits_of_le {value bound maximumBits : ℕ}
    (hvalue : value ≤ bound) (hbits : natBitLength bound ≤ maximumBits) :
    natBitLength value ≤ maximumBits :=
  (natBitLength_mono hvalue).trans hbits

/-! ## §1 Coordinate sets as bitmasks -/

/-- Little-endian membership numeral of a coordinate set. -/
def coordinateMask {q : ℕ} (values : Finset (Fin q)) : ℕ :=
  Nat.ofBits fun index : Fin q => decide (index ∈ values)

theorem testBit_coordinateMask {q : ℕ} (values : Finset (Fin q))
    (index : Fin q) :
    (coordinateMask values).testBit index.val = decide (index ∈ values) := by
  unfold coordinateMask
  rw [Nat.testBit_ofBits_lt _ _ index.isLt]

theorem coordinateMask_lt {q : ℕ} (values : Finset (Fin q)) :
    coordinateMask values < 2 ^ q :=
  Nat.ofBits_lt_two_pow _

/-- One bit of a mask, as the machine's `testBit` instruction returns it. -/
def maskBit (mask index : ℕ) : ℕ :=
  (mask.testBit index).toNat

theorem maskBit_le_one (mask index : ℕ) : maskBit mask index ≤ 1 := by
  unfold maskBit
  cases mask.testBit index <;> simp

theorem maskBit_coordinateMask {q : ℕ} (values : Finset (Fin q))
    (index : Fin q) :
    maskBit (coordinateMask values) index.val =
      if index ∈ values then 1 else 0 := by
  unfold maskBit
  rw [testBit_coordinateMask]
  by_cases hmember : index ∈ values <;> simp [hmember]

/-! ## §2 The three coordinate censuses -/

/-- Number of coordinate positions below `count` lying in both masks. -/
def meetsCensus (selectedMask supportMask : ℕ) : ℕ → ℕ
  | 0 => 0
  | count + 1 =>
      meetsCensus selectedMask supportMask count +
        (maskBit selectedMask count + maskBit supportMask count - 1)

/-- Number of coordinate positions below `count` lying in the mask. -/
def undecidedCensus (undecidedMask : ℕ) : ℕ → ℕ
  | 0 => 0
  | count + 1 =>
      undecidedCensus undecidedMask count + maskBit undecidedMask count

/-- Number of coordinate positions below `count` in the first mask and outside
the second. -/
def residualCensus (undecidedMask supportMask : ℕ) : ℕ → ℕ
  | 0 => 0
  | count + 1 =>
      residualCensus undecidedMask supportMask count +
        (maskBit undecidedMask count - maskBit supportMask count)

theorem meetsCensus_succ (selectedMask supportMask count : ℕ) :
    meetsCensus selectedMask supportMask (count + 1) =
      meetsCensus selectedMask supportMask count +
        (maskBit selectedMask count + maskBit supportMask count - 1) :=
  rfl

theorem undecidedCensus_succ (undecidedMask count : ℕ) :
    undecidedCensus undecidedMask (count + 1) =
      undecidedCensus undecidedMask count + maskBit undecidedMask count :=
  rfl

theorem residualCensus_succ (undecidedMask supportMask count : ℕ) :
    residualCensus undecidedMask supportMask (count + 1) =
      residualCensus undecidedMask supportMask count +
        (maskBit undecidedMask count - maskBit supportMask count) :=
  rfl

theorem meetsCensus_sum (selectedMask supportMask count : ℕ) :
    meetsCensus selectedMask supportMask count =
      ∑ index ∈ Finset.range count,
        (maskBit selectedMask index + maskBit supportMask index - 1) := by
  induction count with
  | zero => simp [meetsCensus]
  | succ count inductionHypothesis =>
      rw [meetsCensus, inductionHypothesis, Finset.sum_range_succ]

theorem undecidedCensus_sum (undecidedMask count : ℕ) :
    undecidedCensus undecidedMask count =
      ∑ index ∈ Finset.range count, maskBit undecidedMask index := by
  induction count with
  | zero => simp [undecidedCensus]
  | succ count inductionHypothesis =>
      rw [undecidedCensus, inductionHypothesis, Finset.sum_range_succ]

theorem residualCensus_sum (undecidedMask supportMask count : ℕ) :
    residualCensus undecidedMask supportMask count =
      ∑ index ∈ Finset.range count,
        (maskBit undecidedMask index - maskBit supportMask index) := by
  induction count with
  | zero => simp [residualCensus]
  | succ count inductionHypothesis =>
      rw [residualCensus, inductionHypothesis, Finset.sum_range_succ]

theorem meetsCensus_le (selectedMask supportMask : ℕ) {count bound : ℕ}
    (hcount : count ≤ bound) :
    meetsCensus selectedMask supportMask count ≤
      meetsCensus selectedMask supportMask bound := by
  rw [meetsCensus_sum, meetsCensus_sum]
  exact Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr hcount)

theorem undecidedCensus_le (undecidedMask : ℕ) {count bound : ℕ}
    (hcount : count ≤ bound) :
    undecidedCensus undecidedMask count ≤
      undecidedCensus undecidedMask bound := by
  rw [undecidedCensus_sum, undecidedCensus_sum]
  exact Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr hcount)

theorem residualCensus_le (undecidedMask supportMask : ℕ) {count bound : ℕ}
    (hcount : count ≤ bound) :
    residualCensus undecidedMask supportMask count ≤
      residualCensus undecidedMask supportMask bound := by
  rw [residualCensus_sum, residualCensus_sum]
  exact Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr hcount)

/-! ## §3 The censuses are the ledger's set quantities -/

private theorem sum_range_eq_sum_fin (q : ℕ) (values : ℕ → ℕ) :
    (∑ index ∈ Finset.range q, values index) =
      ∑ index : Fin q, values index.val :=
  (Fin.sum_univ_eq_sum_range values q).symm

private theorem sum_mem_indicator {q : ℕ} (values : Finset (Fin q)) :
    (∑ _index : Fin q, if _index ∈ values then 1 else 0) = values.card := by
  simp

theorem undecidedCensus_coordinateMask {q : ℕ} (values : Finset (Fin q)) :
    undecidedCensus (coordinateMask values) q = values.card := by
  rw [undecidedCensus_sum, sum_range_eq_sum_fin]
  have hpointwise : ∀ index : Fin q,
      maskBit (coordinateMask values) index.val =
        if index ∈ values then 1 else 0 :=
    fun index => maskBit_coordinateMask values index
  rw [Finset.sum_congr rfl fun index _ => hpointwise index]
  exact sum_mem_indicator values

theorem residualCensus_coordinateMask {q : ℕ}
    (undecided support : Finset (Fin q)) :
    residualCensus (coordinateMask undecided) (coordinateMask support) q =
      (undecided \ support).card := by
  rw [residualCensus_sum, sum_range_eq_sum_fin]
  have hpointwise : ∀ index : Fin q,
      maskBit (coordinateMask undecided) index.val -
          maskBit (coordinateMask support) index.val =
        if index ∈ undecided \ support then 1 else 0 := by
    intro index
    rw [maskBit_coordinateMask, maskBit_coordinateMask]
    by_cases hundecided : index ∈ undecided <;>
      by_cases hsupport : index ∈ support <;>
        simp [Finset.mem_sdiff, hundecided, hsupport]
  rw [Finset.sum_congr rfl fun index _ => hpointwise index]
  exact sum_mem_indicator (undecided \ support)

theorem meetsCensus_coordinateMask {q : ℕ}
    (selected support : Finset (Fin q)) :
    meetsCensus (coordinateMask selected) (coordinateMask support) q =
      (selected ∩ support).card := by
  rw [meetsCensus_sum, sum_range_eq_sum_fin]
  have hpointwise : ∀ index : Fin q,
      maskBit (coordinateMask selected) index.val +
          maskBit (coordinateMask support) index.val - 1 =
        if index ∈ selected ∩ support then 1 else 0 := by
    intro index
    rw [maskBit_coordinateMask, maskBit_coordinateMask]
    by_cases hselected : index ∈ selected <;>
      by_cases hsupport : index ∈ support <;>
        simp [Finset.mem_inter, hselected, hsupport]
  rw [Finset.sum_congr rfl fun index _ => hpointwise index]
  exact sum_mem_indicator (selected ∩ support)

theorem meetsCensus_eq_zero_iff {q : ℕ}
    (selected support : Finset (Fin q)) :
    meetsCensus (coordinateMask selected) (coordinateMask support) q = 0 ↔
      touchIndicator selected support = 0 := by
  rw [meetsCensus_coordinateMask]
  unfold touchIndicator
  constructor
  · intro hcard
    have hdisjoint : Disjoint selected support :=
      Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp hcard)
    simp [hdisjoint]
  · intro hindicator
    by_cases hdisjoint : Disjoint selected support
    · rw [Finset.disjoint_iff_inter_eq_empty.mp hdisjoint]
      simp
    · simp [hdisjoint] at hindicator

private theorem gateTouchValue_congr_meets
    {meets otherMeets undecidedCard residualCard stepCount : ℕ}
    (hmeets : meets = 0 ↔ otherMeets = 0) :
    gateTouchValue meets undecidedCard residualCard stepCount =
      gateTouchValue otherMeets undecidedCard residualCard stepCount := by
  unfold gateTouchValue
  by_cases hzero : meets = 0
  · rw [if_pos hzero, if_pos (hmeets.mp hzero)]
  · rw [if_neg hzero, if_neg fun hother => hzero (hmeets.mpr hother)]

/-- **The census triple is exactly the ledger's per-gate score.** -/
theorem gateTouchValue_census {q : ℕ}
    (selected undecided support : Finset (Fin q)) (stepCount : ℕ) :
    gateTouchValue
        (meetsCensus (coordinateMask selected) (coordinateMask support) q)
        (undecidedCensus (coordinateMask undecided) q)
        (residualCensus (coordinateMask undecided) (coordinateMask support) q)
        stepCount =
      conditionalGateTouchCount selected undecided support stepCount := by
  rw [undecidedCensus_coordinateMask, residualCensus_coordinateMask]
  rw [gateTouchValue_congr_meets (meetsCensus_eq_zero_iff selected support)]
  exact gateTouchValue_eq_conditionalGateTouchCount selected undecided support
    stepCount

/-! ## §4 The fixed census program

Register ABI:

* `r0`: the census request, then the `gateTouchProgram` request it builds;
* `r1`: native input length, never written;
* `r2`, `r3`, `r4`: the selected, undecided, and support masks;
* `r5`: the descending coordinate counter;
* `r6`, `r7`, `r8`: the meets, undecided, and residual accumulators;
* `r9`: the step count, carried through untouched;
* `r10`, `r11`, `r12`: the three extracted coordinate bits;
* `r13`: arithmetic scratch and output plumbing.
-/

/-- Public census ABI:
`pair (pair selected undecided) (pair support (pair width step))`. -/
def censusInput
    (selectedMask undecidedMask supportMask width stepCount : ℕ) : ℕ :=
  Nat.pair (Nat.pair selectedMask undecidedMask)
    (Nat.pair supportMask (Nat.pair width stepCount))

/-- **The coordinate census program.**  One counted loop of `testBit` reads
turns three bitmasks into the numeric triple `gateTouchProgram` consumes. -/
def censusProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .unpairRight 5 9 5
  , .unpairLeft 5 5 6
  , .unpairRight 2 3 7
  , .unpairLeft 2 2 8
  , .set 6 0 9
  , .set 7 0 10
  , .set 8 0 11
  , .branchZero 5 22 12
  , .decrement 5 13
  , .testBit 3 5 10 14
  , .testBit 4 5 11 15
  , .testBit 2 5 12 16
  , .add 7 10 7 17
  , .subtract 10 11 13 18
  , .add 8 13 8 19
  , .add 12 11 13 20
  , .decrement 13 21
  , .add 6 13 6 11
  , .pair 7 8 13 23
  , .pair 13 9 13 24
  , .pair 6 13 0 25
  , .halt 0
  ]

@[simp] theorem censusProgram_oracleFree : OracleFree censusProgram := by
  rfl

def censusFuel (width : ℕ) : ℕ := width * 11 + 16

/-- The census program's output is exactly a `gateTouchProgram` request. -/
def censusHandoff
    (selectedMask undecidedMask supportMask width stepCount : ℕ) : ℕ :=
  gateTouchInput (meetsCensus selectedMask supportMask width)
    (undecidedCensus undecidedMask width)
    (residualCensus undecidedMask supportMask width) stepCount

def censusBits
    (selectedMask undecidedMask supportMask width stepCount : ℕ) : ℕ :=
  max (natBitLength 2) <|
    max
      (natBitLength
        (censusInput selectedMask undecidedMask supportMask width stepCount))
      (natBitLength
        (censusHandoff selectedMask undecidedMask supportMask width stepCount))

private theorem run_censusLoop
    (selectedMask undecidedMask supportMask stepCount maximumBits extra : ℕ)
    (htwo : natBitLength 2 ≤ maximumBits) :
    ∀ (remaining meets undecided residual : ℕ)
      (state : NPOracleState) (result : Option ℕ),
      state.pc = 11 →
      state.registers 2 = selectedMask →
      state.registers 3 = undecidedMask →
      state.registers 4 = supportMask →
      state.registers 5 = remaining →
      state.registers 6 = meets →
      state.registers 7 = undecided →
      state.registers 8 = residual →
      state.registers 9 = stepCount →
      natBitLength remaining ≤ maximumBits →
      natBitLength
          (meets + meetsCensus selectedMask supportMask remaining) ≤
        maximumBits →
      natBitLength (undecided + undecidedCensus undecidedMask remaining) ≤
        maximumBits →
      natBitLength
          (residual + residualCensus undecidedMask supportMask remaining) ≤
        maximumBits →
      (∀ finalState : NPOracleState,
        finalState.pc = 22 →
        finalState.registers 6 =
          meets + meetsCensus selectedMask supportMask remaining →
        finalState.registers 7 =
          undecided + undecidedCensus undecidedMask remaining →
        finalState.registers 8 =
          residual + residualCensus undecidedMask supportMask remaining →
        finalState.registers 9 = stepCount →
        runNPOracleProgram censusProgram maximumBits extra finalState =
          result) →
      runNPOracleProgram censusProgram maximumBits
          (remaining * 11 + 1 + extra) state = result := by
  intro remaining
  induction remaining with
  | zero =>
      intro meets undecided residual state result hpc _ _ _ hcounter
        hmeetsRegister hundecidedRegister hresidualRegister hstepRegister
        _ _ _ _ hfinish
      rw [show 0 * 11 + 1 + extra = extra + 1 by omega]
      rw [run_branchZero_instruction (by rfl) hpc]
      rw [hcounter, if_pos rfl]
      refine hfinish (state.jump 22) rfl ?_ ?_ ?_ ?_
      · simpa [NPOracleState.jump, meetsCensus] using hmeetsRegister
      · simpa [NPOracleState.jump, undecidedCensus] using hundecidedRegister
      · simpa [NPOracleState.jump, residualCensus] using hresidualRegister
      · simpa [NPOracleState.jump] using hstepRegister
  | succ remaining inductionHypothesis =>
      intro meets undecided residual state result hpc hselectedRegister
        hundecidedMaskRegister hsupportRegister hcounter hmeetsRegister
        hundecidedRegister hresidualRegister hstepRegister hcounterBits
        hmeetsBits hundecidedBits hresidualBits hfinish
      have hcounterPredBits : natBitLength remaining ≤ maximumBits :=
        bits_of_le (Nat.le_succ remaining) hcounterBits
      have hsmall : ∀ value : ℕ, value ≤ 2 → natBitLength value ≤ maximumBits :=
        fun value hvalue => bits_of_le hvalue htwo
      have hundecidedBit : maskBit undecidedMask remaining ≤ 1 :=
        maskBit_le_one _ _
      have hsupportBit : maskBit supportMask remaining ≤ 1 :=
        maskBit_le_one _ _
      have hselectedBit : maskBit selectedMask remaining ≤ 1 :=
        maskBit_le_one _ _
      have hundecidedStepBits :
          natBitLength (undecided + maskBit undecidedMask remaining) ≤
            maximumBits := by
        refine bits_of_le ?_ hundecidedBits
        rw [undecidedCensus_succ]
        omega
      have hresidualStepBits :
          natBitLength
              (residual +
                (maskBit undecidedMask remaining -
                  maskBit supportMask remaining)) ≤
            maximumBits := by
        refine bits_of_le ?_ hresidualBits
        rw [residualCensus_succ]
        omega
      have hmeetsStepBits :
          natBitLength
              (meets +
                (maskBit selectedMask remaining +
                  maskBit supportMask remaining - 1)) ≤
            maximumBits := by
        refine bits_of_le ?_ hmeetsBits
        rw [meetsCensus_succ]
        omega
      rw [show (remaining + 1) * 11 + 1 + extra =
          remaining * 11 + 1 + extra + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 +
            1 by
        ring]
      rw [run_branchZero_instruction (by rfl) hpc]
      rw [hcounter, if_neg (by omega)]
      rw [run_decrement_instruction (value := remaining) (by rfl) rfl
        (by simp [NPOracleState.jump, hcounter]) hcounterPredBits]
      rw [run_testBit_instruction
        (value := maskBit undecidedMask remaining) (by rfl) rfl
        (by
          simp [NPOracleState.write, NPOracleState.jump,
            hundecidedMaskRegister, maskBit])
        (hsmall _ (by omega))]
      rw [run_testBit_instruction
        (value := maskBit supportMask remaining) (by rfl) rfl
        (by
          simp [NPOracleState.write, NPOracleState.jump, hsupportRegister,
            maskBit])
        (hsmall _ (by omega))]
      rw [run_testBit_instruction
        (value := maskBit selectedMask remaining) (by rfl) rfl
        (by
          simp [NPOracleState.write, NPOracleState.jump, hselectedRegister,
            maskBit])
        (hsmall _ (by omega))]
      rw [run_add_instruction
        (value := undecided + maskBit undecidedMask remaining) (by rfl) rfl
        (by
          simp [NPOracleState.write, NPOracleState.jump, hundecidedRegister])
        hundecidedStepBits]
      rw [run_subtract_instruction
        (value :=
          maskBit undecidedMask remaining - maskBit supportMask remaining)
        (by rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump])
        (hsmall _ (by omega))]
      rw [run_add_instruction
        (value :=
          residual +
            (maskBit undecidedMask remaining - maskBit supportMask remaining))
        (by rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump, hresidualRegister])
        hresidualStepBits]
      rw [run_add_instruction
        (value :=
          maskBit selectedMask remaining + maskBit supportMask remaining)
        (by rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump])
        (hsmall _ (by omega))]
      rw [run_decrement_instruction
        (value :=
          maskBit selectedMask remaining + maskBit supportMask remaining - 1)
        (by rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump])
        (hsmall _ (by omega))]
      rw [run_add_instruction
        (value :=
          meets +
            (maskBit selectedMask remaining + maskBit supportMask remaining -
              1))
        (by rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump, hmeetsRegister])
        hmeetsStepBits]
      refine inductionHypothesis
        (meets +
          (maskBit selectedMask remaining + maskBit supportMask remaining - 1))
        (undecided + maskBit undecidedMask remaining)
        (residual +
          (maskBit undecidedMask remaining - maskBit supportMask remaining))
        _ result rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hcounterPredBits ?_ ?_ ?_ ?_
      · simp [NPOracleState.write, NPOracleState.jump, hselectedRegister]
      · simp [NPOracleState.write, NPOracleState.jump, hundecidedMaskRegister]
      · simp [NPOracleState.write, NPOracleState.jump, hsupportRegister]
      · simp [NPOracleState.write, NPOracleState.jump]
      · simp [NPOracleState.write, NPOracleState.jump]
      · simp [NPOracleState.write, NPOracleState.jump]
      · simp [NPOracleState.write, NPOracleState.jump]
      · simp [NPOracleState.write, NPOracleState.jump, hstepRegister]
      · refine bits_of_le ?_ hmeetsBits
        rw [meetsCensus_succ]
        omega
      · refine bits_of_le ?_ hundecidedBits
        rw [undecidedCensus_succ]
        omega
      · refine bits_of_le ?_ hresidualBits
        rw [residualCensus_succ]
        omega
      · intro finalState hfinalPc hfinalMeets hfinalUndecided hfinalResidual
          hfinalStep
        refine hfinish finalState hfinalPc ?_ ?_ ?_ hfinalStep
        · rw [hfinalMeets, meetsCensus_succ]
          omega
        · rw [hfinalUndecided, undecidedCensus_succ]
          omega
        · rw [hfinalResidual, residualCensus_succ]
          omega

set_option maxHeartbeats 1200000 in
-- The eight-step decode, the counted census loop, and the three output pairings
-- are discharged in one chain so intermediate machine states stay implicit.
/-- **The coordinate census, executed.**  One fixed oracle-free program turns
three coordinate bitmasks and a width into the exact `gateTouchProgram`
request. -/
theorem run_censusProgram
    (inputLength selectedMask undecidedMask supportMask width stepCount
      maximumBits : ℕ)
    (hbits :
      censusBits selectedMask undecidedMask supportMask width stepCount ≤
        maximumBits) :
    runNPOracleProgram censusProgram maximumBits (censusFuel width)
        (initialNPOracleState inputLength
          (censusInput selectedMask undecidedMask supportMask width
            stepCount)) =
      some
        (censusHandoff selectedMask undecidedMask supportMask width
          stepCount) := by
  have htwo : natBitLength 2 ≤ maximumBits :=
    (Nat.le_max_left _ _).trans hbits
  have hinputBits :
      natBitLength
          (censusInput selectedMask undecidedMask supportMask width
            stepCount) ≤
        maximumBits := by
    refine le_trans ?_ hbits
    exact (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have houtputBits :
      natBitLength
          (censusHandoff selectedMask undecidedMask supportMask width
            stepCount) ≤
        maximumBits := by
    refine le_trans ?_ hbits
    exact (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hleftBits :
      natBitLength (Nat.pair selectedMask undecidedMask) ≤ maximumBits :=
    bits_of_le (Nat.left_le_pair _ _) hinputBits
  have hrightBits :
      natBitLength (Nat.pair supportMask (Nat.pair width stepCount)) ≤
        maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) hinputBits
  have hselectedBits : natBitLength selectedMask ≤ maximumBits :=
    bits_of_le (Nat.left_le_pair _ _) hleftBits
  have hundecidedBits : natBitLength undecidedMask ≤ maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) hleftBits
  have hsupportBits : natBitLength supportMask ≤ maximumBits :=
    bits_of_le (Nat.left_le_pair _ _) hrightBits
  have hwidthPairBits :
      natBitLength (Nat.pair width stepCount) ≤ maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) hrightBits
  have hwidthBits : natBitLength width ≤ maximumBits :=
    bits_of_le (Nat.left_le_pair _ _) hwidthPairBits
  have hstepBits : natBitLength stepCount ≤ maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) hwidthPairBits
  have hzeroBits : natBitLength 0 ≤ maximumBits :=
    bits_of_le (Nat.zero_le 2) htwo
  have hmeetsBits :
      natBitLength (meetsCensus selectedMask supportMask width) ≤
        maximumBits :=
    bits_of_le (Nat.left_le_pair _ _) houtputBits
  have htailBits :
      natBitLength
          (Nat.pair
            (Nat.pair (undecidedCensus undecidedMask width)
              (residualCensus undecidedMask supportMask width))
            stepCount) ≤
        maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) houtputBits
  have hcardsBits :
      natBitLength
          (Nat.pair (undecidedCensus undecidedMask width)
            (residualCensus undecidedMask supportMask width)) ≤
        maximumBits :=
    bits_of_le (Nat.left_le_pair _ _) htailBits
  have hundecidedCardBits :
      natBitLength (undecidedCensus undecidedMask width) ≤ maximumBits :=
    bits_of_le (Nat.left_le_pair _ _) hcardsBits
  have hresidualCardBits :
      natBitLength (residualCensus undecidedMask supportMask width) ≤
        maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) hcardsBits
  rw [show censusFuel width =
      width * 11 + 1 + 4 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 by
    unfold censusFuel
    omega]
  rw [run_unpairLeft_instruction
    (value := Nat.pair selectedMask undecidedMask) (by rfl) rfl
    (by simp [initialNPOracleState, censusInput]) hleftBits]
  rw [run_unpairRight_instruction
    (value := Nat.pair supportMask (Nat.pair width stepCount)) (by rfl) rfl
    (by
      simp [initialNPOracleState, censusInput, NPOracleState.write,
        NPOracleState.jump])
    hrightBits]
  rw [run_unpairLeft_instruction (value := supportMask) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hsupportBits]
  rw [run_unpairRight_instruction (value := Nat.pair width stepCount)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hwidthPairBits]
  rw [run_unpairRight_instruction (value := stepCount) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hstepBits]
  rw [run_unpairLeft_instruction (value := width) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hwidthBits]
  rw [run_unpairRight_instruction (value := undecidedMask) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hundecidedBits]
  rw [run_unpairLeft_instruction (value := selectedMask) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hselectedBits]
  rw [run_set_instruction (value := 0) (by rfl) rfl hzeroBits]
  rw [run_set_instruction (value := 0) (by rfl) rfl hzeroBits]
  rw [run_set_instruction (value := 0) (by rfl) rfl hzeroBits]
  refine run_censusLoop selectedMask undecidedMask supportMask stepCount
    maximumBits 4 htwo width 0 0 0 _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hwidthBits
    ?_ ?_ ?_ ?_
  · rfl
  · simp [NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump]
  · simpa using hmeetsBits
  · simpa using hundecidedCardBits
  · simpa using hresidualCardBits
  · intro finalState hfinalPc hfinalMeets hfinalUndecided hfinalResidual
      hfinalStep
    rw [show (4 : ℕ) = 0 + 1 + 1 + 1 + 1 by omega]
    rw [run_pair_instruction
      (value :=
        Nat.pair (undecidedCensus undecidedMask width)
          (residualCensus undecidedMask supportMask width))
      (by rfl) hfinalPc
      (by rw [hfinalUndecided, hfinalResidual]; simp) hcardsBits]
    rw [run_pair_instruction
      (value :=
        Nat.pair
          (Nat.pair (undecidedCensus undecidedMask width)
            (residualCensus undecidedMask supportMask width))
          stepCount)
      (by rfl) rfl
      (by
        simp only [NPOracleState.write, NPOracleState.jump]
        simp [hfinalStep])
      htailBits]
    rw [run_pair_instruction
      (value :=
        censusHandoff selectedMask undecidedMask supportMask width stepCount)
      (by rfl) rfl
      (by
        simp only [NPOracleState.write, NPOracleState.jump]
        simp [hfinalMeets, censusHandoff, gateTouchInput])
      houtputBits]
    exact run_halt_instruction (fuel := 0)
      (value :=
        censusHandoff selectedMask undecidedMask supportMask width stepCount)
      (by rfl) rfl (by simp [NPOracleState.write, NPOracleState.jump])
      houtputBits

/-! ## §5 One occurrence's conditional touch count -/

def censusSelectedField (code : ℕ) : ℕ :=
  (Nat.unpair (Nat.unpair code).1).1

def censusUndecidedField (code : ℕ) : ℕ :=
  (Nat.unpair (Nat.unpair code).1).2

def censusSupportField (code : ℕ) : ℕ :=
  (Nat.unpair (Nat.unpair code).2).1

def censusWidthField (code : ℕ) : ℕ :=
  (Nat.unpair (Nat.unpair (Nat.unpair code).2).2).1

def censusStepField (code : ℕ) : ℕ :=
  (Nat.unpair (Nat.unpair (Nat.unpair code).2).2).2

@[simp] theorem censusSelectedField_censusInput
    (selectedMask undecidedMask supportMask width stepCount : ℕ) :
    censusSelectedField
        (censusInput selectedMask undecidedMask supportMask width stepCount) =
      selectedMask := by
  simp [censusSelectedField, censusInput]

@[simp] theorem censusUndecidedField_censusInput
    (selectedMask undecidedMask supportMask width stepCount : ℕ) :
    censusUndecidedField
        (censusInput selectedMask undecidedMask supportMask width stepCount) =
      undecidedMask := by
  simp [censusUndecidedField, censusInput]

@[simp] theorem censusSupportField_censusInput
    (selectedMask undecidedMask supportMask width stepCount : ℕ) :
    censusSupportField
        (censusInput selectedMask undecidedMask supportMask width stepCount) =
      supportMask := by
  simp [censusSupportField, censusInput]

@[simp] theorem censusWidthField_censusInput
    (selectedMask undecidedMask supportMask width stepCount : ℕ) :
    censusWidthField
        (censusInput selectedMask undecidedMask supportMask width stepCount) =
      width := by
  simp [censusWidthField, censusInput]

@[simp] theorem censusStepField_censusInput
    (selectedMask undecidedMask supportMask width stepCount : ℕ) :
    censusStepField
        (censusInput selectedMask undecidedMask supportMask width stepCount) =
      stepCount := by
  simp [censusStepField, censusInput]

/-- The pairing bijection makes every natural a legal census request. -/
theorem censusInput_fields (code : ℕ) :
    censusInput (censusSelectedField code) (censusUndecidedField code)
        (censusSupportField code) (censusWidthField code)
        (censusStepField code) =
      code := by
  unfold censusInput censusSelectedField censusUndecidedField
    censusSupportField censusWidthField censusStepField
  rw [Nat.pair_unpair, Nat.pair_unpair, Nat.pair_unpair, Nat.pair_unpair]

/-- The per-occurrence score, as a pure function of the request code. -/
def gateCensusOutput (code : ℕ) : ℕ :=
  gateTouchValue
    (meetsCensus (censusSelectedField code) (censusSupportField code)
      (censusWidthField code))
    (undecidedCensus (censusUndecidedField code) (censusWidthField code))
    (residualCensus (censusUndecidedField code) (censusSupportField code)
      (censusWidthField code))
    (censusStepField code)

/-- **The per-occurrence conditional touch count program.**  Repair the
balanced-call atom, take the coordinate census, and run the existing per-gate
binomial stage. -/
def gateCensusProgram : NPOracleProgram :=
  linkPrograms repairAtomProgram (linkPrograms censusProgram gateTouchProgram)

theorem gateCensusProgram_oracleFree : OracleFree gateCensusProgram :=
  oracleFree_linkPrograms repairAtomProgram_oracleFree
    (oracleFree_linkPrograms censusProgram_oracleFree gateTouchProgram_oracleFree)

def gateCensusFuel (code : ℕ) : ℕ :=
  linkFuel (linkPrograms censusProgram gateTouchProgram) 2
    (linkFuel gateTouchProgram (censusFuel (censusWidthField code))
      (gateTouchFuel
        (undecidedCensus (censusUndecidedField code) (censusWidthField code))
        (residualCensus (censusUndecidedField code) (censusSupportField code)
          (censusWidthField code))
        (censusStepField code)))

def gateCensusBits (code : ℕ) : ℕ :=
  max 1 <| max (natBitLength code) <|
    max
      (censusBits (censusSelectedField code) (censusUndecidedField code)
        (censusSupportField code) (censusWidthField code)
        (censusStepField code))
      (gateTouchBits (Nat.unpair code).1
        (meetsCensus (censusSelectedField code) (censusSupportField code)
          (censusWidthField code))
        (undecidedCensus (censusUndecidedField code) (censusWidthField code))
        (residualCensus (censusUndecidedField code) (censusSupportField code)
          (censusWidthField code))
        (censusStepField code))

set_option maxHeartbeats 800000 in
-- Three linked stages widened to one shared register bound; only the closed
-- `…Bits` names appear in the premises.

theorem run_gateCensusProgram (code maximumBits : ℕ)
    (hbits : gateCensusBits code ≤ maximumBits) :
    runNPOracleProgram gateCensusProgram maximumBits (gateCensusFuel code)
        (initialNPOracleState (Nat.unpair code).1 (Nat.unpair code).2) =
      some (gateCensusOutput code) := by
  have hpositive : 1 ≤ maximumBits := (Nat.le_max_left _ _).trans hbits
  have hcodeBits : natBitLength code ≤ maximumBits :=
    (Nat.le_max_left _ _).trans ((Nat.le_max_right _ _).trans hbits)
  have hcensusBits :
      censusBits (censusSelectedField code) (censusUndecidedField code)
          (censusSupportField code) (censusWidthField code)
          (censusStepField code) ≤
        maximumBits :=
    (Nat.le_max_left _ _).trans
      ((Nat.le_max_right _ _).trans ((Nat.le_max_right _ _).trans hbits))
  have hgateBits :
      gateTouchBits (Nat.unpair code).1
          (meetsCensus (censusSelectedField code) (censusSupportField code)
            (censusWidthField code))
          (undecidedCensus (censusUndecidedField code) (censusWidthField code))
          (residualCensus (censusUndecidedField code) (censusSupportField code)
            (censusWidthField code))
          (censusStepField code) ≤
        maximumBits :=
    (Nat.le_max_right _ _).trans
      ((Nat.le_max_right _ _).trans ((Nat.le_max_right _ _).trans hbits))
  have hlength : natBitLength (Nat.unpair code).1 ≤ maximumBits :=
    bits_of_le (Nat.unpair_left_le _) hcodeBits
  have hpair :
      Nat.pair (Nat.unpair code).1 (Nat.unpair code).2 = code :=
    Nat.pair_unpair _
  have hstageOne :
      runNPOracleProgram repairAtomProgram maximumBits 2
          (initialNPOracleState (Nat.unpair code).1 (Nat.unpair code).2) =
        some code := by
    have hatomBits :
        repairAtomBits (Nat.unpair code).1 (Nat.unpair code).2 ≤
          maximumBits := by
      unfold repairAtomBits
      rw [hpair]
      exact hcodeBits
    have hrun :=
      run_repairAtomProgram (Nat.unpair code).1 (Nat.unpair code).2
    rw [hpair] at hrun
    exact run_bits_mono hrun hatomBits
  have hstageTwo :
      runNPOracleProgram censusProgram maximumBits
          (censusFuel (censusWidthField code))
          (initialNPOracleState (Nat.unpair code).1 code) =
        some
          (censusHandoff (censusSelectedField code) (censusUndecidedField code)
            (censusSupportField code) (censusWidthField code)
            (censusStepField code)) := by
    have hrun :=
      run_censusProgram (Nat.unpair code).1 (censusSelectedField code)
        (censusUndecidedField code) (censusSupportField code)
        (censusWidthField code) (censusStepField code) maximumBits hcensusBits
    rw [censusInput_fields] at hrun
    exact hrun
  have hstageThree :
      runNPOracleProgram gateTouchProgram maximumBits
          (gateTouchFuel
            (undecidedCensus (censusUndecidedField code)
              (censusWidthField code))
            (residualCensus (censusUndecidedField code)
              (censusSupportField code) (censusWidthField code))
            (censusStepField code))
          (initialNPOracleState (Nat.unpair code).1
            (censusHandoff (censusSelectedField code)
              (censusUndecidedField code) (censusSupportField code)
              (censusWidthField code) (censusStepField code))) =
        some (gateCensusOutput code) :=
    run_gateTouchProgram (Nat.unpair code).1
      (meetsCensus (censusSelectedField code) (censusSupportField code)
        (censusWidthField code))
      (undecidedCensus (censusUndecidedField code) (censusWidthField code))
      (residualCensus (censusUndecidedField code) (censusSupportField code)
        (censusWidthField code))
      (censusStepField code) maximumBits hgateBits
  exact run_linkPrograms hpositive hlength hstageOne
    (run_linkPrograms hpositive hlength hstageTwo hstageThree)

/-! ## §6 The whole occurrence pool -/

private theorem le_foldr_max_of_mem
    {value base : ℕ} {values : List ℕ} (hvalue : value ∈ values) :
    value ≤ values.foldr max base := by
  induction values with
  | nil => simp at hvalue
  | cons head tail inductionHypothesis =>
      rcases List.mem_cons.mp hvalue with rfl | hvalue
      · exact Nat.le_max_left _ _
      · exact (inductionHypothesis hvalue).trans (Nat.le_max_right _ _)

/-- One census request per retained occurrence; the two coordinate sets and the
step count are shared context copied into every atom. -/
def conditionalTouchNumeratorRequests {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (selected undecided : Finset (Fin q)) (stepCount : ℕ) : List ℕ :=
  occurrences.map fun gate =>
    censusInput (coordinateMask selected) (coordinateMask undecided)
      (coordinateMask gate.support) q stepCount

def conditionalTouchNumeratorInput {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (selected undecided : Finset (Fin q)) (stepCount : ℕ) : ℕ :=
  encodeBalancedList
    (conditionalTouchNumeratorRequests occurrences selected undecided stepCount)

/-- **The conditional touch numerator program.**  One balanced call of the
per-occurrence stage, then the existing balanced natural-number sum. -/
def conditionalTouchNumeratorProgram : NPOracleProgram :=
  balancedNatSumAfterProgram (balancedCallProgram gateCensusProgram)

theorem conditionalTouchNumeratorProgram_oracleFree :
    OracleFree conditionalTouchNumeratorProgram :=
  balancedNatSumAfterProgram_oracleFree (balancedCallProgram gateCensusProgram)
    (balancedCallProgram_oracleFree gateCensusProgram_oracleFree)

def conditionalTouchNumeratorProducerBits {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (selected undecided : Finset (Fin q)) (stepCount : ℕ) : ℕ :=
  max
    (balancedCallRequiredBits gateCensusOutput
      (conditionalTouchNumeratorRequests occurrences selected undecided
        stepCount))
    (((conditionalTouchNumeratorRequests occurrences selected undecided
      stepCount).map gateCensusBits).foldr max 1)

def conditionalTouchNumeratorFuel {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (selected undecided : Finset (Fin q)) (stepCount : ℕ) : ℕ :=
  balancedNatSumAfterFuel
    (balancedCallFuel gateCensusProgram gateCensusFuel
      (conditionalTouchNumeratorRequests occurrences selected undecided
        stepCount))
    ((conditionalTouchNumeratorRequests occurrences selected undecided
      stepCount).map gateCensusOutput)

def conditionalTouchNumeratorBits {q : ℕ} (inputLength : ℕ)
    (occurrences : List (SupportedNormalizedGate q))
    (selected undecided : Finset (Fin q)) (stepCount : ℕ) : ℕ :=
  balancedNatSumAfterBits inputLength
    (conditionalTouchNumeratorProducerBits occurrences selected undecided
      stepCount)
    ((conditionalTouchNumeratorRequests occurrences selected undecided
      stepCount).map gateCensusOutput)

theorem gateCensusOutput_request {q : ℕ}
    (selected undecided support : Finset (Fin q)) (stepCount : ℕ) :
    gateCensusOutput
        (censusInput (coordinateMask selected) (coordinateMask undecided)
          (coordinateMask support) q stepCount) =
      conditionalGateTouchCount selected undecided support stepCount := by
  unfold gateCensusOutput
  simp only [censusSelectedField_censusInput, censusUndecidedField_censusInput,
    censusSupportField_censusInput, censusWidthField_censusInput,
    censusStepField_censusInput]
  exact gateTouchValue_census selected undecided support stepCount

theorem sum_gateCensusOutput {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (selected undecided : Finset (Fin q)) (stepCount : ℕ) :
    ((conditionalTouchNumeratorRequests occurrences selected undecided
        stepCount).map gateCensusOutput).sum =
      conditionalTouchNumerator (occurrenceSupport occurrences) selected
        undecided stepCount := by
  unfold conditionalTouchNumeratorRequests
  rw [List.map_map]
  have hscores :
      occurrences.map
          (gateCensusOutput ∘ fun gate =>
            censusInput (coordinateMask selected) (coordinateMask undecided)
              (coordinateMask gate.support) q stepCount) =
        occurrences.map fun gate =>
          conditionalGateTouchCount selected undecided gate.support
            stepCount := by
    refine List.map_congr_left ?_
    intro gate _
    simp only [Function.comp_apply]
    exact gateCensusOutput_request selected undecided gate.support stepCount
  rw [hscores]
  have hlist :
      (occurrences.map fun gate =>
          conditionalGateTouchCount selected undecided gate.support
            stepCount) =
        List.ofFn fun index : Fin occurrences.length =>
          conditionalGateTouchCount selected undecided
            occurrences[(index : ℕ)].support stepCount :=
    (List.ofFn_getElem_eq_map occurrences fun gate =>
      conditionalGateTouchCount selected undecided gate.support stepCount).symm
  rw [hlist, List.sum_ofFn]
  rfl

/-- **The conditional touch numerator, executed.**  One fixed oracle-free
program returns the exact closed score
`conditionalTouchNumerator (occurrenceSupport occurrences) selected undecided
stepCount` from the balanced census request list. -/
theorem run_conditionalTouchNumeratorProgram
    (inputLength : ℕ) {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (selected undecided : Finset (Fin q)) (stepCount maximumBits : ℕ)
    (hbits :
      conditionalTouchNumeratorBits inputLength occurrences selected undecided
          stepCount ≤
        maximumBits) :
    runNPOracleProgram conditionalTouchNumeratorProgram maximumBits
        (conditionalTouchNumeratorFuel occurrences selected undecided
          stepCount)
        (initialNPOracleState inputLength
          (conditionalTouchNumeratorInput occurrences selected undecided
            stepCount)) =
      some
        (conditionalTouchNumerator (occurrenceSupport occurrences) selected
          undecided stepCount) := by
  have hexec : ∀ request : ℕ,
      request ∈
        conditionalTouchNumeratorRequests occurrences selected undecided
          stepCount →
      runNPOracleProgram gateCensusProgram
          (conditionalTouchNumeratorProducerBits occurrences selected undecided
            stepCount)
          (gateCensusFuel request)
          (initialNPOracleState (Nat.unpair request).1
            (Nat.unpair request).2) =
        some (gateCensusOutput request) := by
    intro request hrequest
    refine run_gateCensusProgram request _ ?_
    refine
      le_trans (le_foldr_max_of_mem (base := 1) (List.mem_map_of_mem hrequest))
        ?_
    exact Nat.le_max_right _ _
  have hproducer :=
    run_balancedCallProgram_from
      (callee := gateCensusProgram)
      (maximumBits :=
        conditionalTouchNumeratorProducerBits occurrences selected undecided
          stepCount)
      inputLength
      (conditionalTouchNumeratorRequests occurrences selected undecided
        stepCount)
      gateCensusFuel gateCensusOutput (Nat.le_max_left _ _) hexec
  rw [← sum_gateCensusOutput occurrences selected undecided stepCount]
  exact run_bits_mono
    (run_balancedNatSumAfterProgram (balancedCallProgram gateCensusProgram)
      inputLength
      (conditionalTouchNumeratorInput occurrences selected undecided stepCount)
      (conditionalTouchNumeratorProducerBits occurrences selected undecided
        stepCount)
      (balancedCallFuel gateCensusProgram gateCensusFuel
        (conditionalTouchNumeratorRequests occurrences selected undecided
          stepCount))
      ((conditionalTouchNumeratorRequests occurrences selected undecided
        stepCount).map gateCensusOutput)
      hproducer)
    hbits

/-! ## §7 Mask arithmetic for the greedy sweep

The sweep updates its two coordinate sets one coordinate at a time, so a
controller carrying bitmasks only ever adds or removes a single power of two.
-/

theorem coordinateMask_eq_sum {q : ℕ} (values : Finset (Fin q)) :
    coordinateMask values = ∑ index ∈ values, 2 ^ (index : ℕ) := by
  have hofBits :
      coordinateMask values =
        encodeBitInput fun index : Fin q => decide (index ∈ values) :=
    (encodeBitInput_eq_ofBits _).symm
  rw [hofBits]
  unfold encodeBitInput
  simp

@[simp] theorem coordinateMask_empty (q : ℕ) :
    coordinateMask (∅ : Finset (Fin q)) = 0 := by
  rw [coordinateMask_eq_sum]
  simp

theorem coordinateMask_insert {q : ℕ} (values : Finset (Fin q))
    {index : Fin q} (hindex : index ∉ values) :
    coordinateMask (insert index values) =
      coordinateMask values + 2 ^ (index : ℕ) := by
  rw [coordinateMask_eq_sum, coordinateMask_eq_sum, Finset.sum_insert hindex]
  exact Nat.add_comm _ _

theorem coordinateMask_erase {q : ℕ} (values : Finset (Fin q))
    {index : Fin q} (hindex : index ∈ values) :
    coordinateMask (values.erase index) =
      coordinateMask values - 2 ^ (index : ℕ) := by
  have hsum :=
    Finset.sum_erase_add values (fun index : Fin q => 2 ^ (index : ℕ)) hindex
  rw [coordinateMask_eq_sum, coordinateMask_eq_sum]
  omega

private theorem sum_range_two_pow_succ (count : ℕ) :
    (∑ index ∈ Finset.range count, 2 ^ index) + 1 = 2 ^ count := by
  induction count with
  | zero => simp
  | succ count inductionHypothesis =>
      rw [Finset.sum_range_succ, pow_succ]
      omega

theorem coordinateMask_univ (q : ℕ) :
    coordinateMask (Finset.univ : Finset (Fin q)) = 2 ^ q - 1 := by
  rw [coordinateMask_eq_sum]
  have hrange :
      (∑ index ∈ (Finset.univ : Finset (Fin q)), 2 ^ (index : ℕ)) =
        ∑ index ∈ Finset.range q, 2 ^ index :=
    Fin.sum_univ_eq_sum_range (fun index => 2 ^ index) q
  have hsum := sum_range_two_pow_succ q
  omega

/-! ## §8 The touching cost and the greedy sweep's step

At `stepCount = 0` the same fold is the touching cost itself
(`SupplierTouching.conditionalTouchNumerator_zero`), so no second program is
needed for the sweep's final answer. -/

/-- **The touching cost of an occurrence pool, executed.** -/
theorem run_touchingCostProgram
    (inputLength : ℕ) {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (selected undecided : Finset (Fin q)) (maximumBits : ℕ)
    (hbits :
      conditionalTouchNumeratorBits inputLength occurrences selected undecided
          0 ≤
        maximumBits) :
    runNPOracleProgram conditionalTouchNumeratorProgram maximumBits
        (conditionalTouchNumeratorFuel occurrences selected undecided 0)
        (initialNPOracleState inputLength
          (conditionalTouchNumeratorInput occurrences selected undecided 0)) =
      some (touchingCost (occurrenceSupport occurrences) selected) := by
  rw [← conditionalTouchNumerator_zero (occurrenceSupport occurrences) selected
    undecided]
  exact run_conditionalTouchNumeratorProgram inputLength occurrences selected
    undecided 0 maximumBits hbits

/-- One greedy sweep step, restated against the exact zero-or-one decision
`CanonicalTouchingStepProgram.run_touchingStepProgram` returns.  Both numerators
in the test are instances of `run_conditionalTouchNumeratorProgram`, so a
sweep controller needs no further arithmetic. -/
theorem touchingSelectAux_cons_decision
    {Gate : Type} [Fintype Gate] {q : ℕ} (support : Gate → Finset (Fin q))
    (selected : Finset (Fin q)) (stepCount : ℕ) (coordinate : Fin q)
    (rest : List (Fin q)) (hstep : stepCount ≠ 0) :
    touchingSelectAux support selected stepCount (coordinate :: rest) =
      (if
          (if conditionalTouchNumerator support (insert coordinate selected)
                  rest.toFinset (stepCount - 1) *
                Nat.choose rest.length stepCount ≤
              conditionalTouchNumerator support selected rest.toFinset
                  stepCount *
                Nat.choose rest.length (stepCount - 1) then
            1
          else
            0) = 1 then
        touchingSelectAux support (insert coordinate selected) (stepCount - 1)
          rest
      else
        touchingSelectAux support selected stepCount rest) := by
  by_cases hchoice :
      conditionalTouchNumerator support (insert coordinate selected)
            rest.toFinset (stepCount - 1) *
          Nat.choose rest.length stepCount ≤
        conditionalTouchNumerator support selected rest.toFinset stepCount *
          Nat.choose rest.length (stepCount - 1)
  · simp [touchingSelectAux, hstep, hchoice]
  · simp [touchingSelectAux, hstep, hchoice]

end NearCubicWires.CanonicalConditionalTouchProgram
