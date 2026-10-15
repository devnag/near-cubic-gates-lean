import Proof.MachineModel.CanonicalNativeCallProgram
import Proof.MachineModel.CanonicalTouchingSweepProgram
import Proof.MachineModel.CanonicalTwoPowProgram

/-!
# The greedy touching sweep, one round at a time

`CanonicalTouchingSweepProgram` §5 leaves exactly one obligation on the
symmetric counting path: a *round* program whose single step is
`CanonicalTouchingSweepProgram.sweepRound`.  This module supplies it, and
composes it with the counted round controller to obtain the executable
`SupplierTouching.touchingSelect`.

The round's data is fixed by `sweepRound`'s definition:

* the coordinate of the round at descending counter `counter + 1` is
  `q - (counter + 1)`, and the remaining-coordinate set is the suffix
  `(List.finRange q).drop (q - counter)`, whose `coordinateMask` is the
  one-`binaryTwoPowProgram` difference `2 ^ q - 2 ^ (q - counter)`;
* the two conditional numerators are
  `CanonicalConditionalTouchProgram.run_conditionalTouchNumeratorProgram` at
  `(insert coordinate selected, rest, stepCount - 1)` and
  `(selected, rest, stepCount)`, whose census request lists are the
  shared-context broadcast of `pair (pair selectedMask restMask)` over the
  pool's support-mask list;
* the branch test is `CanonicalTouchingStepProgram.run_touchingStepProgram`;
* the mask update is `coordinateMask_insert`, taken through the machine's
  `testBit` so that the update is correct even for a coordinate the carried
  mask already holds.

The round callee's context register `r1` carries the whole sweep state, so the
broadcast reads its shared census fields straight from the round-call ABI.
-/

open Finset

namespace NearCubicWires.CanonicalTouchingSweepRoundProgram

open NearCubicWires
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalConditionalTouchProgram
open NearCubicWires.CanonicalNativeCallProgram
open NearCubicWires.CanonicalOccurrencePopulationProgram
open NearCubicWires.CanonicalPairedCall
open NearCubicWires.CanonicalRoundCall
open NearCubicWires.CanonicalTouchingStepProgram
open NearCubicWires.CanonicalTouchingSweepProgram
open NearCubicWires.CanonicalTwoPowProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierTouching
open NearCubicWires.VerifiedLinker

private theorem bits_of_le {value bound maximumBits : ℕ}
    (hvalue : value ≤ bound) (hbits : natBitLength bound ≤ maximumBits) :
    natBitLength value ≤ maximumBits :=
  (natBitLength_mono hvalue).trans hbits

private theorem le_foldr_max_of_mem
    {value base : ℕ} {values : List ℕ} (hvalue : value ∈ values) :
    value ≤ values.foldr max base := by
  induction values with
  | nil => simp at hvalue
  | cons head tail inductionHypothesis =>
      rcases List.mem_cons.mp hvalue with rfl | hvalue
      · exact Nat.le_max_left _ _
      · exact (inductionHypothesis hvalue).trans (Nat.le_max_right _ _)

/-! ## §1 The remaining-coordinate suffix, as a bitmask -/

/-- Membership in the sweep's remaining-coordinate suffix is one comparison. -/
theorem mem_finRange_drop {q : ℕ} :
    ∀ counter : ℕ, counter ≤ q → ∀ index : Fin q,
      (index ∈ (List.finRange q).drop (q - counter) ↔
        q - counter ≤ index.val) := by
  intro counter
  induction counter with
  | zero =>
      intro _hcounter index
      rw [Nat.sub_zero, finRange_drop_self]
      constructor
      · intro hmember
        simp at hmember
      · intro hbound
        exact absurd index.isLt (by omega)
  | succ count inductionHypothesis =>
      intro hcounter index
      have hindex : q - (count + 1) < q := by omega
      have hshift : q - (count + 1) + 1 = q - count := by omega
      have htail := inductionHypothesis (by omega) index
      rw [finRange_drop_cons q (q - (count + 1)) hindex, hshift, List.mem_cons,
        htail]
      constructor
      · rintro (hequal | hbound)
        · subst hequal
          exact Nat.le_refl _
        · omega
      · intro hbound
        rcases Nat.eq_or_lt_of_le hbound with hequal | hstrict
        · exact Or.inl (Fin.ext hequal.symm)
        · exact Or.inr (by omega)

/-- The suffix has exactly `counter` coordinates left. -/
theorem length_finRange_drop (q counter : ℕ) (hcounter : counter ≤ q) :
    ((List.finRange q).drop (q - counter)).length = counter := by
  rw [List.length_drop, List.length_finRange]
  omega

private theorem sub_double_add_half {total half : ℕ}
    (hhalf : half + half ≤ total) :
    total - (half + half) + half = total - half := by
  omega

/-- **The remaining-coordinate mask is one power-of-two difference.** -/
theorem coordinateMask_finRange_drop {q : ℕ} :
    ∀ counter : ℕ, counter ≤ q →
      coordinateMask (((List.finRange q).drop (q - counter)).toFinset) =
        2 ^ q - 2 ^ (q - counter) := by
  intro counter
  induction counter with
  | zero =>
      intro _hcounter
      rw [Nat.sub_zero, finRange_drop_self]
      simp
  | succ count inductionHypothesis =>
      intro hcounter
      have hindex : q - (count + 1) < q := by omega
      have hshift : q - (count + 1) + 1 = q - count := by omega
      have hnotMember :
          (⟨q - (count + 1), hindex⟩ : Fin q) ∉
            ((List.finRange q).drop (q - count)).toFinset := by
        rw [List.mem_toFinset,
          mem_finRange_drop count (by omega) ⟨q - (count + 1), hindex⟩]
        change ¬ q - count ≤ q - (count + 1)
        omega
      have htail := inductionHypothesis (by omega)
      have hpower :
          2 ^ (q - count) =
            2 ^ (q - (count + 1)) + 2 ^ (q - (count + 1)) := by
        rw [← hshift, pow_succ]
        ring
      have hbound : 2 ^ (q - count) ≤ 2 ^ q :=
        Nat.pow_le_pow_right (by omega) (by omega)
      have hhalf :
          2 ^ (q - (count + 1)) + 2 ^ (q - (count + 1)) ≤ 2 ^ q := by
        rw [← hpower]
        exact hbound
      rw [finRange_drop_cons q (q - (count + 1)) hindex, hshift,
        List.toFinset_cons, coordinateMask_insert _ hnotMember, htail]
      change 2 ^ q - 2 ^ (q - count) + 2 ^ (q - (count + 1)) =
        2 ^ q - 2 ^ (q - (count + 1))
      rw [hpower]
      exact sub_double_add_half hhalf

/-- Inserting a coordinate into a mask, exactly as the machine does it: the
carried mask's own bit decides whether the power of two is added. -/
def insertMask (selectedMask coordinate : ℕ) : ℕ :=
  if selectedMask.testBit coordinate then
    selectedMask
  else
    selectedMask + 2 ^ coordinate

theorem insertMask_coordinateMask {q : ℕ} (values : Finset (Fin q))
    (index : Fin q) :
    insertMask (coordinateMask values) index.val =
      coordinateMask (insert index values) := by
  unfold insertMask
  by_cases hmember : index ∈ values
  · rw [if_pos (by rw [testBit_coordinateMask]; simpa using hmember)]
    rw [Finset.insert_eq_self.mpr hmember]
  · rw [if_neg (by rw [testBit_coordinateMask]; simpa using hmember)]
    exact (coordinateMask_insert values hmember).symm

/-! ## §2 The pool's support masks and the round context -/

/-- The occurrence pool's support masks, in occurrence order. -/
def occurrenceSupportMasks {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q)) : List ℕ :=
  occurrences.map fun gate => coordinateMask gate.support

/-- **The round callee's fixed context**: the coordinate count beside the
balanced list of the pool's support masks. -/
def touchingSweepContext {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q)) (width : ℕ) : ℕ :=
  Nat.pair width (encodeBalancedList (occurrenceSupportMasks occurrences))

/-- Shared census context, broadcast over the support-mask list: everything a
census request holds except the gate's own support mask. -/
def censusShared (selectedMask undecidedMask width stepCount : ℕ) : ℕ :=
  Nat.pair (Nat.pair selectedMask undecidedMask) (Nat.pair width stepCount)

/-! ## §3 One census request, built from the shared context -/

/-- Splice one support mask into the shared census context. -/
def censusAtomOutput (code : ℕ) : ℕ :=
  Nat.pair (Nat.unpair (Nat.unpair code).1).1
    (Nat.pair (Nat.unpair code).2 (Nat.unpair (Nat.unpair code).1).2)

theorem censusAtomOutput_censusShared
    (selectedMask undecidedMask width stepCount mask : ℕ) :
    censusAtomOutput
        (Nat.pair (censusShared selectedMask undecidedMask width stepCount)
          mask) =
      censusInput selectedMask undecidedMask mask width stepCount := by
  simp [censusAtomOutput, censusShared, censusInput]

/-- Splice the shared context around one support mask. -/
def censusBuildProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 2 4 3
  , .unpairRight 2 5 4
  , .pair 3 5 6 5
  , .pair 4 6 0 6
  , .halt 0
  ]

@[simp] theorem censusBuildProgram_oracleFree :
    OracleFree censusBuildProgram := by
  rfl

def censusBuildBits (code : ℕ) : ℕ :=
  max (natBitLength code) (natBitLength (censusAtomOutput code))

theorem run_censusBuildProgram (inputLength code maximumBits : ℕ)
    (hbits : censusBuildBits code ≤ maximumBits) :
    runNPOracleProgram censusBuildProgram maximumBits 7
        (initialNPOracleState inputLength code) =
      some (censusAtomOutput code) := by
  have hshape :
      censusAtomOutput code =
        Nat.pair (Nat.unpair (Nat.unpair code).1).1
          (Nat.pair (Nat.unpair code).2
            (Nat.unpair (Nat.unpair code).1).2) := rfl
  have hcodeBits : natBitLength code ≤ maximumBits :=
    (Nat.le_max_left _ _).trans hbits
  have houtputBits : natBitLength (censusAtomOutput code) ≤ maximumBits :=
    (Nat.le_max_right _ _).trans hbits
  rw [hshape] at houtputBits
  have hsharedBits : natBitLength (Nat.unpair code).1 ≤ maximumBits :=
    bits_of_le (Nat.unpair_left_le _) hcodeBits
  have hmaskBits : natBitLength (Nat.unpair code).2 ≤ maximumBits :=
    bits_of_le (Nat.unpair_right_le _) hcodeBits
  have hheadBits :
      natBitLength (Nat.unpair (Nat.unpair code).1).1 ≤ maximumBits :=
    bits_of_le (Nat.left_le_pair _ _) houtputBits
  have htailBits :
      natBitLength
          (Nat.pair (Nat.unpair code).2
            (Nat.unpair (Nat.unpair code).1).2) ≤
        maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) houtputBits
  have hsharedTailBits :
      natBitLength (Nat.unpair (Nat.unpair code).1).2 ≤ maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) htailBits
  rw [show (7 : ℕ) = 0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 by omega]
  rw [run_unpairLeft_instruction (value := (Nat.unpair code).1) (by rfl) rfl
    (by simp [initialNPOracleState]) hsharedBits]
  rw [run_unpairRight_instruction (value := (Nat.unpair code).2) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hmaskBits]
  rw [run_unpairLeft_instruction
    (value := (Nat.unpair (Nat.unpair code).1).1) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hheadBits]
  rw [run_unpairRight_instruction
    (value := (Nat.unpair (Nat.unpair code).1).2) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hsharedTailBits]
  rw [run_pair_instruction
    (value :=
      Nat.pair (Nat.unpair code).2 (Nat.unpair (Nat.unpair code).1).2)
    (by rfl) rfl (by simp [NPOracleState.write, NPOracleState.jump])
    htailBits]
  rw [run_pair_instruction (value := censusAtomOutput code) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hshape]) (by
      rw [hshape]
      exact houtputBits)]
  exact run_halt_instruction (fuel := 0) (value := censusAtomOutput code)
    (by rfl) rfl (by simp [NPOracleState.write, NPOracleState.jump])
    (by rw [hshape]; exact houtputBits)

/-- **The per-atom census request builder.**  Repair the balanced-call atom,
then splice the shared context around the support mask. -/
def censusAtomProgram : NPOracleProgram :=
  linkPrograms repairAtomProgram censusBuildProgram

theorem censusAtomProgram_oracleFree : OracleFree censusAtomProgram :=
  oracleFree_linkPrograms repairAtomProgram_oracleFree
    censusBuildProgram_oracleFree

def censusAtomFuel (_code : ℕ) : ℕ :=
  linkFuel censusBuildProgram 2 7

def censusAtomBits (code : ℕ) : ℕ :=
  max 1 (max (natBitLength code) (censusBuildBits code))

theorem run_censusAtomProgram (code maximumBits : ℕ)
    (hbits : censusAtomBits code ≤ maximumBits) :
    runNPOracleProgram censusAtomProgram maximumBits (censusAtomFuel code)
        (initialNPOracleState (Nat.unpair code).1 (Nat.unpair code).2) =
      some (censusAtomOutput code) := by
  have hpositive : 1 ≤ maximumBits := (Nat.le_max_left _ _).trans hbits
  have hcodeBits : natBitLength code ≤ maximumBits :=
    (Nat.le_max_left _ _).trans ((Nat.le_max_right _ _).trans hbits)
  have hbuildBits : censusBuildBits code ≤ maximumBits :=
    (Nat.le_max_right _ _).trans ((Nat.le_max_right _ _).trans hbits)
  have hlength : natBitLength (Nat.unpair code).1 ≤ maximumBits :=
    bits_of_le (Nat.unpair_left_le _) hcodeBits
  have hpair : Nat.pair (Nat.unpair code).1 (Nat.unpair code).2 = code :=
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
      runNPOracleProgram censusBuildProgram maximumBits 7
          (initialNPOracleState (Nat.unpair code).1 code) =
        some (censusAtomOutput code) :=
    run_censusBuildProgram (Nat.unpair code).1 code maximumBits hbuildBits
  exact run_linkPrograms hpositive hlength hstageOne hstageTwo

/-! ## §4 The shared-context broadcast over the support-mask list -/

def censusBroadcastRequests (shared : ℕ) (masks : List ℕ) : List ℕ :=
  masks.map (nativeInputRequest shared)

def censusBroadcastOutputs (shared : ℕ) (masks : List ℕ) : List ℕ :=
  masks.map fun mask => censusAtomOutput (Nat.pair shared mask)

theorem map_censusAtomOutput_censusBroadcastRequests
    (shared : ℕ) (masks : List ℕ) :
    (censusBroadcastRequests shared masks).map censusAtomOutput =
      censusBroadcastOutputs shared masks := by
  unfold censusBroadcastRequests censusBroadcastOutputs
  rw [List.map_map]
  refine List.map_congr_left ?_
  intro mask _
  simp only [Function.comp_apply]
  rfl

/-- **The broadcast program.**  Pair the preserved shared context onto every
support mask, then splice each pair into a census request. -/
def censusBroadcastProgram : NPOracleProgram :=
  linkPrograms nativeInputRequestTreeProgram
    (balancedCallProgram censusAtomProgram)

theorem censusBroadcastProgram_oracleFree :
    OracleFree censusBroadcastProgram :=
  oracleFree_linkPrograms nativeInputRequestTreeProgram_oracleFree
    (balancedCallProgram_oracleFree censusAtomProgram_oracleFree)

def censusBroadcastFuel (shared : ℕ) (masks : List ℕ) : ℕ :=
  linkFuel (balancedCallProgram censusAtomProgram)
    (nativeInputRequestTreeFuel masks)
    (balancedCallFuel censusAtomProgram censusAtomFuel
      (censusBroadcastRequests shared masks))

def censusBroadcastStageBits (shared : ℕ) (masks : List ℕ) : List ℕ :=
  [ 1
  , natBitLength shared
  , nativeInputRequestTreeBits shared masks
  , balancedCallRequiredBits censusAtomOutput
      (censusBroadcastRequests shared masks)
  , ((censusBroadcastRequests shared masks).map censusAtomBits).foldr max 1
  ]

def censusBroadcastBits (shared : ℕ) (masks : List ℕ) : ℕ :=
  (censusBroadcastStageBits shared masks).foldr max 1

/-- **The broadcast, executed.**  The shared census context arrives in the
preserved context register, so no request repeats it. -/
theorem run_censusBroadcastProgram (shared : ℕ) (masks : List ℕ)
    (maximumBits : ℕ)
    (hbits : censusBroadcastBits shared masks ≤ maximumBits) :
    runNPOracleProgram censusBroadcastProgram maximumBits
        (censusBroadcastFuel shared masks)
        (initialNPOracleState shared (encodeBalancedList masks)) =
      some (encodeBalancedList (censusBroadcastOutputs shared masks)) := by
  have bits_of_member {value : ℕ}
      (hvalue : value ∈ censusBroadcastStageBits shared masks) :
      value ≤ maximumBits :=
    le_trans (le_foldr_max_of_mem hvalue) hbits
  have hpositive : 1 ≤ maximumBits := by
    apply bits_of_member
    simp [censusBroadcastStageBits]
  have hlength : natBitLength shared ≤ maximumBits := by
    apply bits_of_member
    simp [censusBroadcastStageBits]
  have htreeBits : nativeInputRequestTreeBits shared masks ≤ maximumBits := by
    apply bits_of_member
    simp [censusBroadcastStageBits]
  have hcallBits :
      balancedCallRequiredBits censusAtomOutput
          (censusBroadcastRequests shared masks) ≤
        maximumBits := by
    apply bits_of_member
    simp [censusBroadcastStageBits]
  have hcalleeBits :
      ((censusBroadcastRequests shared masks).map censusAtomBits).foldr max 1 ≤
        maximumBits := by
    apply bits_of_member
    simp [censusBroadcastStageBits]
  have hstageOne :
      runNPOracleProgram nativeInputRequestTreeProgram maximumBits
          (nativeInputRequestTreeFuel masks)
          (initialNPOracleState shared (encodeBalancedList masks)) =
        some (encodeBalancedList (censusBroadcastRequests shared masks)) :=
    run_bits_mono (run_nativeInputRequestTreeProgram shared masks) htreeBits
  have hexec : ∀ request : ℕ,
      request ∈ censusBroadcastRequests shared masks →
      runNPOracleProgram censusAtomProgram maximumBits
          (censusAtomFuel request)
          (initialNPOracleState (Nat.unpair request).1
            (Nat.unpair request).2) =
        some (censusAtomOutput request) := by
    intro request hrequest
    refine run_censusAtomProgram request maximumBits ?_
    exact le_trans
      (le_foldr_max_of_mem (base := 1) (List.mem_map_of_mem hrequest))
      hcalleeBits
  have hstageTwo :=
    run_balancedCallProgram_from (callee := censusAtomProgram)
      (maximumBits := maximumBits) shared
      (censusBroadcastRequests shared masks) censusAtomFuel censusAtomOutput
      hcallBits hexec
  rw [map_censusAtomOutput_censusBroadcastRequests] at hstageTwo
  exact run_linkPrograms hpositive hlength hstageOne hstageTwo

/-- The broadcast's output list is exactly the conditional numerator's census
request list. -/
theorem censusBroadcastOutputs_occurrenceSupportMasks {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (selected undecided : Finset (Fin q)) (stepCount : ℕ) :
    censusBroadcastOutputs
        (censusShared (coordinateMask selected) (coordinateMask undecided) q
          stepCount)
        (occurrenceSupportMasks occurrences) =
      conditionalTouchNumeratorRequests occurrences selected undecided
        stepCount := by
  unfold censusBroadcastOutputs occurrenceSupportMasks
    conditionalTouchNumeratorRequests
  rw [List.map_map]
  refine List.map_congr_left ?_
  intro gate _
  simp only [Function.comp_apply]
  exact censusAtomOutput_censusShared (coordinateMask selected)
    (coordinateMask undecided) q stepCount (coordinateMask gate.support)

/-! ## §5 One numerator's request tree, on a computed context -/

/-- **The broadcast, invoked with a computed context.**  The census context of
the round is not the round callee's own input length, so the broadcast runs
behind the canonical native-input call. -/
def broadcastCallProgram : NPOracleProgram :=
  nativeCallProgram censusBroadcastProgram

theorem broadcastCallProgram_oracleFree : OracleFree broadcastCallProgram :=
  nativeCallProgram_oracleFree censusBroadcastProgram_oracleFree

def broadcastCallFuel (shared : ℕ) (masks : List ℕ) : ℕ :=
  nativeCallFuel censusBroadcastProgram (censusBroadcastFuel shared masks)
    shared (encodeBalancedList masks)

def broadcastCallBits (outerInputLength shared : ℕ) (masks : List ℕ) : ℕ :=
  nativeCallBits outerInputLength shared (encodeBalancedList masks)
    (encodeBalancedList (censusBroadcastOutputs shared masks))
    (censusBroadcastBits shared masks)

theorem run_broadcastCallProgram
    (outerInputLength shared : ℕ) (masks : List ℕ) :
    runNPOracleProgram broadcastCallProgram
        (broadcastCallBits outerInputLength shared masks)
        (broadcastCallFuel shared masks)
        (initialNPOracleState outerInputLength
          (Nat.pair shared (encodeBalancedList masks))) =
      some (encodeBalancedList (censusBroadcastOutputs shared masks)) :=
  run_nativeCallProgram censusBroadcastProgram outerInputLength shared
    (encodeBalancedList masks)
    (encodeBalancedList (censusBroadcastOutputs shared masks))
    (censusBroadcastBits shared masks) (censusBroadcastFuel shared masks)
    (run_censusBroadcastProgram shared masks
      (censusBroadcastBits shared masks) (le_refl _))

/-- The round's shared census context for one of its two numerators. -/
def roundSharedContext {q : ℕ} (selected undecided : Finset (Fin q))
    (stepCount : ℕ) : ℕ :=
  censusShared (coordinateMask selected) (coordinateMask undecided) q stepCount

/-- The broadcast request of one numerator: its shared context beside the
pool's support-mask list. -/
def roundBroadcastRequest {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (selected undecided : Finset (Fin q)) (stepCount : ℕ) : ℕ :=
  Nat.pair (roundSharedContext selected undecided stepCount)
    (encodeBalancedList (occurrenceSupportMasks occurrences))

def roundBroadcastFuel {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (selected undecided : Finset (Fin q)) (stepCount : ℕ) : ℕ :=
  broadcastCallFuel (roundSharedContext selected undecided stepCount)
    (occurrenceSupportMasks occurrences)

def roundBroadcastBits {q : ℕ} (inputLength : ℕ)
    (occurrences : List (SupportedNormalizedGate q))
    (selected undecided : Finset (Fin q)) (stepCount : ℕ) : ℕ :=
  broadcastCallBits inputLength
    (roundSharedContext selected undecided stepCount)
    (occurrenceSupportMasks occurrences)

/-- **One numerator's census request tree, executed.** -/
theorem run_roundBroadcast {q : ℕ} (inputLength : ℕ)
    (occurrences : List (SupportedNormalizedGate q))
    (selected undecided : Finset (Fin q)) (stepCount : ℕ) :
    runNPOracleProgram broadcastCallProgram
        (roundBroadcastBits inputLength occurrences selected undecided
          stepCount)
        (roundBroadcastFuel occurrences selected undecided stepCount)
        (initialNPOracleState inputLength
          (roundBroadcastRequest occurrences selected undecided stepCount)) =
      some
        (conditionalTouchNumeratorInput occurrences selected undecided
          stepCount) := by
  have hrun :=
    run_broadcastCallProgram inputLength
      (roundSharedContext selected undecided stepCount)
      (occurrenceSupportMasks occurrences)
  have houtputs :
      censusBroadcastOutputs (roundSharedContext selected undecided stepCount)
          (occurrenceSupportMasks occurrences) =
        conditionalTouchNumeratorRequests occurrences selected undecided
          stepCount :=
    censusBroadcastOutputs_occurrenceSupportMasks occurrences selected
      undecided stepCount
  rw [houtputs] at hrun
  exact hrun

/-! ## §6 Both numerators of one round -/

/-- **The round's numerator pair.**  One paired broadcast builds both census
request trees; one paired conditional-numerator call scores them. -/
def numeratorPairProgram : NPOracleProgram :=
  linkPrograms (pairedCallProgram broadcastCallProgram)
    (pairedCallProgram conditionalTouchNumeratorProgram)

theorem numeratorPairProgram_oracleFree : OracleFree numeratorPairProgram :=
  oracleFree_linkPrograms
    (pairedCallProgram_oracleFree broadcastCallProgram
      broadcastCallProgram_oracleFree)
    (pairedCallProgram_oracleFree conditionalTouchNumeratorProgram
      conditionalTouchNumeratorProgram_oracleFree)

def numeratorPairFuel {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (leftSelected leftUndecided rightSelected rightUndecided : Finset (Fin q))
    (leftStep rightStep : ℕ) : ℕ :=
  linkFuel (pairedCallProgram conditionalTouchNumeratorProgram)
    (pairedCallFuel broadcastCallProgram
      (roundBroadcastFuel occurrences leftSelected leftUndecided leftStep)
      (roundBroadcastFuel occurrences rightSelected rightUndecided rightStep))
    (pairedCallFuel conditionalTouchNumeratorProgram
      (conditionalTouchNumeratorFuel occurrences leftSelected leftUndecided
        leftStep)
      (conditionalTouchNumeratorFuel occurrences rightSelected rightUndecided
        rightStep))

def numeratorPairStageBits {q : ℕ} (inputLength : ℕ)
    (occurrences : List (SupportedNormalizedGate q))
    (leftSelected leftUndecided rightSelected rightUndecided : Finset (Fin q))
    (leftStep rightStep : ℕ) : List ℕ :=
  [ 1
  , natBitLength inputLength
  , pairedCallBits inputLength
      (roundBroadcastBits inputLength occurrences leftSelected leftUndecided
        leftStep)
      (roundBroadcastBits inputLength occurrences rightSelected rightUndecided
        rightStep)
      (roundBroadcastRequest occurrences leftSelected leftUndecided leftStep)
      (roundBroadcastRequest occurrences rightSelected rightUndecided rightStep)
      (conditionalTouchNumeratorInput occurrences leftSelected leftUndecided
        leftStep)
      (conditionalTouchNumeratorInput occurrences rightSelected rightUndecided
        rightStep)
  , pairedCallBits inputLength
      (conditionalTouchNumeratorBits inputLength occurrences leftSelected
        leftUndecided leftStep)
      (conditionalTouchNumeratorBits inputLength occurrences rightSelected
        rightUndecided rightStep)
      (conditionalTouchNumeratorInput occurrences leftSelected leftUndecided
        leftStep)
      (conditionalTouchNumeratorInput occurrences rightSelected rightUndecided
        rightStep)
      (conditionalTouchNumerator (occurrenceSupport occurrences) leftSelected
        leftUndecided leftStep)
      (conditionalTouchNumerator (occurrenceSupport occurrences) rightSelected
        rightUndecided rightStep)
  ]

def numeratorPairBits {q : ℕ} (inputLength : ℕ)
    (occurrences : List (SupportedNormalizedGate q))
    (leftSelected leftUndecided rightSelected rightUndecided : Finset (Fin q))
    (leftStep rightStep : ℕ) : ℕ :=
  (numeratorPairStageBits inputLength occurrences leftSelected leftUndecided
    rightSelected rightUndecided leftStep rightStep).foldr max 1

set_option maxHeartbeats 800000 in
-- Two paired calls linked at one shared register bound; only the closed
-- `…Bits` names appear in the premises.
/-- **Both conditional numerators of one round, executed** from the two shared
census contexts and the pool's support-mask list. -/
theorem run_numeratorPairProgram {q : ℕ} (inputLength : ℕ)
    (occurrences : List (SupportedNormalizedGate q))
    (leftSelected leftUndecided rightSelected rightUndecided : Finset (Fin q))
    (leftStep rightStep maximumBits : ℕ)
    (hbits :
      numeratorPairBits inputLength occurrences leftSelected leftUndecided
          rightSelected rightUndecided leftStep rightStep ≤
        maximumBits) :
    runNPOracleProgram numeratorPairProgram maximumBits
        (numeratorPairFuel occurrences leftSelected leftUndecided rightSelected
          rightUndecided leftStep rightStep)
        (initialNPOracleState inputLength
          (Nat.pair
            (roundBroadcastRequest occurrences leftSelected leftUndecided
              leftStep)
            (roundBroadcastRequest occurrences rightSelected rightUndecided
              rightStep))) =
      some
        (Nat.pair
          (conditionalTouchNumerator (occurrenceSupport occurrences)
            leftSelected leftUndecided leftStep)
          (conditionalTouchNumerator (occurrenceSupport occurrences)
            rightSelected rightUndecided rightStep)) := by
  have bits_of_member {value : ℕ}
      (hvalue :
        value ∈
          numeratorPairStageBits inputLength occurrences leftSelected
            leftUndecided rightSelected rightUndecided leftStep rightStep) :
      value ≤ maximumBits :=
    le_trans (le_foldr_max_of_mem hvalue) hbits
  have hpositive : 1 ≤ maximumBits := by
    apply bits_of_member
    simp [numeratorPairStageBits]
  have hlength : natBitLength inputLength ≤ maximumBits := by
    apply bits_of_member
    simp [numeratorPairStageBits]
  have hbroadcastBits :
      pairedCallBits inputLength
          (roundBroadcastBits inputLength occurrences leftSelected
            leftUndecided leftStep)
          (roundBroadcastBits inputLength occurrences rightSelected
            rightUndecided rightStep)
          (roundBroadcastRequest occurrences leftSelected leftUndecided
            leftStep)
          (roundBroadcastRequest occurrences rightSelected rightUndecided
            rightStep)
          (conditionalTouchNumeratorInput occurrences leftSelected
            leftUndecided leftStep)
          (conditionalTouchNumeratorInput occurrences rightSelected
            rightUndecided rightStep) ≤
        maximumBits := by
    apply bits_of_member
    simp [numeratorPairStageBits]
  have hscoreBits :
      pairedCallBits inputLength
          (conditionalTouchNumeratorBits inputLength occurrences leftSelected
            leftUndecided leftStep)
          (conditionalTouchNumeratorBits inputLength occurrences rightSelected
            rightUndecided rightStep)
          (conditionalTouchNumeratorInput occurrences leftSelected
            leftUndecided leftStep)
          (conditionalTouchNumeratorInput occurrences rightSelected
            rightUndecided rightStep)
          (conditionalTouchNumerator (occurrenceSupport occurrences)
            leftSelected leftUndecided leftStep)
          (conditionalTouchNumerator (occurrenceSupport occurrences)
            rightSelected rightUndecided rightStep) ≤
        maximumBits := by
    apply bits_of_member
    simp [numeratorPairStageBits]
  have hstageOne :=
    run_bits_mono
      (run_pairedCallProgram broadcastCallProgram inputLength
        (roundBroadcastBits inputLength occurrences leftSelected leftUndecided
          leftStep)
        (roundBroadcastBits inputLength occurrences rightSelected
          rightUndecided rightStep)
        (roundBroadcastFuel occurrences leftSelected leftUndecided leftStep)
        (roundBroadcastFuel occurrences rightSelected rightUndecided rightStep)
        (roundBroadcastRequest occurrences leftSelected leftUndecided leftStep)
        (roundBroadcastRequest occurrences rightSelected rightUndecided
          rightStep)
        (conditionalTouchNumeratorInput occurrences leftSelected leftUndecided
          leftStep)
        (conditionalTouchNumeratorInput occurrences rightSelected
          rightUndecided rightStep)
        (run_roundBroadcast inputLength occurrences leftSelected leftUndecided
          leftStep)
        (run_roundBroadcast inputLength occurrences rightSelected
          rightUndecided rightStep))
      hbroadcastBits
  have hstageTwo :=
    run_bits_mono
      (run_pairedCallProgram conditionalTouchNumeratorProgram inputLength
        (conditionalTouchNumeratorBits inputLength occurrences leftSelected
          leftUndecided leftStep)
        (conditionalTouchNumeratorBits inputLength occurrences rightSelected
          rightUndecided rightStep)
        (conditionalTouchNumeratorFuel occurrences leftSelected leftUndecided
          leftStep)
        (conditionalTouchNumeratorFuel occurrences rightSelected rightUndecided
          rightStep)
        (conditionalTouchNumeratorInput occurrences leftSelected leftUndecided
          leftStep)
        (conditionalTouchNumeratorInput occurrences rightSelected
          rightUndecided rightStep)
        (conditionalTouchNumerator (occurrenceSupport occurrences) leftSelected
          leftUndecided leftStep)
        (conditionalTouchNumerator (occurrenceSupport occurrences)
          rightSelected rightUndecided rightStep)
        (run_conditionalTouchNumeratorProgram inputLength occurrences
          leftSelected leftUndecided leftStep
          (conditionalTouchNumeratorBits inputLength occurrences leftSelected
            leftUndecided leftStep)
          (le_refl _))
        (run_conditionalTouchNumeratorProgram inputLength occurrences
          rightSelected rightUndecided rightStep
          (conditionalTouchNumeratorBits inputLength occurrences rightSelected
            rightUndecided rightStep)
          (le_refl _)))
      hscoreBits
  exact run_linkPrograms hpositive hlength hstageOne hstageTwo

/-! ## §7 The round's straight-line stages -/

/-- Decode the round: at descending counter `counter + 1` the round's
coordinate is `q - (counter + 1)` and the remaining suffix has `counter`
coordinates.  The two exponents are handed to one paired dyadic exponential;
the coordinate and the suffix length are carried past it. -/
def roundDecodeProgram : NPOracleProgram :=
  [ .unpairRight 0 2 1
  , .unpairLeft 1 3 2
  , .unpairLeft 3 4 3
  , .subtract 4 2 5 4
  , .decrement 2 5
  , .pair 5 4 6 6
  , .pair 5 2 7 7
  , .pair 6 7 0 8
  , .halt 0
  ]

@[simp] theorem roundDecodeProgram_oracleFree :
    OracleFree roundDecodeProgram := by
  rfl

def roundDecodeOutput (q counter : ℕ) : ℕ :=
  Nat.pair (Nat.pair (q - (counter + 1)) q)
    (Nat.pair (q - (counter + 1)) counter)

def roundDecodeBits (q masksTree selectedMask stepCount counter : ℕ) : ℕ :=
  max
    (natBitLength
      (Nat.pair (sweepCode (Nat.pair q masksTree) selectedMask stepCount)
        (counter + 1)))
    (natBitLength (roundDecodeOutput q counter))

theorem run_roundDecodeProgram
    (q masksTree selectedMask stepCount counter maximumBits : ℕ)
    (hbits :
      roundDecodeBits q masksTree selectedMask stepCount counter ≤
        maximumBits) :
    runNPOracleProgram roundDecodeProgram maximumBits 9
        (initialNPOracleState
          (sweepCode (Nat.pair q masksTree) selectedMask stepCount)
          (Nat.pair (sweepCode (Nat.pair q masksTree) selectedMask stepCount)
            (counter + 1))) =
      some (roundDecodeOutput q counter) := by
  have hcarried :
      sweepCode (Nat.pair q masksTree) selectedMask stepCount =
        Nat.pair (Nat.pair q masksTree) (Nat.pair selectedMask stepCount) :=
    rfl
  have hshape :
      roundDecodeOutput q counter =
        Nat.pair (Nat.pair (q - (counter + 1)) q)
          (Nat.pair (q - (counter + 1)) counter) := rfl
  have hinputBits :
      natBitLength
          (Nat.pair (sweepCode (Nat.pair q masksTree) selectedMask stepCount)
            (counter + 1)) ≤
        maximumBits :=
    (Nat.le_max_left _ _).trans hbits
  have houtputBits :
      natBitLength (roundDecodeOutput q counter) ≤ maximumBits :=
    (Nat.le_max_right _ _).trans hbits
  rw [hshape] at houtputBits
  have hcarriedBits :
      natBitLength
          (Nat.pair (Nat.pair q masksTree) (Nat.pair selectedMask stepCount)) ≤
        maximumBits := by
    rw [← hcarried]
    exact bits_of_le (Nat.left_le_pair _ _) hinputBits
  have hcounterBits : natBitLength (counter + 1) ≤ maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) hinputBits
  have hcontextBits : natBitLength (Nat.pair q masksTree) ≤ maximumBits :=
    bits_of_le (Nat.left_le_pair _ _) hcarriedBits
  have hwidthBits : natBitLength q ≤ maximumBits :=
    bits_of_le (Nat.left_le_pair _ _) hcontextBits
  have hcoordinateBits : natBitLength (q - (counter + 1)) ≤ maximumBits :=
    bits_of_le (Nat.sub_le _ _) hwidthBits
  have hrestBits : natBitLength counter ≤ maximumBits :=
    bits_of_le (Nat.le_succ counter) hcounterBits
  have hexponentBits :
      natBitLength (Nat.pair (q - (counter + 1)) q) ≤ maximumBits :=
    bits_of_le (Nat.left_le_pair _ _) houtputBits
  have hsuffixBits :
      natBitLength (Nat.pair (q - (counter + 1)) counter) ≤ maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) houtputBits
  rw [show (9 : ℕ) = 0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 by omega]
  rw [run_unpairRight_instruction (value := counter + 1) (by rfl) rfl
    (by simp [initialNPOracleState]) hcounterBits]
  rw [run_unpairLeft_instruction (value := Nat.pair q masksTree) (by rfl) rfl
    (by
      simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump,
        sweepCode])
    hcontextBits]
  rw [run_unpairLeft_instruction (value := q) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hwidthBits]
  rw [run_subtract_instruction (value := q - (counter + 1)) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hcoordinateBits]
  rw [run_decrement_instruction (value := counter) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hrestBits]
  rw [run_pair_instruction (value := Nat.pair (q - (counter + 1)) q)
    (by rfl) rfl (by simp [NPOracleState.write, NPOracleState.jump])
    hexponentBits]
  rw [run_pair_instruction (value := Nat.pair (q - (counter + 1)) counter)
    (by rfl) rfl (by simp [NPOracleState.write, NPOracleState.jump])
    hsuffixBits]
  rw [run_pair_instruction (value := roundDecodeOutput q counter)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hshape])
    (by rw [hshape]; exact houtputBits)]
  exact run_halt_instruction (fuel := 0) (value := roundDecodeOutput q counter)
    (by rfl) rfl (by simp [NPOracleState.write, NPOracleState.jump])
    (by rw [hshape]; exact houtputBits)

/-- `Nat.pair guard (Nat.pair takeValue stayValue) ↦
if guard = 0 then stayValue else takeValue`: the machine's only data branch on
the sweep's round. -/
def guardedSelectProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .branchZero 2 4 3
  , .unpairLeft 3 0 5
  , .unpairRight 3 0 5
  , .halt 0
  ]

@[simp] theorem guardedSelectProgram_oracleFree :
    OracleFree guardedSelectProgram := by
  rfl

def guardedSelectBits (guard takeValue stayValue : ℕ) : ℕ :=
  natBitLength (Nat.pair guard (Nat.pair takeValue stayValue))

theorem run_guardedSelectProgram
    (inputLength guard takeValue stayValue maximumBits : ℕ)
    (hbits : guardedSelectBits guard takeValue stayValue ≤ maximumBits) :
    runNPOracleProgram guardedSelectProgram maximumBits 5
        (initialNPOracleState inputLength
          (Nat.pair guard (Nat.pair takeValue stayValue))) =
      some (if guard = 0 then stayValue else takeValue) := by
  have hinputBits :
      natBitLength (Nat.pair guard (Nat.pair takeValue stayValue)) ≤
        maximumBits := hbits
  have hguardBits : natBitLength guard ≤ maximumBits :=
    bits_of_le (Nat.left_le_pair _ _) hinputBits
  have hvaluesBits :
      natBitLength (Nat.pair takeValue stayValue) ≤ maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) hinputBits
  have htakeBits : natBitLength takeValue ≤ maximumBits :=
    bits_of_le (Nat.left_le_pair _ _) hvaluesBits
  have hstayBits : natBitLength stayValue ≤ maximumBits :=
    bits_of_le (Nat.right_le_pair _ _) hvaluesBits
  rw [show (5 : ℕ) = 0 + 1 + 1 + 1 + 1 + 1 by omega]
  rw [run_unpairLeft_instruction (value := guard) (by rfl) rfl
    (by simp [initialNPOracleState]) hguardBits]
  rw [run_unpairRight_instruction (value := Nat.pair takeValue stayValue)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hvaluesBits]
  rw [run_branchZero_instruction (by rfl) rfl]
  by_cases hguard : guard = 0
  · rw [show
      (((((initialNPOracleState inputLength
        (Nat.pair guard (Nat.pair takeValue stayValue))).write 2 guard).jump
          1).write 3 (Nat.pair takeValue stayValue)).jump 2).registers 2 =
        0 by
      simp [NPOracleState.write, NPOracleState.jump, hguard]]
    rw [if_pos rfl]
    rw [run_unpairRight_instruction (value := stayValue) (by rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) hstayBits]
    rw [if_pos hguard]
    exact run_halt_instruction (fuel := 0) (value := stayValue) (by rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) hstayBits
  · rw [show
      (((((initialNPOracleState inputLength
        (Nat.pair guard (Nat.pair takeValue stayValue))).write 2 guard).jump
          1).write 3 (Nat.pair takeValue stayValue)).jump 2).registers 2 =
        guard by
      simp [NPOracleState.write, NPOracleState.jump]]
    rw [if_neg hguard]
    rw [run_unpairLeft_instruction (value := takeValue) (by rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) htakeBits]
    rw [if_neg hguard]
    exact run_halt_instruction (fuel := 0) (value := takeValue) (by rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) htakeBits

/-- Read the round's two candidate selection masks and the remaining-coordinate
mask.  The carried mask's own bit at the round's coordinate is the guard that
decides between them. -/
def roundMaskProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 2 4 3
  , .unpairRight 2 5 4
  , .unpairLeft 3 6 5
  , .unpairRight 3 7 6
  , .unpairRight 1 8 7
  , .unpairLeft 8 9 8
  , .add 4 4 10 9
  , .subtract 5 10 10 10
  , .testBit 9 6 11 11
  , .add 9 4 12 12
  , .pair 9 12 13 13
  , .pair 11 13 13 14
  , .pair 10 7 14 15
  , .pair 13 14 0 16
  , .halt 0
  ]

@[simp] theorem roundMaskProgram_oracleFree :
    OracleFree roundMaskProgram := by
  rfl

def roundMaskOutput (q selectedMask d restLength : ℕ) : ℕ :=
  Nat.pair
    (Nat.pair (selectedMask.testBit d).toNat
      (Nat.pair selectedMask (selectedMask + 2 ^ d)))
    (Nat.pair (2 ^ q - (2 ^ d + 2 ^ d)) restLength)

def roundMaskBits
    (q masksTree selectedMask stepCount d restLength : ℕ) : ℕ :=
  max (natBitLength (sweepCode (Nat.pair q masksTree) selectedMask stepCount))
    (max
      (natBitLength
        (Nat.pair (Nat.pair (2 ^ d) (2 ^ q)) (Nat.pair d restLength)))
      (natBitLength (roundMaskOutput q selectedMask d restLength)))

set_option maxHeartbeats 800000 in
-- Sixteen straight-line instructions; every intermediate is a component of the
-- carried state, the request, or the output.
theorem run_roundMaskProgram
    (q masksTree selectedMask stepCount d restLength maximumBits : ℕ)
    (hcoordinate : d < q)
    (hbits :
      roundMaskBits q masksTree selectedMask stepCount d restLength ≤
        maximumBits) :
    runNPOracleProgram roundMaskProgram maximumBits 17
        (initialNPOracleState
          (sweepCode (Nat.pair q masksTree) selectedMask stepCount)
          (Nat.pair (Nat.pair (2 ^ d) (2 ^ q)) (Nat.pair d restLength))) =
      some (roundMaskOutput q selectedMask d restLength) := by
  have hcarried :
      sweepCode (Nat.pair q masksTree) selectedMask stepCount =
        Nat.pair (Nat.pair q masksTree) (Nat.pair selectedMask stepCount) :=
    rfl
  have hshape :
      roundMaskOutput q selectedMask d restLength =
        Nat.pair
          (Nat.pair (selectedMask.testBit d).toNat
            (Nat.pair selectedMask (selectedMask + 2 ^ d)))
          (Nat.pair (2 ^ q - (2 ^ d + 2 ^ d)) restLength) := rfl
  have hcarriedBits :
      natBitLength
          (Nat.pair (Nat.pair q masksTree) (Nat.pair selectedMask stepCount)) ≤
        maximumBits := by
    rw [← hcarried]
    exact (Nat.le_max_left _ _).trans hbits
  have hinputBits :
      natBitLength
          (Nat.pair (Nat.pair (2 ^ d) (2 ^ q)) (Nat.pair d restLength)) ≤
        maximumBits :=
    (Nat.le_max_left _ _).trans ((Nat.le_max_right _ _).trans hbits)
  have houtputBits :
      natBitLength (roundMaskOutput q selectedMask d restLength) ≤
        maximumBits :=
    (Nat.le_max_right _ _).trans ((Nat.le_max_right _ _).trans hbits)
  have houtputShapeBits := houtputBits
  rw [hshape] at houtputShapeBits
  have hpowerPairBits :=
    bits_of_le (Nat.left_le_pair _ _) hinputBits
  have hcoordinatePairBits :=
    bits_of_le (Nat.right_le_pair _ _) hinputBits
  have hpBits := bits_of_le (Nat.left_le_pair _ _) hpowerPairBits
  have hwidthPowerBits := bits_of_le (Nat.right_le_pair _ _) hpowerPairBits
  have hcoordinateBits :=
    bits_of_le (Nat.left_le_pair _ _) hcoordinatePairBits
  have hrestLengthBits :=
    bits_of_le (Nat.right_le_pair _ _) hcoordinatePairBits
  have hstayBits := bits_of_le (Nat.right_le_pair _ _) hcarriedBits
  have hselectedBits := bits_of_le (Nat.left_le_pair _ _) hstayBits
  have hguardPairBits := bits_of_le (Nat.left_le_pair _ _) houtputShapeBits
  have hmaskTailBits := bits_of_le (Nat.right_le_pair _ _) houtputShapeBits
  have hcandidatesBits := bits_of_le (Nat.right_le_pair _ _) hguardPairBits
  have hinsertedBits := bits_of_le (Nat.right_le_pair _ _) hcandidatesBits
  have hdouble : 2 ^ d + 2 ^ d ≤ 2 ^ q := by
    have hsucc : 2 ^ d + 2 ^ d = 2 ^ (d + 1) := by
      rw [pow_succ]
      ring
    rw [hsucc]
    exact Nat.pow_le_pow_right (by omega) (by omega)
  have hdoubleBits : natBitLength (2 ^ d + 2 ^ d) ≤ maximumBits :=
    bits_of_le hdouble hwidthPowerBits
  have hrestMaskBits :
      natBitLength (2 ^ q - (2 ^ d + 2 ^ d)) ≤ maximumBits :=
    bits_of_le (Nat.sub_le _ _) hwidthPowerBits
  have hguardBits :
      natBitLength (selectedMask.testBit d).toNat ≤ maximumBits := by
    refine bits_of_le ?_ hpBits
    have hone : (selectedMask.testBit d).toNat ≤ 1 := by
      cases selectedMask.testBit d <;> simp
    exact hone.trans Nat.one_le_two_pow
  rw [show (17 : ℕ) =
    0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 by
    omega]
  rw [run_unpairLeft_instruction (value := Nat.pair (2 ^ d) (2 ^ q))
    (by rfl) rfl (by simp [initialNPOracleState]) hpowerPairBits]
  rw [run_unpairRight_instruction (value := Nat.pair d restLength)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hcoordinatePairBits]
  rw [run_unpairLeft_instruction (value := 2 ^ d) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hpBits]
  rw [run_unpairRight_instruction (value := 2 ^ q) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hwidthPowerBits]
  rw [run_unpairLeft_instruction (value := d) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hcoordinateBits]
  rw [run_unpairRight_instruction (value := restLength) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hrestLengthBits]
  rw [run_unpairRight_instruction (value := Nat.pair selectedMask stepCount)
    (by rfl) rfl
    (by
      simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump,
        sweepCode])
    hstayBits]
  rw [run_unpairLeft_instruction (value := selectedMask) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hselectedBits]
  rw [run_add_instruction (value := 2 ^ d + 2 ^ d) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hdoubleBits]
  rw [run_subtract_instruction (value := 2 ^ q - (2 ^ d + 2 ^ d))
    (by rfl) rfl (by simp [NPOracleState.write, NPOracleState.jump])
    hrestMaskBits]
  rw [run_testBit_instruction (value := (selectedMask.testBit d).toNat)
    (by rfl) rfl (by simp [NPOracleState.write, NPOracleState.jump])
    hguardBits]
  rw [run_add_instruction (value := selectedMask + 2 ^ d) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hinsertedBits]
  rw [run_pair_instruction
    (value := Nat.pair selectedMask (selectedMask + 2 ^ d)) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hcandidatesBits]
  rw [run_pair_instruction
    (value :=
      Nat.pair (selectedMask.testBit d).toNat
        (Nat.pair selectedMask (selectedMask + 2 ^ d)))
    (by rfl) rfl (by simp [NPOracleState.write, NPOracleState.jump])
    hguardPairBits]
  rw [run_pair_instruction
    (value := Nat.pair (2 ^ q - (2 ^ d + 2 ^ d)) restLength) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hmaskTailBits]
  rw [run_pair_instruction
    (value := roundMaskOutput q selectedMask d restLength) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hshape]) houtputBits]
  exact run_halt_instruction (fuel := 0)
    (value := roundMaskOutput q selectedMask d restLength) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtputBits

/-- Assemble the round's two broadcast requests, the step comparison's shared
context, and the candidate carried state of a taken round. -/
def roundRequestProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .unpairLeft 1 6 5
  , .unpairRight 1 7 6
  , .unpairLeft 6 8 7
  , .unpairRight 6 9 8
  , .unpairLeft 7 10 9
  , .unpairRight 7 11 10
  , .copy 11 12 11
  , .decrement 12 12
  , .pair 2 4 13 13
  , .pair 8 12 14 14
  , .pair 13 14 13 15
  , .pair 13 9 13 16
  , .pair 10 4 14 17
  , .pair 8 11 15 18
  , .pair 14 15 14 19
  , .pair 14 9 14 20
  , .pair 13 14 13 21
  , .pair 5 11 14 22
  , .pair 13 14 13 23
  , .pair 2 12 14 24
  , .pair 13 14 0 25
  , .halt 0
  ]

@[simp] theorem roundRequestProgram_oracleFree :
    OracleFree roundRequestProgram := by
  rfl

def roundRequestOutput
    (q masksTree selectedMask stepCount insertedMask restMask restLength :
      ℕ) : ℕ :=
  Nat.pair
    (Nat.pair
      (Nat.pair
        (Nat.pair (censusShared insertedMask restMask q (stepCount - 1))
          masksTree)
        (Nat.pair (censusShared selectedMask restMask q stepCount) masksTree))
      (Nat.pair restLength stepCount))
    (Nat.pair insertedMask (stepCount - 1))

def roundRequestBits
    (q masksTree selectedMask stepCount insertedMask restMask restLength :
      ℕ) : ℕ :=
  max (natBitLength (sweepCode (Nat.pair q masksTree) selectedMask stepCount))
    (max (natBitLength (Nat.pair insertedMask (Nat.pair restMask restLength)))
      (natBitLength
        (roundRequestOutput q masksTree selectedMask stepCount insertedMask
          restMask restLength)))

set_option maxHeartbeats 1200000 in
-- Twenty-five straight-line instructions; every intermediate is a component of
-- the carried state, the request, or the output.
theorem run_roundRequestProgram
    (q masksTree selectedMask stepCount insertedMask restMask restLength
      maximumBits : ℕ)
    (hbits :
      roundRequestBits q masksTree selectedMask stepCount insertedMask restMask
          restLength ≤
        maximumBits) :
    runNPOracleProgram roundRequestProgram maximumBits 26
        (initialNPOracleState
          (sweepCode (Nat.pair q masksTree) selectedMask stepCount)
          (Nat.pair insertedMask (Nat.pair restMask restLength))) =
      some
        (roundRequestOutput q masksTree selectedMask stepCount insertedMask
          restMask restLength) := by
  have hcarried :
      sweepCode (Nat.pair q masksTree) selectedMask stepCount =
        Nat.pair (Nat.pair q masksTree) (Nat.pair selectedMask stepCount) :=
    rfl
  have hshape :
      roundRequestOutput q masksTree selectedMask stepCount insertedMask
          restMask restLength =
        Nat.pair
          (Nat.pair
            (Nat.pair
              (Nat.pair
                (Nat.pair (Nat.pair insertedMask restMask)
                  (Nat.pair q (stepCount - 1)))
                masksTree)
              (Nat.pair
                (Nat.pair (Nat.pair selectedMask restMask)
                  (Nat.pair q stepCount))
                masksTree))
            (Nat.pair restLength stepCount))
          (Nat.pair insertedMask (stepCount - 1)) := rfl
  have hcarriedBits :
      natBitLength
          (Nat.pair (Nat.pair q masksTree) (Nat.pair selectedMask stepCount)) ≤
        maximumBits := by
    rw [← hcarried]
    exact (Nat.le_max_left _ _).trans hbits
  have hinputBits :
      natBitLength (Nat.pair insertedMask (Nat.pair restMask restLength)) ≤
        maximumBits :=
    (Nat.le_max_left _ _).trans ((Nat.le_max_right _ _).trans hbits)
  have houtputBits :
      natBitLength
          (roundRequestOutput q masksTree selectedMask stepCount insertedMask
            restMask restLength) ≤
        maximumBits :=
    (Nat.le_max_right _ _).trans ((Nat.le_max_right _ _).trans hbits)
  have houtputShapeBits := houtputBits
  rw [hshape] at houtputShapeBits
  have hinsertedBits := bits_of_le (Nat.left_le_pair _ _) hinputBits
  have hmaskTailBits := bits_of_le (Nat.right_le_pair _ _) hinputBits
  have hrestMaskBits := bits_of_le (Nat.left_le_pair _ _) hmaskTailBits
  have hrestLengthBits := bits_of_le (Nat.right_le_pair _ _) hmaskTailBits
  have hcontextBits := bits_of_le (Nat.left_le_pair _ _) hcarriedBits
  have hstayBits := bits_of_le (Nat.right_le_pair _ _) hcarriedBits
  have hwidthBits := bits_of_le (Nat.left_le_pair _ _) hcontextBits
  have hmasksTreeBits := bits_of_le (Nat.right_le_pair _ _) hcontextBits
  have hselectedBits := bits_of_le (Nat.left_le_pair _ _) hstayBits
  have hstepBits := bits_of_le (Nat.right_le_pair _ _) hstayBits
  have hstepPredBits : natBitLength (stepCount - 1) ≤ maximumBits :=
    bits_of_le (Nat.sub_le _ _) hstepBits
  have hstepArgsBits := bits_of_le (Nat.left_le_pair _ _) houtputShapeBits
  have htakeCodeBits := bits_of_le (Nat.right_le_pair _ _) houtputShapeBits
  have hrequestPairBits := bits_of_le (Nat.left_le_pair _ _) hstepArgsBits
  have hsuffixBits := bits_of_le (Nat.right_le_pair _ _) hstepArgsBits
  have hfirstRequestBits :=
    bits_of_le (Nat.left_le_pair _ _) hrequestPairBits
  have hsecondRequestBits :=
    bits_of_le (Nat.right_le_pair _ _) hrequestPairBits
  have hfirstSharedBits :=
    bits_of_le (Nat.left_le_pair _ _) hfirstRequestBits
  have hsecondSharedBits :=
    bits_of_le (Nat.left_le_pair _ _) hsecondRequestBits
  have hfirstMasksBits := bits_of_le (Nat.left_le_pair _ _) hfirstSharedBits
  have hfirstWidthBits := bits_of_le (Nat.right_le_pair _ _) hfirstSharedBits
  have hsecondMasksBits := bits_of_le (Nat.left_le_pair _ _) hsecondSharedBits
  have hsecondWidthBits :=
    bits_of_le (Nat.right_le_pair _ _) hsecondSharedBits
  rw [show (26 : ℕ) =
    0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 +
      1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 by
    omega]
  rw [run_unpairLeft_instruction (value := insertedMask) (by rfl) rfl
    (by simp [initialNPOracleState]) hinsertedBits]
  rw [run_unpairRight_instruction (value := Nat.pair restMask restLength)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hmaskTailBits]
  rw [run_unpairLeft_instruction (value := restMask) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hrestMaskBits]
  rw [run_unpairRight_instruction (value := restLength) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hrestLengthBits]
  rw [run_unpairLeft_instruction (value := Nat.pair q masksTree) (by rfl) rfl
    (by
      simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump,
        sweepCode])
    hcontextBits]
  rw [run_unpairRight_instruction (value := Nat.pair selectedMask stepCount)
    (by rfl) rfl
    (by
      simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump,
        sweepCode])
    hstayBits]
  rw [run_unpairLeft_instruction (value := q) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hwidthBits]
  rw [run_unpairRight_instruction (value := masksTree) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hmasksTreeBits]
  rw [run_unpairLeft_instruction (value := selectedMask) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hselectedBits]
  rw [run_unpairRight_instruction (value := stepCount) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hstepBits]
  rw [run_copy_instruction (value := stepCount) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hstepBits]
  rw [run_decrement_instruction (value := stepCount - 1) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hstepPredBits]
  rw [run_pair_instruction (value := Nat.pair insertedMask restMask)
    (by rfl) rfl (by simp [NPOracleState.write, NPOracleState.jump])
    hfirstMasksBits]
  rw [run_pair_instruction (value := Nat.pair q (stepCount - 1))
    (by rfl) rfl (by simp [NPOracleState.write, NPOracleState.jump])
    hfirstWidthBits]
  rw [run_pair_instruction
    (value :=
      Nat.pair (Nat.pair insertedMask restMask) (Nat.pair q (stepCount - 1)))
    (by rfl) rfl (by simp [NPOracleState.write, NPOracleState.jump])
    hfirstSharedBits]
  rw [run_pair_instruction
    (value :=
      Nat.pair
        (Nat.pair (Nat.pair insertedMask restMask)
          (Nat.pair q (stepCount - 1)))
        masksTree)
    (by rfl) rfl (by simp [NPOracleState.write, NPOracleState.jump])
    hfirstRequestBits]
  rw [run_pair_instruction (value := Nat.pair selectedMask restMask)
    (by rfl) rfl (by simp [NPOracleState.write, NPOracleState.jump])
    hsecondMasksBits]
  rw [run_pair_instruction (value := Nat.pair q stepCount) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hsecondWidthBits]
  rw [run_pair_instruction
    (value :=
      Nat.pair (Nat.pair selectedMask restMask) (Nat.pair q stepCount))
    (by rfl) rfl (by simp [NPOracleState.write, NPOracleState.jump])
    hsecondSharedBits]
  rw [run_pair_instruction
    (value :=
      Nat.pair
        (Nat.pair (Nat.pair selectedMask restMask) (Nat.pair q stepCount))
        masksTree)
    (by rfl) rfl (by simp [NPOracleState.write, NPOracleState.jump])
    hsecondRequestBits]
  rw [run_pair_instruction
    (value :=
      Nat.pair
        (Nat.pair
          (Nat.pair (Nat.pair insertedMask restMask)
            (Nat.pair q (stepCount - 1)))
          masksTree)
        (Nat.pair
          (Nat.pair (Nat.pair selectedMask restMask) (Nat.pair q stepCount))
          masksTree))
    (by rfl) rfl (by simp [NPOracleState.write, NPOracleState.jump])
    hrequestPairBits]
  rw [run_pair_instruction (value := Nat.pair restLength stepCount)
    (by rfl) rfl (by simp [NPOracleState.write, NPOracleState.jump])
    hsuffixBits]
  rw [run_pair_instruction
    (value :=
      Nat.pair
        (Nat.pair
          (Nat.pair
            (Nat.pair (Nat.pair insertedMask restMask)
              (Nat.pair q (stepCount - 1)))
            masksTree)
          (Nat.pair
            (Nat.pair (Nat.pair selectedMask restMask) (Nat.pair q stepCount))
            masksTree))
        (Nat.pair restLength stepCount))
    (by rfl) rfl (by simp [NPOracleState.write, NPOracleState.jump])
    hstepArgsBits]
  rw [run_pair_instruction (value := Nat.pair insertedMask (stepCount - 1))
    (by rfl) rfl (by simp [NPOracleState.write, NPOracleState.jump])
    htakeCodeBits]
  rw [run_pair_instruction
    (value :=
      roundRequestOutput q masksTree selectedMask stepCount insertedMask
        restMask restLength)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hshape]) houtputBits]
  exact run_halt_instruction (fuel := 0)
    (value :=
      roundRequestOutput q masksTree selectedMask stepCount insertedMask
        restMask restLength)
    (by rfl) rfl (by simp [NPOracleState.write, NPOracleState.jump])
    houtputBits

/-- Frame the step comparison's answer for the first guarded select. -/
def roundSelectFrameProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 1 4 3
  , .pair 4 3 5 4
  , .pair 5 1 6 5
  , .pair 2 6 0 6
  , .halt 0
  ]

@[simp] theorem roundSelectFrameProgram_oracleFree :
    OracleFree roundSelectFrameProgram := by
  rfl

def roundSelectFrameOutput (context stayCode takeCode decision : ℕ) : ℕ :=
  Nat.pair decision
    (Nat.pair (Nat.pair context takeCode) (Nat.pair context stayCode))

def roundSelectFrameBits (context stayCode takeCode decision : ℕ) : ℕ :=
  max (natBitLength (Nat.pair context stayCode))
    (max (natBitLength (Nat.pair decision takeCode))
      (natBitLength (roundSelectFrameOutput context stayCode takeCode
        decision)))

theorem run_roundSelectFrameProgram
    (context stayCode takeCode decision maximumBits : ℕ)
    (hbits :
      roundSelectFrameBits context stayCode takeCode decision ≤ maximumBits) :
    runNPOracleProgram roundSelectFrameProgram maximumBits 7
        (initialNPOracleState (Nat.pair context stayCode)
          (Nat.pair decision takeCode)) =
      some (roundSelectFrameOutput context stayCode takeCode decision) := by
  have hshape :
      roundSelectFrameOutput context stayCode takeCode decision =
        Nat.pair decision
          (Nat.pair (Nat.pair context takeCode)
            (Nat.pair context stayCode)) := rfl
  have hcarriedBits :
      natBitLength (Nat.pair context stayCode) ≤ maximumBits :=
    (Nat.le_max_left _ _).trans hbits
  have hinputBits :
      natBitLength (Nat.pair decision takeCode) ≤ maximumBits :=
    (Nat.le_max_left _ _).trans ((Nat.le_max_right _ _).trans hbits)
  have houtputBits :
      natBitLength (roundSelectFrameOutput context stayCode takeCode
        decision) ≤ maximumBits :=
    (Nat.le_max_right _ _).trans ((Nat.le_max_right _ _).trans hbits)
  have houtputShapeBits := houtputBits
  rw [hshape] at houtputShapeBits
  have hdecisionBits := bits_of_le (Nat.left_le_pair _ _) hinputBits
  have htakeCodeBits := bits_of_le (Nat.right_le_pair _ _) hinputBits
  have hcontextBits := bits_of_le (Nat.left_le_pair _ _) hcarriedBits
  have hvaluesBits := bits_of_le (Nat.right_le_pair _ _) houtputShapeBits
  have htakeValueBits := bits_of_le (Nat.left_le_pair _ _) hvaluesBits
  rw [show (7 : ℕ) = 0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 by omega]
  rw [run_unpairLeft_instruction (value := decision) (by rfl) rfl
    (by simp [initialNPOracleState]) hdecisionBits]
  rw [run_unpairRight_instruction (value := takeCode) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    htakeCodeBits]
  rw [run_unpairLeft_instruction (value := context) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hcontextBits]
  rw [run_pair_instruction (value := Nat.pair context takeCode) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) htakeValueBits]
  rw [run_pair_instruction
    (value := Nat.pair (Nat.pair context takeCode) (Nat.pair context stayCode))
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hvaluesBits]
  rw [run_pair_instruction
    (value := roundSelectFrameOutput context stayCode takeCode decision)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hshape]) houtputBits]
  exact run_halt_instruction (fuel := 0)
    (value := roundSelectFrameOutput context stayCode takeCode decision)
    (by rfl) rfl (by simp [NPOracleState.write, NPOracleState.jump])
    houtputBits

/-- Frame the exhausted-budget guard for the second guarded select. -/
def roundGuardFrameProgram : NPOracleProgram :=
  [ .unpairRight 1 2 1
  , .unpairRight 2 3 2
  , .pair 0 1 4 3
  , .pair 3 4 0 4
  , .halt 0
  ]

@[simp] theorem roundGuardFrameProgram_oracleFree :
    OracleFree roundGuardFrameProgram := by
  rfl

def roundGuardFrameOutput
    (context selectedMask stepCount chosen : ℕ) : ℕ :=
  Nat.pair stepCount
    (Nat.pair chosen (Nat.pair context (Nat.pair selectedMask stepCount)))

def roundGuardFrameBits
    (context selectedMask stepCount chosen : ℕ) : ℕ :=
  max (natBitLength (Nat.pair context (Nat.pair selectedMask stepCount)))
    (max (natBitLength chosen)
      (natBitLength
        (roundGuardFrameOutput context selectedMask stepCount chosen)))

theorem run_roundGuardFrameProgram
    (context selectedMask stepCount chosen maximumBits : ℕ)
    (hbits :
      roundGuardFrameBits context selectedMask stepCount chosen ≤
        maximumBits) :
    runNPOracleProgram roundGuardFrameProgram maximumBits 5
        (initialNPOracleState
          (Nat.pair context (Nat.pair selectedMask stepCount)) chosen) =
      some (roundGuardFrameOutput context selectedMask stepCount chosen) := by
  have hshape :
      roundGuardFrameOutput context selectedMask stepCount chosen =
        Nat.pair stepCount
          (Nat.pair chosen
            (Nat.pair context (Nat.pair selectedMask stepCount))) := rfl
  have hcarriedBits :
      natBitLength (Nat.pair context (Nat.pair selectedMask stepCount)) ≤
        maximumBits :=
    (Nat.le_max_left _ _).trans hbits
  have houtputBits :
      natBitLength
          (roundGuardFrameOutput context selectedMask stepCount chosen) ≤
        maximumBits :=
    (Nat.le_max_right _ _).trans ((Nat.le_max_right _ _).trans hbits)
  have houtputShapeBits := houtputBits
  rw [hshape] at houtputShapeBits
  have hstayBits := bits_of_le (Nat.right_le_pair _ _) hcarriedBits
  have hstepBits := bits_of_le (Nat.right_le_pair _ _) hstayBits
  have hvaluesBits := bits_of_le (Nat.right_le_pair _ _) houtputShapeBits
  rw [show (5 : ℕ) = 0 + 1 + 1 + 1 + 1 + 1 by omega]
  rw [run_unpairRight_instruction
    (value := Nat.pair selectedMask stepCount) (by rfl) rfl
    (by simp [initialNPOracleState]) hstayBits]
  rw [run_unpairRight_instruction (value := stepCount) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hstepBits]
  rw [run_pair_instruction
    (value :=
      Nat.pair chosen (Nat.pair context (Nat.pair selectedMask stepCount)))
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hvaluesBits]
  rw [run_pair_instruction
    (value := roundGuardFrameOutput context selectedMask stepCount chosen)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hshape]) houtputBits]
  exact run_halt_instruction (fuel := 0)
    (value := roundGuardFrameOutput context selectedMask stepCount chosen)
    (by rfl) rfl (by simp [NPOracleState.write, NPOracleState.jump])
    houtputBits

/-- **The round's carried-state update.**  The comparison's answer chooses
between the two candidate states, and an exhausted step budget overrides it. -/
def roundSelectProgram : NPOracleProgram :=
  linkPrograms roundSelectFrameProgram
    (linkPrograms guardedSelectProgram
      (linkPrograms roundGuardFrameProgram guardedSelectProgram))

theorem roundSelectProgram_oracleFree : OracleFree roundSelectProgram :=
  oracleFree_linkPrograms roundSelectFrameProgram_oracleFree
    (oracleFree_linkPrograms guardedSelectProgram_oracleFree
      (oracleFree_linkPrograms roundGuardFrameProgram_oracleFree
        guardedSelectProgram_oracleFree))

def roundSelectFuel : ℕ :=
  linkFuel
    (linkPrograms guardedSelectProgram
      (linkPrograms roundGuardFrameProgram guardedSelectProgram)) 7
    (linkFuel (linkPrograms roundGuardFrameProgram guardedSelectProgram) 5
      (linkFuel guardedSelectProgram 5 5))

/-- The carried state a round produces once the comparison has answered but
before the step budget is consulted. -/
def roundSelectFirst
    (context selectedMask stepCount takeCode decision : ℕ) : ℕ :=
  if decision = 0 then
    Nat.pair context (Nat.pair selectedMask stepCount)
  else
    Nat.pair context takeCode

/-- The carried state a round produces. -/
def roundSelectOutput
    (context selectedMask stepCount takeCode decision : ℕ) : ℕ :=
  if stepCount = 0 then
    Nat.pair context (Nat.pair selectedMask stepCount)
  else
    roundSelectFirst context selectedMask stepCount takeCode decision

def roundSelectStageBits
    (context selectedMask stepCount takeCode decision : ℕ) : List ℕ :=
  [ 1
  , natBitLength (Nat.pair context (Nat.pair selectedMask stepCount))
  , roundSelectFrameBits context (Nat.pair selectedMask stepCount) takeCode
      decision
  , guardedSelectBits decision (Nat.pair context takeCode)
      (Nat.pair context (Nat.pair selectedMask stepCount))
  , roundGuardFrameBits context selectedMask stepCount
      (roundSelectFirst context selectedMask stepCount takeCode decision)
  , guardedSelectBits stepCount
      (roundSelectFirst context selectedMask stepCount takeCode decision)
      (Nat.pair context (Nat.pair selectedMask stepCount))
  ]

def roundSelectBits
    (context selectedMask stepCount takeCode decision : ℕ) : ℕ :=
  (roundSelectStageBits context selectedMask stepCount takeCode
    decision).foldr max 1

set_option maxHeartbeats 800000 in
-- Four linked stages: two framings and two shallow guarded selects.
theorem run_roundSelectProgram
    (context selectedMask stepCount takeCode decision maximumBits : ℕ)
    (hbits :
      roundSelectBits context selectedMask stepCount takeCode decision ≤
        maximumBits) :
    runNPOracleProgram roundSelectProgram maximumBits roundSelectFuel
        (initialNPOracleState
          (Nat.pair context (Nat.pair selectedMask stepCount))
          (Nat.pair decision takeCode)) =
      some
        (roundSelectOutput context selectedMask stepCount takeCode
          decision) := by
  have bits_of_member {value : ℕ}
      (hvalue :
        value ∈
          roundSelectStageBits context selectedMask stepCount takeCode
            decision) :
      value ≤ maximumBits :=
    le_trans (le_foldr_max_of_mem hvalue) hbits
  have hpositive : 1 ≤ maximumBits := by
    apply bits_of_member
    simp [roundSelectStageBits]
  have hlength :
      natBitLength (Nat.pair context (Nat.pair selectedMask stepCount)) ≤
        maximumBits := by
    apply bits_of_member
    simp [roundSelectStageBits]
  have hframeBits :
      roundSelectFrameBits context (Nat.pair selectedMask stepCount) takeCode
          decision ≤
        maximumBits := by
    apply bits_of_member
    simp [roundSelectStageBits]
  have hfirstGuardBits :
      guardedSelectBits decision (Nat.pair context takeCode)
          (Nat.pair context (Nat.pair selectedMask stepCount)) ≤
        maximumBits := by
    apply bits_of_member
    simp [roundSelectStageBits]
  have hguardFrameBits :
      roundGuardFrameBits context selectedMask stepCount
          (roundSelectFirst context selectedMask stepCount takeCode
            decision) ≤
        maximumBits := by
    apply bits_of_member
    simp [roundSelectStageBits]
  have hsecondGuardBits :
      guardedSelectBits stepCount
          (roundSelectFirst context selectedMask stepCount takeCode decision)
          (Nat.pair context (Nat.pair selectedMask stepCount)) ≤
        maximumBits := by
    apply bits_of_member
    simp [roundSelectStageBits]
  have hstageOne :=
    run_roundSelectFrameProgram context (Nat.pair selectedMask stepCount)
      takeCode decision maximumBits hframeBits
  have hstageTwo :
      runNPOracleProgram guardedSelectProgram maximumBits 5
          (initialNPOracleState
            (Nat.pair context (Nat.pair selectedMask stepCount))
            (roundSelectFrameOutput context (Nat.pair selectedMask stepCount)
              takeCode decision)) =
        some
          (roundSelectFirst context selectedMask stepCount takeCode
            decision) :=
    run_guardedSelectProgram
      (Nat.pair context (Nat.pair selectedMask stepCount)) decision
      (Nat.pair context takeCode)
      (Nat.pair context (Nat.pair selectedMask stepCount)) maximumBits
      hfirstGuardBits
  have hstageThree :=
    run_roundGuardFrameProgram context selectedMask stepCount
      (roundSelectFirst context selectedMask stepCount takeCode decision)
      maximumBits hguardFrameBits
  have hstageFour :
      runNPOracleProgram guardedSelectProgram maximumBits 5
          (initialNPOracleState
            (Nat.pair context (Nat.pair selectedMask stepCount))
            (roundGuardFrameOutput context selectedMask stepCount
              (roundSelectFirst context selectedMask stepCount takeCode
                decision))) =
        some
          (roundSelectOutput context selectedMask stepCount takeCode
            decision) :=
    run_guardedSelectProgram
      (Nat.pair context (Nat.pair selectedMask stepCount)) stepCount
      (roundSelectFirst context selectedMask stepCount takeCode decision)
      (Nat.pair context (Nat.pair selectedMask stepCount)) maximumBits
      hsecondGuardBits
  exact run_linkPrograms hpositive hlength hstageOne
    (run_linkPrograms hpositive hlength hstageTwo
      (run_linkPrograms hpositive hlength hstageThree hstageFour))

/-! ## §8 The round's greedy comparison -/

/-- The round's two numerators, in the sweep's own order. -/
def roundIncluded {q : ℕ} (occurrences : List (SupportedNormalizedGate q))
    (inserted rest : Finset (Fin q)) (stepCount : ℕ) : ℕ :=
  conditionalTouchNumerator (occurrenceSupport occurrences) inserted rest
    (stepCount - 1)

def roundExcluded {q : ℕ} (occurrences : List (SupportedNormalizedGate q))
    (selected rest : Finset (Fin q)) (stepCount : ℕ) : ℕ :=
  conditionalTouchNumerator (occurrenceSupport occurrences) selected rest
    stepCount

/-- The round's greedy answer: one if the coordinate is taken. -/
def roundDecision {q : ℕ} (occurrences : List (SupportedNormalizedGate q))
    (selected inserted rest : Finset (Fin q))
    (stepCount restLength : ℕ) : ℕ :=
  if
      roundIncluded occurrences inserted rest stepCount *
          Nat.choose restLength stepCount ≤
        roundExcluded occurrences selected rest stepCount *
          Nat.choose restLength (stepCount - 1) then
    1
  else
    0

/-- **The round's comparison stage.**  Both numerators under one preserved
context, then the exact cross-multiplied test. -/
def roundStepProgram : NPOracleProgram :=
  linkPrograms (preserveRightProgram numeratorPairProgram) touchingStepProgram

theorem roundStepProgram_oracleFree : OracleFree roundStepProgram :=
  oracleFree_linkPrograms
    (preserveRightProgram_oracleFree numeratorPairProgram
      numeratorPairProgram_oracleFree)
    touchingStepProgram_oracleFree

def roundStepFuel {q : ℕ} (occurrences : List (SupportedNormalizedGate q))
    (selected inserted rest : Finset (Fin q))
    (stepCount restLength : ℕ) : ℕ :=
  linkFuel touchingStepProgram
    (preserveRightFuel
      (numeratorPairFuel occurrences inserted rest selected rest
        (stepCount - 1) stepCount))
    (touchingStepFuel (roundIncluded occurrences inserted rest stepCount)
      (roundExcluded occurrences selected rest stepCount) restLength stepCount)

def roundStepStageBits {q : ℕ} (inputLength : ℕ)
    (occurrences : List (SupportedNormalizedGate q))
    (selected inserted rest : Finset (Fin q))
    (stepCount restLength : ℕ) : List ℕ :=
  [ 1
  , natBitLength inputLength
  , preserveRightBits
      (numeratorPairBits inputLength occurrences inserted rest selected rest
        (stepCount - 1) stepCount)
      (Nat.pair
        (roundBroadcastRequest occurrences inserted rest (stepCount - 1))
        (roundBroadcastRequest occurrences selected rest stepCount))
      (Nat.pair restLength stepCount)
      (Nat.pair (roundIncluded occurrences inserted rest stepCount)
        (roundExcluded occurrences selected rest stepCount))
  , touchingStepBits inputLength
      (roundIncluded occurrences inserted rest stepCount)
      (roundExcluded occurrences selected rest stepCount) restLength stepCount
  ]

def roundStepBits {q : ℕ} (inputLength : ℕ)
    (occurrences : List (SupportedNormalizedGate q))
    (selected inserted rest : Finset (Fin q))
    (stepCount restLength : ℕ) : ℕ :=
  (roundStepStageBits inputLength occurrences selected inserted rest stepCount
    restLength).foldr max 1

/-- **The round's comparison stage, executed.** -/
theorem run_roundStepProgram {q : ℕ} (inputLength : ℕ)
    (occurrences : List (SupportedNormalizedGate q))
    (selected inserted rest : Finset (Fin q))
    (stepCount restLength maximumBits : ℕ)
    (hbits :
      roundStepBits inputLength occurrences selected inserted rest stepCount
          restLength ≤
        maximumBits) :
    runNPOracleProgram roundStepProgram maximumBits
        (roundStepFuel occurrences selected inserted rest stepCount restLength)
        (initialNPOracleState inputLength
          (Nat.pair
            (Nat.pair
              (roundBroadcastRequest occurrences inserted rest (stepCount - 1))
              (roundBroadcastRequest occurrences selected rest stepCount))
            (Nat.pair restLength stepCount))) =
      some
        (roundDecision occurrences selected inserted rest stepCount
          restLength) := by
  have bits_of_member {value : ℕ}
      (hvalue :
        value ∈
          roundStepStageBits inputLength occurrences selected inserted rest
            stepCount restLength) :
      value ≤ maximumBits :=
    le_trans (le_foldr_max_of_mem hvalue) hbits
  have hpositive : 1 ≤ maximumBits := by
    apply bits_of_member
    simp [roundStepStageBits]
  have hlength : natBitLength inputLength ≤ maximumBits := by
    apply bits_of_member
    simp [roundStepStageBits]
  have hnumeratorBits :
      preserveRightBits
          (numeratorPairBits inputLength occurrences inserted rest selected
            rest (stepCount - 1) stepCount)
          (Nat.pair
            (roundBroadcastRequest occurrences inserted rest (stepCount - 1))
            (roundBroadcastRequest occurrences selected rest stepCount))
          (Nat.pair restLength stepCount)
          (Nat.pair (roundIncluded occurrences inserted rest stepCount)
            (roundExcluded occurrences selected rest stepCount)) ≤
        maximumBits := by
    apply bits_of_member
    simp [roundStepStageBits]
  have hcompareBits :
      touchingStepBits inputLength
          (roundIncluded occurrences inserted rest stepCount)
          (roundExcluded occurrences selected rest stepCount) restLength
          stepCount ≤
        maximumBits := by
    apply bits_of_member
    simp [roundStepStageBits]
  have hstageOne :=
    run_bits_mono
      (run_preserveRightProgram numeratorPairProgram inputLength
        (numeratorPairBits inputLength occurrences inserted rest selected rest
          (stepCount - 1) stepCount)
        (numeratorPairFuel occurrences inserted rest selected rest
          (stepCount - 1) stepCount)
        (Nat.pair
          (roundBroadcastRequest occurrences inserted rest (stepCount - 1))
          (roundBroadcastRequest occurrences selected rest stepCount))
        (Nat.pair restLength stepCount)
        (Nat.pair (roundIncluded occurrences inserted rest stepCount)
          (roundExcluded occurrences selected rest stepCount))
        (run_numeratorPairProgram inputLength occurrences inserted rest
          selected rest (stepCount - 1) stepCount
          (numeratorPairBits inputLength occurrences inserted rest selected
            rest (stepCount - 1) stepCount)
          (le_refl _)))
      hnumeratorBits
  have hstageTwo :=
    run_touchingStepProgram inputLength
      (roundIncluded occurrences inserted rest stepCount)
      (roundExcluded occurrences selected rest stepCount) restLength stepCount
      maximumBits hcompareBits
  exact run_linkPrograms hpositive hlength hstageOne hstageTwo

/-! ## §9 The round program -/

/-- The coordinate set a mask denotes. -/
def maskFinset (q mask : ℕ) : Finset (Fin q) :=
  Finset.univ.filter fun index : Fin q => mask.testBit index.val

theorem maskFinset_coordinateMask {q : ℕ} (values : Finset (Fin q)) :
    maskFinset q (coordinateMask values) = values := by
  ext index
  simp [maskFinset, testBit_coordinateMask]

/-- The round's remaining-coordinate set, as a function of the counter. -/
def roundRestSet (q restCounter : ℕ) : Finset (Fin q) :=
  ((List.finRange q).drop (q - restCounter)).toFinset

/-- The round's candidate selection after the coordinate is taken. -/
def roundInsertedSet {q : ℕ} (selected : Finset (Fin q))
    (coordinate : ℕ) : Finset (Fin q) :=
  maskFinset q (insertMask (coordinateMask selected) coordinate)

theorem roundInsertedSet_eq {q : ℕ} (selected : Finset (Fin q))
    (coordinate : Fin q) :
    roundInsertedSet selected coordinate.val =
      insert coordinate selected := by
  unfold roundInsertedSet
  rw [insertMask_coordinateMask, maskFinset_coordinateMask]

theorem roundInsertedSet_eq_of_lt {q : ℕ} (selected : Finset (Fin q))
    (coordinate : ℕ) (hcoordinate : coordinate < q) :
    roundInsertedSet selected coordinate =
      insert (⟨coordinate, hcoordinate⟩ : Fin q) selected :=
  roundInsertedSet_eq selected ⟨coordinate, hcoordinate⟩

theorem insertMask_coordinateMask_of_lt {q : ℕ} (values : Finset (Fin q))
    (coordinate : ℕ) (hcoordinate : coordinate < q) :
    insertMask (coordinateMask values) coordinate =
      coordinateMask (insert (⟨coordinate, hcoordinate⟩ : Fin q) values) :=
  insertMask_coordinateMask values ⟨coordinate, hcoordinate⟩

theorem sweepStateCode_pair {q : ℕ} (context : ℕ)
    (selected : Finset (Fin q)) (stepCount : ℕ) :
    sweepStateCode context (selected, stepCount) =
      sweepCode context (coordinateMask selected) stepCount := rfl

theorem roundBroadcastRequest_masks {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (selected undecided : Finset (Fin q)) (stepCount : ℕ) :
    roundBroadcastRequest occurrences selected undecided stepCount =
      Nat.pair
        (censusShared (coordinateMask selected) (coordinateMask undecided) q
          stepCount)
        (encodeBalancedList (occurrenceSupportMasks occurrences)) := rfl

private theorem guardedSelect_insertMask (selectedMask coordinate : ℕ) :
    (if (selectedMask.testBit coordinate).toNat = 0 then
        selectedMask + 2 ^ coordinate
      else
        selectedMask) =
      insertMask selectedMask coordinate := by
  unfold insertMask
  cases hbit : selectedMask.testBit coordinate <;> simp

private def roundTailFive : NPOracleProgram :=
  linkPrograms (preserveRightProgram roundStepProgram) roundSelectProgram

private def roundTailFour : NPOracleProgram :=
  linkPrograms roundRequestProgram roundTailFive

private def roundTailThree : NPOracleProgram :=
  linkPrograms (preserveRightProgram guardedSelectProgram) roundTailFour

private def roundTailTwo : NPOracleProgram :=
  linkPrograms roundMaskProgram roundTailThree

private def roundTailOne : NPOracleProgram :=
  linkPrograms (preserveRightProgram (pairedCallProgram binaryTwoPowProgram))
    roundTailTwo

/-- **The greedy sweep's round program.**  Decode the round, take the two
powers of two, update the selection mask, build both census request trees,
compare the two numerators, and install the new carried state. -/
def touchingSweepRoundProgram : NPOracleProgram :=
  linkPrograms roundDecodeProgram roundTailOne

theorem touchingSweepRoundProgram_oracleFree :
    OracleFree touchingSweepRoundProgram :=
  oracleFree_linkPrograms roundDecodeProgram_oracleFree
    (oracleFree_linkPrograms
      (preserveRightProgram_oracleFree (pairedCallProgram binaryTwoPowProgram)
        (pairedCallProgram_oracleFree binaryTwoPowProgram
          binaryTwoPowProgram_oracleFree))
      (oracleFree_linkPrograms roundMaskProgram_oracleFree
        (oracleFree_linkPrograms
          (preserveRightProgram_oracleFree guardedSelectProgram
            guardedSelectProgram_oracleFree)
          (oracleFree_linkPrograms roundRequestProgram_oracleFree
            (oracleFree_linkPrograms
              (preserveRightProgram_oracleFree roundStepProgram
                roundStepProgram_oracleFree)
              roundSelectProgram_oracleFree)))))

def touchingSweepRoundFuel {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (selected : Finset (Fin q))
    (stepCount coordinate restCounter : ℕ) : ℕ :=
  linkFuel roundTailOne 9
    (linkFuel roundTailTwo
      (preserveRightFuel
        (pairedCallFuel binaryTwoPowProgram (binaryTwoPowFuel coordinate)
          (binaryTwoPowFuel q)))
      (linkFuel roundTailThree 17
        (linkFuel roundTailFour (preserveRightFuel 5)
          (linkFuel roundTailFive 26
            (linkFuel roundSelectProgram
              (preserveRightFuel
                (roundStepFuel occurrences selected
                  (roundInsertedSet selected coordinate)
                  (roundRestSet q restCounter) stepCount restCounter))
              roundSelectFuel)))))

/-- The request the comparison stage consumes: both broadcast requests beside
the suffix length and the step budget. -/
def roundStepArguments {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (selectedMask stepCount insertedMask restMask restCounter : ℕ) : ℕ :=
  Nat.pair
    (Nat.pair
      (Nat.pair (censusShared insertedMask restMask q (stepCount - 1))
        (encodeBalancedList (occurrenceSupportMasks occurrences)))
      (Nat.pair (censusShared selectedMask restMask q stepCount)
        (encodeBalancedList (occurrenceSupportMasks occurrences))))
    (Nat.pair restCounter stepCount)

def touchingSweepRoundStageBits {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (selected : Finset (Fin q))
    (stepCount coordinate restCounter : ℕ) : List ℕ :=
  [ 1
  , natBitLength
      (sweepCode (touchingSweepContext occurrences q) (coordinateMask selected)
        stepCount)
  , roundDecodeBits q (encodeBalancedList (occurrenceSupportMasks occurrences))
      (coordinateMask selected) stepCount restCounter
  , preserveRightBits
      (pairedCallBits
        (sweepCode (touchingSweepContext occurrences q)
          (coordinateMask selected) stepCount)
        (binaryTwoPowBits coordinate) (binaryTwoPowBits q) coordinate q
        (2 ^ coordinate) (2 ^ q))
      (Nat.pair coordinate q) (Nat.pair coordinate restCounter)
      (Nat.pair (2 ^ coordinate) (2 ^ q))
  , roundMaskBits q (encodeBalancedList (occurrenceSupportMasks occurrences))
      (coordinateMask selected) stepCount coordinate restCounter
  , preserveRightBits
      (guardedSelectBits ((coordinateMask selected).testBit coordinate).toNat
        (coordinateMask selected)
        (coordinateMask selected + 2 ^ coordinate))
      (Nat.pair ((coordinateMask selected).testBit coordinate).toNat
        (Nat.pair (coordinateMask selected)
          (coordinateMask selected + 2 ^ coordinate)))
      (Nat.pair (2 ^ q - (2 ^ coordinate + 2 ^ coordinate)) restCounter)
      (insertMask (coordinateMask selected) coordinate)
  , roundRequestBits q
      (encodeBalancedList (occurrenceSupportMasks occurrences))
      (coordinateMask selected) stepCount
      (insertMask (coordinateMask selected) coordinate)
      (2 ^ q - (2 ^ coordinate + 2 ^ coordinate)) restCounter
  , preserveRightBits
      (roundStepBits
        (sweepCode (touchingSweepContext occurrences q)
          (coordinateMask selected) stepCount)
        occurrences selected (roundInsertedSet selected coordinate)
        (roundRestSet q restCounter) stepCount restCounter)
      (roundStepArguments occurrences (coordinateMask selected) stepCount
        (insertMask (coordinateMask selected) coordinate)
        (2 ^ q - (2 ^ coordinate + 2 ^ coordinate)) restCounter)
      (Nat.pair (insertMask (coordinateMask selected) coordinate)
        (stepCount - 1))
      (roundDecision occurrences selected
        (roundInsertedSet selected coordinate) (roundRestSet q restCounter)
        stepCount restCounter)
  , roundSelectBits (touchingSweepContext occurrences q)
      (coordinateMask selected) stepCount
      (Nat.pair (insertMask (coordinateMask selected) coordinate)
        (stepCount - 1))
      (roundDecision occurrences selected
        (roundInsertedSet selected coordinate) (roundRestSet q restCounter)
        stepCount restCounter)
  ]

def touchingSweepRoundBits {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (selected : Finset (Fin q))
    (stepCount coordinate restCounter : ℕ) : ℕ :=
  (touchingSweepRoundStageBits occurrences selected stepCount coordinate
    restCounter).foldr max 1

/-- The remaining-coordinate mask of the round at descending counter
`counter + 1`. -/
theorem coordinateMask_roundRestSet {q : ℕ} (counter : ℕ)
    (hcounter : counter + 1 ≤ q) :
    coordinateMask (roundRestSet q counter) =
      2 ^ q - (2 ^ (q - (counter + 1)) + 2 ^ (q - (counter + 1))) := by
  have hmask := coordinateMask_finRange_drop (q := q) counter (by omega)
  have hpower :
      2 ^ (q - counter) =
        2 ^ (q - (counter + 1)) + 2 ^ (q - (counter + 1)) := by
    rw [show q - counter = q - (counter + 1) + 1 by omega, pow_succ]
    ring
  unfold roundRestSet
  rw [hmask, hpower]

/-- **The round's carried-state answer is exactly `sweepRound`.** -/
theorem roundSelectOutput_sweepRound {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (selected : Finset (Fin q)) (stepCount counter : ℕ)
    (hcounter : counter + 1 ≤ q) :
    roundSelectOutput (touchingSweepContext occurrences q)
        (coordinateMask selected) stepCount
        (Nat.pair (insertMask (coordinateMask selected) (q - (counter + 1)))
          (stepCount - 1))
        (roundDecision occurrences selected
          (roundInsertedSet selected (q - (counter + 1)))
          (roundRestSet q counter) stepCount counter) =
      sweepStateCode (touchingSweepContext occurrences q)
        (sweepRound (occurrenceSupport occurrences)
          ((List.finRange q).drop (q - (counter + 1)))
          (selected, stepCount)) := by
  have hcoordinate : q - (counter + 1) < q := by omega
  have hshift : q - (counter + 1) + 1 = q - counter := by omega
  have hlist :
      (List.finRange q).drop (q - (counter + 1)) =
        (⟨q - (counter + 1), hcoordinate⟩ : Fin q) ::
          (List.finRange q).drop (q - counter) := by
    rw [finRange_drop_cons q (q - (counter + 1)) hcoordinate, hshift]
  have hinserted :
      roundInsertedSet selected (q - (counter + 1)) =
        insert (⟨q - (counter + 1), hcoordinate⟩ : Fin q) selected :=
    roundInsertedSet_eq_of_lt selected (q - (counter + 1)) hcoordinate
  have hinsertedMask :
      insertMask (coordinateMask selected) (q - (counter + 1)) =
        coordinateMask
          (insert (⟨q - (counter + 1), hcoordinate⟩ : Fin q) selected) :=
    insertMask_coordinateMask_of_lt selected (q - (counter + 1)) hcoordinate
  have hrest :
      roundRestSet q counter =
        ((List.finRange q).drop (q - counter)).toFinset := rfl
  have hlength :
      ((List.finRange q).drop (q - counter)).length = counter :=
    length_finRange_drop q counter (by omega)
  rw [hlist]
  unfold roundSelectOutput roundSelectFirst roundDecision roundIncluded
    roundExcluded
  rw [hinserted, hrest, hinsertedMask]
  by_cases hstep : stepCount = 0
  · rw [if_pos hstep]
    rw [show
      sweepRound (occurrenceSupport occurrences)
          ((⟨q - (counter + 1), hcoordinate⟩ : Fin q) ::
            (List.finRange q).drop (q - counter)) (selected, stepCount) =
        (selected, stepCount) by
      simp [sweepRound, hstep]]
    rfl
  · rw [if_neg hstep]
    by_cases hchoice :
        conditionalTouchNumerator (occurrenceSupport occurrences)
              (insert (⟨q - (counter + 1), hcoordinate⟩ : Fin q) selected)
              ((List.finRange q).drop (q - counter)).toFinset
              (stepCount - 1) *
            Nat.choose counter stepCount ≤
          conditionalTouchNumerator (occurrenceSupport occurrences) selected
              ((List.finRange q).drop (q - counter)).toFinset stepCount *
            Nat.choose counter (stepCount - 1)
    · rw [if_pos hchoice]
      rw [show
        sweepRound (occurrenceSupport occurrences)
            ((⟨q - (counter + 1), hcoordinate⟩ : Fin q) ::
              (List.finRange q).drop (q - counter)) (selected, stepCount) =
          (insert (⟨q - (counter + 1), hcoordinate⟩ : Fin q) selected,
            stepCount - 1) by
        simp [sweepRound, hstep, hlength, hchoice]]
      rw [if_neg (Nat.one_ne_zero)]
      rfl
    · rw [if_neg hchoice]
      rw [show
        sweepRound (occurrenceSupport occurrences)
            ((⟨q - (counter + 1), hcoordinate⟩ : Fin q) ::
              (List.finRange q).drop (q - counter)) (selected, stepCount) =
          (selected, stepCount) by
        simp [sweepRound, hstep, hlength, hchoice]]
      rw [if_pos rfl]
      rfl

set_option maxHeartbeats 2000000 in
-- Seven linked stages, each widened to the shared register bound first; only
-- the closed `…Bits` names appear in the premise.
/-- **One greedy round of the touching sweep, executed.**  This is
`CanonicalTouchingSweepProgram` §5's round obligation. -/
theorem run_touchingSweepRoundProgram {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (selected : Finset (Fin q)) (stepCount counter maximumBits : ℕ)
    (hcounter : counter + 1 ≤ q)
    (hbits :
      touchingSweepRoundBits occurrences selected stepCount
          (q - (counter + 1)) counter ≤
        maximumBits) :
    runNPOracleProgram touchingSweepRoundProgram maximumBits
        (touchingSweepRoundFuel occurrences selected stepCount
          (q - (counter + 1)) counter)
        (initialNPOracleState
          (sweepStateCode (touchingSweepContext occurrences q)
            (selected, stepCount))
          (Nat.pair
            (sweepStateCode (touchingSweepContext occurrences q)
              (selected, stepCount))
            (counter + 1))) =
      some
        (sweepStateCode (touchingSweepContext occurrences q)
          (sweepRound (occurrenceSupport occurrences)
            ((List.finRange q).drop (q - (counter + 1)))
            (selected, stepCount))) := by
  have hcoordinate : q - (counter + 1) < q := by omega
  have hinsertedMaskEq :
      coordinateMask (roundInsertedSet selected (q - (counter + 1))) =
        insertMask (coordinateMask selected) (q - (counter + 1)) := by
    rw [roundInsertedSet_eq_of_lt selected (q - (counter + 1)) hcoordinate,
      insertMask_coordinateMask_of_lt selected (q - (counter + 1)) hcoordinate]
  have hrestMaskEq :
      coordinateMask (roundRestSet q counter) =
        2 ^ q - (2 ^ (q - (counter + 1)) + 2 ^ (q - (counter + 1))) :=
    coordinateMask_roundRestSet counter hcounter
  have bits_of_member {value : ℕ}
      (hvalue :
        value ∈
          touchingSweepRoundStageBits occurrences selected stepCount
            (q - (counter + 1)) counter) :
      value ≤ maximumBits :=
    le_trans (le_foldr_max_of_mem hvalue) hbits
  have hpositive : 1 ≤ maximumBits := by
    apply bits_of_member
    simp [touchingSweepRoundStageBits]
  have hlength :
      natBitLength
          (sweepCode (touchingSweepContext occurrences q)
            (coordinateMask selected) stepCount) ≤
        maximumBits := by
    apply bits_of_member
    simp [touchingSweepRoundStageBits]
  have hdecodeBits :
      roundDecodeBits q
          (encodeBalancedList (occurrenceSupportMasks occurrences))
          (coordinateMask selected) stepCount counter ≤
        maximumBits := by
    apply bits_of_member
    simp [touchingSweepRoundStageBits]
  have htwoPowBits :
      preserveRightBits
          (pairedCallBits
            (sweepCode (touchingSweepContext occurrences q)
              (coordinateMask selected) stepCount)
            (binaryTwoPowBits (q - (counter + 1))) (binaryTwoPowBits q)
            (q - (counter + 1)) q (2 ^ (q - (counter + 1))) (2 ^ q))
          (Nat.pair (q - (counter + 1)) q)
          (Nat.pair (q - (counter + 1)) counter)
          (Nat.pair (2 ^ (q - (counter + 1))) (2 ^ q)) ≤
        maximumBits := by
    apply bits_of_member
    simp [touchingSweepRoundStageBits]
  have hmaskBits :
      roundMaskBits q
          (encodeBalancedList (occurrenceSupportMasks occurrences))
          (coordinateMask selected) stepCount (q - (counter + 1)) counter ≤
        maximumBits := by
    apply bits_of_member
    simp [touchingSweepRoundStageBits]
  have hguardBits :
      preserveRightBits
          (guardedSelectBits
            ((coordinateMask selected).testBit (q - (counter + 1))).toNat
            (coordinateMask selected)
            (coordinateMask selected + 2 ^ (q - (counter + 1))))
          (Nat.pair
            ((coordinateMask selected).testBit (q - (counter + 1))).toNat
            (Nat.pair (coordinateMask selected)
              (coordinateMask selected + 2 ^ (q - (counter + 1)))))
          (Nat.pair
            (2 ^ q - (2 ^ (q - (counter + 1)) + 2 ^ (q - (counter + 1))))
            counter)
          (insertMask (coordinateMask selected) (q - (counter + 1))) ≤
        maximumBits := by
    apply bits_of_member
    simp [touchingSweepRoundStageBits]
  have hrequestBits :
      roundRequestBits q
          (encodeBalancedList (occurrenceSupportMasks occurrences))
          (coordinateMask selected) stepCount
          (insertMask (coordinateMask selected) (q - (counter + 1)))
          (2 ^ q - (2 ^ (q - (counter + 1)) + 2 ^ (q - (counter + 1))))
          counter ≤
        maximumBits := by
    apply bits_of_member
    simp [touchingSweepRoundStageBits]
  have hstepPreserveBits :
      preserveRightBits
          (roundStepBits
            (sweepCode (touchingSweepContext occurrences q)
              (coordinateMask selected) stepCount)
            occurrences selected
            (roundInsertedSet selected (q - (counter + 1)))
            (roundRestSet q counter) stepCount counter)
          (roundStepArguments occurrences (coordinateMask selected) stepCount
            (insertMask (coordinateMask selected) (q - (counter + 1)))
            (2 ^ q - (2 ^ (q - (counter + 1)) + 2 ^ (q - (counter + 1))))
            counter)
          (Nat.pair (insertMask (coordinateMask selected) (q - (counter + 1)))
            (stepCount - 1))
          (roundDecision occurrences selected
            (roundInsertedSet selected (q - (counter + 1)))
            (roundRestSet q counter) stepCount counter) ≤
        maximumBits := by
    apply bits_of_member
    simp [touchingSweepRoundStageBits]
  have hselectBits :
      roundSelectBits (touchingSweepContext occurrences q)
          (coordinateMask selected) stepCount
          (Nat.pair (insertMask (coordinateMask selected) (q - (counter + 1)))
            (stepCount - 1))
          (roundDecision occurrences selected
            (roundInsertedSet selected (q - (counter + 1)))
            (roundRestSet q counter) stepCount counter) ≤
        maximumBits := by
    apply bits_of_member
    simp [touchingSweepRoundStageBits]
  have hstageOne :
      runNPOracleProgram roundDecodeProgram maximumBits 9
          (initialNPOracleState
            (sweepCode (touchingSweepContext occurrences q)
              (coordinateMask selected) stepCount)
            (Nat.pair
              (sweepCode (touchingSweepContext occurrences q)
                (coordinateMask selected) stepCount)
              (counter + 1))) =
        some
          (Nat.pair (Nat.pair (q - (counter + 1)) q)
            (Nat.pair (q - (counter + 1)) counter)) :=
    run_roundDecodeProgram q
      (encodeBalancedList (occurrenceSupportMasks occurrences))
      (coordinateMask selected) stepCount counter maximumBits hdecodeBits
  have hstageTwo :
      runNPOracleProgram
          (preserveRightProgram (pairedCallProgram binaryTwoPowProgram))
          maximumBits
          (preserveRightFuel
            (pairedCallFuel binaryTwoPowProgram
              (binaryTwoPowFuel (q - (counter + 1))) (binaryTwoPowFuel q)))
          (initialNPOracleState
            (sweepCode (touchingSweepContext occurrences q)
              (coordinateMask selected) stepCount)
            (Nat.pair (Nat.pair (q - (counter + 1)) q)
              (Nat.pair (q - (counter + 1)) counter))) =
        some
          (Nat.pair (Nat.pair (2 ^ (q - (counter + 1))) (2 ^ q))
            (Nat.pair (q - (counter + 1)) counter)) :=
    run_bits_mono
      (run_preserveRightProgram (pairedCallProgram binaryTwoPowProgram)
        (sweepCode (touchingSweepContext occurrences q)
          (coordinateMask selected) stepCount)
        (pairedCallBits
          (sweepCode (touchingSweepContext occurrences q)
            (coordinateMask selected) stepCount)
          (binaryTwoPowBits (q - (counter + 1))) (binaryTwoPowBits q)
          (q - (counter + 1)) q (2 ^ (q - (counter + 1))) (2 ^ q))
        (pairedCallFuel binaryTwoPowProgram
          (binaryTwoPowFuel (q - (counter + 1))) (binaryTwoPowFuel q))
        (Nat.pair (q - (counter + 1)) q)
        (Nat.pair (q - (counter + 1)) counter)
        (Nat.pair (2 ^ (q - (counter + 1))) (2 ^ q))
        (run_pairedCallProgram binaryTwoPowProgram
          (sweepCode (touchingSweepContext occurrences q)
            (coordinateMask selected) stepCount)
          (binaryTwoPowBits (q - (counter + 1))) (binaryTwoPowBits q)
          (binaryTwoPowFuel (q - (counter + 1))) (binaryTwoPowFuel q)
          (q - (counter + 1)) q (2 ^ (q - (counter + 1))) (2 ^ q)
          (run_binaryTwoPowProgram
            (sweepCode (touchingSweepContext occurrences q)
              (coordinateMask selected) stepCount) (q - (counter + 1))
            (binaryTwoPowBits (q - (counter + 1))) (le_refl _))
          (run_binaryTwoPowProgram
            (sweepCode (touchingSweepContext occurrences q)
              (coordinateMask selected) stepCount) q (binaryTwoPowBits q)
            (le_refl _))))
      htwoPowBits
  have hstageThree :
      runNPOracleProgram roundMaskProgram maximumBits 17
          (initialNPOracleState
            (sweepCode (touchingSweepContext occurrences q)
              (coordinateMask selected) stepCount)
            (Nat.pair (Nat.pair (2 ^ (q - (counter + 1))) (2 ^ q))
              (Nat.pair (q - (counter + 1)) counter))) =
        some
          (Nat.pair
            (Nat.pair
              ((coordinateMask selected).testBit (q - (counter + 1))).toNat
              (Nat.pair (coordinateMask selected)
                (coordinateMask selected + 2 ^ (q - (counter + 1)))))
            (Nat.pair
              (2 ^ q - (2 ^ (q - (counter + 1)) + 2 ^ (q - (counter + 1))))
              counter)) :=
    run_roundMaskProgram q
      (encodeBalancedList (occurrenceSupportMasks occurrences))
      (coordinateMask selected) stepCount (q - (counter + 1)) counter
      maximumBits hcoordinate hmaskBits
  have hguardRun :
      runNPOracleProgram guardedSelectProgram
          (guardedSelectBits
            ((coordinateMask selected).testBit (q - (counter + 1))).toNat
            (coordinateMask selected)
            (coordinateMask selected + 2 ^ (q - (counter + 1)))) 5
          (initialNPOracleState
            (sweepCode (touchingSweepContext occurrences q)
              (coordinateMask selected) stepCount)
            (Nat.pair
              ((coordinateMask selected).testBit (q - (counter + 1))).toNat
              (Nat.pair (coordinateMask selected)
                (coordinateMask selected + 2 ^ (q - (counter + 1)))))) =
        some (insertMask (coordinateMask selected) (q - (counter + 1))) := by
    have hrun :=
      run_guardedSelectProgram
        (sweepCode (touchingSweepContext occurrences q)
          (coordinateMask selected) stepCount)
        ((coordinateMask selected).testBit (q - (counter + 1))).toNat
        (coordinateMask selected)
        (coordinateMask selected + 2 ^ (q - (counter + 1)))
        (guardedSelectBits
          ((coordinateMask selected).testBit (q - (counter + 1))).toNat
          (coordinateMask selected)
          (coordinateMask selected + 2 ^ (q - (counter + 1)))) (le_refl _)
    rw [guardedSelect_insertMask] at hrun
    exact hrun
  have hstageFour :
      runNPOracleProgram (preserveRightProgram guardedSelectProgram)
          maximumBits (preserveRightFuel 5)
          (initialNPOracleState
            (sweepCode (touchingSweepContext occurrences q)
              (coordinateMask selected) stepCount)
            (Nat.pair
              (Nat.pair
                ((coordinateMask selected).testBit (q - (counter + 1))).toNat
                (Nat.pair (coordinateMask selected)
                  (coordinateMask selected + 2 ^ (q - (counter + 1)))))
              (Nat.pair
                (2 ^ q - (2 ^ (q - (counter + 1)) + 2 ^ (q - (counter + 1))))
                counter))) =
        some
          (Nat.pair (insertMask (coordinateMask selected) (q - (counter + 1)))
            (Nat.pair
              (2 ^ q - (2 ^ (q - (counter + 1)) + 2 ^ (q - (counter + 1))))
              counter)) :=
    run_bits_mono
      (run_preserveRightProgram guardedSelectProgram
        (sweepCode (touchingSweepContext occurrences q)
          (coordinateMask selected) stepCount)
        (guardedSelectBits
          ((coordinateMask selected).testBit (q - (counter + 1))).toNat
          (coordinateMask selected)
          (coordinateMask selected + 2 ^ (q - (counter + 1)))) 5
        (Nat.pair
          ((coordinateMask selected).testBit (q - (counter + 1))).toNat
          (Nat.pair (coordinateMask selected)
            (coordinateMask selected + 2 ^ (q - (counter + 1)))))
        (Nat.pair
          (2 ^ q - (2 ^ (q - (counter + 1)) + 2 ^ (q - (counter + 1))))
          counter)
        (insertMask (coordinateMask selected) (q - (counter + 1))) hguardRun)
      hguardBits
  have hstageFive :
      runNPOracleProgram roundRequestProgram maximumBits 26
          (initialNPOracleState
            (sweepCode (touchingSweepContext occurrences q)
              (coordinateMask selected) stepCount)
            (Nat.pair (insertMask (coordinateMask selected) (q - (counter + 1)))
              (Nat.pair
                (2 ^ q - (2 ^ (q - (counter + 1)) + 2 ^ (q - (counter + 1))))
                counter))) =
        some
          (Nat.pair
            (roundStepArguments occurrences (coordinateMask selected) stepCount
              (insertMask (coordinateMask selected) (q - (counter + 1)))
              (2 ^ q - (2 ^ (q - (counter + 1)) + 2 ^ (q - (counter + 1))))
              counter)
            (Nat.pair (insertMask (coordinateMask selected) (q - (counter + 1)))
              (stepCount - 1))) :=
    run_roundRequestProgram q
      (encodeBalancedList (occurrenceSupportMasks occurrences))
      (coordinateMask selected) stepCount
      (insertMask (coordinateMask selected) (q - (counter + 1)))
      (2 ^ q - (2 ^ (q - (counter + 1)) + 2 ^ (q - (counter + 1)))) counter
      maximumBits hrequestBits
  have hstepRun :
      runNPOracleProgram roundStepProgram
          (roundStepBits
            (sweepCode (touchingSweepContext occurrences q)
              (coordinateMask selected) stepCount)
            occurrences selected
            (roundInsertedSet selected (q - (counter + 1)))
            (roundRestSet q counter) stepCount counter)
          (roundStepFuel occurrences selected
            (roundInsertedSet selected (q - (counter + 1)))
            (roundRestSet q counter) stepCount counter)
          (initialNPOracleState
            (sweepCode (touchingSweepContext occurrences q)
              (coordinateMask selected) stepCount)
            (roundStepArguments occurrences (coordinateMask selected) stepCount
              (insertMask (coordinateMask selected) (q - (counter + 1)))
              (2 ^ q - (2 ^ (q - (counter + 1)) + 2 ^ (q - (counter + 1))))
              counter)) =
        some
          (roundDecision occurrences selected
            (roundInsertedSet selected (q - (counter + 1)))
            (roundRestSet q counter) stepCount counter) := by
    have hrun :=
      run_roundStepProgram
        (sweepCode (touchingSweepContext occurrences q)
          (coordinateMask selected) stepCount)
        occurrences selected (roundInsertedSet selected (q - (counter + 1)))
        (roundRestSet q counter) stepCount counter
        (roundStepBits
          (sweepCode (touchingSweepContext occurrences q)
            (coordinateMask selected) stepCount)
          occurrences selected (roundInsertedSet selected (q - (counter + 1)))
          (roundRestSet q counter) stepCount counter) (le_refl _)
    rw [roundBroadcastRequest_masks, roundBroadcastRequest_masks,
      hinsertedMaskEq, hrestMaskEq] at hrun
    exact hrun
  have hstageSix :
      runNPOracleProgram (preserveRightProgram roundStepProgram) maximumBits
          (preserveRightFuel
            (roundStepFuel occurrences selected
              (roundInsertedSet selected (q - (counter + 1)))
              (roundRestSet q counter) stepCount counter))
          (initialNPOracleState
            (sweepCode (touchingSweepContext occurrences q)
              (coordinateMask selected) stepCount)
            (Nat.pair
              (roundStepArguments occurrences (coordinateMask selected)
                stepCount
                (insertMask (coordinateMask selected) (q - (counter + 1)))
                (2 ^ q - (2 ^ (q - (counter + 1)) + 2 ^ (q - (counter + 1))))
                counter)
              (Nat.pair
                (insertMask (coordinateMask selected) (q - (counter + 1)))
                (stepCount - 1)))) =
        some
          (Nat.pair
            (roundDecision occurrences selected
              (roundInsertedSet selected (q - (counter + 1)))
              (roundRestSet q counter) stepCount counter)
            (Nat.pair
              (insertMask (coordinateMask selected) (q - (counter + 1)))
              (stepCount - 1))) :=
    run_bits_mono
      (run_preserveRightProgram roundStepProgram
        (sweepCode (touchingSweepContext occurrences q)
          (coordinateMask selected) stepCount)
        (roundStepBits
          (sweepCode (touchingSweepContext occurrences q)
            (coordinateMask selected) stepCount)
          occurrences selected (roundInsertedSet selected (q - (counter + 1)))
          (roundRestSet q counter) stepCount counter)
        (roundStepFuel occurrences selected
          (roundInsertedSet selected (q - (counter + 1)))
          (roundRestSet q counter) stepCount counter)
        (roundStepArguments occurrences (coordinateMask selected) stepCount
          (insertMask (coordinateMask selected) (q - (counter + 1)))
          (2 ^ q - (2 ^ (q - (counter + 1)) + 2 ^ (q - (counter + 1))))
          counter)
        (Nat.pair (insertMask (coordinateMask selected) (q - (counter + 1)))
          (stepCount - 1))
        (roundDecision occurrences selected
          (roundInsertedSet selected (q - (counter + 1)))
          (roundRestSet q counter) stepCount counter) hstepRun)
      hstepPreserveBits
  have hstageSeven :
      runNPOracleProgram roundSelectProgram maximumBits roundSelectFuel
          (initialNPOracleState
            (sweepCode (touchingSweepContext occurrences q)
              (coordinateMask selected) stepCount)
            (Nat.pair
              (roundDecision occurrences selected
                (roundInsertedSet selected (q - (counter + 1)))
                (roundRestSet q counter) stepCount counter)
              (Nat.pair
                (insertMask (coordinateMask selected) (q - (counter + 1)))
                (stepCount - 1)))) =
        some
          (roundSelectOutput (touchingSweepContext occurrences q)
            (coordinateMask selected) stepCount
            (Nat.pair
              (insertMask (coordinateMask selected) (q - (counter + 1)))
              (stepCount - 1))
            (roundDecision occurrences selected
              (roundInsertedSet selected (q - (counter + 1)))
              (roundRestSet q counter) stepCount counter)) :=
    run_roundSelectProgram (touchingSweepContext occurrences q)
      (coordinateMask selected) stepCount
      (Nat.pair (insertMask (coordinateMask selected) (q - (counter + 1)))
        (stepCount - 1))
      (roundDecision occurrences selected
        (roundInsertedSet selected (q - (counter + 1)))
        (roundRestSet q counter) stepCount counter) maximumBits hselectBits
  rw [← roundSelectOutput_sweepRound occurrences selected stepCount counter
    hcounter]
  exact run_linkPrograms hpositive hlength hstageOne
    (run_linkPrograms hpositive hlength hstageTwo
      (run_linkPrograms hpositive hlength hstageThree
        (run_linkPrograms hpositive hlength hstageFour
          (run_linkPrograms hpositive hlength hstageFive
            (run_linkPrograms hpositive hlength hstageSix hstageSeven)))))

/-! ## §10 The greedy sweep, executed -/

/-- The round controller's carried-state transition, as a total function of the
carried code and the descending counter. -/
def touchingSweepStep {q : ℕ} (occurrences : List (SupportedNormalizedGate q))
    (carried counter : ℕ) : ℕ :=
  sweepStateCode (touchingSweepContext occurrences q)
    (sweepRound (occurrenceSupport occurrences)
      ((List.finRange q).drop (q - counter))
      (maskFinset q (Nat.unpair (Nat.unpair carried).2).1,
        (Nat.unpair (Nat.unpair carried).2).2))

def touchingSweepCalleeFuel {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (carried counter : ℕ) : ℕ :=
  touchingSweepRoundFuel occurrences
    (maskFinset q (Nat.unpair (Nat.unpair carried).2).1)
    (Nat.unpair (Nat.unpair carried).2).2 (q - counter) (counter - 1)

private theorem sweepStateCode_fields {q : ℕ} (context : ℕ)
    (selected : Finset (Fin q)) (stepCount : ℕ) :
    (Nat.unpair (Nat.unpair (sweepStateCode context (selected, stepCount))).2).1
        = coordinateMask selected ∧
      (Nat.unpair
          (Nat.unpair (sweepStateCode context (selected, stepCount))).2).2 =
        stepCount := by
  constructor <;> simp [sweepStateCode, sweepCode]

theorem touchingSweepStep_sweepStateCode {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (selected : Finset (Fin q)) (stepCount counter : ℕ) :
    touchingSweepStep occurrences
        (sweepStateCode (touchingSweepContext occurrences q)
          (selected, stepCount)) counter =
      sweepStateCode (touchingSweepContext occurrences q)
        (sweepRound (occurrenceSupport occurrences)
          ((List.finRange q).drop (q - counter)) (selected, stepCount)) := by
  obtain ⟨hmask, hstep⟩ :=
    sweepStateCode_fields (touchingSweepContext occurrences q) selected
      stepCount
  unfold touchingSweepStep
  rw [hmask, hstep, maskFinset_coordinateMask]

theorem touchingSweepCalleeFuel_sweepStateCode {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (selected : Finset (Fin q)) (stepCount counter : ℕ) :
    touchingSweepCalleeFuel occurrences
        (sweepStateCode (touchingSweepContext occurrences q)
          (selected, stepCount)) (counter + 1) =
      touchingSweepRoundFuel occurrences selected stepCount
        (q - (counter + 1)) counter := by
  obtain ⟨hmask, hstep⟩ :=
    sweepStateCode_fields (touchingSweepContext occurrences q) selected
      stepCount
  unfold touchingSweepCalleeFuel
  rw [hmask, hstep, maskFinset_coordinateMask]
  simp

set_option maxHeartbeats 1200000 in
-- The round program discharges the counted controller's only interpreter
-- premise; the width premises stay stated on the sweep's reachable states.
/-- **The greedy touching sweep, executed.**  One fixed oracle-free program
returns the `coordinateMask` numeral of
`SupplierTouching.touchingSelect (occurrenceSupport occurrences) liveCount`. -/
theorem run_touchingSweepSelectProgram {q : ℕ}
    (occurrences : List (SupportedNormalizedGate q))
    (inputLength liveCount maximumBits : ℕ)
    (hpositive : 1 ≤ maximumBits)
    (hinputBits :
      natBitLength
          (roundCallInput q
            (sweepStateCode (touchingSweepContext occurrences q)
              ((∅ : Finset (Fin q)), liveCount))) ≤
        maximumBits)
    (hcarriedBits : ∀ carried counter,
      SweepReachable q (touchingSweepContext occurrences q) liveCount carried
        counter →
      natBitLength (Nat.pair carried counter) ≤ maximumBits)
    (hreturnBits : ∀ carried counter,
      SweepReachable q (touchingSweepContext occurrences q) liveCount carried
        (counter + 1) →
      natBitLength
          (Nat.pair (Nat.pair carried (counter + 1))
            (touchingSweepStep occurrences carried (counter + 1))) ≤
        maximumBits)
    (hroundBits : ∀ (selected : Finset (Fin q)) (stepCount counter : ℕ),
      counter + 1 ≤ q → stepCount ≤ liveCount →
      touchingSweepRoundBits occurrences selected stepCount
          (q - (counter + 1)) counter ≤
        maximumBits) :
    runNPOracleProgram (roundCallProgram touchingSweepRoundProgram) maximumBits
        (roundCallFuel touchingSweepRoundProgram
          (touchingSweepCalleeFuel occurrences)
          (touchingSweepStep occurrences)
          (sweepStateCode (touchingSweepContext occurrences q)
            ((∅ : Finset (Fin q)), liveCount)) q)
        (initialNPOracleState inputLength
          (roundCallInput q
            (sweepStateCode (touchingSweepContext occurrences q)
              ((∅ : Finset (Fin q)), liveCount)))) =
      some
        (sweepCode (touchingSweepContext occurrences q)
          (coordinateMask
            (touchingSelect (occurrenceSupport occurrences) liveCount))
          (sweepFold (occurrenceSupport occurrences) (List.finRange q)
            ((∅ : Finset (Fin q)), liveCount)).2) := by
  have hstep : ∀ (selected : Finset (Fin q)) (stepCount counter : ℕ),
      counter + 1 ≤ q →
      touchingSweepStep occurrences
          (sweepStateCode (touchingSweepContext occurrences q)
            (selected, stepCount)) (counter + 1) =
        sweepStateCode (touchingSweepContext occurrences q)
          (sweepRound (occurrenceSupport occurrences)
            ((List.finRange q).drop (q - (counter + 1)))
            (selected, stepCount)) := by
    intro selected stepCount counter _hcounter
    exact touchingSweepStep_sweepStateCode occurrences selected stepCount
      (counter + 1)
  have hexec : ∀ carried counter,
      SweepReachable q (touchingSweepContext occurrences q) liveCount carried
        (counter + 1) →
      runNPOracleProgram touchingSweepRoundProgram maximumBits
          (touchingSweepCalleeFuel occurrences carried (counter + 1))
          (initialNPOracleState carried (Nat.pair carried (counter + 1))) =
        some (touchingSweepStep occurrences carried (counter + 1)) := by
    intro carried counter hreachable
    obtain ⟨hcounter, selected, stepCount, hstepCount, hcarried⟩ := hreachable
    rw [hcarried]
    rw [touchingSweepCalleeFuel_sweepStateCode occurrences selected stepCount
      counter]
    rw [touchingSweepStep_sweepStateCode occurrences selected stepCount
      (counter + 1)]
    exact run_touchingSweepRoundProgram occurrences selected stepCount counter
      maximumBits hcounter (hroundBits selected stepCount counter hcounter
        hstepCount)
  exact run_touchingSweepProgram (occurrenceSupport occurrences)
    touchingSweepRoundProgram inputLength (touchingSweepContext occurrences q)
    liveCount maximumBits (touchingSweepCalleeFuel occurrences)
    (touchingSweepStep occurrences) hpositive hinputBits hcarriedBits
    hreturnBits hstep hexec

end NearCubicWires.CanonicalTouchingSweepRoundProgram
