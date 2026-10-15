import Proof.Circuits.CanonicalBalancedCall
import Proof.MachineModel.CanonicalNatDecodeProgram

namespace NearCubicWires.CanonicalNatDecodeFoldProgram

open NearCubicWires
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalNatDecodeProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock

/-! ## §1 The packed fold state -/

/-- One decoded bit, as an update of the packed fold register.  The left
component is the value decoded so far; the right component is one less than the
current place value, so the zero register denotes `(0, 1)`. -/
def natDecodeFoldStep (packed atom : ℕ) : ℕ :=
  Nat.pair
    (if atom = 0 then (Nat.unpair packed).1
      else (Nat.unpair packed).1 + ((Nat.unpair packed).2 + 1))
    ((Nat.unpair packed).2 + (Nat.unpair packed).2 + 1)

private theorem pred_double_place (stored : ℕ) :
    Nat.pred (stored + 1 + (stored + 1)) = stored + stored + 1 := by
  simp only [Nat.pred_eq_sub_one]
  omega

/-- **Exact little-endian semantics.**  The packed fold agrees with the fixed
decoder's arithmetic description on every list, at every starting state. -/
theorem foldl_natDecodeFoldStep (bits : List ℕ) (value stored : ℕ) :
    bits.foldl natDecodeFoldStep (Nat.pair value stored) =
      Nat.pair (taggedBitFoldValue bits value (stored + 1))
        ((stored + 1) * 2 ^ bits.length - 1) := by
  induction bits generalizing value stored with
  | nil =>
      simp only [List.foldl_nil, taggedBitFoldValue, List.length_nil, pow_zero]
      congr 1
      omega
  | cons atom bits inductionHypothesis =>
      simp only [List.foldl_cons, natDecodeFoldStep, Nat.unpair_pair,
        taggedBitFoldValue, List.length_cons]
      rw [inductionHypothesis]
      congr 2
      · omega
      · rw [show stored + stored + 1 + 1 = (stored + 1) * 2 by ring]
        rw [show (stored + 1) * 2 * 2 ^ bits.length =
            (stored + 1) * 2 ^ (bits.length + 1) by
          rw [pow_succ]
          ring]

private theorem pair_zero_zero : Nat.pair 0 0 = 0 := by
  simp [Nat.pair]

/-- The decoded value is the left projection of the fold's final register. -/
theorem unpair_foldl_natDecodeFoldStep (bits : List ℕ) :
    (Nat.unpair (bits.foldl natDecodeFoldStep 0)).1 =
      taggedBitFoldValue bits 0 1 := by
  have hfold := foldl_natDecodeFoldStep bits 0 0
  rw [pair_zero_zero] at hfold
  rw [hfold]
  simp

/-! ## §2 The fixed program -/

def canonicalNatDecodeFoldProgram : NPOracleProgram :=
  balancedTraversalController 34 43 ++
    [ .unpairLeft 9 4 35
    , .unpairRight 9 5 36
    , .increment 5 37
    , .branchZero 3 38 39
    , .branchZero 3 40 40
    , .add 4 5 4 40
    , .add 5 5 5 41
    , .decrement 5 42
    , .pair 4 5 9 balancedTraversalLeafReturnPc
    , .unpairLeft 9 0 44
    , .halt 0
    ]

@[simp] theorem canonicalNatDecodeFoldProgram_oracleFree :
    OracleFree canonicalNatDecodeFoldProgram := by
  rfl

theorem canonicalNatDecodeFoldProgram_controllerAt :
    BalancedTraversalControllerAt canonicalNatDecodeFoldProgram 34 43 := by
  intro pc instruction hlookup
  have hpc : pc < (balancedTraversalController 34 43).length :=
    (List.getElem?_eq_some_iff.mp hlookup).choose
  simp only [canonicalNatDecodeFoldProgram]
  rw [List.getElem?_append_left hpc]
  exact hlookup

/-! ### The leaf handler's width certificate -/

private def natDecodeFoldWidths (packed atom : ℕ) : List ℕ :=
  [ natBitLength packed
  , natBitLength (Nat.unpair packed).1
  , natBitLength (Nat.unpair packed).2
  , natBitLength ((Nat.unpair packed).2 + 1)
  , natBitLength ((Nat.unpair packed).1 + ((Nat.unpair packed).2 + 1))
  , natBitLength ((Nat.unpair packed).2 + 1 + ((Nat.unpair packed).2 + 1))
  , natBitLength (Nat.pred ((Nat.unpair packed).2 + 1 + ((Nat.unpair packed).2 + 1)))
  , natBitLength (natDecodeFoldStep packed atom)
  ]

/-- Every register width the leaf handler demands, at one visited atom. -/
def natDecodeFoldLeafRequiredBits (packed atom : ℕ) : ℕ :=
  (natDecodeFoldWidths packed atom).foldr max 0

/-- One decoded bit costs eight instructions on both branches. -/
def natDecodeFoldLeafBudget (_packed _atom : ℕ) : ℕ := 8

private theorem le_foldr_max_of_mem
    {value : ℕ} {values : List ℕ} (hmem : value ∈ values) :
    value ≤ values.foldr max 0 := by
  induction values with
  | nil => simp at hmem
  | cons head tail inductionHypothesis =>
      simp only [List.mem_cons] at hmem
      simp only [List.foldr]
      rcases hmem with rfl | hmem
      · exact Nat.le_max_left _ _
      · exact (inductionHypothesis hmem).trans (Nat.le_max_right _ _)

private theorem natDecodeFoldWidth_le
    {packed atom maximumBits width : ℕ}
    (hmem : width ∈ natDecodeFoldWidths packed atom)
    (hbits : natDecodeFoldLeafRequiredBits packed atom ≤ maximumBits) :
    width ≤ maximumBits :=
  (le_foldr_max_of_mem hmem).trans hbits

/-! ### The leaf handler's execution -/

private theorem run_natDecodeFoldTail
    {maximumBits : ℕ} (entry : NPOracleState) (decoded place : ℕ)
    (hpc : entry.pc = 40)
    (hdecoded : entry.registers 4 = decoded)
    (hplace : entry.registers 5 = place)
    (hdoubleBits : natBitLength (place + place) ≤ maximumBits)
    (hstoredBits : natBitLength (Nat.pred (place + place)) ≤ maximumBits)
    (hpackedBits :
      natBitLength (Nat.pair decoded (Nat.pred (place + place))) ≤ maximumBits) :
    ∃ finish,
      RunsToIn canonicalNatDecodeFoldProgram maximumBits 3 entry finish ∧
      finish.pc = balancedTraversalLeafReturnPc ∧
      finish.registers 9 = Nat.pair decoded (Nat.pred (place + place)) ∧
      ∀ register, register ≠ 5 → register ≠ 9 →
        finish.registers register = entry.registers register := by
  let state1 := (entry.write 5 (place + place)).jump 41
  let state2 := (state1.write 5 (Nat.pred (place + place))).jump 42
  let finish :=
    (state2.write 9 (Nat.pair decoded (Nat.pred (place + place)))).jump
      balancedTraversalLeafReturnPc
  have hruns :
      RunsToIn canonicalNatDecodeFoldProgram maximumBits 3 entry finish := by
    intro extra
    rw [show 3 + extra = (2 + extra) + 1 by omega]
    rw [run_add_instruction (fuel := 2 + extra) (value := place + place)
      (by rfl) hpc (by rw [hplace]) hdoubleBits]
    change
      runNPOracleProgram canonicalNatDecodeFoldProgram maximumBits
          (2 + extra) state1 =
        runNPOracleProgram canonicalNatDecodeFoldProgram maximumBits
          extra finish
    rw [show 2 + extra = (1 + extra) + 1 by omega]
    rw [run_decrement_instruction (fuel := 1 + extra)
      (value := Nat.pred (place + place)) (by rfl) rfl
      (by simp [state1, NPOracleState.write, NPOracleState.jump]) hstoredBits]
    change
      runNPOracleProgram canonicalNatDecodeFoldProgram maximumBits
          (1 + extra) state2 =
        runNPOracleProgram canonicalNatDecodeFoldProgram maximumBits
          extra finish
    rw [show 1 + extra = extra + 1 by omega]
    rw [run_pair_instruction (fuel := extra)
      (value := Nat.pair decoded (Nat.pred (place + place))) (by rfl) rfl
      (by
        simp [state2, state1, NPOracleState.write, NPOracleState.jump,
          hdecoded])
      hpackedBits]
  refine ⟨finish, hruns, rfl, ?_, ?_⟩
  · simp [finish, NPOracleState.write, NPOracleState.jump]
  · intro register hfive hnine
    simp [finish, state2, state1, NPOracleState.write, NPOracleState.jump,
      hfive, hnine]

private theorem run_natDecodeFoldLeaf
    {maximumBits : ℕ} (entry : NPOracleState) (atom : ℕ)
    (hpc : entry.pc = 34)
    (hatom : entry.registers 3 = atom)
    (hbits :
      natDecodeFoldLeafRequiredBits (entry.registers 9) atom ≤ maximumBits) :
    ∃ finish,
      RunsToIn canonicalNatDecodeFoldProgram maximumBits 8 entry finish ∧
      finish.pc = balancedTraversalLeafReturnPc ∧
      finish.registers 0 = entry.registers 0 ∧
      finish.registers 2 = entry.registers 2 ∧
      finish.registers 3 = atom ∧
      finish.registers 9 = natDecodeFoldStep (entry.registers 9) atom ∧
      SameTraversalContextFrom 10 entry finish := by
  set packed := entry.registers 9 with hpacked
  set value := (Nat.unpair packed).1 with hvalue
  set stored := (Nat.unpair packed).2 with hstored
  have hvalueBits : natBitLength value ≤ maximumBits :=
    natDecodeFoldWidth_le (by simp [natDecodeFoldWidths, hvalue]) hbits
  have hstoredBits : natBitLength stored ≤ maximumBits :=
    natDecodeFoldWidth_le (by simp [natDecodeFoldWidths, hstored]) hbits
  have hplaceBits : natBitLength (stored + 1) ≤ maximumBits :=
    natDecodeFoldWidth_le (by simp [natDecodeFoldWidths, hstored]) hbits
  have hsumBits : natBitLength (value + (stored + 1)) ≤ maximumBits :=
    natDecodeFoldWidth_le (by simp [natDecodeFoldWidths, hvalue, hstored]) hbits
  have hdoubleBits :
      natBitLength (stored + 1 + (stored + 1)) ≤ maximumBits :=
    natDecodeFoldWidth_le (by simp [natDecodeFoldWidths, hstored]) hbits
  have hnextStoredBits :
      natBitLength (Nat.pred (stored + 1 + (stored + 1))) ≤ maximumBits :=
    natDecodeFoldWidth_le (by simp [natDecodeFoldWidths, hstored]) hbits
  have hstepBits :
      natBitLength (natDecodeFoldStep packed atom) ≤ maximumBits :=
    natDecodeFoldWidth_le (by simp [natDecodeFoldWidths]) hbits
  let state1 := (entry.write 4 value).jump 35
  let state2 := (state1.write 5 stored).jump 36
  let state3 := (state2.write 5 (stored + 1)).jump 37
  have hprefix :
      RunsToIn canonicalNatDecodeFoldProgram maximumBits 3 entry state3 := by
    intro extra
    rw [show 3 + extra = (2 + extra) + 1 by omega]
    rw [run_unpairLeft_instruction (fuel := 2 + extra) (value := value)
      (by rfl) hpc rfl hvalueBits]
    change
      runNPOracleProgram canonicalNatDecodeFoldProgram maximumBits
          (2 + extra) state1 =
        runNPOracleProgram canonicalNatDecodeFoldProgram maximumBits
          extra state3
    rw [show 2 + extra = (1 + extra) + 1 by omega]
    rw [run_unpairRight_instruction (fuel := 1 + extra) (value := stored)
      (by rfl) rfl
      (by
        simp [state1, NPOracleState.write, NPOracleState.jump, hstored,
          hpacked])
      hstoredBits]
    change
      runNPOracleProgram canonicalNatDecodeFoldProgram maximumBits
          (1 + extra) state2 =
        runNPOracleProgram canonicalNatDecodeFoldProgram maximumBits
          extra state3
    rw [show 1 + extra = extra + 1 by omega]
    rw [run_increment_instruction (fuel := extra) (value := stored + 1)
      (by rfl) rfl
      (by simp [state2, state1, NPOracleState.write, NPOracleState.jump])
      hplaceBits]
  have hstate3Atom : state3.registers 3 = atom := by
    simp [state3, state2, state1, NPOracleState.write, NPOracleState.jump,
      hatom]
  have hstate3Place : state3.registers 5 = stored + 1 := by
    simp [state3, NPOracleState.write, NPOracleState.jump]
  have hstate3Value : state3.registers 4 = value := by
    simp [state3, state2, state1, NPOracleState.write, NPOracleState.jump]
  have hstate3Nine : state3.registers 9 = packed := by
    simp [state3, state2, state1, NPOracleState.write, NPOracleState.jump,
      hpacked]
  by_cases hzero : atom = 0
  · let state4 := state3.jump 38
    let state5 := state4.jump 40
    have hbranch :
        RunsToIn canonicalNatDecodeFoldProgram maximumBits 2 state3 state5 := by
      intro extra
      rw [show 2 + extra = (1 + extra) + 1 by omega]
      rw [run_branchZero_instruction (fuel := 1 + extra) (by rfl) rfl]
      rw [hstate3Atom, if_pos hzero]
      change
        runNPOracleProgram canonicalNatDecodeFoldProgram maximumBits
            (1 + extra) state4 =
          runNPOracleProgram canonicalNatDecodeFoldProgram maximumBits
            extra state5
      rw [show 1 + extra = extra + 1 by omega]
      rw [run_branchZero_instruction (fuel := extra) (by rfl) rfl]
      simp only [state5]
      congr 1
      simp [state4, NPOracleState.jump]
    rcases run_natDecodeFoldTail (maximumBits := maximumBits) state5 value
        (stored + 1) rfl
        (by simp [state5, state4, NPOracleState.jump, hstate3Value])
        (by simp [state5, state4, NPOracleState.jump, hstate3Place])
        hdoubleBits hnextStoredBits
        (by
          have hstep :
              natDecodeFoldStep packed atom =
                Nat.pair value (Nat.pred (stored + 1 + (stored + 1))) := by
            simp only [natDecodeFoldStep, ← hvalue, ← hstored, if_pos hzero,
              pred_double_place]
          rwa [hstep] at hstepBits) with
      ⟨finish, htailRuns, hfinishPc, hfinishNine, hfinishOther⟩
    refine ⟨finish, ?_, hfinishPc, ?_, ?_, ?_, ?_, ?_⟩
    · have hcombined := (hprefix.trans hbranch).trans htailRuns
      simpa using hcombined
    · rw [hfinishOther 0 (by omega) (by omega)]
      simp [state5, state4, state3, state2, state1, NPOracleState.write,
        NPOracleState.jump]
    · rw [hfinishOther 2 (by omega) (by omega)]
      simp [state5, state4, state3, state2, state1, NPOracleState.write,
        NPOracleState.jump]
    · rw [hfinishOther 3 (by omega) (by omega)]
      simp [state5, state4, NPOracleState.jump, hstate3Atom]
    · rw [hfinishNine]
      simp only [natDecodeFoldStep, ← hvalue, ← hstored, if_pos hzero,
        pred_double_place]
    · refine ⟨?_, ?_⟩
      · rw [hfinishOther 1 (by omega) (by omega)]
        simp [state5, state4, state3, state2, state1, NPOracleState.write,
          NPOracleState.jump]
      · intro register hregister
        rw [hfinishOther register (by omega) (by omega)]
        simp [state5, state4, state3, state2, state1, NPOracleState.write,
          NPOracleState.jump, show register ≠ 4 by omega,
          show register ≠ 5 by omega]
  · let state4 := state3.jump 39
    let state5 := (state4.write 4 (value + (stored + 1))).jump 40
    have hbranch :
        RunsToIn canonicalNatDecodeFoldProgram maximumBits 2 state3 state5 := by
      intro extra
      rw [show 2 + extra = (1 + extra) + 1 by omega]
      rw [run_branchZero_instruction (fuel := 1 + extra) (by rfl) rfl]
      rw [hstate3Atom, if_neg hzero]
      change
        runNPOracleProgram canonicalNatDecodeFoldProgram maximumBits
            (1 + extra) state4 =
          runNPOracleProgram canonicalNatDecodeFoldProgram maximumBits
            extra state5
      rw [show 1 + extra = extra + 1 by omega]
      rw [run_add_instruction (fuel := extra) (value := value + (stored + 1))
        (by rfl) rfl
        (by
          simp only [state4, NPOracleState.jump]
          rw [hstate3Value, hstate3Place])
        hsumBits]
    rcases run_natDecodeFoldTail (maximumBits := maximumBits) state5
        (value + (stored + 1)) (stored + 1) rfl
        (by simp [state5, NPOracleState.write, NPOracleState.jump])
        (by
          simp [state5, state4, NPOracleState.write, NPOracleState.jump,
            hstate3Place])
        hdoubleBits hnextStoredBits
        (by
          have hstep :
              natDecodeFoldStep packed atom =
                Nat.pair (value + (stored + 1))
                  (Nat.pred (stored + 1 + (stored + 1))) := by
            simp only [natDecodeFoldStep, ← hvalue, ← hstored, if_neg hzero,
              pred_double_place]
          rwa [hstep] at hstepBits) with
      ⟨finish, htailRuns, hfinishPc, hfinishNine, hfinishOther⟩
    refine ⟨finish, ?_, hfinishPc, ?_, ?_, ?_, ?_, ?_⟩
    · have hcombined := (hprefix.trans hbranch).trans htailRuns
      simpa using hcombined
    · rw [hfinishOther 0 (by omega) (by omega)]
      simp [state5, state4, state3, state2, state1, NPOracleState.write,
        NPOracleState.jump]
    · rw [hfinishOther 2 (by omega) (by omega)]
      simp [state5, state4, state3, state2, state1, NPOracleState.write,
        NPOracleState.jump]
    · rw [hfinishOther 3 (by omega) (by omega)]
      simp [state5, state4, NPOracleState.write, NPOracleState.jump,
        hstate3Atom]
    · rw [hfinishNine]
      simp only [natDecodeFoldStep, ← hvalue, ← hstored, if_neg hzero,
        pred_double_place]
    · refine ⟨?_, ?_⟩
      · rw [hfinishOther 1 (by omega) (by omega)]
        simp [state5, state4, state3, state2, state1, NPOracleState.write,
          NPOracleState.jump]
      · intro register hregister
        rw [hfinishOther register (by omega) (by omega)]
        simp [state5, state4, state3, state2, state1, NPOracleState.write,
          NPOracleState.jump, show register ≠ 4 by omega,
          show register ≠ 5 by omega]

/-! ## §3 The public decoder, and its polynomial charge -/

private theorem balancedFoldLeafSteps_natDecodeFold
    (bits : List ℕ) (packed : ℕ) :
    balancedFoldLeafSteps natDecodeFoldStep natDecodeFoldLeafBudget
        packed bits =
      8 * bits.length := by
  induction bits generalizing packed with
  | nil => simp [balancedFoldLeafSteps]
  | cons atom bits inductionHypothesis =>
      simp only [balancedFoldLeafSteps, natDecodeFoldLeafBudget,
        List.length_cons]
      rw [inductionHypothesis]
      ring

/-- Fuel: the structural traversal, eight instructions per decoded bit, the
controller's final empty-stack branch and the two-instruction epilogue. -/
def canonicalNatDecodeFoldListFuel (bits : List ℕ) : ℕ :=
  balancedTraversalStructuralSteps (balancedTraversalTree bits) +
    8 * bits.length + 3

/-- Every register width the fold materializes, along its own accumulator
trace.  Unlike `taggedBitFoldBits` this never mentions `encodeTaggedList`: the
tagged intermediate no longer exists. -/
private def natDecodeFoldTraceBits : ℕ → List ℕ → ℕ
  | packed, [] => natBitLength packed
  | packed, atom :: atoms =>
      max (natDecodeFoldLeafRequiredBits packed atom)
        (natDecodeFoldTraceBits (natDecodeFoldStep packed atom) atoms)

/-- The repaired decode charge: one balanced-traversal charge on the
structural side and one fold trace on the arithmetic side. -/
def canonicalNatDecodeFoldListBits (inputLength : ℕ) (bits : List ℕ) : ℕ :=
  max 1 <| max (natBitLength inputLength) <|
    max
      (balancedTraversalRequiredBits (fun value => value)
        (balancedTraversalTree bits) [])
      (natDecodeFoldTraceBits 0 bits)

private theorem natDecodeFoldTraceFits
    (maximumBits packed : ℕ) (bits : List ℕ)
    (htrace : natDecodeFoldTraceBits packed bits ≤ maximumBits) :
    BalancedFoldFits maximumBits natDecodeFoldStep packed bits ∧
      BalancedFoldLeafFits maximumBits natDecodeFoldStep
        natDecodeFoldLeafRequiredBits packed bits := by
  induction bits generalizing packed with
  | nil =>
      simpa [natDecodeFoldTraceBits, BalancedFoldFits, BalancedFoldLeafFits]
        using htrace
  | cons atom bits inductionHypothesis =>
      have hrequired :
          natDecodeFoldLeafRequiredBits packed atom ≤ maximumBits :=
        (Nat.le_max_left _ _).trans htrace
      have htail :
          natDecodeFoldTraceBits (natDecodeFoldStep packed atom) bits ≤
            maximumBits :=
        (Nat.le_max_right _ _).trans htrace
      have hpackedBits : natBitLength packed ≤ maximumBits :=
        natDecodeFoldWidth_le (by simp [natDecodeFoldWidths]) hrequired
      have hstepBits :
          natBitLength (natDecodeFoldStep packed atom) ≤ maximumBits :=
        natDecodeFoldWidth_le (by simp [natDecodeFoldWidths]) hrequired
      rcases inductionHypothesis (natDecodeFoldStep packed atom) htail with
        ⟨hfoldTail, hleafTail⟩
      exact
        ⟨by
          simp only [BalancedFoldFits]
          exact ⟨hpackedBits, hstepBits, hfoldTail⟩,
        by
          simp only [BalancedFoldLeafFits]
          exact ⟨hrequired, hleafTail⟩⟩

/-- **Exact execution of the repaired decoder.**  The output contract is the
one `CanonicalNatDecodeProgram` publishes — the same arithmetic value at the
same input — but the run crosses no tagged intermediate. -/
theorem run_canonicalNatDecodeFoldProgram_fromList
    (inputLength : ℕ) (bits : List ℕ) :
    runNPOracleProgram canonicalNatDecodeFoldProgram
        (canonicalNatDecodeFoldListBits inputLength bits)
        (canonicalNatDecodeFoldListFuel bits)
        (initialNPOracleState inputLength (encodeBalancedList bits)) =
      some (taggedBitFoldValue bits 0 1) := by
  let maximumBits := canonicalNatDecodeFoldListBits inputLength bits
  let initial := initialNPOracleState inputLength (encodeBalancedList bits)
  have hnine : initial.registers 9 = 0 := by
    simp [initial, initialNPOracleState]
  have hrequired :
      balancedTraversalRequiredBits (fun value => value)
          (balancedTraversalTree bits) [] ≤ maximumBits :=
    (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hfit :
      BalancedTraversalFits maximumBits (fun value => value)
        (balancedTraversalTree bits) [] :=
    (balancedTraversalRequiredBits_le_iff maximumBits (fun value => value)
      (balancedTraversalTree bits) []).mp hrequired
  have htrace : natDecodeFoldTraceBits 0 bits ≤ maximumBits :=
    (Nat.le_max_right _ _).trans <|
      (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  rcases natDecodeFoldTraceFits maximumBits 0 bits htrace with
    ⟨hfoldFit, hleafFit⟩
  have houtputBits :
      natBitLength (taggedBitFoldValue bits 0 1) ≤ maximumBits := by
    rw [← unpair_foldl_natDecodeFoldStep bits]
    exact (natBitLength_mono (Nat.unpair_left_le _)).trans hfoldFit.final
  have hwithin :=
    run_balancedTraversalFoldWithin natDecodeFoldStep natDecodeFoldLeafBudget
      natDecodeFoldLeafRequiredBits bits initial inputLength 10 (le_refl 10)
      canonicalNatDecodeFoldProgram_controllerAt
      (by simp [initial, initialNPOracleState])
      (by simp [initial, initialNPOracleState])
      (by simp [initial, initialNPOracleState])
      (by simp [initial, initialNPOracleState])
      hfit
      (by rw [hnine]; exact hfoldFit)
      (by rw [hnine]; exact hleafFit)
      (by
        intro atom _hmem entry hentryPc _hcurrent hatom _hinputLength
          _haccumulator _hresult hleafRequired
        rcases run_natDecodeFoldLeaf (maximumBits := maximumBits) entry atom
            hentryPc hatom hleafRequired with
          ⟨finish, hruns, hfinishPc, hzero, htwo, hthree, hnineValue,
            hcontext⟩
        refine hruns.toRunsWithin.mono ?_
        intro candidate hcandidate
        subst candidate
        exact ⟨hfinishPc, hzero, htwo, hthree, hnineValue, hcontext⟩)
  rw [hnine] at hwithin
  rw [balancedFoldLeafSteps_natDecodeFold bits 0] at hwithin
  change
    runNPOracleProgram canonicalNatDecodeFoldProgram maximumBits
        (canonicalNatDecodeFoldListFuel bits) initial =
      some (taggedBitFoldValue bits 0 1)
  rw [show canonicalNatDecodeFoldListFuel bits =
      (balancedTraversalStructuralSteps (balancedTraversalTree bits) +
        8 * bits.length + 1) + 2 by
    simp [canonicalNatDecodeFoldListFuel]]
  apply hwithin 2 (taggedBitFoldValue bits 0 1)
  intro finish unused hfinish
  rw [show unused + 2 = (unused + 1) + 1 by omega]
  rw [run_unpairLeft_instruction (fuel := unused + 1)
    (value := taggedBitFoldValue bits 0 1) (by rfl) hfinish.1
    (by
      rw [hfinish.2.2.2.1]
      exact unpair_foldl_natDecodeFoldStep bits)
    houtputBits]
  exact run_halt_instruction (fuel := unused) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtputBits

def canonicalNatDecodeFoldFuel (value : ℕ) : ℕ :=
  canonicalNatDecodeFoldListFuel (canonicalNatDecodeRawBits value)

def canonicalNatDecodeFoldBits (inputLength value : ℕ) : ℕ :=
  canonicalNatDecodeFoldListBits inputLength (canonicalNatDecodeRawBits value)

/-- **The repaired decoder is a drop-in inverse of `encodeNat`.**  Same input
convention, same returned natural, same `initialNPOracleState` entry — so the
stage can be linked exactly where `canonicalNatDecodeProgram` was. -/
theorem run_canonicalNatDecodeFoldProgram (inputLength value : ℕ) :
    runNPOracleProgram canonicalNatDecodeFoldProgram
        (canonicalNatDecodeFoldBits inputLength value)
        (canonicalNatDecodeFoldFuel value)
        (initialNPOracleState inputLength (encodeNat value)) =
      some value := by
  let rawBits := canonicalNatDecodeRawBits value
  have hrun := run_canonicalNatDecodeFoldProgram_fromList inputLength rawBits
  have hvalue : taggedBitFoldValue rawBits 0 1 = value := by
    change taggedBitFoldValue (value.bits.map Bool.toNat) 0 1 = value
    exact (taggedBitFoldValue_boolBits value.bits).trans
      (bitsValue_natBits value)
  rw [hvalue] at hrun
  simpa [rawBits, canonicalNatDecodeRawBits, canonicalNatDecodeFoldBits,
    canonicalNatDecodeFoldFuel, encodeNat, encodeBits, encodeBoolList,
    boolCode] using hrun

theorem canonicalNatDecodeFoldFuel_positive (value : ℕ) :
    0 < canonicalNatDecodeFoldFuel value := by
  unfold canonicalNatDecodeFoldFuel canonicalNatDecodeFoldListFuel
  omega

theorem canonicalNatDecodeFold_inputLength_bits (inputLength value : ℕ) :
    natBitLength inputLength ≤ canonicalNatDecodeFoldBits inputLength value := by
  unfold canonicalNatDecodeFoldBits canonicalNatDecodeFoldListBits
  exact (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)

/-- **The fuel is linear in the decoded bit count.**  The controller's
structural charge is linear, and one decoded bit costs eight instructions
regardless of magnitude. -/
theorem canonicalNatDecodeFoldListFuel_le (bits : List ℕ) :
    canonicalNatDecodeFoldListFuel bits ≤ 78 * bits.length + 38 := by
  have hstructural := balancedTraversalStructuralSteps_le_linear bits
  unfold canonicalNatDecodeFoldListFuel
  omega

/-! ### The charge is polynomial -/

private theorem natBitLength_two_pow (exponent : ℕ) :
    natBitLength (2 ^ exponent) = exponent + 1 := by
  unfold natBitLength
  rw [Nat.log_pow (by omega)]

private theorem natBitLength_le_of_le_two_pow
    {value exponent : ℕ} (hvalue : value ≤ 2 ^ exponent) :
    natBitLength value ≤ exponent + 1 := by
  rw [← natBitLength_two_pow exponent]
  exact natBitLength_mono hvalue

private theorem natBitLength_packed_le {packed bound : ℕ}
    (hleft : natBitLength (Nat.unpair packed).1 ≤ bound)
    (hright : natBitLength (Nat.unpair packed).2 ≤ bound) :
    natBitLength packed ≤ 2 * bound := by
  have hpair :=
    pairCodeBits_le (Nat.unpair packed).1 (Nat.unpair packed).2
  rw [Nat.pair_unpair] at hpair
  have hmax :
      max (natBitLength (Nat.unpair packed).1)
        (natBitLength (Nat.unpair packed).2) ≤ bound :=
    max_le hleft hright
  omega

private theorem natDecodeFoldLeafRequiredBits_le
    {packed atom index bound : ℕ}
    (hplace : (Nat.unpair packed).2 + 1 = 2 ^ index)
    (hvalue : (Nat.unpair packed).1 < 2 ^ index)
    (hindex : index + 1 ≤ bound) :
    natDecodeFoldLeafRequiredBits packed atom ≤ 2 * (bound + 1) := by
  have hpow : (2 : ℕ) ^ (index + 1) ≤ 2 ^ bound :=
    Nat.pow_le_pow_right (by omega) hindex
  have hdouble : (2 : ℕ) ^ (index + 1) = 2 ^ index + 2 ^ index := by
    rw [pow_succ]
    ring
  have hleftBits : natBitLength (Nat.unpair packed).1 ≤ bound + 1 :=
    natBitLength_le_of_le_two_pow (by omega)
  have hrightBits : natBitLength (Nat.unpair packed).2 ≤ bound + 1 :=
    natBitLength_le_of_le_two_pow (by omega)
  have hpackedBits : natBitLength packed ≤ 2 * (bound + 1) :=
    natBitLength_packed_le hleftBits hrightBits
  have hplaceBits :
      natBitLength ((Nat.unpair packed).2 + 1) ≤ bound + 1 :=
    natBitLength_le_of_le_two_pow (by omega)
  have hsumBits :
      natBitLength ((Nat.unpair packed).1 + ((Nat.unpair packed).2 + 1)) ≤
        bound + 1 :=
    natBitLength_le_of_le_two_pow (by omega)
  have hdoubleBits :
      natBitLength ((Nat.unpair packed).2 + 1 + ((Nat.unpair packed).2 + 1)) ≤
        bound + 1 :=
    natBitLength_le_of_le_two_pow (by omega)
  have hpredBits :
      natBitLength
          (Nat.pred
            ((Nat.unpair packed).2 + 1 + ((Nat.unpair packed).2 + 1))) ≤
        bound + 1 := by
    apply natBitLength_le_of_le_two_pow (exponent := bound)
    simp only [Nat.pred_eq_sub_one]
    omega
  have hstepBits :
      natBitLength (natDecodeFoldStep packed atom) ≤ 2 * (bound + 1) := by
    apply natBitLength_packed_le (bound := bound + 1)
    · simp only [natDecodeFoldStep, Nat.unpair_pair]
      split
      · exact hleftBits
      · exact hsumBits
    · simp only [natDecodeFoldStep, Nat.unpair_pair]
      exact natBitLength_le_of_le_two_pow (by omega)
  simp only [natDecodeFoldLeafRequiredBits, natDecodeFoldWidths,
    List.foldr_cons, List.foldr_nil]
  exact max_le hpackedBits (max_le (by omega) (max_le (by omega)
    (max_le (by omega) (max_le (by omega) (max_le (by omega)
      (max_le (by omega) (max_le hstepBits (Nat.zero_le _))))))))

private theorem natDecodeFoldTraceBits_le_aux :
    ∀ (bits : List ℕ) (packed index bound : ℕ),
      (Nat.unpair packed).2 + 1 = 2 ^ index →
      (Nat.unpair packed).1 < 2 ^ index →
      index + bits.length ≤ bound →
      natDecodeFoldTraceBits packed bits ≤ 2 * (bound + 1) := by
  intro bits
  induction bits with
  | nil =>
      intro packed index bound hplace hvalue hindex
      simp only [List.length_nil, Nat.add_zero] at hindex
      have hpow : (2 : ℕ) ^ index ≤ 2 ^ bound :=
        Nat.pow_le_pow_right (by omega) hindex
      have hleftBits : natBitLength (Nat.unpair packed).1 ≤ bound + 1 :=
        natBitLength_le_of_le_two_pow (by omega)
      have hrightBits : natBitLength (Nat.unpair packed).2 ≤ bound + 1 :=
        natBitLength_le_of_le_two_pow (by omega)
      simpa [natDecodeFoldTraceBits] using
        natBitLength_packed_le hleftBits hrightBits
  | cons atom rest inductionHypothesis =>
      intro packed index bound hplace hvalue hindex
      simp only [List.length_cons] at hindex
      have hpow : (2 : ℕ) ^ (index + 1) = 2 ^ index + 2 ^ index := by
        rw [pow_succ]
        ring
      have hleaf :=
        natDecodeFoldLeafRequiredBits_le (packed := packed) (atom := atom)
          (bound := bound) hplace hvalue (by omega)
      have hnextPlace :
          (Nat.unpair (natDecodeFoldStep packed atom)).2 + 1 =
            2 ^ (index + 1) := by
        simp only [natDecodeFoldStep, Nat.unpair_pair]
        omega
      have hnextValue :
          (Nat.unpair (natDecodeFoldStep packed atom)).1 < 2 ^ (index + 1) := by
        simp only [natDecodeFoldStep, Nat.unpair_pair]
        split <;> omega
      have htail :=
        inductionHypothesis (natDecodeFoldStep packed atom) (index + 1) bound
          hnextPlace hnextValue (by omega)
      simp only [natDecodeFoldTraceBits]
      exact max_le hleaf htail

private theorem unpair_zero : Nat.unpair 0 = (0, 0) := by
  have hpair : Nat.unpair (Nat.pair 0 0) = (0, 0) := Nat.unpair_pair 0 0
  rwa [pair_zero_zero] at hpair

/-- **The fold trace is linear.**  Every value the decoding fold materializes
is below `2 ^ bits.length`, and the packed register holds two of them. -/
private theorem natDecodeFoldTraceBits_zero_le (bits : List ℕ) :
    natDecodeFoldTraceBits 0 bits ≤ 2 * (bits.length + 1) := by
  apply natDecodeFoldTraceBits_le_aux bits 0 0 bits.length
  · simp
  · simp
  · omega

theorem canonicalNatDecodeFoldListBits_le (inputLength : ℕ) (bits : List ℕ) :
    canonicalNatDecodeFoldListBits inputLength bits ≤
      max (natBitLength inputLength)
        (max
          (balancedTraversalRequiredBits (fun value => value)
            (balancedTraversalTree bits) [])
          (2 * (bits.length + 1))) := by
  have hone : 1 ≤ natBitLength inputLength := by
    unfold natBitLength
    omega
  have htrace := natDecodeFoldTraceBits_zero_le bits
  simp only [canonicalNatDecodeFoldListBits]
  omega

/-- **The repaired charge is polynomial.**  `CanonicalBalancedCall` closes the
traversal charge by one fixed polynomial in the atom count and the total atom
width; the fold trace is linear.  Nothing here is geometric in the number of
public bits. -/
theorem canonicalNatDecodeFoldListBits_le_polynomial
    (inputLength : ℕ) (bits : List ℕ) :
    canonicalNatDecodeFoldListBits inputLength bits ≤
      max (natBitLength inputLength)
        (max (balancedCallPolynomialBits (fun value => value) bits)
          (2 * (bits.length + 1))) := by
  have hstage := canonicalNatDecodeFoldListBits_le inputLength bits
  have htraversal :=
    (balancedCallRequiredBits_traversal (fun value => value) bits).trans
      (balancedCallRequiredBits_le_polynomial (fun value => value) bits)
  omega

end NearCubicWires.CanonicalNatDecodeFoldProgram
