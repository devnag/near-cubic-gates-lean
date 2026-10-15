import Proof.Circuits.CanonicalBalancedTraversal
import Proof.Circuits.RegisterBounds

namespace NearCubicWires.GeneratedBalancedRangeProgram

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.RegisterBounds

/-- Request atom emitted for one public range index. -/
def balancedRangeRequestAtom
    (inputLength index context : ℕ) : ℕ :=
  Nat.pair inputLength (Nat.pair index context)

/-- Consecutive request atoms, stated recursively so midpoint splitting has a
small proof interface.  `balancedRangeRequestAtoms_eq_map_range` exposes the
usual `List.range` view to callers. -/
def balancedRangeRequestAtoms
    (inputLength context first : ℕ) : ℕ → List ℕ
  | 0 => []
  | count + 1 =>
      balancedRangeRequestAtom inputLength first context ::
        balancedRangeRequestAtoms inputLength context (first + 1) count

@[simp] theorem balancedRangeRequestAtoms_zero
    (inputLength context first : ℕ) :
    balancedRangeRequestAtoms inputLength context first 0 = [] := rfl

@[simp] theorem balancedRangeRequestAtoms_succ
    (inputLength context first count : ℕ) :
    balancedRangeRequestAtoms inputLength context first (count + 1) =
      balancedRangeRequestAtom inputLength first context ::
        balancedRangeRequestAtoms inputLength context (first + 1) count := rfl

@[simp] theorem balancedRangeRequestAtoms_length
    (inputLength context first count : ℕ) :
    (balancedRangeRequestAtoms inputLength context first count).length =
      count := by
  induction count generalizing first with
  | zero => rfl
  | succ count ih =>
      simp [balancedRangeRequestAtoms, ih]

theorem balancedRangeRequestAtoms_append
    (inputLength context first left right : ℕ) :
    balancedRangeRequestAtoms inputLength context first (left + right) =
      balancedRangeRequestAtoms inputLength context first left ++
        balancedRangeRequestAtoms inputLength context (first + left) right := by
  induction left generalizing first with
  | zero =>
      simp [balancedRangeRequestAtoms]
  | succ left ih =>
      simp only [Nat.succ_add, balancedRangeRequestAtoms_succ,
        List.cons_append]
      rw [ih]
      apply congrArg
        (fun tail =>
          balancedRangeRequestAtom inputLength first context :: tail)
      apply congrArg₂ (fun x y : List ℕ => x ++ y) rfl
      exact congrArg
        (fun start =>
          balancedRangeRequestAtoms inputLength context start right) (by
            omega)

theorem balancedRangeRequestAtoms_eq_map_range
    (inputLength context first count : ℕ) :
    balancedRangeRequestAtoms inputLength context first count =
      (List.range count).map fun offset =>
        balancedRangeRequestAtom inputLength (first + offset) context := by
  induction count generalizing first with
  | zero => rfl
  | succ count ih =>
      simp [List.range_succ_eq_map, ih, Function.comp_def,
        Nat.add_comm, Nat.add_left_comm]

/-- Proof view of the exact midpoint tree built by the machine. -/
def generatedBalancedRangeTree
    (inputLength context first : ℕ) :
    (count : ℕ) → BalancedTraversalTree
  | 0 => .empty
  | 1 => .leaf (balancedRangeRequestAtom inputLength first context)
  | count + 2 =>
      let total := count + 2
      let leftCount := (total + 1) / 2
      let rightCount := total / 2
      .branch
        (generatedBalancedRangeTree inputLength context first leftCount)
        (generatedBalancedRangeTree inputLength context
          (first + leftCount) rightCount)
termination_by count => count
decreasing_by
  all_goals
    simp_wf
    omega

@[simp] theorem generatedBalancedRangeTree_zero
    (inputLength context first : ℕ) :
    generatedBalancedRangeTree inputLength context first 0 = .empty := by
  rw [generatedBalancedRangeTree]

@[simp] theorem generatedBalancedRangeTree_one
    (inputLength context first : ℕ) :
    generatedBalancedRangeTree inputLength context first 1 =
      .leaf (balancedRangeRequestAtom inputLength first context) := by
  rw [generatedBalancedRangeTree]

/-- Canonical tree shape and range order agree at the public codec boundary. -/
theorem generatedBalancedRangeTree_atoms
    (inputLength context first count : ℕ) :
    (generatedBalancedRangeTree inputLength context first count).atoms =
      balancedRangeRequestAtoms inputLength context first count := by
  induction count using Nat.strong_induction_on generalizing first with
  | h count ih =>
      match count with
      | 0 =>
          simp [balancedRangeRequestAtoms, BalancedTraversalTree.atoms]
      | 1 =>
          simp [balancedRangeRequestAtoms, BalancedTraversalTree.atoms]
      | rest + 2 =>
          let total := rest + 2
          let leftCount := (total + 1) / 2
          let rightCount := total / 2
          have hleftLt : leftCount < total := by
            dsimp [leftCount, total]
            omega
          have hrightLt : rightCount < total := by
            dsimp [rightCount, total]
            omega
          have hsplit : leftCount + rightCount = total := by
            dsimp [leftCount, rightCount, total]
            omega
          rw [generatedBalancedRangeTree]
          simp only [BalancedTraversalTree.atoms]
          rw [ih leftCount hleftLt, ih rightCount hrightLt]
          rw [← balancedRangeRequestAtoms_append, hsplit]

theorem generatedBalancedRangeTree_code
    (inputLength context first count : ℕ) :
    (generatedBalancedRangeTree inputLength context first count).code =
      encodeBalancedList
        (balancedRangeRequestAtoms inputLength context first count) := by
  induction count using Nat.strong_induction_on generalizing first with
  | h count ih =>
      match count with
      | 0 =>
          simp [balancedRangeRequestAtoms, BalancedTraversalTree.code,
            encodeBalancedList]
      | 1 =>
          simp [balancedRangeRequestAtoms, BalancedTraversalTree.code,
            encodeBalancedList]
      | rest + 2 =>
          let total := rest + 2
          let leftCount := (total + 1) / 2
          let rightCount := total / 2
          have hleftPositive : 0 < leftCount := by
            dsimp [leftCount, total]
            omega
          have hleftLt : leftCount < total := by
            dsimp [leftCount, total]
            omega
          have hrightPositive : 0 < rightCount := by
            dsimp [rightCount, total]
            omega
          have hrightLt : rightCount < total := by
            dsimp [rightCount, total]
            omega
          have hsplit : leftCount + rightCount = total := by
            dsimp [leftCount, rightCount, total]
            omega
          let left :=
            balancedRangeRequestAtoms inputLength context first leftCount
          let right :=
            balancedRangeRequestAtoms inputLength context
              (first + leftCount) rightCount
          have hwhole :
              balancedRangeRequestAtoms inputLength context first total =
                left ++ right := by
            dsimp [left, right]
            rw [← balancedRangeRequestAtoms_append, hsplit]
          have hleftLength : left.length = leftCount := by
            simp [left]
          have hrightLength : right.length = rightCount := by
            simp [right]
          have htake :
              (balancedRangeRequestAtoms inputLength context first total).take
                  leftCount =
                left := by
            rw [hwhole, ← hleftLength]
            simp
          have hdrop :
              (balancedRangeRequestAtoms inputLength context first total).drop
                  leftCount =
                right := by
            rw [hwhole, ← hleftLength]
            simp
          rw [generatedBalancedRangeTree]
          simp only [BalancedTraversalTree.code]
          rw [ih leftCount hleftLt, ih rightCount hrightLt]
          conv_rhs => rw [encodeBalancedList.eq_def]
          simp only [balancedRangeRequestAtoms_succ, List.length_cons,
            balancedRangeRequestAtoms_length]
          have hcanonicalLeft :
              (rest + 2 + 1) / 2 = leftCount := by
            rfl
          rw [hcanonicalLeft]
          rw [show
            (balancedRangeRequestAtom inputLength first context ::
              balancedRangeRequestAtom inputLength (first + 1) context ::
              balancedRangeRequestAtoms inputLength context (first + 1 + 1)
                rest) =
              balancedRangeRequestAtoms inputLength context first total by
                rfl]
          rw [htake, hdrop]

/-- Public input and exact successful output. -/
def generatedBalancedRangeInput (count context : ℕ) : ℕ :=
  Nat.pair count context

def generatedBalancedRangeOutput
    (inputLength count context : ℕ) : ℕ :=
  Nat.pair
    (encodeBalancedList
      (balancedRangeRequestAtoms inputLength context 0 count))
    context

/-- Register ABI:

* `r0`: next range index;
* `r1`: current subtree count;
* `r2`: canonical tagged continuation stack;
* `r3`: completed subtree and final result;
* `r4`--`r6`: frame and pairing scratch;
* `r7`, `r9`, `r10`: constants zero, one, and two;
* `r8`: preserved context;
* `r11`: preserved source input length.

The continuation uses the shared `BalancedTraversalFrame` encoding.  A
`visitRight` frame stores the right count; after the left subtree finishes it
is replaced by `combineLeft`, which stores the completed left code. -/
def generatedBalancedRangeProgram : NPOracleProgram :=
  [ .copy 1 11 1
  , .unpairLeft 0 1 2
  , .unpairRight 0 8 3
  , .set 0 0 4
  , .set 2 0 5
  , .set 7 0 6
  , .set 9 1 7
  , .set 10 2 8
  , .set 3 0 9
  , .set 4 0 10
  , .set 5 0 11
  , .set 6 0 12
  , .branchZero 7 13 13
  , .branchZero 1 14 16
  , .set 3 0 15
  , .branchZero 7 30 30
  , .copy 1 4 17
  , .decrement 4 18
  , .branchZero 4 19 23
    -- Singleton: construct `pair inputLength (pair index context)`.
  , .pair 0 8 5 20
  , .pair 11 5 3 21
  , .increment 0 22
  , .pair 9 3 3 30
    -- Branch: descend left and remember the right count.
  , .shiftRight 1 1 4 24
  , .increment 1 25
  , .shiftRight 1 1 1 26
  , .pair 7 4 5 27
  , .pair 5 2 5 28
  , .pair 9 5 2 29
  , .branchZero 7 13 13
    -- Pop one `BalancedTraversalFrame`.
  , .branchZero 2 46 31
  , .unpairRight 2 5 32
  , .unpairLeft 5 4 33
  , .unpairRight 5 2 34
  , .unpairLeft 4 6 35
  , .unpairRight 4 4 36
  , .branchZero 6 37 43
    -- Left complete: save it and descend into the pending right subtree.
  , .copy 3 6 38
  , .pair 9 6 5 39
  , .pair 5 2 5 40
  , .pair 9 5 2 41
  , .copy 4 1 42
  , .branchZero 7 13 13
    -- Right complete: construct the unique canonical branch.
  , .pair 4 3 5 44
  , .pair 10 5 3 45
  , .branchZero 7 30 30
    -- Preserve context for the next compositional stage.
  , .pair 3 8 3 47
  , .halt 3
  ]

@[simp] theorem generatedBalancedRangeProgram_length :
    generatedBalancedRangeProgram.length = 48 := by
  rfl

theorem generatedBalancedRangeProgram_oracleFree :
    OracleFree generatedBalancedRangeProgram := by
  rfl

/-- Exact build-controller fuel, from `pc = 13` through arrival at the return
dispatcher `pc = 30`. -/
def generatedBalancedRangeBuildFuel : BalancedTraversalTree → ℕ
  | .empty => 3
  | .leaf _ => 8
  | .branch left right =>
      34 + generatedBalancedRangeBuildFuel left +
        generatedBalancedRangeBuildFuel right

/-- Thirteen setup instructions and three final return/output instructions. -/
def generatedBalancedRangeFuel
    (inputLength count context : ℕ) : ℕ :=
  16 + generatedBalancedRangeBuildFuel
    (generatedBalancedRangeTree inputLength context 0 count)

/-! ## Exact execution ledger

The ledger lists values actually written by the trace.  It is deliberately
structural rather than a `pairIter fuel` bound: sequential work must not be
misreported as additional pairing depth.  The later width theorem therefore
has only the logarithmic continuation depth to discharge. -/

private def framePayload
    (frame : BalancedTraversalFrame)
    (frames : List BalancedTraversalFrame) : ℕ :=
  Nat.pair (encodeBalancedTraversalFrame frame)
    (encodeBalancedTraversalStack frames)

private def generatedBalancedRangeBuildValues
    (inputLength context first : ℕ) :
    (count : ℕ) → List BalancedTraversalFrame → List ℕ
  | 0, _frames => [0]
  | 1, _frames =>
      let inner := Nat.pair first context
      let atom := balancedRangeRequestAtom inputLength first context
      [1, 0, inner, atom, first + 1, Nat.pair 1 atom]
  | count + 2, frames =>
      let total := count + 2
      let leftCount := (total + 1) / 2
      let rightCount := total / 2
      let leftTree :=
        generatedBalancedRangeTree inputLength context first leftCount
      let rightTree :=
        generatedBalancedRangeTree inputLength context
          (first + leftCount) rightCount
      let visit : BalancedTraversalFrame := .visitRight rightCount
      let combine : BalancedTraversalFrame := .combineLeft leftTree.code
      let visitPayload := framePayload visit frames
      let combinePayload := framePayload combine frames
      [ total
      , total.pred
      , rightCount
      , total + 1
      , leftCount
      , encodeBalancedTraversalFrame visit
      , visitPayload
      , encodeBalancedTraversalStack (visit :: frames)
      ] ++
      generatedBalancedRangeBuildValues inputLength context first leftCount
        (visit :: frames) ++
      [ visitPayload
      , encodeBalancedTraversalFrame visit
      , encodeBalancedTraversalStack frames
      , 0
      , rightCount
      , leftTree.code
      , encodeBalancedTraversalFrame combine
      , combinePayload
      , encodeBalancedTraversalStack (combine :: frames)
      , rightCount
      ] ++
      generatedBalancedRangeBuildValues inputLength context
        (first + leftCount) rightCount (combine :: frames) ++
      [ combinePayload
      , encodeBalancedTraversalFrame combine
      , encodeBalancedTraversalStack frames
      , 1
      , leftTree.code
      , Nat.pair leftTree.code rightTree.code
      , Nat.pair 2 (Nat.pair leftTree.code rightTree.code)
      ]
termination_by count => count
decreasing_by
  all_goals
    simp_wf
    omega

def generatedBalancedRangeExecutionValues
    (inputLength count context : ℕ) : List ℕ :=
  let tree := generatedBalancedRangeTree inputLength context 0 count
  [inputLength, count, context, 0, 1, 2] ++
    generatedBalancedRangeBuildValues inputLength context 0 count [] ++
    [tree.code, Nat.pair tree.code context]

def generatedBalancedRangeRequiredBits
    (inputLength count context : ℕ) : ℕ :=
  ((generatedBalancedRangeExecutionValues inputLength count context).map
    natBitLength).foldr max 0

private theorem le_foldr_max_of_mem
    {value : ℕ} {values : List ℕ} (hmem : value ∈ values) :
    value ≤ values.foldr max 0 := by
  induction values with
  | nil => simp at hmem
  | cons head tail ih =>
      simp only [List.mem_cons] at hmem
      simp only [List.foldr]
      rcases hmem with rfl | hmem
      · exact le_max_left _ _
      · exact (ih hmem).trans (le_max_right _ _)

theorem generatedBalancedRangeRequiredBits_of_mem
    {inputLength count context value : ℕ}
    (hmem :
      value ∈ generatedBalancedRangeExecutionValues
        inputLength count context) :
    natBitLength value ≤
      generatedBalancedRangeRequiredBits inputLength count context := by
  apply le_foldr_max_of_mem
  exact List.mem_map.mpr ⟨value, hmem, rfl⟩

theorem generatedBalancedRangeRequiredBits_positive
    (inputLength count context : ℕ) :
    0 < generatedBalancedRangeRequiredBits inputLength count context := by
  have hmem :
      inputLength ∈
        generatedBalancedRangeExecutionValues inputLength count context := by
    simp [generatedBalancedRangeExecutionValues]
  have hle := generatedBalancedRangeRequiredBits_of_mem hmem
  have hpositive : 0 < natBitLength inputLength := by
    simp [natBitLength]
  omega

/-! ## Controller chunks -/

private def emptyBuildState (state : NPOracleState) : NPOracleState :=
  (((state.jump 14).write 3 0).jump 15).jump 30

private theorem run_emptyBuildState
    {maximumBits extra : ℕ} (state : NPOracleState)
    (hpc : state.pc = 13)
    (hcount : state.registers 1 = 0)
    (hzeroBits : natBitLength 0 ≤ maximumBits) :
    runNPOracleProgram generatedBalancedRangeProgram maximumBits
        (3 + extra) state =
      runNPOracleProgram generatedBalancedRangeProgram maximumBits extra
        (emptyBuildState state) := by
  rw [show 3 + extra = (2 + extra) + 1 by omega]
  rw [run_branchZero_instruction (fuel := 2 + extra) (by rfl) hpc]
  rw [if_pos hcount]
  rw [show 2 + extra = (1 + extra) + 1 by omega]
  rw [run_set_instruction (fuel := 1 + extra) (by rfl) rfl hzeroBits]
  rw [show 1 + extra = extra + 1 by omega]
  rw [run_branchZero_instruction (fuel := extra) (by rfl) rfl]
  simp [emptyBuildState]

private def leafBuildState
    (inputLength context first : ℕ)
    (state : NPOracleState) : NPOracleState :=
  let state1 := state.jump 16
  let state2 := (state1.write 4 1).jump 17
  let state3 := (state2.write 4 0).jump 18
  let state4 := state3.jump 19
  let inner := Nat.pair first context
  let state5 := (state4.write 5 inner).jump 20
  let atom := balancedRangeRequestAtom inputLength first context
  let state6 := (state5.write 3 atom).jump 21
  let state7 := (state6.write 0 (first + 1)).jump 22
  (state7.write 3 (Nat.pair 1 atom)).jump 30

private theorem run_leafBuildState
    (inputLength context first : ℕ)
    {maximumBits extra : ℕ} (state : NPOracleState)
    (hpc : state.pc = 13)
    (hindex : state.registers 0 = first)
    (hcount : state.registers 1 = 1)
    (hcontext : state.registers 8 = context)
    (hone : state.registers 9 = 1)
    (hinputLength : state.registers 11 = inputLength)
    (hzeroBits : natBitLength 0 ≤ maximumBits)
    (honeBits : natBitLength 1 ≤ maximumBits)
    (hinnerBits :
      natBitLength (Nat.pair first context) ≤ maximumBits)
    (hatomBits :
      natBitLength (balancedRangeRequestAtom inputLength first context) ≤
        maximumBits)
    (hnextBits : natBitLength (first + 1) ≤ maximumBits)
    (hleafBits :
      natBitLength
          (Nat.pair 1
            (balancedRangeRequestAtom inputLength first context)) ≤
        maximumBits) :
    runNPOracleProgram generatedBalancedRangeProgram maximumBits
        (8 + extra) state =
      runNPOracleProgram generatedBalancedRangeProgram maximumBits extra
        (leafBuildState inputLength context first state) := by
  let state1 := state.jump 16
  let state2 := (state1.write 4 1).jump 17
  let state3 := (state2.write 4 0).jump 18
  let state4 := state3.jump 19
  let inner := Nat.pair first context
  let state5 := (state4.write 5 inner).jump 20
  let atom := balancedRangeRequestAtom inputLength first context
  let state6 := (state5.write 3 atom).jump 21
  let state7 := (state6.write 0 (first + 1)).jump 22
  let state8 := (state7.write 3 (Nat.pair 1 atom)).jump 30
  rw [show 8 + extra = (7 + extra) + 1 by omega]
  rw [run_branchZero_instruction (fuel := 7 + extra) (by rfl) hpc]
  rw [hcount, if_neg (by omega : (1 : ℕ) ≠ 0)]
  change
    runNPOracleProgram generatedBalancedRangeProgram maximumBits
        (7 + extra) state1 =
      runNPOracleProgram generatedBalancedRangeProgram maximumBits extra
        (leafBuildState inputLength context first state)
  rw [show 7 + extra = (6 + extra) + 1 by omega]
  rw [run_copy_instruction (fuel := 6 + extra)
    (value := 1) (by rfl) rfl (by
      simp [state1, hcount]) honeBits]
  change
    runNPOracleProgram generatedBalancedRangeProgram maximumBits
        (6 + extra) state2 =
      runNPOracleProgram generatedBalancedRangeProgram maximumBits extra
        (leafBuildState inputLength context first state)
  rw [show 6 + extra = (5 + extra) + 1 by omega]
  rw [run_decrement_instruction (fuel := 5 + extra)
    (value := 0) (by rfl) rfl (by
      simp [state2, state1]) hzeroBits]
  change
    runNPOracleProgram generatedBalancedRangeProgram maximumBits
        (5 + extra) state3 =
      runNPOracleProgram generatedBalancedRangeProgram maximumBits extra
        (leafBuildState inputLength context first state)
  rw [show 5 + extra = (4 + extra) + 1 by omega]
  rw [run_branchZero_instruction (fuel := 4 + extra) (by rfl) rfl]
  change
    runNPOracleProgram generatedBalancedRangeProgram maximumBits
        (4 + extra) state4 =
      runNPOracleProgram generatedBalancedRangeProgram maximumBits extra
        (leafBuildState inputLength context first state)
  rw [show 4 + extra = (3 + extra) + 1 by omega]
  rw [run_pair_instruction (fuel := 3 + extra)
    (value := inner) (by rfl) rfl (by
      simp [state4, state3, state2, state1, inner, hindex, hcontext])
    (by simpa [inner] using hinnerBits)]
  change
    runNPOracleProgram generatedBalancedRangeProgram maximumBits
        (3 + extra) state5 =
      runNPOracleProgram generatedBalancedRangeProgram maximumBits extra
        (leafBuildState inputLength context first state)
  rw [show 3 + extra = (2 + extra) + 1 by omega]
  rw [run_pair_instruction (fuel := 2 + extra)
    (value := atom) (by rfl) rfl (by
      simp [state5, state4, state3, state2, state1, atom, inner,
        balancedRangeRequestAtom, hinputLength])
    (by simpa [atom] using hatomBits)]
  change
    runNPOracleProgram generatedBalancedRangeProgram maximumBits
        (2 + extra) state6 =
      runNPOracleProgram generatedBalancedRangeProgram maximumBits extra
        (leafBuildState inputLength context first state)
  rw [show 2 + extra = (1 + extra) + 1 by omega]
  rw [run_increment_instruction (fuel := 1 + extra)
    (value := first + 1) (by rfl) rfl (by
      simp [state6, state5, state4, state3, state2, state1, hindex])
    hnextBits]
  change
    runNPOracleProgram generatedBalancedRangeProgram maximumBits
        (1 + extra) state7 =
      runNPOracleProgram generatedBalancedRangeProgram maximumBits extra
        (leafBuildState inputLength context first state)
  rw [show 1 + extra = extra + 1 by omega]
  rw [run_pair_instruction (fuel := extra)
    (value := Nat.pair 1 atom) (by rfl) rfl (by
      simp [state7, state6, state5, state4, state3, state2, state1,
        hone, atom])
    (by simpa [atom] using hleafBits)]
  rfl

private def descendBuildState
    (total leftCount rightCount : ℕ)
    (frames : List BalancedTraversalFrame)
    (state : NPOracleState) : NPOracleState :=
  let visit : BalancedTraversalFrame := .visitRight rightCount
  let frameCode := encodeBalancedTraversalFrame visit
  let payload := framePayload visit frames
  let stack := encodeBalancedTraversalStack (visit :: frames)
  let state1 := state.jump 16
  let state2 := (state1.write 4 total).jump 17
  let state3 := (state2.write 4 total.pred).jump 18
  let state4 := state3.jump 23
  let state5 := (state4.write 4 rightCount).jump 24
  let state6 := (state5.write 1 (total + 1)).jump 25
  let state7 := (state6.write 1 leftCount).jump 26
  let state8 := (state7.write 5 frameCode).jump 27
  let state9 := (state8.write 5 payload).jump 28
  let state10 := (state9.write 2 stack).jump 29
  state10.jump 13

private theorem run_descendBuildState
    (total leftCount rightCount : ℕ)
    (frames : List BalancedTraversalFrame)
    {maximumBits extra : ℕ} (state : NPOracleState)
    (hpc : state.pc = 13)
    (hcount : state.registers 1 = total)
    (hstack :
      state.registers 2 = encodeBalancedTraversalStack frames)
    (hzero : state.registers 7 = 0)
    (hone : state.registers 9 = 1)
    (htwo : 2 ≤ total)
    (hright : Nat.shiftRight total 1 = rightCount)
    (hleft : Nat.shiftRight (total + 1) 1 = leftCount)
    (htotalBits : natBitLength total ≤ maximumBits)
    (hpredBits : natBitLength total.pred ≤ maximumBits)
    (hrightBits : natBitLength rightCount ≤ maximumBits)
    (hsuccBits : natBitLength (total + 1) ≤ maximumBits)
    (hleftBits : natBitLength leftCount ≤ maximumBits)
    (hframeBits :
      natBitLength
          (encodeBalancedTraversalFrame (.visitRight rightCount)) ≤
        maximumBits)
    (hpayloadBits :
      natBitLength (framePayload (.visitRight rightCount) frames) ≤
        maximumBits)
    (hnewStackBits :
      natBitLength
          (encodeBalancedTraversalStack
            (.visitRight rightCount :: frames)) ≤
        maximumBits) :
    runNPOracleProgram generatedBalancedRangeProgram maximumBits
        (11 + extra) state =
      runNPOracleProgram generatedBalancedRangeProgram maximumBits extra
        (descendBuildState total leftCount rightCount frames state) := by
  let visit : BalancedTraversalFrame := .visitRight rightCount
  let frameCode := encodeBalancedTraversalFrame visit
  let payload := framePayload visit frames
  let stack := encodeBalancedTraversalStack (visit :: frames)
  let state1 := state.jump 16
  let state2 := (state1.write 4 total).jump 17
  let state3 := (state2.write 4 total.pred).jump 18
  let state4 := state3.jump 23
  let state5 := (state4.write 4 rightCount).jump 24
  let state6 := (state5.write 1 (total + 1)).jump 25
  let state7 := (state6.write 1 leftCount).jump 26
  let state8 := (state7.write 5 frameCode).jump 27
  let state9 := (state8.write 5 payload).jump 28
  let state10 := (state9.write 2 stack).jump 29
  let state11 := state10.jump 13
  rw [show 11 + extra = (10 + extra) + 1 by omega]
  rw [run_branchZero_instruction (fuel := 10 + extra) (by rfl) hpc]
  rw [hcount, if_neg (by omega)]
  change
    runNPOracleProgram generatedBalancedRangeProgram maximumBits
        (10 + extra) state1 =
      runNPOracleProgram generatedBalancedRangeProgram maximumBits extra
        (descendBuildState total leftCount rightCount frames state)
  rw [show 10 + extra = (9 + extra) + 1 by omega]
  rw [run_copy_instruction (fuel := 9 + extra)
    (value := total) (by rfl) rfl (by
      simp [state1, hcount]) htotalBits]
  change
    runNPOracleProgram generatedBalancedRangeProgram maximumBits
        (9 + extra) state2 =
      runNPOracleProgram generatedBalancedRangeProgram maximumBits extra
        (descendBuildState total leftCount rightCount frames state)
  rw [show 9 + extra = (8 + extra) + 1 by omega]
  rw [run_decrement_instruction (fuel := 8 + extra)
    (value := total.pred) (by rfl) rfl (by
      simp [state2, state1]) hpredBits]
  change
    runNPOracleProgram generatedBalancedRangeProgram maximumBits
        (8 + extra) state3 =
      runNPOracleProgram generatedBalancedRangeProgram maximumBits extra
        (descendBuildState total leftCount rightCount frames state)
  rw [show 8 + extra = (7 + extra) + 1 by omega]
  rw [run_branchZero_instruction (fuel := 7 + extra) (by rfl) rfl]
  have hpredNe : total.pred ≠ 0 := by
    simp only [Nat.pred_eq_sub_one]
    omega
  rw [show state3.registers 4 = total.pred by
    simp [state3, state2, state1]]
  rw [if_neg hpredNe]
  change
    runNPOracleProgram generatedBalancedRangeProgram maximumBits
        (7 + extra) state4 =
      runNPOracleProgram generatedBalancedRangeProgram maximumBits extra
        (descendBuildState total leftCount rightCount frames state)
  rw [show 7 + extra = (6 + extra) + 1 by omega]
  rw [run_shiftRight_instruction (fuel := 6 + extra)
    (value := rightCount) (by rfl) rfl (by
      simpa [state4, state3, state2, state1, hcount] using hright)
    hrightBits]
  change
    runNPOracleProgram generatedBalancedRangeProgram maximumBits
        (6 + extra) state5 =
      runNPOracleProgram generatedBalancedRangeProgram maximumBits extra
        (descendBuildState total leftCount rightCount frames state)
  rw [show 6 + extra = (5 + extra) + 1 by omega]
  rw [run_increment_instruction (fuel := 5 + extra)
    (value := total + 1) (by rfl) rfl (by
      simp [state5, state4, state3, state2, state1, hcount])
    hsuccBits]
  change
    runNPOracleProgram generatedBalancedRangeProgram maximumBits
        (5 + extra) state6 =
      runNPOracleProgram generatedBalancedRangeProgram maximumBits extra
        (descendBuildState total leftCount rightCount frames state)
  rw [show 5 + extra = (4 + extra) + 1 by omega]
  rw [run_shiftRight_instruction (fuel := 4 + extra)
    (value := leftCount) (by rfl) rfl (by
      simpa [state6, state5, state4, state3, state2, state1] using hleft)
    hleftBits]
  change
    runNPOracleProgram generatedBalancedRangeProgram maximumBits
        (4 + extra) state7 =
      runNPOracleProgram generatedBalancedRangeProgram maximumBits extra
        (descendBuildState total leftCount rightCount frames state)
  rw [show 4 + extra = (3 + extra) + 1 by omega]
  rw [run_pair_instruction (fuel := 3 + extra)
    (value := frameCode) (by rfl) rfl (by
      simp [state7, state6, state5, state4, state3, state2, state1,
        frameCode, visit, encodeBalancedTraversalFrame, hzero])
    (by simpa [frameCode, visit] using hframeBits)]
  change
    runNPOracleProgram generatedBalancedRangeProgram maximumBits
        (3 + extra) state8 =
      runNPOracleProgram generatedBalancedRangeProgram maximumBits extra
        (descendBuildState total leftCount rightCount frames state)
  rw [show 3 + extra = (2 + extra) + 1 by omega]
  rw [run_pair_instruction (fuel := 2 + extra)
    (value := payload) (by rfl) rfl (by
      simp [state8, state7, state6, state5, state4, state3, state2,
        state1, payload, framePayload, frameCode, visit, hstack])
    (by simpa [payload, visit] using hpayloadBits)]
  change
    runNPOracleProgram generatedBalancedRangeProgram maximumBits
        (2 + extra) state9 =
      runNPOracleProgram generatedBalancedRangeProgram maximumBits extra
        (descendBuildState total leftCount rightCount frames state)
  rw [show 2 + extra = (1 + extra) + 1 by omega]
  rw [run_pair_instruction (fuel := 1 + extra)
    (value := stack) (by rfl) rfl (by
      simp [state9, state8, state7, state6, state5, state4, state3,
        state2, state1, stack, payload, framePayload, frameCode, visit,
        encodeBalancedTraversalStack_cons, hone])
    (by simpa [stack, visit] using hnewStackBits)]
  change
    runNPOracleProgram generatedBalancedRangeProgram maximumBits
        (1 + extra) state10 =
      runNPOracleProgram generatedBalancedRangeProgram maximumBits extra
        (descendBuildState total leftCount rightCount frames state)
  rw [show 1 + extra = extra + 1 by omega]
  rw [run_branchZero_instruction (fuel := extra) (by rfl) rfl]
  simp [state10, state9, state8, state7, state6, state5, state4,
    state3, state2, state1, hzero, descendBuildState,
    stack, payload, framePayload, frameCode, visit]

private def resumeRightState
    (rightCount leftCode : ℕ)
    (frames : List BalancedTraversalFrame)
    (state : NPOracleState) : NPOracleState :=
  let visit : BalancedTraversalFrame := .visitRight rightCount
  let combine : BalancedTraversalFrame := .combineLeft leftCode
  let visitFrame := encodeBalancedTraversalFrame visit
  let visitPayload := framePayload visit frames
  let rest := encodeBalancedTraversalStack frames
  let combineFrame := encodeBalancedTraversalFrame combine
  let combinePayload := framePayload combine frames
  let combineStack := encodeBalancedTraversalStack (combine :: frames)
  let state1 := state.jump 31
  let state2 := (state1.write 5 visitPayload).jump 32
  let state3 := (state2.write 4 visitFrame).jump 33
  let state4 := (state3.write 2 rest).jump 34
  let state5 := (state4.write 6 0).jump 35
  let state6 := (state5.write 4 rightCount).jump 36
  let state7 := state6.jump 37
  let state8 := (state7.write 6 leftCode).jump 38
  let state9 := (state8.write 5 combineFrame).jump 39
  let state10 := (state9.write 5 combinePayload).jump 40
  let state11 := (state10.write 2 combineStack).jump 41
  let state12 := (state11.write 1 rightCount).jump 42
  state12.jump 13

private theorem run_resumeRightState
    (rightCount leftCode : ℕ)
    (frames : List BalancedTraversalFrame)
    {maximumBits extra : ℕ} (state : NPOracleState)
    (hpc : state.pc = 30)
    (hstack :
      state.registers 2 =
        encodeBalancedTraversalStack
          (.visitRight rightCount :: frames))
    (hleftCode : state.registers 3 = leftCode)
    (hzero : state.registers 7 = 0)
    (hone : state.registers 9 = 1)
    (hvisitPayloadBits :
      natBitLength (framePayload (.visitRight rightCount) frames) ≤
        maximumBits)
    (hvisitFrameBits :
      natBitLength
          (encodeBalancedTraversalFrame (.visitRight rightCount)) ≤
        maximumBits)
    (hrestBits :
      natBitLength (encodeBalancedTraversalStack frames) ≤ maximumBits)
    (hzeroBits : natBitLength 0 ≤ maximumBits)
    (hrightBits : natBitLength rightCount ≤ maximumBits)
    (hleftBits : natBitLength leftCode ≤ maximumBits)
    (hcombineFrameBits :
      natBitLength
          (encodeBalancedTraversalFrame (.combineLeft leftCode)) ≤
        maximumBits)
    (hcombinePayloadBits :
      natBitLength (framePayload (.combineLeft leftCode) frames) ≤
        maximumBits)
    (hcombineStackBits :
      natBitLength
          (encodeBalancedTraversalStack (.combineLeft leftCode :: frames)) ≤
        maximumBits) :
    runNPOracleProgram generatedBalancedRangeProgram maximumBits
        (13 + extra) state =
      runNPOracleProgram generatedBalancedRangeProgram maximumBits extra
        (resumeRightState rightCount leftCode frames state) := by
  let visit : BalancedTraversalFrame := .visitRight rightCount
  let combine : BalancedTraversalFrame := .combineLeft leftCode
  let visitFrame := encodeBalancedTraversalFrame visit
  let visitPayload := framePayload visit frames
  let rest := encodeBalancedTraversalStack frames
  let combineFrame := encodeBalancedTraversalFrame combine
  let combinePayload := framePayload combine frames
  let combineStack := encodeBalancedTraversalStack (combine :: frames)
  let state1 := state.jump 31
  let state2 := (state1.write 5 visitPayload).jump 32
  let state3 := (state2.write 4 visitFrame).jump 33
  let state4 := (state3.write 2 rest).jump 34
  let state5 := (state4.write 6 0).jump 35
  let state6 := (state5.write 4 rightCount).jump 36
  let state7 := state6.jump 37
  let state8 := (state7.write 6 leftCode).jump 38
  let state9 := (state8.write 5 combineFrame).jump 39
  let state10 := (state9.write 5 combinePayload).jump 40
  let state11 := (state10.write 2 combineStack).jump 41
  let state12 := (state11.write 1 rightCount).jump 42
  have hstackNe :
      encodeBalancedTraversalStack
          (.visitRight rightCount :: frames) ≠ 0 := by
    rw [encodeBalancedTraversalStack_cons]
    exact (lt_of_lt_of_le Nat.zero_lt_one
      (Nat.left_le_pair 1
        (Nat.pair
          (encodeBalancedTraversalFrame (.visitRight rightCount))
          (encodeBalancedTraversalStack frames)))).ne'
  rw [show 13 + extra = (12 + extra) + 1 by omega]
  rw [run_branchZero_instruction (fuel := 12 + extra) (by rfl) hpc]
  rw [hstack, if_neg hstackNe]
  change
    runNPOracleProgram generatedBalancedRangeProgram maximumBits
        (12 + extra) state1 =
      runNPOracleProgram generatedBalancedRangeProgram maximumBits extra
        (resumeRightState rightCount leftCode frames state)
  rw [show 12 + extra = (11 + extra) + 1 by omega]
  rw [run_unpairRight_instruction (fuel := 11 + extra)
    (value := visitPayload) (by rfl) rfl (by
      simp [state1, hstack, visitPayload, framePayload, visit,
        encodeBalancedTraversalStack_cons])
    (by simpa [visitPayload, visit] using hvisitPayloadBits)]
  change
    runNPOracleProgram generatedBalancedRangeProgram maximumBits
        (11 + extra) state2 =
      runNPOracleProgram generatedBalancedRangeProgram maximumBits extra
        (resumeRightState rightCount leftCode frames state)
  rw [show 11 + extra = (10 + extra) + 1 by omega]
  rw [run_unpairLeft_instruction (fuel := 10 + extra)
    (value := visitFrame) (by rfl) rfl (by
      simp [state2, state1, visitPayload, framePayload, visitFrame,
        visit])
    (by simpa [visitFrame, visit] using hvisitFrameBits)]
  change
    runNPOracleProgram generatedBalancedRangeProgram maximumBits
        (10 + extra) state3 =
      runNPOracleProgram generatedBalancedRangeProgram maximumBits extra
        (resumeRightState rightCount leftCode frames state)
  rw [show 10 + extra = (9 + extra) + 1 by omega]
  rw [run_unpairRight_instruction (fuel := 9 + extra)
    (value := rest) (by rfl) rfl (by
      simp [state3, state2, state1, visitPayload, framePayload, rest,
        visit])
    (by simpa [rest] using hrestBits)]
  change
    runNPOracleProgram generatedBalancedRangeProgram maximumBits
        (9 + extra) state4 =
      runNPOracleProgram generatedBalancedRangeProgram maximumBits extra
        (resumeRightState rightCount leftCode frames state)
  rw [show 9 + extra = (8 + extra) + 1 by omega]
  rw [run_unpairLeft_instruction (fuel := 8 + extra)
    (value := 0) (by rfl) rfl (by
      simp [state4, state3, state2, state1, visitFrame,
        encodeBalancedTraversalFrame, visit])
    hzeroBits]
  change
    runNPOracleProgram generatedBalancedRangeProgram maximumBits
        (8 + extra) state5 =
      runNPOracleProgram generatedBalancedRangeProgram maximumBits extra
        (resumeRightState rightCount leftCode frames state)
  rw [show 8 + extra = (7 + extra) + 1 by omega]
  rw [run_unpairRight_instruction (fuel := 7 + extra)
    (value := rightCount) (by rfl) rfl (by
      simp [state5, state4, state3, state2, state1, visitFrame,
        encodeBalancedTraversalFrame, visit])
    hrightBits]
  change
    runNPOracleProgram generatedBalancedRangeProgram maximumBits
        (7 + extra) state6 =
      runNPOracleProgram generatedBalancedRangeProgram maximumBits extra
        (resumeRightState rightCount leftCode frames state)
  rw [show 7 + extra = (6 + extra) + 1 by omega]
  rw [run_branchZero_instruction (fuel := 6 + extra) (by rfl) rfl]
  change
    runNPOracleProgram generatedBalancedRangeProgram maximumBits
        (6 + extra) state7 =
      runNPOracleProgram generatedBalancedRangeProgram maximumBits extra
        (resumeRightState rightCount leftCode frames state)
  rw [show 6 + extra = (5 + extra) + 1 by omega]
  rw [run_copy_instruction (fuel := 5 + extra)
    (value := leftCode) (by rfl) rfl (by
      simp [state7, state6, state5, state4, state3, state2, state1,
        hleftCode])
    hleftBits]
  change
    runNPOracleProgram generatedBalancedRangeProgram maximumBits
        (5 + extra) state8 =
      runNPOracleProgram generatedBalancedRangeProgram maximumBits extra
        (resumeRightState rightCount leftCode frames state)
  rw [show 5 + extra = (4 + extra) + 1 by omega]
  rw [run_pair_instruction (fuel := 4 + extra)
    (value := combineFrame) (by rfl) rfl (by
      simp [state8, state7, state6, state5, state4, state3, state2,
        state1, combineFrame, combine, encodeBalancedTraversalFrame,
        hone])
    (by simpa [combineFrame, combine] using hcombineFrameBits)]
  change
    runNPOracleProgram generatedBalancedRangeProgram maximumBits
        (4 + extra) state9 =
      runNPOracleProgram generatedBalancedRangeProgram maximumBits extra
        (resumeRightState rightCount leftCode frames state)
  rw [show 4 + extra = (3 + extra) + 1 by omega]
  rw [run_pair_instruction (fuel := 3 + extra)
    (value := combinePayload) (by rfl) rfl (by
      simp [state9, state8, state7, state6, state5, state4, state3,
        state2, state1, combinePayload, framePayload, combineFrame,
        combine, rest])
    (by simpa [combinePayload, combine] using hcombinePayloadBits)]
  change
    runNPOracleProgram generatedBalancedRangeProgram maximumBits
        (3 + extra) state10 =
      runNPOracleProgram generatedBalancedRangeProgram maximumBits extra
        (resumeRightState rightCount leftCode frames state)
  rw [show 3 + extra = (2 + extra) + 1 by omega]
  rw [run_pair_instruction (fuel := 2 + extra)
    (value := combineStack) (by rfl) rfl (by
      simp [state10, state9, state8, state7, state6, state5, state4,
        state3, state2, state1, combineStack, combinePayload,
        framePayload, combineFrame, combine,
        encodeBalancedTraversalStack_cons, hone])
    (by simpa [combineStack, combine] using hcombineStackBits)]
  change
    runNPOracleProgram generatedBalancedRangeProgram maximumBits
        (2 + extra) state11 =
      runNPOracleProgram generatedBalancedRangeProgram maximumBits extra
        (resumeRightState rightCount leftCode frames state)
  rw [show 2 + extra = (1 + extra) + 1 by omega]
  rw [run_copy_instruction (fuel := 1 + extra)
    (value := rightCount) (by rfl) rfl (by
      simp [state11, state10, state9, state8, state7, state6, state5,
        state4, state3, state2, state1])
    hrightBits]
  change
    runNPOracleProgram generatedBalancedRangeProgram maximumBits
        (1 + extra) state12 =
      runNPOracleProgram generatedBalancedRangeProgram maximumBits extra
        (resumeRightState rightCount leftCode frames state)
  rw [show 1 + extra = extra + 1 by omega]
  rw [run_branchZero_instruction (fuel := extra) (by rfl) rfl]
  simp [state12, state11, state10, state9, state8, state7, state6,
    state5, state4, state3, state2, state1, resumeRightState, hzero,
    combineStack, combinePayload, combineFrame, rest, visitPayload,
    visitFrame, framePayload, combine, visit]

private def combineBranchState
    (leftCode rightCode : ℕ)
    (frames : List BalancedTraversalFrame)
    (state : NPOracleState) : NPOracleState :=
  let combine : BalancedTraversalFrame := .combineLeft leftCode
  let frame := encodeBalancedTraversalFrame combine
  let payload := framePayload combine frames
  let rest := encodeBalancedTraversalStack frames
  let inner := Nat.pair leftCode rightCode
  let branch := Nat.pair 2 inner
  let state1 := state.jump 31
  let state2 := (state1.write 5 payload).jump 32
  let state3 := (state2.write 4 frame).jump 33
  let state4 := (state3.write 2 rest).jump 34
  let state5 := (state4.write 6 1).jump 35
  let state6 := (state5.write 4 leftCode).jump 36
  let state7 := state6.jump 43
  let state8 := (state7.write 5 inner).jump 44
  let state9 := (state8.write 3 branch).jump 45
  state9.jump 30

private theorem run_combineBranchState
    (leftCode rightCode : ℕ)
    (frames : List BalancedTraversalFrame)
    {maximumBits extra : ℕ} (state : NPOracleState)
    (hpc : state.pc = 30)
    (hstack :
      state.registers 2 =
        encodeBalancedTraversalStack
          (.combineLeft leftCode :: frames))
    (hrightCode : state.registers 3 = rightCode)
    (hzero : state.registers 7 = 0)
    (htwo : state.registers 10 = 2)
    (hpayloadBits :
      natBitLength (framePayload (.combineLeft leftCode) frames) ≤
        maximumBits)
    (hframeBits :
      natBitLength
          (encodeBalancedTraversalFrame (.combineLeft leftCode)) ≤
        maximumBits)
    (hrestBits :
      natBitLength (encodeBalancedTraversalStack frames) ≤ maximumBits)
    (honeBits : natBitLength 1 ≤ maximumBits)
    (hleftBits : natBitLength leftCode ≤ maximumBits)
    (hinnerBits :
      natBitLength (Nat.pair leftCode rightCode) ≤ maximumBits)
    (hbranchBits :
      natBitLength (Nat.pair 2 (Nat.pair leftCode rightCode)) ≤
        maximumBits) :
    runNPOracleProgram generatedBalancedRangeProgram maximumBits
        (10 + extra) state =
      runNPOracleProgram generatedBalancedRangeProgram maximumBits extra
        (combineBranchState leftCode rightCode frames state) := by
  let combine : BalancedTraversalFrame := .combineLeft leftCode
  let frame := encodeBalancedTraversalFrame combine
  let payload := framePayload combine frames
  let rest := encodeBalancedTraversalStack frames
  let inner := Nat.pair leftCode rightCode
  let branch := Nat.pair 2 inner
  let state1 := state.jump 31
  let state2 := (state1.write 5 payload).jump 32
  let state3 := (state2.write 4 frame).jump 33
  let state4 := (state3.write 2 rest).jump 34
  let state5 := (state4.write 6 1).jump 35
  let state6 := (state5.write 4 leftCode).jump 36
  let state7 := state6.jump 43
  let state8 := (state7.write 5 inner).jump 44
  let state9 := (state8.write 3 branch).jump 45
  have hstackNe :
      encodeBalancedTraversalStack
          (.combineLeft leftCode :: frames) ≠ 0 := by
    rw [encodeBalancedTraversalStack_cons]
    exact (lt_of_lt_of_le Nat.zero_lt_one
      (Nat.left_le_pair 1
        (Nat.pair
          (encodeBalancedTraversalFrame (.combineLeft leftCode))
          (encodeBalancedTraversalStack frames)))).ne'
  rw [show 10 + extra = (9 + extra) + 1 by omega]
  rw [run_branchZero_instruction (fuel := 9 + extra) (by rfl) hpc]
  rw [hstack, if_neg hstackNe]
  change
    runNPOracleProgram generatedBalancedRangeProgram maximumBits
        (9 + extra) state1 =
      runNPOracleProgram generatedBalancedRangeProgram maximumBits extra
        (combineBranchState leftCode rightCode frames state)
  rw [show 9 + extra = (8 + extra) + 1 by omega]
  rw [run_unpairRight_instruction (fuel := 8 + extra)
    (value := payload) (by rfl) rfl (by
      simp [state1, hstack, payload, framePayload, combine,
        encodeBalancedTraversalStack_cons])
    (by simpa [payload, combine] using hpayloadBits)]
  change
    runNPOracleProgram generatedBalancedRangeProgram maximumBits
        (8 + extra) state2 =
      runNPOracleProgram generatedBalancedRangeProgram maximumBits extra
        (combineBranchState leftCode rightCode frames state)
  rw [show 8 + extra = (7 + extra) + 1 by omega]
  rw [run_unpairLeft_instruction (fuel := 7 + extra)
    (value := frame) (by rfl) rfl (by
      simp [state2, state1, payload, framePayload, frame, combine])
    (by simpa [frame, combine] using hframeBits)]
  change
    runNPOracleProgram generatedBalancedRangeProgram maximumBits
        (7 + extra) state3 =
      runNPOracleProgram generatedBalancedRangeProgram maximumBits extra
        (combineBranchState leftCode rightCode frames state)
  rw [show 7 + extra = (6 + extra) + 1 by omega]
  rw [run_unpairRight_instruction (fuel := 6 + extra)
    (value := rest) (by rfl) rfl (by
      simp [state3, state2, state1, payload, framePayload, rest, combine])
    (by simpa [rest] using hrestBits)]
  change
    runNPOracleProgram generatedBalancedRangeProgram maximumBits
        (6 + extra) state4 =
      runNPOracleProgram generatedBalancedRangeProgram maximumBits extra
        (combineBranchState leftCode rightCode frames state)
  rw [show 6 + extra = (5 + extra) + 1 by omega]
  rw [run_unpairLeft_instruction (fuel := 5 + extra)
    (value := 1) (by rfl) rfl (by
      simp [state4, state3, state2, state1, frame, combine,
        encodeBalancedTraversalFrame])
    honeBits]
  change
    runNPOracleProgram generatedBalancedRangeProgram maximumBits
        (5 + extra) state5 =
      runNPOracleProgram generatedBalancedRangeProgram maximumBits extra
        (combineBranchState leftCode rightCode frames state)
  rw [show 5 + extra = (4 + extra) + 1 by omega]
  rw [run_unpairRight_instruction (fuel := 4 + extra)
    (value := leftCode) (by rfl) rfl (by
      simp [state5, state4, state3, state2, state1, frame, combine,
        encodeBalancedTraversalFrame])
    hleftBits]
  change
    runNPOracleProgram generatedBalancedRangeProgram maximumBits
        (4 + extra) state6 =
      runNPOracleProgram generatedBalancedRangeProgram maximumBits extra
        (combineBranchState leftCode rightCode frames state)
  rw [show 4 + extra = (3 + extra) + 1 by omega]
  rw [run_branchZero_instruction (fuel := 3 + extra) (by rfl) rfl]
  rw [show state6.registers 6 = 1 by
    simp [state6, state5, state4, state3, state2, state1]]
  rw [if_neg (by omega : (1 : ℕ) ≠ 0)]
  change
    runNPOracleProgram generatedBalancedRangeProgram maximumBits
        (3 + extra) state7 =
      runNPOracleProgram generatedBalancedRangeProgram maximumBits extra
        (combineBranchState leftCode rightCode frames state)
  rw [show 3 + extra = (2 + extra) + 1 by omega]
  rw [run_pair_instruction (fuel := 2 + extra)
    (value := inner) (by rfl) rfl (by
      simp [state7, state6, state5, state4, state3, state2, state1,
        inner, hrightCode])
    (by simpa [inner] using hinnerBits)]
  change
    runNPOracleProgram generatedBalancedRangeProgram maximumBits
        (2 + extra) state8 =
      runNPOracleProgram generatedBalancedRangeProgram maximumBits extra
        (combineBranchState leftCode rightCode frames state)
  rw [show 2 + extra = (1 + extra) + 1 by omega]
  rw [run_pair_instruction (fuel := 1 + extra)
    (value := branch) (by rfl) rfl (by
      simp [state8, state7, state6, state5, state4, state3, state2,
        state1, branch, inner, htwo])
    (by simpa [branch, inner] using hbranchBits)]
  change
    runNPOracleProgram generatedBalancedRangeProgram maximumBits
        (1 + extra) state9 =
      runNPOracleProgram generatedBalancedRangeProgram maximumBits extra
        (combineBranchState leftCode rightCode frames state)
  rw [show 1 + extra = extra + 1 by omega]
  rw [run_branchZero_instruction (fuel := extra) (by rfl) rfl]
  simp [state9, state8, state7, state6, state5, state4, state3, state2,
    state1, combineBranchState, hzero, branch, inner, rest, payload,
    framePayload, frame, combine]

/-! ## Recursive exact trace -/

private theorem run_generatedBalancedRangeBuild
    (inputLength context first count : ℕ)
    (frames : List BalancedTraversalFrame)
    {maximumBits extra output : ℕ} (state : NPOracleState)
    (hpc : state.pc = 13)
    (hindex : state.registers 0 = first)
    (hcount : state.registers 1 = count)
    (hstack :
      state.registers 2 = encodeBalancedTraversalStack frames)
    (hzero : state.registers 7 = 0)
    (hcontext : state.registers 8 = context)
    (hone : state.registers 9 = 1)
    (htwo : state.registers 10 = 2)
    (hinputLength : state.registers 11 = inputLength)
    (hfits : ∀ value,
      value ∈ generatedBalancedRangeBuildValues
          inputLength context first count frames →
        natBitLength value ≤ maximumBits)
    (hcontinue : ∀ finalState,
      finalState.pc = 30 →
      finalState.registers 0 = first + count →
      finalState.registers 2 = encodeBalancedTraversalStack frames →
      finalState.registers 3 =
        (generatedBalancedRangeTree
          inputLength context first count).code →
      finalState.registers 7 = 0 →
      finalState.registers 8 = context →
      finalState.registers 9 = 1 →
      finalState.registers 10 = 2 →
      finalState.registers 11 = inputLength →
      runNPOracleProgram generatedBalancedRangeProgram maximumBits extra
        finalState = some output) :
    runNPOracleProgram generatedBalancedRangeProgram maximumBits
        (generatedBalancedRangeBuildFuel
          (generatedBalancedRangeTree inputLength context first count) +
          extra)
        state =
      some output := by
  induction count using Nat.strong_induction_on generalizing
      first frames state extra with
  | h count ih =>
      match count with
      | 0 =>
          have hzeroBits : natBitLength 0 ≤ maximumBits :=
            hfits 0 (by
              simp [generatedBalancedRangeBuildValues])
          rw [show
            generatedBalancedRangeBuildFuel
                (generatedBalancedRangeTree inputLength context first 0) +
                extra =
              3 + extra by
                simp [generatedBalancedRangeBuildFuel]]
          rw [run_emptyBuildState state hpc hcount hzeroBits]
          apply hcontinue (emptyBuildState state)
          · rfl
          · simp [emptyBuildState, hindex]
          · simp [emptyBuildState, hstack]
          · simp [emptyBuildState,
              BalancedTraversalTree.code]
          · simp [emptyBuildState, hzero]
          · simp [emptyBuildState, hcontext]
          · simp [emptyBuildState, hone]
          · simp [emptyBuildState, htwo]
          · simp [emptyBuildState, hinputLength]
      | 1 =>
          have hzeroBits : natBitLength 0 ≤ maximumBits :=
            hfits 0 (by
              simp [generatedBalancedRangeBuildValues])
          have honeBits : natBitLength 1 ≤ maximumBits :=
            hfits 1 (by
              simp [generatedBalancedRangeBuildValues])
          have hinnerBits :
              natBitLength (Nat.pair first context) ≤ maximumBits :=
            hfits _ (by
              simp [generatedBalancedRangeBuildValues])
          have hatomBits :
              natBitLength
                  (balancedRangeRequestAtom inputLength first context) ≤
                maximumBits :=
            hfits _ (by
              simp [generatedBalancedRangeBuildValues])
          have hnextBits :
              natBitLength (first + 1) ≤ maximumBits :=
            hfits _ (by
              simp [generatedBalancedRangeBuildValues])
          have hleafBits :
              natBitLength
                  (Nat.pair 1
                    (balancedRangeRequestAtom inputLength first context)) ≤
                maximumBits :=
            hfits _ (by
              simp [generatedBalancedRangeBuildValues])
          rw [show
            generatedBalancedRangeBuildFuel
                (generatedBalancedRangeTree inputLength context first 1) +
                extra =
              8 + extra by
                simp [generatedBalancedRangeBuildFuel]]
          rw [run_leafBuildState inputLength context first state hpc hindex
            hcount hcontext hone hinputLength hzeroBits honeBits hinnerBits
            hatomBits hnextBits hleafBits]
          apply hcontinue
            (leafBuildState inputLength context first state)
          · rfl
          · simp [leafBuildState]
          · simp [leafBuildState, hstack]
          · simp [leafBuildState,
              BalancedTraversalTree.code]
          · simp [leafBuildState, hzero]
          · simp [leafBuildState, hcontext]
          · simp [leafBuildState, hone]
          · simp [leafBuildState, htwo]
          · simp [leafBuildState, hinputLength]
      | rest + 2 =>
          let total := rest + 2
          let leftCount := (total + 1) / 2
          let rightCount := total / 2
          let leftTree :=
            generatedBalancedRangeTree inputLength context first leftCount
          let rightTree :=
            generatedBalancedRangeTree inputLength context
              (first + leftCount) rightCount
          let visit : BalancedTraversalFrame := .visitRight rightCount
          let combine : BalancedTraversalFrame :=
            .combineLeft leftTree.code
          let leftFuel := generatedBalancedRangeBuildFuel leftTree
          let rightFuel := generatedBalancedRangeBuildFuel rightTree
          have hleftPositive : 0 < leftCount := by
            dsimp [leftCount, total]
            omega
          have hleftLt : leftCount < total := by
            dsimp [leftCount, total]
            omega
          have hrightPositive : 0 < rightCount := by
            dsimp [rightCount, total]
            omega
          have hrightLt : rightCount < total := by
            dsimp [rightCount, total]
            omega
          have hsplit : leftCount + rightCount = total := by
            dsimp [leftCount, rightCount, total]
            omega
          have hrightShift :
              Nat.shiftRight total 1 = rightCount := by
            simp [rightCount, Nat.shiftRight_eq_div_pow]
          have hleftShift :
              Nat.shiftRight (total + 1) 1 = leftCount := by
            simp [leftCount, Nat.shiftRight_eq_div_pow]
          have htree :
              generatedBalancedRangeTree inputLength context first total =
                .branch leftTree rightTree := by
            simp [generatedBalancedRangeTree, total, leftCount, rightCount,
              leftTree, rightTree]
          have hfitsLeft : ∀ value,
              value ∈ generatedBalancedRangeBuildValues inputLength context
                  first leftCount (visit :: frames) →
                natBitLength value ≤ maximumBits := by
            intro value hvalue
            apply hfits value
            rw [generatedBalancedRangeBuildValues.eq_def]
            simp only [List.mem_append]
            exact Or.inl <| Or.inl <| Or.inl <| Or.inr <| by
              simpa [total, leftCount, rightCount, visit] using hvalue
          have hfitsRight : ∀ value,
              value ∈ generatedBalancedRangeBuildValues inputLength context
                  (first + leftCount) rightCount (combine :: frames) →
                natBitLength value ≤ maximumBits := by
            intro value hvalue
            apply hfits value
            rw [generatedBalancedRangeBuildValues.eq_def]
            simp only [List.mem_append]
            exact Or.inl <| Or.inr <| by
              simpa [total, leftCount, rightCount, leftTree, combine] using
                hvalue
          have htotalBits : natBitLength total ≤ maximumBits :=
            hfits total (by
              simp [generatedBalancedRangeBuildValues, total])
          have hpredBits : natBitLength total.pred ≤ maximumBits :=
            hfits total.pred (by
              simp [generatedBalancedRangeBuildValues, total])
          have hrightBits : natBitLength rightCount ≤ maximumBits :=
            hfits rightCount (by
              simp [generatedBalancedRangeBuildValues, total, rightCount])
          have hsuccBits : natBitLength (total + 1) ≤ maximumBits :=
            hfits (total + 1) (by
              simp [generatedBalancedRangeBuildValues, total])
          have hleftCountBits : natBitLength leftCount ≤ maximumBits :=
            hfits leftCount (by
              simp [generatedBalancedRangeBuildValues, total, leftCount])
          have hvisitFrameBits :
              natBitLength (encodeBalancedTraversalFrame visit) ≤
                maximumBits :=
            hfits _ (by
              simp [generatedBalancedRangeBuildValues, total, rightCount,
                visit])
          have hvisitPayloadBits :
              natBitLength (framePayload visit frames) ≤ maximumBits :=
            hfits _ (by
              simp [generatedBalancedRangeBuildValues, total, rightCount,
                visit])
          have hvisitStackBits :
              natBitLength (encodeBalancedTraversalStack (visit :: frames)) ≤
                maximumBits :=
            hfits _ (by
              simp [generatedBalancedRangeBuildValues, total, rightCount,
                visit])
          have hrestBits :
              natBitLength (encodeBalancedTraversalStack frames) ≤
                maximumBits :=
            hfits _ (by
              simp [generatedBalancedRangeBuildValues])
          have hzeroBits : natBitLength 0 ≤ maximumBits :=
            hfits 0 (by
              simp [generatedBalancedRangeBuildValues])
          have honeBits : natBitLength 1 ≤ maximumBits :=
            hfits 1 (by
              simp [generatedBalancedRangeBuildValues])
          have hleftCodeBits : natBitLength leftTree.code ≤ maximumBits :=
            hfits leftTree.code (by
              simp [generatedBalancedRangeBuildValues, total, leftCount,
                leftTree])
          have hcombineFrameBits :
              natBitLength (encodeBalancedTraversalFrame combine) ≤
                maximumBits :=
            hfits _ (by
              simp [generatedBalancedRangeBuildValues, total, leftCount,
                leftTree, combine])
          have hcombinePayloadBits :
              natBitLength (framePayload combine frames) ≤ maximumBits :=
            hfits _ (by
              simp [generatedBalancedRangeBuildValues, total, leftCount,
                leftTree, combine])
          have hcombineStackBits :
              natBitLength
                  (encodeBalancedTraversalStack (combine :: frames)) ≤
                maximumBits :=
            hfits _ (by
              simp [generatedBalancedRangeBuildValues, total, leftCount,
                leftTree, combine])
          have hinnerBits :
              natBitLength (Nat.pair leftTree.code rightTree.code) ≤
                maximumBits :=
            hfits _ (by
              simp [generatedBalancedRangeBuildValues, total, leftCount,
                rightCount, leftTree, rightTree])
          have hbranchBits :
              natBitLength
                  (Nat.pair 2 (Nat.pair leftTree.code rightTree.code)) ≤
                maximumBits :=
            hfits _ (by
              simp [generatedBalancedRangeBuildValues, total, leftCount,
                rightCount, leftTree, rightTree])
          rw [show
            generatedBalancedRangeBuildFuel
                (generatedBalancedRangeTree
                  inputLength context first total) + extra =
              11 + (leftFuel +
                (13 + (rightFuel + (10 + extra)))) by
              rw [htree]
              simp [generatedBalancedRangeBuildFuel, leftFuel, rightFuel]
              omega]
          rw [run_descendBuildState total leftCount rightCount frames
            (extra := leftFuel + (13 + (rightFuel + (10 + extra))))
            state hpc hcount hstack hzero hone (by omega) hrightShift
            hleftShift htotalBits hpredBits hrightBits hsuccBits
            hleftCountBits (by simpa [visit] using hvisitFrameBits)
            (by simpa [visit] using hvisitPayloadBits)
            (by simpa [visit] using hvisitStackBits)]
          let descend :=
            descendBuildState total leftCount rightCount frames state
          apply ih leftCount hleftLt first (visit :: frames)
            (extra := 13 + (rightFuel + (10 + extra))) descend
          · simp [descend, descendBuildState]
          · simp [descend, descendBuildState, hindex]
          · simp [descend, descendBuildState]
          · simp [descend, descendBuildState, visit]
          · simp [descend, descendBuildState, hzero]
          · simp [descend, descendBuildState, hcontext]
          · simp [descend, descendBuildState, hone]
          · simp [descend, descendBuildState, htwo]
          · simp [descend, descendBuildState, hinputLength]
          · exact hfitsLeft
          · intro leftState hleftPc hleftIndex hleftStack hleftOutput
              hleftZero hleftContext hleftOne hleftTwo hleftInputLength
            rw [run_resumeRightState rightCount leftTree.code frames
              (extra := rightFuel + (10 + extra)) leftState hleftPc
              (by simpa [visit] using hleftStack) hleftOutput hleftZero
              hleftOne
              (by simpa [visit] using hvisitPayloadBits)
              (by simpa [visit] using hvisitFrameBits) hrestBits hzeroBits
              hrightBits hleftCodeBits
              (by simpa [combine] using hcombineFrameBits)
              (by simpa [combine] using hcombinePayloadBits)
              (by simpa [combine] using hcombineStackBits)]
            let resumed :=
              resumeRightState rightCount leftTree.code frames leftState
            apply ih rightCount hrightLt (first + leftCount)
              (combine :: frames) (extra := 10 + extra) resumed
            · simp [resumed, resumeRightState]
            · simp [resumed, resumeRightState, hleftIndex]
            · simp [resumed, resumeRightState]
            · simp [resumed, resumeRightState, combine]
            · simp [resumed, resumeRightState, hleftZero]
            · simp [resumed, resumeRightState, hleftContext]
            · simp [resumed, resumeRightState, hleftOne]
            · simp [resumed, resumeRightState, hleftTwo]
            · simp [resumed, resumeRightState, hleftInputLength]
            · exact hfitsRight
            · intro rightState hrightPc hrightIndex hrightStack
                hrightOutput hrightZero hrightContext hrightOne hrightTwo
                hrightInputLength
              rw [run_combineBranchState leftTree.code rightTree.code frames
                (extra := extra) rightState hrightPc
                (by simpa [combine] using hrightStack) hrightOutput
                hrightZero hrightTwo
                (by simpa [combine] using hcombinePayloadBits)
                (by simpa [combine] using hcombineFrameBits) hrestBits
                honeBits hleftCodeBits hinnerBits hbranchBits]
              apply hcontinue
                (combineBranchState leftTree.code rightTree.code frames
                  rightState)
              · rfl
              · simp [combineBranchState, hrightIndex]
                omega
              · simp [combineBranchState]
              · simp [combineBranchState]
                simpa [BalancedTraversalTree.code, total] using
                  (congrArg BalancedTraversalTree.code htree).symm
              · simp [combineBranchState, hrightZero]
              · simp [combineBranchState, hrightContext]
              · simp [combineBranchState, hrightOne]
              · simp [combineBranchState, hrightTwo]
              · simp [combineBranchState, hrightInputLength]

/-! ## Public entry point -/

private def generatedBalancedRangeEntryState
    (inputLength count context : ℕ)
    (state : NPOracleState) : NPOracleState :=
  let state1 := (state.write 11 inputLength).jump 1
  let state2 := (state1.write 1 count).jump 2
  let state3 := (state2.write 8 context).jump 3
  let state4 := (state3.write 0 0).jump 4
  let state5 := (state4.write 2 0).jump 5
  let state6 := (state5.write 7 0).jump 6
  let state7 := (state6.write 9 1).jump 7
  let state8 := (state7.write 10 2).jump 8
  let state9 := (state8.write 3 0).jump 9
  let state10 := (state9.write 4 0).jump 10
  let state11 := (state10.write 5 0).jump 11
  let state12 := (state11.write 6 0).jump 12
  state12.jump 13

private theorem run_generatedBalancedRangeSetup
    (inputLength count context : ℕ)
    {maximumBits extra : ℕ} (state : NPOracleState)
    (hpc : state.pc = 0)
    (hinput : state.registers 0 = generatedBalancedRangeInput count context)
    (hinputLength : state.registers 1 = inputLength)
    (hinputLengthBits : natBitLength inputLength ≤ maximumBits)
    (hcountBits : natBitLength count ≤ maximumBits)
    (hcontextBits : natBitLength context ≤ maximumBits)
    (hzeroBits : natBitLength 0 ≤ maximumBits)
    (honeBits : natBitLength 1 ≤ maximumBits)
    (htwoBits : natBitLength 2 ≤ maximumBits) :
    runNPOracleProgram generatedBalancedRangeProgram maximumBits
        (13 + extra) state =
      runNPOracleProgram generatedBalancedRangeProgram maximumBits extra
        (generatedBalancedRangeEntryState inputLength count context state) := by
  let state1 := (state.write 11 inputLength).jump 1
  let state2 := (state1.write 1 count).jump 2
  let state3 := (state2.write 8 context).jump 3
  let state4 := (state3.write 0 0).jump 4
  let state5 := (state4.write 2 0).jump 5
  let state6 := (state5.write 7 0).jump 6
  let state7 := (state6.write 9 1).jump 7
  let state8 := (state7.write 10 2).jump 8
  let state9 := (state8.write 3 0).jump 9
  let state10 := (state9.write 4 0).jump 10
  let state11 := (state10.write 5 0).jump 11
  let state12 := (state11.write 6 0).jump 12
  rw [show 13 + extra = (12 + extra) + 1 by omega]
  rw [run_copy_instruction (fuel := 12 + extra)
    (value := inputLength) (by rfl) hpc hinputLength hinputLengthBits]
  change
    runNPOracleProgram generatedBalancedRangeProgram maximumBits
        (12 + extra) state1 =
      runNPOracleProgram generatedBalancedRangeProgram maximumBits extra
        (generatedBalancedRangeEntryState inputLength count context state)
  rw [show 12 + extra = (11 + extra) + 1 by omega]
  rw [run_unpairLeft_instruction (fuel := 11 + extra)
    (value := count) (by rfl) rfl (by
      simp [state1, hinput, generatedBalancedRangeInput])
    hcountBits]
  change
    runNPOracleProgram generatedBalancedRangeProgram maximumBits
        (11 + extra) state2 =
      runNPOracleProgram generatedBalancedRangeProgram maximumBits extra
        (generatedBalancedRangeEntryState inputLength count context state)
  rw [show 11 + extra = (10 + extra) + 1 by omega]
  rw [run_unpairRight_instruction (fuel := 10 + extra)
    (value := context) (by rfl) rfl (by
      simp [state2, state1, hinput, generatedBalancedRangeInput])
    hcontextBits]
  change
    runNPOracleProgram generatedBalancedRangeProgram maximumBits
        (10 + extra) state3 =
      runNPOracleProgram generatedBalancedRangeProgram maximumBits extra
        (generatedBalancedRangeEntryState inputLength count context state)
  rw [show 10 + extra = (9 + extra) + 1 by omega]
  rw [run_set_instruction (fuel := 9 + extra) (by rfl) rfl hzeroBits]
  change
    runNPOracleProgram generatedBalancedRangeProgram maximumBits
        (9 + extra) state4 =
      runNPOracleProgram generatedBalancedRangeProgram maximumBits extra
        (generatedBalancedRangeEntryState inputLength count context state)
  rw [show 9 + extra = (8 + extra) + 1 by omega]
  rw [run_set_instruction (fuel := 8 + extra) (by rfl) rfl hzeroBits]
  change
    runNPOracleProgram generatedBalancedRangeProgram maximumBits
        (8 + extra) state5 =
      runNPOracleProgram generatedBalancedRangeProgram maximumBits extra
        (generatedBalancedRangeEntryState inputLength count context state)
  rw [show 8 + extra = (7 + extra) + 1 by omega]
  rw [run_set_instruction (fuel := 7 + extra) (by rfl) rfl hzeroBits]
  change
    runNPOracleProgram generatedBalancedRangeProgram maximumBits
        (7 + extra) state6 =
      runNPOracleProgram generatedBalancedRangeProgram maximumBits extra
        (generatedBalancedRangeEntryState inputLength count context state)
  rw [show 7 + extra = (6 + extra) + 1 by omega]
  rw [run_set_instruction (fuel := 6 + extra) (by rfl) rfl honeBits]
  change
    runNPOracleProgram generatedBalancedRangeProgram maximumBits
        (6 + extra) state7 =
      runNPOracleProgram generatedBalancedRangeProgram maximumBits extra
        (generatedBalancedRangeEntryState inputLength count context state)
  rw [show 6 + extra = (5 + extra) + 1 by omega]
  rw [run_set_instruction (fuel := 5 + extra) (by rfl) rfl htwoBits]
  change
    runNPOracleProgram generatedBalancedRangeProgram maximumBits
        (5 + extra) state8 =
      runNPOracleProgram generatedBalancedRangeProgram maximumBits extra
        (generatedBalancedRangeEntryState inputLength count context state)
  rw [show 5 + extra = (4 + extra) + 1 by omega]
  rw [run_set_instruction (fuel := 4 + extra) (by rfl) rfl hzeroBits]
  change
    runNPOracleProgram generatedBalancedRangeProgram maximumBits
        (4 + extra) state9 =
      runNPOracleProgram generatedBalancedRangeProgram maximumBits extra
        (generatedBalancedRangeEntryState inputLength count context state)
  rw [show 4 + extra = (3 + extra) + 1 by omega]
  rw [run_set_instruction (fuel := 3 + extra) (by rfl) rfl hzeroBits]
  change
    runNPOracleProgram generatedBalancedRangeProgram maximumBits
        (3 + extra) state10 =
      runNPOracleProgram generatedBalancedRangeProgram maximumBits extra
        (generatedBalancedRangeEntryState inputLength count context state)
  rw [show 3 + extra = (2 + extra) + 1 by omega]
  rw [run_set_instruction (fuel := 2 + extra) (by rfl) rfl hzeroBits]
  change
    runNPOracleProgram generatedBalancedRangeProgram maximumBits
        (2 + extra) state11 =
      runNPOracleProgram generatedBalancedRangeProgram maximumBits extra
        (generatedBalancedRangeEntryState inputLength count context state)
  rw [show 2 + extra = (1 + extra) + 1 by omega]
  rw [run_set_instruction (fuel := 1 + extra) (by rfl) rfl hzeroBits]
  change
    runNPOracleProgram generatedBalancedRangeProgram maximumBits
        (1 + extra) state12 =
      runNPOracleProgram generatedBalancedRangeProgram maximumBits extra
        (generatedBalancedRangeEntryState inputLength count context state)
  rw [show 1 + extra = extra + 1 by omega]
  rw [run_branchZero_instruction (fuel := extra) (by rfl) rfl]
  simp [state12, state11, state10, state9, state8, state7, state6,
    state5, state4, state3, state2, state1,
    generatedBalancedRangeEntryState]

private def generatedBalancedRangeFinishedState
    (treeCode context : ℕ) (state : NPOracleState) : NPOracleState :=
  let state1 := state.jump 46
  (state1.write 3 (Nat.pair treeCode context)).jump 47

private theorem run_generatedBalancedRangeFinish
    (treeCode context : ℕ)
    {maximumBits : ℕ} (state : NPOracleState)
    (hpc : state.pc = 30)
    (hstack : state.registers 2 = 0)
    (htree : state.registers 3 = treeCode)
    (hcontext : state.registers 8 = context)
    (houtputBits :
      natBitLength (Nat.pair treeCode context) ≤ maximumBits) :
    runNPOracleProgram generatedBalancedRangeProgram maximumBits 3 state =
      some (Nat.pair treeCode context) := by
  let state1 := state.jump 46
  let state2 := (state1.write 3 (Nat.pair treeCode context)).jump 47
  rw [show 3 = 2 + 1 by omega]
  rw [run_branchZero_instruction (fuel := 2) (by rfl) hpc]
  rw [hstack, if_pos rfl]
  change
    runNPOracleProgram generatedBalancedRangeProgram maximumBits 2 state1 =
      some (Nat.pair treeCode context)
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction (fuel := 1)
    (value := Nat.pair treeCode context) (by rfl) rfl (by
      simp [state1, htree, hcontext])
    houtputBits]
  change
    runNPOracleProgram generatedBalancedRangeProgram maximumBits 1 state2 =
      some (Nat.pair treeCode context)
  rw [show 1 = 0 + 1 by omega]
  exact run_halt_instruction (by rfl) rfl (by
    simp [state2, state1]) houtputBits

theorem run_generatedBalancedRangeProgram
    (inputLength count context : ℕ) :
    runNPOracleProgram generatedBalancedRangeProgram
        (generatedBalancedRangeRequiredBits inputLength count context)
        (generatedBalancedRangeFuel inputLength count context)
        (initialNPOracleState inputLength
          (generatedBalancedRangeInput count context)) =
      some (generatedBalancedRangeOutput inputLength count context) := by
  let tree := generatedBalancedRangeTree inputLength context 0 count
  let maximumBits :=
    generatedBalancedRangeRequiredBits inputLength count context
  let initial :=
    initialNPOracleState inputLength
      (generatedBalancedRangeInput count context)
  let entry :=
    generatedBalancedRangeEntryState inputLength count context initial
  have hinputLengthBits : natBitLength inputLength ≤ maximumBits := by
    apply generatedBalancedRangeRequiredBits_of_mem
    simp [generatedBalancedRangeExecutionValues]
  have hcountBits : natBitLength count ≤ maximumBits := by
    apply generatedBalancedRangeRequiredBits_of_mem
    simp [generatedBalancedRangeExecutionValues]
  have hcontextBits : natBitLength context ≤ maximumBits := by
    apply generatedBalancedRangeRequiredBits_of_mem
    simp [generatedBalancedRangeExecutionValues]
  have hzeroBits : natBitLength 0 ≤ maximumBits := by
    apply generatedBalancedRangeRequiredBits_of_mem
    simp [generatedBalancedRangeExecutionValues]
  have honeBits : natBitLength 1 ≤ maximumBits := by
    apply generatedBalancedRangeRequiredBits_of_mem
    simp [generatedBalancedRangeExecutionValues]
  have htwoBits : natBitLength 2 ≤ maximumBits := by
    apply generatedBalancedRangeRequiredBits_of_mem
    simp [generatedBalancedRangeExecutionValues]
  have hbuildFits : ∀ value,
      value ∈ generatedBalancedRangeBuildValues
          inputLength context 0 count [] →
        natBitLength value ≤ maximumBits := by
    intro value hvalue
    apply generatedBalancedRangeRequiredBits_of_mem
    simp [generatedBalancedRangeExecutionValues, hvalue]
  have houtputBits :
      natBitLength (Nat.pair tree.code context) ≤ maximumBits := by
    apply generatedBalancedRangeRequiredBits_of_mem
    simp [generatedBalancedRangeExecutionValues, tree]
  rw [show
    generatedBalancedRangeFuel inputLength count context =
      13 + (generatedBalancedRangeBuildFuel tree + 3) by
        simp [generatedBalancedRangeFuel, tree]
        omega]
  rw [run_generatedBalancedRangeSetup inputLength count context
    (extra := generatedBalancedRangeBuildFuel tree + 3) initial
    (by simp [initial, initialNPOracleState])
    (by simp [initial, initialNPOracleState])
    (by simp [initial, initialNPOracleState])
    hinputLengthBits hcountBits hcontextBits hzeroBits honeBits htwoBits]
  apply run_generatedBalancedRangeBuild inputLength context 0 count []
    (extra := 3) (output := generatedBalancedRangeOutput inputLength count context)
    entry
  · simp [entry, generatedBalancedRangeEntryState]
  · simp [entry, generatedBalancedRangeEntryState]
  · simp [entry, generatedBalancedRangeEntryState]
  · change 0 = 0
    rfl
  · simp [entry, generatedBalancedRangeEntryState]
  · simp [entry, generatedBalancedRangeEntryState]
  · simp [entry, generatedBalancedRangeEntryState]
  · simp [entry, generatedBalancedRangeEntryState]
  · simp [entry, generatedBalancedRangeEntryState]
  · exact hbuildFits
  · intro finalState hpc hindex hstack htree hzero hcontext hone htwo
      hinputLength
    change finalState.registers 2 = 0 at hstack
    have hfinish :=
      run_generatedBalancedRangeFinish
        (generatedBalancedRangeTree inputLength context 0 count).code
        context finalState hpc hstack htree hcontext
        (by simpa [tree] using houtputBits)
    rw [generatedBalancedRangeOutput,
      ← generatedBalancedRangeTree_code inputLength context 0 count]
    exact hfinish

/-! ## Fuel closure -/

theorem generatedBalancedRangeBuildFuel_eq
    (inputLength context first count : ℕ) :
    generatedBalancedRangeBuildFuel
        (generatedBalancedRangeTree inputLength context first count) =
      if count = 0 then 3 else 42 * count - 34 := by
  induction count using Nat.strong_induction_on generalizing first with
  | h count ih =>
      match count with
      | 0 =>
          simp [generatedBalancedRangeBuildFuel]
      | 1 =>
          norm_num [generatedBalancedRangeTree,
            generatedBalancedRangeBuildFuel]
      | rest + 2 =>
          let total := rest + 2
          let leftCount := (total + 1) / 2
          let rightCount := total / 2
          have hleftPositive : 0 < leftCount := by
            dsimp [leftCount, total]
            omega
          have hleftLt : leftCount < total := by
            dsimp [leftCount, total]
            omega
          have hrightPositive : 0 < rightCount := by
            dsimp [rightCount, total]
            omega
          have hrightLt : rightCount < total := by
            dsimp [rightCount, total]
            omega
          have hsplit : leftCount + rightCount = total := by
            dsimp [leftCount, rightCount, total]
            omega
          rw [generatedBalancedRangeTree]
          simp only [generatedBalancedRangeBuildFuel]
          rw [ih leftCount hleftLt, ih rightCount hrightLt]
          simp only [if_neg hleftPositive.ne', if_neg hrightPositive.ne']
          split
          · omega
          · omega

theorem generatedBalancedRangeFuel_le_linear
    (inputLength count context : ℕ) :
    generatedBalancedRangeFuel inputLength count context ≤
      42 * (count + 1) := by
  rw [generatedBalancedRangeFuel,
    generatedBalancedRangeBuildFuel_eq]
  split <;> omega

/-! ## Register-width closure -/

private theorem balancedTraversalTree_code_injective :
    Function.Injective BalancedTraversalTree.code := by
  intro left
  induction left with
  | empty =>
      intro right h
      cases right with
      | empty => rfl
      | leaf atom =>
          exfalso
          have hpositive := Nat.left_le_pair 1 atom
          simp [BalancedTraversalTree.code] at h
          omega
      | branch left right =>
          exfalso
          have hpositive :=
            Nat.left_le_pair 2 (Nat.pair left.code right.code)
          simp [BalancedTraversalTree.code] at h
          omega
  | leaf leftAtom =>
      intro right h
      cases right with
      | empty =>
          exfalso
          have hpositive := Nat.left_le_pair 1 leftAtom
          simp [BalancedTraversalTree.code] at h
          omega
      | leaf rightAtom =>
          simp [BalancedTraversalTree.code] at h
          simp [h]
      | branch rightLeft rightRight =>
          simp [BalancedTraversalTree.code] at h
  | branch leftLeft leftRight ihLeft ihRight =>
      intro right h
      cases right with
      | empty =>
          exfalso
          have hpositive :=
            Nat.left_le_pair 2 (Nat.pair leftLeft.code leftRight.code)
          simp [BalancedTraversalTree.code] at h
          omega
      | leaf rightAtom =>
          simp [BalancedTraversalTree.code] at h
      | branch rightLeft rightRight =>
          simp [BalancedTraversalTree.code] at h
          simp [ihLeft h.1, ihRight h.2]

theorem generatedBalancedRangeTree_eq_balancedTraversalTree
    (inputLength context first count : ℕ) :
    generatedBalancedRangeTree inputLength context first count =
      balancedTraversalTree
        (balancedRangeRequestAtoms inputLength context first count) := by
  apply balancedTraversalTree_code_injective
  rw [generatedBalancedRangeTree_code, balancedTraversalTree_code]

theorem generatedBalancedRangeTree_height_le_clog
    (inputLength context first count : ℕ) :
    (generatedBalancedRangeTree inputLength context first count).height ≤
      Nat.clog 2 count + 1 := by
  rw [generatedBalancedRangeTree_eq_balancedTraversalTree,
    balancedTraversalTree_height_eq]
  simpa using
    (balancedListHeight_le_clog
      (balancedRangeRequestAtoms inputLength context first count))

private def traversalFrameData : BalancedTraversalFrame → ℕ
  | .visitRight data => data
  | .combineLeft data => data

private theorem pairIter_mono_depth
    {first second value : ℕ} (hle : first ≤ second) :
    pairIter first value ≤ pairIter second value := by
  obtain ⟨difference, rfl⟩ := Nat.exists_eq_add_of_le hle
  rw [pairIter_add]
  exact value_le_pairIter difference _

private theorem pair_le_pairIter_succ
    {left right depth bound : ℕ}
    (hleft : left ≤ pairIter depth bound)
    (hright : right ≤ pairIter depth bound) :
    Nat.pair left right ≤ pairIter (depth + 1) bound := by
  rw [pairIter_succ_right]
  exact pair_mono hleft hright

private theorem encodeBalancedTraversalFrame_le
    (frame : BalancedTraversalFrame) (bound : ℕ)
    (hbound : 1 ≤ bound)
    (hdata : traversalFrameData frame ≤ bound) :
    encodeBalancedTraversalFrame frame ≤ pairIter 1 bound := by
  rw [pairIter_succ_right]
  simp only [pairIter]
  cases frame with
  | visitRight data =>
      exact pair_mono (by omega) hdata
  | combineLeft data =>
      exact pair_mono hbound hdata

private theorem encodeBalancedTraversalStack_le
    (frames : List BalancedTraversalFrame) (bound : ℕ)
    (hbound : 1 ≤ bound)
    (hdata : ∀ frame, frame ∈ frames →
      traversalFrameData frame ≤ bound) :
    encodeBalancedTraversalStack frames ≤
      pairIter (3 * frames.length) bound := by
  induction frames with
  | nil =>
      simp [encodeBalancedTraversalStack, encodeTaggedList]
  | cons frame frames ih =>
      have hframeData := hdata frame (by simp)
      have htailData : ∀ candidate, candidate ∈ frames →
          traversalFrameData candidate ≤ bound := by
        intro candidate hcandidate
        exact hdata candidate (by simp [hcandidate])
      have htail :=
        ih htailData
      have hframeOne :=
        encodeBalancedTraversalFrame_le frame bound hbound hframeData
      have hone :
          1 ≤ pairIter (3 * frames.length + 2) bound :=
        one_le_pairIter _ hbound
      have hframe :
          encodeBalancedTraversalFrame frame ≤
            pairIter (3 * frames.length + 1) bound :=
        hframeOne.trans <|
          pairIter_mono_depth (by omega)
      have htail' :
          encodeBalancedTraversalStack frames ≤
            pairIter (3 * frames.length + 1) bound :=
        htail.trans <|
          pairIter_mono_depth (by omega)
      have hpayload :
          Nat.pair (encodeBalancedTraversalFrame frame)
              (encodeBalancedTraversalStack frames) ≤
            pairIter (3 * frames.length + 2) bound :=
        pair_le_pairIter_succ hframe htail'
      have hstack :
          Nat.pair 1
              (Nat.pair (encodeBalancedTraversalFrame frame)
                (encodeBalancedTraversalStack frames)) ≤
            pairIter (3 * frames.length + 3) bound :=
        pair_le_pairIter_succ hone hpayload
      rw [encodeBalancedTraversalStack_cons]
      change
        Nat.pair 1
            (Nat.pair (encodeBalancedTraversalFrame frame)
              (encodeBalancedTraversalStack frames)) ≤
          pairIter (3 * (frames.length + 1)) bound
      rw [show 3 * (frames.length + 1) =
        3 * frames.length + 3 by omega]
      exact hstack

private theorem generatedBalancedRangeBuildValues_forall_le
    (inputLength context bound heightCap : ℕ)
    (hbound : 2 ≤ bound)
    (hinputLength : inputLength ≤ bound)
    (hcontext : context ≤ bound) :
    ∀ count first frames,
      first + count + 1 ≤ bound →
      (generatedBalancedRangeTree inputLength context first count).code ≤
        bound →
      (∀ frame, frame ∈ frames →
        traversalFrameData frame ≤ bound) →
      frames.length +
          (generatedBalancedRangeTree
            inputLength context first count).height ≤
        heightCap →
      (generatedBalancedRangeBuildValues
        inputLength context first count frames).Forall
          (fun value => value ≤ pairIter (3 * heightCap + 6) bound) := by
  intro count
  induction count using Nat.strong_induction_on with
  | h count ih =>
      intro first frames hindex htree hframes hheight
      have hlift :
          ∀ {depth value},
            value ≤ pairIter depth bound →
            depth ≤ 3 * heightCap + 6 →
            value ≤ pairIter (3 * heightCap + 6) bound := by
        intro depth value hvalue hdepth
        exact hvalue.trans (pairIter_mono_depth hdepth)
      have hbase :
          ∀ {value}, value ≤ bound →
            value ≤ pairIter (3 * heightCap + 6) bound := by
        intro value hvalue
        apply hlift (depth := 0)
        · simpa using hvalue
        · omega
      match count with
      | 0 =>
          simp [generatedBalancedRangeBuildValues]
      | 1 =>
          have hfirst : first ≤ bound := by omega
          have hinnerRaw :
              Nat.pair first context ≤ pairIter 1 bound := by
            simpa using
              (pair_le_pairIter_succ
                (depth := 0) hfirst hcontext)
          have hinner :
              Nat.pair first context ≤
                pairIter (3 * heightCap + 6) bound :=
            hlift hinnerRaw (by omega)
          have hatomRaw :
              balancedRangeRequestAtom inputLength first context ≤
                pairIter 2 bound := by
            apply pair_le_pairIter_succ
                (depth := 1)
            · exact hinputLength.trans (value_le_pairIter 1 bound)
            · exact hinnerRaw.trans (pairIter_mono_depth (by omega))
          have hatom :
              balancedRangeRequestAtom inputLength first context ≤
                pairIter (3 * heightCap + 6) bound :=
            hlift hatomRaw (by omega)
          have htaggedRaw :
              Nat.pair 1
                  (balancedRangeRequestAtom inputLength first context) ≤
                pairIter 3 bound := by
            apply pair_le_pairIter_succ
                (depth := 2)
            · exact one_le_pairIter 2 (by omega)
            · exact hatomRaw.trans (pairIter_mono_depth (by omega))
          have htagged :
              Nat.pair 1
                  (balancedRangeRequestAtom inputLength first context) ≤
                pairIter (3 * heightCap + 6) bound :=
            hlift htaggedRaw (by omega)
          simp only [generatedBalancedRangeBuildValues, List.forall_cons]
          exact
            ⟨hbase (by omega), hbase (Nat.zero_le bound), hinner, hatom,
              hbase (by omega), htagged, by simp⟩
      | rest + 2 =>
          let total := rest + 2
          let leftCount := (total + 1) / 2
          let rightCount := total / 2
          let leftTree :=
            generatedBalancedRangeTree inputLength context first leftCount
          let rightTree :=
            generatedBalancedRangeTree inputLength context
              (first + leftCount) rightCount
          let visit : BalancedTraversalFrame := .visitRight rightCount
          let combine : BalancedTraversalFrame := .combineLeft leftTree.code
          have hleftPositive : 0 < leftCount := by
            dsimp [leftCount, total]
            omega
          have hrightPositive : 0 < rightCount := by
            dsimp [rightCount, total]
            omega
          have hleftLt : leftCount < total := by
            dsimp [leftCount, total]
            omega
          have hrightLt : rightCount < total := by
            dsimp [rightCount, total]
            omega
          have hsplit : leftCount + rightCount = total := by
            dsimp [leftCount, rightCount, total]
            omega
          have htreeEq :
              generatedBalancedRangeTree
                  inputLength context first total =
                .branch leftTree rightTree := by
            simp [generatedBalancedRangeTree, total, leftCount, rightCount,
              leftTree, rightTree]
          have hbranchBound :
              Nat.pair 2 (Nat.pair leftTree.code rightTree.code) ≤ bound := by
            have htree' := htree
            rw [htreeEq] at htree'
            exact htree'
          have hleftCode : leftTree.code ≤ bound :=
            (Nat.left_le_pair leftTree.code rightTree.code).trans <|
              (Nat.right_le_pair 2
                (Nat.pair leftTree.code rightTree.code)).trans hbranchBound
          have hrightCode : rightTree.code ≤ bound :=
            (Nat.right_le_pair leftTree.code rightTree.code).trans <|
              (Nat.right_le_pair 2
                (Nat.pair leftTree.code rightTree.code)).trans hbranchBound
          have hheight' :
              frames.length +
                  (1 + max leftTree.height rightTree.height) ≤
                heightCap := by
            simpa [htreeEq, BalancedTraversalTree.height, total] using hheight
          have hframesSucc : frames.length + 1 ≤ heightCap := by
            omega
          have hstackRaw :=
            encodeBalancedTraversalStack_le frames bound (by omega) hframes
          have hstack :
              encodeBalancedTraversalStack frames ≤
                pairIter (3 * heightCap + 6) bound :=
            hlift hstackRaw (by omega)
          have htotal : total ≤ bound := by omega
          have htotalPred : total.pred ≤ bound :=
            (Nat.pred_le total).trans htotal
          have htotalSucc : total + 1 ≤ bound := by omega
          have hrightCount : rightCount ≤ bound := by omega
          have hleftCount : leftCount ≤ bound := by omega
          have hvisitData :
              traversalFrameData visit ≤ bound := by
            simpa [visit, traversalFrameData] using hrightCount
          have hvisitFrames :
              ∀ frame, frame ∈ visit :: frames →
                traversalFrameData frame ≤ bound := by
            intro frame hmem
            simp only [List.mem_cons] at hmem
            rcases hmem with rfl | hmem
            · exact hvisitData
            · exact hframes frame hmem
          have hvisitFrameRaw :
              encodeBalancedTraversalFrame visit ≤ pairIter 1 bound :=
            encodeBalancedTraversalFrame_le visit bound (by omega) hvisitData
          have hvisitFrameAligned :
              encodeBalancedTraversalFrame visit ≤
                pairIter (3 * frames.length + 1) bound :=
            hvisitFrameRaw.trans (pairIter_mono_depth (by omega))
          have hstackAligned :
              encodeBalancedTraversalStack frames ≤
                pairIter (3 * frames.length + 1) bound :=
            hstackRaw.trans (pairIter_mono_depth (by omega))
          have hvisitPayloadRaw :
              framePayload visit frames ≤
                pairIter (3 * frames.length + 2) bound := by
            simpa [framePayload] using
              (pair_le_pairIter_succ hvisitFrameAligned hstackAligned)
          have hvisitPayload :
              framePayload visit frames ≤
                pairIter (3 * heightCap + 6) bound :=
            hlift hvisitPayloadRaw (by omega)
          have hvisitStackRaw :
              encodeBalancedTraversalStack (visit :: frames) ≤
                pairIter (3 * (visit :: frames).length) bound :=
            encodeBalancedTraversalStack_le
              (visit :: frames) bound (by omega) hvisitFrames
          have hvisitStack :
              encodeBalancedTraversalStack (visit :: frames) ≤
                pairIter (3 * heightCap + 6) bound :=
            hlift hvisitStackRaw (by simp only [List.length_cons]; omega)
          have hcombineData :
              traversalFrameData combine ≤ bound := by
            simpa [combine, traversalFrameData] using hleftCode
          have hcombineFrames :
              ∀ frame, frame ∈ combine :: frames →
                traversalFrameData frame ≤ bound := by
            intro frame hmem
            simp only [List.mem_cons] at hmem
            rcases hmem with rfl | hmem
            · exact hcombineData
            · exact hframes frame hmem
          have hcombineFrameRaw :
              encodeBalancedTraversalFrame combine ≤ pairIter 1 bound :=
            encodeBalancedTraversalFrame_le
              combine bound (by omega) hcombineData
          have hcombineFrameAligned :
              encodeBalancedTraversalFrame combine ≤
                pairIter (3 * frames.length + 1) bound :=
            hcombineFrameRaw.trans (pairIter_mono_depth (by omega))
          have hcombinePayloadRaw :
              framePayload combine frames ≤
                pairIter (3 * frames.length + 2) bound := by
            simpa [framePayload] using
              (pair_le_pairIter_succ hcombineFrameAligned hstackAligned)
          have hcombinePayload :
              framePayload combine frames ≤
                pairIter (3 * heightCap + 6) bound :=
            hlift hcombinePayloadRaw (by omega)
          have hcombineStackRaw :
              encodeBalancedTraversalStack (combine :: frames) ≤
                pairIter (3 * (combine :: frames).length) bound :=
            encodeBalancedTraversalStack_le
              (combine :: frames) bound (by omega) hcombineFrames
          have hcombineStack :
              encodeBalancedTraversalStack (combine :: frames) ≤
                pairIter (3 * heightCap + 6) bound :=
            hlift hcombineStackRaw (by simp only [List.length_cons]; omega)
          have hinnerRaw :
              Nat.pair leftTree.code rightTree.code ≤ pairIter 1 bound := by
            simpa using
              (pair_le_pairIter_succ
                (depth := 0) hleftCode hrightCode)
          have hinner :
              Nat.pair leftTree.code rightTree.code ≤
                pairIter (3 * heightCap + 6) bound :=
            hlift hinnerRaw (by omega)
          have hbranchRaw :
              Nat.pair 2 (Nat.pair leftTree.code rightTree.code) ≤
                pairIter 2 bound := by
            apply pair_le_pairIter_succ
                (depth := 1)
            · exact (show 2 ≤ bound from hbound).trans
                (value_le_pairIter 1 bound)
            · exact hinnerRaw.trans (pairIter_mono_depth (by omega))
          have hbranch :
              Nat.pair 2 (Nat.pair leftTree.code rightTree.code) ≤
                pairIter (3 * heightCap + 6) bound :=
            hlift hbranchRaw (by omega)
          have hleftIndex : first + leftCount + 1 ≤ bound := by omega
          have hrightIndex :
              first + leftCount + rightCount + 1 ≤ bound := by omega
          have hleftHeight :
              (visit :: frames).length + leftTree.height ≤ heightCap := by
            simp only [List.length_cons]
            have := le_max_left leftTree.height rightTree.height
            omega
          have hrightHeight :
              (combine :: frames).length + rightTree.height ≤ heightCap := by
            simp only [List.length_cons]
            have := le_max_right leftTree.height rightTree.height
            omega
          have hleftValues :=
            ih leftCount hleftLt first (visit :: frames)
              hleftIndex hleftCode hvisitFrames hleftHeight
          have hrightValues :=
            ih rightCount hrightLt (first + leftCount) (combine :: frames)
              hrightIndex hrightCode hcombineFrames hrightHeight
          have hpre :
              [ total
              , total.pred
              , rightCount
              , total + 1
              , leftCount
              , encodeBalancedTraversalFrame visit
              , framePayload visit frames
              , encodeBalancedTraversalStack (visit :: frames)
              ].Forall
                (fun value =>
                  value ≤ pairIter (3 * heightCap + 6) bound) := by
            simp only [List.forall_cons]
            exact
              ⟨hbase htotal, hbase htotalPred, hbase hrightCount,
                hbase htotalSucc, hbase hleftCount,
                hlift hvisitFrameRaw (by omega), hvisitPayload,
                hvisitStack, by simp⟩
          have hmiddle :
              [ framePayload visit frames
              , encodeBalancedTraversalFrame visit
              , encodeBalancedTraversalStack frames
              , 0
              , rightCount
              , leftTree.code
              , encodeBalancedTraversalFrame combine
              , framePayload combine frames
              , encodeBalancedTraversalStack (combine :: frames)
              , rightCount
              ].Forall
                (fun value =>
                  value ≤ pairIter (3 * heightCap + 6) bound) := by
            simp only [List.forall_cons]
            exact
              ⟨hvisitPayload, hlift hvisitFrameRaw (by omega), hstack,
                hbase (Nat.zero_le bound), hbase hrightCount,
                hbase hleftCode, hlift hcombineFrameRaw (by omega),
                hcombinePayload, hcombineStack, hbase hrightCount, by simp⟩
          have hpost :
              [ framePayload combine frames
              , encodeBalancedTraversalFrame combine
              , encodeBalancedTraversalStack frames
              , 1
              , leftTree.code
              , Nat.pair leftTree.code rightTree.code
              , Nat.pair 2 (Nat.pair leftTree.code rightTree.code)
              ].Forall
                (fun value =>
                  value ≤ pairIter (3 * heightCap + 6) bound) := by
            simp only [List.forall_cons]
            exact
              ⟨hcombinePayload, hlift hcombineFrameRaw (by omega), hstack,
                hbase (by omega), hbase hleftCode, hinner, hbranch, by simp⟩
          rw [generatedBalancedRangeBuildValues.eq_def]
          simp only [List.forall_append]
          exact
            ⟨⟨⟨⟨by
              simpa [total, leftCount, rightCount, leftTree, rightTree, visit,
                combine] using hpre, by
              simpa [total, leftCount, rightCount, leftTree, rightTree, visit,
                combine] using hleftValues⟩, by
              simpa [total, leftCount, rightCount, leftTree, rightTree, visit,
                combine] using hmiddle⟩, by
              simpa [total, leftCount, rightCount, leftTree, rightTree, visit,
                combine] using hrightValues⟩, by
              simpa [total, leftCount, rightCount, leftTree, rightTree, visit,
                combine] using hpost⟩

/-- A single structural bound contains every unpaired input and completed
subtree code.  Pairing depth is accounted for separately, so sequential work
cannot inflate the width argument. -/
def generatedBalancedRangeInitialBound
    (inputLength count context : ℕ) : ℕ :=
  let tree := generatedBalancedRangeTree inputLength context 0 count
  max 2 (max inputLength (max context (max (count + 1) tree.code)))

def generatedBalancedRangeValueBound
    (inputLength count context : ℕ) : ℕ :=
  let tree := generatedBalancedRangeTree inputLength context 0 count
  pairIter (3 * tree.height + 6)
    (generatedBalancedRangeInitialBound inputLength count context)

private theorem generatedBalancedRangeExecutionValues_forall_le
    (inputLength count context : ℕ) :
    (generatedBalancedRangeExecutionValues inputLength count context).Forall
      (fun value =>
        value ≤ generatedBalancedRangeValueBound inputLength count context) := by
  let tree := generatedBalancedRangeTree inputLength context 0 count
  let bound :=
    generatedBalancedRangeInitialBound inputLength count context
  have hbound : 2 ≤ bound := by
    simp [bound, generatedBalancedRangeInitialBound]
  have hinputLength : inputLength ≤ bound := by
    simp [bound, generatedBalancedRangeInitialBound]
  have hcontext : context ≤ bound := by
    simp [bound, generatedBalancedRangeInitialBound]
  have hcount : count + 1 ≤ bound := by
    simp [bound, generatedBalancedRangeInitialBound]
  have htree : tree.code ≤ bound := by
    simp [bound, tree, generatedBalancedRangeInitialBound]
  have hbase :
      ∀ {value}, value ≤ bound →
        value ≤ generatedBalancedRangeValueBound inputLength count context := by
    intro value hvalue
    exact hvalue.trans <| by
      simp only [generatedBalancedRangeValueBound]
      exact value_le_pairIter (3 * tree.height + 6) bound
  have hbuild :
      (generatedBalancedRangeBuildValues
        inputLength context 0 count []).Forall
          (fun value =>
            value ≤
              generatedBalancedRangeValueBound inputLength count context) := by
    simpa only [generatedBalancedRangeValueBound, tree] using
      generatedBalancedRangeBuildValues_forall_le
        inputLength context bound tree.height hbound hinputLength hcontext
        count 0 []
        (by simpa using hcount)
        (by simpa [tree] using htree)
        (by simp)
        (by simp [tree])
  have hprefix :
      [inputLength, count, context, 0, 1, 2].Forall
        (fun value =>
          value ≤
            generatedBalancedRangeValueBound inputLength count context) := by
    simp only [List.forall_cons]
    exact
      ⟨hbase hinputLength, hbase (by omega), hbase hcontext,
        hbase (Nat.zero_le bound), hbase (by omega), hbase hbound, by simp⟩
  have houtputRaw :
      Nat.pair tree.code context ≤ pairIter 1 bound := by
    change Nat.pair tree.code context ≤ Nat.pair bound bound
    exact pair_mono htree hcontext
  have houtput :
      Nat.pair tree.code context ≤
        generatedBalancedRangeValueBound inputLength count context := by
    exact houtputRaw.trans <| by
      simp only [generatedBalancedRangeValueBound]
      apply pairIter_mono_depth
      omega
  have hsuffix :
      [tree.code, Nat.pair tree.code context].Forall
        (fun value =>
          value ≤
            generatedBalancedRangeValueBound inputLength count context) := by
    simp only [List.forall_cons]
    exact ⟨hbase htree, houtput, by simp⟩
  rw [generatedBalancedRangeExecutionValues]
  simp only [List.forall_append]
  exact
    ⟨⟨hprefix, hbuild⟩, by
      simpa [tree] using hsuffix⟩

private theorem foldr_max_map_natBitLength_le
    {values : List ℕ} {bound : ℕ}
    (hvalues : values.Forall (fun value => value ≤ bound)) :
    (values.map natBitLength).foldr max 0 ≤ natBitLength bound := by
  induction values with
  | nil => simp
  | cons head tail ih =>
      rw [List.forall_cons] at hvalues
      simp only [List.map, List.foldr]
      apply max_le
      · exact natBitLength_mono hvalues.1
      · exact ih hvalues.2

/-- The exact maximum-bit parameter used by the execution theorem is bounded
by a height-sensitive structural cap. -/
theorem generatedBalancedRangeRequiredBits_le_valueBound
    (inputLength count context : ℕ) :
    generatedBalancedRangeRequiredBits inputLength count context ≤
      natBitLength
        (generatedBalancedRangeValueBound inputLength count context) := by
  exact foldr_max_map_natBitLength_le
    (generatedBalancedRangeExecutionValues_forall_le
      inputLength count context)

private theorem pairIter_bits_le
    (depth value : ℕ) :
    natBitLength (pairIter depth value) ≤
      2 ^ depth * natBitLength value := by
  induction depth generalizing value with
  | zero => simp
  | succ depth ih =>
      calc
        natBitLength (pairIter (depth + 1) value) =
            natBitLength (pairIter depth (Nat.pair value value)) := rfl
        _ ≤ 2 ^ depth * natBitLength (Nat.pair value value) := ih _
        _ ≤ 2 ^ depth * (2 * natBitLength value) := by
          apply Nat.mul_le_mul_left
          simpa using pairCodeBits_le value value
        _ = 2 ^ (depth + 1) * natBitLength value := by
          rw [pow_succ]
          ring

private theorem generatedBalancedRange_two_pow_clog_le
    (length : ℕ) :
    2 ^ Nat.clog 2 length ≤ 2 * (length + 1) := by
  by_cases hsmall : length ≤ 1
  · have hclog : Nat.clog 2 length = 0 :=
      Nat.clog_of_right_le_one hsmall 2
    simp [hclog]
    omega
  · have hlarge : 1 < length := by omega
    have hpred :=
      Nat.pow_pred_clog_lt_self (b := 2) (by omega) hlarge
    have hpositive : 0 < Nat.clog 2 length :=
      Nat.clog_pos (by omega) hlarge
    have heq :
        (Nat.clog 2 length).pred + 1 = Nat.clog 2 length :=
      Nat.succ_pred_eq_of_pos hpositive
    rw [← heq, pow_succ]
    nlinarith

private theorem generatedBalancedRange_depthPower_le
    (inputLength count context : ℕ) :
    2 ^ (3 *
          (generatedBalancedRangeTree
            inputLength context 0 count).height + 6) ≤
      4096 * (count + 1) ^ 3 := by
  let height :=
    (generatedBalancedRangeTree inputLength context 0 count).height
  have hheight : height ≤ Nat.clog 2 count + 1 := by
    simpa [height] using
      generatedBalancedRangeTree_height_le_clog
        inputLength context 0 count
  have hheightPower :
      2 ^ height ≤ 4 * (count + 1) := by
    calc
      2 ^ height ≤ 2 ^ (Nat.clog 2 count + 1) :=
        Nat.pow_le_pow_right (by omega) hheight
      _ = 2 ^ Nat.clog 2 count * 2 := by rw [pow_succ]
      _ ≤ (2 * (count + 1)) * 2 :=
        Nat.mul_le_mul_right 2
          (generatedBalancedRange_two_pow_clog_le count)
      _ = 4 * (count + 1) := by ring
  calc
    2 ^ (3 *
          (generatedBalancedRangeTree
            inputLength context 0 count).height + 6) =
        64 * (2 ^ height) ^ 3 := by
      dsimp only [height]
      rw [pow_add, show
        3 *
            (generatedBalancedRangeTree
              inputLength context 0 count).height =
          (generatedBalancedRangeTree
            inputLength context 0 count).height * 3 by omega,
        pow_mul]
      norm_num
      ring
    _ ≤ 64 * (4 * (count + 1)) ^ 3 :=
      Nat.mul_le_mul_left 64 (Nat.pow_le_pow_left hheightPower 3)
    _ = 4096 * (count + 1) ^ 3 := by ring

/-- Explicit polynomial-width closure for the balanced range generator.  The
remaining factor is the bit width of the unpaired inputs and canonical output
tree; no runtime-length or linked-list depth appears. -/
theorem generatedBalancedRangeRequiredBits_le_polynomial
    (inputLength count context : ℕ) :
    generatedBalancedRangeRequiredBits inputLength count context ≤
      4096 * (count + 1) ^ 3 *
        natBitLength
          (generatedBalancedRangeInitialBound
            inputLength count context) := by
  let tree := generatedBalancedRangeTree inputLength context 0 count
  let bound :=
    generatedBalancedRangeInitialBound inputLength count context
  calc
    generatedBalancedRangeRequiredBits inputLength count context ≤
        natBitLength
          (generatedBalancedRangeValueBound
            inputLength count context) :=
      generatedBalancedRangeRequiredBits_le_valueBound
        inputLength count context
    _ = natBitLength (pairIter (3 * tree.height + 6) bound) := by
      rfl
    _ ≤ 2 ^ (3 * tree.height + 6) * natBitLength bound :=
      pairIter_bits_le _ _
    _ ≤ 4096 * (count + 1) ^ 3 * natBitLength bound :=
      Nat.mul_le_mul_right _
        (by simpa [tree] using
          generatedBalancedRange_depthPower_le inputLength count context)

/-- Uniform width of one generated request atom when its index is bounded. -/
def generatedBalancedRangeAtomBitEnvelope
    (inputLength indexBound context : ℕ) : ℕ :=
  4 * (natBitLength inputLength + natBitLength indexBound +
    natBitLength context)

theorem balancedRangeRequestAtom_bits_le
    (inputLength index context indexBound : ℕ)
    (hindex : index ≤ indexBound) :
    natBitLength
        (balancedRangeRequestAtom inputLength index context) ≤
      generatedBalancedRangeAtomBitEnvelope
        inputLength indexBound context := by
  have hindexBits :
      natBitLength index ≤ natBitLength indexBound :=
    natBitLength_mono hindex
  have hinner :=
    pairCodeBits_le index context
  have hinnerMax :
      max (natBitLength index) (natBitLength context) ≤
        natBitLength indexBound + natBitLength context := by
    apply max_le
    · omega
    · omega
  have hinner' :
      natBitLength (Nat.pair index context) ≤
        2 * (natBitLength indexBound + natBitLength context) :=
    hinner.trans (Nat.mul_le_mul_left 2 hinnerMax)
  have houter :=
    pairCodeBits_le inputLength (Nat.pair index context)
  have houterMax :
      max (natBitLength inputLength)
          (natBitLength (Nat.pair index context)) ≤
        natBitLength inputLength +
          2 * (natBitLength indexBound + natBitLength context) := by
    apply max_le
    · omega
    · omega
  calc
    natBitLength
        (balancedRangeRequestAtom inputLength index context) ≤
      2 * (natBitLength inputLength +
        2 * (natBitLength indexBound + natBitLength context)) := by
          simpa [balancedRangeRequestAtom] using
            houter.trans (Nat.mul_le_mul_left 2 houterMax)
    _ ≤ generatedBalancedRangeAtomBitEnvelope
          inputLength indexBound context := by
      simp only [generatedBalancedRangeAtomBitEnvelope]
      omega

private theorem balancedRangeRequestAtoms_sum_bits_le
    (inputLength context first count indexBound : ℕ)
    (hindices : first + count ≤ indexBound) :
    ((balancedRangeRequestAtoms inputLength context first count).map
      natBitLength).sum ≤
      count *
        generatedBalancedRangeAtomBitEnvelope
          inputLength indexBound context := by
  induction count generalizing first with
  | zero =>
      simp [balancedRangeRequestAtoms]
  | succ count ih =>
      have hfirst : first ≤ indexBound := by omega
      have htailIndices : first + 1 + count ≤ indexBound := by omega
      have hhead :=
        balancedRangeRequestAtom_bits_le
          inputLength first context indexBound hfirst
      have htail := ih (first + 1) htailIndices
      simp only [balancedRangeRequestAtoms_succ, List.map_cons,
        List.sum_cons]
      calc
        natBitLength (balancedRangeRequestAtom inputLength first context) +
            ((balancedRangeRequestAtoms
              inputLength context (first + 1) count).map natBitLength).sum ≤
          generatedBalancedRangeAtomBitEnvelope
              inputLength indexBound context +
            count * generatedBalancedRangeAtomBitEnvelope
              inputLength indexBound context :=
          Nat.add_le_add hhead htail
        _ = (count + 1) *
            generatedBalancedRangeAtomBitEnvelope
              inputLength indexBound context := by ring

private theorem natBitLength_max_le_add (left right : ℕ) :
    natBitLength (max left right) ≤
      natBitLength left + natBitLength right := by
  rcases le_total left right with hle | hle
  · rw [max_eq_right hle]
    omega
  · rw [max_eq_left hle]
    omega

/-- The structural base itself has an explicit polynomial bit envelope. -/
theorem generatedBalancedRangeInitialBound_bits_le
    (inputLength count context : ℕ) :
    natBitLength
        (generatedBalancedRangeInitialBound inputLength count context) ≤
      natBitLength 2 + natBitLength inputLength +
        natBitLength context + natBitLength (count + 1) +
        (1 + 2 * count ^ 4 *
          (count *
              generatedBalancedRangeAtomBitEnvelope
                inputLength count context + 1)) := by
  let atoms := balancedRangeRequestAtoms inputLength context 0 count
  let tree := generatedBalancedRangeTree inputLength context 0 count
  have hatomSum :
      (atoms.map natBitLength).sum ≤
        count *
          generatedBalancedRangeAtomBitEnvelope
            inputLength count context := by
    simpa [atoms] using
      balancedRangeRequestAtoms_sum_bits_le
        inputLength context 0 count count (by omega)
  have hatomBits :
      balancedListAtomBits atoms ≤
        count *
            generatedBalancedRangeAtomBitEnvelope
              inputLength count context + 1 := by
    simp only [balancedListAtomBits]
    exact Nat.add_le_add_right hatomSum 1
  have htreeBits :
      natBitLength tree.code ≤
        1 + 2 * count ^ 4 *
          (count *
              generatedBalancedRangeAtomBitEnvelope
                inputLength count context + 1) := by
    calc
      natBitLength tree.code =
          natBitLength (encodeBalancedList atoms) := by
        rw [generatedBalancedRangeTree_code]
      _ ≤ 1 + 2 * atoms.length ^ 4 * balancedListAtomBits atoms :=
        balancedListCodeBits_le atoms
      _ ≤ 1 + 2 * count ^ 4 *
          (count *
              generatedBalancedRangeAtomBitEnvelope
                inputLength count context + 1) := by
        rw [show atoms.length = count by simp [atoms]]
        gcongr
  let tail₃ := max (count + 1) tree.code
  let tail₂ := max context tail₃
  let tail₁ := max inputLength tail₂
  calc
    natBitLength
        (generatedBalancedRangeInitialBound inputLength count context) =
        natBitLength (max 2 tail₁) := by
      rfl
    _ ≤ natBitLength 2 + natBitLength tail₁ :=
      natBitLength_max_le_add 2 tail₁
    _ ≤ natBitLength 2 +
        (natBitLength inputLength + natBitLength tail₂) :=
      Nat.add_le_add_left
        (natBitLength_max_le_add inputLength tail₂) _
    _ ≤ natBitLength 2 +
        (natBitLength inputLength +
          (natBitLength context + natBitLength tail₃)) := by
      gcongr
      exact natBitLength_max_le_add context tail₃
    _ ≤ natBitLength 2 +
        (natBitLength inputLength +
          (natBitLength context +
            (natBitLength (count + 1) + natBitLength tree.code))) := by
      gcongr
      exact natBitLength_max_le_add (count + 1) tree.code
    _ ≤ natBitLength 2 + natBitLength inputLength +
        natBitLength context + natBitLength (count + 1) +
        (1 + 2 * count ^ 4 *
          (count *
              generatedBalancedRangeAtomBitEnvelope
                inputLength count context + 1)) := by
      omega

/-- Fully explicit polynomial maximum-bit bound for the exact generator trace. -/
theorem generatedBalancedRangeRequiredBits_le_explicitPolynomial
    (inputLength count context : ℕ) :
    generatedBalancedRangeRequiredBits inputLength count context ≤
      4096 * (count + 1) ^ 3 *
        (natBitLength 2 + natBitLength inputLength +
          natBitLength context + natBitLength (count + 1) +
          (1 + 2 * count ^ 4 *
            (count *
                generatedBalancedRangeAtomBitEnvelope
                  inputLength count context + 1))) := by
  exact
    (generatedBalancedRangeRequiredBits_le_polynomial
      inputLength count context).trans <|
        Nat.mul_le_mul_left (4096 * (count + 1) ^ 3)
          (generatedBalancedRangeInitialBound_bits_le
            inputLength count context)

end NearCubicWires.GeneratedBalancedRangeProgram
