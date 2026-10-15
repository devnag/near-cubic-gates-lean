import Proof.Circuits.CanonicalBalancedTraversal

namespace NearCubicWires.BalancedClauseStreamFlattenProgram

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock

def balancedClauseStreamFlattenProgram : NPOracleProgram :=
  [ .branchZero 0 13 1
  , .unpairLeft 0 8 2
  , .decrement 8 3
  , .branchZero 8 28 22
  , .branchZero 3 12 5
  , .unpairRight 3 6 6
  , .unpairLeft 6 7 7
  , .unpairRight 6 3 8
  , .pair 7 4 10 9
  , .set 9 1 10
  , .pair 9 10 4 11
  , .branchZero 9 4 4
  , .branchZero 11 13 14
  , .branchZero 2 15 18
  , .halt 4
  , .copy 4 3 16
  , .set 4 0 17
  , .set 11 1 4
  , .unpairRight 2 6 19
  , .unpairLeft 6 0 20
  , .unpairRight 6 2 21
  , .branchZero 9 0 0
  , .unpairRight 0 6 23
  , .unpairLeft 6 0 24
  , .unpairRight 6 3 25
  , .pair 3 2 10 26
  , .set 9 1 27
  , .pair 9 10 2 0
  , .unpairRight 0 3 4
  ]

@[simp] theorem balancedClauseStreamFlattenProgram_length :
    balancedClauseStreamFlattenProgram.length = 29 := by
  rfl

theorem balancedClauseStreamFlattenProgram_oracleFree :
    OracleFree balancedClauseStreamFlattenProgram := by
  rfl

def streamOfCode (code : ℕ) : List ℕ :=
  (decodeTaggedList code).getD []

@[simp] theorem streamOfCode_encodeTaggedList (values : List ℕ) :
    streamOfCode (encodeTaggedList values) = values := by
  simp [streamOfCode]

def treeStreamValues (tree : BalancedTraversalTree) : List ℕ :=
  tree.atoms.flatMap streamOfCode

def forestStreamValues (forest : List BalancedTraversalTree) : List ℕ :=
  forest.flatMap treeStreamValues

private def forestAtoms (forest : List BalancedTraversalTree) : List ℕ :=
  forest.flatMap BalancedTraversalTree.atoms

private def innerWrites : List ℕ → List ℕ → List ℕ
  | [], _accumulator => []
  | value :: rest, accumulator =>
      let payload := Nat.pair value (encodeTaggedList rest)
      let accumulatorPayload :=
        Nat.pair value (encodeTaggedList accumulator)
      let nextAccumulator := encodeTaggedList (value :: accumulator)
      [payload, value, encodeTaggedList rest, accumulatorPayload, 1,
        nextAccumulator] ++
        innerWrites rest (value :: accumulator)

private def popWrites
    (rest : List BalancedTraversalTree) : List ℕ :=
  match rest with
  | [] => []
  | next :: tail =>
      let tailCode := encodeTaggedList (tail.map BalancedTraversalTree.code)
      let payload := Nat.pair next.code tailCode
      [payload, next.code, tailCode]

def popFuel : List BalancedTraversalTree → ℕ
  | [] => 0
  | _ :: _ => 5

def phaseFuel : List BalancedTraversalTree → ℕ
  | [] => 0
  | .empty :: rest =>
      1 + popFuel rest + phaseFuel rest
  | .leaf atom :: rest =>
      5 + (8 * (streamOfCode atom).length + 2) +
        popFuel rest + phaseFuel rest
  | .branch left right :: rest =>
      10 + phaseFuel (left :: right :: rest)
termination_by forest =>
  (forest.map BalancedTraversalTree.nodeCount).sum
decreasing_by
  all_goals
    simp_wf
    simp [BalancedTraversalTree.nodeCount]
    try omega

private def phaseWrites :
    List BalancedTraversalTree → List ℕ → List ℕ
  | [], _accumulator => []
  | .empty :: rest, accumulator =>
      popWrites rest ++ phaseWrites rest accumulator
  | .leaf atom :: rest, accumulator =>
      let stream := streamOfCode atom
      [1, 0, atom] ++ innerWrites stream accumulator ++
        popWrites rest ++
        phaseWrites rest (stream.reverse ++ accumulator)
  | .branch left right :: rest, accumulator =>
      let stackCode :=
        encodeTaggedList (rest.map BalancedTraversalTree.code)
      let payload := Nat.pair left.code right.code
      let stackPayload := Nat.pair right.code stackCode
      let nextStack :=
        encodeTaggedList (right.code :: rest.map BalancedTraversalTree.code)
      [2, 1, payload, left.code, right.code, stackPayload, 1,
        nextStack] ++
        phaseWrites (left :: right :: rest) accumulator
termination_by forest _ =>
  (forest.map BalancedTraversalTree.nodeCount).sum
decreasing_by
  all_goals
    simp_wf
    simp [BalancedTraversalTree.nodeCount]
    try omega

def balancedClauseStreamFlattenFuel
    (streams : List (List ℕ)) : ℕ :=
  let tree :=
    balancedTraversalTree (streams.map encodeTaggedList)
  phaseFuel [tree] + 8 * streams.flatten.length + 7

private def balancedClauseStreamFlattenWorkingValues
    (streams : List (List ℕ)) : List ℕ :=
  let tree :=
    balancedTraversalTree (streams.map encodeTaggedList)
  let output := encodeTaggedList streams.flatten
  let reverse := encodeTaggedList streams.flatten.reverse
  [tree.code, output, 0, 1, 2] ++ phaseWrites [tree] [] ++
    [reverse, 0, 1] ++ innerWrites streams.flatten.reverse []

private def balancedClauseStreamFlattenWorkBound
    (streams : List (List ℕ)) : ℕ :=
  (balancedClauseStreamFlattenWorkingValues streams).foldr max 0

def balancedClauseStreamFlattenMaximumBits
    (streams : List (List ℕ)) : ℕ :=
  natBitLength (balancedClauseStreamFlattenWorkBound streams)

private theorem member_le_foldr_max
    {value : ℕ} {values : List ℕ} (hmem : value ∈ values) :
    value ≤ values.foldr max 0 := by
  induction values with
  | nil => simp at hmem
  | cons head tail ih =>
      simp only [List.mem_cons] at hmem
      simp only [List.foldr_cons]
      rcases hmem with rfl | hmem
      · exact Nat.le_max_left _ _
      · exact (ih hmem).trans (Nat.le_max_right _ _)

private theorem workingValue_fits
    (streams : List (List ℕ)) {value : ℕ}
    (hmem :
      value ∈ balancedClauseStreamFlattenWorkingValues streams) :
    natBitLength value ≤
      balancedClauseStreamFlattenMaximumBits streams := by
  unfold balancedClauseStreamFlattenMaximumBits
    balancedClauseStreamFlattenWorkBound
  exact natBitLength_mono (member_le_foldr_max hmem)

private theorem taggedCons_ne_zero (value : ℕ) (rest : List ℕ) :
    encodeTaggedList (value :: rest) ≠ 0 := by
  have hpositive :
      0 < Nat.pair 1 (Nat.pair value (encodeTaggedList rest)) :=
    lt_of_lt_of_le (by omega) <|
      Nat.left_le_pair 1
        (Nat.pair value (encodeTaggedList rest))
  simpa only [encodeTaggedList] using hpositive.ne'

private def foldState :
    List ℕ → List ℕ → NPOracleState → NPOracleState
  | [], _accumulator, state => state
  | value :: rest, accumulator, state =>
      let payload := Nat.pair value (encodeTaggedList rest)
      let accumulatorPayload :=
        Nat.pair value (encodeTaggedList accumulator)
      let nextAccumulator := encodeTaggedList (value :: accumulator)
      let state1 := state.jump 5
      let state2 := (state1.write 6 payload).jump 6
      let state3 := (state2.write 7 value).jump 7
      let state4 :=
        (state3.write 3 (encodeTaggedList rest)).jump 8
      let state5 := (state4.write 10 accumulatorPayload).jump 9
      let state6 := (state5.write 9 1).jump 10
      let state7 := (state6.write 4 nextAccumulator).jump 11
      let state8 := state7.jump 4
      foldState rest (value :: accumulator) state8

@[simp] private theorem foldState_pc
    (values accumulator : List ℕ) (state : NPOracleState)
    (hpc : state.pc = 4) :
    (foldState values accumulator state).pc = 4 := by
  induction values generalizing accumulator state with
  | nil => exact hpc
  | cons value rest ih =>
      simp only [foldState]
      exact ih (value :: accumulator) _ rfl

@[simp] private theorem foldState_cursor
    (values accumulator : List ℕ) (state : NPOracleState)
    (hcursor : state.registers 3 = encodeTaggedList values) :
    (foldState values accumulator state).registers 3 = 0 := by
  induction values generalizing accumulator state with
  | nil => simpa only [foldState, encodeTaggedList] using hcursor
  | cons value rest ih =>
      simp only [foldState]
      apply ih (value :: accumulator)
      simp [NPOracleState.write, NPOracleState.jump]

@[simp] private theorem foldState_accumulator
    (values accumulator : List ℕ) (state : NPOracleState)
    (haccumulator :
      state.registers 4 = encodeTaggedList accumulator) :
    (foldState values accumulator state).registers 4 =
      encodeTaggedList (values.reverse ++ accumulator) := by
  induction values generalizing accumulator state with
  | nil =>
      simpa only [foldState, List.reverse_nil, List.nil_append] using
        haccumulator
  | cons value rest ih =>
      simp only [foldState]
      rw [show (value :: rest).reverse ++ accumulator =
          rest.reverse ++ value :: accumulator by
        simp [List.reverse_cons, List.append_assoc]]
      apply ih (value :: accumulator)
      rfl

@[simp] private theorem foldState_current
    (values accumulator : List ℕ) (state : NPOracleState) :
    (foldState values accumulator state).registers 0 =
      state.registers 0 := by
  induction values generalizing accumulator state with
  | nil => rfl
  | cons value rest ih =>
      simp only [foldState]
      rw [ih]
      simp [NPOracleState.write, NPOracleState.jump]

@[simp] private theorem foldState_stack
    (values accumulator : List ℕ) (state : NPOracleState) :
    (foldState values accumulator state).registers 2 =
      state.registers 2 := by
  induction values generalizing accumulator state with
  | nil => rfl
  | cons value rest ih =>
      simp only [foldState]
      rw [ih]
      simp [NPOracleState.write, NPOracleState.jump]

@[simp] private theorem foldState_mode
    (values accumulator : List ℕ) (state : NPOracleState) :
    (foldState values accumulator state).registers 11 =
      state.registers 11 := by
  induction values generalizing accumulator state with
  | nil => rfl
  | cons value rest ih =>
      simp only [foldState]
      rw [ih]
      simp [NPOracleState.write, NPOracleState.jump]

private theorem run_foldItems
    (values accumulator : List ℕ) {maximumBits : ℕ}
    (state : NPOracleState)
    (hpc : state.pc = 4)
    (hcursor : state.registers 3 = encodeTaggedList values)
    (haccumulator :
      state.registers 4 = encodeTaggedList accumulator)
    (hfit :
      ∀ value, value ∈ innerWrites values accumulator →
        natBitLength value ≤ maximumBits) :
    RunsToIn balancedClauseStreamFlattenProgram maximumBits
      (8 * values.length) state
      (foldState values accumulator state) := by
  induction values generalizing accumulator state with
  | nil =>
      simpa [foldState] using
        (RunsToIn.refl balancedClauseStreamFlattenProgram
          maximumBits state)
  | cons value rest inductionHypothesis =>
      let payload := Nat.pair value (encodeTaggedList rest)
      let accumulatorPayload :=
        Nat.pair value (encodeTaggedList accumulator)
      let nextAccumulator := encodeTaggedList (value :: accumulator)
      let state1 := state.jump 5
      let state2 := (state1.write 6 payload).jump 6
      let state3 := (state2.write 7 value).jump 7
      let state4 :=
        (state3.write 3 (encodeTaggedList rest)).jump 8
      let state5 := (state4.write 10 accumulatorPayload).jump 9
      let state6 := (state5.write 9 1).jump 10
      let state7 := (state6.write 4 nextAccumulator).jump 11
      let state8 := state7.jump 4
      have hpayloadBits : natBitLength payload ≤ maximumBits :=
        hfit payload (by simp [innerWrites, payload])
      have hvalueBits : natBitLength value ≤ maximumBits :=
        hfit value (by simp [innerWrites])
      have hrestBits :
          natBitLength (encodeTaggedList rest) ≤ maximumBits :=
        hfit (encodeTaggedList rest) (by simp [innerWrites])
      have haccumulatorPayloadBits :
          natBitLength accumulatorPayload ≤ maximumBits :=
        hfit accumulatorPayload (by
          simp [innerWrites, accumulatorPayload])
      have honeBits : natBitLength 1 ≤ maximumBits :=
        hfit 1 (by simp [innerWrites])
      have hnextAccumulatorBits :
          natBitLength nextAccumulator ≤ maximumBits :=
        hfit nextAccumulator (by simp [innerWrites, nextAccumulator])
      have hstep :
          RunsToIn balancedClauseStreamFlattenProgram maximumBits
            8 state state8 := by
        intro extra
        rw [show 8 + extra = (7 + extra) + 1 by omega]
        rw [run_branchZero_instruction
          (fuel := 7 + extra) (by rfl) hpc]
        rw [hcursor, if_neg (taggedCons_ne_zero value rest)]
        change
          runNPOracleProgram balancedClauseStreamFlattenProgram
              maximumBits (7 + extra) state1 =
            runNPOracleProgram balancedClauseStreamFlattenProgram
              maximumBits extra state8
        rw [show 7 + extra = (6 + extra) + 1 by omega]
        rw [run_unpairRight_instruction (value := payload)
          (fuel := 6 + extra) (by rfl) rfl
          (by simp [state1, hcursor, payload, encodeTaggedList])
          hpayloadBits]
        change
          runNPOracleProgram balancedClauseStreamFlattenProgram
              maximumBits (6 + extra) state2 =
            runNPOracleProgram balancedClauseStreamFlattenProgram
              maximumBits extra state8
        rw [show 6 + extra = (5 + extra) + 1 by omega]
        rw [run_unpairLeft_instruction (value := value)
          (fuel := 5 + extra) (by rfl) rfl
          (by simp [state2, state1, payload]) hvalueBits]
        change
          runNPOracleProgram balancedClauseStreamFlattenProgram
              maximumBits (5 + extra) state3 =
            runNPOracleProgram balancedClauseStreamFlattenProgram
              maximumBits extra state8
        rw [show 5 + extra = (4 + extra) + 1 by omega]
        rw [run_unpairRight_instruction
          (value := encodeTaggedList rest)
          (fuel := 4 + extra) (by rfl) rfl
          (by simp [state3, state2, state1, payload]) hrestBits]
        change
          runNPOracleProgram balancedClauseStreamFlattenProgram
              maximumBits (4 + extra) state4 =
            runNPOracleProgram balancedClauseStreamFlattenProgram
              maximumBits extra state8
        rw [show 4 + extra = (3 + extra) + 1 by omega]
        rw [run_pair_instruction (value := accumulatorPayload)
          (fuel := 3 + extra) (by rfl) rfl
          (by
            simp [state4, state3, state2, state1, haccumulator,
              accumulatorPayload])
          haccumulatorPayloadBits]
        change
          runNPOracleProgram balancedClauseStreamFlattenProgram
              maximumBits (3 + extra) state5 =
            runNPOracleProgram balancedClauseStreamFlattenProgram
              maximumBits extra state8
        rw [show 3 + extra = (2 + extra) + 1 by omega]
        rw [run_set_instruction (fuel := 2 + extra)
          (by rfl) rfl honeBits]
        change
          runNPOracleProgram balancedClauseStreamFlattenProgram
              maximumBits (2 + extra) state6 =
            runNPOracleProgram balancedClauseStreamFlattenProgram
              maximumBits extra state8
        rw [show 2 + extra = (1 + extra) + 1 by omega]
        rw [run_pair_instruction (value := nextAccumulator)
          (fuel := 1 + extra) (by rfl) rfl
          (by
            simp [state6, state5, state4, state3, state2, state1,
              nextAccumulator, accumulatorPayload, encodeTaggedList])
          hnextAccumulatorBits]
        change
          runNPOracleProgram balancedClauseStreamFlattenProgram
              maximumBits (1 + extra) state7 =
            runNPOracleProgram balancedClauseStreamFlattenProgram
              maximumBits extra state8
        rw [show 1 + extra = extra + 1 by omega]
        rw [run_branchZero_instruction (fuel := extra)
          (by rfl) rfl]
        simp [state8]
      have hrestFit :
          ∀ candidate,
            candidate ∈ innerWrites rest (value :: accumulator) →
              natBitLength candidate ≤ maximumBits := by
        intro candidate hmember
        apply hfit candidate
        simp [innerWrites, hmember]
      have hrecursive :=
        inductionHypothesis (value :: accumulator) state8 rfl
          (by simp [state8, state7, state6, state5, state4,
            state3, state2, state1])
          rfl hrestFit
      simpa only [List.length_cons, Nat.mul_succ, foldState,
        Nat.add_comm] using hstep.trans hrecursive

private theorem run_leafFold
    (values accumulator : List ℕ) {maximumBits : ℕ}
    (state : NPOracleState)
    (hpc : state.pc = 4)
    (hcursor : state.registers 3 = encodeTaggedList values)
    (haccumulator :
      state.registers 4 = encodeTaggedList accumulator)
    (hmode : state.registers 11 = 0)
    (hfit :
      ∀ value, value ∈ innerWrites values accumulator →
        natBitLength value ≤ maximumBits) :
    ∃ finish,
      RunsToIn balancedClauseStreamFlattenProgram maximumBits
        (8 * values.length + 2) state finish ∧
      finish.pc = 13 ∧
      finish.registers 0 = state.registers 0 ∧
      finish.registers 2 = state.registers 2 ∧
      finish.registers 4 =
        encodeTaggedList (values.reverse ++ accumulator) ∧
      finish.registers 11 = 0 := by
  let folded := foldState values accumulator state
  let atMode := folded.jump 12
  let finish := atMode.jump 13
  have hitems :=
    run_foldItems values accumulator state hpc hcursor haccumulator hfit
  have hfinish :
      RunsToIn balancedClauseStreamFlattenProgram maximumBits
        2 folded finish := by
    intro extra
    rw [show 2 + extra = (1 + extra) + 1 by omega]
    rw [run_branchZero_instruction
      (fuel := 1 + extra) (by rfl) (foldState_pc _ _ _ hpc)]
    rw [foldState_cursor _ _ _ hcursor, if_pos rfl]
    change
      runNPOracleProgram balancedClauseStreamFlattenProgram
          maximumBits (1 + extra) atMode =
        runNPOracleProgram balancedClauseStreamFlattenProgram
          maximumBits extra finish
    rw [show 1 + extra = extra + 1 by omega]
    rw [run_branchZero_instruction (fuel := extra)
      (by rfl) rfl]
    rw [show atMode.registers 11 = 0 by
      simp [atMode, folded, foldState_mode, hmode]]
    rfl
  refine ⟨finish, ?_, rfl, ?_, ?_, ?_, ?_⟩
  · simpa [Nat.add_assoc] using hitems.trans hfinish
  · simp [finish, atMode, folded, foldState_current]
  · simp [finish, atMode, folded, foldState_stack]
  · simp [finish, atMode, folded,
      foldState_accumulator _ _ _ haccumulator]
  · simp [finish, atMode, folded, foldState_mode, hmode]

private def phasePc : List BalancedTraversalTree → ℕ
  | [] => 13
  | _ :: _ => 0

private def phaseStackCode : List BalancedTraversalTree → ℕ
  | [] => 0
  | _ :: rest =>
      encodeTaggedList (rest.map BalancedTraversalTree.code)

private theorem run_popMaybe
    (forest : List BalancedTraversalTree) {maximumBits : ℕ}
    (state : NPOracleState)
    (hpc : state.pc = 13)
    (hstack :
      state.registers 2 =
        encodeTaggedList (forest.map BalancedTraversalTree.code))
    (hfit :
      ∀ value, value ∈ popWrites forest →
        natBitLength value ≤ maximumBits) :
    ∃ finish,
      RunsToIn balancedClauseStreamFlattenProgram maximumBits
        (popFuel forest) state finish ∧
      finish.pc = phasePc forest ∧
      (∀ tree rest, forest = tree :: rest →
        finish.registers 0 = tree.code) ∧
      finish.registers 2 = phaseStackCode forest ∧
      finish.registers 4 = state.registers 4 ∧
      finish.registers 11 = state.registers 11 := by
  cases forest with
  | nil =>
      refine ⟨state, ?_, hpc, ?_, ?_, rfl, rfl⟩
      · simpa [popFuel] using
          (RunsToIn.refl balancedClauseStreamFlattenProgram
            maximumBits state)
      · intro tree rest himpossible
        cases himpossible
      · simpa [phaseStackCode, encodeTaggedList] using hstack
  | cons next tail =>
      let tailCode :=
        encodeTaggedList (tail.map BalancedTraversalTree.code)
      let payload := Nat.pair next.code tailCode
      let state1 := state.jump 18
      let state2 := (state1.write 6 payload).jump 19
      let state3 := (state2.write 0 next.code).jump 20
      let state4 := (state3.write 2 tailCode).jump 21
      let finish := state4.jump 0
      have hpayloadBits : natBitLength payload ≤ maximumBits :=
        hfit payload (by simp [popWrites, payload, tailCode])
      have hnextBits : natBitLength next.code ≤ maximumBits :=
        hfit next.code (by simp [popWrites])
      have htailBits : natBitLength tailCode ≤ maximumBits :=
        hfit tailCode (by simp [popWrites, tailCode])
      have hruns :
          RunsToIn balancedClauseStreamFlattenProgram maximumBits
            5 state finish := by
        intro extra
        rw [show 5 + extra = (4 + extra) + 1 by omega]
        rw [run_branchZero_instruction
          (fuel := 4 + extra) (by rfl) hpc]
        rw [hstack]
        simp only [List.map_cons,
          if_neg (taggedCons_ne_zero next.code
            (tail.map BalancedTraversalTree.code))]
        change
          runNPOracleProgram balancedClauseStreamFlattenProgram
              maximumBits (4 + extra) state1 =
            runNPOracleProgram balancedClauseStreamFlattenProgram
              maximumBits extra finish
        rw [show 4 + extra = (3 + extra) + 1 by omega]
        rw [run_unpairRight_instruction (value := payload)
          (fuel := 3 + extra) (by rfl) rfl
          (by
            simp [state1, hstack, payload, tailCode,
              encodeTaggedList])
          hpayloadBits]
        change
          runNPOracleProgram balancedClauseStreamFlattenProgram
              maximumBits (3 + extra) state2 =
            runNPOracleProgram balancedClauseStreamFlattenProgram
              maximumBits extra finish
        rw [show 3 + extra = (2 + extra) + 1 by omega]
        rw [run_unpairLeft_instruction (value := next.code)
          (fuel := 2 + extra) (by rfl) rfl
          (by simp [state2, state1, payload]) hnextBits]
        change
          runNPOracleProgram balancedClauseStreamFlattenProgram
              maximumBits (2 + extra) state3 =
            runNPOracleProgram balancedClauseStreamFlattenProgram
              maximumBits extra finish
        rw [show 2 + extra = (1 + extra) + 1 by omega]
        rw [run_unpairRight_instruction (value := tailCode)
          (fuel := 1 + extra) (by rfl) rfl
          (by simp [state3, state2, state1, payload]) htailBits]
        change
          runNPOracleProgram balancedClauseStreamFlattenProgram
              maximumBits (1 + extra) state4 =
            runNPOracleProgram balancedClauseStreamFlattenProgram
              maximumBits extra finish
        rw [show 1 + extra = extra + 1 by omega]
        rw [run_branchZero_instruction (fuel := extra)
          (by rfl) rfl]
        simp [finish]
      refine ⟨finish, ?_, rfl, ?_, ?_, ?_, ?_⟩
      · simpa [popFuel] using hruns
      · intro tree rest heq
        cases heq
        simp [finish, state4, state3]
      · simp [finish, state4, state3, tailCode, phaseStackCode]
      · simp [finish, state4, state3, state2, state1,
          NPOracleState.write, NPOracleState.jump]
      · simp [finish, state4, state3, state2, state1,
          NPOracleState.write, NPOracleState.jump]

private theorem run_emptyEntry
    {maximumBits : ℕ} (state : NPOracleState)
    (hpc : state.pc = 0)
    (hcurrent : state.registers 0 = 0) :
    RunsToIn balancedClauseStreamFlattenProgram maximumBits
      1 state (state.jump 13) := by
  intro extra
  rw [show 1 + extra = extra + 1 by omega]
  rw [run_branchZero_instruction (fuel := extra) (by rfl) hpc]
  rw [hcurrent, if_pos rfl]

private theorem run_leafEntry
    (atom : ℕ) {maximumBits : ℕ} (state : NPOracleState)
    (hpc : state.pc = 0)
    (hcurrent :
      state.registers 0 = (BalancedTraversalTree.leaf atom).code)
    (honeBits : natBitLength 1 ≤ maximumBits)
    (hzeroBits : natBitLength 0 ≤ maximumBits)
    (hatomBits : natBitLength atom ≤ maximumBits) :
    ∃ finish,
      RunsToIn balancedClauseStreamFlattenProgram maximumBits
        5 state finish ∧
      finish.pc = 4 ∧
      finish.registers 0 = state.registers 0 ∧
      finish.registers 2 = state.registers 2 ∧
      finish.registers 3 = atom ∧
      finish.registers 4 = state.registers 4 ∧
      finish.registers 11 = state.registers 11 := by
  let state1 := state.jump 1
  let state2 := (state1.write 8 1).jump 2
  let state3 := (state2.write 8 0).jump 3
  let state4 := state3.jump 28
  let finish := (state4.write 3 atom).jump 4
  have hcurrentNonzero :
      (BalancedTraversalTree.leaf atom).code ≠ 0 := by
    have hpositive :
        0 < Nat.pair 1 atom :=
      lt_of_lt_of_le (by omega) (Nat.left_le_pair 1 atom)
    simpa [BalancedTraversalTree.code] using hpositive.ne'
  have hruns :
      RunsToIn balancedClauseStreamFlattenProgram maximumBits
        5 state finish := by
    intro extra
    rw [show 5 + extra = (4 + extra) + 1 by omega]
    rw [run_branchZero_instruction
      (fuel := 4 + extra) (by rfl) hpc]
    rw [hcurrent, if_neg hcurrentNonzero]
    change
      runNPOracleProgram balancedClauseStreamFlattenProgram
          maximumBits (4 + extra) state1 =
        runNPOracleProgram balancedClauseStreamFlattenProgram
          maximumBits extra finish
    rw [show 4 + extra = (3 + extra) + 1 by omega]
    rw [run_unpairLeft_instruction (value := 1)
      (fuel := 3 + extra) (by rfl) rfl
      (by simp [state1, hcurrent, BalancedTraversalTree.code])
      honeBits]
    change
      runNPOracleProgram balancedClauseStreamFlattenProgram
          maximumBits (3 + extra) state2 =
        runNPOracleProgram balancedClauseStreamFlattenProgram
          maximumBits extra finish
    rw [show 3 + extra = (2 + extra) + 1 by omega]
    rw [run_decrement_instruction (value := 0)
      (fuel := 2 + extra) (by rfl) rfl
      (by simp [state2]) hzeroBits]
    change
      runNPOracleProgram balancedClauseStreamFlattenProgram
          maximumBits (2 + extra) state3 =
        runNPOracleProgram balancedClauseStreamFlattenProgram
          maximumBits extra finish
    rw [show 2 + extra = (1 + extra) + 1 by omega]
    rw [run_branchZero_instruction
      (fuel := 1 + extra) (by rfl) rfl]
    rw [show state3.registers 8 = 0 by simp [state3, state2]]
    rw [if_pos rfl]
    change
      runNPOracleProgram balancedClauseStreamFlattenProgram
          maximumBits (1 + extra) state4 =
        runNPOracleProgram balancedClauseStreamFlattenProgram
          maximumBits extra finish
    rw [show 1 + extra = extra + 1 by omega]
    rw [run_unpairRight_instruction (value := atom)
      (fuel := extra) (by rfl) rfl
      (by simp [state4, state3, state2, state1, hcurrent,
        BalancedTraversalTree.code])
      hatomBits]
  refine ⟨finish, hruns, rfl, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [finish, state4, state3, state2, state1,
      NPOracleState.write, NPOracleState.jump]

private theorem run_branchEntry
    (left right : BalancedTraversalTree)
    (rest : List BalancedTraversalTree) {maximumBits : ℕ}
    (state : NPOracleState)
    (hpc : state.pc = 0)
    (hcurrent :
      state.registers 0 =
        (BalancedTraversalTree.branch left right).code)
    (hstack :
      state.registers 2 =
        encodeTaggedList (rest.map BalancedTraversalTree.code))
    (hfit :
      ∀ value,
        value ∈
          [2, 1, Nat.pair left.code right.code, left.code,
            right.code,
            Nat.pair right.code
              (encodeTaggedList
                (rest.map BalancedTraversalTree.code)),
            1,
            encodeTaggedList
              (right.code ::
                rest.map BalancedTraversalTree.code)] →
          natBitLength value ≤ maximumBits) :
    ∃ finish,
      RunsToIn balancedClauseStreamFlattenProgram maximumBits
        10 state finish ∧
      finish.pc = 0 ∧
      finish.registers 0 = left.code ∧
      finish.registers 2 =
        encodeTaggedList
          (right.code :: rest.map BalancedTraversalTree.code) ∧
      finish.registers 4 = state.registers 4 ∧
      finish.registers 11 = state.registers 11 := by
  let stackCode :=
    encodeTaggedList (rest.map BalancedTraversalTree.code)
  let payload := Nat.pair left.code right.code
  let stackPayload := Nat.pair right.code stackCode
  let nextStack :=
    encodeTaggedList
      (right.code :: rest.map BalancedTraversalTree.code)
  let state1 := state.jump 1
  let state2 := (state1.write 8 2).jump 2
  let state3 := (state2.write 8 1).jump 3
  let state4 := state3.jump 22
  let state5 := (state4.write 6 payload).jump 23
  let state6 := (state5.write 0 left.code).jump 24
  let state7 := (state6.write 3 right.code).jump 25
  let state8 := (state7.write 10 stackPayload).jump 26
  let state9 := (state8.write 9 1).jump 27
  let finish := (state9.write 2 nextStack).jump 0
  have hcurrentNonzero :
      (BalancedTraversalTree.branch left right).code ≠ 0 := by
    have hpositive :
        0 < Nat.pair 2 (Nat.pair left.code right.code) :=
      lt_of_lt_of_le (by omega) <|
        Nat.left_le_pair 2 (Nat.pair left.code right.code)
    simpa [BalancedTraversalTree.code] using hpositive.ne'
  have htwoBits : natBitLength 2 ≤ maximumBits :=
    hfit 2 (by simp)
  have honeBits : natBitLength 1 ≤ maximumBits :=
    hfit 1 (by simp)
  have hpayloadBits : natBitLength payload ≤ maximumBits :=
    hfit payload (by simp [payload])
  have hleftBits : natBitLength left.code ≤ maximumBits :=
    hfit left.code (by simp)
  have hrightBits : natBitLength right.code ≤ maximumBits :=
    hfit right.code (by simp)
  have hstackPayloadBits :
      natBitLength stackPayload ≤ maximumBits :=
    hfit stackPayload (by simp [stackPayload, stackCode])
  have hnextStackBits : natBitLength nextStack ≤ maximumBits :=
    hfit nextStack (by simp [nextStack])
  have hruns :
      RunsToIn balancedClauseStreamFlattenProgram maximumBits
        10 state finish := by
    intro extra
    rw [show 10 + extra = (9 + extra) + 1 by omega]
    rw [run_branchZero_instruction
      (fuel := 9 + extra) (by rfl) hpc]
    rw [hcurrent, if_neg hcurrentNonzero]
    change
      runNPOracleProgram balancedClauseStreamFlattenProgram
          maximumBits (9 + extra) state1 =
        runNPOracleProgram balancedClauseStreamFlattenProgram
          maximumBits extra finish
    rw [show 9 + extra = (8 + extra) + 1 by omega]
    rw [run_unpairLeft_instruction (value := 2)
      (fuel := 8 + extra) (by rfl) rfl
      (by simp [state1, hcurrent, BalancedTraversalTree.code])
      htwoBits]
    change
      runNPOracleProgram balancedClauseStreamFlattenProgram
          maximumBits (8 + extra) state2 =
        runNPOracleProgram balancedClauseStreamFlattenProgram
          maximumBits extra finish
    rw [show 8 + extra = (7 + extra) + 1 by omega]
    rw [run_decrement_instruction (value := 1)
      (fuel := 7 + extra) (by rfl) rfl
      (by simp [state2]) honeBits]
    change
      runNPOracleProgram balancedClauseStreamFlattenProgram
          maximumBits (7 + extra) state3 =
        runNPOracleProgram balancedClauseStreamFlattenProgram
          maximumBits extra finish
    rw [show 7 + extra = (6 + extra) + 1 by omega]
    rw [run_branchZero_instruction
      (fuel := 6 + extra) (by rfl) rfl]
    rw [show state3.registers 8 = 1 by simp [state3, state2]]
    rw [if_neg (by omega : (1 : ℕ) ≠ 0)]
    change
      runNPOracleProgram balancedClauseStreamFlattenProgram
          maximumBits (6 + extra) state4 =
        runNPOracleProgram balancedClauseStreamFlattenProgram
          maximumBits extra finish
    rw [show 6 + extra = (5 + extra) + 1 by omega]
    rw [run_unpairRight_instruction (value := payload)
      (fuel := 5 + extra) (by rfl) rfl
      (by
        simp [state4, state3, state2, state1, hcurrent,
          BalancedTraversalTree.code, payload])
      hpayloadBits]
    change
      runNPOracleProgram balancedClauseStreamFlattenProgram
          maximumBits (5 + extra) state5 =
        runNPOracleProgram balancedClauseStreamFlattenProgram
          maximumBits extra finish
    rw [show 5 + extra = (4 + extra) + 1 by omega]
    rw [run_unpairLeft_instruction (value := left.code)
      (fuel := 4 + extra) (by rfl) rfl
      (by simp [state5, state4, payload]) hleftBits]
    change
      runNPOracleProgram balancedClauseStreamFlattenProgram
          maximumBits (4 + extra) state6 =
        runNPOracleProgram balancedClauseStreamFlattenProgram
          maximumBits extra finish
    rw [show 4 + extra = (3 + extra) + 1 by omega]
    rw [run_unpairRight_instruction (value := right.code)
      (fuel := 3 + extra) (by rfl) rfl
      (by simp [state6, state5, state4, payload]) hrightBits]
    change
      runNPOracleProgram balancedClauseStreamFlattenProgram
          maximumBits (3 + extra) state7 =
        runNPOracleProgram balancedClauseStreamFlattenProgram
          maximumBits extra finish
    rw [show 3 + extra = (2 + extra) + 1 by omega]
    rw [run_pair_instruction (value := stackPayload)
      (fuel := 2 + extra) (by rfl) rfl
      (by
        simp [state7, state6, state5, state4, state3, state2,
          state1, hstack, stackPayload, stackCode])
      hstackPayloadBits]
    change
      runNPOracleProgram balancedClauseStreamFlattenProgram
          maximumBits (2 + extra) state8 =
        runNPOracleProgram balancedClauseStreamFlattenProgram
          maximumBits extra finish
    rw [show 2 + extra = (1 + extra) + 1 by omega]
    rw [run_set_instruction (fuel := 1 + extra)
      (by rfl) rfl honeBits]
    change
      runNPOracleProgram balancedClauseStreamFlattenProgram
          maximumBits (1 + extra) state9 =
        runNPOracleProgram balancedClauseStreamFlattenProgram
          maximumBits extra finish
    rw [show 1 + extra = extra + 1 by omega]
    rw [run_pair_instruction (value := nextStack)
      (fuel := extra) (by rfl) rfl
      (by
        simp [state9, state8, state7, state6, state5, state4,
          state3, state2, state1, nextStack, stackPayload, stackCode,
          encodeTaggedList])
      hnextStackBits]
  refine ⟨finish, hruns, rfl, ?_, ?_, ?_, ?_⟩ <;>
    simp [finish, state9, state8, state7, state6, state5,
      state4, state3, state2, state1, nextStack]

private theorem run_phase
    (forest : List BalancedTraversalTree) (accumulator : List ℕ)
    {maximumBits : ℕ} (state : NPOracleState)
    (hpc : state.pc = phasePc forest)
    (hcurrent :
      ∀ tree rest, forest = tree :: rest →
        state.registers 0 = tree.code)
    (hstack : state.registers 2 = phaseStackCode forest)
    (haccumulator :
      state.registers 4 = encodeTaggedList accumulator)
    (hmode : state.registers 11 = 0)
    (hvalid :
      ∀ atom, atom ∈ forestAtoms forest →
        encodeTaggedList (streamOfCode atom) = atom)
    (hfit :
      ∀ value, value ∈ phaseWrites forest accumulator →
        natBitLength value ≤ maximumBits) :
    ∃ finish,
      RunsToIn balancedClauseStreamFlattenProgram maximumBits
        (phaseFuel forest) state finish ∧
      finish.pc = 13 ∧
      finish.registers 2 = 0 ∧
      finish.registers 4 =
        encodeTaggedList
          ((forestStreamValues forest).reverse ++ accumulator) ∧
      finish.registers 11 = 0 := by
  cases forest with
  | nil =>
      refine ⟨state, ?_, ?_, ?_, ?_, hmode⟩
      · simpa [phaseFuel] using
          (RunsToIn.refl balancedClauseStreamFlattenProgram
            maximumBits state)
      · simpa [phasePc] using hpc
      · simpa [phaseStackCode] using hstack
      · simpa [forestStreamValues] using haccumulator
  | cons tree rest =>
      cases tree with
      | empty =>
          have hcurrentZero : state.registers 0 = 0 := by
            simpa [BalancedTraversalTree.code] using
              hcurrent .empty rest rfl
          have hentry :=
            run_emptyEntry (maximumBits := maximumBits) state
              (by simpa [phasePc] using hpc) hcurrentZero
          let atRest := state.jump 13
          have hpopFit :
              ∀ value, value ∈ popWrites rest →
                natBitLength value ≤ maximumBits := by
            intro value hmember
            apply hfit value
            simp [phaseWrites, hmember]
          rcases run_popMaybe rest atRest rfl
              (by
                simpa [atRest, phaseStackCode] using hstack)
              hpopFit with
            ⟨afterPop, hpopRuns, hpopPc, hpopCurrent,
              hpopStack, hpopAccumulator, hpopMode⟩
          have hrestValid :
              ∀ atom, atom ∈ forestAtoms rest →
                encodeTaggedList (streamOfCode atom) = atom := by
            intro atom hmember
            apply hvalid atom
            simpa only [forestAtoms, List.flatMap_cons,
              BalancedTraversalTree.atoms, List.nil_append] using
              hmember
          have hrestFit :
              ∀ value, value ∈ phaseWrites rest accumulator →
                natBitLength value ≤ maximumBits := by
            intro value hmember
            apply hfit value
            simp [phaseWrites, hmember]
          rcases run_phase rest accumulator afterPop
              hpopPc hpopCurrent hpopStack
              (by rw [hpopAccumulator]; exact haccumulator)
              (by rw [hpopMode]; exact hmode)
              hrestValid hrestFit with
            ⟨finish, hrecursiveRuns, hfinishPc, hfinishStack,
              hfinishAccumulator, hfinishMode⟩
          refine ⟨finish, ?_, hfinishPc, hfinishStack, ?_,
            hfinishMode⟩
          · have hall :=
              hentry.trans (hpopRuns.trans hrecursiveRuns)
            simpa [phaseFuel, popFuel, Nat.add_assoc] using hall
          · simpa [forestStreamValues, treeStreamValues,
              BalancedTraversalTree.atoms] using
              hfinishAccumulator
      | leaf atom =>
          let stream := streamOfCode atom
          have hvalidAtom :
              encodeTaggedList stream = atom := by
            apply hvalid atom
            simp [forestAtoms, BalancedTraversalTree.atoms]
          have honeBits : natBitLength 1 ≤ maximumBits := by
            apply hfit 1
            simp [phaseWrites]
          have hzeroBits : natBitLength 0 ≤ maximumBits := by
            apply hfit 0
            simp [phaseWrites]
          have hatomBits : natBitLength atom ≤ maximumBits := by
            apply hfit atom
            simp [phaseWrites]
          rcases run_leafEntry atom state
              (by simpa [phasePc] using hpc)
              (hcurrent (.leaf atom) rest rfl)
              honeBits hzeroBits hatomBits with
            ⟨atLeaf, hentryRuns, hatLeafPc, hatLeafCurrent,
              hatLeafStack, hatLeafCursor, hatLeafAccumulator,
              hatLeafMode⟩
          have hinnerFit :
              ∀ value, value ∈ innerWrites stream accumulator →
                natBitLength value ≤ maximumBits := by
            intro value hmember
            apply hfit value
            simp [phaseWrites, stream, hmember]
          rcases run_leafFold stream accumulator atLeaf
              hatLeafPc
              (by rw [hatLeafCursor, hvalidAtom])
              (by rw [hatLeafAccumulator]; exact haccumulator)
              (by rw [hatLeafMode]; exact hmode)
              hinnerFit with
            ⟨afterLeaf, hleafRuns, hafterLeafPc,
              hafterLeafCurrent, hafterLeafStack,
              hafterLeafAccumulator, hafterLeafMode⟩
          have hpopFit :
              ∀ value, value ∈ popWrites rest →
                natBitLength value ≤ maximumBits := by
            intro value hmember
            apply hfit value
            simp [phaseWrites, hmember]
          rcases run_popMaybe rest afterLeaf hafterLeafPc
              (by
                rw [hafterLeafStack, hatLeafStack]
                simpa [phaseStackCode] using hstack)
              hpopFit with
            ⟨afterPop, hpopRuns, hpopPc, hpopCurrent,
              hpopStack, hpopAccumulator, hpopMode⟩
          have hrestValid :
              ∀ candidate, candidate ∈ forestAtoms rest →
                encodeTaggedList (streamOfCode candidate) =
                  candidate := by
            intro candidate hmember
            apply hvalid candidate
            simp only [forestAtoms, List.flatMap_cons,
              BalancedTraversalTree.atoms, List.mem_append,
              List.mem_singleton]
            exact Or.inr hmember
          have hrestFit :
              ∀ value,
                value ∈
                  phaseWrites rest (stream.reverse ++ accumulator) →
                natBitLength value ≤ maximumBits := by
            intro value hmember
            apply hfit value
            simp [phaseWrites, stream, hmember]
          rcases run_phase rest (stream.reverse ++ accumulator)
              afterPop hpopPc hpopCurrent hpopStack
              (by
                rw [hpopAccumulator, hafterLeafAccumulator])
              (by
                rw [hpopMode, hafterLeafMode])
              hrestValid hrestFit with
            ⟨finish, hrecursiveRuns, hfinishPc, hfinishStack,
              hfinishAccumulator, hfinishMode⟩
          refine ⟨finish, ?_, hfinishPc, hfinishStack, ?_,
            hfinishMode⟩
          · have hall :=
              hentryRuns.trans <|
                hleafRuns.trans <|
                  hpopRuns.trans hrecursiveRuns
            simpa [phaseFuel, popFuel, stream, Nat.add_assoc] using
              hall
          · simpa [forestStreamValues, treeStreamValues,
              BalancedTraversalTree.atoms, stream,
              List.reverse_append, List.append_assoc] using
              hfinishAccumulator
      | branch left right =>
          let stackCode :=
            encodeTaggedList (rest.map BalancedTraversalTree.code)
          let payload := Nat.pair left.code right.code
          let stackPayload := Nat.pair right.code stackCode
          let nextStack :=
            encodeTaggedList
              (right.code ::
                rest.map BalancedTraversalTree.code)
          have hentryFit :
              ∀ value,
                value ∈
                  [2, 1, payload, left.code, right.code,
                    stackPayload, 1, nextStack] →
                  natBitLength value ≤ maximumBits := by
            intro value hmember
            apply hfit value
            simp only [phaseWrites]
            apply List.mem_append.mpr
            left
            simpa [stackCode, payload, stackPayload, nextStack] using
              hmember
          rcases run_branchEntry left right rest state
              (by simpa [phasePc] using hpc)
              (hcurrent (.branch left right) rest rfl)
              (by simpa [phaseStackCode, stackCode] using hstack)
              (by
                simpa [stackCode, payload, stackPayload, nextStack]
                  using hentryFit) with
            ⟨afterBranch, hentryRuns, hafterBranchPc,
              hafterBranchCurrent, hafterBranchStack,
              hafterBranchAccumulator, hafterBranchMode⟩
          have hexpandedValid :
              ∀ atom,
                atom ∈ forestAtoms (left :: right :: rest) →
                encodeTaggedList (streamOfCode atom) = atom := by
            intro atom hmember
            apply hvalid atom
            simpa [forestAtoms, BalancedTraversalTree.atoms,
              List.append_assoc] using hmember
          have hexpandedFit :
              ∀ value,
                value ∈
                  phaseWrites (left :: right :: rest) accumulator →
                natBitLength value ≤ maximumBits := by
            intro value hmember
            apply hfit value
            simp [phaseWrites, hmember]
          rcases run_phase (left :: right :: rest) accumulator
              afterBranch
              (by simpa [phasePc] using hafterBranchPc)
              (by
                intro tree tail heq
                cases heq
                exact hafterBranchCurrent)
              (by
                simpa [phaseStackCode] using hafterBranchStack)
              (by
                rw [hafterBranchAccumulator]
                exact haccumulator)
              (by
                rw [hafterBranchMode]
                exact hmode)
              hexpandedValid hexpandedFit with
            ⟨finish, hrecursiveRuns, hfinishPc, hfinishStack,
              hfinishAccumulator, hfinishMode⟩
          refine ⟨finish, ?_, hfinishPc, hfinishStack, ?_,
            hfinishMode⟩
          · have hall := hentryRuns.trans hrecursiveRuns
            simpa [phaseFuel] using hall
          · simpa [forestStreamValues, treeStreamValues,
              BalancedTraversalTree.atoms, List.append_assoc] using
              hfinishAccumulator
termination_by
  (forest.map BalancedTraversalTree.nodeCount).sum
decreasing_by
  all_goals
    subst_vars
    simp [BalancedTraversalTree.nodeCount]
    try omega

private theorem run_finalReverse
    (values : List ℕ) {maximumBits : ℕ} (state : NPOracleState)
    (hpc : state.pc = 13)
    (hstack : state.registers 2 = 0)
    (haccumulator :
      state.registers 4 = encodeTaggedList values)
    (hcursorBits :
      natBitLength (encodeTaggedList values) ≤ maximumBits)
    (hzeroBits : natBitLength 0 ≤ maximumBits)
    (honeBits : natBitLength 1 ≤ maximumBits)
    (hfoldBits :
      ∀ value, value ∈ innerWrites values [] →
        natBitLength value ≤ maximumBits)
    (houtputBits :
      natBitLength (encodeTaggedList values.reverse) ≤ maximumBits) :
    runNPOracleProgram balancedClauseStreamFlattenProgram maximumBits
        (8 * values.length + 7) state =
      some (encodeTaggedList values.reverse) := by
  let state1 := state.jump 15
  let state2 :=
    (state1.write 3 (encodeTaggedList values)).jump 16
  let state3 := (state2.write 4 0).jump 17
  let atFold := (state3.write 11 1).jump 4
  let folded := foldState values [] atFold
  let atMode := folded.jump 12
  let atHalt := atMode.jump 14
  have hsetup :
      RunsToIn balancedClauseStreamFlattenProgram maximumBits
        4 state atFold := by
    intro extra
    rw [show 4 + extra = (3 + extra) + 1 by omega]
    rw [run_branchZero_instruction
      (fuel := 3 + extra) (by rfl) hpc]
    rw [hstack, if_pos rfl]
    change
      runNPOracleProgram balancedClauseStreamFlattenProgram
          maximumBits (3 + extra) state1 =
        runNPOracleProgram balancedClauseStreamFlattenProgram
          maximumBits extra atFold
    rw [show 3 + extra = (2 + extra) + 1 by omega]
    rw [run_copy_instruction
      (fuel := 2 + extra) (value := encodeTaggedList values)
      (by rfl) rfl
      (by simp [state1, haccumulator]) hcursorBits]
    change
      runNPOracleProgram balancedClauseStreamFlattenProgram
          maximumBits (2 + extra) state2 =
        runNPOracleProgram balancedClauseStreamFlattenProgram
          maximumBits extra atFold
    rw [show 2 + extra = (1 + extra) + 1 by omega]
    rw [run_set_instruction (fuel := 1 + extra)
      (by rfl) rfl hzeroBits]
    change
      runNPOracleProgram balancedClauseStreamFlattenProgram
          maximumBits (1 + extra) state3 =
        runNPOracleProgram balancedClauseStreamFlattenProgram
          maximumBits extra atFold
    rw [show 1 + extra = extra + 1 by omega]
    rw [run_set_instruction (fuel := extra)
      (by rfl) rfl honeBits]
  have hitems :
      RunsToIn balancedClauseStreamFlattenProgram maximumBits
        (8 * values.length) atFold folded := by
    apply run_foldItems values [] atFold
    · rfl
    · simp [atFold, state3, state2, state1]
    · simp [atFold, state3, encodeTaggedList]
    · exact hfoldBits
  have hterminal :
      runNPOracleProgram balancedClauseStreamFlattenProgram maximumBits
          3 folded =
        some (encodeTaggedList values.reverse) := by
    rw [show 3 = 2 + 1 by omega]
    rw [run_branchZero_instruction
      (fuel := 2) (by rfl)
      (foldState_pc values [] atFold rfl)]
    rw [foldState_cursor values [] atFold
      (by simp [atFold, state3, state2, state1]),
      if_pos rfl]
    change
      runNPOracleProgram balancedClauseStreamFlattenProgram
          maximumBits 2 atMode =
        some (encodeTaggedList values.reverse)
    rw [show 2 = 1 + 1 by omega]
    rw [run_branchZero_instruction
      (fuel := 1) (by rfl) rfl]
    rw [show atMode.registers 11 = 1 by
      simp [atMode, folded, atFold, state3, foldState_mode]]
    simp only [if_neg (by omega : (1 : ℕ) ≠ 0)]
    change
      runNPOracleProgram balancedClauseStreamFlattenProgram
          maximumBits 1 atHalt =
        some (encodeTaggedList values.reverse)
    apply run_halt_instruction (fuel := 0) (by rfl) rfl
    · simp [atHalt, atMode, folded,
        foldState_accumulator values [] atFold,
        atFold, state3, encodeTaggedList]
    · exact houtputBits
  rw [show 8 * values.length + 7 =
      4 + (8 * values.length + 3) by omega]
  rw [hsetup]
  rw [show 8 * values.length + 3 =
      8 * values.length + 3 by rfl]
  rw [hitems]
  exact hterminal

private theorem treeStreamValues_balanced
    (streams : List (List ℕ)) :
    treeStreamValues
        (balancedTraversalTree (streams.map encodeTaggedList)) =
      streams.flatten := by
  rw [treeStreamValues, balancedTraversalTree_atoms]
  induction streams with
  | nil => rfl
  | cons stream rest inductionHypothesis =>
      simp [streamOfCode_encodeTaggedList, inductionHypothesis]

/-- Exact direct refinement from the balanced batch-call output ABI to the
single tagged raw-clause stream consumed by the recovery controller. -/
theorem run_balancedClauseStreamFlattenProgram
    (streams : List (List ℕ)) (inputLength : ℕ) :
    runNPOracleProgram balancedClauseStreamFlattenProgram
        (balancedClauseStreamFlattenMaximumBits streams)
        (balancedClauseStreamFlattenFuel streams)
        (initialNPOracleState inputLength
          (encodeBalancedList (streams.map encodeTaggedList))) =
      some (encodeTaggedList streams.flatten) := by
  let tree :=
    balancedTraversalTree (streams.map encodeTaggedList)
  let initialState :=
    initialNPOracleState inputLength tree.code
  have hinitialCode :
      tree.code =
        encodeBalancedList (streams.map encodeTaggedList) := by
    simpa [tree] using
      balancedTraversalTree_code
        (streams.map encodeTaggedList)
  have hvalid :
      ∀ atom, atom ∈ forestAtoms [tree] →
        encodeTaggedList (streamOfCode atom) = atom := by
    intro atom hmember
    have hatom :
        atom ∈ streams.map encodeTaggedList := by
      simpa [forestAtoms, tree,
        balancedTraversalTree_atoms] using hmember
    rcases List.mem_map.mp hatom with
      ⟨stream, _hstream, rfl⟩
    exact congrArg encodeTaggedList
      (streamOfCode_encodeTaggedList stream)
  have hphaseFit :
      ∀ value, value ∈ phaseWrites [tree] [] →
        natBitLength value ≤
          balancedClauseStreamFlattenMaximumBits streams := by
    intro value hmember
    apply workingValue_fits streams
    simp [balancedClauseStreamFlattenWorkingValues, tree, hmember]
  rcases run_phase [tree] [] initialState
      (by rfl)
      (by
        intro current rest heq
        cases heq
        rfl)
      (by simp [phaseStackCode, initialState,
        initialNPOracleState, encodeTaggedList])
      (by simp [initialState, initialNPOracleState,
        encodeTaggedList])
      (by simp [initialState, initialNPOracleState])
      hvalid hphaseFit with
    ⟨afterPhase, hphaseRuns, hafterPhasePc,
      hafterPhaseStack, hafterPhaseAccumulator,
      hafterPhaseMode⟩
  have hforestValues :
      forestStreamValues [tree] = streams.flatten := by
    simpa [forestStreamValues, tree] using
      treeStreamValues_balanced streams
  have hreverseCursorBits :
      natBitLength (encodeTaggedList streams.flatten.reverse) ≤
        balancedClauseStreamFlattenMaximumBits streams := by
    apply workingValue_fits streams
    simp [balancedClauseStreamFlattenWorkingValues]
  have hzeroBits :
      natBitLength 0 ≤
        balancedClauseStreamFlattenMaximumBits streams := by
    apply workingValue_fits streams
    simp [balancedClauseStreamFlattenWorkingValues]
  have honeBits :
      natBitLength 1 ≤
        balancedClauseStreamFlattenMaximumBits streams := by
    apply workingValue_fits streams
    simp [balancedClauseStreamFlattenWorkingValues]
  have hreverseFoldBits :
      ∀ value,
        value ∈ innerWrites streams.flatten.reverse [] →
          natBitLength value ≤
            balancedClauseStreamFlattenMaximumBits streams := by
    intro value hmember
    apply workingValue_fits streams
    simp [balancedClauseStreamFlattenWorkingValues, hmember]
  have houtputBits :
      natBitLength (encodeTaggedList streams.flatten) ≤
        balancedClauseStreamFlattenMaximumBits streams := by
    apply workingValue_fits streams
    simp [balancedClauseStreamFlattenWorkingValues]
  have hfinal :=
    run_finalReverse streams.flatten.reverse afterPhase
      hafterPhasePc hafterPhaseStack
      (by
        rw [hafterPhaseAccumulator, hforestValues]
        simp)
      hreverseCursorBits hzeroBits honeBits hreverseFoldBits
      (by simpa using houtputBits)
  rw [show balancedClauseStreamFlattenFuel streams =
      phaseFuel [tree] + (8 * streams.flatten.length + 7) by
    change
      phaseFuel [tree] + 8 * streams.flatten.length + 7 =
        phaseFuel [tree] + (8 * streams.flatten.length + 7)
    omega]
  rw [← hinitialCode]
  change
    runNPOracleProgram balancedClauseStreamFlattenProgram
        (balancedClauseStreamFlattenMaximumBits streams)
        (phaseFuel [tree] + (8 * streams.flatten.length + 7))
        initialState =
      some (encodeTaggedList streams.flatten)
  rw [hphaseRuns]
  simpa using hfinal

def balancedTreeStreamFlattenFuel
    (tree : BalancedTraversalTree) : ℕ :=
  phaseFuel [tree] + 8 * (treeStreamValues tree).length + 7

private def balancedTreeStreamFlattenWorkingValues
    (tree : BalancedTraversalTree) : List ℕ :=
  let values := treeStreamValues tree
  [tree.code, encodeTaggedList values, 0, 1, 2] ++
    phaseWrites [tree] [] ++
    [encodeTaggedList values.reverse, 0, 1] ++
    innerWrites values.reverse []

private def balancedTreeStreamFlattenWorkBound
    (tree : BalancedTraversalTree) : ℕ :=
  (balancedTreeStreamFlattenWorkingValues tree).foldr max 0

def balancedTreeStreamFlattenMaximumBits
    (tree : BalancedTraversalTree) : ℕ :=
  natBitLength (balancedTreeStreamFlattenWorkBound tree)

private theorem balancedTreeStreamFlattenWorkingValue_fits
    (tree : BalancedTraversalTree) {value : ℕ}
    (hmem : value ∈ balancedTreeStreamFlattenWorkingValues tree) :
    natBitLength value ≤ balancedTreeStreamFlattenMaximumBits tree := by
  unfold balancedTreeStreamFlattenMaximumBits
    balancedTreeStreamFlattenWorkBound
  exact natBitLength_mono (member_le_foldr_max hmem)

/-- Exact flattening for any structural balanced tree.  This is deliberately
the same interpreter as `run_balancedClauseStreamFlattenProgram`; only its
proof-facing entry type is more general. -/
theorem run_balancedClauseStreamFlattenTree
    (tree : BalancedTraversalTree) (inputLength : ℕ)
    (hvalid : ∀ atom ∈ tree.atoms,
      encodeTaggedList (streamOfCode atom) = atom) :
    runNPOracleProgram balancedClauseStreamFlattenProgram
        (balancedTreeStreamFlattenMaximumBits tree)
        (balancedTreeStreamFlattenFuel tree)
        (initialNPOracleState inputLength tree.code) =
      some (encodeTaggedList (treeStreamValues tree)) := by
  let initialState := initialNPOracleState inputLength tree.code
  have hphaseFit :
      ∀ value, value ∈ phaseWrites [tree] [] →
        natBitLength value ≤
          balancedTreeStreamFlattenMaximumBits tree := by
    intro value hmember
    apply balancedTreeStreamFlattenWorkingValue_fits tree
    simp [balancedTreeStreamFlattenWorkingValues, hmember]
  have hforestValid :
      ∀ atom, atom ∈ forestAtoms [tree] →
        encodeTaggedList (streamOfCode atom) = atom := by
    intro atom hmember
    apply hvalid atom
    simpa [forestAtoms] using hmember
  rcases run_phase [tree] [] initialState
      (by rfl)
      (by
        intro current rest heq
        cases heq
        rfl)
      (by simp [phaseStackCode, initialState,
        initialNPOracleState, encodeTaggedList])
      (by simp [initialState, initialNPOracleState,
        encodeTaggedList])
      (by simp [initialState, initialNPOracleState])
      hforestValid hphaseFit with
    ⟨afterPhase, hphaseRuns, hafterPhasePc,
      hafterPhaseStack, hafterPhaseAccumulator,
      _hafterPhaseMode⟩
  have hforestValues :
      forestStreamValues [tree] = treeStreamValues tree := by
    simp [forestStreamValues]
  have hreverseCursorBits :
      natBitLength
          (encodeTaggedList (treeStreamValues tree).reverse) ≤
        balancedTreeStreamFlattenMaximumBits tree := by
    apply balancedTreeStreamFlattenWorkingValue_fits tree
    simp [balancedTreeStreamFlattenWorkingValues]
  have hzeroBits :
      natBitLength 0 ≤ balancedTreeStreamFlattenMaximumBits tree := by
    apply balancedTreeStreamFlattenWorkingValue_fits tree
    simp [balancedTreeStreamFlattenWorkingValues]
  have honeBits :
      natBitLength 1 ≤ balancedTreeStreamFlattenMaximumBits tree := by
    apply balancedTreeStreamFlattenWorkingValue_fits tree
    simp [balancedTreeStreamFlattenWorkingValues]
  have hreverseFoldBits :
      ∀ value,
        value ∈ innerWrites (treeStreamValues tree).reverse [] →
          natBitLength value ≤
            balancedTreeStreamFlattenMaximumBits tree := by
    intro value hmember
    apply balancedTreeStreamFlattenWorkingValue_fits tree
    simp [balancedTreeStreamFlattenWorkingValues, hmember]
  have houtputBits :
      natBitLength (encodeTaggedList (treeStreamValues tree)) ≤
        balancedTreeStreamFlattenMaximumBits tree := by
    apply balancedTreeStreamFlattenWorkingValue_fits tree
    simp [balancedTreeStreamFlattenWorkingValues]
  have hfinal :=
    run_finalReverse (treeStreamValues tree).reverse afterPhase
      hafterPhasePc hafterPhaseStack
      (by
        rw [hafterPhaseAccumulator, hforestValues]
        simp)
      hreverseCursorBits hzeroBits honeBits hreverseFoldBits
      (by simpa using houtputBits)
  rw [show balancedTreeStreamFlattenFuel tree =
      phaseFuel [tree] +
        (8 * (treeStreamValues tree).length + 7) by
    unfold balancedTreeStreamFlattenFuel
    omega]
  change
    runNPOracleProgram balancedClauseStreamFlattenProgram
        (balancedTreeStreamFlattenMaximumBits tree)
        (phaseFuel [tree] +
          (8 * (treeStreamValues tree).length + 7))
        initialState =
      some (encodeTaggedList (treeStreamValues tree))
  rw [hphaseRuns]
  simpa using hfinal

end NearCubicWires.BalancedClauseStreamFlattenProgram
