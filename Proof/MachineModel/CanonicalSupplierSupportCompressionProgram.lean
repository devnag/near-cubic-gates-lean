import Proof.MachineModel.CanonicalBalancedLookupProgram
import Proof.Circuits.CanonicalBalancedCall
import Proof.MachineModel.GeneratedBalancedRangeProgram
import Proof.MachineModel.PreserveRightProgram
import Proof.Circuits.RegisterBounds
import Proof.Foundations.VerifiedLinker

/-!
# Canonical supplier support compression

Supplier gates carry parallel canonical balanced vectors of integer weights and
Boolean support bits.  Compression must retain only supported weights without
ever materializing a linear tagged list: such a spine has exponential register
width.  This module starts the production path with a direct balanced-tree
support count.  Its work stack contains only pending balanced subtrees and
therefore has logarithmic depth on canonical inputs.
-/

namespace NearCubicWires.CanonicalSupplierSupportCompressionProgram

open NearCubicWires
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBalancedLookupProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.RegisterBounds
open NearCubicWires.VerifiedLinker

/-! ## Semantic support order -/

/-- Native number of physically retained coordinates. -/
def nonzeroSupportCount : List Bool → ℕ
  | [] => 0
  | bit :: rest => (if bit then 1 else 0) + nonzeroSupportCount rest

theorem nonzeroSupportCount_eq_sum_toNat
    (values : List Bool) :
    nonzeroSupportCount values = (values.map Bool.toNat).sum := by
  induction values with
  | nil => rfl
  | cons value values inductionHypothesis =>
      cases value <;>
        simp [nonzeroSupportCount, inductionHypothesis]

/-- Number of nonzero atoms in a native list.  This is the semantic result of
the shared balanced count controller; Boolean support counting is its typed
special case. -/
def nonzeroAtomCount : List ℕ → ℕ
  | [] => 0
  | atom :: rest =>
      (if atom = 0 then 0 else 1) + nonzeroAtomCount rest

@[simp] private theorem nonzeroAtomCount_append
    (left right : List ℕ) :
    nonzeroAtomCount (left ++ right) =
      nonzeroAtomCount left + nonzeroAtomCount right := by
  induction left with
  | nil => simp [nonzeroAtomCount]
  | cons atom rest inductionHypothesis =>
      simp [nonzeroAtomCount, inductionHypothesis, Nat.add_assoc]

private def BalancedTraversalTree.nonzeroCount : BalancedTraversalTree → ℕ
  | .empty => 0
  | .leaf atom => if atom = 0 then 0 else 1
  | .branch left right =>
      BalancedTraversalTree.nonzeroCount left +
        BalancedTraversalTree.nonzeroCount right

@[simp] private theorem BalancedTraversalTree.nonzeroCount_empty :
    BalancedTraversalTree.nonzeroCount .empty = 0 := by
  rfl

@[simp] private theorem BalancedTraversalTree.nonzeroCount_leaf
    (atom : ℕ) :
    BalancedTraversalTree.nonzeroCount (.leaf atom) =
      if atom = 0 then 0 else 1 := by
  rfl

@[simp] private theorem BalancedTraversalTree.nonzeroCount_branch
    (left right : BalancedTraversalTree) :
    BalancedTraversalTree.nonzeroCount (.branch left right) =
      BalancedTraversalTree.nonzeroCount left +
        BalancedTraversalTree.nonzeroCount right := by
  rfl

@[simp] private theorem BalancedTraversalTree.code_empty :
    BalancedTraversalTree.code .empty = 0 := by
  rfl

@[simp] private theorem BalancedTraversalTree.code_leaf (atom : ℕ) :
    BalancedTraversalTree.code (.leaf atom) = Nat.pair 1 atom := by
  rfl

@[simp] private theorem BalancedTraversalTree.code_branch
    (left right : BalancedTraversalTree) :
    BalancedTraversalTree.code (.branch left right) =
      Nat.pair 2 (Nat.pair left.code right.code) := by
  rfl

@[simp] private theorem balancedTraversalAtoms_empty :
    BalancedTraversalTree.atoms .empty = [] := by
  rfl

@[simp] private theorem balancedTraversalAtoms_leaf (atom : ℕ) :
    BalancedTraversalTree.atoms (.leaf atom) = [atom] := by
  rfl

@[simp] private theorem balancedTraversalAtoms_branch
    (left right : BalancedTraversalTree) :
    BalancedTraversalTree.atoms (.branch left right) =
      left.atoms ++ right.atoms := by
  rfl

private theorem BalancedTraversalTree.nonzeroCount_atoms
    (tree : BalancedTraversalTree) :
    BalancedTraversalTree.nonzeroCount tree =
      nonzeroAtomCount tree.atoms := by
  induction tree with
  | empty => rfl
  | leaf atom =>
      simp [BalancedTraversalTree.nonzeroCount,
        BalancedTraversalTree.atoms, nonzeroAtomCount]
  | branch left right ihLeft ihRight =>
      simp [BalancedTraversalTree.nonzeroCount,
        BalancedTraversalTree.atoms, ihLeft, ihRight]

private theorem balancedSupportTree_nonzeroCount
    (support : List Bool) :
    BalancedTraversalTree.nonzeroCount
        (balancedTraversalTree (support.map boolCode)) =
      nonzeroSupportCount support := by
  rw [BalancedTraversalTree.nonzeroCount_atoms,
    balancedTraversalTree_atoms]
  induction support with
  | nil => rfl
  | cons bit rest inductionHypothesis =>
      cases bit <;>
        simp [nonzeroSupportCount, nonzeroAtomCount, boolCode,
          inductionHypothesis]

/-- Original positions of the nonzero atoms, starting at a caller-supplied
offset.  This is a proof view only; the selector below never materializes it. -/
def nonzeroAtomIndicesFrom : ℕ → List ℕ → List ℕ
  | _first, [] => []
  | first, atom :: rest =>
      if atom = 0 then
        nonzeroAtomIndicesFrom (first + 1) rest
      else
        first :: nonzeroAtomIndicesFrom (first + 1) rest

def nonzeroSupportIndices (support : List Bool) : List ℕ :=
  nonzeroAtomIndicesFrom 0 (support.map boolCode)

/-- Stable zip-filter semantics for the compressed supplier weight vector.
Unequal malformed inputs truncate at the shorter side; production theorems
require equal lengths. -/
def supportedWeights : List ℕ → List Bool → List ℕ
  | weight :: weights, bit :: support =>
      if bit then
        weight :: supportedWeights weights support
      else
        supportedWeights weights support
  | _, _ => []

@[simp] private theorem nonzeroAtomIndicesFrom_length
    (first : ℕ) (atoms : List ℕ) :
    (nonzeroAtomIndicesFrom first atoms).length =
      nonzeroAtomCount atoms := by
  induction atoms generalizing first with
  | nil => rfl
  | cons atom rest inductionHypothesis =>
      by_cases hatom : atom = 0
      · simp [nonzeroAtomIndicesFrom, nonzeroAtomCount, hatom,
          inductionHypothesis]
      · simp [nonzeroAtomIndicesFrom, nonzeroAtomCount, hatom,
          inductionHypothesis, Nat.add_comm]

@[simp] private theorem nonzeroSupportIndices_length
    (support : List Bool) :
    (nonzeroSupportIndices support).length =
      nonzeroSupportCount support := by
  unfold nonzeroSupportIndices
  rw [nonzeroAtomIndicesFrom_length]
  induction support with
  | nil => rfl
  | cons bit rest inductionHypothesis =>
      cases bit <;>
        simp [nonzeroAtomCount, nonzeroSupportCount, boolCode,
          inductionHypothesis]

private theorem nonzeroAtomIndicesFrom_mem_lt
    {first value : ℕ} {atoms : List ℕ}
    (hvalue : value ∈ nonzeroAtomIndicesFrom first atoms) :
    value < first + atoms.length := by
  induction atoms generalizing first with
  | nil => simp [nonzeroAtomIndicesFrom] at hvalue
  | cons atom rest inductionHypothesis =>
      by_cases hatom : atom = 0
      · have htail :
            value ∈ nonzeroAtomIndicesFrom (first + 1) rest := by
          simpa [nonzeroAtomIndicesFrom, hatom] using hvalue
        have := inductionHypothesis htail
        simp only [List.length_cons]
        omega
      · have hcases :
            value = first ∨
              value ∈ nonzeroAtomIndicesFrom (first + 1) rest := by
          simpa [nonzeroAtomIndicesFrom, hatom] using hvalue
        rcases hcases with rfl | htail
        · simp
        · have := inductionHypothesis htail
          simp only [List.length_cons]
          omega

private theorem nonzeroSupportIndex_lt
    (support : List Bool) (rank : ℕ)
    (hrank : rank < (nonzeroSupportIndices support).length) :
    (nonzeroSupportIndices support)[rank] < support.length := by
  have hmem :
      (nonzeroSupportIndices support)[rank] ∈
        nonzeroSupportIndices support :=
    List.getElem_mem hrank
  have hmem' :
      (nonzeroSupportIndices support)[rank] ∈
        nonzeroAtomIndicesFrom 0 (support.map boolCode) := by
    simpa only [nonzeroSupportIndices] using hmem
  have hbound :=
    nonzeroAtomIndicesFrom_mem_lt
      (first := 0) (atoms := support.map boolCode) hmem'
  simpa only [zero_add, List.length_map] using hbound

/-! ## Balanced support count and range-context preparation -/

/-- Pending subtrees are a control stack, not a public sequence encoding.  On
canonical balanced inputs its length never exceeds the tree height. -/
private def encodeSupportWork (trees : List BalancedTraversalTree) : ℕ :=
  encodeTaggedList (trees.map BalancedTraversalTree.code)

@[simp] private theorem encodeSupportWork_nil :
    encodeSupportWork [] = 0 := by
  rfl

@[simp] private theorem encodeSupportWork_cons
    (tree : BalancedTraversalTree)
    (rest : List BalancedTraversalTree) :
    encodeSupportWork (tree :: rest) =
      Nat.pair 1 (Nat.pair tree.code (encodeSupportWork rest)) := by
  rfl

private def supportWorkCount (trees : List BalancedTraversalTree) : ℕ :=
  (trees.map (fun tree =>
    BalancedTraversalTree.nonzeroCount tree)).sum

@[simp] private theorem supportWorkCount_nil :
    supportWorkCount [] = 0 := by
  rfl

@[simp] private theorem supportWorkCount_cons
    (tree : BalancedTraversalTree)
    (rest : List BalancedTraversalTree) :
    supportWorkCount (tree :: rest) =
      BalancedTraversalTree.nonzeroCount tree +
        supportWorkCount rest := by
  simp [supportWorkCount]

private def supportWorkAtoms (trees : List BalancedTraversalTree) : List ℕ :=
  trees.flatMap BalancedTraversalTree.atoms

private def supportWorkSelectedIndicesFrom
    (first : ℕ) (trees : List BalancedTraversalTree) : List ℕ :=
  nonzeroAtomIndicesFrom first (supportWorkAtoms trees)

@[simp] private theorem supportWorkAtoms_nil :
    supportWorkAtoms [] = [] := by
  rfl

@[simp] private theorem supportWorkAtoms_empty_cons
    (rest : List BalancedTraversalTree) :
    supportWorkAtoms (.empty :: rest) = supportWorkAtoms rest := by
  rfl

@[simp] private theorem supportWorkAtoms_leaf_cons
    (atom : ℕ) (rest : List BalancedTraversalTree) :
    supportWorkAtoms (.leaf atom :: rest) =
      atom :: supportWorkAtoms rest := by
  rfl

@[simp] private theorem supportWorkAtoms_branch_cons
    (left right : BalancedTraversalTree)
    (rest : List BalancedTraversalTree) :
    supportWorkAtoms (.branch left right :: rest) =
      supportWorkAtoms (left :: right :: rest) := by
  simp [supportWorkAtoms, List.append_assoc]

private theorem supportWorkCount_eq_nonzeroAtomCount
    (trees : List BalancedTraversalTree) :
    supportWorkCount trees = nonzeroAtomCount (supportWorkAtoms trees) := by
  induction trees with
  | nil => rfl
  | cons tree rest inductionHypothesis =>
      simp only [supportWorkCount_cons, supportWorkAtoms, List.flatMap_cons,
        nonzeroAtomCount_append]
      rw [← BalancedTraversalTree.nonzeroCount_atoms,
        inductionHypothesis]
      rfl

@[simp] private theorem supportWorkSelectedIndicesFrom_length
    (first : ℕ) (trees : List BalancedTraversalTree) :
    (supportWorkSelectedIndicesFrom first trees).length =
      supportWorkCount trees := by
  simp [supportWorkSelectedIndicesFrom,
    ← supportWorkCount_eq_nonzeroAtomCount]

private def supportWorkMeasure (trees : List BalancedTraversalTree) : ℕ :=
  (trees.map BalancedTraversalTree.nodeCount).sum

/-- Exact instructions from the traversal loop through the final halt. -/
def supplierSupportCountWorkFuel :
    List BalancedTraversalTree → ℕ
  | [] => 5
  | .empty :: rest =>
      6 + supplierSupportCountWorkFuel rest
  | .leaf atom :: rest =>
      (if atom = 0 then 11 else 12) +
        supplierSupportCountWorkFuel rest
  | .branch left right :: rest =>
      15 + supplierSupportCountWorkFuel (left :: right :: rest)
termination_by trees => supportWorkMeasure trees
decreasing_by
  all_goals
    simp [supportWorkMeasure, BalancedTraversalTree.nodeCount] <;>
      omega

/-- Values written while processing the proof-level work stack.  This exact
ledger is used only to state the narrowest successful register budget. -/
private def supplierSupportCountWorkValues :
    List BalancedTraversalTree → ℕ → List ℕ
  | [], accumulator => [0, accumulator]
  | .empty :: rest, accumulator =>
      [ encodeSupportWork (.empty :: rest)
      , Nat.pair 0 (encodeSupportWork rest)
      , 0
      , encodeSupportWork rest
      ] ++ supplierSupportCountWorkValues rest accumulator
  | .leaf atom :: rest, accumulator =>
      let next := if atom = 0 then accumulator else accumulator + 1
      [ encodeSupportWork (.leaf atom :: rest)
      , Nat.pair (BalancedTraversalTree.leaf atom).code
          (encodeSupportWork rest)
      , (BalancedTraversalTree.leaf atom).code
      , encodeSupportWork rest
      , 1
      , 0
      , atom
      , next
      ] ++ supplierSupportCountWorkValues rest next
  | .branch left right :: rest, accumulator =>
      let rightPayload := Nat.pair right.code (encodeSupportWork rest)
      let rightStack := Nat.pair 1 rightPayload
      let leftPayload := Nat.pair left.code rightStack
      let nextStack := Nat.pair 1 leftPayload
      [ encodeSupportWork (.branch left right :: rest)
      , Nat.pair (BalancedTraversalTree.branch left right).code
          (encodeSupportWork rest)
      , (BalancedTraversalTree.branch left right).code
      , encodeSupportWork rest
      , 2
      , 1
      , Nat.pair left.code right.code
      , left.code
      , right.code
      , rightPayload
      , rightStack
      , leftPayload
      , nextStack
      ] ++
        supplierSupportCountWorkValues (left :: right :: rest) accumulator
termination_by trees _ => supportWorkMeasure trees
decreasing_by
  all_goals
    simp [supportWorkMeasure, BalancedTraversalTree.nodeCount] <;>
      omega

/-- Public output is already the exact input expected by
`generatedBalancedRangeProgram`: `pair(count, context)`, where the retained
context is `pair(weights, pair(count, support))`. -/
private def supplierSupportCountPrepareOutput
    (weightsCode supportCode count : ℕ) : ℕ :=
  Nat.pair count (Nat.pair weightsCode (Nat.pair count supportCode))

/-- Register ABI:

* `r0`: work stack, then final output;
* `r2`: rest of work stack;
* `r3`: native selected count;
* `r4`/`r5`: preserved weights/support codes;
* `r8`: constant one;
* `r6`/`r7`/`r9`/`r10`/`r11`: structural scratch.

The stack contains only balanced subtrees pending in a depth-first traversal.
-/
def supplierSupportCountPrepareProgram : NPOracleProgram :=
  [ .unpairLeft 0 4 1
  , .unpairRight 0 5 2
  , .set 3 0 3
  , .set 8 1 4
  , .set 2 0 5
  , .pair 5 2 9 6
  , .pair 8 9 0 7
  , .branchZero 0 26 8
  , .unpairRight 0 6 9
  , .unpairLeft 6 0 10
  , .unpairRight 6 2 11
  , .branchZero 0 25 12
  , .unpairLeft 0 7 13
  , .decrement 7 14
  , .branchZero 7 15 18
  , .unpairRight 0 7 16
  , .branchZero 7 25 17
  , .increment 3 25
  , .unpairRight 0 6 19
  , .unpairLeft 6 0 20
  , .unpairRight 6 7 21
  , .pair 7 2 9 22
  , .pair 8 9 9 23
  , .pair 0 9 10 24
  , .pair 8 10 0 7
  , .copy 2 0 7
  , .pair 3 5 6 27
  , .pair 4 6 11 28
  , .pair 3 11 0 29
  , .halt 0
  ]

@[simp] private theorem supplierSupportCountPrepareProgram_oracleFree :
    OracleFree supplierSupportCountPrepareProgram := by
  rfl

def supplierSupportCountPrepareFuel (support : List Bool) : ℕ :=
  7 + supplierSupportCountWorkFuel
    [balancedTraversalTree (support.map boolCode)]

private def supplierSupportCountPreparePrefixValues
    (weightsCode : ℕ) (support : List Bool) : List ℕ :=
  let supportCode := encodeBoolList support
  let tree := balancedTraversalTree (support.map boolCode)
  let count := nonzeroSupportCount support
  [ 0, 1, weightsCode, supportCode, Nat.pair weightsCode supportCode
  , Nat.pair supportCode 0
  , encodeSupportWork [tree]
  , count
  , Nat.pair count supportCode
  , Nat.pair weightsCode (Nat.pair count supportCode)
  , supplierSupportCountPrepareOutput weightsCode supportCode count
  ]

private def supplierSupportCountPrepareExecutionValues
    (weightsCode : ℕ) (support : List Bool) : List ℕ :=
  let tree := balancedTraversalTree (support.map boolCode)
  supplierSupportCountPreparePrefixValues weightsCode support ++
    supplierSupportCountWorkValues [tree] 0

private def supplierSupportCountPrepareBits
    (inputLength weightsCode : ℕ) (support : List Bool) : ℕ :=
  max (natBitLength inputLength) <|
    ((supplierSupportCountPrepareExecutionValues weightsCode support).map
      natBitLength).foldr max 0

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

private theorem supplierSupportCountPrepareBits_of_mem
    {inputLength weightsCode value : ℕ} {support : List Bool}
    (hmem :
      value ∈
        supplierSupportCountPrepareExecutionValues weightsCode support) :
    natBitLength value ≤
      supplierSupportCountPrepareBits inputLength weightsCode support := by
  unfold supplierSupportCountPrepareBits
  apply (le_foldr_max_of_mem (List.mem_map.mpr ⟨value, hmem, rfl⟩)).trans
  exact Nat.le_max_right _ _

private theorem run_supplierSupportCountWork
    (trees : List BalancedTraversalTree)
    (accumulator weightsCode supportCode maximumBits : ℕ)
    (state : NPOracleState)
    (hpc : state.pc = 7)
    (hwork : state.registers 0 = encodeSupportWork trees)
    (haccumulator : state.registers 3 = accumulator)
    (hweights : state.registers 4 = weightsCode)
    (hsupport : state.registers 5 = supportCode)
    (hone : state.registers 8 = 1)
    (hfits :
      ∀ value,
        value ∈ supplierSupportCountWorkValues trees accumulator →
          natBitLength value ≤ maximumBits)
    (hcountSupport :
      natBitLength
          (Nat.pair (accumulator + supportWorkCount trees) supportCode) ≤
        maximumBits)
    (hcontext :
      natBitLength
          (Nat.pair weightsCode
            (Nat.pair (accumulator + supportWorkCount trees)
              supportCode)) ≤
        maximumBits)
    (houtput :
      natBitLength
          (supplierSupportCountPrepareOutput weightsCode supportCode
            (accumulator + supportWorkCount trees)) ≤
        maximumBits) :
    runNPOracleProgram supplierSupportCountPrepareProgram maximumBits
        (supplierSupportCountWorkFuel trees) state =
      some
        (supplierSupportCountPrepareOutput weightsCode supportCode
          (accumulator + supportWorkCount trees)) := by
  induction trees using supplierSupportCountWorkFuel.induct
      generalizing accumulator state with
  | case1 =>
      let countSupport := Nat.pair accumulator supportCode
      let context := Nat.pair weightsCode countSupport
      let output :=
        supplierSupportCountPrepareOutput weightsCode supportCode accumulator
      have hcountSupport' :
          natBitLength countSupport ≤ maximumBits := by
        simpa [countSupport, supportWorkCount] using hcountSupport
      have hcontext' :
          natBitLength context ≤ maximumBits := by
        simpa [context, countSupport, supportWorkCount] using hcontext
      have houtput' :
          natBitLength output ≤ maximumBits := by
        simpa [output, supportWorkCount] using houtput
      rw [supplierSupportCountWorkFuel]
      rw [show 5 = 4 + 1 by omega]
      rw [run_branchZero_instruction (by rfl) hpc]
      rw [hwork, if_pos (by rfl)]
      rw [show 4 = 3 + 1 by omega]
      rw [run_pair_instruction (value := countSupport)
        (by rfl) rfl
        (by simp [NPOracleState.jump, countSupport, haccumulator, hsupport])
        hcountSupport']
      rw [show 3 = 2 + 1 by omega]
      rw [run_pair_instruction (value := context)
        (by rfl) rfl
        (by
          simp [NPOracleState.write, NPOracleState.jump, context,
            hweights, countSupport])
        hcontext']
      rw [show 2 = 1 + 1 by omega]
      rw [run_pair_instruction (value := output)
        (by rfl) rfl
        (by
          simp [NPOracleState.write, NPOracleState.jump, output,
            supplierSupportCountPrepareOutput, context, countSupport,
            haccumulator])
        houtput']
      exact run_halt_instruction (fuel := 0) (by rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump, output])
        houtput'
  | case2 rest inductionHypothesis =>
      let restCode := encodeSupportWork rest
      let payload := Nat.pair 0 restCode
      let stackCode := Nat.pair 1 payload
      let state1 := state.jump 8
      let state2 := (state1.write 6 payload).jump 9
      let state3 := (state2.write 0 0).jump 10
      let state4 := (state3.write 2 restCode).jump 11
      let state5 := state4.jump 25
      let nextState := (state5.write 0 restCode).jump 7
      have hstackNonzero : stackCode ≠ 0 := by
        dsimp only [stackCode]
        apply Nat.ne_of_gt
        exact lt_of_lt_of_le (by omega : 0 < 1)
          (Nat.left_le_pair 1 payload)
      have hpayloadBits : natBitLength payload ≤ maximumBits := by
        apply hfits
        simp [supplierSupportCountWorkValues, payload, restCode]
      have hzeroBits : natBitLength 0 ≤ maximumBits := by
        apply hfits
        simp [supplierSupportCountWorkValues]
      have hrestBits : natBitLength restCode ≤ maximumBits := by
        apply hfits
        simp [supplierSupportCountWorkValues, restCode]
      have hfitsRest :
          ∀ value,
            value ∈ supplierSupportCountWorkValues rest accumulator →
              natBitLength value ≤ maximumBits := by
        intro value hvalue
        apply hfits
        simp [supplierSupportCountWorkValues, hvalue]
      rw [supplierSupportCountWorkFuel]
      rw [show
        6 + supplierSupportCountWorkFuel rest =
          (5 + supplierSupportCountWorkFuel rest) + 1 by omega]
      rw [run_branchZero_instruction (by rfl) hpc]
      rw [hwork, encodeSupportWork_cons, if_neg (by
        simpa [stackCode, payload, restCode] using hstackNonzero)]
      change
        runNPOracleProgram supplierSupportCountPrepareProgram maximumBits
            (5 + supplierSupportCountWorkFuel rest) state1 =
          some
            (supplierSupportCountPrepareOutput weightsCode supportCode
              (accumulator + supportWorkCount (.empty :: rest)))
      rw [show
        5 + supplierSupportCountWorkFuel rest =
          (4 + supplierSupportCountWorkFuel rest) + 1 by omega]
      rw [run_unpairRight_instruction (value := payload)
        (by rfl) rfl
        (by
          simp [state1, payload, restCode,
            encodeSupportWork_cons, hwork])
        hpayloadBits]
      change
        runNPOracleProgram supplierSupportCountPrepareProgram maximumBits
            (4 + supplierSupportCountWorkFuel rest) state2 =
          some
            (supplierSupportCountPrepareOutput weightsCode supportCode
              (accumulator + supportWorkCount (.empty :: rest)))
      rw [show
        4 + supplierSupportCountWorkFuel rest =
          (3 + supplierSupportCountWorkFuel rest) + 1 by omega]
      rw [run_unpairLeft_instruction (value := 0)
        (by rfl) rfl
        (by simp [state2, payload])
        hzeroBits]
      change
        runNPOracleProgram supplierSupportCountPrepareProgram maximumBits
            (3 + supplierSupportCountWorkFuel rest) state3 =
          some
            (supplierSupportCountPrepareOutput weightsCode supportCode
              (accumulator + supportWorkCount (.empty :: rest)))
      rw [show
        3 + supplierSupportCountWorkFuel rest =
          (2 + supplierSupportCountWorkFuel rest) + 1 by omega]
      rw [run_unpairRight_instruction (value := restCode)
        (by rfl) rfl
        (by simp [state3, state2, payload, restCode])
        hrestBits]
      change
        runNPOracleProgram supplierSupportCountPrepareProgram maximumBits
            (2 + supplierSupportCountWorkFuel rest) state4 =
          some
            (supplierSupportCountPrepareOutput weightsCode supportCode
              (accumulator + supportWorkCount (.empty :: rest)))
      rw [show
        2 + supplierSupportCountWorkFuel rest =
          (1 + supplierSupportCountWorkFuel rest) + 1 by omega]
      rw [run_branchZero_instruction (by rfl) rfl]
      rw [show state4.registers 0 = 0 by simp [state4, state3]]
      rw [if_pos rfl]
      change
        runNPOracleProgram supplierSupportCountPrepareProgram maximumBits
            (1 + supplierSupportCountWorkFuel rest) state5 =
          some
            (supplierSupportCountPrepareOutput weightsCode supportCode
              (accumulator + supportWorkCount (.empty :: rest)))
      rw [show
        1 + supplierSupportCountWorkFuel rest =
          supplierSupportCountWorkFuel rest + 1 by omega]
      rw [run_copy_instruction (value := restCode)
        (by rfl) rfl
        (by simp [state5, state4, restCode])
        hrestBits]
      change
        runNPOracleProgram supplierSupportCountPrepareProgram maximumBits
            (supplierSupportCountWorkFuel rest) nextState =
          some
            (supplierSupportCountPrepareOutput weightsCode supportCode
              (accumulator + supportWorkCount (.empty :: rest)))
      have hrun :=
        inductionHypothesis accumulator nextState rfl
          (by simp [nextState, restCode])
          (by simp [nextState, state5, state4, state3, state2, state1,
            haccumulator])
          (by simp [nextState, state5, state4, state3, state2, state1,
            hweights])
          (by simp [nextState, state5, state4, state3, state2, state1,
            hsupport])
          (by simp [nextState, state5, state4, state3, state2, state1,
            hone])
          hfitsRest
          (by simpa [supportWorkCount,
            BalancedTraversalTree.nonzeroCount] using hcountSupport)
          (by simpa [supportWorkCount,
            BalancedTraversalTree.nonzeroCount] using hcontext)
          (by simpa [supportWorkCount,
            BalancedTraversalTree.nonzeroCount] using houtput)
      simpa [supportWorkCount,
        BalancedTraversalTree.nonzeroCount] using hrun
  | case3 atom rest inductionHypothesis =>
      by_cases hatom : atom = 0
      · subst atom
        let restCode := encodeSupportWork rest
        let treeCode := (BalancedTraversalTree.leaf 0).code
        let payload := Nat.pair treeCode restCode
        let stackCode := Nat.pair 1 payload
        let state1 := state.jump 8
        let state2 := (state1.write 6 payload).jump 9
        let state3 := (state2.write 0 treeCode).jump 10
        let state4 := (state3.write 2 restCode).jump 11
        let state5 := state4.jump 12
        let state6 := (state5.write 7 1).jump 13
        let state7 := (state6.write 7 0).jump 14
        let state8 := state7.jump 15
        let state9 := (state8.write 7 0).jump 16
        let state10 := state9.jump 25
        let nextState := (state10.write 0 restCode).jump 7
        have hstackNonzero : stackCode ≠ 0 := by
          dsimp only [stackCode]
          apply Nat.ne_of_gt
          exact lt_of_lt_of_le (by omega : 0 < 1)
            (Nat.left_le_pair 1 payload)
        have hbits (value : ℕ)
            (hvalue :
              value ∈
                [stackCode, payload, treeCode, restCode, 1, 0]) :
            natBitLength value ≤ maximumBits := by
          apply hfits
          simp [supplierSupportCountWorkValues, stackCode, payload,
            treeCode, restCode] at hvalue ⊢
          aesop
        have hfitsRest :
            ∀ value,
              value ∈ supplierSupportCountWorkValues rest accumulator →
                natBitLength value ≤ maximumBits := by
          intro value hvalue
          apply hfits
          simp [supplierSupportCountWorkValues, hvalue]
        rw [supplierSupportCountWorkFuel, if_pos rfl]
        rw [show
          11 + supplierSupportCountWorkFuel rest =
            (10 + supplierSupportCountWorkFuel rest) + 1 by omega]
        rw [run_branchZero_instruction (by rfl) hpc]
        rw [hwork, encodeSupportWork_cons, if_neg (by
          simpa [stackCode, payload, treeCode, restCode] using
            hstackNonzero)]
        rw [show
          10 + supplierSupportCountWorkFuel rest =
            (9 + supplierSupportCountWorkFuel rest) + 1 by omega]
        rw [run_unpairRight_instruction (value := payload)
          (by rfl) rfl
          (by simp [payload, treeCode, restCode,
            encodeSupportWork_cons, hwork])
          (hbits payload (by simp))]
        rw [show
          9 + supplierSupportCountWorkFuel rest =
            (8 + supplierSupportCountWorkFuel rest) + 1 by omega]
        rw [run_unpairLeft_instruction (value := treeCode)
          (by rfl) rfl
          (by simp [payload])
          (hbits treeCode (by simp))]
        rw [show
          8 + supplierSupportCountWorkFuel rest =
            (7 + supplierSupportCountWorkFuel rest) + 1 by omega]
        rw [run_unpairRight_instruction (value := restCode)
          (by rfl) rfl
          (by simp [payload])
          (hbits restCode (by simp))]
        rw [show
          7 + supplierSupportCountWorkFuel rest =
            (6 + supplierSupportCountWorkFuel rest) + 1 by omega]
        rw [run_branchZero_instruction (by rfl) rfl]
        rw [show state4.registers 0 = treeCode by
          simp [state4, state3]]
        rw [if_neg (by
          have := Nat.left_le_pair 1 0
          simp [treeCode]
          omega)]
        rw [show
          6 + supplierSupportCountWorkFuel rest =
            (5 + supplierSupportCountWorkFuel rest) + 1 by omega]
        rw [run_unpairLeft_instruction (value := 1)
          (by rfl) rfl
          (by simp [treeCode])
          (hbits 1 (by simp))]
        rw [show
          5 + supplierSupportCountWorkFuel rest =
            (4 + supplierSupportCountWorkFuel rest) + 1 by omega]
        rw [run_decrement_instruction (value := 0)
          (by rfl) rfl
          (by simp)
          (hbits 0 (by simp))]
        rw [show
          4 + supplierSupportCountWorkFuel rest =
            (3 + supplierSupportCountWorkFuel rest) + 1 by omega]
        rw [run_branchZero_instruction (by rfl) rfl]
        rw [show state7.registers 7 = 0 by simp [state7]]
        rw [if_pos rfl]
        rw [show
          3 + supplierSupportCountWorkFuel rest =
            (2 + supplierSupportCountWorkFuel rest) + 1 by omega]
        rw [run_unpairRight_instruction (value := 0)
          (by rfl) rfl
          (by simp [treeCode])
          (hbits 0 (by simp))]
        rw [show
          2 + supplierSupportCountWorkFuel rest =
            (1 + supplierSupportCountWorkFuel rest) + 1 by omega]
        rw [run_branchZero_instruction (by rfl) rfl]
        rw [show state9.registers 7 = 0 by simp [state9]]
        rw [if_pos rfl]
        rw [show
          1 + supplierSupportCountWorkFuel rest =
            supplierSupportCountWorkFuel rest + 1 by omega]
        rw [run_copy_instruction (value := restCode)
          (by rfl) rfl
          (by simp [restCode])
          (hbits restCode (by simp))]
        change
          runNPOracleProgram supplierSupportCountPrepareProgram maximumBits
              (supplierSupportCountWorkFuel rest) nextState =
            some
              (supplierSupportCountPrepareOutput weightsCode supportCode
                (accumulator +
                  supportWorkCount (BalancedTraversalTree.leaf 0 :: rest)))
        have hrun :=
          inductionHypothesis accumulator nextState rfl
            (by simp [nextState, restCode])
            (by simp [nextState, state10, state9, state8, state7,
              state6, state5, state4, state3, state2, state1,
              haccumulator])
            (by simp [nextState, state10, state9, state8, state7,
              state6, state5, state4, state3, state2, state1,
              hweights])
            (by simp [nextState, state10, state9, state8, state7,
              state6, state5, state4, state3, state2, state1,
              hsupport])
            (by simp [nextState, state10, state9, state8, state7,
              state6, state5, state4, state3, state2, state1,
              hone])
            hfitsRest
            (by simpa [supportWorkCount,
              BalancedTraversalTree.nonzeroCount] using hcountSupport)
            (by simpa [supportWorkCount,
              BalancedTraversalTree.nonzeroCount] using hcontext)
            (by simpa [supportWorkCount,
              BalancedTraversalTree.nonzeroCount] using houtput)
        simpa [supportWorkCount,
          BalancedTraversalTree.nonzeroCount] using hrun
      · let nextAccumulator := accumulator + 1
        let restCode := encodeSupportWork rest
        let treeCode := (BalancedTraversalTree.leaf atom).code
        let payload := Nat.pair treeCode restCode
        let stackCode := Nat.pair 1 payload
        let state1 := state.jump 8
        let state2 := (state1.write 6 payload).jump 9
        let state3 := (state2.write 0 treeCode).jump 10
        let state4 := (state3.write 2 restCode).jump 11
        let state5 := state4.jump 12
        let state6 := (state5.write 7 1).jump 13
        let state7 := (state6.write 7 0).jump 14
        let state8 := state7.jump 15
        let state9 := (state8.write 7 atom).jump 16
        let state10 := state9.jump 17
        let state11 :=
          (state10.write 3 nextAccumulator).jump 25
        let nextState := (state11.write 0 restCode).jump 7
        have hstackNonzero : stackCode ≠ 0 := by
          dsimp only [stackCode]
          apply Nat.ne_of_gt
          exact lt_of_lt_of_le (by omega : 0 < 1)
            (Nat.left_le_pair 1 payload)
        have htreeNonzero : treeCode ≠ 0 := by
          dsimp only [treeCode]
          apply Nat.ne_of_gt
          exact lt_of_lt_of_le (by omega : 0 < 1)
            (Nat.left_le_pair 1 atom)
        have hbits (value : ℕ)
            (hvalue :
              value ∈
                [stackCode, payload, treeCode, restCode, 1, 0, atom,
                  nextAccumulator]) :
            natBitLength value ≤ maximumBits := by
          apply hfits
          simp [supplierSupportCountWorkValues, stackCode, payload,
            treeCode, restCode, nextAccumulator, hatom] at hvalue ⊢
          aesop
        have hfitsRest :
            ∀ value,
              value ∈
                  supplierSupportCountWorkValues rest nextAccumulator →
                natBitLength value ≤ maximumBits := by
          intro value hvalue
          apply hfits
          simp [supplierSupportCountWorkValues, nextAccumulator, hatom,
            hvalue]
        rw [supplierSupportCountWorkFuel, if_neg hatom]
        rw [show
          12 + supplierSupportCountWorkFuel rest =
            (11 + supplierSupportCountWorkFuel rest) + 1 by omega]
        rw [run_branchZero_instruction (by rfl) hpc]
        rw [hwork, encodeSupportWork_cons, if_neg (by
          simpa [stackCode, payload, treeCode, restCode] using
            hstackNonzero)]
        rw [show
          11 + supplierSupportCountWorkFuel rest =
            (10 + supplierSupportCountWorkFuel rest) + 1 by omega]
        rw [run_unpairRight_instruction (value := payload)
          (by rfl) rfl
          (by simp [payload, treeCode, restCode,
            encodeSupportWork_cons, hwork])
          (hbits payload (by simp))]
        rw [show
          10 + supplierSupportCountWorkFuel rest =
            (9 + supplierSupportCountWorkFuel rest) + 1 by omega]
        rw [run_unpairLeft_instruction (value := treeCode)
          (by rfl) rfl
          (by simp [payload])
          (hbits treeCode (by simp))]
        rw [show
          9 + supplierSupportCountWorkFuel rest =
            (8 + supplierSupportCountWorkFuel rest) + 1 by omega]
        rw [run_unpairRight_instruction (value := restCode)
          (by rfl) rfl
          (by simp [payload])
          (hbits restCode (by simp))]
        rw [show
          8 + supplierSupportCountWorkFuel rest =
            (7 + supplierSupportCountWorkFuel rest) + 1 by omega]
        rw [run_branchZero_instruction (by rfl) rfl]
        rw [show state4.registers 0 = treeCode by
          simp [state4, state3]]
        rw [if_neg htreeNonzero]
        rw [show
          7 + supplierSupportCountWorkFuel rest =
            (6 + supplierSupportCountWorkFuel rest) + 1 by omega]
        rw [run_unpairLeft_instruction (value := 1)
          (by rfl) rfl
          (by simp [treeCode])
          (hbits 1 (by simp))]
        rw [show
          6 + supplierSupportCountWorkFuel rest =
            (5 + supplierSupportCountWorkFuel rest) + 1 by omega]
        rw [run_decrement_instruction (value := 0)
          (by rfl) rfl
          (by simp)
          (hbits 0 (by simp))]
        rw [show
          5 + supplierSupportCountWorkFuel rest =
            (4 + supplierSupportCountWorkFuel rest) + 1 by omega]
        rw [run_branchZero_instruction (by rfl) rfl]
        rw [show state7.registers 7 = 0 by simp [state7]]
        rw [if_pos rfl]
        rw [show
          4 + supplierSupportCountWorkFuel rest =
            (3 + supplierSupportCountWorkFuel rest) + 1 by omega]
        rw [run_unpairRight_instruction (value := atom)
          (by rfl) rfl
          (by simp [treeCode])
          (hbits atom (by simp))]
        rw [show
          3 + supplierSupportCountWorkFuel rest =
            (2 + supplierSupportCountWorkFuel rest) + 1 by omega]
        rw [run_branchZero_instruction (by rfl) rfl]
        rw [show state9.registers 7 = atom by simp [state9]]
        rw [if_neg hatom]
        rw [show
          2 + supplierSupportCountWorkFuel rest =
            (1 + supplierSupportCountWorkFuel rest) + 1 by omega]
        rw [run_increment_instruction (value := nextAccumulator)
          (by rfl) rfl
          (by
            simp [nextAccumulator, haccumulator])
          (hbits nextAccumulator (by simp))]
        rw [show
          1 + supplierSupportCountWorkFuel rest =
            supplierSupportCountWorkFuel rest + 1 by omega]
        rw [run_copy_instruction (value := restCode)
          (by rfl) rfl
          (by simp [restCode])
          (hbits restCode (by simp))]
        change
          runNPOracleProgram supplierSupportCountPrepareProgram maximumBits
              (supplierSupportCountWorkFuel rest) nextState =
            some
              (supplierSupportCountPrepareOutput weightsCode supportCode
                (accumulator +
                  supportWorkCount
                    (BalancedTraversalTree.leaf atom :: rest)))
        have hrun :=
          inductionHypothesis nextAccumulator nextState rfl
            (by simp [nextState, restCode])
            (by simp [nextState, state11, nextAccumulator])
            (by simp [nextState, state11, state10, state9, state8,
              state7, state6, state5, state4, state3, state2, state1,
              hweights])
            (by simp [nextState, state11, state10, state9, state8,
              state7, state6, state5, state4, state3, state2, state1,
              hsupport])
            (by simp [nextState, state11, state10, state9, state8,
              state7, state6, state5, state4, state3, state2, state1,
              hone])
            hfitsRest
            (by
              simpa [supportWorkCount,
                BalancedTraversalTree.nonzeroCount, nextAccumulator,
                hatom, Nat.add_assoc] using hcountSupport)
            (by
              simpa [supportWorkCount,
                BalancedTraversalTree.nonzeroCount, nextAccumulator,
                hatom, Nat.add_assoc] using hcontext)
            (by
              simpa [supportWorkCount,
                BalancedTraversalTree.nonzeroCount, nextAccumulator,
                hatom, Nat.add_assoc] using houtput)
        simpa [supportWorkCount, BalancedTraversalTree.nonzeroCount,
          nextAccumulator, hatom, Nat.add_assoc] using hrun
  | case4 left right rest inductionHypothesis =>
      let restCode := encodeSupportWork rest
      let treeCode := (BalancedTraversalTree.branch left right).code
      let branchPayload := Nat.pair left.code right.code
      let payload := Nat.pair treeCode restCode
      let rightPayload := Nat.pair right.code restCode
      let rightStack := Nat.pair 1 rightPayload
      let leftPayload := Nat.pair left.code rightStack
      let nextStack := Nat.pair 1 leftPayload
      let state1 := state.jump 8
      let state2 := (state1.write 6 payload).jump 9
      let state3 := (state2.write 0 treeCode).jump 10
      let state4 := (state3.write 2 restCode).jump 11
      let state5 := state4.jump 12
      let state6 := (state5.write 7 2).jump 13
      let state7 := (state6.write 7 1).jump 14
      let state8 := state7.jump 18
      let state9 := (state8.write 6 branchPayload).jump 19
      let state10 := (state9.write 0 left.code).jump 20
      let state11 := (state10.write 7 right.code).jump 21
      let state12 := (state11.write 9 rightPayload).jump 22
      let state13 := (state12.write 9 rightStack).jump 23
      let state14 := (state13.write 10 leftPayload).jump 24
      let nextState := (state14.write 0 nextStack).jump 7
      have hstackNonzero :
          encodeSupportWork
              (BalancedTraversalTree.branch left right :: rest) ≠ 0 := by
        rw [encodeSupportWork_cons]
        apply Nat.ne_of_gt
        exact lt_of_lt_of_le (by omega : 0 < 1)
          (Nat.left_le_pair 1
            (Nat.pair
              (BalancedTraversalTree.branch left right).code
              (encodeSupportWork rest)))
      have htreeNonzero : treeCode ≠ 0 := by
        dsimp only [treeCode, BalancedTraversalTree.code]
        apply Nat.ne_of_gt
        exact lt_of_lt_of_le (by omega : 0 < 2)
          (Nat.left_le_pair 2 (Nat.pair left.code right.code))
      have honeNonzero : (1 : ℕ) ≠ 0 := by omega
      have hbits (value : ℕ)
          (hvalue :
            value ∈
              [ encodeSupportWork
                  (BalancedTraversalTree.branch left right :: rest)
              , payload, treeCode, restCode, 2, 1, branchPayload,
                left.code, right.code, rightPayload, rightStack,
                leftPayload, nextStack ]) :
          natBitLength value ≤ maximumBits := by
        apply hfits
        simp [supplierSupportCountWorkValues, payload, treeCode,
          restCode, branchPayload, rightPayload, rightStack,
          leftPayload, nextStack] at hvalue ⊢
        aesop
      have hfitsNext :
          ∀ value,
            value ∈
                supplierSupportCountWorkValues
                  (left :: right :: rest) accumulator →
              natBitLength value ≤ maximumBits := by
        intro value hvalue
        apply hfits
        simp [supplierSupportCountWorkValues, hvalue]
      rw [supplierSupportCountWorkFuel]
      rw [show
        15 + supplierSupportCountWorkFuel (left :: right :: rest) =
          (14 + supplierSupportCountWorkFuel (left :: right :: rest)) + 1
            by omega]
      rw [run_branchZero_instruction (by rfl) hpc]
      rw [hwork, if_neg hstackNonzero]
      rw [show
        14 + supplierSupportCountWorkFuel (left :: right :: rest) =
          (13 + supplierSupportCountWorkFuel (left :: right :: rest)) + 1
            by omega]
      rw [run_unpairRight_instruction (value := payload)
        (by rfl) rfl
        (by
          simp [payload, treeCode, restCode,
            encodeSupportWork_cons, hwork])
        (hbits payload (by simp))]
      rw [show
        13 + supplierSupportCountWorkFuel (left :: right :: rest) =
          (12 + supplierSupportCountWorkFuel (left :: right :: rest)) + 1
            by omega]
      rw [run_unpairLeft_instruction (value := treeCode)
        (by rfl) rfl
        (by simp [payload])
        (hbits treeCode (by simp))]
      rw [show
        12 + supplierSupportCountWorkFuel (left :: right :: rest) =
          (11 + supplierSupportCountWorkFuel (left :: right :: rest)) + 1
            by omega]
      rw [run_unpairRight_instruction (value := restCode)
        (by rfl) rfl
        (by simp [payload])
        (hbits restCode (by simp))]
      rw [show
        11 + supplierSupportCountWorkFuel (left :: right :: rest) =
          (10 + supplierSupportCountWorkFuel (left :: right :: rest)) + 1
            by omega]
      rw [run_branchZero_instruction (by rfl) rfl]
      rw [show state4.registers 0 = treeCode by
        simp [state4, state3]]
      rw [if_neg htreeNonzero]
      rw [show
        10 + supplierSupportCountWorkFuel (left :: right :: rest) =
          (9 + supplierSupportCountWorkFuel (left :: right :: rest)) + 1
            by omega]
      rw [run_unpairLeft_instruction (value := 2)
        (by rfl) rfl
        (by
          simp [treeCode])
        (hbits 2 (by simp))]
      rw [show
        9 + supplierSupportCountWorkFuel (left :: right :: rest) =
          (8 + supplierSupportCountWorkFuel (left :: right :: rest)) + 1
            by omega]
      rw [run_decrement_instruction (value := 1)
        (by rfl) rfl
        (by simp)
        (hbits 1 (by simp))]
      rw [show
        8 + supplierSupportCountWorkFuel (left :: right :: rest) =
          (7 + supplierSupportCountWorkFuel (left :: right :: rest)) + 1
            by omega]
      rw [run_branchZero_instruction (by rfl) rfl]
      rw [show state7.registers 7 = 1 by simp [state7]]
      rw [if_neg honeNonzero]
      rw [show
        7 + supplierSupportCountWorkFuel (left :: right :: rest) =
          (6 + supplierSupportCountWorkFuel (left :: right :: rest)) + 1
            by omega]
      rw [run_unpairRight_instruction (value := branchPayload)
        (by rfl) rfl
        (by
          simp [treeCode, branchPayload])
        (hbits branchPayload (by simp))]
      rw [show
        6 + supplierSupportCountWorkFuel (left :: right :: rest) =
          (5 + supplierSupportCountWorkFuel (left :: right :: rest)) + 1
            by omega]
      rw [run_unpairLeft_instruction (value := left.code)
        (by rfl) rfl
        (by simp [branchPayload])
        (hbits left.code (by simp))]
      rw [show
        5 + supplierSupportCountWorkFuel (left :: right :: rest) =
          (4 + supplierSupportCountWorkFuel (left :: right :: rest)) + 1
            by omega]
      rw [run_unpairRight_instruction (value := right.code)
        (by rfl) rfl
        (by simp [branchPayload])
        (hbits right.code (by simp))]
      rw [show
        4 + supplierSupportCountWorkFuel (left :: right :: rest) =
          (3 + supplierSupportCountWorkFuel (left :: right :: rest)) + 1
            by omega]
      rw [run_pair_instruction (value := rightPayload)
        (by rfl) rfl
        (by simp [rightPayload, restCode])
        (hbits rightPayload (by simp))]
      rw [show
        3 + supplierSupportCountWorkFuel (left :: right :: rest) =
          (2 + supplierSupportCountWorkFuel (left :: right :: rest)) + 1
            by omega]
      rw [run_pair_instruction (value := rightStack)
        (by rfl) rfl
        (by simp [rightStack, rightPayload, hone])
        (hbits rightStack (by simp))]
      rw [show
        2 + supplierSupportCountWorkFuel (left :: right :: rest) =
          (1 + supplierSupportCountWorkFuel (left :: right :: rest)) + 1
            by omega]
      rw [run_pair_instruction (value := leftPayload)
        (by rfl) rfl
        (by simp [leftPayload, rightStack])
        (hbits leftPayload (by simp))]
      rw [show
        1 + supplierSupportCountWorkFuel (left :: right :: rest) =
          supplierSupportCountWorkFuel (left :: right :: rest) + 1
            by omega]
      rw [run_pair_instruction (value := nextStack)
        (by rfl) rfl
        (by simp [nextStack, leftPayload, hone])
        (hbits nextStack (by simp))]
      change
        runNPOracleProgram supplierSupportCountPrepareProgram maximumBits
            (supplierSupportCountWorkFuel (left :: right :: rest))
            nextState =
          some
            (supplierSupportCountPrepareOutput weightsCode supportCode
              (accumulator +
                supportWorkCount
                  (BalancedTraversalTree.branch left right :: rest)))
      have hrun :=
        inductionHypothesis accumulator nextState rfl
          (by
            simp [nextState, nextStack, leftPayload, rightStack,
              rightPayload, restCode, encodeSupportWork_cons])
          (by simp [nextState, state14, state13, state12, state11,
            state10, state9, state8, state7, state6, state5, state4,
            state3, state2, state1, haccumulator])
          (by simp [nextState, state14, state13, state12, state11,
            state10, state9, state8, state7, state6, state5, state4,
            state3, state2, state1, hweights])
          (by simp [nextState, state14, state13, state12, state11,
            state10, state9, state8, state7, state6, state5, state4,
            state3, state2, state1, hsupport])
          (by simp [nextState, state14, state13, state12, state11,
            state10, state9, state8, state7, state6, state5, state4,
            state3, state2, state1, hone])
          hfitsNext
          (by
            simpa [supportWorkCount,
              BalancedTraversalTree.nonzeroCount, Nat.add_assoc,
              Nat.add_left_comm, Nat.add_comm] using hcountSupport)
          (by
            simpa [supportWorkCount,
              BalancedTraversalTree.nonzeroCount, Nat.add_assoc,
              Nat.add_left_comm, Nat.add_comm] using hcontext)
          (by
            simpa [supportWorkCount,
              BalancedTraversalTree.nonzeroCount, Nat.add_assoc,
              Nat.add_left_comm, Nat.add_comm] using houtput)
      simpa [supportWorkCount, BalancedTraversalTree.nonzeroCount,
        Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hrun

set_option maxRecDepth 5000 in
/-- Setup and traversal theorem over an opaque balanced tree.  Keeping the
tree opaque prevents the elaborator from unfolding a symbolic canonical tree
merely to normalize the exact work fuel. -/
private theorem run_supplierSupportCountPrepareProgram_of_fits
    (inputLength weightsCode supportCode count maximumBits : ℕ)
    (tree : BalancedTraversalTree)
    (hcode : tree.code = supportCode)
    (hcount : BalancedTraversalTree.nonzeroCount tree = count)
    (hweightsBits : natBitLength weightsCode ≤ maximumBits)
    (hsupportBits : natBitLength supportCode ≤ maximumBits)
    (hzeroBits : natBitLength 0 ≤ maximumBits)
    (honeBits : natBitLength 1 ≤ maximumBits)
    (hpayloadBits : natBitLength (Nat.pair supportCode 0) ≤ maximumBits)
    (hworkBits : natBitLength (encodeSupportWork [tree]) ≤ maximumBits)
    (hworkFits :
      ∀ value,
        value ∈ supplierSupportCountWorkValues [tree] 0 →
          natBitLength value ≤ maximumBits)
    (hcountSupport :
      natBitLength (Nat.pair count supportCode) ≤ maximumBits)
    (hcontext :
      natBitLength (Nat.pair weightsCode (Nat.pair count supportCode)) ≤
        maximumBits)
    (houtput :
      natBitLength
          (supplierSupportCountPrepareOutput weightsCode supportCode count) ≤
        maximumBits) :
    runNPOracleProgram supplierSupportCountPrepareProgram
        maximumBits
        (7 + supplierSupportCountWorkFuel [tree])
        (initialNPOracleState inputLength
          (Nat.pair weightsCode supportCode)) =
      some
        (supplierSupportCountPrepareOutput weightsCode
          supportCode count) := by
  let initial :=
    initialNPOracleState inputLength (Nat.pair weightsCode supportCode)
  let state1 := (initial.write 4 weightsCode).jump 1
  let state2 := (state1.write 5 supportCode).jump 2
  let state3 := (state2.write 3 0).jump 3
  let state4 := (state3.write 8 1).jump 4
  let state5 := (state4.write 2 0).jump 5
  let payload := Nat.pair supportCode 0
  let state6 := (state5.write 9 payload).jump 6
  let workCode := Nat.pair 1 payload
  let entry := (state6.write 0 workCode).jump 7
  generalize hworkFuel :
    supplierSupportCountWorkFuel [tree] = workFuel
  have hworkCodeBits :
      natBitLength workCode ≤ maximumBits := by
    simpa [workCode, payload, encodeSupportWork_cons, hcode] using hworkBits
  rw [show 7 + workFuel = 6 + workFuel + 1 by omega]
  rw [run_unpairLeft_instruction (value := weightsCode)
    (by rfl) rfl
    (by simp [initialNPOracleState]) hweightsBits]
  rw [show 6 + workFuel = 5 + workFuel + 1 by omega]
  change
    runNPOracleProgram supplierSupportCountPrepareProgram maximumBits
        (5 + workFuel + 1) state1 =
      some
        (supplierSupportCountPrepareOutput weightsCode supportCode count)
  rw [run_unpairRight_instruction (value := supportCode)
    (by rfl) rfl
    (by simp [state1, initial, initialNPOracleState]) hsupportBits]
  rw [show 5 + workFuel = 4 + workFuel + 1 by omega]
  change
    runNPOracleProgram supplierSupportCountPrepareProgram maximumBits
        (4 + workFuel + 1) state2 =
      some
        (supplierSupportCountPrepareOutput weightsCode supportCode count)
  rw [run_set_instruction (value := 0)
    (by rfl) rfl hzeroBits]
  rw [show 4 + workFuel = 3 + workFuel + 1 by omega]
  change
    runNPOracleProgram supplierSupportCountPrepareProgram maximumBits
        (3 + workFuel + 1) state3 =
      some
        (supplierSupportCountPrepareOutput weightsCode supportCode count)
  rw [run_set_instruction (value := 1)
    (by rfl) rfl honeBits]
  rw [show 3 + workFuel = 2 + workFuel + 1 by omega]
  change
    runNPOracleProgram supplierSupportCountPrepareProgram maximumBits
        (2 + workFuel + 1) state4 =
      some
        (supplierSupportCountPrepareOutput weightsCode supportCode count)
  rw [run_set_instruction (value := 0)
    (by rfl) rfl hzeroBits]
  rw [show 2 + workFuel = 1 + workFuel + 1 by omega]
  change
    runNPOracleProgram supplierSupportCountPrepareProgram maximumBits
        (1 + workFuel + 1) state5 =
      some
        (supplierSupportCountPrepareOutput weightsCode supportCode count)
  rw [run_pair_instruction (value := payload)
    (by rfl) rfl
    (by simp [state5, state4, state3, state2, payload])
    hpayloadBits]
  rw [show 1 + workFuel = workFuel + 1 by omega]
  change
    runNPOracleProgram supplierSupportCountPrepareProgram maximumBits
        (workFuel + 1) state6 =
      some
        (supplierSupportCountPrepareOutput weightsCode supportCode count)
  rw [run_pair_instruction (value := workCode)
    (by rfl) rfl
    (by simp [state6, state5, state4, workCode, payload])
    hworkCodeBits]
  change
    runNPOracleProgram supplierSupportCountPrepareProgram maximumBits
        workFuel entry =
      some
        (supplierSupportCountPrepareOutput weightsCode supportCode count)
  have hrun :=
    run_supplierSupportCountWork [tree] 0 weightsCode supportCode
      maximumBits entry rfl
      (by
        simp [entry, workCode, payload, encodeSupportWork_cons, hcode])
      (by simp [entry, state6, state5, state4, state3])
      (by simp [entry, state6, state5, state4, state3, state2,
        state1])
      (by simp [entry, state6, state5, state4, state3, state2])
      (by simp [entry, state6, state5, state4])
      hworkFits
      (by simpa [supportWorkCount, hcount] using hcountSupport)
      (by simpa [supportWorkCount, hcount] using hcontext)
      (by simpa [supportWorkCount, hcount] using houtput)
  rw [hworkFuel] at hrun
  simpa [supportWorkCount, hcount] using hrun

/-- Exact canonical support count with the generator-ready context.  The only
runtime input is the pair of canonical balanced weight/support codes; neither
vector is decoded into a host or tagged linear list. -/
private theorem run_supplierSupportCountPrepareProgram
    (inputLength weightsCode : ℕ) (support : List Bool) :
    runNPOracleProgram supplierSupportCountPrepareProgram
        (supplierSupportCountPrepareBits inputLength weightsCode support)
        (supplierSupportCountPrepareFuel support)
        (initialNPOracleState inputLength
          (Nat.pair weightsCode (encodeBoolList support))) =
      some
        (supplierSupportCountPrepareOutput weightsCode
          (encodeBoolList support) (nonzeroSupportCount support)) := by
  let supportCode := encodeBoolList support
  let tree := balancedTraversalTree (support.map boolCode)
  let count := nonzeroSupportCount support
  let maximumBits :=
    supplierSupportCountPrepareBits inputLength weightsCode support
  have hbits :
      ∀ value,
        value ∈
            supplierSupportCountPrepareExecutionValues weightsCode support →
          natBitLength value ≤ maximumBits := by
    intro value hvalue
    exact supplierSupportCountPrepareBits_of_mem hvalue
  have hprefix :
      ∀ value,
        value ∈
            supplierSupportCountPreparePrefixValues weightsCode support →
          natBitLength value ≤ maximumBits := by
    intro value hvalue
    apply hbits
    unfold supplierSupportCountPrepareExecutionValues
    exact List.mem_append_left _ hvalue
  have hwork :
      ∀ value,
        value ∈ supplierSupportCountWorkValues [tree] 0 →
          natBitLength value ≤ maximumBits := by
    intro value hvalue
    apply hbits
    unfold supplierSupportCountPrepareExecutionValues
    exact List.mem_append_right _ hvalue
  have hcode : tree.code = supportCode := by
    simp [tree, supportCode, balancedTraversalTree_code, encodeBoolList]
  have hcount :
      BalancedTraversalTree.nonzeroCount tree = count := by
    simpa [tree, count] using balancedSupportTree_nonzeroCount support
  have hweightsBits : natBitLength weightsCode ≤ maximumBits := by
    apply hprefix
    simp [supplierSupportCountPreparePrefixValues]
  have hsupportBits : natBitLength supportCode ≤ maximumBits := by
    apply hprefix
    simp [supplierSupportCountPreparePrefixValues, supportCode]
  have hzeroBits : natBitLength 0 ≤ maximumBits := by
    apply hprefix
    simp [supplierSupportCountPreparePrefixValues]
  have honeBits : natBitLength 1 ≤ maximumBits := by
    apply hprefix
    simp [supplierSupportCountPreparePrefixValues]
  have hpayloadBits :
      natBitLength (Nat.pair supportCode 0) ≤ maximumBits := by
    apply hprefix
    simp [supplierSupportCountPreparePrefixValues, supportCode]
  have hworkBits :
      natBitLength (encodeSupportWork [tree]) ≤ maximumBits := by
    apply hprefix
    simp [supplierSupportCountPreparePrefixValues, tree,
      encodeSupportWork_cons, balancedTraversalTree_code, encodeBoolList]
  have hcountSupport :
      natBitLength (Nat.pair count supportCode) ≤ maximumBits := by
    apply hprefix
    simp [supplierSupportCountPreparePrefixValues, count, supportCode]
  have hcontext :
      natBitLength
          (Nat.pair weightsCode (Nat.pair count supportCode)) ≤
        maximumBits := by
    apply hprefix
    simp [supplierSupportCountPreparePrefixValues, count, supportCode]
  have houtput :
      natBitLength
          (supplierSupportCountPrepareOutput weightsCode supportCode count) ≤
        maximumBits := by
    apply hprefix
    simp [supplierSupportCountPreparePrefixValues, count, supportCode]
  have hrun :=
    run_supplierSupportCountPrepareProgram_of_fits
      inputLength weightsCode supportCode count maximumBits tree
      hcode hcount hweightsBits hsupportBits hzeroBits honeBits
      hpayloadBits hworkBits hwork hcountSupport hcontext houtput
  simpa only [supplierSupportCountPrepareFuel, supportCode, tree, count,
    maximumBits] using hrun

/-! ## Reusable balanced Boolean aggregation -/

/-- The count traversal above is the canonical Boolean aggregation primitive.
This fixed projection removes its compression-only bookkeeping and returns the
true count paired with an opaque preserved context. -/
def balancedBoolCountProjectionProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .pair 2 4 0 4
  , .halt 0
  ]

private def balancedBoolCountProjectionBits
    (context supportCode count : ℕ) : ℕ :=
  max
    (natBitLength
      (supplierSupportCountPrepareOutput context supportCode count))
    (natBitLength (Nat.pair count context))

private theorem run_balancedBoolCountProjectionProgram
    (inputLength context supportCode count : ℕ) :
    runNPOracleProgram balancedBoolCountProjectionProgram
        (balancedBoolCountProjectionBits context supportCode count) 5
        (initialNPOracleState inputLength
          (supplierSupportCountPrepareOutput context supportCode count)) =
      some (Nat.pair count context) := by
  let tail := Nat.pair context (Nat.pair count supportCode)
  let output := Nat.pair count context
  have hsourceBits :
      natBitLength
          (supplierSupportCountPrepareOutput context supportCode count) ≤
        balancedBoolCountProjectionBits context supportCode count :=
    Nat.le_max_left _ _
  have htailBits :
      natBitLength tail ≤
        balancedBoolCountProjectionBits context supportCode count := by
    exact
      (natBitLength_mono (Nat.right_le_pair count tail)).trans
        hsourceBits
  have hcountBits :
      natBitLength count ≤
        balancedBoolCountProjectionBits context supportCode count := by
    exact
      (natBitLength_mono (Nat.left_le_pair count tail)).trans
        hsourceBits
  have hcontextBits :
      natBitLength context ≤
        balancedBoolCountProjectionBits context supportCode count := by
    exact
      (natBitLength_mono
        (Nat.left_le_pair context (Nat.pair count supportCode))).trans
          htailBits
  have houtputBits :
      natBitLength output ≤
        balancedBoolCountProjectionBits context supportCode count :=
    Nat.le_max_right _ _
  rw [show 5 = 4 + 1 by omega]
  rw [run_unpairLeft_instruction (value := count)
    (by rfl) rfl
    (by
      simp [initialNPOracleState,
        supplierSupportCountPrepareOutput]) hcountBits]
  rw [show 4 = 3 + 1 by omega]
  rw [run_unpairRight_instruction (value := tail)
    (by rfl) rfl
    (by
      simp [initialNPOracleState, NPOracleState.write,
        NPOracleState.jump, supplierSupportCountPrepareOutput, tail])
    htailBits]
  rw [show 3 = 2 + 1 by omega]
  rw [run_unpairLeft_instruction (value := context)
    (by rfl) rfl
    (by
      simp [initialNPOracleState, NPOracleState.write,
        NPOracleState.jump, supplierSupportCountPrepareOutput, tail])
    hcontextBits]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction (value := output)
    (by rfl) rfl
    (by
      simp [initialNPOracleState, NPOracleState.write,
        NPOracleState.jump, supplierSupportCountPrepareOutput, tail,
        output])
    houtputBits]
  exact run_halt_instruction (fuel := 0) (value := output)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, output])
    houtputBits

def balancedBoolCountProgram : NPOracleProgram :=
  linkPrograms supplierSupportCountPrepareProgram
    balancedBoolCountProjectionProgram

def balancedBoolCountFuel (values : List Bool) : ℕ :=
  linkFuel balancedBoolCountProjectionProgram
    (supplierSupportCountPrepareFuel values) 5

def balancedBoolCountBits
    (inputLength context : ℕ) (values : List Bool) : ℕ :=
  max
    (supplierSupportCountPrepareBits inputLength context values)
    (balancedBoolCountProjectionBits context
      (encodeBoolList values) (nonzeroSupportCount values))

def balancedBoolCountOutput
    (context : ℕ) (values : List Bool) : ℕ :=
  Nat.pair (nonzeroSupportCount values) context

@[simp] theorem balancedBoolCountProgram_oracleFree :
    OracleFree balancedBoolCountProgram := by
  exact oracleFree_linkPrograms
    supplierSupportCountPrepareProgram_oracleFree (by rfl)

theorem run_balancedBoolCountProgram
    (inputLength context : ℕ) (values : List Bool) :
    runNPOracleProgram balancedBoolCountProgram
        (balancedBoolCountBits inputLength context values)
        (balancedBoolCountFuel values)
        (initialNPOracleState inputLength
          (Nat.pair context (encodeBoolList values))) =
      some (balancedBoolCountOutput context values) := by
  let count := nonzeroSupportCount values
  let supportCode := encodeBoolList values
  let maximumBits :=
    balancedBoolCountBits inputLength context values
  have hinputLengthBits :
      natBitLength inputLength ≤ maximumBits := by
    exact
      (Nat.le_max_left _ _).trans <|
        Nat.le_max_left _ _
  have hpositive : 1 ≤ maximumBits := by
    exact (show 1 ≤ natBitLength inputLength by
      unfold natBitLength
      omega).trans hinputLengthBits
  have hcountBits :
      supplierSupportCountPrepareBits inputLength context values ≤
        maximumBits :=
    Nat.le_max_left _ _
  have hprojectionBits :
      balancedBoolCountProjectionBits context supportCode count ≤
        maximumBits := by
    dsimp only [maximumBits, balancedBoolCountBits]
    simpa only [supportCode, count] using
      (Nat.le_max_right
        (supplierSupportCountPrepareBits inputLength context values)
        (balancedBoolCountProjectionBits context
          (encodeBoolList values) (nonzeroSupportCount values)))
  have hcount :
      runNPOracleProgram supplierSupportCountPrepareProgram maximumBits
          (supplierSupportCountPrepareFuel values)
          (initialNPOracleState inputLength
            (Nat.pair context supportCode)) =
        some
          (supplierSupportCountPrepareOutput context supportCode count) := by
    exact run_bits_mono
      (run_supplierSupportCountPrepareProgram inputLength context values)
      hcountBits
  have hprojection :
      runNPOracleProgram balancedBoolCountProjectionProgram maximumBits 5
          (initialNPOracleState inputLength
            (supplierSupportCountPrepareOutput
              context supportCode count)) =
        some (Nat.pair count context) := by
    exact run_bits_mono
      (run_balancedBoolCountProjectionProgram
        inputLength context supportCode count)
      hprojectionBits
  have hrun :=
    run_linkPrograms hpositive hinputLengthBits hcount hprojection
  simpa only [balancedBoolCountProgram, balancedBoolCountFuel,
    balancedBoolCountBits, balancedBoolCountOutput, supportCode,
    count, maximumBits] using hrun

/-! ## Generic nonzero aggregation

Validation callees use zero as their unique rejection result and a nonzero
payload on success.  The Boolean counter above already implements exactly the
required register semantics, so the following theorem exposes that same
program over arbitrary canonical balanced atoms.  This avoids a second
list-fold implementation for each validator family. -/

private def balancedNonzeroCountPreparePrefixValues
    (context : ℕ) (values : List ℕ) : List ℕ :=
  let valuesCode := encodeBalancedList values
  let tree := balancedTraversalTree values
  let count := nonzeroAtomCount values
  [ 0, 1, context, valuesCode, Nat.pair context valuesCode
  , Nat.pair valuesCode 0
  , encodeSupportWork [tree]
  , count
  , Nat.pair count valuesCode
  , Nat.pair context (Nat.pair count valuesCode)
  , supplierSupportCountPrepareOutput context valuesCode count
  ]

private def balancedNonzeroCountPrepareExecutionValues
    (context : ℕ) (values : List ℕ) : List ℕ :=
  let tree := balancedTraversalTree values
  balancedNonzeroCountPreparePrefixValues context values ++
    supplierSupportCountWorkValues [tree] 0

private def balancedNonzeroCountPrepareBits
    (inputLength context : ℕ) (values : List ℕ) : ℕ :=
  max (natBitLength inputLength) <|
    ((balancedNonzeroCountPrepareExecutionValues context values).map
      natBitLength).foldr max 0

private theorem balancedNonzeroCountPrepareBits_of_mem
    {inputLength context value : ℕ} {values : List ℕ}
    (hvalue :
      value ∈ balancedNonzeroCountPrepareExecutionValues context values) :
    natBitLength value ≤
      balancedNonzeroCountPrepareBits inputLength context values := by
  unfold balancedNonzeroCountPrepareBits
  apply (le_foldr_max_of_mem
    (List.mem_map.mpr ⟨value, hvalue, rfl⟩)).trans
  exact Nat.le_max_right _ _

private theorem run_balancedNonzeroCountPrepareProgram
    (inputLength context : ℕ) (values : List ℕ) :
    runNPOracleProgram supplierSupportCountPrepareProgram
        (balancedNonzeroCountPrepareBits inputLength context values)
        (7 + supplierSupportCountWorkFuel
          [balancedTraversalTree values])
        (initialNPOracleState inputLength
          (Nat.pair context (encodeBalancedList values))) =
      some
        (supplierSupportCountPrepareOutput context
          (encodeBalancedList values) (nonzeroAtomCount values)) := by
  let valuesCode := encodeBalancedList values
  let tree := balancedTraversalTree values
  let count := nonzeroAtomCount values
  let maximumBits :=
    balancedNonzeroCountPrepareBits inputLength context values
  have hbits :
      ∀ value,
        value ∈
            balancedNonzeroCountPrepareExecutionValues context values →
          natBitLength value ≤ maximumBits := by
    intro value hvalue
    exact balancedNonzeroCountPrepareBits_of_mem hvalue
  have hprefix :
      ∀ value,
        value ∈ balancedNonzeroCountPreparePrefixValues context values →
          natBitLength value ≤ maximumBits := by
    intro value hvalue
    apply hbits
    unfold balancedNonzeroCountPrepareExecutionValues
    exact List.mem_append_left _ hvalue
  have hwork :
      ∀ value,
        value ∈ supplierSupportCountWorkValues [tree] 0 →
          natBitLength value ≤ maximumBits := by
    intro value hvalue
    apply hbits
    unfold balancedNonzeroCountPrepareExecutionValues
    exact List.mem_append_right _ hvalue
  have hcode : tree.code = valuesCode := by
    simp [tree, valuesCode, balancedTraversalTree_code]
  have hcount :
      BalancedTraversalTree.nonzeroCount tree = count := by
    rw [BalancedTraversalTree.nonzeroCount_atoms]
    simp [tree, count, balancedTraversalTree_atoms]
  have hcontextBits : natBitLength context ≤ maximumBits := by
    apply hprefix
    simp [balancedNonzeroCountPreparePrefixValues]
  have hvaluesBits : natBitLength valuesCode ≤ maximumBits := by
    apply hprefix
    simp [balancedNonzeroCountPreparePrefixValues, valuesCode]
  have hzeroBits : natBitLength 0 ≤ maximumBits := by
    apply hprefix
    simp [balancedNonzeroCountPreparePrefixValues]
  have honeBits : natBitLength 1 ≤ maximumBits := by
    apply hprefix
    simp [balancedNonzeroCountPreparePrefixValues]
  have hpayloadBits :
      natBitLength (Nat.pair valuesCode 0) ≤ maximumBits := by
    apply hprefix
    simp [balancedNonzeroCountPreparePrefixValues, valuesCode]
  have hworkBits :
      natBitLength (encodeSupportWork [tree]) ≤ maximumBits := by
    apply hprefix
    simp [balancedNonzeroCountPreparePrefixValues, tree,
      encodeSupportWork_cons, balancedTraversalTree_code]
  have hcountValues :
      natBitLength (Nat.pair count valuesCode) ≤ maximumBits := by
    apply hprefix
    simp [balancedNonzeroCountPreparePrefixValues, count, valuesCode]
  have hcontextPayload :
      natBitLength
          (Nat.pair context (Nat.pair count valuesCode)) ≤
        maximumBits := by
    apply hprefix
    simp [balancedNonzeroCountPreparePrefixValues, count, valuesCode]
  have houtput :
      natBitLength
          (supplierSupportCountPrepareOutput
            context valuesCode count) ≤
        maximumBits := by
    apply hprefix
    simp [balancedNonzeroCountPreparePrefixValues, count, valuesCode]
  have hrun :=
    run_supplierSupportCountPrepareProgram_of_fits
      inputLength context valuesCode count maximumBits tree
      hcode hcount hcontextBits hvaluesBits hzeroBits honeBits
      hpayloadBits hworkBits hwork hcountValues hcontextPayload houtput
  simpa only [valuesCode, tree, count, maximumBits] using hrun

/-- Exact fuel for the generic nonzero-count interpretation of
`balancedBoolCountProgram`. -/
def balancedNonzeroCountFuel (values : List ℕ) : ℕ :=
  linkFuel balancedBoolCountProjectionProgram
    (7 + supplierSupportCountWorkFuel [balancedTraversalTree values]) 5

/-- Exact register width for generic nonzero aggregation. -/
def balancedNonzeroCountBits
    (inputLength context : ℕ) (values : List ℕ) : ℕ :=
  max
    (balancedNonzeroCountPrepareBits inputLength context values)
    (balancedBoolCountProjectionBits context
      (encodeBalancedList values) (nonzeroAtomCount values))

def balancedNonzeroCountOutput
    (context : ℕ) (values : List ℕ) : ℕ :=
  Nat.pair (nonzeroAtomCount values) context

theorem run_balancedNonzeroCountProgram
    (inputLength context : ℕ) (values : List ℕ) :
    runNPOracleProgram balancedBoolCountProgram
        (balancedNonzeroCountBits inputLength context values)
        (balancedNonzeroCountFuel values)
        (initialNPOracleState inputLength
          (Nat.pair context (encodeBalancedList values))) =
      some (balancedNonzeroCountOutput context values) := by
  let count := nonzeroAtomCount values
  let valuesCode := encodeBalancedList values
  let maximumBits :=
    balancedNonzeroCountBits inputLength context values
  have hlengthBits : natBitLength inputLength ≤ maximumBits := by
    apply (show natBitLength inputLength ≤
      balancedNonzeroCountPrepareBits inputLength context values from ?_)
      |>.trans (Nat.le_max_left _ _)
    exact Nat.le_max_left _ _
  have hpositive : 1 ≤ maximumBits := by
    exact (show 1 ≤ natBitLength inputLength by
      unfold natBitLength
      omega).trans hlengthBits
  have hcountBits :
      balancedNonzeroCountPrepareBits inputLength context values ≤
        maximumBits :=
    Nat.le_max_left _ _
  have hprojectionBits :
      balancedBoolCountProjectionBits context valuesCode count ≤
        maximumBits := by
    dsimp only [maximumBits, balancedNonzeroCountBits]
    simpa only [valuesCode, count] using
      (Nat.le_max_right
        (balancedNonzeroCountPrepareBits inputLength context values)
        (balancedBoolCountProjectionBits context
          (encodeBalancedList values) (nonzeroAtomCount values)))
  have hcount :
      runNPOracleProgram supplierSupportCountPrepareProgram maximumBits
          (7 + supplierSupportCountWorkFuel
            [balancedTraversalTree values])
          (initialNPOracleState inputLength
            (Nat.pair context valuesCode)) =
        some
          (supplierSupportCountPrepareOutput
            context valuesCode count) := by
    exact run_bits_mono
      (run_balancedNonzeroCountPrepareProgram
        inputLength context values)
      hcountBits
  have hprojection :
      runNPOracleProgram balancedBoolCountProjectionProgram maximumBits 5
          (initialNPOracleState inputLength
            (supplierSupportCountPrepareOutput
              context valuesCode count)) =
        some (Nat.pair count context) := by
    exact run_bits_mono
      (run_balancedBoolCountProjectionProgram
        inputLength context valuesCode count)
      hprojectionBits
  have hrun :=
    run_linkPrograms hpositive hlengthBits hcount hprojection
  simpa only [balancedBoolCountProgram, balancedNonzeroCountFuel,
    balancedNonzeroCountBits, balancedNonzeroCountOutput, valuesCode,
    count, maximumBits] using hrun

/-! ## Canonical rank selector -/

private def supplierSupportRankSelectorInput
    (rank weightsCode count supportCode : ℕ) : ℕ :=
  Nat.pair rank (Nat.pair weightsCode (Nat.pair count supportCode))

/-- One native-input request for the existing canonical balanced lookup. -/
def supplierSupportLookupRequest
    (inputLength weightsCode index : ℕ) : ℕ :=
  nativeInputRequest inputLength
    (Nat.pair inputLength (Nat.pair index weightsCode))

def supplierSupportRankSelectorProgram : NPOracleProgram :=
  [ .unpairLeft 0 4 1
  , .unpairRight 0 6 2
  , .unpairLeft 6 5 3
  , .unpairRight 6 7 4
  , .unpairRight 7 6 5
  , .set 3 0 6
  , .set 8 1 7
  , .set 2 0 8
  , .pair 6 2 9 9
  , .pair 8 9 0 10
  , .branchZero 0 36 11
  , .unpairRight 0 6 12
  , .unpairLeft 6 0 13
  , .unpairRight 6 2 14
  , .branchZero 0 24 15
  , .unpairLeft 0 7 16
  , .decrement 7 17
  , .branchZero 7 18 25
  , .unpairRight 0 7 19
  , .branchZero 7 23 20
  , .branchZero 4 32 21
  , .decrement 4 22
  , .increment 3 24
  , .increment 3 24
  , .copy 2 0 10
  , .unpairRight 0 6 26
  , .unpairLeft 6 0 27
  , .unpairRight 6 7 28
  , .pair 7 2 9 29
  , .pair 8 9 9 30
  , .pair 0 9 10 31
  , .pair 8 10 0 10
  , .pair 3 5 9 33
  , .pair 1 9 10 34
  , .pair 1 10 0 35
  , .halt 0
  , .halt 0
  ]

@[simp] private theorem supplierSupportRankSelectorProgram_oracleFree :
    OracleFree supplierSupportRankSelectorProgram := by
  rfl

def supplierSupportRankSelectorWorkFuel :
    List BalancedTraversalTree → ℕ → ℕ
  | [], _rank => 2
  | .empty :: rest, rank =>
      6 + supplierSupportRankSelectorWorkFuel rest rank
  | .leaf atom :: rest, rank =>
      if atom = 0 then
        12 + supplierSupportRankSelectorWorkFuel rest rank
      else
        match rank with
        | 0 => 15
        | nextRank + 1 =>
            14 + supplierSupportRankSelectorWorkFuel rest nextRank
  | .branch left right :: rest, rank =>
      15 +
        supplierSupportRankSelectorWorkFuel (left :: right :: rest) rank
termination_by trees _ => supportWorkMeasure trees
decreasing_by
  all_goals
    simp [supportWorkMeasure, BalancedTraversalTree.nodeCount] <;>
      omega

private def supplierSupportRankSelectorWorkValues :
    List BalancedTraversalTree → ℕ → ℕ → ℕ → ℕ → List ℕ
  | [], index, rank, inputLength, weightsCode =>
      [0, index, rank, inputLength, weightsCode]
  | .empty :: rest, index, rank, inputLength, weightsCode =>
      let restCode := encodeSupportWork rest
      [ encodeSupportWork (.empty :: rest)
      , Nat.pair 0 restCode
      , 0
      , restCode
      ] ++
        supplierSupportRankSelectorWorkValues rest index rank
          inputLength weightsCode
  | .leaf atom :: rest, index, rank, inputLength, weightsCode =>
      let restCode := encodeSupportWork rest
      let treeCode := (BalancedTraversalTree.leaf atom).code
      let common :=
        [ encodeSupportWork (.leaf atom :: rest)
        , Nat.pair treeCode restCode
        , treeCode
        , restCode
        , 1
        , 0
        , atom
        , index
        , rank
        ]
      if atom = 0 then
        common ++ [index + 1] ++
          supplierSupportRankSelectorWorkValues rest (index + 1) rank
            inputLength weightsCode
      else
        match rank with
        | 0 =>
            let indexWeights := Nat.pair index weightsCode
            let lookupInput := Nat.pair inputLength indexWeights
            common ++
              [ indexWeights
              , lookupInput
              , supplierSupportLookupRequest inputLength weightsCode index
              ]
        | nextRank + 1 =>
            common ++ [nextRank, index + 1] ++
              supplierSupportRankSelectorWorkValues rest (index + 1)
                nextRank inputLength weightsCode
  | .branch left right :: rest, index, rank, inputLength, weightsCode =>
      let restCode := encodeSupportWork rest
      let treeCode := (BalancedTraversalTree.branch left right).code
      let branchPayload := Nat.pair left.code right.code
      let rightPayload := Nat.pair right.code restCode
      let rightStack := Nat.pair 1 rightPayload
      let leftPayload := Nat.pair left.code rightStack
      let nextStack := Nat.pair 1 leftPayload
      [ encodeSupportWork (.branch left right :: rest)
      , Nat.pair treeCode restCode
      , treeCode
      , restCode
      , 2
      , 1
      , branchPayload
      , left.code
      , right.code
      , rightPayload
      , rightStack
      , leftPayload
      , nextStack
      , index
      , rank
      ] ++
        supplierSupportRankSelectorWorkValues (left :: right :: rest)
          index rank inputLength weightsCode
termination_by trees _ _ _ _ => supportWorkMeasure trees
decreasing_by
  all_goals
    simp [supportWorkMeasure, BalancedTraversalTree.nodeCount] <;>
      omega

def supplierSupportRankSelectorFuel
    (support : List Bool) (rank : ℕ) : ℕ :=
  10 + supplierSupportRankSelectorWorkFuel
    [balancedTraversalTree (support.map boolCode)] rank

private def supplierSupportRankSelectorPrefixValues
    (inputLength weightsCode count supportCode rank : ℕ) : List ℕ :=
  let countSupport := Nat.pair count supportCode
  let context := Nat.pair weightsCode countSupport
  let payload := Nat.pair supportCode 0
  [ 0
  , 1
  , inputLength
  , rank
  , weightsCode
  , count
  , supportCode
  , countSupport
  , context
  , supplierSupportRankSelectorInput rank weightsCode count supportCode
  , payload
  , Nat.pair 1 payload
  ]

private def supplierSupportRankSelectorExecutionValues
    (weights : List ℕ) (support : List Bool) (rank : ℕ) : List ℕ :=
  let inputLength := weights.length
  let weightsCode := encodeBalancedList weights
  let count := nonzeroSupportCount support
  let supportCode := encodeBoolList support
  let tree := balancedTraversalTree (support.map boolCode)
  supplierSupportRankSelectorPrefixValues inputLength weightsCode count
      supportCode rank ++
    supplierSupportRankSelectorWorkValues [tree] 0 rank inputLength
      weightsCode

private def supplierSupportRankSelectorBits
    (weights : List ℕ) (support : List Bool) (rank : ℕ) : ℕ :=
  ((supplierSupportRankSelectorExecutionValues weights support rank).map
    natBitLength).foldr max 0

private theorem supplierSupportRankSelectorBits_of_mem
    {weights : List ℕ} {support : List Bool} {rank value : ℕ}
    (hmem :
      value ∈
        supplierSupportRankSelectorExecutionValues weights support rank) :
    natBitLength value ≤
      supplierSupportRankSelectorBits weights support rank := by
  unfold supplierSupportRankSelectorBits
  exact le_foldr_max_of_mem (List.mem_map.mpr ⟨value, hmem, rfl⟩)

private theorem run_supplierSupportRankSelectorWork
    (trees : List BalancedTraversalTree)
    (index rank inputLength weightsCode selectedIndex maximumBits : ℕ)
    (state : NPOracleState)
    (hpc : state.pc = 10)
    (hwork : state.registers 0 = encodeSupportWork trees)
    (hinputLength : state.registers 1 = inputLength)
    (hindex : state.registers 3 = index)
    (hrank : state.registers 4 = rank)
    (hweights : state.registers 5 = weightsCode)
    (hone : state.registers 8 = 1)
    (hselected :
      (supportWorkSelectedIndicesFrom index trees)[rank]? =
        some selectedIndex)
    (hfits :
      ∀ value,
        value ∈
            supplierSupportRankSelectorWorkValues trees index rank
              inputLength weightsCode →
          natBitLength value ≤ maximumBits) :
    runNPOracleProgram supplierSupportRankSelectorProgram maximumBits
        (supplierSupportRankSelectorWorkFuel trees rank) state =
      some
        (supplierSupportLookupRequest inputLength weightsCode
          selectedIndex) := by
  induction trees, rank using
      supplierSupportRankSelectorWorkFuel.induct
      generalizing index state with
  | case1 rank =>
      cases rank <;>
        simp [supportWorkSelectedIndicesFrom, supportWorkAtoms,
          nonzeroAtomIndicesFrom] at hselected
  | case2 rest rank inductionHypothesis =>
      let restCode := encodeSupportWork rest
      let payload := Nat.pair 0 restCode
      let stackCode := Nat.pair 1 payload
      let state1 := state.jump 11
      let state2 := (state1.write 6 payload).jump 12
      let state3 := (state2.write 0 0).jump 13
      let state4 := (state3.write 2 restCode).jump 14
      let state5 := state4.jump 24
      let nextState := (state5.write 0 restCode).jump 10
      have hstackNonzero : stackCode ≠ 0 := by
        dsimp only [stackCode]
        apply Nat.ne_of_gt
        exact lt_of_lt_of_le (by omega : 0 < 1)
          (Nat.left_le_pair 1 payload)
      have hpayloadBits : natBitLength payload ≤ maximumBits := by
        apply hfits
        simp [supplierSupportRankSelectorWorkValues, payload, restCode]
      have hzeroBits : natBitLength 0 ≤ maximumBits := by
        apply hfits
        simp [supplierSupportRankSelectorWorkValues]
      have hrestBits : natBitLength restCode ≤ maximumBits := by
        apply hfits
        simp [supplierSupportRankSelectorWorkValues, restCode]
      have hfitsRest :
          ∀ value,
            value ∈
                supplierSupportRankSelectorWorkValues rest index rank
                  inputLength weightsCode →
              natBitLength value ≤ maximumBits := by
        intro value hvalue
        apply hfits
        simp [supplierSupportRankSelectorWorkValues, hvalue]
      have hselectedRest :
          (supportWorkSelectedIndicesFrom index rest)[rank]? =
            some selectedIndex := by
        simpa [supportWorkSelectedIndicesFrom] using hselected
      rw [supplierSupportRankSelectorWorkFuel]
      rw [show
        6 + supplierSupportRankSelectorWorkFuel rest rank =
          (5 + supplierSupportRankSelectorWorkFuel rest rank) + 1 by omega]
      rw [run_branchZero_instruction (by rfl) hpc]
      rw [hwork, encodeSupportWork_cons, if_neg (by
        simpa [stackCode, payload, restCode] using hstackNonzero)]
      change
        runNPOracleProgram supplierSupportRankSelectorProgram maximumBits
            (5 + supplierSupportRankSelectorWorkFuel rest rank) state1 =
          some
            (supplierSupportLookupRequest inputLength weightsCode
              selectedIndex)
      rw [show
        5 + supplierSupportRankSelectorWorkFuel rest rank =
          (4 + supplierSupportRankSelectorWorkFuel rest rank) + 1 by omega]
      rw [run_unpairRight_instruction (value := payload)
        (by rfl) rfl
        (by
          simp [state1, payload, restCode, encodeSupportWork_cons, hwork])
        hpayloadBits]
      change
        runNPOracleProgram supplierSupportRankSelectorProgram maximumBits
            (4 + supplierSupportRankSelectorWorkFuel rest rank) state2 =
          some
            (supplierSupportLookupRequest inputLength weightsCode
              selectedIndex)
      rw [show
        4 + supplierSupportRankSelectorWorkFuel rest rank =
          (3 + supplierSupportRankSelectorWorkFuel rest rank) + 1 by omega]
      rw [run_unpairLeft_instruction (value := 0)
        (by rfl) rfl
        (by simp [state2, payload])
        hzeroBits]
      change
        runNPOracleProgram supplierSupportRankSelectorProgram maximumBits
            (3 + supplierSupportRankSelectorWorkFuel rest rank) state3 =
          some
            (supplierSupportLookupRequest inputLength weightsCode
              selectedIndex)
      rw [show
        3 + supplierSupportRankSelectorWorkFuel rest rank =
          (2 + supplierSupportRankSelectorWorkFuel rest rank) + 1 by omega]
      rw [run_unpairRight_instruction (value := restCode)
        (by rfl) rfl
        (by simp [state3, state2, payload, restCode])
        hrestBits]
      change
        runNPOracleProgram supplierSupportRankSelectorProgram maximumBits
            (2 + supplierSupportRankSelectorWorkFuel rest rank) state4 =
          some
            (supplierSupportLookupRequest inputLength weightsCode
              selectedIndex)
      rw [show
        2 + supplierSupportRankSelectorWorkFuel rest rank =
          (1 + supplierSupportRankSelectorWorkFuel rest rank) + 1 by omega]
      rw [run_branchZero_instruction (by rfl) rfl]
      rw [show state4.registers 0 = 0 by simp [state4, state3]]
      rw [if_pos rfl]
      change
        runNPOracleProgram supplierSupportRankSelectorProgram maximumBits
            (1 + supplierSupportRankSelectorWorkFuel rest rank) state5 =
          some
            (supplierSupportLookupRequest inputLength weightsCode
              selectedIndex)
      rw [show
        1 + supplierSupportRankSelectorWorkFuel rest rank =
          supplierSupportRankSelectorWorkFuel rest rank + 1 by omega]
      rw [run_copy_instruction (value := restCode)
        (by rfl) rfl
        (by simp [state5, state4, restCode])
        hrestBits]
      change
        runNPOracleProgram supplierSupportRankSelectorProgram maximumBits
            (supplierSupportRankSelectorWorkFuel rest rank) nextState =
          some
            (supplierSupportLookupRequest inputLength weightsCode
              selectedIndex)
      exact inductionHypothesis index nextState rfl
        (by simp [nextState, restCode])
        (by simp [nextState, state5, state4, state3, state2, state1,
          hinputLength])
        (by simp [nextState, state5, state4, state3, state2, state1,
          hindex])
        (by simp [nextState, state5, state4, state3, state2, state1,
          hrank])
        (by simp [nextState, state5, state4, state3, state2, state1,
          hweights])
        (by simp [nextState, state5, state4, state3, state2, state1,
          hone])
        hselectedRest hfitsRest
  | case3 rest rank inductionHypothesis =>
      let nextIndex := index + 1
      let restCode := encodeSupportWork rest
      let treeCode := (BalancedTraversalTree.leaf 0).code
      let payload := Nat.pair treeCode restCode
      let stackCode := Nat.pair 1 payload
      let state1 := state.jump 11
      let state2 := (state1.write 6 payload).jump 12
      let state3 := (state2.write 0 treeCode).jump 13
      let state4 := (state3.write 2 restCode).jump 14
      let state5 := state4.jump 15
      let state6 := (state5.write 7 1).jump 16
      let state7 := (state6.write 7 0).jump 17
      let state8 := state7.jump 18
      let state9 := (state8.write 7 0).jump 19
      let state10 := state9.jump 23
      let state11 := (state10.write 3 nextIndex).jump 24
      let nextState := (state11.write 0 restCode).jump 10
      have hstackNonzero : stackCode ≠ 0 := by
        dsimp only [stackCode]
        apply Nat.ne_of_gt
        exact lt_of_lt_of_le (by omega : 0 < 1)
          (Nat.left_le_pair 1 payload)
      have hbits (value : ℕ)
          (hvalue :
            value ∈
              [stackCode, payload, treeCode, restCode, 1, 0, index,
                rank, nextIndex]) :
          natBitLength value ≤ maximumBits := by
        apply hfits
        rw [supplierSupportRankSelectorWorkValues.eq_def]
        simp [stackCode, payload,
          treeCode, restCode, nextIndex] at hvalue ⊢
        aesop
      have hfitsRest :
          ∀ value,
            value ∈
                supplierSupportRankSelectorWorkValues rest nextIndex rank
                  inputLength weightsCode →
              natBitLength value ≤ maximumBits := by
        intro value hvalue
        apply hfits
        rw [supplierSupportRankSelectorWorkValues.eq_def]
        simp [nextIndex, hvalue]
      have hselectedRest :
          (supportWorkSelectedIndicesFrom nextIndex rest)[rank]? =
            some selectedIndex := by
        simpa [supportWorkSelectedIndicesFrom, nonzeroAtomIndicesFrom,
          nextIndex] using hselected
      rw [supplierSupportRankSelectorWorkFuel.eq_def]
      simp only [if_true]
      rw [show
        12 + supplierSupportRankSelectorWorkFuel rest rank =
          (11 + supplierSupportRankSelectorWorkFuel rest rank) + 1 by omega]
      rw [run_branchZero_instruction (by rfl) hpc]
      rw [hwork, encodeSupportWork_cons, if_neg (by
        simpa [stackCode, payload, treeCode, restCode] using
          hstackNonzero)]
      rw [show
        11 + supplierSupportRankSelectorWorkFuel rest rank =
          (10 + supplierSupportRankSelectorWorkFuel rest rank) + 1 by omega]
      rw [run_unpairRight_instruction (value := payload)
        (by rfl) rfl
        (by simp [payload, treeCode, restCode, encodeSupportWork_cons,
          hwork])
        (hbits payload (by simp))]
      rw [show
        10 + supplierSupportRankSelectorWorkFuel rest rank =
          (9 + supplierSupportRankSelectorWorkFuel rest rank) + 1 by omega]
      rw [run_unpairLeft_instruction (value := treeCode)
        (by rfl) rfl
        (by simp [payload])
        (hbits treeCode (by simp))]
      rw [show
        9 + supplierSupportRankSelectorWorkFuel rest rank =
          (8 + supplierSupportRankSelectorWorkFuel rest rank) + 1 by omega]
      rw [run_unpairRight_instruction (value := restCode)
        (by rfl) rfl
        (by simp [payload])
        (hbits restCode (by simp))]
      rw [show
        8 + supplierSupportRankSelectorWorkFuel rest rank =
          (7 + supplierSupportRankSelectorWorkFuel rest rank) + 1 by omega]
      rw [run_branchZero_instruction (by rfl) rfl]
      rw [show state4.registers 0 = treeCode by simp [state4, state3]]
      rw [if_neg (by
        have := Nat.left_le_pair 1 0
        simp [treeCode]
        omega)]
      rw [show
        7 + supplierSupportRankSelectorWorkFuel rest rank =
          (6 + supplierSupportRankSelectorWorkFuel rest rank) + 1 by omega]
      rw [run_unpairLeft_instruction (value := 1)
        (by rfl) rfl
        (by simp [treeCode])
        (hbits 1 (by simp))]
      rw [show
        6 + supplierSupportRankSelectorWorkFuel rest rank =
          (5 + supplierSupportRankSelectorWorkFuel rest rank) + 1 by omega]
      rw [run_decrement_instruction (value := 0)
        (by rfl) rfl
        (by simp)
        (hbits 0 (by simp))]
      rw [show
        5 + supplierSupportRankSelectorWorkFuel rest rank =
          (4 + supplierSupportRankSelectorWorkFuel rest rank) + 1 by omega]
      rw [run_branchZero_instruction (by rfl) rfl]
      rw [show state7.registers 7 = 0 by simp [state7]]
      rw [if_pos rfl]
      rw [show
        4 + supplierSupportRankSelectorWorkFuel rest rank =
          (3 + supplierSupportRankSelectorWorkFuel rest rank) + 1 by omega]
      rw [run_unpairRight_instruction (value := 0)
        (by rfl) rfl
        (by simp [treeCode])
        (hbits 0 (by simp))]
      rw [show
        3 + supplierSupportRankSelectorWorkFuel rest rank =
          (2 + supplierSupportRankSelectorWorkFuel rest rank) + 1 by omega]
      rw [run_branchZero_instruction (by rfl) rfl]
      rw [show state9.registers 7 = 0 by simp [state9]]
      rw [if_pos rfl]
      rw [show
        2 + supplierSupportRankSelectorWorkFuel rest rank =
          (1 + supplierSupportRankSelectorWorkFuel rest rank) + 1 by omega]
      rw [run_increment_instruction (value := nextIndex)
        (by rfl) rfl
        (by simp [nextIndex, hindex])
        (hbits nextIndex (by simp))]
      rw [show
        1 + supplierSupportRankSelectorWorkFuel rest rank =
          supplierSupportRankSelectorWorkFuel rest rank + 1 by omega]
      rw [run_copy_instruction (value := restCode)
        (by rfl) rfl
        (by simp [restCode])
        (hbits restCode (by simp))]
      change
        runNPOracleProgram supplierSupportRankSelectorProgram maximumBits
            (supplierSupportRankSelectorWorkFuel rest rank) nextState =
          some
            (supplierSupportLookupRequest inputLength weightsCode
              selectedIndex)
      exact inductionHypothesis nextIndex nextState rfl
        (by simp [nextState, restCode])
        (by simp [nextState, state11, state10, state9, state8, state7,
          state6, state5, state4, state3, state2, state1,
          hinputLength])
        (by simp [nextState, state11, nextIndex])
        (by simp [nextState, state11, state10, state9, state8, state7,
          state6, state5, state4, state3, state2, state1, hrank])
        (by simp [nextState, state11, state10, state9, state8, state7,
          state6, state5, state4, state3, state2, state1,
          hweights])
        (by simp [nextState, state11, state10, state9, state8, state7,
          state6, state5, state4, state3, state2, state1, hone])
        hselectedRest hfitsRest
  | case4 atom rest hatom =>
      let restCode := encodeSupportWork rest
      let treeCode := (BalancedTraversalTree.leaf atom).code
      let payload := Nat.pair treeCode restCode
      let stackCode := Nat.pair 1 payload
      let indexWeights := Nat.pair index weightsCode
      let lookupInput := Nat.pair inputLength indexWeights
      let output :=
        supplierSupportLookupRequest inputLength weightsCode index
      let state1 := state.jump 11
      let state2 := (state1.write 6 payload).jump 12
      let state3 := (state2.write 0 treeCode).jump 13
      let state4 := (state3.write 2 restCode).jump 14
      let state5 := state4.jump 15
      let state6 := (state5.write 7 1).jump 16
      let state7 := (state6.write 7 0).jump 17
      let state8 := state7.jump 18
      let state9 := (state8.write 7 atom).jump 19
      let state10 := state9.jump 20
      let state11 := state10.jump 32
      let state12 := (state11.write 9 indexWeights).jump 33
      let state13 := (state12.write 10 lookupInput).jump 34
      let state14 := (state13.write 0 output).jump 35
      have hselectedIndex : index = selectedIndex := by
        simpa [supportWorkSelectedIndicesFrom, nonzeroAtomIndicesFrom,
          hatom] using hselected
      subst selectedIndex
      have hstackNonzero : stackCode ≠ 0 := by
        dsimp only [stackCode]
        apply Nat.ne_of_gt
        exact lt_of_lt_of_le (by omega : 0 < 1)
          (Nat.left_le_pair 1 payload)
      have htreeNonzero : treeCode ≠ 0 := by
        dsimp only [treeCode]
        apply Nat.ne_of_gt
        exact lt_of_lt_of_le (by omega : 0 < 1)
          (Nat.left_le_pair 1 atom)
      have hbits (value : ℕ)
          (hvalue :
            value ∈
              [stackCode, payload, treeCode, restCode, 1, 0, atom,
                index, indexWeights, lookupInput, output]) :
          natBitLength value ≤ maximumBits := by
        apply hfits
        rw [supplierSupportRankSelectorWorkValues.eq_def]
        simp [hatom, stackCode, payload, treeCode, restCode,
          indexWeights, lookupInput, output] at hvalue ⊢
        aesop
      rw [supplierSupportRankSelectorWorkFuel.eq_def]
      simp only [hatom, ↓reduceIte]
      rw [show 15 = 14 + 1 by omega]
      rw [run_branchZero_instruction (by rfl) hpc]
      rw [hwork, encodeSupportWork_cons, if_neg (by
        simpa [stackCode, payload, treeCode, restCode] using
          hstackNonzero)]
      rw [show 14 = 13 + 1 by omega]
      rw [run_unpairRight_instruction (value := payload)
        (by rfl) rfl
        (by simp [payload, treeCode, restCode, encodeSupportWork_cons,
          hwork])
        (hbits payload (by simp))]
      rw [show 13 = 12 + 1 by omega]
      rw [run_unpairLeft_instruction (value := treeCode)
        (by rfl) rfl
        (by simp [payload])
        (hbits treeCode (by simp))]
      rw [show 12 = 11 + 1 by omega]
      rw [run_unpairRight_instruction (value := restCode)
        (by rfl) rfl
        (by simp [payload])
        (hbits restCode (by simp))]
      rw [show 11 = 10 + 1 by omega]
      rw [run_branchZero_instruction (by rfl) rfl]
      rw [show state4.registers 0 = treeCode by simp [state4, state3]]
      rw [if_neg htreeNonzero]
      rw [show 10 = 9 + 1 by omega]
      rw [run_unpairLeft_instruction (value := 1)
        (by rfl) rfl
        (by simp [treeCode])
        (hbits 1 (by simp))]
      rw [show 9 = 8 + 1 by omega]
      rw [run_decrement_instruction (value := 0)
        (by rfl) rfl
        (by simp)
        (hbits 0 (by simp))]
      rw [show 8 = 7 + 1 by omega]
      rw [run_branchZero_instruction (by rfl) rfl]
      rw [show state7.registers 7 = 0 by simp [state7]]
      rw [if_pos rfl]
      rw [show 7 = 6 + 1 by omega]
      rw [run_unpairRight_instruction (value := atom)
        (by rfl) rfl
        (by simp [treeCode])
        (hbits atom (by simp))]
      rw [show 6 = 5 + 1 by omega]
      rw [run_branchZero_instruction (by rfl) rfl]
      rw [show state9.registers 7 = atom by simp [state9]]
      rw [if_neg hatom]
      rw [show 5 = 4 + 1 by omega]
      rw [run_branchZero_instruction (by rfl) rfl]
      rw [show state10.registers 4 = 0 by
        simp [state10, state9, state8, state7, state6, state5, state4,
          state3, state2, state1, hrank]]
      rw [if_pos rfl]
      rw [show 4 = 3 + 1 by omega]
      rw [run_pair_instruction (value := indexWeights)
        (by rfl) rfl
        (by simp [indexWeights, hindex, hweights])
        (hbits indexWeights (by simp))]
      rw [show 3 = 2 + 1 by omega]
      rw [run_pair_instruction (value := lookupInput)
        (by rfl) rfl
        (by simp [lookupInput, hinputLength, indexWeights])
        (hbits lookupInput (by simp))]
      rw [show 2 = 1 + 1 by omega]
      rw [run_pair_instruction (value := output)
        (by rfl) rfl
        (by
          simp [output, supplierSupportLookupRequest, nativeInputRequest,
            hinputLength, lookupInput, indexWeights])
        (hbits output (by simp))]
      exact run_halt_instruction (fuel := 0) (by rfl) rfl
        (by simp [output])
        (hbits output (by simp))
  | case5 atom rest hatom nextRank inductionHypothesis =>
      let nextIndex := index + 1
      let restCode := encodeSupportWork rest
      let treeCode := (BalancedTraversalTree.leaf atom).code
      let payload := Nat.pair treeCode restCode
      let stackCode := Nat.pair 1 payload
      let state1 := state.jump 11
      let state2 := (state1.write 6 payload).jump 12
      let state3 := (state2.write 0 treeCode).jump 13
      let state4 := (state3.write 2 restCode).jump 14
      let state5 := state4.jump 15
      let state6 := (state5.write 7 1).jump 16
      let state7 := (state6.write 7 0).jump 17
      let state8 := state7.jump 18
      let state9 := (state8.write 7 atom).jump 19
      let state10 := state9.jump 20
      let state11 := state10.jump 21
      let state12 := (state11.write 4 nextRank).jump 22
      let state13 := (state12.write 3 nextIndex).jump 24
      let nextState := (state13.write 0 restCode).jump 10
      have hstackNonzero : stackCode ≠ 0 := by
        dsimp only [stackCode]
        apply Nat.ne_of_gt
        exact lt_of_lt_of_le (by omega : 0 < 1)
          (Nat.left_le_pair 1 payload)
      have htreeNonzero : treeCode ≠ 0 := by
        dsimp only [treeCode]
        apply Nat.ne_of_gt
        exact lt_of_lt_of_le (by omega : 0 < 1)
          (Nat.left_le_pair 1 atom)
      have hbits (value : ℕ)
          (hvalue :
            value ∈
              [stackCode, payload, treeCode, restCode, 1, 0, atom,
                index, nextRank + 1, nextRank, nextIndex]) :
          natBitLength value ≤ maximumBits := by
        apply hfits
        rw [supplierSupportRankSelectorWorkValues.eq_def]
        simp [hatom, stackCode, payload, treeCode, restCode,
          nextIndex] at hvalue ⊢
        aesop
      have hfitsRest :
          ∀ value,
            value ∈
                supplierSupportRankSelectorWorkValues rest nextIndex
                  nextRank inputLength weightsCode →
              natBitLength value ≤ maximumBits := by
        intro value hvalue
        apply hfits
        rw [supplierSupportRankSelectorWorkValues.eq_def]
        simp [hatom, nextIndex, hvalue]
      have hselectedRest :
          (supportWorkSelectedIndicesFrom nextIndex rest)[nextRank]? =
            some selectedIndex := by
        simpa [supportWorkSelectedIndicesFrom, nonzeroAtomIndicesFrom,
          hatom, nextIndex] using hselected
      rw [supplierSupportRankSelectorWorkFuel.eq_def]
      simp only [hatom, ↓reduceIte]
      rw [show
        14 + supplierSupportRankSelectorWorkFuel rest nextRank =
          (13 + supplierSupportRankSelectorWorkFuel rest nextRank) + 1
            by omega]
      rw [run_branchZero_instruction (by rfl) hpc]
      rw [hwork, encodeSupportWork_cons, if_neg (by
        simpa [stackCode, payload, treeCode, restCode] using
          hstackNonzero)]
      rw [show
        13 + supplierSupportRankSelectorWorkFuel rest nextRank =
          (12 + supplierSupportRankSelectorWorkFuel rest nextRank) + 1
            by omega]
      rw [run_unpairRight_instruction (value := payload)
        (by rfl) rfl
        (by simp [payload, treeCode, restCode, encodeSupportWork_cons,
          hwork])
        (hbits payload (by simp))]
      rw [show
        12 + supplierSupportRankSelectorWorkFuel rest nextRank =
          (11 + supplierSupportRankSelectorWorkFuel rest nextRank) + 1
            by omega]
      rw [run_unpairLeft_instruction (value := treeCode)
        (by rfl) rfl
        (by simp [payload])
        (hbits treeCode (by simp))]
      rw [show
        11 + supplierSupportRankSelectorWorkFuel rest nextRank =
          (10 + supplierSupportRankSelectorWorkFuel rest nextRank) + 1
            by omega]
      rw [run_unpairRight_instruction (value := restCode)
        (by rfl) rfl
        (by simp [payload])
        (hbits restCode (by simp))]
      rw [show
        10 + supplierSupportRankSelectorWorkFuel rest nextRank =
          (9 + supplierSupportRankSelectorWorkFuel rest nextRank) + 1
            by omega]
      rw [run_branchZero_instruction (by rfl) rfl]
      rw [show state4.registers 0 = treeCode by simp [state4, state3]]
      rw [if_neg htreeNonzero]
      rw [show
        9 + supplierSupportRankSelectorWorkFuel rest nextRank =
          (8 + supplierSupportRankSelectorWorkFuel rest nextRank) + 1
            by omega]
      rw [run_unpairLeft_instruction (value := 1)
        (by rfl) rfl
        (by simp [treeCode])
        (hbits 1 (by simp))]
      rw [show
        8 + supplierSupportRankSelectorWorkFuel rest nextRank =
          (7 + supplierSupportRankSelectorWorkFuel rest nextRank) + 1
            by omega]
      rw [run_decrement_instruction (value := 0)
        (by rfl) rfl
        (by simp)
        (hbits 0 (by simp))]
      rw [show
        7 + supplierSupportRankSelectorWorkFuel rest nextRank =
          (6 + supplierSupportRankSelectorWorkFuel rest nextRank) + 1
            by omega]
      rw [run_branchZero_instruction (by rfl) rfl]
      rw [show state7.registers 7 = 0 by simp [state7]]
      rw [if_pos rfl]
      rw [show
        6 + supplierSupportRankSelectorWorkFuel rest nextRank =
          (5 + supplierSupportRankSelectorWorkFuel rest nextRank) + 1
            by omega]
      rw [run_unpairRight_instruction (value := atom)
        (by rfl) rfl
        (by simp [treeCode])
        (hbits atom (by simp))]
      rw [show
        5 + supplierSupportRankSelectorWorkFuel rest nextRank =
          (4 + supplierSupportRankSelectorWorkFuel rest nextRank) + 1
            by omega]
      rw [run_branchZero_instruction (by rfl) rfl]
      rw [show state9.registers 7 = atom by simp [state9]]
      rw [if_neg hatom]
      rw [show
        4 + supplierSupportRankSelectorWorkFuel rest nextRank =
          (3 + supplierSupportRankSelectorWorkFuel rest nextRank) + 1
            by omega]
      rw [run_branchZero_instruction (by rfl) rfl]
      rw [show state10.registers 4 = nextRank + 1 by
        simp [state10, state9, state8, state7, state6, state5, state4,
          state3, state2, state1, hrank]]
      rw [if_neg (by omega)]
      rw [show
        3 + supplierSupportRankSelectorWorkFuel rest nextRank =
          (2 + supplierSupportRankSelectorWorkFuel rest nextRank) + 1
            by omega]
      rw [run_decrement_instruction (value := nextRank)
        (by rfl) rfl
        (by simp [hrank])
        (hbits nextRank (by simp))]
      rw [show
        2 + supplierSupportRankSelectorWorkFuel rest nextRank =
          (1 + supplierSupportRankSelectorWorkFuel rest nextRank) + 1
            by omega]
      rw [run_increment_instruction (value := nextIndex)
        (by rfl) rfl
        (by simp [nextIndex, hindex])
        (hbits nextIndex (by simp))]
      rw [show
        1 + supplierSupportRankSelectorWorkFuel rest nextRank =
          supplierSupportRankSelectorWorkFuel rest nextRank + 1 by omega]
      rw [run_copy_instruction (value := restCode)
        (by rfl) rfl
        (by simp [restCode])
        (hbits restCode (by simp))]
      change
        runNPOracleProgram supplierSupportRankSelectorProgram maximumBits
            (supplierSupportRankSelectorWorkFuel rest nextRank) nextState =
          some
            (supplierSupportLookupRequest inputLength weightsCode
              selectedIndex)
      exact inductionHypothesis nextIndex nextState rfl
        (by simp [nextState, restCode])
        (by simp [nextState, state13, state12, state11, state10, state9,
          state8, state7, state6, state5, state4, state3, state2, state1,
          hinputLength])
        (by simp [nextState, state13, nextIndex])
        (by simp [nextState, state13, state12])
        (by simp [nextState, state13, state12, state11, state10, state9,
          state8, state7, state6, state5, state4, state3, state2, state1,
          hweights])
        (by simp [nextState, state13, state12, state11, state10, state9,
          state8, state7, state6, state5, state4, state3, state2, state1,
          hone])
        hselectedRest hfitsRest
  | case6 left right rest rank inductionHypothesis =>
      let restCode := encodeSupportWork rest
      let treeCode := (BalancedTraversalTree.branch left right).code
      let branchPayload := Nat.pair left.code right.code
      let payload := Nat.pair treeCode restCode
      let rightPayload := Nat.pair right.code restCode
      let rightStack := Nat.pair 1 rightPayload
      let leftPayload := Nat.pair left.code rightStack
      let nextStack := Nat.pair 1 leftPayload
      let state1 := state.jump 11
      let state2 := (state1.write 6 payload).jump 12
      let state3 := (state2.write 0 treeCode).jump 13
      let state4 := (state3.write 2 restCode).jump 14
      let state5 := state4.jump 15
      let state6 := (state5.write 7 2).jump 16
      let state7 := (state6.write 7 1).jump 17
      let state8 := state7.jump 25
      let state9 := (state8.write 6 branchPayload).jump 26
      let state10 := (state9.write 0 left.code).jump 27
      let state11 := (state10.write 7 right.code).jump 28
      let state12 := (state11.write 9 rightPayload).jump 29
      let state13 := (state12.write 9 rightStack).jump 30
      let state14 := (state13.write 10 leftPayload).jump 31
      let nextState := (state14.write 0 nextStack).jump 10
      have hstackNonzero :
          encodeSupportWork
              (BalancedTraversalTree.branch left right :: rest) ≠ 0 := by
        rw [encodeSupportWork_cons]
        apply Nat.ne_of_gt
        exact lt_of_lt_of_le (by omega : 0 < 1)
          (Nat.left_le_pair 1
            (Nat.pair
              (BalancedTraversalTree.branch left right).code
              (encodeSupportWork rest)))
      have htreeNonzero : treeCode ≠ 0 := by
        dsimp only [treeCode]
        apply Nat.ne_of_gt
        exact lt_of_lt_of_le (by omega : 0 < 2)
          (Nat.left_le_pair 2 branchPayload)
      have honeNonzero : (1 : ℕ) ≠ 0 := by omega
      have hbits (value : ℕ)
          (hvalue :
            value ∈
              [ encodeSupportWork
                  (BalancedTraversalTree.branch left right :: rest)
              , payload
              , treeCode
              , restCode
              , 2
              , 1
              , branchPayload
              , left.code
              , right.code
              , rightPayload
              , rightStack
              , leftPayload
              , nextStack
              , index
              , rank
              ]) :
          natBitLength value ≤ maximumBits := by
        apply hfits
        rw [supplierSupportRankSelectorWorkValues.eq_def]
        simp [payload, treeCode, restCode, branchPayload, rightPayload,
          rightStack, leftPayload, nextStack] at hvalue ⊢
        aesop
      have hfitsNext :
          ∀ value,
            value ∈
                supplierSupportRankSelectorWorkValues
                  (left :: right :: rest) index rank inputLength
                    weightsCode →
              natBitLength value ≤ maximumBits := by
        intro value hvalue
        apply hfits
        rw [supplierSupportRankSelectorWorkValues.eq_def]
        simp [hvalue]
      have hselectedNext :
          (supportWorkSelectedIndicesFrom index
              (left :: right :: rest))[rank]? =
            some selectedIndex := by
        simpa only [supportWorkSelectedIndicesFrom,
          supportWorkAtoms_branch_cons] using hselected
      rw [supplierSupportRankSelectorWorkFuel.eq_def]
      change
        runNPOracleProgram supplierSupportRankSelectorProgram maximumBits
            (15 +
              supplierSupportRankSelectorWorkFuel
                (left :: right :: rest) rank) state =
          some
            (supplierSupportLookupRequest inputLength weightsCode
              selectedIndex)
      rw [show
        15 +
            supplierSupportRankSelectorWorkFuel
              (left :: right :: rest) rank =
          (14 +
            supplierSupportRankSelectorWorkFuel
              (left :: right :: rest) rank) + 1 by omega]
      rw [run_branchZero_instruction (by rfl) hpc]
      rw [hwork, if_neg hstackNonzero]
      rw [show
        14 +
            supplierSupportRankSelectorWorkFuel
              (left :: right :: rest) rank =
          (13 +
            supplierSupportRankSelectorWorkFuel
              (left :: right :: rest) rank) + 1 by omega]
      rw [run_unpairRight_instruction (value := payload)
        (by rfl) rfl
        (by simp [payload, treeCode, restCode, encodeSupportWork_cons,
          hwork])
        (hbits payload (by simp))]
      rw [show
        13 +
            supplierSupportRankSelectorWorkFuel
              (left :: right :: rest) rank =
          (12 +
            supplierSupportRankSelectorWorkFuel
              (left :: right :: rest) rank) + 1 by omega]
      rw [run_unpairLeft_instruction (value := treeCode)
        (by rfl) rfl
        (by simp [payload])
        (hbits treeCode (by simp))]
      rw [show
        12 +
            supplierSupportRankSelectorWorkFuel
              (left :: right :: rest) rank =
          (11 +
            supplierSupportRankSelectorWorkFuel
              (left :: right :: rest) rank) + 1 by omega]
      rw [run_unpairRight_instruction (value := restCode)
        (by rfl) rfl
        (by simp [payload])
        (hbits restCode (by simp))]
      rw [show
        11 +
            supplierSupportRankSelectorWorkFuel
              (left :: right :: rest) rank =
          (10 +
            supplierSupportRankSelectorWorkFuel
              (left :: right :: rest) rank) + 1 by omega]
      rw [run_branchZero_instruction (by rfl) rfl]
      rw [show state4.registers 0 = treeCode by simp [state4, state3]]
      rw [if_neg htreeNonzero]
      rw [show
        10 +
            supplierSupportRankSelectorWorkFuel
              (left :: right :: rest) rank =
          (9 +
            supplierSupportRankSelectorWorkFuel
              (left :: right :: rest) rank) + 1 by omega]
      rw [run_unpairLeft_instruction (value := 2)
        (by rfl) rfl
        (by simp [treeCode])
        (hbits 2 (by simp))]
      rw [show
        9 +
            supplierSupportRankSelectorWorkFuel
              (left :: right :: rest) rank =
          (8 +
            supplierSupportRankSelectorWorkFuel
              (left :: right :: rest) rank) + 1 by omega]
      rw [run_decrement_instruction (value := 1)
        (by rfl) rfl
        (by simp)
        (hbits 1 (by simp))]
      rw [show
        8 +
            supplierSupportRankSelectorWorkFuel
              (left :: right :: rest) rank =
          (7 +
            supplierSupportRankSelectorWorkFuel
              (left :: right :: rest) rank) + 1 by omega]
      rw [run_branchZero_instruction (by rfl) rfl]
      rw [show state7.registers 7 = 1 by simp [state7]]
      rw [if_neg honeNonzero]
      rw [show
        7 +
            supplierSupportRankSelectorWorkFuel
              (left :: right :: rest) rank =
          (6 +
            supplierSupportRankSelectorWorkFuel
              (left :: right :: rest) rank) + 1 by omega]
      rw [run_unpairRight_instruction (value := branchPayload)
        (by rfl) rfl
        (by simp [treeCode, branchPayload])
        (hbits branchPayload (by simp))]
      rw [show
        6 +
            supplierSupportRankSelectorWorkFuel
              (left :: right :: rest) rank =
          (5 +
            supplierSupportRankSelectorWorkFuel
              (left :: right :: rest) rank) + 1 by omega]
      rw [run_unpairLeft_instruction (value := left.code)
        (by rfl) rfl
        (by simp [branchPayload])
        (hbits left.code (by simp))]
      rw [show
        5 +
            supplierSupportRankSelectorWorkFuel
              (left :: right :: rest) rank =
          (4 +
            supplierSupportRankSelectorWorkFuel
              (left :: right :: rest) rank) + 1 by omega]
      rw [run_unpairRight_instruction (value := right.code)
        (by rfl) rfl
        (by simp [branchPayload])
        (hbits right.code (by simp))]
      rw [show
        4 +
            supplierSupportRankSelectorWorkFuel
              (left :: right :: rest) rank =
          (3 +
            supplierSupportRankSelectorWorkFuel
              (left :: right :: rest) rank) + 1 by omega]
      rw [run_pair_instruction (value := rightPayload)
        (by rfl) rfl
        (by simp [rightPayload, restCode])
        (hbits rightPayload (by simp))]
      rw [show
        3 +
            supplierSupportRankSelectorWorkFuel
              (left :: right :: rest) rank =
          (2 +
            supplierSupportRankSelectorWorkFuel
              (left :: right :: rest) rank) + 1 by omega]
      rw [run_pair_instruction (value := rightStack)
        (by rfl) rfl
        (by simp [rightStack, rightPayload, hone])
        (hbits rightStack (by simp))]
      rw [show
        2 +
            supplierSupportRankSelectorWorkFuel
              (left :: right :: rest) rank =
          (1 +
            supplierSupportRankSelectorWorkFuel
              (left :: right :: rest) rank) + 1 by omega]
      rw [run_pair_instruction (value := leftPayload)
        (by rfl) rfl
        (by simp [leftPayload, rightStack])
        (hbits leftPayload (by simp))]
      rw [show
        1 +
            supplierSupportRankSelectorWorkFuel
              (left :: right :: rest) rank =
          supplierSupportRankSelectorWorkFuel
              (left :: right :: rest) rank + 1 by omega]
      rw [run_pair_instruction (value := nextStack)
        (by rfl) rfl
        (by simp [nextStack, leftPayload, hone])
        (hbits nextStack (by simp))]
      change
        runNPOracleProgram supplierSupportRankSelectorProgram maximumBits
            (supplierSupportRankSelectorWorkFuel
              (left :: right :: rest) rank) nextState =
          some
            (supplierSupportLookupRequest inputLength weightsCode
              selectedIndex)
      exact inductionHypothesis index nextState rfl
        (by
          simp [nextState, nextStack, leftPayload, rightStack,
            rightPayload, restCode, encodeSupportWork_cons])
        (by simp [nextState, state14, state13, state12, state11, state10,
          state9, state8, state7, state6, state5, state4, state3, state2,
          state1, hinputLength])
        (by simp [nextState, state14, state13, state12, state11, state10,
          state9, state8, state7, state6, state5, state4, state3, state2,
          state1, hindex])
        (by simp [nextState, state14, state13, state12, state11, state10,
          state9, state8, state7, state6, state5, state4, state3, state2,
          state1, hrank])
        (by simp [nextState, state14, state13, state12, state11, state10,
          state9, state8, state7, state6, state5, state4, state3, state2,
          state1, hweights])
        (by simp [nextState, state14, state13, state12, state11, state10,
          state9, state8, state7, state6, state5, state4, state3, state2,
          state1, hone])
        hselectedNext hfitsNext

set_option maxRecDepth 5000 in
private theorem run_supplierSupportRankSelectorProgram_of_fits
    (inputLength rank weightsCode count supportCode selectedIndex
      maximumBits : ℕ)
    (tree : BalancedTraversalTree)
    (hcode : tree.code = supportCode)
    (hselected :
      (supportWorkSelectedIndicesFrom 0 [tree])[rank]? =
        some selectedIndex)
    (hprefixFits :
      ∀ value,
        value ∈
            supplierSupportRankSelectorPrefixValues inputLength
              weightsCode count supportCode rank →
          natBitLength value ≤ maximumBits)
    (hworkFits :
      ∀ value,
        value ∈
            supplierSupportRankSelectorWorkValues [tree] 0 rank
              inputLength weightsCode →
          natBitLength value ≤ maximumBits) :
    runNPOracleProgram supplierSupportRankSelectorProgram maximumBits
        (10 + supplierSupportRankSelectorWorkFuel [tree] rank)
        (initialNPOracleState inputLength
          (supplierSupportRankSelectorInput rank weightsCode count
            supportCode)) =
      some
        (supplierSupportLookupRequest inputLength weightsCode
          selectedIndex) := by
  let input :=
    supplierSupportRankSelectorInput rank weightsCode count supportCode
  let countSupport := Nat.pair count supportCode
  let context := Nat.pair weightsCode countSupport
  let initial := initialNPOracleState inputLength input
  let state1 := (initial.write 4 rank).jump 1
  let state2 := (state1.write 6 context).jump 2
  let state3 := (state2.write 5 weightsCode).jump 3
  let state4 := (state3.write 7 countSupport).jump 4
  let state5 := (state4.write 6 supportCode).jump 5
  let state6 := (state5.write 3 0).jump 6
  let state7 := (state6.write 8 1).jump 7
  let state8 := (state7.write 2 0).jump 8
  let payload := Nat.pair supportCode 0
  let state9 := (state8.write 9 payload).jump 9
  let workCode := Nat.pair 1 payload
  let entry := (state9.write 0 workCode).jump 10
  have hbits (value : ℕ)
      (hvalue :
        value ∈
          [inputLength, rank, weightsCode, count, supportCode,
            countSupport, context, input, 0, 1, payload, workCode]) :
      natBitLength value ≤ maximumBits := by
    apply hprefixFits
    simp [supplierSupportRankSelectorPrefixValues, input, countSupport,
      context, payload, workCode] at hvalue ⊢
    aesop
  rw [show
    10 + supplierSupportRankSelectorWorkFuel [tree] rank =
      (9 + supplierSupportRankSelectorWorkFuel [tree] rank) + 1 by omega]
  rw [run_unpairLeft_instruction (value := rank)
    (by rfl) rfl
    (by simp [supplierSupportRankSelectorInput,
      initialNPOracleState])
    (hbits rank (by simp))]
  rw [show
    9 + supplierSupportRankSelectorWorkFuel [tree] rank =
      (8 + supplierSupportRankSelectorWorkFuel [tree] rank) + 1 by omega]
  rw [run_unpairRight_instruction (value := context)
    (by rfl) rfl
    (by simp [context, countSupport,
      supplierSupportRankSelectorInput, initialNPOracleState])
    (hbits context (by simp))]
  rw [show
    8 + supplierSupportRankSelectorWorkFuel [tree] rank =
      (7 + supplierSupportRankSelectorWorkFuel [tree] rank) + 1 by omega]
  rw [run_unpairLeft_instruction (value := weightsCode)
    (by rfl) rfl
    (by simp [context])
    (hbits weightsCode (by simp))]
  rw [show
    7 + supplierSupportRankSelectorWorkFuel [tree] rank =
      (6 + supplierSupportRankSelectorWorkFuel [tree] rank) + 1 by omega]
  rw [run_unpairRight_instruction (value := countSupport)
    (by rfl) rfl
    (by simp [context, countSupport])
    (hbits countSupport (by simp))]
  rw [show
    6 + supplierSupportRankSelectorWorkFuel [tree] rank =
      (5 + supplierSupportRankSelectorWorkFuel [tree] rank) + 1 by omega]
  rw [run_unpairRight_instruction (value := supportCode)
    (by rfl) rfl
    (by simp [countSupport])
    (hbits supportCode (by simp))]
  rw [show
    5 + supplierSupportRankSelectorWorkFuel [tree] rank =
      (4 + supplierSupportRankSelectorWorkFuel [tree] rank) + 1 by omega]
  rw [run_set_instruction (value := 0)
    (by rfl) rfl (hbits 0 (by simp))]
  rw [show
    4 + supplierSupportRankSelectorWorkFuel [tree] rank =
      (3 + supplierSupportRankSelectorWorkFuel [tree] rank) + 1 by omega]
  rw [run_set_instruction (value := 1)
    (by rfl) rfl (hbits 1 (by simp))]
  rw [show
    3 + supplierSupportRankSelectorWorkFuel [tree] rank =
      (2 + supplierSupportRankSelectorWorkFuel [tree] rank) + 1 by omega]
  rw [run_set_instruction (value := 0)
    (by rfl) rfl (hbits 0 (by simp))]
  rw [show
    2 + supplierSupportRankSelectorWorkFuel [tree] rank =
      (1 + supplierSupportRankSelectorWorkFuel [tree] rank) + 1 by omega]
  rw [run_pair_instruction (value := payload)
    (by rfl) rfl
    (by simp [payload])
    (hbits payload (by simp))]
  rw [show
    1 + supplierSupportRankSelectorWorkFuel [tree] rank =
      supplierSupportRankSelectorWorkFuel [tree] rank + 1 by omega]
  rw [run_pair_instruction (value := workCode)
    (by rfl) rfl
    (by simp [workCode, payload])
    (hbits workCode (by simp))]
  change
    runNPOracleProgram supplierSupportRankSelectorProgram maximumBits
        (supplierSupportRankSelectorWorkFuel [tree] rank) entry =
      some
        (supplierSupportLookupRequest inputLength weightsCode
          selectedIndex)
  exact run_supplierSupportRankSelectorWork [tree] 0 rank inputLength
    weightsCode selectedIndex maximumBits entry rfl
    (by simp [entry, workCode, payload, encodeSupportWork_cons, hcode])
    (by simp [entry, state9, state8, state7, state6, state5, state4,
      state3, state2, state1, initial, input, initialNPOracleState])
    (by simp [entry, state9, state8, state7, state6])
    (by simp [entry, state9, state8, state7, state6, state5, state4,
      state3, state2, state1])
    (by simp [entry, state9, state8, state7, state6, state5, state4,
      state3])
    (by simp [entry, state9, state8, state7])
    hselected hworkFits

private theorem run_supplierSupportRankSelectorProgram
    (weights : List ℕ) (support : List Bool) (rank : ℕ)
    (hrank : rank < (nonzeroSupportIndices support).length) :
    runNPOracleProgram supplierSupportRankSelectorProgram
        (supplierSupportRankSelectorBits weights support rank)
        (supplierSupportRankSelectorFuel support rank)
        (initialNPOracleState weights.length
          (supplierSupportRankSelectorInput rank
            (encodeBalancedList weights)
            (nonzeroSupportCount support)
            (encodeBoolList support))) =
      some
        (nativeInputRequest weights.length
          (balancedLookupInput weights
            (nonzeroSupportIndices support)[rank])) := by
  let inputLength := weights.length
  let weightsCode := encodeBalancedList weights
  let count := nonzeroSupportCount support
  let supportCode := encodeBoolList support
  let tree := balancedTraversalTree (support.map boolCode)
  let selectedIndex := (nonzeroSupportIndices support)[rank]
  let maximumBits :=
    supplierSupportRankSelectorBits weights support rank
  have hcode : tree.code = supportCode := by
    simp [tree, supportCode, balancedTraversalTree_code, encodeBoolList]
  have hindices :
      supportWorkSelectedIndicesFrom 0 [tree] =
        nonzeroSupportIndices support := by
    simp [supportWorkSelectedIndicesFrom, supportWorkAtoms, tree,
      nonzeroSupportIndices, balancedTraversalTree_atoms]
  have hselected :
      (supportWorkSelectedIndicesFrom 0 [tree])[rank]? =
        some selectedIndex := by
    rw [hindices]
    exact List.getElem?_eq_getElem hrank
  have hprefixFits :
      ∀ value,
        value ∈
            supplierSupportRankSelectorPrefixValues inputLength
              weightsCode count supportCode rank →
          natBitLength value ≤ maximumBits := by
    intro value hvalue
    apply supplierSupportRankSelectorBits_of_mem
    simp [supplierSupportRankSelectorExecutionValues, inputLength,
      weightsCode, count, supportCode, hvalue]
  have hworkFits :
      ∀ value,
        value ∈
            supplierSupportRankSelectorWorkValues [tree] 0 rank
              inputLength weightsCode →
          natBitLength value ≤ maximumBits := by
    intro value hvalue
    apply supplierSupportRankSelectorBits_of_mem
    simp [supplierSupportRankSelectorExecutionValues, inputLength,
      weightsCode, tree, hvalue]
  have hrun :=
    run_supplierSupportRankSelectorProgram_of_fits
      inputLength rank weightsCode count supportCode selectedIndex
      maximumBits tree hcode hselected hprefixFits hworkFits
  simpa only [supplierSupportRankSelectorFuel, inputLength, weightsCode,
    count, supportCode, tree, selectedIndex, maximumBits,
    supplierSupportLookupRequest, balancedLookupInput] using hrun

private theorem nonzeroAtomIndicesFrom_add
    (offset first : ℕ) (atoms : List ℕ) :
    nonzeroAtomIndicesFrom (offset + first) atoms =
      (nonzeroAtomIndicesFrom first atoms).map (offset + ·) := by
  induction atoms generalizing first with
  | nil => rfl
  | cons atom rest inductionHypothesis =>
      by_cases hatom : atom = 0
      · simp [nonzeroAtomIndicesFrom, hatom,
          inductionHypothesis, Nat.add_assoc]
      · simp [nonzeroAtomIndicesFrom, hatom,
          inductionHypothesis, Nat.add_assoc]

private theorem nonzeroSupportIndices_map_getD
    (weights : List ℕ) (support : List Bool)
    (hlength : weights.length = support.length) :
    (nonzeroSupportIndices support).map
        (fun index => weights.getD index 0) =
      supportedWeights weights support := by
  induction weights generalizing support with
  | nil =>
      cases support with
      | nil => rfl
      | cons bit rest => simp at hlength
  | cons weight weights inductionHypothesis =>
      cases support with
      | nil => simp at hlength
      | cons bit support =>
          have htail : weights.length = support.length := by
            simpa using hlength
          cases bit
          · change
              (nonzeroAtomIndicesFrom 1
                  (support.map boolCode)).map
                    (fun index => (weight :: weights).getD index 0) =
                supportedWeights weights support
            rw [nonzeroAtomIndicesFrom_add 1 0]
            simp only [List.map_map, Nat.add_comm]
            exact inductionHypothesis support htail
          · change
              (0 ::
                nonzeroAtomIndicesFrom 1
                  (support.map boolCode)).map
                    (fun index => (weight :: weights).getD index 0) =
                weight :: supportedWeights weights support
            rw [nonzeroAtomIndicesFrom_add 1 0]
            simp only [List.map_cons, List.getD_cons_zero,
              List.map_map, Nat.add_comm, List.cons.injEq, true_and]
            exact inductionHypothesis support htail

private theorem range_map_getD (values : List ℕ) :
    (List.range values.length).map (fun index => values.getD index 0) =
      values := by
  induction values with
  | nil => rfl
  | cons value values inductionHypothesis =>
      simp only [List.length_cons]
      rw [List.range_succ_eq_map]
      simp only [List.map_cons, List.getD_cons_zero, List.map_map,
        List.cons.injEq, true_and]
      exact inductionHypothesis

/-! ## Fixed support-compression pipeline -/

private theorem composition_le_foldr_max_of_mem
    {value : ℕ} {values : List ℕ} (hmem : value ∈ values) :
    value ≤ values.foldr max 0 := by
  induction values with
  | nil => simp at hmem
  | cons head rest inductionHypothesis =>
      simp only [List.mem_cons] at hmem
      simp only [List.foldr]
      rcases hmem with rfl | hmem
      · exact Nat.le_max_left _ _
      · exact (inductionHypothesis hmem).trans (Nat.le_max_right _ _)

def supplierSupportRangeContext
    (weights : List ℕ) (support : List Bool) : ℕ :=
  Nat.pair (encodeBalancedList weights)
    (Nat.pair (nonzeroSupportCount support) (encodeBoolList support))

def supplierSupportSelectorRequests
    (weights : List ℕ) (support : List Bool) : List ℕ :=
  balancedRangeRequestAtoms weights.length
    (supplierSupportRangeContext weights support) 0
    (nonzeroSupportCount support)

def supplierSupportSelectorRequestRank (request : ℕ) : ℕ :=
  (Nat.unpair (Nat.unpair request).2).1

private def supplierSupportIndexAt (support : List Bool) (rank : ℕ) : ℕ :=
  (nonzeroSupportIndices support).getD rank 0

private def supplierSupportSelectorCallOutput
    (weights : List ℕ) (support : List Bool) (request : ℕ) : ℕ :=
  supplierSupportLookupRequest weights.length (encodeBalancedList weights)
    (supplierSupportIndexAt support
      (supplierSupportSelectorRequestRank request))

def supplierSupportSelectorCallFuel
    (support : List Bool) (request : ℕ) : ℕ :=
  supplierSupportRankSelectorFuel support
    (supplierSupportSelectorRequestRank request)

def supplierSupportLookupRequests
    (weights : List ℕ) (support : List Bool) : List ℕ :=
  (nonzeroSupportIndices support).map fun index =>
    supplierSupportLookupRequest weights.length
      (encodeBalancedList weights) index

private def supplierSupportSelectorCallMaximumBits
    (weights : List ℕ) (support : List Bool) : ℕ :=
  max
    (balancedCallRequiredBits
      (supplierSupportSelectorCallOutput weights support)
      (supplierSupportSelectorRequests weights support))
    (((List.range (nonzeroSupportCount support)).map fun rank =>
      supplierSupportRankSelectorBits weights support rank).foldr max 0)

def supplierSupportSelectorCallFuelBound
    (weights : List ℕ) (support : List Bool) : ℕ :=
  balancedCallFuel supplierSupportRankSelectorProgram
    (supplierSupportSelectorCallFuel support)
    (supplierSupportSelectorRequests weights support)

@[simp] private theorem supplierSupportSelectorRequestRank_atom
    (inputLength rank context : ℕ) :
    supplierSupportSelectorRequestRank
        (balancedRangeRequestAtom inputLength rank context) =
      rank := by
  unfold supplierSupportSelectorRequestRank balancedRangeRequestAtom
  simp only [Nat.unpair_pair]

@[simp] private theorem supplierSupportSelectorCallOutput_atom
    (weights : List ℕ) (support : List Bool) (rank context : ℕ) :
    supplierSupportSelectorCallOutput weights support
        (balancedRangeRequestAtom weights.length rank context) =
      supplierSupportLookupRequest weights.length
        (encodeBalancedList weights)
        (supplierSupportIndexAt support rank) := by
  unfold supplierSupportSelectorCallOutput
  rw [supplierSupportSelectorRequestRank_atom]

@[simp] private theorem supplierSupportSelectorCallFuel_atom
    (support : List Bool) (inputLength rank context : ℕ) :
    supplierSupportSelectorCallFuel support
        (balancedRangeRequestAtom inputLength rank context) =
      supplierSupportRankSelectorFuel support rank := by
  unfold supplierSupportSelectorCallFuel
  rw [supplierSupportSelectorRequestRank_atom]

private theorem supplierSupportSelectorOutputs_eq_lookupRequests
    (weights : List ℕ) (support : List Bool) :
    (supplierSupportSelectorRequests weights support).map
        (supplierSupportSelectorCallOutput weights support) =
      supplierSupportLookupRequests weights support := by
  rw [supplierSupportSelectorRequests,
    balancedRangeRequestAtoms_eq_map_range]
  simp only [zero_add, List.map_map, Function.comp_def]
  have hatoms :
      (fun rank =>
        supplierSupportSelectorCallOutput weights support
          (balancedRangeRequestAtom weights.length rank
            (supplierSupportRangeContext weights support))) =
        (fun rank =>
          supplierSupportLookupRequest weights.length
            (encodeBalancedList weights)
            (supplierSupportIndexAt support rank)) := by
    funext rank
    exact supplierSupportSelectorCallOutput_atom weights support rank _
  rw [hatoms]
  unfold supplierSupportLookupRequests supplierSupportIndexAt
  rw [← nonzeroSupportIndices_length support]
  simpa only [List.map_map, Function.comp_def] using
    congrArg
      (List.map fun index =>
        supplierSupportLookupRequest weights.length
          (encodeBalancedList weights) index)
      (range_map_getD (nonzeroSupportIndices support))

private theorem supplierSupportRankSelectorBits_le_callMaximum
    (weights : List ℕ) (support : List Bool) (rank : ℕ)
    (hrank : rank < nonzeroSupportCount support) :
    supplierSupportRankSelectorBits weights support rank ≤
      supplierSupportSelectorCallMaximumBits weights support := by
  apply
    (composition_le_foldr_max_of_mem
      (values :=
        (List.range (nonzeroSupportCount support)).map fun candidate =>
          supplierSupportRankSelectorBits weights support candidate) ?_).trans
  · exact Nat.le_max_right _ _
  · exact List.mem_map.mpr
      ⟨rank, List.mem_range.mpr hrank, rfl⟩

private theorem run_supplierSupportSelectorCallAtom
    (weights : List ℕ) (support : List Bool) (rank : ℕ)
    (hrank : rank < (nonzeroSupportIndices support).length) :
    runNPOracleProgram supplierSupportRankSelectorProgram
        (supplierSupportSelectorCallMaximumBits weights support)
        (supplierSupportSelectorCallFuel support
          (balancedRangeRequestAtom weights.length rank
            (supplierSupportRangeContext weights support)))
        (initialNPOracleState
          (Nat.unpair
            (balancedRangeRequestAtom weights.length rank
              (supplierSupportRangeContext weights support))).1
          (Nat.unpair
            (balancedRangeRequestAtom weights.length rank
              (supplierSupportRangeContext weights support))).2) =
      some
        (supplierSupportSelectorCallOutput weights support
          (balancedRangeRequestAtom weights.length rank
            (supplierSupportRangeContext weights support))) := by
  have hrankCount : rank < nonzeroSupportCount support := by
    rw [← nonzeroSupportIndices_length support]
    exact hrank
  have hrun :=
    run_supplierSupportRankSelectorProgram weights support rank hrank
  have hlifted :=
    run_bits_mono hrun
      (supplierSupportRankSelectorBits_le_callMaximum
        weights support rank hrankCount)
  rw [supplierSupportSelectorCallFuel_atom,
    supplierSupportSelectorCallOutput_atom]
  unfold supplierSupportIndexAt
  rw [List.getD_eq_getElem _ _ hrank]
  simpa only [balancedRangeRequestAtom, supplierSupportRangeContext,
    supplierSupportRankSelectorInput, supplierSupportLookupRequest,
    balancedLookupInput, Nat.unpair_pair] using hlifted

private theorem run_supplierSupportSelectorCallProgram
    (weights : List ℕ) (support : List Bool) :
    runNPOracleProgram
        (balancedCallProgram supplierSupportRankSelectorProgram)
        (supplierSupportSelectorCallMaximumBits weights support)
        (supplierSupportSelectorCallFuelBound weights support)
        (initialNPOracleState weights.length
          (encodeBalancedList
            (supplierSupportSelectorRequests weights support))) =
      some
        (encodeBalancedList
          (supplierSupportLookupRequests weights support)) := by
  rw [← supplierSupportSelectorOutputs_eq_lookupRequests]
  apply run_balancedCallProgram_from weights.length
    (supplierSupportSelectorRequests weights support)
    (supplierSupportSelectorCallFuel support)
    (supplierSupportSelectorCallOutput weights support)
  · exact Nat.le_max_left _ _
  · intro request hrequest
    rw [supplierSupportSelectorRequests,
      balancedRangeRequestAtoms_eq_map_range] at hrequest
    simp only [zero_add] at hrequest
    rcases List.mem_map.mp hrequest with ⟨rank, hrank, rfl⟩
    have hrankCount : rank < nonzeroSupportCount support :=
      List.mem_range.mp hrank
    have hrankIndices :
        rank < (nonzeroSupportIndices support).length := by
      rw [nonzeroSupportIndices_length]
      exact hrankCount
    exact
      run_supplierSupportSelectorCallAtom weights support rank hrankIndices

def supplierSupportLookupRequestIndex (request : ℕ) : ℕ :=
  (Nat.unpair (Nat.unpair (Nat.unpair request).2).2).1

private def supplierSupportLookupCallOutput
    (weights : List ℕ) (request : ℕ) : ℕ :=
  weights.getD (supplierSupportLookupRequestIndex request) 0

def supplierSupportLookupCallFuel
    (weights : List ℕ) (request : ℕ) : ℕ :=
  balancedLookupFuel weights (supplierSupportLookupRequestIndex request)

private def supplierSupportLookupCallMaximumBits
    (weights : List ℕ) (support : List Bool) : ℕ :=
  max
    (balancedCallRequiredBits
      (supplierSupportLookupCallOutput weights)
      (supplierSupportLookupRequests weights support))
    (((nonzeroSupportIndices support).map fun index =>
      balancedLookupMaximumBits weights index).foldr max 0)

def supplierSupportLookupCallFuelBound
    (weights : List ℕ) (support : List Bool) : ℕ :=
  balancedCallFuel canonicalBalancedLookupProgram
    (supplierSupportLookupCallFuel weights)
    (supplierSupportLookupRequests weights support)

@[simp] private theorem supplierSupportLookupRequestIndex_request
    (inputLength weightsCode index : ℕ) :
    supplierSupportLookupRequestIndex
        (supplierSupportLookupRequest inputLength weightsCode index) =
      index := by
  simp only [supplierSupportLookupRequestIndex,
    supplierSupportLookupRequest, nativeInputRequest, Nat.unpair_pair]

@[simp] private theorem supplierSupportLookupCallOutput_request
    (weights : List ℕ) (inputLength weightsCode index : ℕ) :
    supplierSupportLookupCallOutput weights
        (supplierSupportLookupRequest inputLength weightsCode index) =
      weights.getD index 0 := by
  unfold supplierSupportLookupCallOutput
  rw [supplierSupportLookupRequestIndex_request]

@[simp] private theorem supplierSupportLookupCallFuel_request
    (weights : List ℕ) (inputLength weightsCode index : ℕ) :
    supplierSupportLookupCallFuel weights
        (supplierSupportLookupRequest inputLength weightsCode index) =
      balancedLookupFuel weights index := by
  unfold supplierSupportLookupCallFuel
  rw [supplierSupportLookupRequestIndex_request]

private theorem supplierSupportLookupOutputs_eq_supportedWeights
    (weights : List ℕ) (support : List Bool)
    (hlength : weights.length = support.length) :
    (supplierSupportLookupRequests weights support).map
        (supplierSupportLookupCallOutput weights) =
      supportedWeights weights support := by
  unfold supplierSupportLookupRequests
  rw [List.map_map]
  have hatoms :
      (supplierSupportLookupCallOutput weights ∘
        fun index =>
          supplierSupportLookupRequest weights.length
            (encodeBalancedList weights) index) =
        fun index => weights.getD index 0 := by
    funext index
    exact supplierSupportLookupCallOutput_request weights _ _ index
  rw [hatoms]
  exact nonzeroSupportIndices_map_getD weights support hlength

private theorem supplierSupportLookupBits_le_callMaximum
    (weights : List ℕ) (support : List Bool) (index : ℕ)
    (hindex : index ∈ nonzeroSupportIndices support) :
    balancedLookupMaximumBits weights index ≤
      supplierSupportLookupCallMaximumBits weights support := by
  apply
    (composition_le_foldr_max_of_mem
      (values :=
        (nonzeroSupportIndices support).map fun candidate =>
          balancedLookupMaximumBits weights candidate) ?_).trans
  · exact Nat.le_max_right _ _
  · exact List.mem_map.mpr ⟨index, hindex, rfl⟩

private theorem supplierSupportIndex_mem_lt
    (support : List Bool) (index : ℕ)
    (hindex : index ∈ nonzeroSupportIndices support) :
    index < support.length := by
  have hindex' :
      index ∈ nonzeroAtomIndicesFrom 0 (support.map boolCode) := by
    simpa only [nonzeroSupportIndices] using hindex
  have hbound :=
    nonzeroAtomIndicesFrom_mem_lt
      (first := 0) (atoms := support.map boolCode) hindex'
  simpa only [zero_add, List.length_map] using hbound

private theorem run_supplierSupportLookupCallAtom
    (weights : List ℕ) (support : List Bool) (index : ℕ)
    (hlength : weights.length = support.length)
    (hindex : index ∈ nonzeroSupportIndices support) :
    runNPOracleProgram canonicalBalancedLookupProgram
        (supplierSupportLookupCallMaximumBits weights support)
        (supplierSupportLookupCallFuel weights
          (supplierSupportLookupRequest weights.length
            (encodeBalancedList weights) index))
        (initialNPOracleState
          (Nat.unpair
            (supplierSupportLookupRequest weights.length
              (encodeBalancedList weights) index)).1
          (Nat.unpair
            (supplierSupportLookupRequest weights.length
              (encodeBalancedList weights) index)).2) =
      some
        (supplierSupportLookupCallOutput weights
          (supplierSupportLookupRequest weights.length
            (encodeBalancedList weights) index)) := by
  have hindexWeights : index < weights.length := by
    rw [hlength]
    exact supplierSupportIndex_mem_lt support index hindex
  have hrun :=
    run_canonicalBalancedLookupProgram weights index weights.length
      hindexWeights
  have hlifted :=
    run_bits_mono hrun
      (supplierSupportLookupBits_le_callMaximum
        weights support index hindex)
  rw [supplierSupportLookupCallFuel_request,
    supplierSupportLookupCallOutput_request]
  rw [List.getD_eq_getElem _ _ hindexWeights]
  simpa only [supplierSupportLookupRequest, nativeInputRequest,
    balancedLookupInput, Nat.unpair_pair] using hlifted

private theorem run_supplierSupportLookupCallProgram
    (weights : List ℕ) (support : List Bool)
    (hlength : weights.length = support.length) :
    runNPOracleProgram
        (balancedCallProgram canonicalBalancedLookupProgram)
        (supplierSupportLookupCallMaximumBits weights support)
        (supplierSupportLookupCallFuelBound weights support)
        (initialNPOracleState weights.length
          (encodeBalancedList
            (supplierSupportLookupRequests weights support))) =
      some (encodeBalancedList (supportedWeights weights support)) := by
  rw [← supplierSupportLookupOutputs_eq_supportedWeights
    weights support hlength]
  apply run_balancedCallProgram_from weights.length
    (supplierSupportLookupRequests weights support)
    (supplierSupportLookupCallFuel weights)
    (supplierSupportLookupCallOutput weights)
  · exact Nat.le_max_left _ _
  · intro request hrequest
    unfold supplierSupportLookupRequests at hrequest
    rcases List.mem_map.mp hrequest with ⟨index, hindex, rfl⟩
    exact
      run_supplierSupportLookupCallAtom
        weights support index hlength hindex

def supplierSupportSelectorPreserveFuel
    (weights : List ℕ) (support : List Bool) : ℕ :=
  preserveRightFuel
    (supplierSupportSelectorCallFuelBound weights support)

private def supplierSupportSelectorPreserveBits
    (weights : List ℕ) (support : List Bool) : ℕ :=
  preserveRightBits
    (supplierSupportSelectorCallMaximumBits weights support)
    (encodeBalancedList (supplierSupportSelectorRequests weights support))
    (supplierSupportRangeContext weights support)
    (encodeBalancedList (supplierSupportLookupRequests weights support))

private theorem run_supplierSupportSelectorPreserveProgram
    (weights : List ℕ) (support : List Bool) :
    runNPOracleProgram
        (preserveRightProgram
          (balancedCallProgram supplierSupportRankSelectorProgram))
        (supplierSupportSelectorPreserveBits weights support)
        (supplierSupportSelectorPreserveFuel weights support)
        (initialNPOracleState weights.length
          (Nat.pair
            (encodeBalancedList
              (supplierSupportSelectorRequests weights support))
            (supplierSupportRangeContext weights support))) =
      some
        (Nat.pair
          (encodeBalancedList
            (supplierSupportLookupRequests weights support))
          (supplierSupportRangeContext weights support)) := by
  exact
    run_preserveRightProgram
      (balancedCallProgram supplierSupportRankSelectorProgram)
      weights.length
      (supplierSupportSelectorCallMaximumBits weights support)
      (supplierSupportSelectorCallFuelBound weights support)
      (encodeBalancedList (supplierSupportSelectorRequests weights support))
      (supplierSupportRangeContext weights support)
      (encodeBalancedList (supplierSupportLookupRequests weights support))
      (run_supplierSupportSelectorCallProgram weights support)

def supplierSupportLookupPreserveFuel
    (weights : List ℕ) (support : List Bool) : ℕ :=
  preserveRightFuel
    (supplierSupportLookupCallFuelBound weights support)

private def supplierSupportLookupPreserveBits
    (weights : List ℕ) (support : List Bool) : ℕ :=
  preserveRightBits
    (supplierSupportLookupCallMaximumBits weights support)
    (encodeBalancedList (supplierSupportLookupRequests weights support))
    (supplierSupportRangeContext weights support)
    (encodeBalancedList (supportedWeights weights support))

private theorem run_supplierSupportLookupPreserveProgram
    (weights : List ℕ) (support : List Bool)
    (hlength : weights.length = support.length) :
    runNPOracleProgram
        (preserveRightProgram
          (balancedCallProgram canonicalBalancedLookupProgram))
        (supplierSupportLookupPreserveBits weights support)
        (supplierSupportLookupPreserveFuel weights support)
        (initialNPOracleState weights.length
          (Nat.pair
            (encodeBalancedList
              (supplierSupportLookupRequests weights support))
            (supplierSupportRangeContext weights support))) =
      some
        (Nat.pair
          (encodeBalancedList (supportedWeights weights support))
          (supplierSupportRangeContext weights support)) := by
  exact
    run_preserveRightProgram
      (balancedCallProgram canonicalBalancedLookupProgram)
      weights.length
      (supplierSupportLookupCallMaximumBits weights support)
      (supplierSupportLookupCallFuelBound weights support)
      (encodeBalancedList (supplierSupportLookupRequests weights support))
      (supplierSupportRangeContext weights support)
      (encodeBalancedList (supportedWeights weights support))
      (run_supplierSupportLookupCallProgram weights support hlength)

private def supplierSupportProjectionInput
    (selectedWeightsCode weightsCode count supportCode : ℕ) : ℕ :=
  Nat.pair selectedWeightsCode
    (Nat.pair weightsCode (Nat.pair count supportCode))

private def supplierSupportProjectionOutput
    (selectedWeightsCode count supportCode : ℕ) : ℕ :=
  Nat.pair selectedWeightsCode (Nat.pair count supportCode)

def supplierSupportProjectionProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairRight 3 4 3
  , .pair 2 4 0 4
  , .halt 0
  ]

@[simp] private theorem supplierSupportProjectionProgram_oracleFree :
    OracleFree supplierSupportProjectionProgram := by
  rfl

private def supplierSupportProjectionBits
    (selectedWeightsCode weightsCode count supportCode : ℕ) : ℕ :=
  max
    (natBitLength
      (supplierSupportProjectionInput selectedWeightsCode weightsCode
        count supportCode))
    (natBitLength
      (supplierSupportProjectionOutput selectedWeightsCode count
        supportCode))

private theorem run_supplierSupportProjectionProgram
    (inputLength selectedWeightsCode weightsCode count supportCode : ℕ) :
    runNPOracleProgram supplierSupportProjectionProgram
        (supplierSupportProjectionBits selectedWeightsCode weightsCode
          count supportCode)
        5
        (initialNPOracleState inputLength
          (supplierSupportProjectionInput selectedWeightsCode weightsCode
            count supportCode)) =
      some
        (supplierSupportProjectionOutput selectedWeightsCode count
          supportCode) := by
  let countSupport := Nat.pair count supportCode
  let context := Nat.pair weightsCode countSupport
  let input :=
    supplierSupportProjectionInput selectedWeightsCode weightsCode count
      supportCode
  let output :=
    supplierSupportProjectionOutput selectedWeightsCode count supportCode
  let maximumBits :=
    supplierSupportProjectionBits selectedWeightsCode weightsCode count
      supportCode
  have hinputBits : natBitLength input ≤ maximumBits :=
    Nat.le_max_left _ _
  have houtputBits : natBitLength output ≤ maximumBits :=
    Nat.le_max_right _ _
  have hselectedBits :
      natBitLength selectedWeightsCode ≤ maximumBits := by
    exact
      (natBitLength_mono
        (Nat.left_le_pair selectedWeightsCode context)).trans hinputBits
  have hcontextBits : natBitLength context ≤ maximumBits := by
    exact
      (natBitLength_mono
        (Nat.right_le_pair selectedWeightsCode context)).trans hinputBits
  have hcountSupportBits :
      natBitLength countSupport ≤ maximumBits := by
    exact
      (natBitLength_mono
        (Nat.right_le_pair weightsCode countSupport)).trans hcontextBits
  rw [show (5 : ℕ) = 4 + 1 by omega]
  rw [run_unpairLeft_instruction
    (program := supplierSupportProjectionProgram)
    (maximumBits := maximumBits) (fuel := 4)
    (pc := 0) (source := 0) (destination := 2) (next := 1)
    (value := selectedWeightsCode)
    (by rfl) rfl
    (by simp [supplierSupportProjectionInput, initialNPOracleState])
    hselectedBits]
  rw [show (4 : ℕ) = 3 + 1 by omega]
  rw [run_unpairRight_instruction
    (program := supplierSupportProjectionProgram)
    (maximumBits := maximumBits) (fuel := 3)
    (pc := 1) (source := 0) (destination := 3) (next := 2)
    (value := context)
    (by rfl) rfl
    (by simp [supplierSupportProjectionInput,
      initialNPOracleState, context, countSupport])
    hcontextBits]
  rw [show (3 : ℕ) = 2 + 1 by omega]
  rw [run_unpairRight_instruction
    (program := supplierSupportProjectionProgram)
    (maximumBits := maximumBits) (fuel := 2)
    (pc := 2) (source := 3) (destination := 4) (next := 3)
    (value := countSupport)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, context])
    hcountSupportBits]
  rw [show (2 : ℕ) = 1 + 1 by omega]
  rw [run_pair_instruction
    (program := supplierSupportProjectionProgram)
    (maximumBits := maximumBits) (fuel := 1)
    (pc := 3) (left := 2) (right := 4) (destination := 0)
    (next := 4) (value := output)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, output,
      supplierSupportProjectionOutput, countSupport])
    houtputBits]
  apply run_halt_instruction
    (program := supplierSupportProjectionProgram)
    (maximumBits := maximumBits) (fuel := 0)
    (pc := 4) (outputRegister := 0) (value := output)
  · rfl
  · rfl
  · simp [NPOracleState.write, NPOracleState.jump]
  · exact houtputBits

def supplierSupportCompressionProgram : NPOracleProgram :=
  linkPrograms
    (linkPrograms
      (linkPrograms
        (linkPrograms
          supplierSupportCountPrepareProgram
          generatedBalancedRangeProgram)
        (preserveRightProgram
          (balancedCallProgram supplierSupportRankSelectorProgram)))
      (preserveRightProgram
        (balancedCallProgram canonicalBalancedLookupProgram)))
    supplierSupportProjectionProgram

@[simp] theorem supplierSupportCompressionProgram_oracleFree :
    OracleFree supplierSupportCompressionProgram := by
  exact
    oracleFree_linkPrograms
      (oracleFree_linkPrograms
        (oracleFree_linkPrograms
          (oracleFree_linkPrograms
            supplierSupportCountPrepareProgram_oracleFree
            generatedBalancedRangeProgram_oracleFree)
          (preserveRightProgram_oracleFree _
            (balancedCallProgram_oracleFree
              supplierSupportRankSelectorProgram_oracleFree)))
        (preserveRightProgram_oracleFree _
          (balancedCallProgram_oracleFree
            canonicalBalancedLookupProgram_oracleFree)))
      supplierSupportProjectionProgram_oracleFree

private def supplierSupportCompressionStageBits
    (inputLength : ℕ) (weights : List ℕ) (support : List Bool) :
    List ℕ :=
  let weightsCode := encodeBalancedList weights
  let supportCode := encodeBoolList support
  let count := nonzeroSupportCount support
  let context := supplierSupportRangeContext weights support
  [ natBitLength inputLength
  , supplierSupportCountPrepareBits inputLength weightsCode support
  , generatedBalancedRangeRequiredBits inputLength count context
  , supplierSupportSelectorPreserveBits weights support
  , supplierSupportLookupPreserveBits weights support
  , supplierSupportProjectionBits
      (encodeBalancedList (supportedWeights weights support))
      weightsCode count supportCode
  ]

def supplierSupportCompressionBits
    (inputLength : ℕ) (weights : List ℕ) (support : List Bool) : ℕ :=
  max 1
    ((supplierSupportCompressionStageBits inputLength weights support).foldr
      max 0)

private theorem supplierSupportCompressionBits_of_mem
    {inputLength value : ℕ} {weights : List ℕ} {support : List Bool}
    (hvalue :
      value ∈
        supplierSupportCompressionStageBits inputLength weights support) :
    value ≤ supplierSupportCompressionBits inputLength weights support := by
  exact
    (composition_le_foldr_max_of_mem hvalue).trans
      (Nat.le_max_right _ _)

def supplierSupportCompressionFuel
    (weights : List ℕ) (support : List Bool) : ℕ :=
  linkFuel supplierSupportProjectionProgram
    (linkFuel
      (preserveRightProgram
        (balancedCallProgram canonicalBalancedLookupProgram))
      (linkFuel
        (preserveRightProgram
          (balancedCallProgram supplierSupportRankSelectorProgram))
        (linkFuel generatedBalancedRangeProgram
          (supplierSupportCountPrepareFuel support)
          (generatedBalancedRangeFuel weights.length
            (nonzeroSupportCount support)
            (supplierSupportRangeContext weights support)))
        (supplierSupportSelectorPreserveFuel weights support))
      (supplierSupportLookupPreserveFuel weights support))
    5

def supplierSupportCompressionOutput
    (weights : List ℕ) (support : List Bool) : ℕ :=
  Nat.pair
    (encodeBalancedList (supportedWeights weights support))
    (Nat.pair (nonzeroSupportCount support) (encodeBoolList support))

theorem run_supplierSupportCompressionProgram
    (inputLength : ℕ) (weights : List ℕ) (support : List Bool)
    (hinputLength : inputLength = weights.length)
    (hlength : weights.length = support.length) :
    runNPOracleProgram supplierSupportCompressionProgram
        (supplierSupportCompressionBits inputLength weights support)
        (supplierSupportCompressionFuel weights support)
        (initialNPOracleState inputLength
          (Nat.pair (encodeBalancedList weights)
            (encodeBoolList support))) =
      some (supplierSupportCompressionOutput weights support) := by
  subst inputLength
  let weightsCode := encodeBalancedList weights
  let supportCode := encodeBoolList support
  let count := nonzeroSupportCount support
  let countSupport := Nat.pair count supportCode
  let context := supplierSupportRangeContext weights support
  let selectorRequests := supplierSupportSelectorRequests weights support
  let lookupRequests := supplierSupportLookupRequests weights support
  let selectedWeightsCode :=
    encodeBalancedList (supportedWeights weights support)
  let countOutput := Nat.pair count context
  let rangeOutput := Nat.pair (encodeBalancedList selectorRequests) context
  let selectorOutput :=
    Nat.pair (encodeBalancedList lookupRequests) context
  let lookupOutput := Nat.pair selectedWeightsCode context
  let maximumBits :=
    supplierSupportCompressionBits weights.length weights support
  have hpositive : 1 ≤ maximumBits := by
    exact Nat.le_max_left _ _
  have hinputLengthBits :
      natBitLength weights.length ≤ maximumBits := by
    apply supplierSupportCompressionBits_of_mem
    simp [supplierSupportCompressionStageBits]
  have hcountBits :
      supplierSupportCountPrepareBits weights.length weightsCode support ≤
        maximumBits := by
    apply supplierSupportCompressionBits_of_mem
    simp [supplierSupportCompressionStageBits, weightsCode]
  have hrangeBits :
      generatedBalancedRangeRequiredBits weights.length count context ≤
        maximumBits := by
    apply supplierSupportCompressionBits_of_mem
    simp [supplierSupportCompressionStageBits, count, context]
  have hselectorBits :
      supplierSupportSelectorPreserveBits weights support ≤
        maximumBits := by
    apply supplierSupportCompressionBits_of_mem
    simp [supplierSupportCompressionStageBits]
  have hlookupBits :
      supplierSupportLookupPreserveBits weights support ≤
        maximumBits := by
    apply supplierSupportCompressionBits_of_mem
    simp [supplierSupportCompressionStageBits]
  have hprojectionBits :
      supplierSupportProjectionBits selectedWeightsCode weightsCode count
          supportCode ≤
        maximumBits := by
    apply supplierSupportCompressionBits_of_mem
    simp [supplierSupportCompressionStageBits, selectedWeightsCode,
      weightsCode, count, supportCode]
  have hcount :
      runNPOracleProgram supplierSupportCountPrepareProgram maximumBits
          (supplierSupportCountPrepareFuel support)
          (initialNPOracleState weights.length
            (Nat.pair weightsCode supportCode)) =
        some countOutput := by
    have hrun :=
      run_bits_mono
        (run_supplierSupportCountPrepareProgram
          weights.length weightsCode support)
        hcountBits
    simpa only [supplierSupportCountPrepareOutput, countOutput, context,
      supplierSupportRangeContext, weightsCode, supportCode, count]
      using hrun
  have hrange :
      runNPOracleProgram generatedBalancedRangeProgram maximumBits
          (generatedBalancedRangeFuel weights.length count context)
          (initialNPOracleState weights.length countOutput) =
        some rangeOutput := by
    have hrun :=
      run_bits_mono
        (run_generatedBalancedRangeProgram weights.length count context)
        hrangeBits
    simpa only [generatedBalancedRangeInput, generatedBalancedRangeOutput,
      rangeOutput, selectorRequests, supplierSupportSelectorRequests,
      countOutput] using hrun
  have hselector :
      runNPOracleProgram
          (preserveRightProgram
            (balancedCallProgram supplierSupportRankSelectorProgram))
          maximumBits
          (supplierSupportSelectorPreserveFuel weights support)
          (initialNPOracleState weights.length rangeOutput) =
        some selectorOutput := by
    have hrun :=
      run_bits_mono
        (run_supplierSupportSelectorPreserveProgram weights support)
        hselectorBits
    simpa only [rangeOutput, selectorOutput, selectorRequests,
      lookupRequests] using hrun
  have hlookup :
      runNPOracleProgram
          (preserveRightProgram
            (balancedCallProgram canonicalBalancedLookupProgram))
          maximumBits
          (supplierSupportLookupPreserveFuel weights support)
          (initialNPOracleState weights.length selectorOutput) =
        some lookupOutput := by
    have hrun :=
      run_bits_mono
        (run_supplierSupportLookupPreserveProgram weights support hlength)
        hlookupBits
    simpa only [selectorOutput, lookupOutput, lookupRequests,
      selectedWeightsCode] using hrun
  have hprojection :
      runNPOracleProgram supplierSupportProjectionProgram maximumBits 5
          (initialNPOracleState weights.length lookupOutput) =
        some (supplierSupportCompressionOutput weights support) := by
    have hrun :=
      run_bits_mono
        (run_supplierSupportProjectionProgram weights.length
          selectedWeightsCode weightsCode count supportCode)
        hprojectionBits
    simpa only [lookupOutput, context, supplierSupportRangeContext,
      supplierSupportProjectionInput, supplierSupportProjectionOutput,
      supplierSupportCompressionOutput, selectedWeightsCode,
      weightsCode, supportCode, count] using hrun
  have hcountRange :=
    run_linkPrograms hpositive hinputLengthBits hcount hrange
  have hthroughSelector :=
    run_linkPrograms hpositive hinputLengthBits hcountRange hselector
  have hthroughLookup :=
    run_linkPrograms hpositive hinputLengthBits hthroughSelector hlookup
  have hthroughProjection :=
    run_linkPrograms hpositive hinputLengthBits hthroughLookup hprojection
  simpa only [supplierSupportCompressionProgram,
    supplierSupportCompressionFuel, weightsCode, supportCode, count, context]
    using hthroughProjection

end NearCubicWires.CanonicalSupplierSupportCompressionProgram
