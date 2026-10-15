import Proof.Circuits.CanonicalBalancedCall
import Proof.MachineModel.BalancedClauseStreamFlattenProgram
import Proof.Foundations.CanonicalBinaryProgram
import Proof.MachineModel.CircuitInputClauseProgram
import Proof.MachineModel.CircuitInputTautologyProgram
import Proof.MachineModel.PreserveRightProgram
import Proof.MachineModel.TaggedProgramChoice

/-!
# Canonical balanced batch calls for circuit-input clauses

The recovery controller emits canonical balanced call atoms.  This module
applies the one fixed `CircuitInputClauseProgram` to every atom through the
shared balanced traversal, preserving gate order and returning one balanced
raw-clause stream per gate.
-/

namespace NearCubicWires.CircuitInputClauseBalancedCall

open NearCubicWires
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.BalancedClauseStreamFlattenProgram
open NearCubicWires.CircuitInputClauseProgram
open NearCubicWires.CircuitInputCNF
open NearCubicWires.CircuitInputTautologyProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.StructuralClauseStreamProgram
open NearCubicWires.TaggedProgramChoice
open NearCubicWires.TseitinCNF
open NearCubicWires.VerifiedLinker

def circuitInputClauseCallAtom {n : ℕ}
    (index : ℕ) (node : BooleanNode n) : ℕ :=
  Nat.pair n (circuitInputClauseRequest index node)

/-- Total decoder used only to state the fixed callee output on arbitrary
machine atoms.  Canonical controller-produced atoms round-trip exactly. -/
def rawCircuitNodeOfCode (inputArity code : ℕ) :
    BooleanNode inputArity :=
  let tag := (Nat.unpair code).1
  let payload := (Nat.unpair code).2
  if tag = 0 then
    .const (decide (payload ≠ 0))
  else if tag = 1 then
    if hsource : payload < inputArity then
      .input ⟨payload, hsource⟩
    else
      .const false
  else if tag = 2 then
    .not (payload - inputArity)
  else if tag = 3 then
    .and ((Nat.unpair payload).1 - inputArity)
      ((Nat.unpair payload).2 - inputArity)
  else
    .or ((Nat.unpair payload).1 - inputArity)
      ((Nat.unpair payload).2 - inputArity)

@[simp] theorem rawCircuitNodeOfCode_encode {n : ℕ}
    (node : BooleanNode n) :
    rawCircuitNodeOfCode n (rawCircuitNodeCode node) = node := by
  cases node with
  | const value =>
      cases value <;>
        simp [rawCircuitNodeOfCode, rawCircuitNodeCode]
  | input source =>
      simp [rawCircuitNodeOfCode, rawCircuitNodeCode, source.isLt]
  | not child =>
      simp [rawCircuitNodeOfCode, rawCircuitNodeCode]
  | and left right =>
      simp [rawCircuitNodeOfCode, rawCircuitNodeCode]
  | or left right =>
      simp [rawCircuitNodeOfCode, rawCircuitNodeCode]

def circuitInputClauseCallInputArity (atom : ℕ) : ℕ :=
  (Nat.unpair atom).1

def circuitInputClauseCallRequest (atom : ℕ) : ℕ :=
  (Nat.unpair atom).2

def circuitInputClauseCallIndex (atom : ℕ) : ℕ :=
  let inputArity := circuitInputClauseCallInputArity atom
  (Nat.unpair (circuitInputClauseCallRequest atom)).1 - inputArity

def circuitInputClauseCallOutput (atom : ℕ) : ℕ :=
  let inputArity := circuitInputClauseCallInputArity atom
  let request := circuitInputClauseCallRequest atom
  rawClauseStream <|
    circuitInputNodeClauses
      ((Nat.unpair request).1 - inputArity)
      (rawCircuitNodeOfCode inputArity (Nat.unpair request).2)

def circuitInputClauseCallFuel (_atom : ℕ) : ℕ :=
  circuitInputClauseFuel

@[simp] theorem circuitInputClauseCallInputArity_atom {n : ℕ}
    (index : ℕ) (node : BooleanNode n) :
    circuitInputClauseCallInputArity
        (circuitInputClauseCallAtom index node) = n := by
  simp [circuitInputClauseCallInputArity,
    circuitInputClauseCallAtom]

@[simp] theorem circuitInputClauseCallRequest_atom {n : ℕ}
    (index : ℕ) (node : BooleanNode n) :
    circuitInputClauseCallRequest
        (circuitInputClauseCallAtom index node) =
      circuitInputClauseRequest index node := by
  simp [circuitInputClauseCallRequest,
    circuitInputClauseCallAtom]

@[simp] theorem circuitInputClauseCallIndex_atom {n : ℕ}
    (index : ℕ) (node : BooleanNode n) :
    circuitInputClauseCallIndex
        (circuitInputClauseCallAtom index node) = index := by
  simp [circuitInputClauseCallIndex,
    circuitInputClauseCallInputArity,
    circuitInputClauseCallRequest, circuitInputClauseCallAtom,
    circuitInputClauseRequest, circuitInputGateVariable,
    gateVariable]

@[simp] theorem circuitInputClauseCallOutput_atom {n : ℕ}
    (index : ℕ) (node : BooleanNode n) :
    circuitInputClauseCallOutput
        (circuitInputClauseCallAtom index node) =
      rawClauseStream (circuitInputNodeClauses index node) := by
  simp only [circuitInputClauseCallOutput]
  rw [circuitInputClauseCallInputArity_atom,
    circuitInputClauseCallRequest_atom]
  simp [circuitInputClauseRequest, circuitInputGateVariable,
    gateVariable]

/-! ## One heterogeneous formula-clause callee -/

/-- Tags the two executable formula templates.  Tag zero emits an input
tautology; every nonzero tag invokes the existing node-clause emitter. -/
def circuitInputFormulaClauseTautologyAtom
    (inputArity index : ℕ) : ℕ :=
  Nat.pair inputArity (Nat.pair 0 index)

def circuitInputFormulaClauseNodeAtom {n : ℕ}
    (index : ℕ) (node : BooleanNode n) : ℕ :=
  Nat.pair n (Nat.pair 1 (circuitInputClauseRequest index node))

def circuitInputFormulaClauseCallOutput (atom : ℕ) : ℕ :=
  let inputArity := (Nat.unpair atom).1
  let taggedRequest := (Nat.unpair atom).2
  if (Nat.unpair taggedRequest).1 = 0 then
    rawClauseStream
      [circuitInputTautology (Nat.unpair taggedRequest).2]
  else
    circuitInputClauseCallOutput <|
      Nat.pair inputArity (Nat.unpair taggedRequest).2

def circuitInputFormulaClauseCallFuel (atom : ℕ) : ℕ :=
  let taggedRequest := (Nat.unpair atom).2
  if (Nat.unpair taggedRequest).1 = 0 then
    circuitInputTautologyFuel + 5
  else
    circuitInputClauseFuel + 5

def circuitInputFormulaClauseProgram : NPOracleProgram :=
  taggedProgramChoice circuitInputTautologyProgram circuitInputClauseProgram

theorem circuitInputFormulaClauseProgram_oracleFree :
    OracleFree circuitInputFormulaClauseProgram := by
  exact taggedProgramChoice_oracleFree
    circuitInputTautologyProgram circuitInputClauseProgram
    circuitInputTautologyProgram_oracleFree
    circuitInputClauseProgram_oracleFree

@[simp] theorem circuitInputFormulaClauseCallOutput_tautology
    (inputArity index : ℕ) :
    circuitInputFormulaClauseCallOutput
        (circuitInputFormulaClauseTautologyAtom inputArity index) =
      rawClauseStream [circuitInputTautology index] := by
  simp [circuitInputFormulaClauseCallOutput,
    circuitInputFormulaClauseTautologyAtom]

@[simp] theorem circuitInputFormulaClauseCallOutput_node {n : ℕ}
    (index : ℕ) (node : BooleanNode n) :
    circuitInputFormulaClauseCallOutput
        (circuitInputFormulaClauseNodeAtom index node) =
      rawClauseStream (circuitInputNodeClauses index node) := by
  simp only [circuitInputFormulaClauseCallOutput,
    circuitInputFormulaClauseNodeAtom, Nat.unpair_pair]
  rw [if_neg (by omega)]
  exact circuitInputClauseCallOutput_atom index node

@[simp] theorem circuitInputFormulaClauseCallFuel_tautology
    (inputArity index : ℕ) :
    circuitInputFormulaClauseCallFuel
        (circuitInputFormulaClauseTautologyAtom inputArity index) =
      circuitInputTautologyFuel + 5 := by
  simp [circuitInputFormulaClauseCallFuel,
    circuitInputFormulaClauseTautologyAtom]

@[simp] theorem circuitInputFormulaClauseCallFuel_node {n : ℕ}
    (index : ℕ) (node : BooleanNode n) :
    circuitInputFormulaClauseCallFuel
        (circuitInputFormulaClauseNodeAtom index node) =
      circuitInputClauseFuel + 5 := by
  simp [circuitInputFormulaClauseCallFuel,
    circuitInputFormulaClauseNodeAtom]

def circuitInputClauseAtomsFrom {n : ℕ} :
    ℕ → List (BooleanNode n) → List ℕ
  | _start, [] => []
  | start, node :: rest =>
      circuitInputClauseCallAtom start node ::
        circuitInputClauseAtomsFrom (start + 1) rest

def circuitInputClauseStreamsFrom {n : ℕ} :
    ℕ → List (BooleanNode n) → List ℕ
  | _start, [] => []
  | start, node :: rest =>
      rawClauseStream (circuitInputNodeClauses start node) ::
        circuitInputClauseStreamsFrom (start + 1) rest

def circuitInputClauseBitsFrom {n : ℕ} :
    ℕ → List (BooleanNode n) → List ℕ
  | _start, [] => []
  | start, node :: rest =>
      circuitInputClauseMaximumBits start node ::
        circuitInputClauseBitsFrom (start + 1) rest

@[simp] theorem circuitInputClauseAtomsFrom_length {n : ℕ}
    (start : ℕ) (nodes : List (BooleanNode n)) :
    (circuitInputClauseAtomsFrom start nodes).length = nodes.length := by
  induction nodes generalizing start with
  | nil => rfl
  | cons node rest ih =>
      simp [circuitInputClauseAtomsFrom, ih]

theorem circuitInputClauseAtom_mem_spec {n : ℕ}
    {start : ℕ} {nodes : List (BooleanNode n)} {atom : ℕ}
    (hmem : atom ∈ circuitInputClauseAtomsFrom start nodes) :
    ∃ index : ℕ, ∃ node : BooleanNode n,
      atom = circuitInputClauseCallAtom index node ∧
        circuitInputClauseMaximumBits index node ∈
          circuitInputClauseBitsFrom start nodes := by
  induction nodes generalizing start with
  | nil =>
      simp [circuitInputClauseAtomsFrom] at hmem
  | cons node rest ih =>
      simp only [circuitInputClauseAtomsFrom, List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · exact ⟨start, node, rfl, by
          simp [circuitInputClauseBitsFrom]⟩
      · obtain ⟨index, tailNode, hatom, hbits⟩ := ih hmem
        exact ⟨index, tailNode, hatom, by
          simp [circuitInputClauseBitsFrom, hbits]⟩

theorem circuitInputClauseOutputs_eq_streams {n : ℕ}
    (start : ℕ) (nodes : List (BooleanNode n)) :
    (circuitInputClauseAtomsFrom start nodes).map
        circuitInputClauseCallOutput =
      circuitInputClauseStreamsFrom start nodes := by
  induction nodes generalizing start with
  | nil => rfl
  | cons node rest ih =>
      simp [circuitInputClauseAtomsFrom,
        circuitInputClauseStreamsFrom, ih]

private theorem le_foldr_max_of_mem
    {value : ℕ} {values : List ℕ} (hmem : value ∈ values) :
    value ≤ values.foldr max 0 := by
  induction values with
  | nil => simp at hmem
  | cons head rest ih =>
      simp only [List.mem_cons] at hmem
      simp only [List.foldr]
      rcases hmem with rfl | hmem
      · exact Nat.le_max_left _ _
      · exact (ih hmem).trans (Nat.le_max_right _ _)

def circuitInputClauseBalancedCallBits {n : ℕ}
    (start : ℕ) (nodes : List (BooleanNode n)) : ℕ :=
  let atoms := circuitInputClauseAtomsFrom start nodes
  max
    (balancedCallRequiredBits circuitInputClauseCallOutput atoms)
    ((circuitInputClauseBitsFrom start nodes).foldr max 0)

theorem circuitInputClauseBalancedCallBits_required {n : ℕ}
    (start : ℕ) (nodes : List (BooleanNode n)) :
    balancedCallRequiredBits circuitInputClauseCallOutput
        (circuitInputClauseAtomsFrom start nodes) ≤
      circuitInputClauseBalancedCallBits start nodes :=
  Nat.le_max_left _ _

theorem circuitInputClauseCallBits_le {n : ℕ}
    (start : ℕ) (nodes : List (BooleanNode n))
    (index : ℕ) (node : BooleanNode n)
    (hmem :
      circuitInputClauseMaximumBits index node ∈
        circuitInputClauseBitsFrom start nodes) :
    circuitInputClauseMaximumBits index node ≤
      circuitInputClauseBalancedCallBits start nodes := by
  apply le_trans _ (Nat.le_max_right _ _)
  apply le_foldr_max_of_mem
  exact hmem

set_option maxHeartbeats 1000000 in
-- Dependent atom normalization expands the exact 80-instruction callee trace.
theorem run_circuitInputClauseCallAtom {n : ℕ}
    (start : ℕ) (nodes : List (BooleanNode n))
    (atom : ℕ) (hmem :
      atom ∈ circuitInputClauseAtomsFrom start nodes) :
    runNPOracleProgram circuitInputClauseProgram
        (circuitInputClauseBalancedCallBits start nodes)
        (circuitInputClauseCallFuel atom)
        (initialNPOracleState (Nat.unpair atom).1
          (Nat.unpair atom).2) =
      some (circuitInputClauseCallOutput atom) := by
  obtain ⟨index, node, rfl, hnodeBits⟩ :=
    circuitInputClauseAtom_mem_spec hmem
  rw [show circuitInputClauseCallFuel
      (circuitInputClauseCallAtom index node) =
        circuitInputClauseFuel by rfl]
  rw [show (Nat.unpair
      (circuitInputClauseCallAtom index node)).1 = n by
    simp [circuitInputClauseCallAtom]]
  rw [show (Nat.unpair
      (circuitInputClauseCallAtom index node)).2 =
        circuitInputClauseRequest index node by
    simp [circuitInputClauseCallAtom]]
  rw [circuitInputClauseCallOutput_atom]
  exact run_bits_mono
    (run_circuitInputClauseProgram index node)
    (circuitInputClauseCallBits_le start nodes index node hnodeBits)

theorem run_circuitInputClauseBalancedCallProgram {n : ℕ}
    (inputLength start : ℕ) (nodes : List (BooleanNode n)) :
    runNPOracleProgram
        (balancedCallProgram circuitInputClauseProgram)
        (circuitInputClauseBalancedCallBits start nodes)
        (balancedCallFuel circuitInputClauseProgram
          circuitInputClauseCallFuel
          (circuitInputClauseAtomsFrom start nodes))
        (initialNPOracleState inputLength
          (encodeBalancedList
            (circuitInputClauseAtomsFrom start nodes))) =
      some
        (encodeBalancedList
          (circuitInputClauseStreamsFrom start nodes)) := by
  rw [← circuitInputClauseOutputs_eq_streams start nodes]
  exact
    run_balancedCallProgram_from inputLength
      (circuitInputClauseAtomsFrom start nodes)
      circuitInputClauseCallFuel circuitInputClauseCallOutput
      (circuitInputClauseBalancedCallBits_required start nodes)
      (run_circuitInputClauseCallAtom start nodes)

theorem circuitInputClauseBalancedCallProgram_oracleFree :
    OracleFree (balancedCallProgram circuitInputClauseProgram) :=
  balancedCallProgram_oracleFree circuitInputClauseProgram_oracleFree

/-- Proof view of each raw stream returned by the batch caller. -/
def circuitInputClauseValueStreamsFrom {n : ℕ} :
    ℕ → List (BooleanNode n) → List (List ℕ)
  | _start, [] => []
  | start, node :: rest =>
      (circuitInputNodeClauses start node).map rawEncodedClause ::
        circuitInputClauseValueStreamsFrom (start + 1) rest

@[simp] theorem circuitInputClauseValueStreamsFrom_encode {n : ℕ}
    (start : ℕ) (nodes : List (BooleanNode n)) :
    (circuitInputClauseValueStreamsFrom start nodes).map
        encodeTaggedList =
      circuitInputClauseStreamsFrom start nodes := by
  induction nodes generalizing start with
  | nil => rfl
  | cons node rest inductionHypothesis =>
      simp [circuitInputClauseValueStreamsFrom,
        circuitInputClauseStreamsFrom, rawClauseStream,
        inductionHypothesis]

@[simp] theorem circuitInputClauseValueStreamsFrom_flatten {n : ℕ}
    (start : ℕ) (nodes : List (BooleanNode n)) :
    (circuitInputClauseValueStreamsFrom start nodes).flatten =
      (circuitInputNodesClausesFrom start nodes).map
        rawEncodedClause := by
  induction nodes generalizing start with
  | nil => rfl
  | cons node rest inductionHypothesis =>
      simp [circuitInputClauseValueStreamsFrom,
        circuitInputNodesClausesFrom, inductionHypothesis]

/-! ## Full circuit-input formula -/

def circuitInputFormulaNodeAtomsFrom {n : ℕ} :
    ℕ → List (BooleanNode n) → List ℕ
  | _start, [] => []
  | start, node :: rest =>
      circuitInputFormulaClauseNodeAtom start node ::
        circuitInputFormulaNodeAtomsFrom (start + 1) rest

def circuitInputFormulaAtoms {n : ℕ}
    (circuit : BooleanCircuit n) : List ℕ :=
    (List.range n).map
      (circuitInputFormulaClauseTautologyAtom n) ++
    circuitInputFormulaNodeAtomsFrom 0 circuit.nodes ++
      [circuitInputFormulaClauseNodeAtom circuit.output.val
        (.const true : BooleanNode n)]

def circuitInputFormulaCalleeBits {n : ℕ}
    (circuit : BooleanCircuit n) : List ℕ :=
    (List.range n).map circuitInputTautologyMaximumBits ++
    circuitInputClauseBitsFrom 0 circuit.nodes ++
      [circuitInputClauseMaximumBits circuit.output.val
        (.const true : BooleanNode n)]

def circuitInputFormulaValueStreams {n : ℕ}
    (circuit : BooleanCircuit n) : List (List ℕ) :=
  ((List.range n).map fun index =>
      [rawEncodedClause (circuitInputTautology index)]) ++
    circuitInputClauseValueStreamsFrom 0 circuit.nodes ++
      [[rawEncodedClause
        (positiveUnit
          (circuitInputGateVariable n circuit.output.val))]]

private theorem circuitInputTautologies_eq_rangeMap (count : ℕ) :
    circuitInputTautologies count =
      (List.range count).map circuitInputTautology := by
  induction count with
  | zero => rfl
  | succ count inductionHypothesis =>
      rw [circuitInputTautologies, inductionHypothesis, List.range_succ,
        List.map_append]
      rfl

private theorem circuitInputFormulaNodeAtoms_outputs {n : ℕ}
    (start : ℕ) (nodes : List (BooleanNode n)) :
    (circuitInputFormulaNodeAtomsFrom start nodes).map
        circuitInputFormulaClauseCallOutput =
      (circuitInputClauseValueStreamsFrom start nodes).map
        encodeTaggedList := by
  induction nodes generalizing start with
  | nil => rfl
  | cons node rest inductionHypothesis =>
      simp [circuitInputFormulaNodeAtomsFrom,
        circuitInputClauseValueStreamsFrom, inductionHypothesis,
        rawClauseStream]

private theorem circuitInputFormulaNodeAtom_mem_spec {n : ℕ}
    {start : ℕ} {nodes : List (BooleanNode n)} {atom : ℕ}
    (hmem : atom ∈ circuitInputFormulaNodeAtomsFrom start nodes) :
    ∃ index : ℕ, ∃ node : BooleanNode n,
      atom = circuitInputFormulaClauseNodeAtom index node ∧
        circuitInputClauseMaximumBits index node ∈
          circuitInputClauseBitsFrom start nodes := by
  induction nodes generalizing start with
  | nil =>
      simp [circuitInputFormulaNodeAtomsFrom] at hmem
  | cons node rest inductionHypothesis =>
      simp only [circuitInputFormulaNodeAtomsFrom, List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · exact ⟨start, node, rfl, by
          simp [circuitInputClauseBitsFrom]⟩
      · obtain ⟨index, tailNode, hatom, hbits⟩ :=
          inductionHypothesis hmem
        exact ⟨index, tailNode, hatom, by
          simp [circuitInputClauseBitsFrom, hbits]⟩

@[simp] theorem circuitInputFormulaAtoms_outputs {n : ℕ}
    (circuit : BooleanCircuit n) :
    (circuitInputFormulaAtoms circuit).map
        circuitInputFormulaClauseCallOutput =
      (circuitInputFormulaValueStreams circuit).map
        encodeTaggedList := by
  have htautologies :
      ((List.range n).map
          (circuitInputFormulaClauseTautologyAtom n)).map
          circuitInputFormulaClauseCallOutput =
        (((List.range n).map fun index =>
          [rawEncodedClause (circuitInputTautology index)])).map
            encodeTaggedList := by
    rw [List.map_map, List.map_map]
    apply List.map_congr_left
    intro index hindex
    simp [Function.comp_apply, rawClauseStream]
  unfold circuitInputFormulaAtoms circuitInputFormulaValueStreams
  simp only [List.map_append]
  rw [htautologies, circuitInputFormulaNodeAtoms_outputs]
  simp [rawClauseStream, circuitInputNodeClauses]

private theorem flatten_tautologyValueStreams (count : ℕ) :
    ((List.range count).map fun index =>
        [rawEncodedClause (circuitInputTautology index)]).flatten =
      (circuitInputTautologies count).map rawEncodedClause := by
  rw [circuitInputTautologies_eq_rangeMap]
  induction List.range count with
  | nil => rfl
  | cons index rest inductionHypothesis =>
      simp [inductionHypothesis]

@[simp] theorem circuitInputFormulaValueStreams_flatten {n : ℕ}
    (circuit : BooleanCircuit n) :
    (circuitInputFormulaValueStreams circuit).flatten =
      (circuitInputFormula circuit).map rawEncodedClause := by
  unfold circuitInputFormulaValueStreams circuitInputFormula
  rw [List.flatten_append, List.flatten_append, List.map_append,
    List.map_append, flatten_tautologyValueStreams,
    circuitInputClauseValueStreamsFrom_flatten]
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil,
    List.map_cons, List.map_nil, List.append_assoc]

def circuitInputFormulaBalancedCallBits {n : ℕ}
    (circuit : BooleanCircuit n) : ℕ :=
  max
    (balancedCallRequiredBits circuitInputFormulaClauseCallOutput
      (circuitInputFormulaAtoms circuit))
    ((circuitInputFormulaCalleeBits circuit).foldr max 0)

private theorem circuitInputFormulaBalancedCallBits_required {n : ℕ}
    (circuit : BooleanCircuit n) :
    balancedCallRequiredBits circuitInputFormulaClauseCallOutput
        (circuitInputFormulaAtoms circuit) ≤
      circuitInputFormulaBalancedCallBits circuit :=
  Nat.le_max_left _ _

private theorem circuitInputFormulaCalleeBits_le {n : ℕ}
    (circuit : BooleanCircuit n) {value : ℕ}
    (hmem : value ∈ circuitInputFormulaCalleeBits circuit) :
    value ≤ circuitInputFormulaBalancedCallBits circuit := by
  exact (le_foldr_max_of_mem hmem).trans (Nat.le_max_right _ _)

private theorem run_circuitInputFormulaClauseAtom {n : ℕ}
    (circuit : BooleanCircuit n) (atom : ℕ)
    (hmem : atom ∈ circuitInputFormulaAtoms circuit) :
    runNPOracleProgram circuitInputFormulaClauseProgram
        (circuitInputFormulaBalancedCallBits circuit)
        (circuitInputFormulaClauseCallFuel atom)
        (initialNPOracleState (Nat.unpair atom).1
          (Nat.unpair atom).2) =
      some (circuitInputFormulaClauseCallOutput atom) := by
  have hatomBits :
      natBitLength atom ≤
        circuitInputFormulaBalancedCallBits circuit :=
    (balancedCallRequiredBits_request
      circuitInputFormulaClauseCallOutput hmem).trans
        (circuitInputFormulaBalancedCallBits_required circuit)
  have houtputBits :
      natBitLength (circuitInputFormulaClauseCallOutput atom) ≤
        circuitInputFormulaBalancedCallBits circuit := by
    apply (natBitLength_mono ?_).trans <|
      (balancedCallRequiredBits_pair
        circuitInputFormulaClauseCallOutput hmem).trans
          (circuitInputFormulaBalancedCallBits_required circuit)
    exact Nat.right_le_pair atom
      (circuitInputFormulaClauseCallOutput atom)
  unfold circuitInputFormulaAtoms at hmem
  rw [List.mem_append] at hmem
  rcases hmem with hprefix | hfinal
  · rw [List.mem_append] at hprefix
    rcases hprefix with htautology | hnode
    · obtain ⟨index, hindex, hatom⟩ := List.mem_map.mp htautology
      subst atom
      have hsource :
          circuitInputTautologyMaximumBits index ≤
            circuitInputFormulaBalancedCallBits circuit := by
        apply circuitInputFormulaCalleeBits_le circuit
        unfold circuitInputFormulaCalleeBits
        apply List.mem_append.mpr
        exact Or.inl <| List.mem_append.mpr <|
          Or.inl (List.mem_map.mpr ⟨index, hindex, rfl⟩)
      have hout :
          natBitLength (rawClauseStream [circuitInputTautology index]) ≤
            circuitInputFormulaBalancedCallBits circuit := by
        simpa only [circuitInputFormulaClauseCallOutput_tautology] using
          houtputBits
      rw [circuitInputFormulaClauseCallFuel_tautology,
        circuitInputFormulaClauseCallOutput_tautology]
      simp only [circuitInputFormulaClauseTautologyAtom, Nat.unpair_pair]
      simpa only [circuitInputFormulaClauseProgram,
        taggedProgramChoiceFuel] using
          run_taggedProgramChoice_zero
            circuitInputTautologyProgram circuitInputClauseProgram
            n index (circuitInputFormulaBalancedCallBits circuit)
            circuitInputTautologyFuel
            (rawClauseStream [circuitInputTautology index])
            hatomBits
            (run_bits_mono
              (run_circuitInputTautologyProgram n index) hsource)
            hout
    · obtain ⟨index, node, hatom, hnodeBits⟩ :=
        circuitInputFormulaNodeAtom_mem_spec hnode
      subst atom
      have hsource :
          circuitInputClauseMaximumBits index node ≤
            circuitInputFormulaBalancedCallBits circuit := by
        apply circuitInputFormulaCalleeBits_le circuit
        unfold circuitInputFormulaCalleeBits
        apply List.mem_append.mpr
        exact Or.inl (List.mem_append.mpr (Or.inr hnodeBits))
      have hout :
          natBitLength
              (rawClauseStream (circuitInputNodeClauses index node)) ≤
            circuitInputFormulaBalancedCallBits circuit := by
        simpa only [circuitInputFormulaClauseCallOutput_node] using
          houtputBits
      rw [circuitInputFormulaClauseCallFuel_node,
        circuitInputFormulaClauseCallOutput_node]
      simp only [circuitInputFormulaClauseNodeAtom, Nat.unpair_pair]
      simpa only [circuitInputFormulaClauseProgram,
        taggedProgramChoiceFuel] using
          run_taggedProgramChoice_nonzero
            circuitInputTautologyProgram circuitInputClauseProgram
            n 1 (circuitInputClauseRequest index node)
            (circuitInputFormulaBalancedCallBits circuit)
            circuitInputClauseFuel
            (rawClauseStream (circuitInputNodeClauses index node))
            (by omega) hatomBits
            (run_bits_mono
              (run_circuitInputClauseProgram index node) hsource)
            hout
  · rw [List.mem_singleton] at hfinal
    subst atom
    let outputNode : BooleanNode n := .const true
    have hsource :
        circuitInputClauseMaximumBits circuit.output.val outputNode ≤
          circuitInputFormulaBalancedCallBits circuit := by
      apply circuitInputFormulaCalleeBits_le circuit
      unfold circuitInputFormulaCalleeBits
      apply List.mem_append.mpr
      exact Or.inr (by simp [outputNode])
    have hout :
        natBitLength
            (rawClauseStream
              (circuitInputNodeClauses circuit.output.val outputNode)) ≤
          circuitInputFormulaBalancedCallBits circuit := by
      simpa only [circuitInputFormulaClauseCallOutput_node] using
        houtputBits
    rw [show circuitInputFormulaClauseCallFuel
        (circuitInputFormulaClauseNodeAtom circuit.output.val outputNode) =
          circuitInputClauseFuel + 5 by
      exact circuitInputFormulaClauseCallFuel_node _ _]
    rw [show circuitInputFormulaClauseCallOutput
        (circuitInputFormulaClauseNodeAtom circuit.output.val outputNode) =
          rawClauseStream
            (circuitInputNodeClauses circuit.output.val outputNode) by
      exact circuitInputFormulaClauseCallOutput_node _ _]
    simpa only [outputNode, circuitInputFormulaClauseNodeAtom,
      circuitInputFormulaClauseProgram, taggedProgramChoiceFuel,
      Nat.unpair_pair] using
      run_taggedProgramChoice_nonzero
        circuitInputTautologyProgram circuitInputClauseProgram
        n 1 (circuitInputClauseRequest circuit.output.val outputNode)
        (circuitInputFormulaBalancedCallBits circuit)
        circuitInputClauseFuel
        (rawClauseStream
          (circuitInputNodeClauses circuit.output.val outputNode))
        (by omega) hatomBits
        (run_bits_mono
          (run_circuitInputClauseProgram circuit.output.val outputNode)
          hsource)
        hout

theorem run_circuitInputFormulaBalancedCallProgram {n : ℕ}
    (inputLength : ℕ) (circuit : BooleanCircuit n) :
    runNPOracleProgram
        (balancedCallProgram circuitInputFormulaClauseProgram)
        (circuitInputFormulaBalancedCallBits circuit)
        (balancedCallFuel circuitInputFormulaClauseProgram
          circuitInputFormulaClauseCallFuel
          (circuitInputFormulaAtoms circuit))
        (initialNPOracleState inputLength
          (encodeBalancedList (circuitInputFormulaAtoms circuit))) =
      some
        (encodeBalancedList
          ((circuitInputFormulaValueStreams circuit).map
            encodeTaggedList)) := by
  rw [← circuitInputFormulaAtoms_outputs circuit]
  exact run_balancedCallProgram_from inputLength
    (circuitInputFormulaAtoms circuit)
    circuitInputFormulaClauseCallFuel
    circuitInputFormulaClauseCallOutput
    (circuitInputFormulaBalancedCallBits_required circuit)
    (run_circuitInputFormulaClauseAtom circuit)

theorem circuitInputFormulaBalancedCallProgram_oracleFree :
    OracleFree
      (balancedCallProgram circuitInputFormulaClauseProgram) :=
  balancedCallProgram_oracleFree
    circuitInputFormulaClauseProgram_oracleFree

def circuitInputFormulaBalancedFoldProgram : NPOracleProgram :=
  linkPrograms
    (balancedCallProgram circuitInputFormulaClauseProgram)
    balancedClauseStreamFlattenProgram

def circuitInputFormulaBalancedFoldFuel {n : ℕ}
    (circuit : BooleanCircuit n) : ℕ :=
  linkFuel balancedClauseStreamFlattenProgram
    (balancedCallFuel circuitInputFormulaClauseProgram
      circuitInputFormulaClauseCallFuel
      (circuitInputFormulaAtoms circuit))
    (balancedClauseStreamFlattenFuel
      (circuitInputFormulaValueStreams circuit))

def circuitInputFormulaBalancedFoldBits {n : ℕ}
    (inputLength : ℕ) (circuit : BooleanCircuit n) : ℕ :=
  max (natBitLength inputLength) <|
    max (circuitInputFormulaBalancedCallBits circuit)
      (balancedClauseStreamFlattenMaximumBits
        (circuitInputFormulaValueStreams circuit))

theorem circuitInputFormulaBalancedFoldProgram_oracleFree :
    OracleFree circuitInputFormulaBalancedFoldProgram := by
  apply oracleFree_linkPrograms
  · exact circuitInputFormulaBalancedCallProgram_oracleFree
  · exact balancedClauseStreamFlattenProgram_oracleFree

/-- The full formula boundary includes input tautologies, every compiled node,
and the positive output unit in their semantic order. -/
theorem run_circuitInputFormulaBalancedFoldProgram {n : ℕ}
    (inputLength : ℕ) (circuit : BooleanCircuit n) :
    runNPOracleProgram circuitInputFormulaBalancedFoldProgram
        (circuitInputFormulaBalancedFoldBits inputLength circuit)
        (circuitInputFormulaBalancedFoldFuel circuit)
        (initialNPOracleState inputLength
          (encodeBalancedList (circuitInputFormulaAtoms circuit))) =
      some (rawClauseStream (circuitInputFormula circuit)) := by
  have hinputBits :
      natBitLength inputLength ≤
        circuitInputFormulaBalancedFoldBits inputLength circuit :=
    Nat.le_max_left _ _
  have hcallBits :
      circuitInputFormulaBalancedCallBits circuit ≤
        circuitInputFormulaBalancedFoldBits inputLength circuit := by
    exact (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hfoldBits :
      balancedClauseStreamFlattenMaximumBits
          (circuitInputFormulaValueStreams circuit) ≤
        circuitInputFormulaBalancedFoldBits inputLength circuit := by
    exact (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hpositive :
      1 ≤ circuitInputFormulaBalancedFoldBits inputLength circuit := by
    unfold circuitInputFormulaBalancedFoldBits natBitLength
    omega
  apply run_linkPrograms hpositive hinputBits
  · exact run_bits_mono
      (run_circuitInputFormulaBalancedCallProgram inputLength circuit)
      hcallBits
  · have hrun :=
      run_bits_mono
        (run_balancedClauseStreamFlattenProgram
          (circuitInputFormulaValueStreams circuit) inputLength)
        hfoldBits
    simpa [rawClauseStream] using hrun

/-- The production node-clause stage: one balanced batch call followed
immediately by the direct balanced-tree fold. -/
def circuitInputClauseBalancedFoldProgram : NPOracleProgram :=
  linkPrograms
    (balancedCallProgram circuitInputClauseProgram)
    balancedClauseStreamFlattenProgram

def circuitInputClauseBalancedFoldFuel {n : ℕ}
    (start : ℕ) (nodes : List (BooleanNode n)) : ℕ :=
  linkFuel balancedClauseStreamFlattenProgram
    (balancedCallFuel circuitInputClauseProgram
      circuitInputClauseCallFuel
      (circuitInputClauseAtomsFrom start nodes))
    (balancedClauseStreamFlattenFuel
      (circuitInputClauseValueStreamsFrom start nodes))

def circuitInputClauseBalancedFoldBits {n : ℕ}
    (inputLength start : ℕ)
    (nodes : List (BooleanNode n)) : ℕ :=
  max (natBitLength inputLength) <|
    max (circuitInputClauseBalancedCallBits start nodes)
      (balancedClauseStreamFlattenMaximumBits
        (circuitInputClauseValueStreamsFrom start nodes))

theorem circuitInputClauseBalancedFoldProgram_oracleFree :
    OracleFree circuitInputClauseBalancedFoldProgram := by
  apply oracleFree_linkPrograms
  · exact circuitInputClauseBalancedCallProgram_oracleFree
  · exact balancedClauseStreamFlattenProgram_oracleFree

/-- Exact batch-to-stream refinement.  No tagged outer compatibility list or
host decoder exists between the two fixed interpreters. -/
theorem run_circuitInputClauseBalancedFoldProgram {n : ℕ}
    (inputLength start : ℕ) (nodes : List (BooleanNode n)) :
    runNPOracleProgram circuitInputClauseBalancedFoldProgram
        (circuitInputClauseBalancedFoldBits inputLength start nodes)
        (circuitInputClauseBalancedFoldFuel start nodes)
        (initialNPOracleState inputLength
          (encodeBalancedList
            (circuitInputClauseAtomsFrom start nodes))) =
      some
        (rawClauseStream
          (circuitInputNodesClausesFrom start nodes)) := by
  have hinputBits :
      natBitLength inputLength ≤
        circuitInputClauseBalancedFoldBits inputLength start nodes :=
    Nat.le_max_left _ _
  have hcallBits :
      circuitInputClauseBalancedCallBits start nodes ≤
        circuitInputClauseBalancedFoldBits inputLength start nodes := by
    unfold circuitInputClauseBalancedFoldBits
    exact
      (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hfoldBits :
      balancedClauseStreamFlattenMaximumBits
          (circuitInputClauseValueStreamsFrom start nodes) ≤
        circuitInputClauseBalancedFoldBits inputLength start nodes := by
    unfold circuitInputClauseBalancedFoldBits
    exact
      (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hpositive :
      1 ≤ circuitInputClauseBalancedFoldBits inputLength start nodes := by
    unfold circuitInputClauseBalancedFoldBits natBitLength
    omega
  apply run_linkPrograms hpositive hinputBits
  · exact run_bits_mono
      (run_circuitInputClauseBalancedCallProgram
        inputLength start nodes)
      hcallBits
  · rw [← circuitInputClauseValueStreamsFrom_encode start nodes]
    have hrun :=
      run_bits_mono
        (run_balancedClauseStreamFlattenProgram
          (circuitInputClauseValueStreamsFrom start nodes)
          inputLength)
        hfoldBits
    simpa [rawClauseStream] using hrun

/-! ## Count-preserving handoff -/

/-- Adapt `pair(balanced calls, unary count)` to
`pair(forward raw clauses, unary count)` without a host decode or a second
clause-generation path. -/
def countedCircuitInputClauseBalancedFoldProgram : NPOracleProgram :=
  preserveRightProgram circuitInputClauseBalancedFoldProgram

def countedCircuitInputClauseBalancedFoldInput {n : ℕ}
    (start : ℕ) (nodes : List (BooleanNode n)) (count : ℕ) : ℕ :=
  Nat.pair
    (encodeBalancedList (circuitInputClauseAtomsFrom start nodes))
    (encodeUnary count)

def countedCircuitInputClauseBalancedFoldOutput {n : ℕ}
    (start : ℕ) (nodes : List (BooleanNode n)) (count : ℕ) : ℕ :=
  Nat.pair
    (rawClauseStream (circuitInputNodesClausesFrom start nodes))
    (encodeUnary count)

def countedCircuitInputClauseBalancedFoldFuel {n : ℕ}
    (start : ℕ) (nodes : List (BooleanNode n)) : ℕ :=
  preserveRightFuel (circuitInputClauseBalancedFoldFuel start nodes)

def countedCircuitInputClauseBalancedFoldBits {n : ℕ}
    (inputLength start : ℕ) (nodes : List (BooleanNode n))
    (count : ℕ) : ℕ :=
  preserveRightBits
    (circuitInputClauseBalancedFoldBits inputLength start nodes)
    (encodeBalancedList (circuitInputClauseAtomsFrom start nodes))
    (encodeUnary count)
    (rawClauseStream (circuitInputNodesClausesFrom start nodes))

theorem countedCircuitInputClauseBalancedFoldProgram_oracleFree :
    OracleFree countedCircuitInputClauseBalancedFoldProgram := by
  exact preserveRightProgram_oracleFree
    circuitInputClauseBalancedFoldProgram
    circuitInputClauseBalancedFoldProgram_oracleFree

/-- Exact count-preserving refinement for the node-clause stage.  The theorem
intentionally names `circuitInputNodesClausesFrom`: input tautologies and the
output unit clause belong to later circuit-formula stages. -/
theorem run_countedCircuitInputClauseBalancedFoldProgram {n : ℕ}
    (inputLength start : ℕ) (nodes : List (BooleanNode n))
    (count : ℕ) :
    runNPOracleProgram countedCircuitInputClauseBalancedFoldProgram
        (countedCircuitInputClauseBalancedFoldBits
          inputLength start nodes count)
        (countedCircuitInputClauseBalancedFoldFuel start nodes)
        (initialNPOracleState inputLength
          (countedCircuitInputClauseBalancedFoldInput
            start nodes count)) =
      some
        (countedCircuitInputClauseBalancedFoldOutput
          start nodes count) := by
  exact run_preserveRightProgram
    circuitInputClauseBalancedFoldProgram
    inputLength
    (circuitInputClauseBalancedFoldBits inputLength start nodes)
    (circuitInputClauseBalancedFoldFuel start nodes)
    (encodeBalancedList (circuitInputClauseAtomsFrom start nodes))
    (encodeUnary count)
    (rawClauseStream (circuitInputNodesClausesFrom start nodes))
    (run_circuitInputClauseBalancedFoldProgram inputLength start nodes)

/-! ## Full-formula count-preserving handoff -/

/-- The sole count-preserving circuit-input formula program.  The left side
contains every input tautology, node clause, and the positive output unit. -/
def countedCircuitInputFormulaBalancedFoldProgram : NPOracleProgram :=
  preserveRightProgram circuitInputFormulaBalancedFoldProgram

def countedCircuitInputFormulaBalancedFoldInput {n : ℕ}
    (circuit : BooleanCircuit n) (count : ℕ) : ℕ :=
  Nat.pair
    (encodeBalancedList (circuitInputFormulaAtoms circuit))
    (encodeUnary count)

def countedCircuitInputFormulaBalancedFoldOutput {n : ℕ}
    (circuit : BooleanCircuit n) (count : ℕ) : ℕ :=
  Nat.pair
    (rawClauseStream (circuitInputFormula circuit))
    (encodeUnary count)

def countedCircuitInputFormulaBalancedFoldFuel {n : ℕ}
    (circuit : BooleanCircuit n) : ℕ :=
  preserveRightFuel (circuitInputFormulaBalancedFoldFuel circuit)

def countedCircuitInputFormulaBalancedFoldBits {n : ℕ}
    (inputLength : ℕ) (circuit : BooleanCircuit n) (count : ℕ) : ℕ :=
  preserveRightBits
    (circuitInputFormulaBalancedFoldBits inputLength circuit)
    (encodeBalancedList (circuitInputFormulaAtoms circuit))
    (encodeUnary count)
    (rawClauseStream (circuitInputFormula circuit))

theorem countedCircuitInputFormulaBalancedFoldProgram_oracleFree :
    OracleFree countedCircuitInputFormulaBalancedFoldProgram := by
  exact preserveRightProgram_oracleFree
    circuitInputFormulaBalancedFoldProgram
    circuitInputFormulaBalancedFoldProgram_oracleFree

/-- Exact count-preserving refinement for the complete circuit-input CNF. -/
theorem run_countedCircuitInputFormulaBalancedFoldProgram {n : ℕ}
    (inputLength : ℕ) (circuit : BooleanCircuit n) (count : ℕ) :
    runNPOracleProgram countedCircuitInputFormulaBalancedFoldProgram
        (countedCircuitInputFormulaBalancedFoldBits
          inputLength circuit count)
        (countedCircuitInputFormulaBalancedFoldFuel circuit)
        (initialNPOracleState inputLength
          (countedCircuitInputFormulaBalancedFoldInput circuit count)) =
      some (countedCircuitInputFormulaBalancedFoldOutput circuit count) := by
  exact run_preserveRightProgram
    circuitInputFormulaBalancedFoldProgram
    inputLength
    (circuitInputFormulaBalancedFoldBits inputLength circuit)
    (circuitInputFormulaBalancedFoldFuel circuit)
    (encodeBalancedList (circuitInputFormulaAtoms circuit))
    (encodeUnary count)
    (rawClauseStream (circuitInputFormula circuit))
    (run_circuitInputFormulaBalancedFoldProgram inputLength circuit)

end NearCubicWires.CircuitInputClauseBalancedCall
