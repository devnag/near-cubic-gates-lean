import Proof.Foundations.RecoveryPipeline
import Proof.Foundations.ProjectionPCPPadding
import Proof.Foundations.RefuterClockClosure
import Proof.Foundations.CaseOnePadding
import Proof.Foundations.PhysicalRecovery
import Proof.Foundations.BooleanCircuitSizePadding

/-!
# Outer-PCP Case-1/Case-2 extraction

This module performs the semantic split that occurs only after the fixed weak
machine has forced a hierarchy YES word.  It uses the genuine projection PCP:
absence of a small accepting oracle circuit yields a worst-case-hard proof
function for the STV branch, while an accepting circuit is passed to the
pointwise PCPP and gives one canonical honest occurrence table.
-/

namespace NearCubicWires.OuterPCPRecovery

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.RecoveryPipeline
open NearCubicWires.SourceInterfaces
open NearCubicWires.ProjectionPCPPadding
open NearCubicWires.RefuterClockClosure
open NearCubicWires.CaseOnePadding
open NearCubicWires.CircuitRestriction
open NearCubicWires.ComponentwiseTransfer
open NearCubicWires.PhysicalRecovery

/-- The native random string presented to one projected oracle query. -/
def projectedInput
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (randomness : BitInput (pcp.nativeWidth n))
    (query : Fin (pcp.queryCount n)) :
    BitInput (pcp.nativeWidth n) :=
  fun bit => (pcp.queryAddressBits input query bit).eval randomness

/-- Evaluate the outer verifier after substituting one Boolean oracle
circuit.  The circuit is shared across every query and random row. -/
def acceptsOracleCircuit
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n)
    (circuit : BooleanCircuit (pcp.nativeWidth n))
    (randomness : BitInput (pcp.nativeWidth n)) : Bool :=
  (pcp.decision input randomness).eval fun query =>
    circuit.eval (projectedInput pcp input randomness query)

/-- Regard a native PCP proof table as its address-bit Boolean function. -/
def proofFunction
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (proof : BitInput (2 ^ pcp.nativeWidth n)) :
    BoolFunction (pcp.nativeWidth n) :=
  fun address => proof (binaryAddress address)

/-- The canonical truth-table ABI enumerates a PCP proof in its native
numeric address order.  This is the variable order used by C.12's zero-first
self-reduction. -/
@[simp] theorem boolFunctionTable_proofFunction
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (proof : BitInput (2 ^ pcp.nativeWidth n)) :
    boolFunctionTable (proofFunction pcp proof) = List.ofFn proof := by
  apply List.ext_getElem
  · simp [boolFunctionTable]
  · intro index hleft _hright
    have hindex : index < 2 ^ pcp.nativeWidth n := by
      simpa [boolFunctionTable] using hleft
    simp only [boolFunctionTable, List.getElem_map, List.getElem_range,
      proofFunction, List.getElem_ofFn]
    rw [binaryAddress_testBit hindex]

/-- Decoder-order fields for one Boolean DAG node.  Tags and typed fields are
ordered directly; no wrapper-code ordering leaks into canonical recovery. -/
def canonicalBooleanNodeFields {n : ℕ} : BooleanNode n → List ℕ
  | .const value => [0, value.toNat]
  | .input index => [1, index.val]
  | .not child => [2, child]
  | .and left right => [3, left, right]
  | .or left right => [4, left, right]

theorem canonicalBooleanNodeFields_injective {n : ℕ} :
    Function.Injective (@canonicalBooleanNodeFields n) := by
  intro left right hfields
  cases left <;> cases right <;>
    simp only [canonicalBooleanNodeFields, List.cons.injEq, true_and,
      and_true, Nat.reduceEqDiff, false_and, Bool.toNat] at hfields
  case const.const leftValue rightValue =>
    cases leftValue <;> cases rightValue <;>
      first | contradiction | rfl
  case input.input =>
    have hindex := Fin.ext hfields
    cases hindex
    rfl
  case not.not =>
    cases hfields
    rfl
  case and.and =>
    rcases hfields with ⟨rfl, rfl⟩
    rfl
  case or.or =>
    rcases hfields with ⟨rfl, rfl⟩
    rfl

/-- The circuit's structural recovery order: every node record in topological
decoder order, followed by a distinguished output record. -/
def canonicalBooleanCircuitFields {n : ℕ}
    (circuit : BooleanCircuit n) : List (List ℕ) :=
  circuit.nodes.map canonicalBooleanNodeFields ++
    [[5, circuit.output.val]]

theorem canonicalBooleanCircuitFields_injective {n : ℕ} :
    Function.Injective (@canonicalBooleanCircuitFields n) := by
  rintro ⟨leftNodes, leftOutput, leftWellFormed⟩
    ⟨rightNodes, rightOutput, rightWellFormed⟩ hfields
  have hlength : leftNodes.length = rightNodes.length := by
    have := congrArg List.length hfields
    simpa [canonicalBooleanCircuitFields] using this
  have hparts := List.append_inj hfields (by simp [hlength])
  have hnodes : leftNodes = rightNodes :=
    canonicalBooleanNodeFields_injective.list_map hparts.1
  subst rightNodes
  have houtput : leftOutput = rightOutput := by
    apply Fin.ext
    simpa using hparts.2
  subst rightOutput
  rfl

/- The bounded syntax below is both the finite source for canonical selection
and the typed description decoded by C.12.  Child indices carry their
topological bound in their type, so an invalid DAG never enters the candidate
set. -/
inductive BoundedBooleanNode (n bound : ℕ) where
  | const (value : Bool)
  | input (index : Fin n)
  | not (child : Fin bound)
  | and (left right : Fin bound)
  | or (left right : Fin bound)
  deriving Fintype

def BoundedBooleanNode.fields {n bound : ℕ} :
    BoundedBooleanNode n bound → List ℕ
  | .const value => [0, value.toNat]
  | .input index => [1, index.val]
  | .not child => [2, child.val]
  | .and left right => [3, left.val, right.val]
  | .or left right => [4, left.val, right.val]

def BoundedBooleanNode.toNode {n bound : ℕ} :
    BoundedBooleanNode n bound → BooleanNode n
  | .const value => .const value
  | .input index => .input index
  | .not child => .not child.val
  | .and left right => .and left.val right.val
  | .or left right => .or left.val right.val

@[simp] theorem BoundedBooleanNode.toNode_wellFormed
    {n bound : ℕ} (node : BoundedBooleanNode n bound) :
    node.toNode.WellFormedAt bound := by
  cases node <;> simp [BoundedBooleanNode.toNode,
    BooleanNode.WellFormedAt]

def boundedBooleanNodeOfWellFormed {n index : ℕ}
    (node : BooleanNode n) (hwell : node.WellFormedAt index) :
    BoundedBooleanNode n index :=
  match node with
  | .const value => .const value
  | .input inputIndex => .input inputIndex
  | .not child => .not ⟨child, hwell⟩
  | .and left right => .and ⟨left, hwell.1⟩ ⟨right, hwell.2⟩
  | .or left right => .or ⟨left, hwell.1⟩ ⟨right, hwell.2⟩

@[simp] theorem boundedBooleanNode_fields_ofWellFormed
    {n index : ℕ} (node : BooleanNode n)
    (hwell : node.WellFormedAt index) :
    (boundedBooleanNodeOfWellFormed node hwell).fields =
      canonicalBooleanNodeFields node := by
  cases node <;> rfl

@[simp] theorem boundedBooleanNode_toNode_ofWellFormed
    {n index : ℕ} (node : BooleanNode n)
    (hwell : node.WellFormedAt index) :
    (boundedBooleanNodeOfWellFormed node hwell).toNode = node := by
  cases node <;> rfl

structure BoundedCircuitKeySource (n bound : ℕ) where
  nodeCount : Fin (bound + 1)
  nodes :
    (index : Fin nodeCount.val) → BoundedBooleanNode n index.val
  output : Fin nodeCount.val
  deriving Fintype

def BoundedCircuitKeySource.toCircuit {n bound : ℕ}
    (source : BoundedCircuitKeySource n bound) : BooleanCircuit n where
  nodes :=
    List.ofFn fun index =>
      (source.nodes index).toNode
  output :=
    ⟨source.output.val, by
      simpa only [List.length_ofFn] using source.output.isLt⟩
  wellFormed := by
    intro index
    rw [List.get_ofFn]
    convert
      BoundedBooleanNode.toNode_wellFormed
        (source.nodes
          (Fin.cast (by simp only [List.length_ofFn]) index)) using 1
    exact
      (Fin.val_cast (by simp only [List.length_ofFn]) index).symm

@[simp] theorem BoundedCircuitKeySource.toCircuit_size_le
    {n bound : ℕ} (source : BoundedCircuitKeySource n bound) :
    source.toCircuit.size ≤ bound := by
  simpa [BoundedCircuitKeySource.toCircuit, BooleanCircuit.size] using
    Nat.le_of_lt_succ source.nodeCount.isLt

def BoundedCircuitKeySource.fields {n bound : ℕ}
    (source : BoundedCircuitKeySource n bound) : List (List ℕ) :=
  List.ofFn (fun index => (source.nodes index).fields) ++
    [[5, source.output.val]]

def boundedCircuitKeySourceOfCircuit {n bound : ℕ}
    (circuit : BooleanCircuit n) (hsize : circuit.size ≤ bound) :
    BoundedCircuitKeySource n bound where
  nodeCount := ⟨circuit.nodes.length, by
    simpa [BooleanCircuit.size] using Nat.lt_succ_of_le hsize⟩
  nodes := fun index =>
    boundedBooleanNodeOfWellFormed (circuit.nodes.get index)
      (circuit.wellFormed index)
  output := circuit.output

@[simp] theorem boundedCircuitKeySource_fields_ofCircuit
    {n bound : ℕ} (circuit : BooleanCircuit n)
    (hsize : circuit.size ≤ bound) :
    (boundedCircuitKeySourceOfCircuit circuit hsize).fields =
      canonicalBooleanCircuitFields circuit := by
  unfold BoundedCircuitKeySource.fields canonicalBooleanCircuitFields
  congr 1
  apply List.ext_getElem
  · simp [boundedCircuitKeySourceOfCircuit]
  · intro index _hleft _hright
    simp [boundedCircuitKeySourceOfCircuit]

private theorem booleanCircuit_ext {n : ℕ}
    (left right : BooleanCircuit n)
    (hnodes : left.nodes = right.nodes)
    (houtput : left.output.val = right.output.val) :
    left = right := by
  cases left with
  | mk leftNodes leftOutput leftWellFormed =>
      cases right with
      | mk rightNodes rightOutput rightWellFormed =>
          simp only at hnodes houtput
          subst rightNodes
          have hfin : leftOutput = rightOutput :=
            Fin.ext houtput
          subst rightOutput
          rfl

@[simp] theorem boundedCircuitKeySource_toCircuit_ofCircuit
    {n bound : ℕ} (circuit : BooleanCircuit n)
    (hsize : circuit.size ≤ bound) :
    (boundedCircuitKeySourceOfCircuit circuit hsize).toCircuit =
      circuit := by
  cases circuit with
  | mk nodes output wellFormed =>
      let constructed :=
        (boundedCircuitKeySourceOfCircuit
          { nodes := nodes
            output := output
            wellFormed := wellFormed } hsize).toCircuit
      have hnodes : constructed.nodes = nodes := by
        apply List.ext_getElem
        · simp [constructed, BoundedCircuitKeySource.toCircuit,
            boundedCircuitKeySourceOfCircuit]
        · intro index _hleft _hright
          simp [constructed, BoundedCircuitKeySource.toCircuit,
            boundedCircuitKeySourceOfCircuit]
      apply booleanCircuit_ext constructed
        { nodes := nodes
          output := output
          wellFormed := wellFormed } hnodes
      rfl

/-! ### Fixed structural description block -/

/-- False-first unary rank bits.  For values at most `limit`, ordinary list
lexicographic order is exactly numeric order, with no container-code order
leaking into C.12's SAT variables. -/
def orderedNatBits (limit value : ℕ) : List Bool :=
  (List.range limit).map fun index => decide (index < value)

@[simp] theorem orderedNatBits_length (limit value : ℕ) :
    (orderedNatBits limit value).length = limit := by
  simp [orderedNatBits]

def boundedCircuitFieldLimit (n bound : ℕ) : ℕ :=
  n + bound + 1

def boundedNodeDescriptionBits {n : ℕ} (bound : ℕ) :
    BooleanNode n → List Bool
  | .const value =>
      orderedNatBits 6 0 ++
        orderedNatBits (boundedCircuitFieldLimit n bound) value.toNat ++
        orderedNatBits (boundedCircuitFieldLimit n bound) 0
  | .input index =>
      orderedNatBits 6 1 ++
        orderedNatBits (boundedCircuitFieldLimit n bound) index.val ++
        orderedNatBits (boundedCircuitFieldLimit n bound) 0
  | .not child =>
      orderedNatBits 6 2 ++
        orderedNatBits (boundedCircuitFieldLimit n bound) child ++
        orderedNatBits (boundedCircuitFieldLimit n bound) 0
  | .and left right =>
      orderedNatBits 6 3 ++
        orderedNatBits (boundedCircuitFieldLimit n bound) left ++
        orderedNatBits (boundedCircuitFieldLimit n bound) right
  | .or left right =>
      orderedNatBits 6 4 ++
        orderedNatBits (boundedCircuitFieldLimit n bound) left ++
        orderedNatBits (boundedCircuitFieldLimit n bound) right

def boundedOutputDescriptionBits
    (n bound output : ℕ) : List Bool :=
  orderedNatBits 6 5 ++
    orderedNatBits (boundedCircuitFieldLimit n bound) output ++
    orderedNatBits (boundedCircuitFieldLimit n bound) 0

def boundedPaddingDescriptionBits
    (n bound : ℕ) : List Bool :=
  orderedNatBits 6 6 ++
    orderedNatBits (boundedCircuitFieldLimit n bound) 0 ++
    orderedNatBits (boundedCircuitFieldLimit n bound) 0

def boundedCircuitDescriptionWidth (n bound : ℕ) : ℕ :=
  (bound + 1) * (6 + 2 * boundedCircuitFieldLimit n bound)

/-- Direct decoder-order description: typed node rows, one output sentinel,
then padding sentinels.  A longer valid DAG compares before a shorter one at
the first node/output boundary, exactly as its structural field list does. -/
def canonicalBoundedCircuitDescription {n : ℕ}
    (bound : ℕ) (circuit : BooleanCircuit n) : List Bool :=
  ((circuit.nodes.map (boundedNodeDescriptionBits bound)) ++
      [boundedOutputDescriptionBits n bound circuit.output.val] ++
      List.replicate (bound - circuit.size)
        (boundedPaddingDescriptionBits n bound)).flatten

@[simp] theorem boundedNodeDescriptionBits_length {n bound : ℕ}
    (node : BooleanNode n) :
    (boundedNodeDescriptionBits bound node).length =
      6 + 2 * boundedCircuitFieldLimit n bound := by
  cases node <;> simp [boundedNodeDescriptionBits] <;> omega

@[simp] theorem boundedOutputDescriptionBits_length (n bound output : ℕ) :
    (boundedOutputDescriptionBits n bound output).length =
      6 + 2 * boundedCircuitFieldLimit n bound := by
  simp [boundedOutputDescriptionBits]
  omega

@[simp] theorem boundedPaddingDescriptionBits_length (n bound : ℕ) :
    (boundedPaddingDescriptionBits n bound).length =
      6 + 2 * boundedCircuitFieldLimit n bound := by
  simp [boundedPaddingDescriptionBits]
  omega

@[simp] theorem sum_nodeDescriptionLengths {n bound : ℕ}
    (nodes : List (BooleanNode n)) :
    (nodes.map
      (List.length ∘ boundedNodeDescriptionBits bound)).sum =
        nodes.length *
          (6 + 2 * boundedCircuitFieldLimit n bound) := by
  induction nodes with
  | nil =>
      simp
  | cons node rest ih =>
      simp only [List.map_cons, List.sum_cons, Function.comp_apply,
        boundedNodeDescriptionBits_length, List.length_cons, ih]
      ring

theorem canonicalBoundedCircuitDescription_length {n bound : ℕ}
    (circuit : BooleanCircuit n) (hsize : circuit.size ≤ bound) :
    (canonicalBoundedCircuitDescription bound circuit).length =
      boundedCircuitDescriptionWidth n bound := by
  have hlength : circuit.nodes.length ≤ bound := by
    simpa only [BooleanCircuit.size] using hsize
  simp only [canonicalBoundedCircuitDescription, List.length_flatten,
    List.map_append, List.sum_append, List.map_map,
    sum_nodeDescriptionLengths, List.map_singleton, List.sum_singleton,
    boundedOutputDescriptionBits_length, List.map_replicate,
    List.sum_replicate, nsmul_eq_mul,
    boundedPaddingDescriptionBits_length,
    boundedCircuitDescriptionWidth, BooleanCircuit.size]
  have hpartition :
      circuit.nodes.length + (bound - circuit.nodes.length) = bound :=
    Nat.add_sub_of_le hlength
  calc
    circuit.nodes.length *
          (6 + 2 * boundedCircuitFieldLimit n bound) +
        (6 + 2 * boundedCircuitFieldLimit n bound) +
        (bound - circuit.nodes.length) *
          (6 + 2 * boundedCircuitFieldLimit n bound) =
        (circuit.nodes.length + (bound - circuit.nodes.length) + 1) *
          (6 + 2 * boundedCircuitFieldLimit n bound) := by ring
    _ = (bound + 1) *
          (6 + 2 * boundedCircuitFieldLimit n bound) := by
      rw [hpartition]

theorem acceptsOracleCircuit_of_proof
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n)
    (proof : BitInput (2 ^ pcp.nativeWidth n))
    (hproof : ∀ randomness, pcp.accepts input proof randomness)
    (circuit : BooleanCircuit (pcp.nativeWidth n))
    (hcircuit : circuit.eval = proofFunction pcp proof) :
    ∀ randomness, acceptsOracleCircuit pcp input circuit randomness := by
  intro randomness
  unfold acceptsOracleCircuit
  rw [hcircuit]
  unfold proofFunction
  rw [show
    (fun query =>
      proof (binaryAddress (projectedInput pcp input randomness query))) =
    (fun query =>
      proof (binaryAddress fun bit =>
        (pcp.queryAddressBits input query bit).eval randomness)) by
      rfl]
  exact hproof randomness

/-- Perfect completeness plus failure of every small substituted oracle
circuit exposes an actual worst-case-hard proof function.  This is the
logical core of Appendix C's Case 1. -/
theorem existsWorstCaseHardProofFunction
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n size : ℕ}
    (input : BitInput n)
    (complete :
      ∃ proof, ∀ randomness, pcp.accepts input proof randomness)
    (noSmallAcceptingCircuit :
      ∀ circuit : BooleanCircuit (pcp.nativeWidth n),
        circuit.size ≤ size →
        ¬∀ randomness, acceptsOracleCircuit pcp input circuit randomness) :
    ∃ function : BoolFunction (pcp.nativeWidth n),
      WorstCaseHardAt function size := by
  rcases complete with ⟨proof, hproof⟩
  refine ⟨proofFunction pcp proof, ?_⟩
  intro circuit hsize
  by_contra hmatches
  have heval : circuit.eval = proofFunction pcp proof := by
    funext address
    exact not_ne_iff.mp (not_exists.mp hmatches address)
  exact
    (noSmallAcceptingCircuit circuit hsize)
      (acceptsOracleCircuit_of_proof pcp input proof hproof circuit heval)

/-- Case 1 applied after exact-width padding.  Completeness is transported
from the native PCP by the zero-face adapter before the circuit case split. -/
theorem existsWorstCaseHardPaddedProofFunction
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound)
    (paddedWidth : ℕ → ℕ)
    (hwidth : ∀ n, pcp.nativeWidth n ≤ paddedWidth n)
    {n size : ℕ} (input : BitInput n)
    (nativeComplete :
      ∃ proof, ∀ randomness, pcp.accepts input proof randomness)
    (noSmallAcceptingCircuit :
      ∀ circuit : BooleanCircuit (paddedWidth n),
        circuit.size ≤ size →
        ¬∀ randomness,
          acceptsOracleCircuit
            (padProjectionPCP pcp paddedWidth hwidth)
            input circuit randomness) :
    ∃ function : BoolFunction (paddedWidth n),
      WorstCaseHardAt function size := by
  exact
    existsWorstCaseHardProofFunction
      (padProjectionPCP pcp paddedWidth hwidth) input
      (padProjectionPCP_complete pcp paddedWidth hwidth input nativeComplete)
      noSmallAcceptingCircuit

/-- The zero-first truth table among perfectly accepting outer proofs.  The
order is the native `Fin` address order proved by
`boolFunctionTable_proofFunction`, exactly matching C.12's prefix variables. -/
structure CanonicalAcceptingProof
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) where
  proof : BitInput (2 ^ pcp.nativeWidth n)
  accepts : ∀ randomness, pcp.accepts input proof randomness
  minimal : ∀ candidate,
    (∀ randomness, pcp.accepts input candidate randomness) →
      CanonicalBoolListLE (List.ofFn proof) (List.ofFn candidate)

theorem existsCanonicalAcceptingProof
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n)
    (complete :
      ∃ proof, ∀ randomness, pcp.accepts input proof randomness) :
    Nonempty (CanonicalAcceptingProof pcp input) := by
  classical
  letI : LinearOrder (BitInput (2 ^ pcp.nativeWidth n)) :=
    LinearOrder.lift' List.ofFn List.ofFn_injective
  let eligible : Finset (BitInput (2 ^ pcp.nativeWidth n)) :=
    Finset.univ.filter fun proof =>
      ∀ randomness, pcp.accepts input proof randomness
  have heligible : eligible.Nonempty := by
    rcases complete with ⟨proof, haccepts⟩
    exact ⟨proof, by simp [eligible, haccepts]⟩
  let proof := eligible.min' heligible
  have haccepts : ∀ randomness, pcp.accepts input proof randomness := by
    have hmember := eligible.min'_mem heligible
    simpa only [eligible, Finset.mem_filter, Finset.mem_univ, true_and] using
      hmember
  refine
    ⟨{ proof := proof
       accepts := haccepts
       minimal := ?_ }⟩
  intro candidate hcandidate
  exact eligible.min'_le candidate (by simp [eligible, hcandidate])

/-- Direct Case-1 input extracted from the outer PCP and the fixed amplifier
witness.  No branch-builder or hard-function premise is accepted. -/
noncomputable def caseOneInputOfNoSmallAcceptingCircuit
    {machine : TimedDecisionMachine} {timeBound sizeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound)
    (amplifier : AmplifierWitness)
    (constructible : TimeConstructible sizeBound)
    {n : ℕ} (input : BitInput n)
    (complete :
      ∃ proof, ∀ randomness, pcp.accepts input proof randomness)
    (noSmallAcceptingCircuit :
      ∀ circuit : BooleanCircuit (pcp.nativeWidth n),
        circuit.size ≤ sizeBound (pcp.nativeWidth n) →
        ¬∀ randomness, acceptsOracleCircuit pcp input circuit randomness) :
    CaseOneInput amplifier := by
  let canonical :=
    Classical.choice (existsCanonicalAcceptingProof pcp input complete)
  have hard :
      WorstCaseHardAt (proofFunction pcp canonical.proof)
        (sizeBound (pcp.nativeWidth n)) := by
    intro circuit hsize
    by_contra hmatches
    have heval :
        circuit.eval = proofFunction pcp canonical.proof := by
      funext address
      exact not_ne_iff.mp (not_exists.mp hmatches address)
    exact
      (noSmallAcceptingCircuit circuit hsize)
        (acceptsOracleCircuit_of_proof pcp input canonical.proof
          canonical.accepts circuit heval)
  exact
    { sizeBound := sizeBound
      constructible := constructible
      seedArity := pcp.nativeWidth n
      seed := proofFunction pcp canonical.proof
      worstCaseHard := hard }

/-! ## Canonical representatives for executable recovery -/

/-- The zero-first typed description among small oracle circuits accepting
every outer row.  The fixed row block is the exact C.12 SAT-variable order;
numeric container encodings play no role in selection. -/
structure CanonicalAcceptingOracle
    {machine : TimedDecisionMachine} {timeBound sizeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) where
  circuit : BooleanCircuit (pcp.nativeWidth n)
  sizeBounded : circuit.size ≤ sizeBound (pcp.nativeWidth n)
  accepts : ∀ randomness,
    acceptsOracleCircuit pcp input circuit randomness
  minimal : ∀ candidate : BooleanCircuit (pcp.nativeWidth n),
    candidate.size ≤ sizeBound (pcp.nativeWidth n) →
      (∀ randomness,
        acceptsOracleCircuit pcp input candidate randomness) →
      canonicalBoundedCircuitDescription
          (sizeBound (pcp.nativeWidth n)) circuit ≤
        canonicalBoundedCircuitDescription
          (sizeBound (pcp.nativeWidth n)) candidate

theorem existsCanonicalAcceptingOracle
    {machine : TimedDecisionMachine} {timeBound sizeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n)
    (existsSmall :
      ∃ circuit : BooleanCircuit (pcp.nativeWidth n),
        circuit.size ≤ sizeBound (pcp.nativeWidth n) ∧
          ∀ randomness,
            acceptsOracleCircuit pcp input circuit randomness) :
    Nonempty
      (CanonicalAcceptingOracle (sizeBound := sizeBound) pcp input) := by
  classical
  let bound := sizeBound (pcp.nativeWidth n)
  let candidateDescriptions : Finset (List Bool) :=
    Finset.univ.image
      (fun source : BoundedCircuitKeySource (pcp.nativeWidth n) bound =>
        canonicalBoundedCircuitDescription bound source.toCircuit)
  have description_mem_candidates
      (circuit : BooleanCircuit (pcp.nativeWidth n))
      (hsize : circuit.size ≤ bound) :
      canonicalBoundedCircuitDescription bound circuit ∈
        candidateDescriptions := by
    apply Finset.mem_image.mpr
    refine
      ⟨boundedCircuitKeySourceOfCircuit circuit hsize,
        Finset.mem_univ _, ?_⟩
    rw [boundedCircuitKeySource_toCircuit_ofCircuit]
  let eligibleDescriptions : Finset (List Bool) :=
    candidateDescriptions.filter fun description =>
      ∃ circuit : BooleanCircuit (pcp.nativeWidth n),
        circuit.size ≤ bound ∧
          (∀ randomness,
            acceptsOracleCircuit pcp input circuit randomness) ∧
          canonicalBoundedCircuitDescription bound circuit =
            description
  have heligible : eligibleDescriptions.Nonempty := by
    rcases existsSmall with ⟨circuit, hsize, haccepts⟩
    refine
      ⟨canonicalBoundedCircuitDescription bound circuit, ?_⟩
    apply Finset.mem_filter.mpr
    exact
      ⟨description_mem_candidates circuit hsize,
        circuit, hsize, haccepts, rfl⟩
  let selectedDescription := eligibleDescriptions.min' heligible
  have hselected := eligibleDescriptions.min'_mem heligible
  have hselectedSpec := (Finset.mem_filter.mp hselected).2
  rcases hselectedSpec with
    ⟨circuit, hsize, haccepts, hdescription⟩
  refine
    ⟨{ circuit := circuit
       sizeBounded := hsize
       accepts := haccepts
       minimal := ?_ }⟩
  intro candidate hcandidateSize hcandidateAccepts
  rw [hdescription]
  apply eligibleDescriptions.min'_le
  apply Finset.mem_filter.mpr
  exact
    ⟨description_mem_candidates candidate hcandidateSize,
      candidate, hcandidateSize, hcandidateAccepts, rfl⟩

/-- The genuine outer-oracle split.  In Case 1 the chosen complete proof is
worst-case hard and is packaged for amplification; in Case 2 the same small
oracle circuit accepts every outer-verifier row. -/
inductive OuterOracleCase
    {machine : TimedDecisionMachine} {timeBound sizeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound)
    (amplifier : AmplifierWitness) {n : ℕ} (input : BitInput n) where
  | caseOne :
      CaseOneInput amplifier →
      OuterOracleCase pcp amplifier input
  | caseTwo :
      CanonicalAcceptingOracle (sizeBound := sizeBound) pcp input →
      OuterOracleCase pcp amplifier input

/-- Perfect completeness decides the Case-1/Case-2 split without a
caller-supplied branch theorem. -/
theorem existsOuterOracleCase
    {machine : TimedDecisionMachine} {timeBound sizeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound)
    (amplifier : AmplifierWitness)
    (constructible : TimeConstructible sizeBound)
    {n : ℕ} (input : BitInput n)
    (complete :
      ∃ proof, ∀ randomness, pcp.accepts input proof randomness) :
    Nonempty
      (OuterOracleCase (sizeBound := sizeBound) pcp amplifier input) := by
  classical
  by_cases hsmall :
      ∃ circuit : BooleanCircuit (pcp.nativeWidth n),
        circuit.size ≤ sizeBound (pcp.nativeWidth n) ∧
          ∀ randomness,
            acceptsOracleCircuit pcp input circuit randomness
  · rcases hsmall with ⟨circuit, hsize, haccepts⟩
    exact
      ⟨.caseTwo <| Classical.choice <|
        existsCanonicalAcceptingOracle pcp input
          ⟨circuit, hsize, haccepts⟩⟩
  · have hno :
        ∀ circuit : BooleanCircuit (pcp.nativeWidth n),
          circuit.size ≤ sizeBound (pcp.nativeWidth n) →
          ¬∀ randomness,
            acceptsOracleCircuit pcp input circuit randomness := by
      intro circuit hsize haccepts
      exact hsmall ⟨circuit, hsize, haccepts⟩
    exact
      ⟨.caseOne
        (caseOneInputOfNoSmallAcceptingCircuit pcp amplifier constructible
          input complete hno)⟩

/-! ## Genuine hierarchy-PCP instantiation -/

/-- The outer PCP attached to the timed hierarchy machine returned by the
fixed-refuter source.  Its runner bounds and semantic guarantees are retained
for the weak-machine and resource ledgers. -/
structure HierarchyOuterPCP {bound : ℕ → ℕ}
    (source : ExecutableRefuterSource bound) where
  runnerDegree : ℕ
  queryExponent : ℕ
  substitutionExponent : ℕ
  pcp : ExecutableProjectionPCP source.hierarchyMachine bound
  proofExponent : ℕ
  substitution : ExecutableProjectionSubstitution pcp
  shapeDegree : pcp.shape.degree ≤ runnerDegree
  queryDegree : pcp.query.degree ≤ runnerDegree
  decisionDegree : pcp.decisionRunner.degree ≤ runnerDegree
  substitutionDegree : substitution.runner.degree ≤ runnerDegree
  queryCountBound : ∀ n, pcp.queryCount n ≤ pcp.shape.budget n
  compactQueryCountBound : ∀ n,
    pcp.queryCount n ≤
      pcp.shape.coefficient *
        (pcp.nativeWidth n + 1) ^ queryExponent
  decisionLengthBound : ∀ n input randomness,
    (pcp.decision (n := n) input randomness).clauses.length ≤
      pcp.decisionRunner.budget (pcp.decisionRequest input randomness)
  proofSizeBound : ∀ n,
    2 ^ pcp.nativeWidth n ≤
      pcp.shape.coefficient * bound n *
        logScale (bound n) ^ proofExponent
  substitutionSizeBound : ∀ request,
    (substitution.circuit request).size ≤
      substitution.sizeCoefficient *
        (pcp.nativeWidth request.inputArity +
          request.oracle.size + 1) ^ substitutionExponent
  complete : ∀ n input, source.hierarchyMachine.accepts n input →
    ∃ proof, ∀ randomness,
      pcp.toSemantic.accepts input proof randomness
  sound : ∀ n input, ¬source.hierarchyMachine.accepts n input →
    ∀ proof, pcp.toSemantic.acceptanceFraction input proof ≤
      1 / ((n + 1 : ℕ) : ℝ) ^ 10

/-- The outer artifact retains the exact pre-source exponents rather than
merely some source-dependent values satisfying the same inequalities. -/
def HierarchyOuterPCP.MatchesUniformSource
    {bound : ℕ → ℕ} {source : ExecutableRefuterSource bound}
    (outer : HierarchyOuterPCP source)
    (projection : UniformProjectionPCPSource) : Prop :=
  outer.runnerDegree = projection.runnerDegree ∧
    outer.queryExponent = projection.queryExponent ∧
    outer.substitutionExponent = projection.substitutionExponent

/-- Extract the uniform runner degree before applying the source factory, then
instantiate it only on `source.hierarchyMachine` through the canonical
`hierarchyProjectionPCP` theorem. -/
theorem existsHierarchyOuterPCP
    {bound : ℕ → ℕ} (admissible : RefuterClockAdmissible bound)
    (source : ExecutableRefuterSource bound)
    (projection : UniformProjectionPCPSource) :
    Nonempty
      { outer : HierarchyOuterPCP source //
        outer.MatchesUniformSource projection } := by
  rcases hierarchyProjectionPCP admissible source projection with
    ⟨pcp, proofExponent, substitution, hshape, hquery, hdecision, hsubstitution,
      hqueryCount, hcompactQueryCount, hdecisionLength, hproofSize,
      hsubstitutionSize, hcomplete, hsound⟩
  let outer : HierarchyOuterPCP source :=
    { runnerDegree := projection.runnerDegree
      queryExponent := projection.queryExponent
      substitutionExponent := projection.substitutionExponent
      pcp := pcp
      proofExponent := proofExponent
      substitution := substitution
      shapeDegree := hshape
      queryDegree := hquery
      decisionDegree := hdecision
      substitutionDegree := hsubstitution
      queryCountBound := hqueryCount
      compactQueryCountBound := hcompactQueryCount
      decisionLengthBound := hdecisionLength
      proofSizeBound := hproofSize
      substitutionSizeBound := hsubstitutionSize
      complete := hcomplete
      sound := hsound }
  refine ⟨⟨outer, ?_⟩⟩
  unfold HierarchyOuterPCP.MatchesUniformSource
  dsimp [outer]
  exact ⟨rfl, rfl, rfl⟩

/-- On a hierarchy YES word, the genuine hierarchy PCP produces the
Case-1/Case-2 split directly. -/
theorem HierarchyOuterPCP.existsOuterCase
    {bound sizeBound : ℕ → ℕ} {source : ExecutableRefuterSource bound}
    (outer : HierarchyOuterPCP source)
    (amplifier : AmplifierWitness)
    (constructible : TimeConstructible sizeBound)
    {n : ℕ} (input : BitInput n)
    (hyes : source.hierarchyMachine.accepts n input) :
    Nonempty
      (OuterOracleCase (sizeBound := sizeBound)
        outer.pcp.toSemantic amplifier input) :=
  existsOuterOracleCase outer.pcp.toSemantic amplifier constructible input
    (outer.complete n input hyes)

/-- The executable compact substituted verifier for one outer input and
candidate oracle circuit. -/
def HierarchyOuterPCP.substitutedCircuit
    {bound : ℕ → ℕ} {source : ExecutableRefuterSource bound}
    (outer : HierarchyOuterPCP source) {n : ℕ}
    (input : BitInput n)
    (oracle : BooleanCircuit (outer.pcp.nativeWidth n)) :
    BooleanCircuit (outer.pcp.nativeWidth n) :=
  outer.substitution.circuit
    { inputArity := n, input := input, oracle := oracle }

/-- Add only the unreachable nodes needed by the pointwise-PCPP size
precondition. -/
def HierarchyOuterPCP.pcppCircuit
    {bound : ℕ → ℕ} {source : ExecutableRefuterSource bound}
    (outer : HierarchyOuterPCP source) {n : ℕ}
    (input : BitInput n)
    (oracle : BooleanCircuit (outer.pcp.nativeWidth n)) :
    BooleanCircuit (outer.pcp.nativeWidth n) :=
  (outer.substitutedCircuit input oracle).padToArity

theorem HierarchyOuterPCP.pcppCircuit_eval
    {bound : ℕ → ℕ} {source : ExecutableRefuterSource bound}
    (outer : HierarchyOuterPCP source) {n : ℕ}
    (input : BitInput n)
    (oracle : BooleanCircuit (outer.pcp.nativeWidth n))
    (randomness : BitInput (outer.pcp.nativeWidth n)) :
    (outer.pcppCircuit input oracle).eval randomness =
      acceptsOracleCircuit outer.pcp.toSemantic
        input oracle randomness := by
  rw [HierarchyOuterPCP.pcppCircuit,
    BooleanCircuit.padToArity_eval]
  exact outer.substitution.equivalent
    { inputArity := n, input := input, oracle := oracle } randomness

theorem HierarchyOuterPCP.pcppCircuit_arity_le_size
    {bound : ℕ → ℕ} {source : ExecutableRefuterSource bound}
    (outer : HierarchyOuterPCP source) {n : ℕ}
    (input : BitInput n)
    (oracle : BooleanCircuit (outer.pcp.nativeWidth n)) :
    outer.pcp.nativeWidth n ≤
      (outer.pcppCircuit input oracle).size :=
  BooleanCircuit.arity_le_padToArity_size _

theorem HierarchyOuterPCP.pcppCircuit_size_bound
    {bound : ℕ → ℕ} {source : ExecutableRefuterSource bound}
    (outer : HierarchyOuterPCP source) {n : ℕ}
    (input : BitInput n)
    (oracle : BooleanCircuit (outer.pcp.nativeWidth n)) :
    (outer.pcppCircuit input oracle).size ≤
      outer.substitution.sizeCoefficient *
          (outer.pcp.nativeWidth n + oracle.size + 1) ^
            outer.substitutionExponent +
        outer.pcp.nativeWidth n := by
  apply (BooleanCircuit.padToArity_size_le _).trans
  exact Nat.add_le_add_right
    (outer.substitutionSizeBound
      ({ inputArity := n, input := input, oracle := oracle } :
        ProjectionSubstitutionRequest outer.pcp))
    (outer.pcp.nativeWidth n)

/-! ## Canonical Case-2 honest table -/

/-- The first block of an occurrence-table input is the PCPP input. -/
def occurrenceInput {inputArity clauseBits : ℕ}
    (input : BitInput (inputArity + clauseBits + 1)) :
    BitInput inputArity :=
  fun index => input ⟨index.val, by omega⟩

/-- The second block is the power-of-two clause address. -/
def occurrenceClauseAddress {inputArity clauseBits : ℕ}
    (input : BitInput (inputArity + clauseBits + 1)) :
    BitInput clauseBits :=
  fun index => input ⟨inputArity + index.val, by omega⟩

/-- The final bit selects the left or right literal occurrence. -/
def occurrencePosition {inputArity clauseBits : ℕ}
    (input : BitInput (inputArity + clauseBits + 1)) : Bool :=
  input ⟨inputArity + clauseBits, by omega⟩

/-- Project a branch-independent occurrence address onto the native PCPP
layout.  Extra clause-address bits are ignored, while the position bit is
taken from the end of the padded layout rather than accidentally shifted into
the native clause-address block. -/
def projectPaddedOccurrenceInput
    {inputArity nativeClauseBits paddedClauseBits : ℕ}
    (hclause : nativeClauseBits ≤ paddedClauseBits)
    (input : BitInput (inputArity + paddedClauseBits + 1)) :
    BitInput (inputArity + nativeClauseBits + 1) :=
  fun index =>
    if hprefix : index.val < inputArity + nativeClauseBits then
      input ⟨index.val, by omega⟩
    else
      input ⟨inputArity + paddedClauseBits, by omega⟩

@[simp] theorem projectPaddedOccurrenceInput_prefix
    {inputArity nativeClauseBits paddedClauseBits : ℕ}
    (hclause : nativeClauseBits ≤ paddedClauseBits)
    (input : BitInput (inputArity + paddedClauseBits + 1))
    (index : Fin (inputArity + nativeClauseBits))
    (hindex : index.val < inputArity + nativeClauseBits) :
    projectPaddedOccurrenceInput hclause input
        ⟨index.val, by omega⟩ =
      input ⟨index.val, by omega⟩ := by
  simp [projectPaddedOccurrenceInput, hindex]

@[simp] theorem projectPaddedOccurrenceInput_position
    {inputArity nativeClauseBits paddedClauseBits : ℕ}
    (hclause : nativeClauseBits ≤ paddedClauseBits)
    (input : BitInput (inputArity + paddedClauseBits + 1)) :
    projectPaddedOccurrenceInput hclause input
        ⟨inputArity + nativeClauseBits, by omega⟩ =
      input ⟨inputArity + paddedClauseBits, by omega⟩ := by
  simp [projectPaddedOccurrenceInput]

/-- The source PCPP's deterministic honest assignment, flattened by indexed
clause occurrence.  Both circuit classes later analyze this same function. -/
noncomputable def honestOccurrenceFunction
    {n : ℕ} {circuit : BooleanCircuit n}
    (pcpp : PointwisePCPP circuit) :
    BoolFunction (n + pcpp.clauseBits + 1) :=
  fun encoded =>
    let input := occurrenceInput encoded
    let clause :=
      pcpp.clauses (binaryAddress (occurrenceClauseAddress encoded))
    let literal := if occurrencePosition encoded then clause.right else clause.left
    literal.eval (pcpp.assignment input (pcpp.honestAuxiliary input))

/-- Repeat the native occurrence table over every added high clause-address
suffix.  This is the branch-independent table used by scheduling: it changes
neither the selected native clause nor its left/right occurrence. -/
noncomputable def paddedHonestOccurrenceFunction
    {n : ℕ} {circuit : BooleanCircuit n}
    (pcpp : PointwisePCPP circuit) (paddedClauseBits : ℕ)
    (hclause : pcpp.clauseBits ≤ paddedClauseBits) :
    BoolFunction (n + paddedClauseBits + 1) :=
  fun input =>
    honestOccurrenceFunction pcpp
      (projectPaddedOccurrenceInput hclause input)

theorem paddedHonestOccurrenceFunction_eq_native
    {n : ℕ} {circuit : BooleanCircuit n}
    (pcpp : PointwisePCPP circuit) :
    paddedHonestOccurrenceFunction pcpp pcpp.clauseBits le_rfl =
      honestOccurrenceFunction pcpp := by
  funext input
  apply congrArg (honestOccurrenceFunction pcpp)
  funext index
  by_cases hprefix : index.val < n + pcpp.clauseBits
  · simp [projectPaddedOccurrenceInput, hprefix]
  · have hposition : index.val = n + pcpp.clauseBits := by
      omega
    simp only [projectPaddedOccurrenceInput, hprefix]
    apply congrArg input
    exact Fin.ext_iff.mpr hposition.symm

/-- All data in the Case-2 proof table comes from the executable pointwise
PCPP contract.  The stored semantic PCPP is definitionally the executable
one's interpretation, and `honestComplete` is its imported completeness
guarantee for the accepted substituted circuit. -/
structure HonestPCPPTable {n : ℕ} (circuit : BooleanCircuit n) where
  completeness : ℝ
  soundness : ℝ
  gap : soundness < completeness
  coefficient : ℕ
  degree : ℕ
  runnerDegree : ℕ
  coefficientPositive : 0 < coefficient
  executable : ExecutablePointwisePCPP circuit
  supportBound :
    ∀ i, (executable.systematicSupport i).card ≤ n / 2
  shapeDegree : executable.shape.degree ≤ runnerDegree
  supportDegree : executable.supportRunner.degree ≤ runnerDegree
  clauseDegree : executable.clauseRunner.degree ≤ runnerDegree
  honestDegree : executable.honestRunner.degree ≤ runnerDegree
  descriptionBound :
    executable.systematicBits + executable.auxiliaryBits +
        executable.clauseBits ≤
      executable.shape.budget ()
  clauseCountBound :
    2 ^ executable.clauseBits ≤
      coefficient * (circuit.size + 1) ^ degree
  constructionBound :
    (executable.toSemantic supportBound).constructionSteps ≤
      coefficient * (circuit.size + 1) ^ degree
  honestComplete : ∀ input, circuit.eval input →
    (executable.toSemantic supportBound).satisfiedFraction input
        ((executable.toSemantic supportBound).honestAuxiliary input) ≥
      completeness
  rejectSound : ∀ input, ¬circuit.eval input →
    ∀ auxiliary,
      (executable.toSemantic supportBound).satisfiedFraction input auxiliary ≤
        soundness
  honestStepsBound : ∀ input,
    (executable.toSemantic supportBound).honestSteps input ≤
      coefficient * (circuit.size + 1) ^ degree

def HonestPCPPTable.semantic {n : ℕ} {circuit : BooleanCircuit n}
    (table : HonestPCPPTable circuit) : PointwisePCPP circuit :=
  table.executable.toSemantic table.supportBound

noncomputable def HonestPCPPTable.function
    {n : ℕ} {circuit : BooleanCircuit n}
    (table : HonestPCPPTable circuit) :
    BoolFunction (n + table.semantic.clauseBits + 1) :=
  honestOccurrenceFunction table.semantic

/-- The Case-2 table is chosen before the class tag.  If either legal
componentwise approximation would make the fixed union machine accept the
same refuter word, rejection produces the two literal XOR premises for this
single honest table. -/
noncomputable def HonestPCPPTable.commonXorInputOfMachineRejection
    {n : ℕ} {circuit : BooleanCircuit n}
    (table : HonestPCPPTable circuit)
    (xorWitness : XorAmplificationWitness)
    (copies symmetricSize thresholdSize : ℕ) (delta : ℝ)
    (deltaNonnegative : 0 ≤ delta)
    (deltaBelowHalf : delta < 1 / 2)
    (copiesPositive : 1 ≤ copies)
    (machine : ExecutableWeakNondeterministicMachine)
    {inputArity : ℕ} (input : BitInput inputArity)
    (acceptsOfApproximation :
      HasEitherLegalApproximation symmetricWireFamily thresholdWireFamily
        table.function
        symmetricSize
          ⌈xorWitness.termCoefficient delta *
              ((n + table.semantic.clauseBits + 1 : ℕ) : ℝ) /
            xorEpsilon delta copies ^ 2⌉₊
          (xorCoefficientBitBound xorWitness.coefficientBitCoefficient
            xorWitness.coefficientBitDegree delta
            (n + table.semantic.clauseBits + 1))
        thresholdSize
          ⌈xorWitness.termCoefficient delta *
              ((n + table.semantic.clauseBits + 1 : ℕ) : ℝ) /
            xorEpsilon delta copies ^ 2⌉₊
          (xorCoefficientBitBound xorWitness.coefficientBitCoefficient
            xorWitness.coefficientBitDegree delta
            (n + table.semantic.clauseBits + 1))
        (xorWitness.massCoefficient delta / xorEpsilon delta copies)
        (xorWitness.massCoefficient delta / xorEpsilon delta copies)
        delta →
      machine.toSemantic.accepts input)
    (rejects : ¬machine.toSemantic.accepts input) :
    CommonXorInput xorWitness symmetricWireFamily thresholdWireFamily :=
  ComponentwiseTransfer.commonXorInputOfMachineRejection
    xorWitness table.function copies
    symmetricSize thresholdSize delta deltaNonnegative deltaBelowHalf
    copiesPositive machine input acceptsOfApproximation rejects

/-- Apply CLW XOR amplification immediately after the common Case-2 rejection
argument, retaining one truth table for both physical circuit families. -/
noncomputable def HonestPCPPTable.commonHardCoreOfMachineRejection
    {n : ℕ} {circuit : BooleanCircuit n}
    (table : HonestPCPPTable circuit)
    (xorWitness : XorAmplificationWitness)
    (copies symmetricSize thresholdSize : ℕ) (delta : ℝ)
    (deltaNonnegative : 0 ≤ delta)
    (deltaBelowHalf : delta < 1 / 2)
    (copiesPositive : 1 ≤ copies)
    (machine : ExecutableWeakNondeterministicMachine)
    {inputArity : ℕ} (input : BitInput inputArity)
    (acceptsOfApproximation :
      HasEitherLegalApproximation symmetricWireFamily thresholdWireFamily
        table.function
        symmetricSize
          ⌈xorWitness.termCoefficient delta *
              ((n + table.semantic.clauseBits + 1 : ℕ) : ℝ) /
            xorEpsilon delta copies ^ 2⌉₊
          (xorCoefficientBitBound xorWitness.coefficientBitCoefficient
            xorWitness.coefficientBitDegree delta
            (n + table.semantic.clauseBits + 1))
        thresholdSize
          ⌈xorWitness.termCoefficient delta *
              ((n + table.semantic.clauseBits + 1 : ℕ) : ℝ) /
            xorEpsilon delta copies ^ 2⌉₊
          (xorCoefficientBitBound xorWitness.coefficientBitCoefficient
            xorWitness.coefficientBitDegree delta
            (n + table.semantic.clauseBits + 1))
        (xorWitness.massCoefficient delta / xorEpsilon delta copies)
        (xorWitness.massCoefficient delta / xorEpsilon delta copies)
        delta →
      machine.toSemantic.accepts input)
    (rejects : ¬machine.toSemantic.accepts input) :
    CommonHardCore symmetricWireFamily thresholdWireFamily :=
  commonHardCoreFromXor
    (table.commonXorInputOfMachineRejection xorWitness copies
      symmetricSize thresholdSize delta deltaNonnegative deltaBelowHalf
      copiesPositive machine input acceptsOfApproximation rejects)
    symmetricWireFamily_restrictionClosed.toSourceFamily
    thresholdWireFamily_restrictionClosed.toSourceFamily
    symmetricWireFamily_negationClosed
    thresholdWireFamily_negationClosed

/-- Instantiate the one fixed executable PCPP factory on an accepted outer
oracle circuit.  This closes the object-construction half of Appendix C's
Case 2 while retaining the factory chosen before the circuit. -/
theorem existsHonestPCPPTableOfSource
    (source : UniformPointwisePCPPSource)
    {n : ℕ} (circuit : BooleanCircuit n) (hsize : n ≤ circuit.size) :
    Nonempty (HonestPCPPTable circuit) := by
  let pcpp := source.factory.forCircuit circuit
  rcases source.guarantee circuit hsize with
    ⟨supportBound, hshape, hsupport, hclause, hhonest,
      hdescription, hclauseCount, hconstruction, hcomplete, hsound,
      hhonestSteps⟩
  exact
    ⟨{ completeness := source.completeness
       soundness := source.soundness
       gap := source.gap
       coefficient := source.coefficient
       degree := source.degree
       runnerDegree := source.runnerDegree
       coefficientPositive := source.coefficientPositive
       executable := pcpp
       supportBound := supportBound
       shapeDegree := hshape
       supportDegree := hsupport
       clauseDegree := hclause
       honestDegree := hhonest
       descriptionBound := hdescription
       clauseCountBound := hclauseCount
       constructionBound := hconstruction
       honestComplete := hcomplete
       rejectSound := hsound
       honestStepsBound := hhonestSteps }⟩

/-- Instantiate the pointwise PCPP on the compact, minimally size-padded
substituted verifier circuit. -/
theorem HierarchyOuterPCP.existsHonestTableOfSource
    {bound : ℕ → ℕ} {source : ExecutableRefuterSource bound}
    (outer : HierarchyOuterPCP source)
    (pcppSource : UniformPointwisePCPPSource)
    {n : ℕ} (input : BitInput n)
    (oracle : BooleanCircuit (outer.pcp.nativeWidth n)) :
    Nonempty (HonestPCPPTable (outer.pcppCircuit input oracle)) :=
  existsHonestPCPPTableOfSource pcppSource
    (outer.pcppCircuit input oracle)
    (outer.pcppCircuit_arity_le_size input oracle)

theorem HierarchyOuterPCP.pcppCircuit_accepts
    {bound : ℕ → ℕ} {source : ExecutableRefuterSource bound}
    (outer : HierarchyOuterPCP source)
    {n : ℕ} (input : BitInput n)
    (oracle : BooleanCircuit (outer.pcp.nativeWidth n))
    (accepts : ∀ randomness,
      acceptsOracleCircuit outer.pcp.toSemantic
        input oracle randomness) :
    ∀ randomness,
      (outer.pcppCircuit input oracle).eval randomness := by
  intro randomness
  rw [outer.pcppCircuit_eval input oracle randomness]
  exact accepts randomness

theorem HierarchyOuterPCP.honestTable_complete
    {bound : ℕ → ℕ} {source : ExecutableRefuterSource bound}
    (outer : HierarchyOuterPCP source)
    {n : ℕ} (input : BitInput n)
    (oracle : BooleanCircuit (outer.pcp.nativeWidth n))
    (table : HonestPCPPTable (outer.pcppCircuit input oracle))
    (accepts : ∀ randomness,
      acceptsOracleCircuit outer.pcp.toSemantic
        input oracle randomness) :
    ∀ randomness,
      table.semantic.satisfiedFraction randomness
          (table.semantic.honestAuxiliary randomness) ≥
        table.completeness := by
  intro randomness
  exact table.honestComplete randomness
    (outer.pcppCircuit_accepts input oracle accepts randomness)

end NearCubicWires.OuterPCPRecovery
