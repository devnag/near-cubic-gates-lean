import Proof.Foundations.CircuitRestriction

/-!
# Exact padding of the Case-1 Boolean hard core

The worst-case amplifier may return fewer variables than the branch-independent
XOR schedule reserves.  This module restricts ordinary Boolean DAGs after
fixing the added coordinates, proves that gate count is unchanged, and applies
the common padding theorem.  Consequently the Case-1 core can be extended to
the exact scheduled arity without assuming the amplifier's hidden arity
constant is one.
-/

namespace NearCubicWires.CaseOnePadding

open NearCubicWires
open NearCubicWires.CircuitRestriction
open NearCubicWires.ComponentwiseTransfer
open NearCubicWires.RecoveryPipeline

def restrictBooleanNode {core target : ℕ} (hcore : core ≤ target)
    (padding : BitInput (target - core)) :
    BooleanNode target → BooleanNode core
  | .const value => .const value
  | .input index =>
      match (finSplitEquiv hcore).symm index with
      | .inl coreIndex => .input coreIndex
      | .inr paddingIndex => .const (padding paddingIndex)
  | .not child => .not child
  | .and left right => .and left right
  | .or left right => .or left right

theorem restrictBooleanNode_wellFormed
    {core target index : ℕ} (hcore : core ≤ target)
    (padding : BitInput (target - core)) (node : BooleanNode target)
    (hnode : node.WellFormedAt index) :
    (restrictBooleanNode hcore padding node).WellFormedAt index := by
  cases node with
  | const value =>
      trivial
  | input inputIndex =>
      simp only [restrictBooleanNode]
      split <;> trivial
  | not child =>
      exact hnode
  | and left right =>
      exact hnode
  | or left right =>
      exact hnode

theorem restrictBooleanNode_eval
    {core target : ℕ} (hcore : core ≤ target)
    (padding : BitInput (target - core)) (input : BitInput core)
    (prior : Array Bool) (node : BooleanNode target) :
    (restrictBooleanNode hcore padding node).eval input prior =
      node.eval
        (fun index =>
          Sum.elim input padding ((finSplitEquiv hcore).symm index))
        prior := by
  cases node with
  | const value =>
      rfl
  | input index =>
      cases hsplit : (finSplitEquiv hcore).symm index with
      | inl coreIndex =>
          simp [restrictBooleanNode, hsplit, BooleanNode.eval]
      | inr paddingIndex =>
          simp [restrictBooleanNode, hsplit, BooleanNode.eval]
  | not child =>
      rfl
  | and left right =>
      rfl
  | or left right =>
      rfl

def restrictBooleanCircuit {core target : ℕ}
    (circuit : BooleanCircuit target) (hcore : core ≤ target)
    (padding : BitInput (target - core)) : BooleanCircuit core where
  nodes := circuit.nodes.map (restrictBooleanNode hcore padding)
  output :=
    ⟨circuit.output.val, by
      simpa only [List.length_map] using circuit.output.isLt⟩
  wellFormed := by
    intro index
    let sourceIndex : Fin circuit.nodes.length :=
      ⟨index.val, by simpa using index.isLt⟩
    have hsource := circuit.wellFormed sourceIndex
    change
      ((circuit.nodes.map (restrictBooleanNode hcore padding)).get index)
          |>.WellFormedAt index.val
    simp only [List.get_eq_getElem, List.getElem_map]
    exact restrictBooleanNode_wellFormed hcore padding
      (circuit.nodes.get sourceIndex) hsource

private theorem foldl_restrictBooleanNode
    {core target : ℕ} (hcore : core ≤ target)
    (padding : BitInput (target - core)) (input : BitInput core)
    (nodes : List (BooleanNode target)) (prior : Array Bool) :
    (nodes.map (restrictBooleanNode hcore padding)).foldl
        (fun values node => values.push (node.eval input values)) prior =
      nodes.foldl
        (fun values node =>
          values.push
            (node.eval
              (fun index =>
                Sum.elim input padding ((finSplitEquiv hcore).symm index))
              values))
        prior := by
  induction nodes generalizing prior with
  | nil =>
      rfl
  | cons node nodes ih =>
      simp only [List.map_cons, List.foldl_cons]
      rw [restrictBooleanNode_eval]
      exact ih _

theorem restrictBooleanCircuit_values
    {core target : ℕ} (circuit : BooleanCircuit target)
    (hcore : core ≤ target) (padding : BitInput (target - core))
    (input : BitInput core) :
    (restrictBooleanCircuit circuit hcore padding).values input =
      circuit.values
        (fun index =>
          Sum.elim input padding ((finSplitEquiv hcore).symm index)) := by
  unfold BooleanCircuit.values restrictBooleanCircuit
  exact foldl_restrictBooleanNode hcore padding input circuit.nodes #[]

theorem restrictBooleanCircuit_eval
    {core target : ℕ} (circuit : BooleanCircuit target)
    (hcore : core ≤ target) (padding : BitInput (target - core))
    (input : BitInput core) :
    (restrictBooleanCircuit circuit hcore padding).eval input =
      circuit.eval
        (fun index =>
          Sum.elim input padding ((finSplitEquiv hcore).symm index)) := by
  unfold BooleanCircuit.eval
  rw [restrictBooleanCircuit_values]
  rfl

@[simp] theorem restrictBooleanCircuit_size
    {core target : ℕ} (circuit : BooleanCircuit target)
    (hcore : core ≤ target) (padding : BitInput (target - core)) :
    (restrictBooleanCircuit circuit hcore padding).size = circuit.size := by
  simp [BooleanCircuit.size, restrictBooleanCircuit]

theorem booleanCircuitFamily_restrictionClosed :
    RestrictionClosed booleanCircuitFamily := by
  intro core target size candidate hcore hcandidate padding
  rcases hcandidate with ⟨circuit, hsize, heval⟩
  refine ⟨restrictBooleanCircuit circuit hcore padding, ?_, ?_⟩
  · simpa using hsize
  · funext input
    rw [restrictBooleanCircuit_eval]
    rw [heval]
    rfl

/-- Extend a Case-1 amplifier output to the exact shared branch arity.  Size
and advantage are definitionally unchanged; only ignored variables are added. -/
noncomputable def paddedCaseOneHardCore
    {witness : AmplifierWitness} (input : CaseOneInput witness)
    (target : ℕ) (hcore : (hardCoreFromCaseOne input).arity ≤ target) :
    HardCore booleanCircuitFamily where
  arity := target
  function := padCore (hardCoreFromCaseOne input).function hcore
  size := (hardCoreFromCaseOne input).size
  advantage := (hardCoreFromCaseOne input).advantage
  hard :=
    averageHard_padCore
      (family := booleanCircuitFamily)
      (size := (hardCoreFromCaseOne input).size)
      (function := (hardCoreFromCaseOne input).function)
      (advantage := (hardCoreFromCaseOne input).advantage)
      booleanCircuitFamily_restrictionClosed
      (hardCoreFromCaseOne input).hard hcore

@[simp] theorem paddedCaseOneHardCore_arity
    {witness : AmplifierWitness} (input : CaseOneInput witness)
    (target : ℕ) (hcore : (hardCoreFromCaseOne input).arity ≤ target) :
    (paddedCaseOneHardCore input target hcore).arity = target := rfl

@[simp] theorem paddedCaseOneHardCore_size
    {witness : AmplifierWitness} (input : CaseOneInput witness)
    (target : ℕ) (hcore : (hardCoreFromCaseOne input).arity ≤ target) :
    (paddedCaseOneHardCore input target hcore).size =
      (hardCoreFromCaseOne input).size := rfl

@[simp] theorem paddedCaseOneHardCore_advantage
    {witness : AmplifierWitness} (input : CaseOneInput witness)
    (target : ℕ) (hcore : (hardCoreFromCaseOne input).arity ≤ target) :
    (paddedCaseOneHardCore input target hcore).advantage =
      (hardCoreFromCaseOne input).advantage := rfl

end NearCubicWires.CaseOnePadding
