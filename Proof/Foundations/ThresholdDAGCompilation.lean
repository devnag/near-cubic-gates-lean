import Proof.Foundations.BooleanDAGBuilder
import Proof.Foundations.SupplierPipeline

/-!
# Polynomial Boolean-DAG simulations of normalized threshold layers

This module compiles the concrete support-first circuits used by the suppliers
to the canonical topologically ordered `BooleanCircuit` DAG.  Arithmetic is
little-endian and uses shared ripple-carry wires; no formula-tree expansion is
used.  The final theorems expose both semantics and an explicit fixed
polynomial node bound in the input arity and physical wire count.
-/

namespace NearCubicWires.ThresholdDAGSimulation

open Finset
open scoped BigOperators
open NearCubicWires
open NearCubicWires.SupplierPipeline
open NearCubicWires.SourceInterfaces
open NearCubicWires.ThresholdCompiler

/-! ## Bit arithmetic used by the verified DAG compiler -/

/-- Natural value of a little-endian bit list. -/
def bitListValue : List Bool → ℕ
  | [] => 0
  | bit :: bits => bit.toNat + 2 * bitListValue bits

@[simp] theorem bitListValue_nil : bitListValue [] = 0 := rfl

@[simp] theorem bitListValue_cons (bit : Bool) (bits : List Bool) :
    bitListValue (bit :: bits) = bit.toNat + 2 * bitListValue bits :=
  rfl

/-- Sum bit and carry bit of a full adder. -/
def fullAdder (left right carry : Bool) : Bool × Bool :=
  (Bool.xor3 left right carry, Bool.carry left right carry)

theorem fullAdder_value (left right carry : Bool) :
    (fullAdder left right carry).1.toNat +
        2 * (fullAdder left right carry).2.toNat =
      left.toNat + right.toNat + carry.toNat := by
  cases left <;> cases right <;> cases carry <;>
    decide

/-- Equal-width ripple addition.  A final carry bit is always retained, which
keeps the arithmetic exact rather than silently truncating overflow. -/
def rippleAdd : List Bool → List Bool → Bool → List Bool
  | [], _, carry => [carry]
  | left :: leftBits, [], carry =>
      let result := fullAdder left false carry
      result.1 :: rippleAdd leftBits [] result.2
  | left :: leftBits, right :: rightBits, carry =>
      let result := fullAdder left right carry
      result.1 :: rippleAdd leftBits rightBits result.2

@[simp] theorem rippleAdd_nil_left (right : List Bool) (carry : Bool) :
    rippleAdd [] right carry = [carry] :=
  rfl

theorem rippleAdd_value_of_equal_length
    (left right : List Bool) (carry : Bool)
    (hlength : left.length = right.length) :
    bitListValue (rippleAdd left right carry) =
      bitListValue left + bitListValue right + carry.toNat := by
  induction left generalizing right carry with
  | nil =>
      cases right with
      | nil => cases carry <;> decide
      | cons right rightBits => simp at hlength
  | cons left leftBits ih =>
      cases right with
      | nil => simp at hlength
      | cons right rightBits =>
          simp only [List.length_cons, Nat.succ.injEq] at hlength
          let result := fullAdder left right carry
          have htail := ih rightBits result.2 hlength
          simp only [rippleAdd, bitListValue_cons]
          rw [htail]
          have hfull := fullAdder_value left right carry
          dsimp [result] at hfull ⊢
          omega

/-- Little-endian bits of a natural, padded or truncated to exactly `width`
positions.  Callers choose a width large enough for the represented value. -/
def fixedBits (width value : ℕ) : List Bool :=
  match width with
  | 0 => []
  | width + 1 =>
      decide (value % 2 = 1) :: fixedBits width (value / 2)

@[simp] theorem fixedBits_length (width value : ℕ) :
    (fixedBits width value).length = width := by
  induction width generalizing value with
  | zero => rfl
  | succ width ih => simp [fixedBits, ih]

theorem fixedBits_value_of_lt_pow
    (width value : ℕ) (hvalue : value < 2 ^ width) :
    bitListValue (fixedBits width value) = value := by
  -- `Nat.bitwise` exposes exactly the finite binary expansion below `2^width`.
  induction width generalizing value with
  | zero =>
      have : value = 0 := by simpa using hvalue
      subst value
      rfl
  | succ width ih =>
      simp only [fixedBits, bitListValue_cons]
      rw [ih]
      · have hlow :
            (decide (value % 2 = 1)).toNat = value % 2 := by
          have hmod : value % 2 < 2 := Nat.mod_lt _ (by omega)
          interval_cases _h : value % 2 <;> simp
        rw [hlow]
        omega
      · have hpow : 2 ^ (width + 1) = 2 ^ width * 2 := by
          simp [pow_succ, Nat.mul_comm]
        rw [hpow] at hvalue
        exact (Nat.div_lt_iff_lt_mul (by omega : 0 < 2)).2 hvalue

/-! ## Compositional verified gate appenders -/

def wireValue {n : ℕ} (builder : BooleanDAGBuilder n)
    (input : BitInput n) (reference : Fin builder.nodes.length) : Bool :=
  (getElem? (builder.values input) reference.val).getD false

@[simp] theorem wireValue_extension
    {n : ℕ} {prior final : BooleanDAGBuilder n}
    (extension : BooleanDAGExtension prior final)
    (input : BitInput n) (reference : Fin prior.nodes.length) :
    wireValue final input (extension.lift reference) =
      wireValue prior input reference := by
  unfold wireValue
  rw [extension.wireValue_lift]

def buildResultTrans
    {n firstArity secondArity : ℕ}
    {prior : BooleanDAGBuilder n}
    (first : BooleanDAGBuildResult prior firstArity)
    (second : BooleanDAGBuildResult first.final secondArity) :
    BooleanDAGBuildResult prior secondArity where
  final := second.final
  extension := first.extension.trans second.extension
  output := second.output

@[simp] theorem buildResultTrans_addedNodes
    {n firstArity secondArity : ℕ}
    {prior : BooleanDAGBuilder n}
    (first : BooleanDAGBuildResult prior firstArity)
    (second : BooleanDAGBuildResult first.final secondArity) :
    (buildResultTrans first second).addedNodes =
      first.addedNodes + second.addedNodes := by
  simp [buildResultTrans, BooleanDAGBuildResult.addedNodes,
    BooleanDAGExtension.trans]

def buildNode {n : ℕ} (builder : BooleanDAGBuilder n)
    (node : BooleanNode n)
    (hnode : node.WellFormedAt builder.nodes.length) :
    BooleanDAGBuildResult builder 1 where
  final := builder.appendNode node hnode
  extension := BooleanDAGExtension.single builder node hnode
  output := fun _ => builder.newest node hnode

@[simp] theorem buildNode_addedNodes {n : ℕ}
    (builder : BooleanDAGBuilder n) (node : BooleanNode n)
    (hnode : node.WellFormedAt builder.nodes.length) :
    (buildNode builder node hnode).addedNodes = 1 := by
  simp [buildNode, BooleanDAGBuildResult.addedNodes,
    BooleanDAGExtension.single]

theorem buildNode_value {n : ℕ}
    (builder : BooleanDAGBuilder n) (node : BooleanNode n)
    (hnode : node.WellFormedAt builder.nodes.length)
    (input : BitInput n) :
    wireValue (buildNode builder node hnode).final input
        ((buildNode builder node hnode).output 0) =
      node.eval input (builder.values input) := by
  unfold wireValue
  change
    (getElem? ((builder.appendNode node hnode).values input)
      (builder.newest node hnode).val).getD false =
        node.eval input (builder.values input)
  rw [BooleanDAGBuilder.appendNode_newest]
  rfl

def buildConst {n : ℕ} (builder : BooleanDAGBuilder n) (value : Bool) :
    BooleanDAGBuildResult builder 1 :=
  buildNode builder (.const value) trivial

def buildInput {n : ℕ} (builder : BooleanDAGBuilder n) (index : Fin n) :
    BooleanDAGBuildResult builder 1 :=
  buildNode builder (.input index) trivial

def buildNot {n : ℕ} (builder : BooleanDAGBuilder n)
    (child : Fin builder.nodes.length) :
    BooleanDAGBuildResult builder 1 :=
  buildNode builder (.not child.val) child.isLt

def buildAnd {n : ℕ} (builder : BooleanDAGBuilder n)
    (left right : Fin builder.nodes.length) :
    BooleanDAGBuildResult builder 1 :=
  buildNode builder (.and left.val right.val) ⟨left.isLt, right.isLt⟩

def buildOr {n : ℕ} (builder : BooleanDAGBuilder n)
    (left right : Fin builder.nodes.length) :
    BooleanDAGBuildResult builder 1 :=
  buildNode builder (.or left.val right.val) ⟨left.isLt, right.isLt⟩

@[simp] theorem buildConst_addedNodes {n : ℕ}
    (builder : BooleanDAGBuilder n) (value : Bool) :
    (buildConst builder value).addedNodes = 1 :=
  buildNode_addedNodes _ _ _

@[simp] theorem buildInput_addedNodes {n : ℕ}
    (builder : BooleanDAGBuilder n) (index : Fin n) :
    (buildInput builder index).addedNodes = 1 :=
  buildNode_addedNodes _ _ _

@[simp] theorem buildNot_addedNodes {n : ℕ}
    (builder : BooleanDAGBuilder n)
    (child : Fin builder.nodes.length) :
    (buildNot builder child).addedNodes = 1 :=
  buildNode_addedNodes _ _ _

@[simp] theorem buildAnd_addedNodes {n : ℕ}
    (builder : BooleanDAGBuilder n)
    (left right : Fin builder.nodes.length) :
    (buildAnd builder left right).addedNodes = 1 :=
  buildNode_addedNodes _ _ _

@[simp] theorem buildOr_addedNodes {n : ℕ}
    (builder : BooleanDAGBuilder n)
    (left right : Fin builder.nodes.length) :
    (buildOr builder left right).addedNodes = 1 :=
  buildNode_addedNodes _ _ _

@[simp] theorem buildConst_value {n : ℕ}
    (builder : BooleanDAGBuilder n) (value : Bool)
    (input : BitInput n) :
    wireValue (buildConst builder value).final input
      ((buildConst builder value).output 0) = value := by
  simpa [buildConst, BooleanNode.eval] using
    buildNode_value builder (.const value) trivial input

@[simp] theorem buildInput_value {n : ℕ}
    (builder : BooleanDAGBuilder n) (index : Fin n)
    (input : BitInput n) :
    wireValue (buildInput builder index).final input
      ((buildInput builder index).output 0) = input index := by
  simpa [buildInput, BooleanNode.eval] using
    buildNode_value builder (.input index) trivial input

@[simp] theorem buildNot_value {n : ℕ}
    (builder : BooleanDAGBuilder n)
    (child : Fin builder.nodes.length) (input : BitInput n) :
    wireValue (buildNot builder child).final input
      ((buildNot builder child).output 0) =
        !wireValue builder input child := by
  simpa [buildNot, BooleanNode.eval, wireValue] using
    buildNode_value builder (.not child.val) child.isLt input

@[simp] theorem buildAnd_value {n : ℕ}
    (builder : BooleanDAGBuilder n)
    (left right : Fin builder.nodes.length) (input : BitInput n) :
    wireValue (buildAnd builder left right).final input
      ((buildAnd builder left right).output 0) =
        (wireValue builder input left && wireValue builder input right) := by
  simpa [buildAnd, BooleanNode.eval, wireValue] using
    buildNode_value builder (.and left.val right.val)
      ⟨left.isLt, right.isLt⟩ input

@[simp] theorem buildOr_value {n : ℕ}
    (builder : BooleanDAGBuilder n)
    (left right : Fin builder.nodes.length) (input : BitInput n) :
    wireValue (buildOr builder left right).final input
      ((buildOr builder left right).output 0) =
        (wireValue builder input left || wireValue builder input right) := by
  simpa [buildOr, BooleanNode.eval, wireValue] using
    buildNode_value builder (.or left.val right.val)
      ⟨left.isLt, right.isLt⟩ input

/-- Four-node XOR using the shared inputs once each. -/
def buildXor {n : ℕ} (builder : BooleanDAGBuilder n)
    (left right : Fin builder.nodes.length) :
    BooleanDAGBuildResult builder 1 :=
  let disjunction := buildOr builder left right
  let conjunction := buildAnd disjunction.final
    (disjunction.extension.lift left)
    (disjunction.extension.lift right)
  let negatedConjunction := buildNot conjunction.final
    (conjunction.output 0)
  let output := buildAnd negatedConjunction.final
    (negatedConjunction.extension.lift
      (conjunction.extension.lift (disjunction.output 0)))
    (negatedConjunction.output 0)
  buildResultTrans disjunction
    (buildResultTrans conjunction
      (buildResultTrans negatedConjunction output))

@[simp] theorem buildXor_addedNodes {n : ℕ}
    (builder : BooleanDAGBuilder n)
    (left right : Fin builder.nodes.length) :
    (buildXor builder left right).addedNodes = 4 := by
  simp [buildXor, buildResultTrans_addedNodes, buildOr, buildAnd, buildNot]

@[simp] theorem buildXor_value {n : ℕ}
    (builder : BooleanDAGBuilder n)
    (left right : Fin builder.nodes.length) (input : BitInput n) :
    wireValue (buildXor builder left right).final input
      ((buildXor builder left right).output 0) =
        xor (wireValue builder input left) (wireValue builder input right) := by
  simp only [buildXor, buildResultTrans]
  simp only [buildAnd_value, wireValue_extension,
    buildNot_value, buildOr_value]
  cases wireValue builder input left <;>
    cases wireValue builder input right <;> decide

/-- Eleven-node full adder.  The first XOR wire is shared by the sum and
carry computations, which is precisely where a tree encoding would lose the
polynomial size recurrence.  Output `0` is the sum bit and output `1` is the
carry bit. -/
def buildFullAdder {n : ℕ} (builder : BooleanDAGBuilder n)
    (left right carry : Fin builder.nodes.length) :
    BooleanDAGBuildResult builder 2 :=
  let leftXorRight := buildXor builder left right
  let sum := buildXor leftXorRight.final
    (leftXorRight.output 0)
    (leftXorRight.extension.lift carry)
  let leftAndRight := buildAnd sum.final
    (sum.extension.lift (leftXorRight.extension.lift left))
    (sum.extension.lift (leftXorRight.extension.lift right))
  let carryAndXor := buildAnd leftAndRight.final
    (leftAndRight.extension.lift
      (sum.extension.lift (leftXorRight.output 0)))
    (leftAndRight.extension.lift
      (sum.extension.lift (leftXorRight.extension.lift carry)))
  let carryOutput := buildOr carryAndXor.final
    (carryAndXor.extension.lift (leftAndRight.output 0))
    (carryAndXor.output 0)
  let extension :=
    leftXorRight.extension.trans
      (sum.extension.trans
        (leftAndRight.extension.trans
          (carryAndXor.extension.trans carryOutput.extension)))
  let sumOutput :=
    carryOutput.extension.lift
      (carryAndXor.extension.lift
        (leftAndRight.extension.lift (sum.output 0)))
  { final := carryOutput.final
    extension := extension
    output := Fin.cases sumOutput (fun _ => carryOutput.output 0) }

@[simp] theorem buildFullAdder_addedNodes {n : ℕ}
    (builder : BooleanDAGBuilder n)
    (left right carry : Fin builder.nodes.length) :
    (buildFullAdder builder left right carry).addedNodes = 11 := by
  let leftXorRight := buildXor builder left right
  let sum := buildXor leftXorRight.final
    (leftXorRight.output 0)
    (leftXorRight.extension.lift carry)
  let leftAndRight := buildAnd sum.final
    (sum.extension.lift (leftXorRight.extension.lift left))
    (sum.extension.lift (leftXorRight.extension.lift right))
  let carryAndXor := buildAnd leftAndRight.final
    (leftAndRight.extension.lift
      (sum.extension.lift (leftXorRight.output 0)))
    (leftAndRight.extension.lift
      (sum.extension.lift (leftXorRight.extension.lift carry)))
  let carryOutput := buildOr carryAndXor.final
    (carryAndXor.extension.lift (leftAndRight.output 0))
    (carryAndXor.output 0)
  change leftXorRight.addedNodes +
      (sum.addedNodes + (leftAndRight.addedNodes +
        (carryAndXor.addedNodes + carryOutput.addedNodes))) = 11
  simp [leftXorRight, sum, leftAndRight, carryAndXor, carryOutput,
    buildAnd, buildOr]

@[simp] theorem buildFullAdder_sum_value {n : ℕ}
    (builder : BooleanDAGBuilder n)
    (left right carry : Fin builder.nodes.length) (input : BitInput n) :
    wireValue (buildFullAdder builder left right carry).final input
      ((buildFullAdder builder left right carry).output 0) =
        (fullAdder (wireValue builder input left)
          (wireValue builder input right)
          (wireValue builder input carry)).1 := by
  let leftXorRight := buildXor builder left right
  let sum := buildXor leftXorRight.final
    (leftXorRight.output 0)
    (leftXorRight.extension.lift carry)
  let leftAndRight := buildAnd sum.final
    (sum.extension.lift (leftXorRight.extension.lift left))
    (sum.extension.lift (leftXorRight.extension.lift right))
  let carryAndXor := buildAnd leftAndRight.final
    (leftAndRight.extension.lift
      (sum.extension.lift (leftXorRight.output 0)))
    (leftAndRight.extension.lift
      (sum.extension.lift (leftXorRight.extension.lift carry)))
  let carryOutput := buildOr carryAndXor.final
    (carryAndXor.extension.lift (leftAndRight.output 0))
    (carryAndXor.output 0)
  change wireValue carryOutput.final input
      (carryOutput.extension.lift
        (carryAndXor.extension.lift
          (leftAndRight.extension.lift (sum.output 0)))) =
    (fullAdder (wireValue builder input left)
      (wireValue builder input right)
      (wireValue builder input carry)).1
  rw [wireValue_extension, wireValue_extension, wireValue_extension]
  dsimp only [sum]
  rw [buildXor_value, wireValue_extension, buildXor_value]
  rfl

@[simp] theorem buildFullAdder_carry_value {n : ℕ}
    (builder : BooleanDAGBuilder n)
    (left right carry : Fin builder.nodes.length) (input : BitInput n) :
    wireValue (buildFullAdder builder left right carry).final input
      ((buildFullAdder builder left right carry).output 1) =
        (fullAdder (wireValue builder input left)
          (wireValue builder input right)
          (wireValue builder input carry)).2 := by
  let leftXorRight := buildXor builder left right
  let sum := buildXor leftXorRight.final
    (leftXorRight.output 0)
    (leftXorRight.extension.lift carry)
  let leftAndRight := buildAnd sum.final
    (sum.extension.lift (leftXorRight.extension.lift left))
    (sum.extension.lift (leftXorRight.extension.lift right))
  let carryAndXor := buildAnd leftAndRight.final
    (leftAndRight.extension.lift
      (sum.extension.lift (leftXorRight.output 0)))
    (leftAndRight.extension.lift
      (sum.extension.lift (leftXorRight.extension.lift carry)))
  let carryOutput := buildOr carryAndXor.final
    (carryAndXor.extension.lift (leftAndRight.output 0))
    (carryAndXor.output 0)
  change wireValue carryOutput.final input (carryOutput.output 0) =
    (fullAdder (wireValue builder input left)
      (wireValue builder input right)
      (wireValue builder input carry)).2
  have houtput :
      wireValue carryOutput.final input (carryOutput.output 0) =
        (wireValue carryAndXor.final input
            (carryAndXor.extension.lift (leftAndRight.output 0)) ||
          wireValue carryAndXor.final input (carryAndXor.output 0)) := by
    simpa only [carryOutput] using
      buildOr_value carryAndXor.final
        (carryAndXor.extension.lift (leftAndRight.output 0))
        (carryAndXor.output 0) input
  have hleftAndRight :
      wireValue leftAndRight.final input (leftAndRight.output 0) =
        (wireValue builder input left && wireValue builder input right) := by
    have h := buildAnd_value sum.final
      (sum.extension.lift (leftXorRight.extension.lift left))
      (sum.extension.lift (leftXorRight.extension.lift right)) input
    simpa only [leftAndRight, wireValue_extension] using h
  have hcarryAndXor :
      wireValue carryAndXor.final input (carryAndXor.output 0) =
        (wireValue leftXorRight.final input (leftXorRight.output 0) &&
          wireValue builder input carry) := by
    have h := buildAnd_value leftAndRight.final
      (leftAndRight.extension.lift
        (sum.extension.lift (leftXorRight.output 0)))
      (leftAndRight.extension.lift
        (sum.extension.lift (leftXorRight.extension.lift carry))) input
    simpa only [carryAndXor, wireValue_extension] using h
  rw [houtput, wireValue_extension, hleftAndRight, hcarryAndXor,
    buildXor_value]
  cases wireValue builder input left <;>
    cases wireValue builder input right <;>
      cases wireValue builder input carry <;> decide

/-! ## Shared ripple-carry bit-vector compiler -/

def readWires {n : ℕ} (builder : BooleanDAGBuilder n)
    (input : BitInput n) (references : List (Fin builder.nodes.length)) :
    List Bool :=
  references.map (wireValue builder input)

@[simp] theorem readWires_nil {n : ℕ} (builder : BooleanDAGBuilder n)
    (input : BitInput n) :
    readWires builder input [] = [] :=
  rfl

@[simp] theorem readWires_cons {n : ℕ} (builder : BooleanDAGBuilder n)
    (input : BitInput n) (reference : Fin builder.nodes.length)
    (references : List (Fin builder.nodes.length)) :
    readWires builder input (reference :: references) =
      wireValue builder input reference :: readWires builder input references :=
  rfl

@[simp] theorem readWires_lift {n : ℕ}
    {prior final : BooleanDAGBuilder n}
    (extension : BooleanDAGExtension prior final)
    (input : BitInput n)
    (references : List (Fin prior.nodes.length)) :
    readWires final input (references.map extension.lift) =
      readWires prior input references := by
  induction references with
  | nil => rfl
  | cons reference references ih =>
      simp [readWires, wireValue_extension]

/-- A variable-width output bundle over one contiguous DAG extension. -/
structure DAGBitListResult {n : ℕ} (prior : BooleanDAGBuilder n) where
  final : BooleanDAGBuilder n
  extension : BooleanDAGExtension prior final
  bits : List (Fin final.nodes.length)

def DAGBitListResult.addedNodes {n : ℕ}
    {prior : BooleanDAGBuilder n} (result : DAGBitListResult prior) : ℕ :=
  result.extension.suffix.length

theorem DAGBitListResult.final_length {n : ℕ}
    {prior : BooleanDAGBuilder n} (result : DAGBitListResult prior) :
    result.final.nodes.length =
      prior.nodes.length + result.addedNodes :=
  result.extension.length_eq

/-- Compile equal-width addition.  The result contains one extra most
significant carry wire and uses exactly eleven gates per input position. -/
def buildRippleAdd {n : ℕ} (builder : BooleanDAGBuilder n) :
    (left right : List (Fin builder.nodes.length)) →
    left.length = right.length →
    (carry : Fin builder.nodes.length) →
    DAGBitListResult builder
  | [], [], _, carry =>
      { final := builder
        extension := BooleanDAGExtension.refl builder
        bits := [carry] }
  | [], _ :: _, hlength, _ => by simp at hlength
  | _ :: _, [], hlength, _ => by simp at hlength
  | left :: leftBits, right :: rightBits, hlength, carry =>
      let cell := buildFullAdder builder left right carry
      let tail := buildRippleAdd cell.final
        (leftBits.map cell.extension.lift)
        (rightBits.map cell.extension.lift)
        (by simpa using Nat.succ.inj hlength)
        (cell.output 1)
      { final := tail.final
        extension := cell.extension.trans tail.extension
        bits := tail.extension.lift (cell.output 0) :: tail.bits }
termination_by left right _ _carry => left.length

@[simp] theorem buildRippleAdd_bits_length {n : ℕ}
    (builder : BooleanDAGBuilder n)
    (left right : List (Fin builder.nodes.length))
    (hlength : left.length = right.length)
    (carry : Fin builder.nodes.length) :
    (buildRippleAdd builder left right hlength carry).bits.length =
      left.length + 1 := by
  fun_induction buildRippleAdd with
  | case1 => rfl
  | case2 builder left leftBits right rightBits hlength carry cell tail
      _hproof ih =>
      have htail : tail.bits.length = leftBits.length + 1 := by
        simpa only [tail, List.length_map] using ih
      simpa only [List.length_cons] using congrArg Nat.succ htail

@[simp] theorem buildRippleAdd_addedNodes {n : ℕ}
    (builder : BooleanDAGBuilder n)
    (left right : List (Fin builder.nodes.length))
    (hlength : left.length = right.length)
    (carry : Fin builder.nodes.length) :
    (buildRippleAdd builder left right hlength carry).addedNodes =
      11 * left.length := by
  fun_induction buildRippleAdd with
  | case1 => rfl
  | case2 builder left leftBits right rightBits hlength carry cell tail
      _hproof ih =>
      have hcell : cell.extension.suffix.length = 11 := by
        simpa only [cell, BooleanDAGBuildResult.addedNodes] using
          buildFullAdder_addedNodes builder left right carry
      have htail : tail.extension.suffix.length =
          11 * leftBits.length := by
        simpa only [tail, DAGBitListResult.addedNodes,
          List.length_map] using ih
      simp only [DAGBitListResult.addedNodes, BooleanDAGExtension.trans,
        List.length_append, List.length_cons]
      omega

theorem buildRippleAdd_values {n : ℕ}
    (builder : BooleanDAGBuilder n)
    (left right : List (Fin builder.nodes.length))
    (hlength : left.length = right.length)
    (carry : Fin builder.nodes.length) (input : BitInput n) :
    readWires (buildRippleAdd builder left right hlength carry).final input
        (buildRippleAdd builder left right hlength carry).bits =
      rippleAdd (readWires builder input left)
        (readWires builder input right)
        (wireValue builder input carry) := by
  fun_induction buildRippleAdd with
  | case1 => rfl
  | case2 builder left leftBits right rightBits hlength carry cell tail
      _hproof ih =>
      dsimp only
      change
        wireValue tail.final input (tail.extension.lift (cell.output 0)) ::
            readWires tail.final input tail.bits =
          (fullAdder (wireValue builder input left)
            (wireValue builder input right)
            (wireValue builder input carry)).1 ::
            rippleAdd (readWires builder input leftBits)
              (readWires builder input rightBits)
              (fullAdder (wireValue builder input left)
                (wireValue builder input right)
                (wireValue builder input carry)).2
      congr 1
      · rw [wireValue_extension]
        simpa only [cell] using
          buildFullAdder_sum_value builder left right carry input
      · have htail :
            readWires tail.final input tail.bits =
              rippleAdd
                (readWires cell.final input
                  (leftBits.map cell.extension.lift))
                (readWires cell.final input
                  (rightBits.map cell.extension.lift))
                (wireValue cell.final input (cell.output 1)) := by
          simpa only [tail] using ih
        rw [htail, readWires_lift, readWires_lift]
        have hcarry :
            wireValue cell.final input (cell.output 1) =
              (fullAdder (wireValue builder input left)
                (wireValue builder input right)
                (wireValue builder input carry)).2 := by
          simpa only [cell] using
            buildFullAdder_carry_value builder left right carry input
        rw [hcarry]

theorem buildRippleAdd_value {n : ℕ}
    (builder : BooleanDAGBuilder n)
    (left right : List (Fin builder.nodes.length))
    (hlength : left.length = right.length)
    (carry : Fin builder.nodes.length) (input : BitInput n) :
    bitListValue
        (readWires (buildRippleAdd builder left right hlength carry).final
          input (buildRippleAdd builder left right hlength carry).bits) =
      bitListValue (readWires builder input left) +
        bitListValue (readWires builder input right) +
          (wireValue builder input carry).toNat := by
  rw [buildRippleAdd_values]
  exact rippleAdd_value_of_equal_length _ _ _
    (by simp [readWires, hlength])

/-! ## Unsigned comparison against a fixed constant -/

/-- `(greater,equal)` for a little-endian bit list and a fixed natural.
Recursive calls consume the more significant bits first. -/
def compareBitList : List Bool → ℕ → Bool × Bool
  | [], target => (false, decide (target = 0))
  | bit :: bits, target =>
      let high := compareBitList bits (target / 2)
      let targetBit := decide (target % 2 = 1)
      let equal := high.2 && decide (bit = targetBit)
      let greater := high.1 ||
        (high.2 && bit && !targetBit)
      (greater, equal)

theorem compareBitList_correct (bits : List Bool) (target : ℕ)
    (htarget : target < 2 ^ bits.length) :
    compareBitList bits target =
      (decide (target < bitListValue bits),
        decide (target = bitListValue bits)) := by
  induction bits generalizing target with
  | nil =>
      have htargetZero : target = 0 := by simpa using htarget
      subst target
      decide
  | cons bit bits ih =>
      simp only [List.length_cons] at htarget
      have htargetHigh : target / 2 < 2 ^ bits.length := by
        have hpow : 2 ^ (bits.length + 1) = 2 ^ bits.length * 2 := by
          simp [pow_succ, Nat.mul_comm]
        rw [hpow] at htarget
        exact (Nat.div_lt_iff_lt_mul (by omega : 0 < 2)).2 htarget
      rw [compareBitList, ih (target / 2) htargetHigh]
      have hdecompose := Nat.mod_add_div target 2
      have hmod : target % 2 < 2 := Nat.mod_lt _ (by omega)
      by_cases hhighGreater : target / 2 < bitListValue bits <;>
        by_cases hhighEqual : target / 2 = bitListValue bits <;>
        interval_cases _htargetBit : target % 2 <;>
        cases bit <;>
        simp [hhighGreater, hhighEqual, bitListValue] <;>
        omega

/-- Compile comparison against `target`.  Output `0` is strict greater-than
and output `1` is equality.  At most four nodes are added per bit, plus the
two base constants. -/
def buildCompareConstant {n : ℕ} (builder : BooleanDAGBuilder n) :
    (bits : List (Fin builder.nodes.length)) → ℕ →
      BooleanDAGBuildResult builder 2
  | [], _target =>
      let falseNode := buildConst builder false
      let equalityNode := buildConst falseNode.final (decide (_target = 0))
      { final := equalityNode.final
        extension := falseNode.extension.trans equalityNode.extension
        output := Fin.cases
          (equalityNode.extension.lift (falseNode.output 0))
          (fun _ => equalityNode.output 0) }
  | bit :: bits, target =>
      let high := buildCompareConstant builder bits (target / 2)
      let bitInHigh := high.extension.lift bit
      if _htargetBit : target % 2 = 1 then
        let equal := buildAnd high.final (high.output 1) bitInHigh
        { final := equal.final
          extension := high.extension.trans equal.extension
          output := Fin.cases
            (equal.extension.lift (high.output 0))
            (fun _ => equal.output 0) }
      else
        let negatedBit := buildNot high.final bitInHigh
        let equal := buildAnd negatedBit.final
          (negatedBit.extension.lift (high.output 1))
          (negatedBit.output 0)
        let lowGreater := buildAnd equal.final
          (equal.extension.lift
            (negatedBit.extension.lift (high.output 1)))
          (equal.extension.lift
            (negatedBit.extension.lift bitInHigh))
        let greater := buildOr lowGreater.final
          (lowGreater.extension.lift
            (equal.extension.lift
              (negatedBit.extension.lift (high.output 0))))
          (lowGreater.output 0)
        { final := greater.final
          extension := high.extension.trans
            (negatedBit.extension.trans
              (equal.extension.trans
                (lowGreater.extension.trans greater.extension)))
          output := Fin.cases (greater.output 0)
            (fun _ =>
              greater.extension.lift
                (lowGreater.extension.lift (equal.output 0))) }

theorem buildCompareConstant_addedNodes_le {n : ℕ}
    (builder : BooleanDAGBuilder n)
    (bits : List (Fin builder.nodes.length)) (target : ℕ) :
    (buildCompareConstant builder bits target).addedNodes ≤
      4 * bits.length + 2 := by
  fun_induction buildCompareConstant with
  | case1 target falseNode equalityNode =>
      change falseNode.extension.suffix.length +
          equalityNode.extension.suffix.length ≤ 2
      have hfalse : falseNode.extension.suffix.length = 1 := by
        simpa only [falseNode, BooleanDAGBuildResult.addedNodes] using
          buildConst_addedNodes builder false
      have hequality : equalityNode.extension.suffix.length = 1 := by
        simpa only [equalityNode, BooleanDAGBuildResult.addedNodes] using
          buildConst_addedNodes falseNode.final (decide (target = 0))
      omega
  | case2 bit bits target high bitInHigh htargetBit equal ih =>
      simp only [BooleanDAGBuildResult.addedNodes,
        BooleanDAGExtension.trans, List.length_append,
        List.length_cons]
      have hhigh : high.extension.suffix.length ≤
          4 * bits.length + 2 := by
        simpa only [high, BooleanDAGBuildResult.addedNodes] using ih
      have hequal : equal.extension.suffix.length = 1 := by
        simpa only [equal, BooleanDAGBuildResult.addedNodes] using
          buildAnd_addedNodes high.final (high.output 1) bitInHigh
      omega
  | case3 bit bits target high bitInHigh htargetBit negatedBit equal
      lowGreater greater ih =>
      simp only [BooleanDAGBuildResult.addedNodes,
        BooleanDAGExtension.trans, List.length_append,
        List.length_cons]
      have hhigh : high.extension.suffix.length ≤
          4 * bits.length + 2 := by
        simpa only [high, BooleanDAGBuildResult.addedNodes] using ih
      have hnot : negatedBit.extension.suffix.length = 1 := by
        simpa only [negatedBit, BooleanDAGBuildResult.addedNodes] using
          buildNot_addedNodes high.final bitInHigh
      have hequal : equal.extension.suffix.length = 1 := by
        simpa only [equal, BooleanDAGBuildResult.addedNodes] using
          buildAnd_addedNodes negatedBit.final
            (negatedBit.extension.lift (high.output 1))
            (negatedBit.output 0)
      have hlow : lowGreater.extension.suffix.length = 1 := by
        simpa only [lowGreater, BooleanDAGBuildResult.addedNodes] using
          buildAnd_addedNodes equal.final
            (equal.extension.lift
              (negatedBit.extension.lift (high.output 1)))
            (equal.extension.lift
              (negatedBit.extension.lift bitInHigh))
      have hgreater : greater.extension.suffix.length = 1 := by
        simpa only [greater, BooleanDAGBuildResult.addedNodes] using
          buildOr_addedNodes lowGreater.final
            (lowGreater.extension.lift
              (equal.extension.lift
                (negatedBit.extension.lift (high.output 0))))
            (lowGreater.output 0)
      omega

theorem buildCompareConstant_values {n : ℕ}
    (builder : BooleanDAGBuilder n)
    (bits : List (Fin builder.nodes.length)) (target : ℕ)
    (input : BitInput n) :
    (wireValue (buildCompareConstant builder bits target).final input
        ((buildCompareConstant builder bits target).output 0),
      wireValue (buildCompareConstant builder bits target).final input
        ((buildCompareConstant builder bits target).output 1)) =
      compareBitList (readWires builder input bits) target := by
  fun_induction buildCompareConstant with
  | case1 target falseNode equalityNode =>
      change
        (wireValue equalityNode.final input
            (equalityNode.extension.lift (falseNode.output 0)),
          wireValue equalityNode.final input (equalityNode.output 0)) =
        (false, decide (target = 0))
      rw [wireValue_extension, buildConst_value, buildConst_value]
  | case2 bit bits target high bitInHigh htargetBit equal ih =>
      have hgreater :
          wireValue high.final input (high.output 0) =
            (compareBitList (readWires builder input bits)
              (target / 2)).1 := by
        simpa only [high] using congrArg Prod.fst ih
      have hequal :
          wireValue high.final input (high.output 1) =
            (compareBitList (readWires builder input bits)
              (target / 2)).2 := by
        simpa only [high] using congrArg Prod.snd ih
      change
        (wireValue equal.final input
            (equal.extension.lift (high.output 0)),
          wireValue equal.final input (equal.output 0)) =
        compareBitList
          (wireValue builder input bit ::
            readWires builder input bits) target
      rw [wireValue_extension, buildAnd_value, wireValue_extension]
      rw [compareBitList]
      simp only [htargetBit]
      rw [hgreater, hequal]
      cases wireValue builder input bit <;> simp
  | case3 bit bits target high bitInHigh htargetBit negatedBit equal
      lowGreater greater ih =>
      have hhighGreater :
          wireValue high.final input (high.output 0) =
            (compareBitList (readWires builder input bits)
              (target / 2)).1 := by
        simpa only [high] using congrArg Prod.fst ih
      have hhighEqual :
          wireValue high.final input (high.output 1) =
            (compareBitList (readWires builder input bits)
              (target / 2)).2 := by
        simpa only [high] using congrArg Prod.snd ih
      have hbitInHigh :
          wireValue high.final input bitInHigh =
            wireValue builder input bit := by
        simp only [bitInHigh, wireValue_extension]
      have hnegatedBit :
          wireValue negatedBit.final input (negatedBit.output 0) =
            !wireValue builder input bit := by
        rw [buildNot_value, hbitInHigh]
      have hequal :
          wireValue equal.final input (equal.output 0) =
            (wireValue high.final input (high.output 1) &&
              !wireValue builder input bit) := by
        rw [buildAnd_value, wireValue_extension, hnegatedBit]
      have hlowGreater :
          wireValue lowGreater.final input (lowGreater.output 0) =
            (wireValue high.final input (high.output 1) &&
              wireValue builder input bit) := by
        rw [buildAnd_value, wireValue_extension, wireValue_extension,
          wireValue_extension, wireValue_extension, hbitInHigh]
      have hcompiledGreater :
          wireValue greater.final input (greater.output 0) =
            (wireValue high.final input (high.output 0) ||
              (wireValue high.final input (high.output 1) &&
                wireValue builder input bit)) := by
        rw [buildOr_value, wireValue_extension, wireValue_extension,
          wireValue_extension, hlowGreater]
      have hcompiledEqual :
          wireValue greater.final input
              (greater.extension.lift
                (lowGreater.extension.lift (equal.output 0))) =
            (wireValue high.final input (high.output 1) &&
              !wireValue builder input bit) := by
        rw [wireValue_extension, wireValue_extension, hequal]
      change
        (wireValue greater.final input (greater.output 0),
          wireValue greater.final input
            (greater.extension.lift
              (lowGreater.extension.lift (equal.output 0)))) =
        compareBitList
          (wireValue builder input bit ::
            readWires builder input bits) target
      rw [hcompiledGreater, hcompiledEqual]
      rw [compareBitList]
      simp only [htargetBit]
      rw [hhighGreater, hhighEqual]
      cases wireValue builder input bit <;> simp

/-! ## Signed threshold scores -/

/-- Negative coefficients are moved to the other side of the threshold by
complementing their Boolean literal. -/
def shiftedLiteral (weight : ℤ) (bit : Bool) : Bool :=
  if weight < 0 then !bit else bit

def negativeWeight (weight : ℤ) : ℕ :=
  if weight < 0 then weight.natAbs else 0

def shiftedScore {n : ℕ} (gate : NormalizedThresholdGate n)
    (input : BitInput n) : ℕ :=
  ∑ index, (gate.weight index).natAbs *
    (shiftedLiteral (gate.weight index) (input index)).toNat

def negativeMass {n : ℕ} (gate : NormalizedThresholdGate n) : ℕ :=
  ∑ index, negativeWeight (gate.weight index)

theorem shiftedWeight_identity (weight : ℤ) (bit : Bool) :
    ((weight.natAbs * (shiftedLiteral weight bit).toNat : ℕ) : ℤ) =
      weight * bitInt bit + negativeWeight weight := by
  cases weight with
  | ofNat value =>
      have hnonnegative : ¬(Int.ofNat value < 0) := by simp
      simp only [shiftedLiteral, negativeWeight, if_neg hnonnegative]
      cases bit <;> simp [bitInt]
  | negSucc value =>
      have hnegative : Int.negSucc value < 0 := by simp
      simp only [shiftedLiteral, negativeWeight, if_pos hnegative]
      cases bit with
      | false => simp [bitInt]
      | true =>
          simp [bitInt]
          omega

theorem shiftedScore_identity {n : ℕ}
    (gate : NormalizedThresholdGate n) (input : BitInput n) :
    (shiftedScore gate input : ℤ) =
      (∑ index, gate.weight index * bitInt (input index)) +
        negativeMass gate := by
  simp only [shiftedScore, negativeMass, Nat.cast_sum]
  simp_rw [shiftedWeight_identity]
  exact Finset.sum_add_distrib

theorem normalized_eval_eq_shifted {n : ℕ}
    (gate : NormalizedThresholdGate n) (input : BitInput n) :
    gate.eval input =
      decide (gate.threshold + (negativeMass gate : ℤ) ≤
        (shiftedScore gate input : ℤ)) := by
  unfold NormalizedThresholdGate.eval
  apply decide_eq_decide.mpr
  rw [shiftedScore_identity]
  have hscore :
      (∑ index, gate.weight index *
          (if input index then 1 else 0)) =
        ∑ index, gate.weight index * bitInt (input index) := by
    apply Finset.sum_congr rfl
    intro index _
    cases input index <;> rfl
  rw [hscore]
  omega

/-- Boolean acceptance bit represented by the `(greater,equal)` comparator. -/
def compareAtLeast (bits : List Bool) (target : ℕ) : Bool :=
  (compareBitList bits target).1 || (compareBitList bits target).2

theorem compareAtLeast_correct (bits : List Bool) (target : ℕ)
    (htarget : target < 2 ^ bits.length) :
    compareAtLeast bits target = decide (target ≤ bitListValue bits) := by
  unfold compareAtLeast
  rw [compareBitList_correct bits target htarget]
  by_cases hgreater : target < bitListValue bits
  · simp [hgreater, le_of_lt hgreater]
  · have hle : bitListValue bits ≤ target := le_of_not_gt hgreater
    by_cases hequal : target = bitListValue bits
    · simp [hequal]
    · have hstrict : bitListValue bits < target :=
        lt_of_le_of_ne hle (Ne.symm hequal)
      simp [hgreater, hequal, Nat.not_le.mpr hstrict]

/-! ## Shared signed-weight accumulation -/

def buildShiftedLiteral {n : ℕ} (builder : BooleanDAGBuilder n)
    (reference : Fin builder.nodes.length) (weight : ℤ) :
    BooleanDAGBuildResult builder 1 :=
  if weight < 0 then
    buildNot builder reference
  else
    { final := builder
      extension := BooleanDAGExtension.refl builder
      output := fun _ => reference }

theorem buildShiftedLiteral_addedNodes_le {n : ℕ}
    (builder : BooleanDAGBuilder n)
    (reference : Fin builder.nodes.length) (weight : ℤ) :
    (buildShiftedLiteral builder reference weight).addedNodes ≤ 1 := by
  by_cases hweight : weight < 0
  · rw [buildShiftedLiteral, if_pos hweight]
    rw [buildNot_addedNodes]
  · rw [buildShiftedLiteral, if_neg hweight]
    simp [BooleanDAGBuildResult.addedNodes,
      BooleanDAGExtension.refl]

theorem buildShiftedLiteral_value {n : ℕ}
    (builder : BooleanDAGBuilder n)
    (reference : Fin builder.nodes.length) (weight : ℤ)
    (input : BitInput n) :
    wireValue (buildShiftedLiteral builder reference weight).final input
        ((buildShiftedLiteral builder reference weight).output 0) =
      shiftedLiteral weight (wireValue builder input reference) := by
  by_cases hweight : weight < 0
  · rw [buildShiftedLiteral, if_pos hweight,
      shiftedLiteral, if_pos hweight]
    exact buildNot_value builder reference input
  · rw [buildShiftedLiteral, if_neg hweight,
      shiftedLiteral, if_neg hweight]

/-- Replace each constant bit by one of two already-existing wires. -/
def selectBitWires {n : ℕ} {builder : BooleanDAGBuilder n}
    (bits : List Bool) (one zero : Fin builder.nodes.length) :
    List (Fin builder.nodes.length) :=
  bits.map fun bit => if bit then one else zero

@[simp] theorem selectBitWires_length {n : ℕ}
    {builder : BooleanDAGBuilder n} (bits : List Bool)
    (one zero : Fin builder.nodes.length) :
    (selectBitWires bits one zero).length = bits.length := by
  simp [selectBitWires]

theorem read_selectBitWires {n : ℕ}
    (builder : BooleanDAGBuilder n) (input : BitInput n)
    (bits : List Bool) (one zero : Fin builder.nodes.length)
    (hzero : wireValue builder input zero = false) :
    readWires builder input (selectBitWires bits one zero) =
      bits.map fun bit => bit && wireValue builder input one := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
      cases bit <;>
        simp [selectBitWires, readWires, hzero]

def shiftedListScore {m : ℕ} (weights : Fin m → ℤ)
    (values : Fin m → Bool) : List (Fin m) → ℕ
  | [] => 0
  | index :: indices =>
      (weights index).natAbs *
          (shiftedLiteral (weights index) (values index)).toNat +
        shiftedListScore weights values indices

/-- Add a list of signed weighted literals into an existing little-endian
accumulator.  The accumulator grows by one carry wire at each term, so no
overflow fact is hidden in the construction. -/
def buildWeightedSum {n m : ℕ} (weights : Fin m → ℤ)
    (builder : BooleanDAGBuilder n)
    (zero : Fin builder.nodes.length)
    (references : Fin m → Fin builder.nodes.length) :
    (sumBits : List (Fin builder.nodes.length)) →
    List (Fin m) → DAGBitListResult builder
  | sumBits, [] =>
      { final := builder
        extension := BooleanDAGExtension.refl builder
        bits := sumBits }
  | sumBits, index :: indices =>
      let literal :=
        buildShiftedLiteral builder (references index) (weights index)
      let zeroInLiteral := literal.extension.lift zero
      let oldSum := sumBits.map literal.extension.lift
      let term := selectBitWires
        (fixedBits sumBits.length (weights index).natAbs)
        (literal.output 0) zeroInLiteral
      let addition := buildRippleAdd literal.final oldSum term
        (by simp [oldSum, term]) zeroInLiteral
      let tail := buildWeightedSum weights addition.final
        (addition.extension.lift zeroInLiteral)
        (fun next =>
          addition.extension.lift (literal.extension.lift (references next)))
        addition.bits indices
      { final := tail.final
        extension := literal.extension.trans
          (addition.extension.trans tail.extension)
        bits := tail.bits }
termination_by _ indices => indices.length

@[simp] theorem buildWeightedSum_bits_length {n m : ℕ}
    (weights : Fin m → ℤ) (builder : BooleanDAGBuilder n)
    (zero : Fin builder.nodes.length)
    (references : Fin m → Fin builder.nodes.length)
    (sumBits : List (Fin builder.nodes.length))
    (indices : List (Fin m)) :
    (buildWeightedSum weights builder zero references sumBits indices).bits.length =
      sumBits.length + indices.length := by
  fun_induction buildWeightedSum with
  | case1 => simp
  | case2 builder zero references sumBits index indices literal
      zeroInLiteral oldSum term addition tail ih =>
      have haddition :
          addition.bits.length = sumBits.length + 1 := by
        simpa only [addition, oldSum, List.length_map] using
          buildRippleAdd_bits_length literal.final oldSum term
            (by simp [oldSum, term]) zeroInLiteral
      have htail :
          tail.bits.length = addition.bits.length + indices.length := by
        simpa only [tail] using ih
      change tail.bits.length =
        sumBits.length + (index :: indices).length
      simp only [List.length_cons]
      omega

theorem bitListValue_map_and (bits : List Bool) (literal : Bool) :
    bitListValue (bits.map fun bit => bit && literal) =
      bitListValue bits * literal.toNat := by
  induction bits generalizing literal with
  | nil => cases literal <;> decide
  | cons bit bits ih =>
      rw [List.map, bitListValue_cons, ih]
      cases bit <;> cases literal <;> simp [bitListValue]

theorem buildWeightedSum_addedNodes_le {n m : ℕ}
    (weights : Fin m → ℤ) (builder : BooleanDAGBuilder n)
    (zero : Fin builder.nodes.length)
    (references : Fin m → Fin builder.nodes.length)
    (sumBits : List (Fin builder.nodes.length))
    (indices : List (Fin m)) :
    (buildWeightedSum weights builder zero references
        sumBits indices).addedNodes ≤
      indices.length *
        (11 * (sumBits.length + indices.length) + 1) := by
  fun_induction buildWeightedSum with
  | case1 =>
      simp [DAGBitListResult.addedNodes,
        BooleanDAGExtension.refl]
  | case2 builder zero references sumBits index indices literal
      zeroInLiteral oldSum term addition tail ih =>
      have hliteral :
          literal.extension.suffix.length ≤ 1 := by
        simpa only [literal, BooleanDAGBuildResult.addedNodes] using
          buildShiftedLiteral_addedNodes_le builder
            (references index) (weights index)
      have haddition :
          addition.extension.suffix.length = 11 * sumBits.length := by
        simpa only [addition, DAGBitListResult.addedNodes,
          oldSum, List.length_map] using
          buildRippleAdd_addedNodes literal.final oldSum term
            (by simp [oldSum, term]) zeroInLiteral
      have hadditionLength :
          addition.bits.length = sumBits.length + 1 := by
        simpa only [addition, oldSum, List.length_map] using
          buildRippleAdd_bits_length literal.final oldSum term
            (by simp [oldSum, term]) zeroInLiteral
      have htail :
          tail.extension.suffix.length ≤
            indices.length *
              (11 * (addition.bits.length + indices.length) + 1) := by
        simpa only [tail, DAGBitListResult.addedNodes] using ih
      simp only [DAGBitListResult.addedNodes,
        BooleanDAGExtension.trans, List.length_append,
        List.length_cons]
      rw [hadditionLength] at htail
      nlinarith

theorem buildWeightedSum_value {n m : ℕ}
    (weights : Fin m → ℤ) (builder : BooleanDAGBuilder n)
    (zero : Fin builder.nodes.length)
    (references : Fin m → Fin builder.nodes.length)
    (sumBits : List (Fin builder.nodes.length))
    (indices : List (Fin m)) (input : BitInput n)
    (hzero : wireValue builder input zero = false)
    (hweight : ∀ index, (weights index).natAbs < 2 ^ sumBits.length) :
    bitListValue
        (readWires
          (buildWeightedSum weights builder zero references
            sumBits indices).final input
          (buildWeightedSum weights builder zero references
            sumBits indices).bits) =
      bitListValue (readWires builder input sumBits) +
        shiftedListScore weights
          (fun index => wireValue builder input (references index))
          indices := by
  fun_induction buildWeightedSum with
  | case1 => simp [shiftedListScore]
  | case2 builder zero references sumBits index indices literal
      zeroInLiteral oldSum term addition tail ih =>
      have hzeroLiteral :
          wireValue literal.final input zeroInLiteral = false := by
        simpa only [zeroInLiteral, wireValue_extension] using hzero
      have holdSum :
          readWires literal.final input oldSum =
            readWires builder input sumBits := by
        simpa only [oldSum] using
          readWires_lift literal.extension input sumBits
      have hliteral :
          wireValue literal.final input (literal.output 0) =
            shiftedLiteral (weights index)
              (wireValue builder input (references index)) := by
        simpa only [literal] using
          buildShiftedLiteral_value builder
            (references index) (weights index) input
      have hterm :
          bitListValue (readWires literal.final input term) =
            (weights index).natAbs *
              (shiftedLiteral (weights index)
                (wireValue builder input (references index))).toNat := by
        rw [show readWires literal.final input term =
            (fixedBits sumBits.length (weights index).natAbs).map
              (fun bit => bit &&
                wireValue literal.final input (literal.output 0)) by
          simpa only [term] using
            read_selectBitWires literal.final input
              (fixedBits sumBits.length (weights index).natAbs)
              (literal.output 0) zeroInLiteral hzeroLiteral]
        rw [bitListValue_map_and, hliteral,
          fixedBits_value_of_lt_pow _ _ (hweight index)]
      have hadditionLength :
          addition.bits.length = sumBits.length + 1 := by
        simpa only [addition, oldSum, List.length_map] using
          buildRippleAdd_bits_length literal.final oldSum term
            (by simp [oldSum, term]) zeroInLiteral
      have hweightTail :
          ∀ next, (weights next).natAbs <
            2 ^ addition.bits.length := by
        intro next
        apply lt_of_lt_of_le (hweight next)
        exact Nat.pow_le_pow_right (by omega) (by
          rw [hadditionLength]
          omega)
      have hzeroAddition :
          wireValue addition.final input
              (addition.extension.lift zeroInLiteral) = false := by
        simpa only [wireValue_extension] using hzeroLiteral
      have hrefAddition :
          ∀ next,
            wireValue addition.final input
                (addition.extension.lift
                  (literal.extension.lift (references next))) =
              wireValue builder input (references next) := by
        intro next
        simp only [wireValue_extension]
      have htail :
          bitListValue (readWires tail.final input tail.bits) =
            bitListValue
                (readWires addition.final input addition.bits) +
              shiftedListScore weights
                (fun next =>
                  wireValue addition.final input
                    (addition.extension.lift
                      (literal.extension.lift (references next))))
                indices := by
        simpa only [tail] using
          ih hzeroAddition hweightTail
      have haddition :
          bitListValue (readWires addition.final input addition.bits) =
            bitListValue (readWires builder input sumBits) +
              (weights index).natAbs *
                (shiftedLiteral (weights index)
                  (wireValue builder input (references index))).toNat := by
        rw [buildRippleAdd_value, hzeroLiteral, Bool.toNat_false,
          Nat.add_zero, holdSum, hterm]
      change bitListValue (readWires tail.final input tail.bits) =
        bitListValue (readWires builder input sumBits) +
          shiftedListScore weights
            (fun next => wireValue builder input (references next))
            (index :: indices)
      rw [htail, haddition]
      simp only [shiftedListScore, hrefAddition]
      omega

def allIndices (n : ℕ) : List (Fin n) :=
  List.ofFn id

@[simp] theorem allIndices_length (n : ℕ) :
    (allIndices n).length = n := by
  simp [allIndices]

theorem shiftedListScore_eq_sum {n : ℕ}
    (weights : Fin n → ℤ) (input : Fin n → Bool)
    (indices : List (Fin n)) :
    shiftedListScore weights input indices =
      (indices.map fun index =>
        (weights index).natAbs *
          (shiftedLiteral (weights index) (input index)).toNat).sum := by
  induction indices with
  | nil => rfl
  | cons index indices ih =>
      simp [shiftedListScore, ih]

theorem shiftedListScore_allIndices {n : ℕ}
    (gate : NormalizedThresholdGate n) (input : BitInput n) :
    shiftedListScore gate.weight input (allIndices n) =
      shiftedScore gate input := by
  rw [shiftedListScore_eq_sum]
  simp [allIndices, shiftedScore, List.sum_ofFn]

theorem bitListValue_lt_pow (bits : List Bool) :
    bitListValue bits < 2 ^ bits.length := by
  induction bits with
  | nil => decide
  | cons bit bits ih =>
      simp only [bitListValue_cons, List.length_cons, pow_succ]
      have hbit : bit.toNat ≤ 1 := by
        cases bit <;> decide
      omega

@[simp] theorem bitListValue_replicate_false (count : ℕ) :
    bitListValue (List.replicate count false) = 0 := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [List.replicate_succ, bitListValue_cons, ih]
      rfl

/-- Quadratic bit width sufficient for the support-normalized
`n^n` coefficient bound. -/
def normalizedGateWidth (n : ℕ) : ℕ :=
  (n + 1) ^ 2 + 1

theorem self_le_two_pow (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      have hpositive : 0 < 2 ^ n := pow_pos (by omega) _
      omega

theorem boundedParameter_fits_width {n : ℕ}
    (value : ℕ) (hvalue : value ≤ n ^ n) :
    value < 2 ^ normalizedGateWidth n := by
  have hbase : n ^ n ≤ (2 ^ n) ^ n :=
    Nat.pow_le_pow_left (self_le_two_pow n) n
  have hexponent : n * n < normalizedGateWidth n := by
    simp [normalizedGateWidth, pow_two]
    nlinarith
  calc
    value ≤ n ^ n := hvalue
    _ ≤ (2 ^ n) ^ n := hbase
    _ = 2 ^ (n * n) := by rw [pow_mul]
    _ < 2 ^ normalizedGateWidth n :=
      Nat.pow_lt_pow_right (by omega) hexponent

/-- Compile one support-normalized integer threshold gate over already-built
input wires.  A nonpositive shifted threshold is constant true; a threshold
outside the accumulator range is constant false. -/
def buildNormalizedGate {n m : ℕ}
    (builder : BooleanDAGBuilder n)
    (zero : Fin builder.nodes.length)
    (references : Fin m → Fin builder.nodes.length)
    (gate : NormalizedThresholdGate m) :
    BooleanDAGBuildResult builder 1 :=
  let width := normalizedGateWidth m
  let sum := buildWeightedSum gate.weight builder zero references
    (List.replicate width zero) (allIndices m)
  let shiftedThreshold := gate.threshold + (negativeMass gate : ℤ)
  if shiftedThreshold ≤ 0 then
    let output := buildConst sum.final true
    { final := output.final
      extension := sum.extension.trans output.extension
      output := output.output }
  else
    let target := shiftedThreshold.toNat
    if target < 2 ^ sum.bits.length then
      let comparison := buildCompareConstant sum.final sum.bits target
      let output := buildOr comparison.final
        (comparison.output 0) (comparison.output 1)
      { final := output.final
        extension := sum.extension.trans
          (comparison.extension.trans output.extension)
        output := output.output }
    else
      let output := buildConst sum.final false
      { final := output.final
        extension := sum.extension.trans output.extension
        output := output.output }

theorem buildNormalizedGate_value {n m : ℕ}
    (builder : BooleanDAGBuilder n)
    (zero : Fin builder.nodes.length)
    (references : Fin m → Fin builder.nodes.length)
    (gate : NormalizedThresholdGate m)
    (hbound : gate.parametersBoundedBy (m ^ m))
    (input : BitInput n)
    (hzero : wireValue builder input zero = false) :
    wireValue (buildNormalizedGate builder zero references gate).final input
        ((buildNormalizedGate builder zero references gate).output 0) =
      gate.eval
        (fun index => wireValue builder input (references index)) := by
  let width := normalizedGateWidth m
  let sum := buildWeightedSum gate.weight builder zero references
    (List.replicate width zero) (allIndices m)
  let shiftedThreshold := gate.threshold + (negativeMass gate : ℤ)
  have hweights :
      ∀ index, (gate.weight index).natAbs < 2 ^ width := by
    intro index
    exact boundedParameter_fits_width _ (hbound.1 index)
  have hinitial :
      bitListValue
          (readWires builder input (List.replicate width zero)) = 0 := by
    rw [show readWires builder input (List.replicate width zero) =
        List.replicate width (wireValue builder input zero) by
      simp [readWires]]
    rw [hzero, bitListValue_replicate_false]
  have hsum :
      bitListValue (readWires sum.final input sum.bits) =
        shiftedScore gate
          (fun index => wireValue builder input (references index)) := by
    have hcompiled := buildWeightedSum_value gate.weight builder zero
      references (List.replicate width zero) (allIndices m) input
      hzero (by simpa only [List.length_replicate] using hweights)
    simpa only [sum, hinitial, zero_add,
      shiftedListScore_allIndices] using hcompiled
  rw [buildNormalizedGate]
  by_cases hnonpositive :
      gate.threshold + (negativeMass gate : ℤ) ≤ 0
  · rw [if_pos hnonpositive]
    rw [buildConst_value]
    rw [normalized_eval_eq_shifted]
    have hscoreNonnegative :
        (0 : ℤ) ≤ shiftedScore gate
          (fun index => wireValue builder input (references index)) := by
      exact Int.natCast_nonneg _
    have haccepts :
        gate.threshold + (negativeMass gate : ℤ) ≤
          (shiftedScore gate
            (fun index => wireValue builder input (references index)) : ℤ) :=
      le_trans hnonpositive hscoreNonnegative
    simp [haccepts]
  · rw [if_neg hnonpositive]
    by_cases hfits :
        (gate.threshold + (negativeMass gate : ℤ)).toNat <
          2 ^ sum.bits.length
    · rw [if_pos (by simpa only [sum] using hfits)]
      let comparison := buildCompareConstant sum.final sum.bits
        shiftedThreshold.toNat
      have hcomparison :
          (wireValue comparison.final input (comparison.output 0),
            wireValue comparison.final input (comparison.output 1)) =
          compareBitList (readWires sum.final input sum.bits)
            shiftedThreshold.toNat := by
        simpa only [comparison] using
          buildCompareConstant_values sum.final sum.bits
            shiftedThreshold.toNat input
      have haccept :
          (wireValue comparison.final input (comparison.output 0) ||
              wireValue comparison.final input (comparison.output 1)) =
            compareAtLeast (readWires sum.final input sum.bits)
              shiftedThreshold.toNat := by
        simpa only [compareAtLeast] using
          congrArg (fun pair => pair.1 || pair.2) hcomparison
      have hcompareFits :
          shiftedThreshold.toNat <
            2 ^ (readWires sum.final input sum.bits).length := by
        simpa only [shiftedThreshold, readWires, List.length_map] using hfits
      rw [buildOr_value, haccept,
        compareAtLeast_correct _ _ hcompareFits, hsum,
        normalized_eval_eq_shifted]
      apply decide_eq_decide.mpr
      have hthresholdPositive : 0 < shiftedThreshold :=
        lt_of_not_ge hnonpositive
      have hthresholdCast :
          (shiftedThreshold.toNat : ℤ) = shiftedThreshold := by
        exact Int.toNat_of_nonneg (le_of_lt hthresholdPositive)
      change shiftedThreshold.toNat ≤
          shiftedScore gate
            (fun index => wireValue builder input (references index)) ↔
        shiftedThreshold ≤
          (shiftedScore gate
            (fun index => wireValue builder input (references index)) : ℤ)
      constructor
      · intro hnatural
        have hinteger :
            (shiftedThreshold.toNat : ℤ) ≤
              (shiftedScore gate
                (fun index =>
                  wireValue builder input (references index)) : ℤ) := by
          exact_mod_cast hnatural
        rwa [hthresholdCast] at hinteger
      · intro hinteger
        have hcast :
            (shiftedThreshold.toNat : ℤ) ≤
              (shiftedScore gate
                (fun index =>
                  wireValue builder input (references index)) : ℤ) := by
          rwa [hthresholdCast]
        exact_mod_cast hcast
    · rw [if_neg (by simpa only [sum] using hfits)]
      rw [buildConst_value, normalized_eval_eq_shifted]
      have hscoreRange :
          shiftedScore gate
              (fun index => wireValue builder input (references index)) <
            shiftedThreshold.toNat := by
        rw [← hsum]
        have hvalueRange :=
          bitListValue_lt_pow
            (readWires sum.final input sum.bits)
        have hlength :
            (readWires sum.final input sum.bits).length =
              sum.bits.length := by
          simp [readWires]
        rw [hlength] at hvalueRange
        exact lt_of_lt_of_le hvalueRange
          (le_of_not_gt (by
            simpa only [shiftedThreshold] using hfits))
      have hthresholdPositive : 0 < shiftedThreshold :=
        lt_of_not_ge hnonpositive
      have hthresholdCast :
          (shiftedThreshold.toNat : ℤ) = shiftedThreshold :=
        Int.toNat_of_nonneg (le_of_lt hthresholdPositive)
      have hrejected :
          ¬shiftedThreshold ≤
            (shiftedScore gate
              (fun index =>
                wireValue builder input (references index)) : ℤ) := by
        rw [← hthresholdCast]
        exact_mod_cast Nat.not_le.mpr hscoreRange
      simp [shiftedThreshold, hrejected]

theorem buildNormalizedGate_addedNodes_le {n m : ℕ}
    (builder : BooleanDAGBuilder n)
    (zero : Fin builder.nodes.length)
    (references : Fin m → Fin builder.nodes.length)
    (gate : NormalizedThresholdGate m) :
    (buildNormalizedGate builder zero references gate).addedNodes ≤
      m * (11 * (normalizedGateWidth m + m) + 1) +
        4 * (normalizedGateWidth m + m) + 3 := by
  let width := normalizedGateWidth m
  let sum := buildWeightedSum gate.weight builder zero references
    (List.replicate width zero) (allIndices m)
  have hsumLength :
      sum.bits.length = width + m := by
    simpa only [sum, List.length_replicate, allIndices_length] using
      buildWeightedSum_bits_length gate.weight builder zero references
        (List.replicate width zero) (allIndices m)
  have hsum :
      sum.extension.suffix.length ≤
        m * (11 * (width + m) + 1) := by
    simpa only [sum, DAGBitListResult.addedNodes,
      List.length_replicate, allIndices_length] using
      buildWeightedSum_addedNodes_le gate.weight builder zero references
        (List.replicate width zero) (allIndices m)
  rw [buildNormalizedGate]
  by_cases hnonpositive :
      gate.threshold + (negativeMass gate : ℤ) ≤ 0
  · rw [if_pos hnonpositive]
    simp only [BooleanDAGBuildResult.addedNodes,
      BooleanDAGExtension.trans, List.length_append]
    change sum.extension.suffix.length +
        (buildConst sum.final true).extension.suffix.length ≤ _
    have houtput :
        (buildConst sum.final true).extension.suffix.length = 1 := by
      simpa only [BooleanDAGBuildResult.addedNodes] using
        buildConst_addedNodes sum.final true
    dsimp only [width] at hsum ⊢
    omega
  · rw [if_neg hnonpositive]
    by_cases hfits :
        (gate.threshold + (negativeMass gate : ℤ)).toNat <
          2 ^ sum.bits.length
    · rw [if_pos (by simpa only [sum] using hfits)]
      simp only [BooleanDAGBuildResult.addedNodes,
        BooleanDAGExtension.trans, List.length_append]
      let comparison := buildCompareConstant sum.final sum.bits
        (gate.threshold + (negativeMass gate : ℤ)).toNat
      let output := buildOr comparison.final
        (comparison.output 0) (comparison.output 1)
      change sum.extension.suffix.length +
          (comparison.extension.suffix.length +
            output.extension.suffix.length) ≤ _
      have hcomparison :
          comparison.extension.suffix.length ≤
            4 * sum.bits.length + 2 := by
        simpa only [comparison, BooleanDAGBuildResult.addedNodes] using
          buildCompareConstant_addedNodes_le sum.final sum.bits
            (gate.threshold + (negativeMass gate : ℤ)).toNat
      have houtput : output.extension.suffix.length = 1 := by
        simpa only [output, BooleanDAGBuildResult.addedNodes] using
          buildOr_addedNodes comparison.final
            (comparison.output 0) (comparison.output 1)
      rw [hsumLength] at hcomparison
      dsimp only [width] at hsum hcomparison ⊢
      omega
    · rw [if_neg (by simpa only [sum] using hfits)]
      simp only [BooleanDAGBuildResult.addedNodes,
        BooleanDAGExtension.trans, List.length_append]
      change sum.extension.suffix.length +
          (buildConst sum.final false).extension.suffix.length ≤ _
      have houtput :
          (buildConst sum.final false).extension.suffix.length = 1 := by
        simpa only [BooleanDAGBuildResult.addedNodes] using
          buildConst_addedNodes sum.final false
      dsimp only [width] at hsum ⊢
      omega

theorem buildNormalizedGate_addedNodes_polynomial {n m : ℕ}
    (builder : BooleanDAGBuilder n)
    (zero : Fin builder.nodes.length)
    (references : Fin m → Fin builder.nodes.length)
    (gate : NormalizedThresholdGate m) :
    (buildNormalizedGate builder zero references gate).addedNodes ≤
      20 * (m + 2) ^ 3 := by
  apply le_trans
    (buildNormalizedGate_addedNodes_le builder zero references gate)
  unfold normalizedGateWidth
  nlinarith [sq_nonneg (m : ℤ)]

/-! ## Canonical input and gate-vector builders -/

def buildInputList {n : ℕ} (builder : BooleanDAGBuilder n) :
    List (Fin n) → DAGBitListResult builder
  | [] =>
      { final := builder
        extension := BooleanDAGExtension.refl builder
        bits := [] }
  | index :: indices =>
      let head := buildInput builder index
      let tail := buildInputList head.final indices
      { final := tail.final
        extension := head.extension.trans tail.extension
        bits := tail.extension.lift (head.output 0) :: tail.bits }

@[simp] theorem buildInputList_bits_length {n : ℕ}
    (builder : BooleanDAGBuilder n) (indices : List (Fin n)) :
    (buildInputList builder indices).bits.length = indices.length := by
  induction indices generalizing builder with
  | nil => rfl
  | cons index indices ih =>
      simp only [buildInputList, List.length_cons]
      rw [ih]

@[simp] theorem buildInputList_addedNodes {n : ℕ}
    (builder : BooleanDAGBuilder n) (indices : List (Fin n)) :
    (buildInputList builder indices).addedNodes = indices.length := by
  induction indices generalizing builder with
  | nil =>
      simp [buildInputList, DAGBitListResult.addedNodes,
        BooleanDAGExtension.refl]
  | cons index indices ih =>
      let head := buildInput builder index
      let tail := buildInputList head.final indices
      simp only [buildInputList, DAGBitListResult.addedNodes,
        BooleanDAGExtension.trans, List.length_append]
      change head.extension.suffix.length +
        tail.extension.suffix.length = (index :: indices).length
      have hhead : head.extension.suffix.length = 1 := by
        simpa only [head, BooleanDAGBuildResult.addedNodes] using
          buildInput_addedNodes builder index
      have htail : tail.extension.suffix.length = indices.length := by
        simpa only [tail, DAGBitListResult.addedNodes] using
          ih head.final
      simp only [List.length_cons]
      omega

theorem buildInputList_values {n : ℕ}
    (builder : BooleanDAGBuilder n) (indices : List (Fin n))
    (input : BitInput n) :
    readWires (buildInputList builder indices).final input
        (buildInputList builder indices).bits =
      indices.map input := by
  induction indices generalizing builder with
  | nil => rfl
  | cons index indices ih =>
      let head := buildInput builder index
      let tail := buildInputList head.final indices
      change
        wireValue tail.final input
            (tail.extension.lift (head.output 0)) ::
          readWires tail.final input tail.bits =
        input index :: indices.map input
      congr 1
      · rw [wireValue_extension]
        simpa only [head] using buildInput_value builder index input
      · simpa only [tail] using ih head.final

def buildAllInputs {n : ℕ} (builder : BooleanDAGBuilder n) :
    BooleanDAGBuildResult builder n :=
  let result := buildInputList builder (allIndices n)
  { final := result.final
    extension := result.extension
    output := fun index =>
      result.bits.get
        ⟨index.val, by
          rw [buildInputList_bits_length, allIndices_length]
          exact index.isLt⟩ }

@[simp] theorem buildAllInputs_addedNodes {n : ℕ}
    (builder : BooleanDAGBuilder n) :
    (buildAllInputs builder).addedNodes = n := by
  change
    (buildInputList builder (allIndices n)).extension.suffix.length = n
  simpa only [DAGBitListResult.addedNodes, allIndices_length] using
    buildInputList_addedNodes builder (allIndices n)

theorem buildAllInputs_value {n : ℕ}
    (builder : BooleanDAGBuilder n) (index : Fin n)
    (input : BitInput n) :
    wireValue (buildAllInputs builder).final input
        ((buildAllInputs builder).output index) =
      input index := by
  let result := buildInputList builder (allIndices n)
  have hvalues :
      readWires result.final input result.bits =
        (allIndices n).map input := by
    simpa only [result] using
      buildInputList_values builder (allIndices n) input
  have hget := congrArg
    (fun values : List Bool => values[index.val]?) hvalues
  change
    wireValue result.final input
        (result.bits.get
          ⟨index.val, by
            rw [buildInputList_bits_length, allIndices_length]
            exact index.isLt⟩) =
      input index
  have hsome :
      some
          (wireValue result.final input
            (result.bits.get
              ⟨index.val, by
                rw [buildInputList_bits_length, allIndices_length]
                exact index.isLt⟩)) =
        some (input index) := by
    simpa [readWires, result, allIndices] using hget
  exact Option.some.inj hsome

def falseInput (n : ℕ) : BitInput n :=
  fun _ => false

def retainedGateValue {n k : ℕ}
    (gates : Fin k → SupportedNormalizedGate n)
    (retain : Fin k → Bool) (input : BitInput n)
    (index : Fin k) : Bool :=
  if retain index then
    (gates index).eval input
  else
    (gates index).eval (falseInput n)

/-- Compile selected supported gates and replace unselected gates by their
all-false value.  The latter is used only where the caller has proved that the
gate is constant or semantically ignored by the top layer. -/
def buildGateList {n k : ℕ}
    (gates : Fin k → SupportedNormalizedGate n)
    (retain : Fin k → Bool)
    (builder : BooleanDAGBuilder n)
    (zero one : Fin builder.nodes.length)
    (references : Fin n → Fin builder.nodes.length) :
    List (Fin k) → DAGBitListResult builder
  | [] =>
      { final := builder
        extension := BooleanDAGExtension.refl builder
        bits := [] }
  | index :: indices =>
      if retain index then
        let head := buildNormalizedGate builder zero references
          (gates index).gate
        let tail := buildGateList gates retain head.final
          (head.extension.lift zero) (head.extension.lift one)
          (fun inputIndex => head.extension.lift (references inputIndex))
          indices
        { final := tail.final
          extension := head.extension.trans tail.extension
          bits := tail.extension.lift (head.output 0) :: tail.bits }
      else
        let value := (gates index).eval (falseInput n)
        let reference := if value then one else zero
        let tail := buildGateList gates retain builder zero one
          references indices
        { final := tail.final
          extension := tail.extension
          bits := tail.extension.lift reference :: tail.bits }

@[simp] theorem buildGateList_bits_length {n k : ℕ}
    (gates : Fin k → SupportedNormalizedGate n)
    (retain : Fin k → Bool)
    (builder : BooleanDAGBuilder n)
    (zero one : Fin builder.nodes.length)
    (references : Fin n → Fin builder.nodes.length)
    (indices : List (Fin k)) :
    (buildGateList gates retain builder zero one references
      indices).bits.length = indices.length := by
  induction indices generalizing builder with
  | nil => rfl
  | cons index indices ih =>
      simp only [buildGateList]
      by_cases hretain : retain index = true
      · rw [if_pos hretain]
        simp only [List.length_cons]
        rw [ih]
      · rw [if_neg hretain]
        simp only [List.length_cons]
        rw [ih]

theorem buildGateList_addedNodes_le {n k : ℕ}
    (gates : Fin k → SupportedNormalizedGate n)
    (retain : Fin k → Bool)
    (builder : BooleanDAGBuilder n)
    (zero one : Fin builder.nodes.length)
    (references : Fin n → Fin builder.nodes.length)
    (indices : List (Fin k)) :
    (buildGateList gates retain builder zero one references
        indices).addedNodes ≤
      (indices.filter fun index => retain index).length *
        (20 * (n + 2) ^ 3) := by
  induction indices generalizing builder with
  | nil =>
      simp [buildGateList, DAGBitListResult.addedNodes,
        BooleanDAGExtension.refl]
  | cons index indices ih =>
      simp only [buildGateList]
      by_cases hretain : retain index = true
      · rw [if_pos hretain]
        let head := buildNormalizedGate builder zero references
          (gates index).gate
        let tail := buildGateList gates retain head.final
          (head.extension.lift zero) (head.extension.lift one)
          (fun inputIndex => head.extension.lift (references inputIndex))
          indices
        simp only [DAGBitListResult.addedNodes,
          BooleanDAGExtension.trans, List.length_append]
        have hhead :
            head.extension.suffix.length ≤ 20 * (n + 2) ^ 3 := by
          simpa only [head, BooleanDAGBuildResult.addedNodes] using
            buildNormalizedGate_addedNodes_polynomial builder zero
              references (gates index).gate
        have htail :
            tail.extension.suffix.length ≤
              (indices.filter fun next => retain next).length *
                (20 * (n + 2) ^ 3) := by
          simpa only [tail, DAGBitListResult.addedNodes] using
            ih head.final
              (head.extension.lift zero) (head.extension.lift one)
              (fun inputIndex =>
                head.extension.lift (references inputIndex))
        simp [hretain]
        nlinarith
      · rw [if_neg hretain]
        simp only [DAGBitListResult.addedNodes]
        simpa [hretain, DAGBitListResult.addedNodes] using
          ih builder zero one references

theorem buildGateList_values {n k : ℕ}
    (gates : Fin k → SupportedNormalizedGate n)
    (retain : Fin k → Bool)
    (builder : BooleanDAGBuilder n)
    (zero one : Fin builder.nodes.length)
    (references : Fin n → Fin builder.nodes.length)
    (indices : List (Fin k)) (input : BitInput n)
    (hbound :
      ∀ index, (gates index).gate.parametersBoundedBy (n ^ n))
    (hzero : wireValue builder input zero = false)
    (hone : wireValue builder input one = true) :
    readWires
        (buildGateList gates retain builder zero one references indices).final
        input
        (buildGateList gates retain builder zero one references indices).bits =
      indices.map
        (retainedGateValue gates retain
          (fun inputIndex =>
            wireValue builder input (references inputIndex))) := by
  induction indices generalizing builder with
  | nil => rfl
  | cons index indices ih =>
      simp only [buildGateList]
      by_cases hretain : retain index = true
      · rw [if_pos hretain]
        let head := buildNormalizedGate builder zero references
          (gates index).gate
        let tail := buildGateList gates retain head.final
          (head.extension.lift zero) (head.extension.lift one)
          (fun inputIndex => head.extension.lift (references inputIndex))
          indices
        change
          wireValue tail.final input
              (tail.extension.lift (head.output 0)) ::
            readWires tail.final input tail.bits =
          retainedGateValue gates retain
              (fun inputIndex =>
                wireValue builder input (references inputIndex)) index ::
            indices.map
              (retainedGateValue gates retain
                (fun inputIndex =>
                  wireValue builder input (references inputIndex)))
        congr 1
        · rw [wireValue_extension]
          simpa only [head, retainedGateValue, hretain, if_true,
            SupportedNormalizedGate.eval] using
            buildNormalizedGate_value builder zero references
              (gates index).gate (hbound index) input hzero
        · have htail := ih head.final
              (head.extension.lift zero)
              (head.extension.lift one)
              (fun inputIndex =>
                head.extension.lift (references inputIndex))
              (by simpa only [wireValue_extension] using hzero)
              (by simpa only [wireValue_extension] using hone)
          simpa only [tail, retainedGateValue, wireValue_extension] using
            htail
      · have hfalse : retain index = false :=
          Bool.eq_false_of_not_eq_true hretain
        rw [if_neg hretain]
        let value := (gates index).eval (falseInput n)
        let reference := if value then one else zero
        let tail := buildGateList gates retain builder zero one
          references indices
        change
          wireValue tail.final input (tail.extension.lift reference) ::
              readWires tail.final input tail.bits =
            retainedGateValue gates retain
                (fun inputIndex =>
                  wireValue builder input (references inputIndex)) index ::
              indices.map
                (retainedGateValue gates retain
                  (fun inputIndex =>
                    wireValue builder input (references inputIndex)))
        congr 1
        · rw [wireValue_extension]
          unfold reference value retainedGateValue
          simp only [hfalse, Bool.false_eq]
          cases _hvalue : (gates index).eval (falseInput n) <;>
            simp [hzero, hone]
        · simpa only [tail] using
            ih builder zero one references hzero hone

def retainedCount {k : ℕ} (retain : Fin k → Bool) : ℕ :=
  ((allIndices k).filter fun index => retain index).length

def buildGateVector {n k : ℕ}
    (gates : Fin k → SupportedNormalizedGate n)
    (retain : Fin k → Bool)
    (builder : BooleanDAGBuilder n)
    (zero one : Fin builder.nodes.length)
    (references : Fin n → Fin builder.nodes.length) :
    BooleanDAGBuildResult builder k :=
  let result := buildGateList gates retain builder zero one references
    (allIndices k)
  { final := result.final
    extension := result.extension
    output := fun index =>
      result.bits.get
        ⟨index.val, by
          rw [buildGateList_bits_length, allIndices_length]
          exact index.isLt⟩ }

theorem buildGateVector_addedNodes_le {n k : ℕ}
    (gates : Fin k → SupportedNormalizedGate n)
    (retain : Fin k → Bool)
    (builder : BooleanDAGBuilder n)
    (zero one : Fin builder.nodes.length)
    (references : Fin n → Fin builder.nodes.length) :
    (buildGateVector gates retain builder zero one references).addedNodes ≤
      retainedCount retain * (20 * (n + 2) ^ 3) := by
  change
    (buildGateList gates retain builder zero one references
      (allIndices k)).extension.suffix.length ≤ _
  simpa only [DAGBitListResult.addedNodes, retainedCount] using
    buildGateList_addedNodes_le gates retain builder zero one references
      (allIndices k)

theorem buildGateVector_value {n k : ℕ}
    (gates : Fin k → SupportedNormalizedGate n)
    (retain : Fin k → Bool)
    (builder : BooleanDAGBuilder n)
    (zero one : Fin builder.nodes.length)
    (references : Fin n → Fin builder.nodes.length)
    (index : Fin k) (input : BitInput n)
    (hbound :
      ∀ gateIndex, (gates gateIndex).gate.parametersBoundedBy (n ^ n))
    (hzero : wireValue builder input zero = false)
    (hone : wireValue builder input one = true) :
    wireValue
        (buildGateVector gates retain builder zero one references).final input
        ((buildGateVector gates retain builder zero one references).output
          index) =
      retainedGateValue gates retain
        (fun inputIndex =>
          wireValue builder input (references inputIndex)) index := by
  let result := buildGateList gates retain builder zero one references
    (allIndices k)
  have hvalues :
      readWires result.final input result.bits =
        (allIndices k).map
          (retainedGateValue gates retain
            (fun inputIndex =>
              wireValue builder input (references inputIndex))) := by
    simpa only [result] using
      buildGateList_values gates retain builder zero one references
        (allIndices k) input hbound hzero hone
  have hget := congrArg
    (fun values : List Bool => values[index.val]?) hvalues
  change
    wireValue result.final input
        (result.bits.get
          ⟨index.val, by
            rw [buildGateList_bits_length, allIndices_length]
            exact index.isLt⟩) =
      retainedGateValue gates retain
        (fun inputIndex =>
          wireValue builder input (references inputIndex)) index
  have hsome :
      some
          (wireValue result.final input
            (result.bits.get
              ⟨index.val, by
                rw [buildGateList_bits_length, allIndices_length]
                exact index.isLt⟩)) =
        some
          (retainedGateValue gates retain
            (fun inputIndex =>
              wireValue builder input (references inputIndex)) index) := by
    simpa [readWires, result, allIndices] using hget
  exact Option.some.inj hsome

theorem supportedGate_eval_of_support_empty {n : ℕ}
    (gate : SupportedNormalizedGate n)
    (hempty : gate.support = ∅) (input : BitInput n) :
    gate.eval input = gate.eval (falseInput n) := by
  have hweight : ∀ index, gate.gate.weight index = 0 := by
    intro index
    exact gate.zeroOutside index (by simp [hempty])
  simp [SupportedNormalizedGate.eval, NormalizedThresholdGate.eval,
    hweight, falseInput]

def retainNonconstant {n k : ℕ}
    (gates : Fin k → SupportedNormalizedGate n) (index : Fin k) : Bool :=
  decide (gates index).support.Nonempty

theorem retainedGateValue_nonconstant {n k : ℕ}
    (gates : Fin k → SupportedNormalizedGate n)
    (input : BitInput n) (index : Fin k) :
    retainedGateValue gates (retainNonconstant gates) input index =
      (gates index).eval input := by
  by_cases hnonempty : (gates index).support.Nonempty
  · simp [retainedGateValue, retainNonconstant, hnonempty]
  · have hempty : (gates index).support = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hnonempty
    simp [retainedGateValue, retainNonconstant, hnonempty,
      supportedGate_eval_of_support_empty (gates index) hempty input]

/-! ## Hamming count and arbitrary symmetric lookup -/

def buildHammingCount {n k : ℕ}
    (builder : BooleanDAGBuilder n)
    (zero : Fin builder.nodes.length)
    (references : Fin k → Fin builder.nodes.length) :
    DAGBitListResult builder :=
  buildWeightedSum (fun _ : Fin k => (1 : ℤ)) builder zero references
    [zero] (allIndices k)

theorem shiftedScore_one_eq_card {k : ℕ} (input : BitInput k) :
    shiftedScore
        ({ weight := fun _ => 1
           threshold := 0 } : NormalizedThresholdGate k) input =
      (Finset.univ.filter fun index => input index).card := by
  unfold shiftedScore
  simp only [shiftedLiteral, Int.reduceLT, if_false, Int.natAbs_one,
    one_mul]
  rw [Finset.card_eq_sum_ones]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro index _
  cases input index <;> rfl

theorem shiftedListScore_one_eq_card {k : ℕ} (input : BitInput k) :
    shiftedListScore (fun _ : Fin k => (1 : ℤ)) input (allIndices k) =
      (Finset.univ.filter fun index => input index).card := by
  have hscore := shiftedListScore_allIndices
    ({ weight := fun _ => 1
       threshold := 0 } : NormalizedThresholdGate k) input
  rw [shiftedScore_one_eq_card] at hscore
  exact hscore

theorem buildHammingCount_value {n k : ℕ}
    (builder : BooleanDAGBuilder n)
    (zero : Fin builder.nodes.length)
    (references : Fin k → Fin builder.nodes.length)
    (input : BitInput n)
    (hzero : wireValue builder input zero = false) :
    bitListValue
        (readWires (buildHammingCount builder zero references).final input
          (buildHammingCount builder zero references).bits) =
      (Finset.univ.filter fun index =>
        wireValue builder input (references index)).card := by
  have hcompiled := buildWeightedSum_value
    (fun _ : Fin k => (1 : ℤ)) builder zero references
    [zero] (allIndices k) input hzero (by
      intro index
      norm_num)
  rw [show bitListValue (readWires builder input [zero]) = 0 by
    simp [readWires, bitListValue, hzero]] at hcompiled
  rw [zero_add, shiftedListScore_one_eq_card] at hcompiled
  simpa only [buildHammingCount] using hcompiled

theorem buildHammingCount_addedNodes_le {n k : ℕ}
    (builder : BooleanDAGBuilder n)
    (zero : Fin builder.nodes.length)
    (references : Fin k → Fin builder.nodes.length) :
    (buildHammingCount builder zero references).addedNodes ≤
      k * (11 * (k + 1) + 1) := by
  simpa only [buildHammingCount, List.length_cons, List.length_nil,
    zero_add, allIndices_length, Nat.add_comm] using
    buildWeightedSum_addedNodes_le
      (fun _ : Fin k => (1 : ℤ)) builder zero references
      [zero] (allIndices k)

def lookupValue (top : ℕ → Bool) (value : ℕ)
    (initial : Bool) (targets : List ℕ) : Bool :=
  initial ||
    targets.any fun target => top target && decide (target = value)

/-- Compile a finite truth-table lookup using equality outputs from the shared
constant comparator.  The running OR wire prevents a second formula path. -/
def buildLookup {n : ℕ} (top : ℕ → Bool)
    (builder : BooleanDAGBuilder n)
    (bits : List (Fin builder.nodes.length))
    (initial : Fin builder.nodes.length) :
    List ℕ → BooleanDAGBuildResult builder 1
  | [] =>
      { final := builder
        extension := BooleanDAGExtension.refl builder
        output := fun _ => initial }
  | target :: targets =>
      if top target then
        let comparison := buildCompareConstant builder bits target
        let merged := buildOr comparison.final
          (comparison.extension.lift initial) (comparison.output 1)
        let tail := buildLookup top merged.final
          (bits.map fun reference =>
            merged.extension.lift (comparison.extension.lift reference))
          (merged.output 0) targets
        { final := tail.final
          extension := comparison.extension.trans
            (merged.extension.trans tail.extension)
          output := tail.output }
      else
        buildLookup top builder bits initial targets

theorem buildLookup_addedNodes_le {n : ℕ} (top : ℕ → Bool)
    (builder : BooleanDAGBuilder n)
    (bits : List (Fin builder.nodes.length))
    (initial : Fin builder.nodes.length) (targets : List ℕ) :
    (buildLookup top builder bits initial targets).addedNodes ≤
      targets.length * (4 * bits.length + 3) := by
  induction targets generalizing builder bits with
  | nil =>
      simp [buildLookup, BooleanDAGBuildResult.addedNodes,
        BooleanDAGExtension.refl]
  | cons target targets ih =>
      simp only [buildLookup]
      by_cases htop : top target = true
      · rw [if_pos htop]
        let comparison := buildCompareConstant builder bits target
        let merged := buildOr comparison.final
          (comparison.extension.lift initial) (comparison.output 1)
        let tail := buildLookup top merged.final
          (bits.map fun reference =>
            merged.extension.lift (comparison.extension.lift reference))
          (merged.output 0) targets
        simp only [BooleanDAGBuildResult.addedNodes,
          BooleanDAGExtension.trans, List.length_append]
        have hcomparison :
            comparison.extension.suffix.length ≤
              4 * bits.length + 2 := by
          simpa only [comparison, BooleanDAGBuildResult.addedNodes] using
            buildCompareConstant_addedNodes_le builder bits target
        have hmerged : merged.extension.suffix.length = 1 := by
          simpa only [merged, BooleanDAGBuildResult.addedNodes] using
            buildOr_addedNodes comparison.final
              (comparison.extension.lift initial) (comparison.output 1)
        have htail :
            tail.extension.suffix.length ≤
              targets.length * (4 * bits.length + 3) := by
          have := ih merged.final
            (bits.map fun reference =>
              merged.extension.lift (comparison.extension.lift reference))
            (merged.output 0)
          simpa only [tail, List.length_map,
            BooleanDAGBuildResult.addedNodes] using this
        simp only [List.length_cons]
        nlinarith
      · rw [if_neg htop]
        simpa only [List.length_cons] using
          le_trans (ih builder bits initial)
            (Nat.mul_le_mul_right (4 * bits.length + 3)
              (Nat.le_succ targets.length))

theorem buildLookup_value {n : ℕ} (top : ℕ → Bool)
    (builder : BooleanDAGBuilder n)
    (bits : List (Fin builder.nodes.length))
    (initial : Fin builder.nodes.length) (targets : List ℕ)
    (input : BitInput n)
    (hfits : ∀ target ∈ targets, target < 2 ^ bits.length) :
    wireValue (buildLookup top builder bits initial targets).final input
        ((buildLookup top builder bits initial targets).output 0) =
      lookupValue top (bitListValue (readWires builder input bits))
        (wireValue builder input initial) targets := by
  induction targets generalizing builder bits with
  | nil => simp [buildLookup, lookupValue]
  | cons target targets ih =>
      simp only [buildLookup]
      by_cases htop : top target = true
      · rw [if_pos htop]
        let comparison := buildCompareConstant builder bits target
        let merged := buildOr comparison.final
          (comparison.extension.lift initial) (comparison.output 1)
        let liftedBits := bits.map fun reference =>
          merged.extension.lift (comparison.extension.lift reference)
        let tail := buildLookup top merged.final liftedBits
          (merged.output 0) targets
        change wireValue tail.final input (tail.output 0) =
          lookupValue top
            (bitListValue (readWires builder input bits))
            (wireValue builder input initial) (target :: targets)
        have hread :
            readWires merged.final input liftedBits =
              readWires builder input bits := by
          simp [liftedBits, readWires, wireValue_extension]
        have htarget :
            target < 2 ^ (readWires builder input bits).length := by
          simpa only [readWires, List.length_map] using
            hfits target (by simp)
        have hequality :
            wireValue comparison.final input (comparison.output 1) =
              decide
                (target =
                  bitListValue (readWires builder input bits)) := by
          have hpair := buildCompareConstant_values builder bits target input
          rw [compareBitList_correct _ _ htarget] at hpair
          exact congrArg Prod.snd hpair
        have hmerged :
            wireValue merged.final input (merged.output 0) =
              (wireValue builder input initial ||
                decide
                  (target =
                    bitListValue (readWires builder input bits))) := by
          rw [buildOr_value, wireValue_extension, hequality]
        have hfitsTail :
            ∀ next ∈ targets, next < 2 ^ liftedBits.length := by
          intro next hnext
          simpa only [liftedBits, List.length_map] using
            hfits next (by simp [hnext])
        have htail :
            wireValue tail.final input (tail.output 0) =
              lookupValue top
                (bitListValue (readWires merged.final input liftedBits))
                (wireValue merged.final input (merged.output 0)) targets := by
          simpa only [tail] using
            ih merged.final liftedBits (merged.output 0) hfitsTail
        rw [htail, hread, hmerged]
        unfold lookupValue
        simp [htop, Bool.or_assoc]
      · rw [if_neg htop]
        rw [ih builder bits initial (fun next hnext =>
          hfits next (by simp [hnext]))]
        unfold lookupValue
        have hfalse : top target = false :=
          Bool.eq_false_of_not_eq_true htop
        simp [hfalse]

theorem lookupValue_range (top : ℕ → Bool) (value limit : ℕ)
    (hvalue : value < limit) :
    lookupValue top value false (List.range limit) = top value := by
  unfold lookupValue
  simp only [Bool.false_or]
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    List.mem_range]
  constructor
  · rintro ⟨target, _, htop, rfl⟩
    exact htop
  · intro htop
    exact ⟨value, hvalue, htop, rfl⟩

/-! ## Support-compressed two-layer simulations -/

/-- A finite index selected by a decidable support predicate.  Two-layer
simulations enumerate this subtype rather than the raw fan-in, so syntactic
zero-support gates never inflate the Boolean DAG. -/
abbrev SelectedIndex {k : ℕ} (selected : Fin k → Prop) :=
  { index : Fin k // selected index }

def selectedCount {k : ℕ} (selected : Fin k → Prop)
    [DecidablePred selected] : ℕ :=
  Fintype.card (SelectedIndex selected)

/-- Canonical, choice-independent enumeration of a finite selected subtype. -/
noncomputable def selectedIndex {k : ℕ} (selected : Fin k → Prop)
    [DecidablePred selected] :
    Fin (selectedCount selected) → Fin k :=
  fun index =>
    ((Fintype.equivFin (SelectedIndex selected)).symm index).val

theorem selectedIndex_property {k : ℕ} (selected : Fin k → Prop)
    [DecidablePred selected] (index : Fin (selectedCount selected)) :
    selected (selectedIndex selected index) :=
  ((Fintype.equivFin (SelectedIndex selected)).symm index).property

theorem sum_selectedIndex {k : ℕ} (selected : Fin k → Prop)
    [DecidablePred selected] {M : Type} [AddCommMonoid M]
    (value : Fin k → M) :
    (∑ index : Fin (selectedCount selected),
        value (selectedIndex selected index)) =
      ∑ index ∈ Finset.univ.filter selected, value index := by
  classical
  calc
    (∑ index : Fin (selectedCount selected),
        value (selectedIndex selected index)) =
        ∑ index : SelectedIndex selected, value index.val := by
          exact Equiv.sum_comp
            (Fintype.equivFin (SelectedIndex selected)).symm
            (fun index : SelectedIndex selected => value index.val)
    _ = ∑ index ∈ Finset.univ.filter selected, value index := by
      symm
      exact Finset.sum_subtype (Finset.univ.filter selected)
        (by simp) value

theorem bool_filter_card_eq_sum_toNat {k : ℕ}
    (value : Fin k → Bool) :
    (Finset.univ.filter fun index => value index).card =
      ∑ index, (value index).toNat := by
  classical
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro index _
  cases value index <;> rfl

theorem selected_bool_card {k : ℕ} (selected : Fin k → Prop)
    [DecidablePred selected] (value : Fin k → Bool) :
    (Finset.univ.filter fun index : Fin (selectedCount selected) =>
        value (selectedIndex selected index)).card =
      (Finset.univ.filter fun index =>
        selected index ∧ value index).card := by
  classical
  rw [bool_filter_card_eq_sum_toNat]
  rw [sum_selectedIndex selected fun index => (value index).toNat]
  rw [Finset.sum_filter]
  conv_rhs => rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro index _
  by_cases hselected : selected index <;>
    cases value index <;> simp [hselected]

theorem bool_filter_card_partition {k : ℕ}
    (selected : Fin k → Prop) [DecidablePred selected]
    (value : Fin k → Bool) :
    (Finset.univ.filter fun index => value index).card =
      (Finset.univ.filter fun index =>
          ¬selected index ∧ value index).card +
        (Finset.univ.filter fun index =>
          selected index ∧ value index).card := by
  classical
  calc
    (Finset.univ.filter fun index => value index).card =
        ∑ index, if value index then 1 else 0 := by
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = ∑ index, ((if ¬selected index ∧ value index then 1 else 0) +
          (if selected index ∧ value index then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro index _
      by_cases hselected : selected index <;>
        cases value index <;> simp [hselected]
    _ =
        (∑ index,
          if ¬selected index ∧ value index then 1 else 0) +
        (∑ index,
          if selected index ∧ value index then 1 else 0) := by
      exact Finset.sum_add_distrib
    _ =
        (Finset.univ.filter fun index =>
          ¬selected index ∧ value index).card +
        (Finset.univ.filter fun index =>
          selected index ∧ value index).card := by
      congr 1 <;>
        rw [Finset.card_eq_sum_ones, Finset.sum_filter]

def symmetricSelected {n : ℕ}
    (circuit : NormalizedSymmetricThresholdCircuit n)
    (index : Fin circuit.bottomCount) : Prop :=
  (circuit.bottom index).support.Nonempty

instance symmetricSelectedDecidable {n : ℕ}
    (circuit : NormalizedSymmetricThresholdCircuit n) :
    DecidablePred (symmetricSelected circuit) := by
  intro index
  unfold symmetricSelected
  infer_instance

noncomputable def symmetricActiveGate {n : ℕ}
    (circuit : NormalizedSymmetricThresholdCircuit n)
    (index : Fin (selectedCount (symmetricSelected circuit))) :
    SupportedNormalizedGate n :=
  circuit.bottom (selectedIndex (symmetricSelected circuit) index)

def symmetricConstantTrueCount {n : ℕ}
    (circuit : NormalizedSymmetricThresholdCircuit n) : ℕ :=
  (Finset.univ.filter fun index =>
    ¬symmetricSelected circuit index ∧
      (circuit.bottom index).eval (falseInput n)).card

theorem symmetric_true_count_decompose {n : ℕ}
    (circuit : NormalizedSymmetricThresholdCircuit n)
    (input : BitInput n) :
    (Finset.univ.filter fun index =>
        (circuit.bottom index).eval input).card =
      symmetricConstantTrueCount circuit +
        (Finset.univ.filter
          fun index : Fin (selectedCount (symmetricSelected circuit)) =>
            (symmetricActiveGate circuit index).eval input).card := by
  classical
  unfold symmetricActiveGate
  rw [selected_bool_card (symmetricSelected circuit)
    fun index => (circuit.bottom index).eval input]
  rw [bool_filter_card_partition (symmetricSelected circuit)
    fun index => (circuit.bottom index).eval input]
  congr 1
  unfold symmetricConstantTrueCount
  apply congrArg Finset.card
  ext index
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hselected : symmetricSelected circuit index
  · simp [hselected]
  · have hempty : (circuit.bottom index).support = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hselected
    rw [supportedGate_eval_of_support_empty
      (circuit.bottom index) hempty input]

theorem symmetric_selectedCount_le_wireCount {n : ℕ}
    (circuit : NormalizedSymmetricThresholdCircuit n) :
    selectedCount (symmetricSelected circuit) ≤ circuit.wireCount := by
  classical
  have hcard :
      selectedCount (symmetricSelected circuit) =
        ∑ index ∈ Finset.univ.filter (symmetricSelected circuit), 1 := by
    simpa using
      sum_selectedIndex (symmetricSelected circuit) (fun _ => (1 : ℕ))
  rw [hcard]
  unfold NormalizedSymmetricThresholdCircuit.wireCount
  calc
    (∑ index ∈ Finset.univ.filter (symmetricSelected circuit), 1) ≤
        ∑ index ∈ Finset.univ.filter (symmetricSelected circuit),
          ((circuit.bottom index).wireCount + 1) := by
      apply Finset.sum_le_sum
      intro index _
      omega
    _ ≤ ∑ index, ((circuit.bottom index).wireCount + 1) :=
      Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

theorem symmetricConstantTrueCount_add_selectedCount_le {n : ℕ}
    (circuit : NormalizedSymmetricThresholdCircuit n) :
    symmetricConstantTrueCount circuit +
        selectedCount (symmetricSelected circuit) ≤
      circuit.bottomCount := by
  classical
  let constantSet :=
    Finset.univ.filter fun index =>
      ¬symmetricSelected circuit index ∧
        (circuit.bottom index).eval (falseInput n)
  let selectedSet :=
    Finset.univ.filter (symmetricSelected circuit)
  have hselectedCard :
      selectedSet.card =
        selectedCount (symmetricSelected circuit) := by
    simpa only [selectedSet, selectedCount, SelectedIndex] using
      (Fintype.card_subtype
        (symmetricSelected circuit)).symm
  have hdisjoint : Disjoint constantSet selectedSet := by
    apply Finset.disjoint_left.mpr
    intro index hconstant hselected
    have hconstant' :
        ¬symmetricSelected circuit index := by
      have hpair :
          ¬symmetricSelected circuit index ∧
            (circuit.bottom index).eval (falseInput n) := by
        simpa only [constantSet, Finset.mem_filter,
          Finset.mem_univ, true_and] using hconstant
      exact hpair.1
    have hselected' : symmetricSelected circuit index := by
      simpa only [selectedSet, Finset.mem_filter,
        Finset.mem_univ, true_and] using hselected
    exact hconstant' hselected'
  have hunion :
      (constantSet ∪ selectedSet).card ≤
        (Finset.univ : Finset (Fin circuit.bottomCount)).card :=
    Finset.card_le_card (Finset.subset_univ _)
  calc
    symmetricConstantTrueCount circuit +
          selectedCount (symmetricSelected circuit) =
        constantSet.card + selectedSet.card := by
      rw [hselectedCard]
      rfl
    _ = (constantSet ∪ selectedSet).card :=
      (Finset.card_union_of_disjoint hdisjoint).symm
    _ ≤ (Finset.univ :
          Finset (Fin circuit.bottomCount)).card :=
      hunion
    _ = circuit.bottomCount := by simp

/-- Total lookup used by the Boolean DAG.  Only indices at most the selected
gate count are reachable; the false fallback keeps the builder interface
total without introducing a second semantic path. -/
def symmetricTopValue {n : ℕ}
    (circuit : NormalizedSymmetricThresholdCircuit n)
    (selected : ℕ) : Bool :=
  if h :
      symmetricConstantTrueCount circuit + selected <
        circuit.bottomCount + 1 then
    circuit.top
      ⟨symmetricConstantTrueCount circuit + selected, h⟩
  else
    false

theorem symmetricTopValue_of_le {n : ℕ}
    (circuit : NormalizedSymmetricThresholdCircuit n)
    (selected : ℕ)
    (hselected :
      selected ≤ selectedCount (symmetricSelected circuit)) :
    symmetricTopValue circuit selected =
      circuit.top
        ⟨symmetricConstantTrueCount circuit + selected, by
          have :=
            symmetricConstantTrueCount_add_selectedCount_le circuit
          omega⟩ := by
  have hbound :
      symmetricConstantTrueCount circuit + selected <
        circuit.bottomCount + 1 := by
    have :=
      symmetricConstantTrueCount_add_selectedCount_le circuit
    omega
  simp [symmetricTopValue, hbound]

def retainEvery {k : ℕ} (_ : Fin k) : Bool :=
  true

noncomputable def buildSymmetricCircuit {n : ℕ}
    (circuit : NormalizedSymmetricThresholdCircuit n) :
    BooleanCircuit n :=
  let base := BooleanDAGBuilder.empty n
  let inputs := buildAllInputs base
  let zero := buildConst inputs.final false
  let one := buildConst zero.final true
  let zeroRef := one.extension.lift (zero.output 0)
  let inputRefs := fun index =>
    one.extension.lift (zero.extension.lift (inputs.output index))
  let bottoms := buildGateVector
    (symmetricActiveGate circuit) retainEvery one.final
    zeroRef (one.output 0) inputRefs
  let count := buildHammingCount bottoms.final
    (bottoms.extension.lift zeroRef) bottoms.output
  let falseRef := count.extension.lift
    (bottoms.extension.lift zeroRef)
  let lookup := buildLookup
    (symmetricTopValue circuit)
    count.final count.bits falseRef
    (List.range (selectedCount (symmetricSelected circuit) + 1))
  lookup.final.finish (lookup.output 0)

theorem symmetricActiveGate_parameters {n : ℕ}
    (circuit : NormalizedSymmetricThresholdCircuit n)
    (hbound :
      ∀ index, (circuit.bottom index).gate.parametersBoundedBy (n ^ n))
    (index : Fin (selectedCount (symmetricSelected circuit))) :
    (symmetricActiveGate circuit index).gate.parametersBoundedBy (n ^ n) := by
  unfold symmetricActiveGate
  exact hbound _

theorem selected_filter_card_lt_succ {k : ℕ} (value : Fin k → Bool) :
    (Finset.univ.filter fun index => value index).card < k + 1 := by
  have hle :
      (Finset.univ.filter fun index => value index).card ≤
        Finset.univ.card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  simpa using Nat.lt_succ_of_le hle

theorem succ_le_two_pow_succ (k : ℕ) :
    k + 1 ≤ 2 ^ (k + 1) := by
  induction k with
  | zero => decide
  | succ k ih =>
      rw [pow_succ]
      omega

theorem buildSymmetricCircuit_eval {n : ℕ}
    (circuit : NormalizedSymmetricThresholdCircuit n)
    (hbound :
      ∀ index, (circuit.bottom index).gate.parametersBoundedBy (n ^ n))
    (input : BitInput n) :
    (buildSymmetricCircuit circuit).eval input = circuit.eval input := by
  classical
  let active := selectedCount (symmetricSelected circuit)
  let base := BooleanDAGBuilder.empty n
  let inputs := buildAllInputs base
  let zero := buildConst inputs.final false
  let one := buildConst zero.final true
  let zeroRef := one.extension.lift (zero.output 0)
  let inputRefs := fun index =>
    one.extension.lift (zero.extension.lift (inputs.output index))
  let bottoms := buildGateVector
    (symmetricActiveGate circuit) retainEvery one.final
    zeroRef (one.output 0) inputRefs
  let count := buildHammingCount bottoms.final
    (bottoms.extension.lift zeroRef) bottoms.output
  let falseRef := count.extension.lift
    (bottoms.extension.lift zeroRef)
  let lookup := buildLookup
    (symmetricTopValue circuit)
    count.final count.bits falseRef (List.range (active + 1))
  change wireValue lookup.final input (lookup.output 0) =
    circuit.eval input
  have hzeroAtZero :
      wireValue zero.final input (zero.output 0) = false := by
    simpa only [zero] using buildConst_value inputs.final false input
  have hzero :
      wireValue one.final input zeroRef = false := by
    simpa only [zeroRef, wireValue_extension] using hzeroAtZero
  have hone :
      wireValue one.final input (one.output 0) = true := by
    simpa only [one] using buildConst_value zero.final true input
  have hinputRefs (index : Fin n) :
      wireValue one.final input (inputRefs index) = input index := by
    simp only [inputRefs, wireValue_extension]
    simpa only [inputs] using
      buildAllInputs_value base index input
  have hbottom (index : Fin active) :
      wireValue bottoms.final input (bottoms.output index) =
        (symmetricActiveGate circuit index).eval input := by
    have hcompiled := buildGateVector_value
      (symmetricActiveGate circuit) retainEvery one.final
      zeroRef (one.output 0) inputRefs index input
      (symmetricActiveGate_parameters circuit hbound) hzero hone
    simpa only [bottoms, retainedGateValue, retainEvery, if_true,
      hinputRefs] using hcompiled
  have hzeroBottom :
      wireValue bottoms.final input
        (bottoms.extension.lift zeroRef) = false := by
    simpa only [wireValue_extension] using hzero
  have hcount :
      bitListValue (readWires count.final input count.bits) =
        (Finset.univ.filter fun index : Fin active =>
          (symmetricActiveGate circuit index).eval input).card := by
    have hcompiled := buildHammingCount_value bottoms.final
      (bottoms.extension.lift zeroRef) bottoms.output input hzeroBottom
    simpa only [count, hbottom] using hcompiled
  have hfalseRef :
      wireValue count.final input falseRef = false := by
    simpa only [falseRef, wireValue_extension] using hzero
  have hcountLength : count.bits.length = active + 1 := by
    simp only [count, buildHammingCount,
      buildWeightedSum_bits_length, List.length_cons, List.length_nil,
      zero_add, allIndices_length, active, Nat.add_comm]
  have hfits :
      ∀ target ∈ List.range (active + 1),
        target < 2 ^ count.bits.length := by
    intro target htarget
    rw [List.mem_range] at htarget
    rw [hcountLength]
    exact lt_of_lt_of_le htarget (succ_le_two_pow_succ active)
  have hlookup := buildLookup_value
    (symmetricTopValue circuit)
    count.final count.bits falseRef (List.range (active + 1))
    input hfits
  rw [hfalseRef, hcount] at hlookup
  have hactiveRange :
      (Finset.univ.filter fun index : Fin active =>
        (symmetricActiveGate circuit index).eval input).card <
          active + 1 :=
    selected_filter_card_lt_succ _
  rw [lookupValue_range _ _ _ hactiveRange] at hlookup
  rw [hlookup]
  unfold NormalizedSymmetricThresholdCircuit.eval
  rw [symmetricTopValue_of_le circuit _ (by
    have hcard := Finset.card_le_card
      (Finset.filter_subset
        (fun index : Fin active =>
          (symmetricActiveGate circuit index).eval input)
        (Finset.univ : Finset (Fin active)))
    simpa only [Finset.card_univ, Fintype.card_fin, active] using
      hcard)]
  apply congrArg circuit.top
  apply Fin.ext
  exact (symmetric_true_count_decompose circuit input).symm

theorem buildSymmetricCircuit_size {n : ℕ}
    (circuit : NormalizedSymmetricThresholdCircuit n) :
    (buildSymmetricCircuit circuit).size ≤
      40 * (n + circuit.wireCount + 2) ^ 4 := by
  classical
  let active := selectedCount (symmetricSelected circuit)
  let scale := n + circuit.wireCount + 2
  let base := BooleanDAGBuilder.empty n
  let inputs := buildAllInputs base
  let zero := buildConst inputs.final false
  let one := buildConst zero.final true
  let zeroRef := one.extension.lift (zero.output 0)
  let inputRefs := fun index =>
    one.extension.lift (zero.extension.lift (inputs.output index))
  let bottoms := buildGateVector
    (symmetricActiveGate circuit) retainEvery one.final
    zeroRef (one.output 0) inputRefs
  let count := buildHammingCount bottoms.final
    (bottoms.extension.lift zeroRef) bottoms.output
  let falseRef := count.extension.lift
    (bottoms.extension.lift zeroRef)
  let lookup := buildLookup
    (symmetricTopValue circuit)
    count.final count.bits falseRef (List.range (active + 1))
  change lookup.final.nodes.length ≤ 40 * scale ^ 4
  have hprefix : one.final.nodes.length = n + 2 := by
    calc
      one.final.nodes.length =
          zero.final.nodes.length + one.addedNodes :=
        one.final_length
      _ = inputs.final.nodes.length + zero.addedNodes +
          one.addedNodes := by rw [zero.final_length]
      _ = base.nodes.length + inputs.addedNodes + zero.addedNodes +
          one.addedNodes := by rw [inputs.final_length]
      _ = n + 2 := by
        simp only [one, zero, inputs, base, buildConst_addedNodes,
          buildAllInputs_addedNodes, BooleanDAGBuilder.empty,
          List.length_nil]
        omega
  have hbottom :
      bottoms.addedNodes ≤ active * (20 * (n + 2) ^ 3) := by
    simpa only [bottoms, active, retainedCount, retainEvery,
      List.filter_true, allIndices_length] using
      buildGateVector_addedNodes_le
        (symmetricActiveGate circuit) retainEvery one.final
        zeroRef (one.output 0) inputRefs
  have hcountLength : count.bits.length = active + 1 := by
    simp only [count, buildHammingCount,
      buildWeightedSum_bits_length, List.length_cons, List.length_nil,
      zero_add, allIndices_length, active, Nat.add_comm]
  have hcount :
      count.addedNodes ≤ active * (11 * (active + 1) + 1) := by
    simpa only [count, active] using
      buildHammingCount_addedNodes_le bottoms.final
        (bottoms.extension.lift zeroRef) bottoms.output
  have hlookup :
      lookup.addedNodes ≤
        (active + 1) * (4 * (active + 1) + 3) := by
    have hraw := buildLookup_addedNodes_le
      (symmetricTopValue circuit)
      count.final count.bits falseRef (List.range (active + 1))
    simpa only [lookup, List.length_range, hcountLength] using hraw
  have htotal :
      lookup.final.nodes.length ≤
        n + 2 +
          active * (20 * (n + 2) ^ 3) +
          active * (11 * (active + 1) + 1) +
          (active + 1) * (4 * (active + 1) + 3) := by
    rw [lookup.final_length, count.final_length,
      bottoms.final_length, hprefix]
    omega
  have hactiveWire : active ≤ circuit.wireCount := by
    simpa only [active] using
      symmetric_selectedCount_le_wireCount circuit
  have hscalePos : 0 < scale := by
    dsimp only [scale]
    omega
  have hactiveScale : active ≤ scale := by
    dsimp only [scale]
    omega
  have hactiveSuccScale : active + 1 ≤ scale := by
    dsimp only [scale]
    omega
  have hnScale : n + 2 ≤ scale := by
    dsimp only [scale]
    omega
  have hcube : (n + 2) ^ 3 ≤ scale ^ 3 :=
    Nat.pow_le_pow_left hnScale 3
  have hbottomPoly :
      active * (20 * (n + 2) ^ 3) ≤ 20 * scale ^ 4 := by
    calc
      active * (20 * (n + 2) ^ 3) =
          20 * active * (n + 2) ^ 3 := by ring
      _ ≤ 20 * scale * scale ^ 3 := by
        exact Nat.mul_le_mul
          (Nat.mul_le_mul_left 20 hactiveScale) hcube
      _ = 20 * scale ^ 4 := by ring
  have hcountFactor :
      11 * (active + 1) + 1 ≤ 12 * scale := by
    omega
  have hcountPoly :
      active * (11 * (active + 1) + 1) ≤ 12 * scale ^ 2 := by
    calc
      active * (11 * (active + 1) + 1) ≤
          scale * (12 * scale) :=
        Nat.mul_le_mul hactiveScale hcountFactor
      _ = 12 * scale ^ 2 := by ring
  have hlookupFactor :
      4 * (active + 1) + 3 ≤ 7 * scale := by
    omega
  have hlookupPoly :
      (active + 1) * (4 * (active + 1) + 3) ≤
        7 * scale ^ 2 := by
    calc
      (active + 1) * (4 * (active + 1) + 3) ≤
          scale * (7 * scale) :=
        Nat.mul_le_mul hactiveSuccScale hlookupFactor
      _ = 7 * scale ^ 2 := by ring
  have hscaleToFourth : scale ≤ scale ^ 4 := by
    simpa only [pow_one] using
      Nat.pow_le_pow_right hscalePos (by omega : 1 ≤ 4)
  have hsquareToFourth : scale ^ 2 ≤ scale ^ 4 :=
    Nat.pow_le_pow_right hscalePos (by omega : 2 ≤ 4)
  apply le_trans htotal
  calc
    n + 2 +
          active * (20 * (n + 2) ^ 3) +
          active * (11 * (active + 1) + 1) +
          (active + 1) * (4 * (active + 1) + 3) ≤
        scale ^ 4 + 20 * scale ^ 4 +
          12 * scale ^ 2 + 7 * scale ^ 2 := by
      omega
    _ ≤ scale ^ 4 + 20 * scale ^ 4 +
          12 * scale ^ 4 + 7 * scale ^ 4 := by
      gcongr
    _ ≤ 40 * scale ^ 4 := by
      ring_nf
      omega

def thresholdSelected {n : ℕ}
    (circuit : NormalizedThresholdThresholdCircuit n)
    (index : Fin circuit.bottomCount) : Prop :=
  index ∈ circuit.top.support ∧
    (circuit.bottom index).support.Nonempty

instance thresholdSelectedDecidable {n : ℕ}
    (circuit : NormalizedThresholdThresholdCircuit n) :
    DecidablePred (thresholdSelected circuit) := by
  intro index
  unfold thresholdSelected
  infer_instance

noncomputable def thresholdActiveGate {n : ℕ}
    (circuit : NormalizedThresholdThresholdCircuit n)
    (index : Fin (selectedCount (thresholdSelected circuit))) :
    SupportedNormalizedGate n :=
  circuit.bottom (selectedIndex (thresholdSelected circuit) index)

/-- Contribution of every top input that is not a genuinely live physical
bottom gate.  Outside the retained top support the coefficient is zero; inside
it, an empty-support bottom gate is constant and can be absorbed exactly. -/
def thresholdConstantScore {n : ℕ}
    (circuit : NormalizedThresholdThresholdCircuit n) : ℤ :=
  ∑ index, if thresholdSelected circuit index then 0 else
    circuit.top.gate.weight index *
      if (circuit.bottom index).eval (falseInput n) then 1 else 0

noncomputable def reducedTopGate {n : ℕ}
    (circuit : NormalizedThresholdThresholdCircuit n) :
    NormalizedThresholdGate
      (selectedCount (thresholdSelected circuit)) where
  weight index :=
    circuit.top.gate.weight
      (selectedIndex (thresholdSelected circuit) index)
  threshold := circuit.top.gate.threshold - thresholdConstantScore circuit

theorem threshold_score_decompose {n : ℕ}
    (circuit : NormalizedThresholdThresholdCircuit n)
    (input : BitInput n) :
    (∑ index, circuit.top.gate.weight index *
        if (circuit.bottom index).eval input then 1 else 0) =
      thresholdConstantScore circuit +
        ∑ index : Fin (selectedCount (thresholdSelected circuit)),
          (reducedTopGate circuit).weight index *
            if (thresholdActiveGate circuit index).eval input then 1 else 0 := by
  classical
  let actual := fun index : Fin circuit.bottomCount =>
    circuit.top.gate.weight index *
      if (circuit.bottom index).eval input then 1 else 0
  let frozen := fun index : Fin circuit.bottomCount =>
    circuit.top.gate.weight index *
      if (circuit.bottom index).eval (falseInput n) then 1 else 0
  have hinactive (index : Fin circuit.bottomCount)
      (hselected : ¬thresholdSelected circuit index) :
      actual index = frozen index := by
    by_cases htop : index ∈ circuit.top.support
    · have hbottom :
          ¬(circuit.bottom index).support.Nonempty := by
        intro hnonempty
        exact hselected ⟨htop, hnonempty⟩
      have hempty : (circuit.bottom index).support = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hbottom
      unfold actual frozen
      rw [supportedGate_eval_of_support_empty
        (circuit.bottom index) hempty input]
    · have hweight : circuit.top.gate.weight index = 0 :=
        circuit.top.zeroOutside index htop
      simp [actual, frozen, hweight]
  have hselectedSum :
      (∑ index : Fin (selectedCount (thresholdSelected circuit)),
          (reducedTopGate circuit).weight index *
            if (thresholdActiveGate circuit index).eval input then 1 else 0) =
        ∑ index ∈ Finset.univ.filter (thresholdSelected circuit),
          actual index := by
    change
      (∑ index, actual (selectedIndex (thresholdSelected circuit) index)) =
        ∑ index ∈ Finset.univ.filter (thresholdSelected circuit),
          actual index
    exact sum_selectedIndex (thresholdSelected circuit) actual
  rw [hselectedSum]
  unfold thresholdConstantScore
  change (∑ index, actual index) =
    (∑ index, if thresholdSelected circuit index then 0 else frozen index) +
      ∑ index ∈ Finset.univ.filter (thresholdSelected circuit), actual index
  rw [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro index _
  by_cases hselected : thresholdSelected circuit index
  · simp [hselected]
  · simp [hselected, hinactive index hselected]

theorem reducedTopGate_eval {n : ℕ}
    (circuit : NormalizedThresholdThresholdCircuit n)
    (input : BitInput n) :
    (reducedTopGate circuit).eval
        (fun index => (thresholdActiveGate circuit index).eval input) =
      circuit.eval input := by
  classical
  unfold NormalizedThresholdGate.eval
  unfold NormalizedThresholdThresholdCircuit.eval
  unfold SupportedNormalizedGate.eval
  unfold NormalizedThresholdThresholdCircuit.bottomValues
  apply decide_eq_decide.mpr
  have hscore := threshold_score_decompose circuit input
  simp only [SupportedNormalizedGate.eval] at hscore ⊢
  dsimp only [reducedTopGate] at hscore ⊢
  let activeScore : ℤ :=
    ∑ index : Fin (selectedCount (thresholdSelected circuit)),
      circuit.top.gate.weight
          (selectedIndex (thresholdSelected circuit) index) *
        if (thresholdActiveGate circuit index).gate.eval input then 1 else 0
  change
    (circuit.top.gate.threshold - thresholdConstantScore circuit ≤
        activeScore) ↔
      circuit.top.gate.threshold ≤
        ∑ index, circuit.top.gate.weight index *
          if (circuit.bottom index).gate.eval input then 1 else 0
  change
    (∑ index, circuit.top.gate.weight index *
        if (circuit.bottom index).gate.eval input then 1 else 0) =
      thresholdConstantScore circuit + activeScore at hscore
  rw [hscore]
  omega

noncomputable def normalizedAsRealGate {m : ℕ}
    (gate : NormalizedThresholdGate m) : RealThresholdGate m where
  weight index := gate.weight index
  threshold := gate.threshold
  support := Finset.univ.filter fun index => gate.weight index ≠ 0
  mem_support_iff := by simp

theorem normalizedAsRealGate_eval {m : ℕ}
    (gate : NormalizedThresholdGate m) (input : BitInput m) :
    (normalizedAsRealGate gate).eval input = gate.eval input := by
  classical
  unfold RealThresholdGate.eval NormalizedThresholdGate.eval
  apply decide_eq_decide.mpr
  change
    ((gate.threshold : ℝ) ≤
      ∑ index, (gate.weight index : ℝ) * bitAsReal (input index)) ↔
      gate.threshold ≤
        ∑ index, gate.weight index *
          if input index then 1 else 0
  have hsum :
      (∑ index, (gate.weight index : ℝ) * bitAsReal (input index)) =
        ((∑ index, gate.weight index *
          if input index then 1 else 0 : ℤ) : ℝ) := by
    rw [Int.cast_sum]
    apply Finset.sum_congr rfl
    intro index _
    cases input index <;> simp [bitAsReal]
  rw [hsum]
  norm_cast

noncomputable def reducedTopRealGate {n : ℕ}
    (circuit : NormalizedThresholdThresholdCircuit n) :
    RealThresholdGate (selectedCount (thresholdSelected circuit)) :=
  normalizedAsRealGate (reducedTopGate circuit)

theorem reducedTopRealGate_eval {n : ℕ}
    (circuit : NormalizedThresholdThresholdCircuit n)
    (input : BitInput n) :
    (reducedTopRealGate circuit).eval
        (fun index => (thresholdActiveGate circuit index).eval input) =
      circuit.eval input := by
  rw [reducedTopRealGate, normalizedAsRealGate_eval,
    reducedTopGate_eval]

theorem threshold_selectedCount_le_wireCount {n : ℕ}
    (circuit : NormalizedThresholdThresholdCircuit n) :
    selectedCount (thresholdSelected circuit) ≤ circuit.wireCount := by
  classical
  have hcard :
      selectedCount (thresholdSelected circuit) =
        ∑ index ∈ Finset.univ.filter (thresholdSelected circuit), 1 := by
    simpa using
      sum_selectedIndex (thresholdSelected circuit) (fun _ => (1 : ℕ))
  rw [hcard]
  unfold NormalizedThresholdThresholdCircuit.wireCount
  calc
    (∑ index ∈ Finset.univ.filter (thresholdSelected circuit), 1) ≤
        ∑ index ∈ Finset.univ.filter (thresholdSelected circuit),
          ((circuit.bottom index).wireCount + 1) := by
      apply Finset.sum_le_sum
      intro index _
      omega
    _ ≤ ∑ index ∈ circuit.top.support,
          ((circuit.bottom index).wireCount + 1) := by
      apply Finset.sum_le_sum_of_subset
      intro index hindex
      have hselected : thresholdSelected circuit index := by
        simpa using hindex
      exact hselected.1

/-- Re-normalize only the genuinely active top variables.  This is the key
step that removes every dependence on the raw syntactic bottom count from the
compiled coefficient widths. -/
noncomputable def compressedTop {n : ℕ}
    (normalization : ThresholdNormalizationContract)
    (circuit : NormalizedThresholdThresholdCircuit n) :
    SupportedNormalizedGate
      (selectedCount (thresholdSelected circuit)) :=
  Classical.choose
    (normalizeGatePreservingSupport normalization
      (reducedTopRealGate circuit))

theorem compressedTop_eval {n : ℕ}
    (normalization : ThresholdNormalizationContract)
    (circuit : NormalizedThresholdThresholdCircuit n)
    (input :
      BitInput (selectedCount (thresholdSelected circuit))) :
    (compressedTop normalization circuit).eval input =
      (reducedTopRealGate circuit).eval input :=
  (Classical.choose_spec
    (normalizeGatePreservingSupport normalization
      (reducedTopRealGate circuit))).1 input

theorem compressedTop_parameters {n : ℕ}
    (normalization : ThresholdNormalizationContract)
    (circuit : NormalizedThresholdThresholdCircuit n) :
    (compressedTop normalization circuit).gate.parametersBoundedBy
      (selectedCount (thresholdSelected circuit) ^
        selectedCount (thresholdSelected circuit)) :=
  (Classical.choose_spec
    (normalizeGatePreservingSupport normalization
      (reducedTopRealGate circuit))).2.2

theorem thresholdActiveGate_parameters {n : ℕ}
    (circuit : NormalizedThresholdThresholdCircuit n)
    (hbound :
      ∀ index, (circuit.bottom index).gate.parametersBoundedBy (n ^ n))
    (index : Fin (selectedCount (thresholdSelected circuit))) :
    (thresholdActiveGate circuit index).gate.parametersBoundedBy (n ^ n) := by
  unfold thresholdActiveGate
  exact hbound _

noncomputable def buildThresholdCircuit {n : ℕ}
    (normalization : ThresholdNormalizationContract)
    (circuit : NormalizedThresholdThresholdCircuit n) :
    BooleanCircuit n :=
  let base := BooleanDAGBuilder.empty n
  let inputs := buildAllInputs base
  let zero := buildConst inputs.final false
  let one := buildConst zero.final true
  let zeroRef := one.extension.lift (zero.output 0)
  let inputRefs := fun index =>
    one.extension.lift (zero.extension.lift (inputs.output index))
  let bottoms := buildGateVector
    (thresholdActiveGate circuit) retainEvery one.final
    zeroRef (one.output 0) inputRefs
  let top := buildNormalizedGate bottoms.final
    (bottoms.extension.lift zeroRef) bottoms.output
    (compressedTop normalization circuit).gate
  top.final.finish (top.output 0)

theorem buildThresholdCircuit_eval {n : ℕ}
    (normalization : ThresholdNormalizationContract)
    (circuit : NormalizedThresholdThresholdCircuit n)
    (hbound :
      ∀ index, (circuit.bottom index).gate.parametersBoundedBy (n ^ n))
    (input : BitInput n) :
    (buildThresholdCircuit normalization circuit).eval input =
      circuit.eval input := by
  classical
  let active := selectedCount (thresholdSelected circuit)
  let base := BooleanDAGBuilder.empty n
  let inputs := buildAllInputs base
  let zero := buildConst inputs.final false
  let one := buildConst zero.final true
  let zeroRef := one.extension.lift (zero.output 0)
  let inputRefs := fun index =>
    one.extension.lift (zero.extension.lift (inputs.output index))
  let bottoms := buildGateVector
    (thresholdActiveGate circuit) retainEvery one.final
    zeroRef (one.output 0) inputRefs
  let top := buildNormalizedGate bottoms.final
    (bottoms.extension.lift zeroRef) bottoms.output
    (compressedTop normalization circuit).gate
  change wireValue top.final input (top.output 0) = circuit.eval input
  have hzeroAtZero :
      wireValue zero.final input (zero.output 0) = false := by
    simpa only [zero] using buildConst_value inputs.final false input
  have hzero :
      wireValue one.final input zeroRef = false := by
    simpa only [zeroRef, wireValue_extension] using hzeroAtZero
  have hone :
      wireValue one.final input (one.output 0) = true := by
    simpa only [one] using buildConst_value zero.final true input
  have hinputRefs (index : Fin n) :
      wireValue one.final input (inputRefs index) = input index := by
    simp only [inputRefs, wireValue_extension]
    simpa only [inputs] using
      buildAllInputs_value base index input
  have hbottom (index : Fin active) :
      wireValue bottoms.final input (bottoms.output index) =
        (thresholdActiveGate circuit index).eval input := by
    have hcompiled := buildGateVector_value
      (thresholdActiveGate circuit) retainEvery one.final
      zeroRef (one.output 0) inputRefs index input
      (thresholdActiveGate_parameters circuit hbound) hzero hone
    simpa only [bottoms, retainedGateValue, retainEvery, if_true,
      hinputRefs] using hcompiled
  have hzeroBottom :
      wireValue bottoms.final input
        (bottoms.extension.lift zeroRef) = false := by
    simpa only [wireValue_extension] using hzero
  have htop := buildNormalizedGate_value bottoms.final
    (bottoms.extension.lift zeroRef) bottoms.output
    (compressedTop normalization circuit).gate
    (compressedTop_parameters normalization circuit) input hzeroBottom
  have hcompiled :
      wireValue top.final input (top.output 0) =
        (compressedTop normalization circuit).eval
          (fun index => (thresholdActiveGate circuit index).eval input) := by
    simpa only [top, SupportedNormalizedGate.eval, hbottom] using htop
  rw [hcompiled, compressedTop_eval, reducedTopRealGate_eval]

theorem buildThresholdCircuit_size {n : ℕ}
    (normalization : ThresholdNormalizationContract)
    (circuit : NormalizedThresholdThresholdCircuit n) :
    (buildThresholdCircuit normalization circuit).size ≤
      50 * (n + circuit.wireCount + 2) ^ 4 := by
  classical
  let active := selectedCount (thresholdSelected circuit)
  let scale := n + circuit.wireCount + 2
  let base := BooleanDAGBuilder.empty n
  let inputs := buildAllInputs base
  let zero := buildConst inputs.final false
  let one := buildConst zero.final true
  let zeroRef := one.extension.lift (zero.output 0)
  let inputRefs := fun index =>
    one.extension.lift (zero.extension.lift (inputs.output index))
  let bottoms := buildGateVector
    (thresholdActiveGate circuit) retainEvery one.final
    zeroRef (one.output 0) inputRefs
  let top := buildNormalizedGate bottoms.final
    (bottoms.extension.lift zeroRef) bottoms.output
    (compressedTop normalization circuit).gate
  change top.final.nodes.length ≤ 50 * scale ^ 4
  have hprefix : one.final.nodes.length = n + 2 := by
    calc
      one.final.nodes.length =
          zero.final.nodes.length + one.addedNodes :=
        one.final_length
      _ = inputs.final.nodes.length + zero.addedNodes +
          one.addedNodes := by rw [zero.final_length]
      _ = base.nodes.length + inputs.addedNodes + zero.addedNodes +
          one.addedNodes := by rw [inputs.final_length]
      _ = n + 2 := by
        simp only [one, zero, inputs, base, buildConst_addedNodes,
          buildAllInputs_addedNodes, BooleanDAGBuilder.empty,
          List.length_nil]
        omega
  have hbottom :
      bottoms.addedNodes ≤ active * (20 * (n + 2) ^ 3) := by
    simpa only [bottoms, active, retainedCount, retainEvery,
      List.filter_true, allIndices_length] using
      buildGateVector_addedNodes_le
        (thresholdActiveGate circuit) retainEvery one.final
        zeroRef (one.output 0) inputRefs
  have htop :
      top.addedNodes ≤ 20 * (active + 2) ^ 3 := by
    simpa only [top, active] using
      buildNormalizedGate_addedNodes_polynomial bottoms.final
        (bottoms.extension.lift zeroRef) bottoms.output
        (compressedTop normalization circuit).gate
  have htotal :
      top.final.nodes.length ≤
        n + 2 + active * (20 * (n + 2) ^ 3) +
          20 * (active + 2) ^ 3 := by
    rw [top.final_length, bottoms.final_length, hprefix]
    omega
  have hactiveWire : active ≤ circuit.wireCount := by
    simpa only [active] using
      threshold_selectedCount_le_wireCount circuit
  have hscalePos : 0 < scale := by
    dsimp only [scale]
    omega
  have hactiveScale : active ≤ scale := by
    dsimp only [scale]
    omega
  have hactiveTwoScale : active + 2 ≤ scale := by
    dsimp only [scale]
    omega
  have hnScale : n + 2 ≤ scale := by
    dsimp only [scale]
    omega
  have hinputCube : (n + 2) ^ 3 ≤ scale ^ 3 :=
    Nat.pow_le_pow_left hnScale 3
  have hactiveCube : (active + 2) ^ 3 ≤ scale ^ 3 :=
    Nat.pow_le_pow_left hactiveTwoScale 3
  have hbottomPoly :
      active * (20 * (n + 2) ^ 3) ≤ 20 * scale ^ 4 := by
    calc
      active * (20 * (n + 2) ^ 3) =
          20 * active * (n + 2) ^ 3 := by ring
      _ ≤ 20 * scale * scale ^ 3 := by
        exact Nat.mul_le_mul
          (Nat.mul_le_mul_left 20 hactiveScale) hinputCube
      _ = 20 * scale ^ 4 := by ring
  have htopPoly :
      20 * (active + 2) ^ 3 ≤ 20 * scale ^ 3 :=
    Nat.mul_le_mul_left 20 hactiveCube
  have hscaleToFourth : scale ≤ scale ^ 4 := by
    simpa only [pow_one] using
      Nat.pow_le_pow_right hscalePos (by omega : 1 ≤ 4)
  have hcubeToFourth : scale ^ 3 ≤ scale ^ 4 :=
    Nat.pow_le_pow_right hscalePos (by omega : 3 ≤ 4)
  apply le_trans htotal
  calc
    n + 2 + active * (20 * (n + 2) ^ 3) +
          20 * (active + 2) ^ 3 ≤
        scale ^ 4 + 20 * scale ^ 4 + 20 * scale ^ 3 := by
      omega
    _ ≤ scale ^ 4 + 20 * scale ^ 4 + 20 * scale ^ 4 := by
      gcongr
    _ ≤ 50 * scale ^ 4 := by
      ring_nf
      omega

/-! ## Source-circuit simulation theorems -/

/-- Every physical `SYM ∘ THR` circuit has an exactly equivalent canonical
fan-in-two Boolean DAG whose size is polynomial in input arity and physical
wire count, independent of unused syntactic gates. -/
theorem simulateSymmetricThresholdCircuit
    (normalization : ThresholdNormalizationContract)
    {n : ℕ} (source : SymmetricThresholdCircuit n) :
    ∃ circuit : BooleanCircuit n,
      circuit.eval = source.eval ∧
      circuit.size ≤ 40 * (n + source.wireCount + 2) ^ 4 := by
  rcases normalizeSymmetricCircuit normalization source with
    ⟨normalized, hsemantics, hwires, hparameters⟩
  refine ⟨buildSymmetricCircuit normalized, ?_, ?_⟩
  · funext input
    rw [buildSymmetricCircuit_eval normalized hparameters input,
      hsemantics input]
  · rw [← hwires]
    exact buildSymmetricCircuit_size normalized

/-- Every physical `THR ∘ THR` circuit admits the same exact canonical
simulation.  The top gate is re-normalized after constant absorption, so the
bound depends on charged wires rather than raw top fan-in. -/
theorem simulateThresholdThresholdCircuit
    (normalization : ThresholdNormalizationContract)
    {n : ℕ} (source : ThresholdThresholdCircuit n) :
    ∃ circuit : BooleanCircuit n,
      circuit.eval = source.eval ∧
      circuit.size ≤ 50 * (n + source.wireCount + 2) ^ 4 := by
  rcases normalizeThresholdCircuit normalization source with
    ⟨normalized, hsemantics, hwires, _hbottomCount,
      hbottomParameters, _htopParameters⟩
  refine ⟨buildThresholdCircuit normalization normalized, ?_, ?_⟩
  · funext input
    rw [buildThresholdCircuit_eval normalization normalized
      hbottomParameters input, hsemantics input]
  · rw [← hwires]
    exact buildThresholdCircuit_size normalization normalized

end NearCubicWires.ThresholdDAGSimulation
