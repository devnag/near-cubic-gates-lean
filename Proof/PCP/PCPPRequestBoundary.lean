import Proof.Circuits.DecompositionLocalBounds
import Proof.Circuits.CanonicalInputLiftedBooleanCircuitEncoding
import Proof.Amplification.RecoveryWitnessPolicy

/-! Literal source request after native compact substitution. Input-axis
lifting handles the source's minimum arity; isolated nodes handle its size
condition. These semantic/code identities do not claim a paid producer. -/
namespace NearCubicWires.RepairOrdinary.PCPPRequestBoundary
open RepairRepresentation SourceInterfaces ExecutableInterfaces CanonicalBinary
open InputLiftedBooleanCircuit CanonicalInputLiftedBooleanCircuitEncoding
open ProjectionPCPPadding RecoveryWitnessPolicy
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def domain (a : PointwisePCPPAlgorithm) (n : ℕ) := max n a.minimumArity
def lifted (a : PointwisePCPPAlgorithm) {n : ℕ} (c : BooleanCircuit n) :=
  liftBooleanCircuitInputs c (Nat.le_max_left n a.minimumArity)
def request (a : PointwisePCPPAlgorithm) {n : ℕ} (c : BooleanCircuit n) : PCPPRequest a.minimumArity :=
  pointwiseRequest a (lifted a c) (Nat.le_max_right n a.minimumArity)
def padding (a : PointwisePCPPAlgorithm) {n : ℕ} (c : BooleanCircuit n) := domain a n-c.size

theorem request_size (a : PointwisePCPPAlgorithm) {n : ℕ} (c : BooleanCircuit n) :
    (request a c).circuit.size=max c.size (domain a n) := by
  simp only [request,pointwiseRequest,BooleanCircuit.padToArity,BooleanCircuit.padSize_size,
    lifted,liftBooleanCircuitInputs_size]
  unfold domain
  omega

theorem request_eval (a : PointwisePCPPAlgorithm) {n : ℕ} (c : BooleanCircuit n)
    (x : BitInput (domain a n)) :
    (request a c).circuit.eval x=c.eval (prefixBits (Nat.le_max_left n a.minimumArity) x) := by
  simp only [request,pointwiseRequest,BooleanCircuit.padToArity_eval,lifted,liftBooleanCircuitInputs_eval]

theorem request_code (a : PointwisePCPPAlgorithm) {n : ℕ} (c : BooleanCircuit n) :
    encodeBooleanCircuit (request a c).circuit=
      encodeTaggedList [encodeBalancedList
        (c.nodes.map encodeBooleanNode++List.replicate (padding a c) (encodeBooleanNode (BooleanNode.const false : BooleanNode n))),
        encodeNat c.output.val] := by
  simp only [request,pointwiseRequest,BooleanCircuit.padToArity,BooleanCircuit.padSize,
    encodeBooleanCircuit,BooleanDAGBuilder.finish,BooleanDAGBuilder.appendFalse_nodes,
    BooleanCircuit.toBuilder,lifted,liftBooleanCircuitInputs,List.map_append,List.map_replicate,
    List.map_map,Function.comp_def,encodeBooleanNode_liftBooleanNodeInputs,padding,domain,
    BooleanDAGExtension.lift_val,BooleanCircuit.size,List.length_map]
  rfl

theorem source_budget (a : PointwisePCPPAlgorithm) {n : ℕ} (c : BooleanCircuit n) :
    a.coefficient*((request a c).circuit.size+(request a c).arity+1)^a.degree ≤
      a.coefficient*(c.size+2*n+2*a.minimumArity+1)^a.degree := by
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_left
  rw [request_size]
  change max c.size (domain a n)+domain a n+1 ≤ _
  unfold domain
  omega

theorem request_complete (a : PointwisePCPPAlgorithm) {n : ℕ} (c : BooleanCircuit n)
    (x : BitInput (domain a n))
    (hx : c.eval (prefixBits (Nat.le_max_left n a.minimumArity) x)=true) :
    (a.output (request a c)).satisfiedFraction x
      ((a.output (request a c)).honestAuxiliary x) ≥ a.completeness := by
  apply a.complete
  rw [request_eval]
  exact hx

theorem request_sound (a : PointwisePCPPAlgorithm) {n : ℕ} (c : BooleanCircuit n)
    (x : BitInput (domain a n))
    (hx : c.eval (prefixBits (Nat.le_max_left n a.minimumArity) x)=false)
    (auxiliary : BitInput (a.output (request a c)).auxiliaryBits) :
    (a.output (request a c)).satisfiedFraction x auxiliary ≤ a.soundness := by
  apply a.sound
  rw [request_eval]
  exact hx

end NearCubicWires.RepairOrdinary.PCPPRequestBoundary
