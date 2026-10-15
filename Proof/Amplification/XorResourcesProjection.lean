import Proof.Amplification.XorResources
import Proof.Foundations.CircuitRestriction

/-! Full literal-projection closure at the physical retained-support wire budget.
Constants become threshold offsets, and repeated signed variables are collected
in a single weight. New nonzero coordinates lie in the union of old singleton
variable supports, so cancellations and identifications cannot add wires. -/
namespace NearCubicWires.RepairXor
open SourceInterfaces RepairRepresentation CircuitRestriction
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def projectionOffset {m : ℕ} : ProjectedRandomBit m → ℝ
  | .bit _ => 0
  | .negatedBit _ => 1
  | .constant value => bitAsReal value

def projectionCoefficient {m : ℕ} (projection : ProjectedRandomBit m)
    (index : Fin m) : ℝ :=
  match projection with
  | .bit target => if index = target then 1 else 0
  | .negatedBit target => if index = target then -1 else 0
  | .constant _ => 0

def projectionVariables {m : ℕ} : ProjectedRandomBit m → Finset (Fin m)
  | .bit target => {target}
  | .negatedBit target => {target}
  | .constant _ => ∅

theorem projectionVariables_card {m : ℕ} (p : ProjectedRandomBit m) :
    (projectionVariables p).card ≤ 1 := by
  cases p <;> simp [projectionVariables]

theorem projectionCoefficient_mem {m : ℕ} (p : ProjectedRandomBit m)
    (index : Fin m) (h : projectionCoefficient p index ≠ 0) :
    index ∈ projectionVariables p := by
  cases p <;> simp_all [projectionCoefficient, projectionVariables]

theorem projection_score {m : ℕ} (p : ProjectedRandomBit m)
    (weight : ℝ) (input : BitInput m) :
    weight * bitAsReal (p.eval input) = weight * projectionOffset p +
      ∑ index, weight * projectionCoefficient p index * bitAsReal (input index) := by
  cases p with
  | bit target => simp [ProjectedRandomBit.eval, projectionOffset, projectionCoefficient]
  | negatedBit target =>
    have hnot : bitAsReal (!(input target)) = 1 - bitAsReal (input target) := by
      cases input target <;> norm_num [bitAsReal]
    simp [ProjectedRandomBit.eval, projectionOffset, projectionCoefficient, hnot]
    ring
  | constant value => simp [ProjectedRandomBit.eval, projectionOffset, projectionCoefficient]

def projectGate {n m : ℕ} (gate : RealThresholdGate n)
    (p : Fin n → ProjectedRandomBit m) : RealThresholdGate m where
  weight index := ∑ old, gate.weight old * projectionCoefficient (p old) index
  threshold := gate.threshold - ∑ old, gate.weight old * projectionOffset (p old)
  support := Finset.univ.filter fun index =>
    (∑ old, gate.weight old * projectionCoefficient (p old) index) ≠ 0
  mem_support_iff := by simp

theorem projectGate_eval {n m : ℕ} (gate : RealThresholdGate n)
    (p : Fin n → ProjectedRandomBit m) (input : BitInput m) :
    (projectGate gate p).eval input = gate.eval (fun i => (p i).eval input) := by
  have hscore : (∑ old, gate.weight old * bitAsReal ((p old).eval input)) =
      (∑ old, gate.weight old * projectionOffset (p old)) +
      ∑ index, (∑ old, gate.weight old * projectionCoefficient (p old) index) *
        bitAsReal (input index) := by
    calc
      _ = ∑ old, (gate.weight old * projectionOffset (p old) +
          ∑ index, gate.weight old * projectionCoefficient (p old) index *
            bitAsReal (input index)) :=
        Finset.sum_congr rfl fun old _ => projection_score (p old) (gate.weight old) input
      _ = _ := by
        rw [Finset.sum_add_distrib]
        congr 1
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro index _
        exact (Finset.sum_mul _ _ _).symm
  unfold RealThresholdGate.eval
  apply decide_eq_decide.mpr
  change gate.threshold - (∑ old, gate.weight old * projectionOffset (p old)) ≤
    (∑ index, (∑ old, gate.weight old * projectionCoefficient (p old) index) *
      bitAsReal (input index)) ↔ _
  rw [hscore]
  constructor <;> intro h <;> linarith

theorem projectGate_support_card {n m : ℕ} (gate : RealThresholdGate n)
    (p : Fin n → ProjectedRandomBit m) :
    (projectGate gate p).support.card ≤ gate.support.card := by
  classical
  have hsubset : (projectGate gate p).support ⊆
      gate.support.biUnion (fun old => projectionVariables (p old)) := by
    intro index hindex
    have hnonzero := ((projectGate gate p).mem_support_iff index).1 hindex
    change (∑ old, gate.weight old * projectionCoefficient (p old) index) ≠ 0 at hnonzero
    obtain ⟨old, _hold, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hnonzero
    obtain ⟨hw, hp⟩ := mul_ne_zero_iff.mp hterm
    exact Finset.mem_biUnion.mpr ⟨old, (gate.mem_support_iff old).2 hw,
      projectionCoefficient_mem (p old) index hp⟩
  calc
    _ ≤ (gate.support.biUnion (fun old => projectionVariables (p old))).card :=
      Finset.card_le_card hsubset
    _ ≤ ∑ old ∈ gate.support, (projectionVariables (p old)).card := Finset.card_biUnion_le
    _ ≤ ∑ _old ∈ gate.support, 1 :=
      Finset.sum_le_sum fun old _ => projectionVariables_card (p old)
    _ = _ := by simp

def projectSymmetric {n m : ℕ} (circuit : SymmetricThresholdCircuit n)
    (p : Fin n → ProjectedRandomBit m) : SymmetricThresholdCircuit m where
  bottomCount := circuit.bottomCount
  bottom index := projectGate (circuit.bottom index) p
  top := circuit.top

theorem projectSymmetric_eval {n m : ℕ} (circuit : SymmetricThresholdCircuit n)
    (p : Fin n → ProjectedRandomBit m) (input : BitInput m) :
    (projectSymmetric circuit p).eval input = circuit.eval (fun i => (p i).eval input) := by
  unfold SymmetricThresholdCircuit.eval projectSymmetric
  simp only [projectGate_eval]

theorem projectSymmetric_wires {n m : ℕ} (circuit : SymmetricThresholdCircuit n)
    (p : Fin n → ProjectedRandomBit m) :
    (projectSymmetric circuit p).wireCount ≤ circuit.wireCount := by
  unfold SymmetricThresholdCircuit.wireCount projectSymmetric
  exact Finset.sum_le_sum fun index _ => Nat.add_le_add_right
    (projectGate_support_card (circuit.bottom index) p) 1

def projectThreshold {n m : ℕ} (circuit : ThresholdThresholdCircuit n)
    (p : Fin n → ProjectedRandomBit m) : ThresholdThresholdCircuit m where
  bottomCount := circuit.bottomCount
  bottom index := projectGate (circuit.bottom index) p
  topWeight := circuit.topWeight
  topThreshold := circuit.topThreshold

theorem projectThreshold_eval {n m : ℕ} (circuit : ThresholdThresholdCircuit n)
    (p : Fin n → ProjectedRandomBit m) (input : BitInput m) :
    (projectThreshold circuit p).eval input = circuit.eval (fun i => (p i).eval input) := by
  unfold ThresholdThresholdCircuit.eval projectThreshold
  simp only [projectGate_eval]

theorem projectThreshold_wires {n m : ℕ} (circuit : ThresholdThresholdCircuit n)
    (p : Fin n → ProjectedRandomBit m) :
    (projectThreshold circuit p).wireCount ≤ circuit.wireCount := by
  unfold ThresholdThresholdCircuit.wireCount projectThreshold
  exact Finset.sum_le_sum fun index _ => Nat.add_le_add_right
    (projectGate_support_card (circuit.bottom index) p) 1

theorem symmetricWireFamily_literalProjectionClosed : LiteralProjectionClosed symmetricWireFamily := by
  intro n m size f hf p
  obtain ⟨circuit, hw, he⟩ := hf
  refine ⟨projectSymmetric circuit p, (projectSymmetric_wires circuit p).trans hw, ?_⟩
  funext input
  rw [projectSymmetric_eval, he]

theorem thresholdWireFamily_literalProjectionClosed : LiteralProjectionClosed thresholdWireFamily := by
  intro n m size f hf p
  obtain ⟨circuit, hw, he⟩ := hf
  refine ⟨projectThreshold circuit p, (projectThreshold_wires circuit p).trans hw, ?_⟩
  funext input
  rw [projectThreshold_eval, he]

theorem symmetric_xor_consumer (source : XorSource)
    (delta : ℚ) (hd : 0 < delta) (hh : delta < 1 / 2)
    {n : ℕ} (f : BoolFunction n) (hn : 1 ≤ n) (k size : ℕ) (hk : 1 ≤ k)
    (hfar : FarFromCircuitSums symmetricWireFamily f size (xorTermBound delta n k)
      (xorBits delta n k) (1 / xorEpsilon (delta : ℝ) k) (delta : ℝ))
    (candidate : BoolFunction (k * n)) (hcandidate : symmetricWireFamily (k * n) candidate size) :
    agreement candidate (xorPower f k) ≤ 1 / 2 + xorEpsilon (delta : ℝ) k :=
  xor_consumer_closed source delta hd hh symmetricWireFamily
    symmetricWireFamily_literalProjectionClosed symmetricWireFamily_negationClosed
    f hn k size hk hfar candidate hcandidate

theorem threshold_xor_consumer (source : XorSource)
    (delta : ℚ) (hd : 0 < delta) (hh : delta < 1 / 2)
    {n : ℕ} (f : BoolFunction n) (hn : 1 ≤ n) (k size : ℕ) (hk : 1 ≤ k)
    (hfar : FarFromCircuitSums thresholdWireFamily f size (xorTermBound delta n k)
      (xorBits delta n k) (1 / xorEpsilon (delta : ℝ) k) (delta : ℝ))
    (candidate : BoolFunction (k * n)) (hcandidate : thresholdWireFamily (k * n) candidate size) :
    agreement candidate (xorPower f k) ≤ 1 / 2 + xorEpsilon (delta : ℝ) k :=
  xor_consumer_closed source delta hd hh thresholdWireFamily
    thresholdWireFamily_literalProjectionClosed thresholdWireFamily_negationClosed
    f hn k size hk hfar candidate hcandidate

end
end NearCubicWires.RepairXor
