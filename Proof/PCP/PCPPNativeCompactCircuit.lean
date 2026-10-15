import Proof.PCP.PCPPNativeCounterNodes

/-! The emitted bytes and actual output counters describe the original
compact substituted Boolean DAG, with its bounded-reference proof intact. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeCompactNodes
open LocalBitMultitape SourceInterfaces RepairSource ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def circuit (p : RawProjectionPCP) (R Q : ℕ) (hR : p.width≤R) (hQ : p.queries≤Q)
    {n : ℕ} (x : BitInput n) (oracle : BooleanCircuit R) : BooleanCircuit R :=
  PCPPSubstitution.compactSubstituted oracle ((p.normalized R Q hR hQ).queryAddressBits x)
    ((p.normalized R Q hR hQ).decision x (fun _ : Fin R=>false))

theorem circuit_nodes (p : RawProjectionPCP) (R Q : ℕ) (hR : p.width≤R) (hQ : p.queries≤Q)
    {n : ℕ} (x : BitInput n) (oracle : BooleanCircuit R) :
    (circuit p R Q hR hQ x oracle).nodes=nodes p R Q hR hQ x oracle := by
  rw [circuit,PCPPSubstitution.compactSubstituted,PCPPNative.substituted_nodes]
  rfl
theorem circuit_size (p : RawProjectionPCP) (R Q : ℕ) (hR : p.width≤R) (hQ : p.queries≤Q)
    {n : ℕ} (x : BitInput n) (oracle : BooleanCircuit R) :
    (circuit p R Q hR hQ x oracle).size=PCPPNativeCount.nativeSize Q oracle.size (Codec.clauses p).length := by
  rw [circuit,PCPPSubstitution.compactSubstituted,PCPPSubstitution.substituted_size]
  change Q*(2*oracle.size+1)+3*(clauses p R Q hR hQ x).length+1=_
  rw [count]
  simp [PCPPNativeCount.nativeSize,PCPPNativeCount.outputIndex,PCPPNativeCount.queryEnd,PCPPNativeCount.stride,Nat.mul_comm]
theorem circuit_output (p : RawProjectionPCP) (R Q : ℕ) (hR : p.width≤R) (hQ : p.queries≤Q)
    {n : ℕ} (x : BitInput n) (oracle : BooleanCircuit R) :
    (circuit p R Q hR hQ x oracle).output.val=PCPPNativeCount.outputIndex Q oracle.size (Codec.clauses p).length := by
  rw [circuit,PCPPSubstitution.compactSubstituted,PCPPNative.substituted_output]
  change Q*(2*oracle.size+1)+3*(clauses p R Q hR hQ x).length=_
  rw [count]
  simp [PCPPNativeCount.outputIndex,PCPPNativeCount.queryEnd,PCPPNativeCount.stride,Nat.mul_comm]

end NearCubicWires.RepairOrdinary.PCPPNativeCompactNodes
