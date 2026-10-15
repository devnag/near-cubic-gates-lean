import Proof.PCP.PCPPNativeHierarchyPolynomial

/-! Original native descriptor bytes of a checked canonical Boolean DAG
are bounded by its actual size and arity, using the existing DAG bound. -/
namespace NearCubicWires.RepairOrdinary.PCPPNative
open SourceInterfaces RepairSource RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem descriptor_length_bound {n : ℕ} (c : BooleanCircuit n) :
    (descriptor c).length≤39*(n+c.size+5)^2 := by
  have h:=PCPPRequestRuntime.descriptor_parameter c
  change n+(frame (descriptor c)).length+1≤39*(n+c.size+5)^2 at h
  rw [frame_length] at h
  omega

theorem descriptor_cap {n cap : ℕ} (c : BooleanCircuit n) (hs : c.size≤cap) :
    (descriptor c).length≤39*(n+cap+5)^2 :=
  (descriptor_length_bound c).trans (Nat.mul_le_mul_left 39 (Nat.pow_le_pow_left (by omega) 2))

theorem oracle_parameter_bound {n : ℕ} (c : BooleanCircuit n) :
    PCPPNativeHierarchySource.oracleParameter c≤40*(n+c.size+5)^2 := by
  have h:=descriptor_length_bound c
  have hsq : n+c.size+5≤(n+c.size+5)^2 := Nat.le_self_pow (by decide) _
  unfold PCPPNativeHierarchySource.oracleParameter
  omega

end NearCubicWires.RepairOrdinary.PCPPNative
