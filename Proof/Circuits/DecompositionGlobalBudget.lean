import Proof.Circuits.DecompositionOuterBounds

/-! One capacity from the original measured native input covers every actual
magnitude, child and outer serialization. The exponent is fixed globally. -/
namespace NearCubicWires.RepairOrdinary.DecompositionCodeBounds
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def globalCoefficient : ℕ := 1000000000000000000000000000000000000
def globalDegree : ℕ := 144
def globalEnvelope (N : ℕ) := globalCoefficient*(N+1)^globalDegree

theorem global_budget (N : ℕ) :
    DecompositionAtom.envelope N+1+PCPTraversal.budget (21*(N+1)^6)+1+
      PCPTraversal.budget (51*(N+1)^11)+1 ≤ globalEnvelope N := by
  have h6 : 1≤(N+1)^6 := Nat.one_le_pow 6 _ (by omega)
  have h11 : 1≤(N+1)^11 := Nat.one_le_pow 11 _ (by omega)
  have h12 : (N+1)^12≤(N+1)^144 := pow_le_pow_right₀ (by omega) (by omega)
  have h72 : (N+1)^72≤(N+1)^144 := pow_le_pow_right₀ (by omega) (by omega)
  have h132 : (N+1)^132≤(N+1)^144 := pow_le_pow_right₀ (by omega) (by omega)
  have h144 : 1≤(N+1)^144 := Nat.one_le_pow 144 _ (by omega)
  have ha : PCPTraversal.budget (21*(N+1)^6) ≤ (1000000000000*22^12)*(N+1)^72 := by
    unfold PCPTraversal.budget
    calc
      _ ≤ 1000000000000*(22*(N+1)^6)^12 := by gcongr; omega
      _ = _ := by rw [mul_pow,←pow_mul]; ring
  have hb : PCPTraversal.budget (51*(N+1)^11) ≤ (1000000000000*52^12)*(N+1)^132 := by
    unfold PCPTraversal.budget
    calc
      _ ≤ 1000000000000*(52*(N+1)^11)^12 := by gcongr; omega
      _ = _ := by rw [mul_pow,←pow_mul]; ring
  norm_num at ha hb
  unfold DecompositionAtom.envelope globalEnvelope globalCoefficient globalDegree
  omega

theorem global_atom (groups : List (List ℤ)) (values : List ℤ) (z : ℤ) (N : ℕ)
    (hv : values∈groups) (hz : z∈values) (hN : (nativeGroups groups).length≤N) :
    DecompositionAtom.budget z+1 ≤ globalEnvelope N := by
  have hw := (native_member values z hz).trans ((group_native groups values hv).trans hN)
  have he : DecompositionAtom.envelope (natBitLength z.natAbs)≤DecompositionAtom.envelope N := by
    unfold DecompositionAtom.envelope
    gcongr
  have hb := DecompositionAtom.budget_envelope z
  have hg := global_budget N
  omega

theorem global_child (groups : List (List ℤ)) (values : List ℤ) (N : ℕ)
    (hv : values∈groups) (hN : (nativeGroups groups).length≤N) :
    PCPTraversal.budget (PCPSerializerMass.mass (values.map (fun z => (CanonicalBinary.encodeInt z).bits)))+1 ≤
      globalEnvelope N := by
  have hm := atom_mass values N ((group_native groups values hv).trans hN)
  have hb : PCPTraversal.budget (PCPSerializerMass.mass (values.map (fun z => (CanonicalBinary.encodeInt z).bits))) ≤
      PCPTraversal.budget (21*(N+1)^6) := by unfold PCPTraversal.budget; gcongr
  have hg := global_budget N
  omega

theorem global_outer (groups : List (List ℤ)) (N : ℕ)
    (hpos : ∀ values∈groups,0<values.length) (hN : (nativeGroups groups).length≤N) :
    PCPTraversal.budget (PCPSerializerMass.mass (childFields groups))+1 ≤ globalEnvelope N := by
  have hm := outer_mass groups N hpos hN
  have hb : PCPTraversal.budget (PCPSerializerMass.mass (childFields groups)) ≤
      PCPTraversal.budget (51*(N+1)^11) := by unfold PCPTraversal.budget; gcongr
  have hg := global_budget N
  omega

end NearCubicWires.RepairOrdinary.DecompositionCodeBounds
