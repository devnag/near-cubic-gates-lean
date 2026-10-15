import Proof.Circuits.DecompositionCodeBounds

/-! The outer child stream is bounded by the original native signed fields.
Children are nonempty because every exact child contains its target field. -/
namespace NearCubicWires.RepairOrdinary.DecompositionCodeBounds
open CanonicalBinary PCPSerializerMass
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def nativeGroups (groups : List (List ℤ)) := groups.flatMap native
def childFields (groups : List (List ℤ)) := groups.map (fun values => (child values).bits)
def outer (groups : List (List ℤ)) := encodeBalancedList (groups.map child)

theorem group_native (groups : List (List ℤ)) (values : List ℤ) (hv : values∈groups) :
    (native values).length ≤ (nativeGroups groups).length := by
  induction groups with
  | nil => simp at hv
  | cons a groups ih =>
    simp only [List.mem_cons] at hv
    simp only [nativeGroups,List.flatMap_cons,List.length_append]
    rcases hv with hv|hv
    · subst a; omega
    · have h := ih hv
      change (native values).length ≤ (groups.flatMap native).length at h
      omega

theorem groups_count (groups : List (List ℤ)) (hpos : ∀ values∈groups,0<values.length) :
    groups.length ≤ (nativeGroups groups).length := by
  induction groups with
  | nil => rfl
  | cons a groups ih =>
    have ha := hpos a (by simp)
    have hab := native_count a
    have ht := ih (by intro values hv; exact hpos values (by simp [hv]))
    simp only [nativeGroups,List.flatMap_cons,List.length_append,List.length_cons] at ht ⊢
    omega

theorem outer_mass (groups : List (List ℤ)) (N : ℕ)
    (hpos : ∀ values∈groups,0<values.length) (hN : (nativeGroups groups).length≤N) :
    mass (childFields groups) ≤ 51*(N+1)^11 := by
  have hc := (groups_count groups hpos).trans hN
  have hp : 1≤(N+1)^10 := Nat.one_le_pow 10 _ (by omega)
  have hs := sum_bound groups (fun values => 2*(child values).bits.length+1) (51*(N+1)^10) (by
    intro values hv
    have hw := (nat_bits_width (child values)).trans (child_width values N ((group_native groups values hv).trans hN))
    omega)
  have hm : groups.length*(51*(N+1)^10) ≤ 51*(N+1)^11 := by
    calc
      _ ≤ (N+1)*(51*(N+1)^10) := by gcongr; omega
      _ = _ := by ring
  simpa only [mass,childFields,List.map_map,Function.comp_def] using hs.trans hm

theorem outer_width (groups : List (List ℤ)) (N : ℕ)
    (hpos : ∀ values∈groups,0<values.length) (hN : (nativeGroups groups).length≤N) :
    natBitLength (outer groups) ≤ 53*(N+1)^15 := by
  have hc := (groups_count groups hpos).trans hN
  have hs := sum_bound groups (fun values => natBitLength (child values)) (25*(N+1)^10) (by
    intro values hv
    exact child_width values N ((group_native groups values hv).trans hN))
  have hs' : ((groups.map child).map natBitLength).sum ≤ 25*(N+1)^11 := by
    have hm : groups.length*(25*(N+1)^10) ≤ 25*(N+1)^11 := by
      calc
        _ ≤ (N+1)*(25*(N+1)^10) := by gcongr; omega
        _ = _ := by ring
    simpa only [List.map_map,Function.comp_def] using hs.trans hm
  have hp : 1≤(N+1)^11 := Nat.one_le_pow 11 _ (by omega)
  have hb : balancedListAtomBits (groups.map child) ≤ 26*(N+1)^11 := by
    unfold balancedListAtomBits
    omega
  have hcode := balancedListCodeBits_le (groups.map child)
  have hcount : (groups.map child).length ≤ N+1 := by simpa only [List.length_map] using hc.trans (Nat.le_succ _)
  have hproduct : 1+2*(groups.map child).length^4*balancedListAtomBits (groups.map child) ≤
      1+52*(N+1)^15 := by
    calc
      _ ≤ 1+2*(N+1)^4*(26*(N+1)^11) := by gcongr
      _ = _ := by ring
  have hp15 : 1≤(N+1)^15 := Nat.one_le_pow 15 _ (by omega)
  exact hcode.trans (hproduct.trans (by omega))

end NearCubicWires.RepairOrdinary.DecompositionCodeBounds
