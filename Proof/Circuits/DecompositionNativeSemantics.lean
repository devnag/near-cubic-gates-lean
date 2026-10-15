import Proof.Circuits.DecompositionGlobalLayout

/-! Exact semantic reconciliation of all three uses of the shared codec. -/
namespace NearCubicWires.RepairOrdinary.DecompositionNesting
open CanonicalBinary DecompositionCodeBounds
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem atom_code (xs : List ℤ) : PCPTraversal.code (atomFields xs)=child xs := by
  simp only [PCPTraversal.code,PCPSerializerMass.values,atomFields,child,atoms,
    List.map_map,Function.comp_def,CanonicalPositiveOutput.nat_bits_value]

theorem child_fields (groups : List (List ℤ)) :
    DecompositionChildOuter.fields (fieldGroups groups)=childFields groups := by
  simp only [DecompositionChildOuter.fields,fieldGroups,childFields,List.map_map,Function.comp_def,atom_code]

theorem outer_code (groups : List (List ℤ)) :
    PCPTraversal.code (DecompositionChildOuter.fields (fieldGroups groups))=outer groups := by
  rw [child_fields]
  simp only [PCPTraversal.code,PCPSerializerMass.values,childFields,outer,List.map_map,
    Function.comp_def,CanonicalPositiveOutput.nat_bits_value]

theorem native_flatten (groups : List (List ℤ)) :
    native groups.flatten=nativeGroups groups := by
  induction groups with
  | nil => rfl
  | cons xs groups ih =>
    simp only [List.flatten_cons,native,List.flatMap_append,nativeGroups,List.flatMap_cons] at ih ⊢
    rw [ih]

end NearCubicWires.RepairOrdinary.DecompositionNesting
