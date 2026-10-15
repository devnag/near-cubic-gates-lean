import Proof.Circuits.DecompositionGlobalBudget

/-! The exact native weight/target grouping and final local codec. Every
child includes its target; no nonempty-child assumption is imported. -/
namespace NearCubicWires.RepairOrdinary.DecompositionSchema
open LocalBitMultitape CanonicalBinary RepairRepresentation DecompositionCodeBounds
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def fields {n : ℕ} (g : ExactThresholdGate n) : List ℤ := List.ofFn g.weight++[g.target]
def groups {n : ℕ} (children : List (ExactThresholdGate n)) := children.map fields
def values {n : ℕ} (children : List (ExactThresholdGate n)) := (groups children).flatten
def payload {n : ℕ} (children : List (ExactThresholdGate n)) := natWord n++exactListWord children
def measured {n : ℕ} (children : List (ExactThresholdGate n)) := (frame (payload children)).length
def output {n : ℕ} (children : List (ExactThresholdGate n)) := outer (groups children)

theorem fields_length {n : ℕ} (g : ExactThresholdGate n) : (fields g).length=n+1 := by
  simp [fields]

theorem groups_length {n : ℕ} (children : List (ExactThresholdGate n)) :
    (groups children).length=children.length := by simp [groups]

theorem group_length {n : ℕ} (children : List (ExactThresholdGate n))
    (xs : List ℤ) (hx : xs∈groups children) : xs.length=n+1 := by
  obtain ⟨g,_,rfl⟩ := List.mem_map.mp hx
  exact fields_length g

theorem group_positive {n : ℕ} (children : List (ExactThresholdGate n)) :
    ∀ xs∈groups children,0<xs.length := by
  intro xs hx
  rw [group_length children xs hx]
  omega

theorem values_length {n : ℕ} (children : List (ExactThresholdGate n)) :
    (values children).length=(n+1)*children.length := by
  induction children with
  | nil => simp [values,groups]
  | cons g children ih =>
    simp only [values,groups,List.map_cons,List.flatten_cons,List.length_append,fields_length,
      List.length_cons] at ih ⊢
    nlinarith

theorem native_fields {n : ℕ} (g : ExactThresholdGate n) : native (fields g)=exactWord g := by
  simp [native,fields,exactWord]

theorem native_groups {n : ℕ} (children : List (ExactThresholdGate n)) :
    nativeGroups (groups children)=children.flatMap exactWord := by
  induction children with
  | nil => rfl
  | cons g children ih =>
    simp only [nativeGroups,groups,List.map_cons,List.flatMap_cons,native_fields] at ih ⊢
    rw [ih]

theorem native_values {n : ℕ} (children : List (ExactThresholdGate n)) :
    native (values children)=nativeGroups (groups children) := by
  induction children with
  | nil => rfl
  | cons g children ih =>
    simp only [native,values,groups,List.map_cons,List.flatten_cons,List.flatMap_append,
      nativeGroups,List.flatMap_cons] at ih ⊢
    rw [ih]

theorem payload_eq {n : ℕ} (children : List (ExactThresholdGate n)) :
    payload children=natWord n++natWord children.length++native (values children) := by
  rw [native_values,native_groups]
  simp only [payload,exactListWord,List.append_assoc]

theorem native_measured {n : ℕ} (children : List (ExactThresholdGate n)) :
    (nativeGroups (groups children)).length ≤ measured children := by
  rw [native_groups]
  simp only [measured,payload,frame_length,exactListWord,List.length_append]
  omega

theorem output_decode {n : ℕ} (children : List (ExactThresholdGate n)) :
    decodeBalancedList (output children)=some (children.map (fun g =>
      encodeBalancedList ((List.ofFn g.weight).map encodeInt++[encodeInt g.target]))) := by
  simp [output,outer,decodeBalancedList_encode,groups,child,atoms,fields]

theorem output_width {n : ℕ} (children : List (ExactThresholdGate n)) :
    natBitLength (output children) ≤ 53*(measured children+1)^15 :=
  outer_width (groups children) (measured children) (group_positive children) (native_measured children)

end NearCubicWires.RepairOrdinary.DecompositionSchema
