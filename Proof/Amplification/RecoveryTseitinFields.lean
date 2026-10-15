import Proof.Amplification.RecoveryFormulaPayload
import Proof.Amplification.RecoveryQueryCellReuse

/-! The six existing pair/list-cell operations for one original Tseitin
clause. Signs use the original Encodable Bool convention, not native PCP
literal parity. This is the exact clause-code field expected by the existing
balanced formula serializer. -/
namespace NearCubicWires.RepairSource.RecoveryTseitin
open RepairOrdinary TseitinCNF CircuitInputCNF
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev Literals := Fin 3 → EncodedLiteral
def clause (ls : Literals) : EncodedClause := [ls 0,ls 1,ls 2]
def literalCode (l : EncodedLiteral) := Nat.pair l.1.toNat l.2
def tailOne (ls : Literals) := Nat.pair (literalCode (ls 2)) 0+1
def tailTwo (ls : Literals) := Nat.pair (literalCode (ls 1)) (tailOne ls)+1
def clauseCode (ls : Literals) := Nat.pair (literalCode (ls 0)) (tailTwo ls)+1
def operations : Fin 6→Bool := ![false,false,false,true,true,true]
def lefts (ls : Literals) : Fin 6→Nat :=
  ![(ls 0).1.toNat,(ls 1).1.toNat,(ls 2).1.toNat,
    literalCode (ls 2),literalCode (ls 1),literalCode (ls 0)]
def rights (ls : Literals) : Fin 6→Nat :=
  ![(ls 0).2,(ls 1).2,(ls 2).2,0,tailOne ls,tailTwo ls]
def values (ls : Literals) : Fin 6→Nat :=
  ![literalCode (ls 0),literalCode (ls 1),literalCode (ls 2),
    tailOne ls,tailTwo ls,clauseCode ls]

theorem node_result (ls : Literals) (j : Fin 6) :
    RecoveryQueryCell.result (operations j) (lefts ls j) (rights ls j)=values ls j := by
  fin_cases j <;> rfl

theorem literal_code (l : EncodedLiteral) : literalCode l=Encodable.encode l := by
  rcases l with ⟨b,n⟩
  cases b <;> rfl

theorem exact_code (ls : Literals) : clauseCode ls=Encodable.encode (clause ls) := by
  simp [clauseCode,tailTwo,tailOne,clause,Encodable.encode_list_cons,literal_code]

theorem values_le (ls : Literals) (j : Fin 6) : values ls j ≤ clauseCode ls := by
  have h21 : literalCode (ls 2) ≤ tailOne ls :=
    (Nat.left_le_pair _ _).trans (Nat.le_add_right _ 1)
  have h12 : tailOne ls ≤ tailTwo ls :=
    (Nat.right_le_pair _ _).trans (Nat.le_add_right _ 1)
  have h1 : literalCode (ls 1) ≤ tailTwo ls :=
    (Nat.left_le_pair _ _).trans (Nat.le_add_right _ 1)
  have h2 : tailTwo ls ≤ clauseCode ls :=
    (Nat.right_le_pair _ _).trans (Nat.le_add_right _ 1)
  have h0 : literalCode (ls 0) ≤ clauseCode ls :=
    (Nat.left_le_pair _ _).trans (Nat.le_add_right _ 1)
  fin_cases j
  · exact h0
  · exact h1.trans h2
  · exact h21.trans (h12.trans h2)
  · exact h12.trans h2
  · exact h2
  · exact Nat.le_refl _

def width (ls : Literals) := natBitLength (clauseCode ls)
def capacity (ls : Literals) := 16384*(width ls+1)^2+1

theorem argument_widths (ls : Literals) (j : Fin 6) :
    (lefts ls j).bits.length ≤ width ls ∧ (rights ls j).bits.length ≤ width ls := by
  have hn := values_le ls j
  rw [←node_result] at hn
  have hp : Nat.pair (lefts ls j) (rights ls j) ≤ values ls j := by
    rw [←node_result]
    exact Nat.le_add_right _ _
  have hl := (Nat.left_le_pair (lefts ls j) (rights ls j)).trans (hp.trans (values_le ls j))
  have hr := (Nat.right_le_pair (lefts ls j) (rights ls j)).trans (hp.trans (values_le ls j))
  exact ⟨(PCPSerializerMass.nat_bits_width _).trans
    (Nat.add_le_add_right (Nat.log_mono_right hl) 1),
    (PCPSerializerMass.nat_bits_width _).trans
    (Nat.add_le_add_right (Nat.log_mono_right hr) 1)⟩

theorem cell_capacity (ls : Literals) (j : Fin 6) :
    RecoveryQueryCell.budget (operations j) (lefts ls j) (rights ls j)+1 ≤ capacity ls ∧
    2*(lefts ls j).bits.length+1 ≤ capacity ls ∧
    2*(rights ls j).bits.length+1 ≤ capacity ls := by
  obtain ⟨hl,hr⟩ := argument_widths ls j
  have hb := RecoveryQueryCell.budget_quadratic (operations j) (lefts ls j) (rights ls j)
  have hs : (lefts ls j).bits.length+(rights ls j).bits.length+1 ≤ 2*(width ls+1) := by omega
  have hsq := Nat.pow_le_pow_left hs 2
  have he : (2*(width ls+1))^2=4*(width ls+1)^2 := by ring
  rw [he] at hsq
  have hw : width ls+1 ≤ (width ls+1)^2 := by nlinarith
  unfold capacity
  omega

theorem output_length (ls : Literals) :
    (frame (Encodable.encode (clause ls)).bits).length ≤ 2*width ls+1 := by
  rw [←exact_code,frame_length]
  have h := PCPSerializerMass.nat_bits_width (clauseCode ls)
  change (clauseCode ls).bits.length ≤ width ls at h
  omega

theorem formula_fields {n : Nat} (c : BooleanCircuit n) :
    RecoveryFormulaPayload.fields (circuitInputFormula c)=
      RecoveryFormulaPayload.fields (circuitInputTautologies n) ++
      (RecoveryFormulaPayload.fields (circuitInputNodesClausesFrom 0 c.nodes) ++
        [(Encodable.encode (positiveUnit (circuitInputGateVariable n c.output.val))).bits]) := by
  simp only [RecoveryFormulaPayload.fields,circuitInputFormula,List.map_append,List.map_cons,List.map_nil]

end NearCubicWires.RepairSource.RecoveryTseitin
