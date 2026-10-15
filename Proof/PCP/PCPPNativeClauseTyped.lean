import Proof.PCP.PCPPNativeClauseFullCapacity

/-! The reusable clause machine is applied to the literal original compact
PCP clause fields and returns the exact native DAG clause nodes. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeClauseTyped
open LocalBitMultitape RadixSemantics RepairSource SourceInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def index {q : ℕ} : Literal q→ℕ | .positive i=>i.val | .negative i=>i.val
def negative {q : ℕ} : Literal q→Bool | .positive _=>false | .negative _=>true
def bits {q : ℕ} (clause : Fin 3→Literal q) := fun j=>(literalCode (clause j)).bits
def fields {q : ℕ} (clause : Fin 3→Literal q) := PCPPNativeClauseTriple.fields (bits clause)
def reference {q : ℕ} (stride p n : ℕ) (literal : Literal q) :=
  PCPPNativeClauseReusable.reference (index literal) stride (negative literal) p n
def refs {q : ℕ} (stride p n : ℕ) (clause : Fin 3→Literal q) := fun j=>reference stride p n (clause j)

theorem original_fields {q : ℕ} (clause : Fin 3→Literal q) :
    fields clause=ProjectionNormalization.ClauseEquality.stream (ProjectionNormalization.DedupBytes.row clause) := rfl

theorem code_value {q : ℕ} (literal : Literal q) :
    value (literalCode literal).bits=2*index literal+(negative literal).toNat := by
  rw [CanonicalPositiveOutput.nat_bits_value]
  cases literal <;> rfl

theorem index_lt {q : ℕ} (literal : Literal q) : index literal<q := by
  cases literal with | positive i=>exact i.isLt | negative i=>exact i.isLt

theorem query_reference {q : ℕ} (size output : ℕ) (literal : Literal q) :
    reference (2*size+1) (2*output+1) (2*size) literal=
      PCPPSubstitution.queryAddress 0 size output (index literal) (negative literal) := by
  cases literal <;> simp [reference,PCPPNativeClauseReusable.reference,index,negative,
    PCPPNativeClauseReference.offset,PCPPNativeClauseOffset.value,PCPPSubstitution.queryAddress,
    PCPPSubstitution.queryOffset]

theorem clause_run {q : ℕ} (r stride p n W C base accumulator : ℕ)
    (clause : Fin 3→Literal q) (pre tail out : List Bool)
    (hq : q≤W) (hs : stride≤W) (hp : p≤W) (hn : n≤W)
    (hl : ∀ j,(bits clause j).length≤W) (hr : ∀ j,refs stride p n clause j≤W)
    (ha : accumulator≤base) (hb : base+3≤W) (hC : 16384*(W+1)^2≤C) :
    ∃ result,runFrom PCPPNativeClauseReuse.machine (48*C+128)
      (PCPPNativeClauseReuse.entry PCPPNativeClauseReuse.machine (pre++fields clause++tail) pre.length
        stride p n C base accumulator 0 (fun _=>0) out)=some result ∧
      result.final.heads=PCPPNativeClauseBody.heads (pre++fields clause).length
        (out++(PCPPNative.clauseNodes (r:=r) base accumulator (refs stride p n clause)).flatMap PCPPRequestNodeSchema.native) ∧
      result.final.tapes=PCPPNativeClauseReuse.data (pre++fields clause++tail) stride p n C (base+3) (base+2) 0 (fun _=>0)
        (out++(PCPPNative.clauseNodes (r:=r) base accumulator (refs stride p n clause)).flatMap PCPPRequestNodeSchema.native) ∧
      result.steps≤48*C+128 := by
  have hc:=PCPPNativeClauseCapacity.width_le_capacity W C hC
  have field (j : Fin 3) : PCPPNativeClauseField.budget (bits clause j) (index (clause j))
      (negative (clause j)) stride p n+1≤C :=
    PCPPNativeClauseCapacity.field_capacity _ _ _ stride p n W C (code_value _)
      (Nat.le_trans (Nat.le_of_lt (index_lt _)) hq) hs hp hn (hl j) hC
  have block:=PCPPNativeClauseCapacity.block_capacity base accumulator W C (refs stride p n clause)
    (by omega) (by omega) hr hC
  have h:=PCPPNativeClauseReuse.uniform_run pre tail (bits clause) (fun j=>index (clause j))
    (fun j=>negative (clause j)) stride p n C base accumulator out (fun j=>code_value (clause j)) field block
    (fun j=>(hr j).trans hc) ha (by omega)
  have he : PCPPNativeClauseBank.emitted (PCPPNativeClauseBank.values base accumulator
      (PCPPNativeClauseBody.references (fun j=>index (clause j)) (fun j=>negative (clause j)) stride p n))=
      (PCPPNative.clauseNodes (r:=r) base accumulator (refs stride p n clause)).flatMap PCPPRequestNodeSchema.native :=
    PCPPNativeClauseBank.emitted_nodes r base accumulator (refs stride p n clause)
  obtain ⟨result,hresult,hheads,htapes,hsteps⟩:=h
  rw [he] at hheads htapes
  exact ⟨result,hresult,hheads,htapes,hsteps⟩

end NearCubicWires.RepairOrdinary.PCPPNativeClauseTyped
