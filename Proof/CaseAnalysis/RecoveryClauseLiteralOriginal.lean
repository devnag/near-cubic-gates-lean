import Proof.CaseAnalysis.RecoveryClauseOrRun

/-! Apply the complete reusable literal to the exact original live query
wires and original binary literalCode stream. All resource bounds follow
from the same W/C/L bank envelope. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedClauseLiteralOriginal
open LocalBitMultitape SourceInterfaces RepairRepresentation RecoveryRootRound
open BoundedOracleStructuralCircuit FinitePredicateCircuit RecoveryBoundedClauseState
open RecoveryBoundedLiteral (query negative references reference)
open RecoveryBoundedSelectorLoop (sourceWord)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def before {n q : ℕ} {b : BooleanDAGBuilder n} (values : List (LiveWire b)) (literal : Literal q):=
  (references values).take (query literal).val
theorem before_length {n q : ℕ} {b : BooleanDAGBuilder n} (values : List (LiveWire b))
    (hv : values.length=q) (literal : Literal q) : (before values literal).length=(query literal).val := by
  simp only [before,references,List.length_take,List.length_map,hv,Nat.min_eq_left (query literal).isLt.le]
theorem code_eq {q : ℕ} (literal : Literal q) :
    RecoveryBoundedLiteralDriver.code (query literal).val (negative literal)=(RepairSource.literalCode literal).bits := by
  cases literal <;> simp [RecoveryBoundedLiteralDriver.code,query,negative,RepairSource.literalCode]
theorem graph_eq {n q : ℕ} (b : BooleanDAGBuilder n) (values : List (LiveWire b))
    (hv : values.length=q) (literal : Literal q) (second : Bool) (out : List Bool) :
    RecoveryBoundedClauseLiteralOutput.graph second (negative literal) (reference values hv literal) out=
      out++(compileLiteral b values hv literal).compiled.extension.suffix.flatMap PCPPRequestNodeSchema.native := by
  rw [RecoveryBoundedLiteral.original_native]
  unfold RecoveryBoundedClauseLiteralOutput.graph
  rw [RecoveryBoundedLiteral.emitted_not n (reference values hv literal) second]

theorem prefix_bound {n q : ℕ} (b : BooleanDAGBuilder n) (values : List (LiveWire b))
    (hv : values.length=q) (literal : Literal q) (W C : ℕ)
    (hb : b.nodes.length ≤ W) (hq : q ≤ W) (hC : 16384*(W+1)^2 ≤ C) :
    (sourceWord (before values literal)).length ≤ C := by
  have hlen : (before values literal).length ≤ W := by rw [before_length values hv literal];omega
  have hvals : ∀ r∈before values literal,r ≤ W := by
    intro r hr
    have hm : r∈references values:=List.mem_of_mem_take hr
    obtain ⟨w,_hw,rfl⟩:=List.mem_map.mp hm
    exact w.output.isLt.le.trans hb
  have hp:=RecoveryBoundedTableReferenceReset.source_length_bound (before values literal) W hvals
  have ht : (before values literal).length*(2*W+1) ≤ W*(2*W+1):=Nat.mul_le_mul_right _ hlen
  nlinarith [Nat.zero_le (W^2)]

theorem original_run {n q : ℕ} (b : BooleanDAGBuilder n) (values : List (LiveWire b))
    (hv : values.length=q) (literal : Literal q) (second : Bool)
    (H : Fin 71→ℕ) (A : Fin 71→List Bool) (left right W C L : ℕ) (out pre source tail : List Bool)
    (h : State H A b.nodes.length left right C L out pre source (sourceWord (references values)))
    (hSource : source=pre++frame (RepairSource.literalCode literal).bits++tail)
    (hb : b.nodes.length ≤ W) (hq : q ≤ W) (hl : left ≤ W) (hr : right ≤ W)
    (hC : 16384*(W+1)^2 ≤ C) (hL : C+5*W+7 ≤ L) :
    let compiled:=compileLiteral b values hv literal
    let bits:=(RepairSource.literalCode literal).bits
    ∃ work r,runFrom (RecoveryBoundedLiteralStream.machine second) (literalBudget W C)
      ⟨(RecoveryBoundedLiteralStream.machine second).start,H,A⟩=some r ∧
      r.steps ≤ literalBudget W C ∧
      r.final.heads=RecoveryBoundedClauseLiteralOutput.heads H second (negative literal) (reference values hv literal) out pre bits ∧
      r.final.tapes=RecoveryBoundedClauseLiteralOutput.data A second (negative literal) (before values literal)
        (reference values hv literal) b.nodes.length C out bits work ∧
      State r.final.heads r.final.tapes compiled.compiled.final.nodes.length
        (if second then left else compiled.compiled.output.val) (if second then compiled.compiled.output.val else right) C L
        (out++compiled.compiled.extension.suffix.flatMap PCPPRequestNodeSchema.native) (pre++frame bits) source
        (sourceWord (references values)) := by
  have hi : (before values literal).length ≤ W := by rw [before_length values hv literal];omega
  have href : reference values hv literal ≤ W:=(literalWire values hv literal).output.isLt.le.trans hb
  have hp:=prefix_bound b values hv literal W C hb hq hC
  have hlog : RecoveryBoundedClauseLookup.rawBudget (before values literal) (reference values hv literal) ≤ L := by
    unfold RecoveryBoundedClauseLookup.rawBudget
    omega
  have hc : RecoveryBoundedLiteralDriver.code (before values literal).length (negative literal)=
      (RepairSource.literalCode literal).bits := by rw [before_length values hv literal,code_eq]
  obtain ⟨work,r,rr,rs,rh,rt,hs⟩:=RecoveryBoundedClauseState.literal_run H A b.nodes.length left right W C L
    out pre source (sourceWord (references values)) h second (negative literal) (before values literal)
    (reference values hv literal) tail (sourceWord ((references values).drop ((query literal).val+1)))
    (by rw [hc];exact hSource) (RecoveryBoundedLiteral.literal_stream values hv literal) hlog hp hi href hb hl hr hC
  rw [hc] at rh rt hs
  refine ⟨work,r,rr,rs,rh,rt,?_⟩
  rw [RecoveryBoundedLiteral.original_output,RecoveryBoundedLiteral.original_count,←graph_eq b values hv literal second out]
  exact hs

end NearCubicWires.RepairOrdinary.RecoveryBoundedClauseLiteralOriginal
