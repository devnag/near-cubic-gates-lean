import Proof.CaseAnalysis.RecoverySelectorRestore

/-! Exact next builder and bounded erased stack for the original selector
loop. Its next value refers to the same shared description-variable block. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedSelectorLoop
open LocalBitMultitape SourceInterfaces RepairRepresentation
open BoundedOracleStructuralCircuit FinitePredicateCircuit RecoveryBoundedNative
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def head {n : ℕ} (b : BooleanDAGBuilder n) (e : BoolExpr n) (wire : LiveWire b) :=
  let condition:=compileExpr b e
  (compileAnd condition.final condition.live (wire.lift condition.extension)).prepend condition.extension

theorem head_suffix {n : ℕ} (b : BooleanDAGBuilder n) (e : BoolExpr n) (wire : LiveWire b) :
    (head b e wire).extension.suffix=(compileExpr b e).extension.suffix++
      [BooleanNode.and (compileExpr b e).output.val wire.output.val] := rfl

theorem head_length {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (row : Fin (bound+1)) (start limit value : ℕ) (wire : LiveWire b)
    (hblock : start+limit ≤ rowWidth n bound) :
    (head b (unaryEqualsExpr row start limit value hblock) wire).final.nodes.length=
      RecoveryBoundedSelectorJoin.counter b row start limit value hblock+2 := by
  change (compileAnd (compileExpr b _).final (compileExpr b _).live _).final.nodes.length=_
  rw [RecoveryBoundedUniversal.compileAnd_length,compileExpr_length,unary_expression,all_nodeCount]
  have hl : (unaryItems row start limit value hblock).length=limit := by simp [unaryItems]
  rw [hl]
  unfold RecoveryBoundedSelectorJoin.counter
  omega

theorem head_output {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (row : Fin (bound+1)) (start limit value : ℕ) (wire : LiveWire b)
    (hblock : start+limit ≤ rowWidth n bound) :
    (head b (unaryEqualsExpr row start limit value hblock) wire).output.val=
      RecoveryBoundedSelectorJoin.counter b row start limit value hblock+1 := by
  change (compileExpr b (unaryEqualsExpr row start limit value hblock)).final.nodes.length=_
  rw [compileExpr_length,unary_expression,all_nodeCount]
  have hl : (unaryItems row start limit value hblock).length=limit := by simp [unaryItems]
  rw [hl]
  unfold RecoveryBoundedSelectorJoin.counter
  omega

theorem erased_bound (conjunction : Bool) (W : ℕ) (refs : List ℕ)
    (a : RecoveryBoundedNativeFoldLoop.State) (href : ∀ ref∈refs,ref≤W) :
    (a.iterate conjunction refs).erased ≤ a.erased+refs.length*(2*W+1) := by
  induction refs generalizing a with
  | nil=>simp [RecoveryBoundedNativeFoldLoop.State.iterate]
  | cons ref refs ih=>
    have hr:=href ref (by simp)
    have h:=ih (a.next conjunction ref) (by intro v hv; exact href v (by simp [hv]))
    simp only [RecoveryBoundedNativeFoldLoop.State.iterate,
      RecoveryBoundedNativeFoldLoop.State.next,List.length_cons,Nat.add_mul,Nat.one_mul] at h ⊢
    omega

theorem unary_erased_bound {n : ℕ} (base acc W C : ℕ) (out : List Bool) (items : List (Item n))
    (hp : base+3*items.length≤W) (hC : 16384*(W+1)^2≤C) :
    (RecoveryBoundedNativeFoldLoop.State.iterate true (literalReferences base items).reverse
      ⟨acc,0,0,out⟩).erased≤C := by
  have hc:=prefixCount_bound items
  have href : ∀ ref∈(literalReferences base items).reverse,ref≤W := by
    intro ref hr
    have h:=references_bound base items ref (List.mem_reverse.mp hr)
    omega
  have h:=erased_bound true W (literalReferences base items).reverse ⟨acc,0,0,out⟩ href
  simp only [Nat.zero_add,List.length_reverse,references_length] at h
  have hl : items.length≤W := by omega
  have hm:=Nat.mul_le_mul_right (2*W+1) hl
  nlinarith [Nat.zero_le (W*W)]

theorem pad_erased (C z : ℕ) (hz : z≤C) :
    ZeroPadding.pad C (List.replicate z false)=List.replicate C false := by
  simp only [ZeroPadding.pad,List.length_replicate,←List.replicate_add]
  congr 1
  omega

end NearCubicWires.RepairOrdinary.RecoveryBoundedSelectorLoop
