import Proof.CaseAnalysis.RecoveryAddressBody

/-! The actual repeated address state retains native graph bytes, child
references, the same field index, and the consumed physical address prefix. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedAddress
open LocalBitMultitape SourceInterfaces RepairRepresentation
open BoundedOracleStructuralCircuit FinitePredicateCircuit RecoveryBoundedNative
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure State where
  position : ℕ
  value : ℕ
  out : List Bool
  skipped : List Bool
  stack : List Bool

def State.next {n bound : ℕ} (row : Fin (bound+1)) (start limit : ℕ)
    (hblock : start+limit ≤ rowWidth n bound) (bit : Bool) (a : State) : State:=
  let e:=if bit then unaryEqualsExpr row start limit a.value hblock else .const false
  ⟨a.position+e.nodeCount,a.value+1,
    a.out++(exprNodes a.position e).flatMap PCPPRequestNodeSchema.native,
    a.skipped++[bit],pushed (a.position+e.nodeCount-1) a.stack⟩
def State.iterate {n bound : ℕ} (row : Fin (bound+1)) (start limit : ℕ)
    (hblock : start+limit ≤ rowWidth n bound) : List Bool→State→State
  | [],a=>a
  | bit::rest,a=>State.iterate row start limit hblock rest (a.next row start limit hblock bit)
noncomputable def State.entry {n bound : ℕ} (row : Fin (bound+1)) (start limit W D : ℕ)
    (a : State) (source : List Bool) :=
  let index:=RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start
  (⟨body.start,heads a.out a.stack a.skipped.length,
    data index a.position (RecoveryBoundedSelectorLoop.capacity W) D a.value limit false a.out source a.stack index⟩ : Configuration 40 _)

theorem next_position {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (row : Fin (bound+1)) (start limit : ℕ) (a : State) (bit : Bool)
    (hblock : start+limit ≤ rowWidth n bound) (hp : a.position=b.nodes.length) :
    (a.next row start limit hblock bit).position=
      (compileExpr b (if bit then unaryEqualsExpr row start limit a.value hblock else .const false)).final.nodes.length := by
  rw [compileExpr_length]
  simp only [State.next,hp]

theorem next_bound {n bound : ℕ} (row : Fin (bound+1)) (start limit : ℕ)
    (hblock : start+limit ≤ rowWidth n bound) (bit : Bool) (a : State) :
    (a.next row start limit hblock bit).position ≤ a.position+3*limit+1 := by
  have h:=prefixCount_bound (unaryItems row start limit a.value hblock)
  have hl : (unaryItems row start limit a.value hblock).length=limit := by simp only [unaryItems,List.length_ofFn]
  rw [hl] at h
  cases bit <;>
    simp only [State.next,Bool.false_eq_true,↓reduceIte,BoolExpr.nodeCount,RecoveryBoundedSelectorLoop.unary_count] <;> omega

theorem state_run {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (row : Fin (bound+1)) (start limit W D : ℕ) (a : State) (bit : Bool) (tail : List Bool)
    (hblock : start+limit ≤ rowWidth n bound) (hb : a.position=b.nodes.length)
    (hi : RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start+limit ≤ W)
    (hp : a.position+3*limit ≤ W) (hv : a.value ≤ W)
    (hD : RecoveryBoundedNativeUnaryJoin.budget limit (RecoveryBoundedSelectorLoop.capacity W) ≤ D) :
    ∃ r,runFrom body (stepBudget W)
      (a.entry (n:=n) row start limit W D (a.skipped++bit::tail))=some r ∧
      r.steps ≤ stepBudget W ∧
      r.final.heads=((a.next row start limit hblock bit).entry (n:=n) row start limit W D (a.skipped++bit::tail)).heads ∧
      r.final.tapes=((a.next row start limit hblock bit).entry (n:=n) row start limit W D (a.skipped++bit::tail)).tapes := by
  rcases a with ⟨base,value,out,skipped,stack⟩
  dsimp only at hb hp hv
  subst base
  obtain ⟨r,hr,rs,rh,rt⟩:=body_run b row start limit value W D skipped.length out (skipped++bit::tail) stack bit
    (Streaming.read_append skipped tail bit) hblock hi hp hv hD
  refine ⟨r,hr,rs,?_,?_⟩
  · rw [rh,compileExpr_nodes,compileExpr_output]
    change heads _ _ (skipped.length+1)=heads _ _ (skipped++[bit]).length
    rw [List.length_append,List.length_singleton]
    rfl
  · rw [rt,compileExpr_nodes,compileExpr_output,compileExpr_length]
    rfl

end NearCubicWires.RepairOrdinary.RecoveryBoundedAddress
