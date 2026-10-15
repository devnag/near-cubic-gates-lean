import Proof.CaseAnalysis.RecoveryAddressTail

/-! One complete original address-expression child, including its actual
branch, saved live output, graph counter, next value and source cursor. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedAddress
open LocalBitMultitape SourceInterfaces RepairRepresentation Composition
open BoundedOracleStructuralCircuit FinitePredicateCircuit RecoveryBoundedNative
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def body:=Composition.machine branch tailMachine
def bodyBudget (acc index value limit C : ℕ):=branchBudget limit C+1+tailBudget acc index value C
def stepBudget (W : ℕ):=33554432*(W+1)^3

theorem child_output_bound {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (row : Fin (bound+1)) (start limit value W : ℕ) (bit : Bool)
    (hblock : start+limit ≤ rowWidth n bound) (hp : b.nodes.length+3*limit ≤ W) :
    (compileExpr b (if bit then unaryEqualsExpr row start limit value hblock else .const false)).output.val ≤ W := by
  cases bit
  · change b.nodes.length ≤ W
    omega
  · change (compileExpr b (unaryEqualsExpr row start limit value hblock)).output.val ≤ W
    rw [compileExpr_output,RecoveryBoundedSelectorLoop.unary_count]
    have h:=prefixCount_bound (unaryItems row start limit value hblock)
    have hl : (unaryItems row start limit value hblock).length=limit := by simp only [unaryItems,List.length_ofFn]
    rw [hl] at h
    omega

theorem body_budget_cubic (acc index value limit W : ℕ)
    (ha : acc ≤ W) (hi : index ≤ W) (hv : value ≤ W) (hl : limit ≤ W) :
    bodyBudget acc index value limit (RecoveryBoundedSelectorLoop.capacity W) ≤ stepBudget W := by
  have h:=RecoveryBoundedUnaryReuse.budget_cubic limit W hl
  have hf : RecoveryBoundedSelectorFinish.falseBits.length ≤ 100 := by decide
  unfold bodyBudget branchBudget tailBudget RecoveryBoundedSelectorLoop.capacity stepBudget
  nlinarith [Nat.zero_le (W^2),Nat.zero_le (W^3)]

theorem body_run {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (row : Fin (bound+1)) (start limit value W D pos : ℕ) (out source stack : List Bool)
    (bit : Bool) (hread : readTapeBit source pos=bit)
    (hblock : start+limit ≤ rowWidth n bound)
    (hi : RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start+limit ≤ W)
    (hp : b.nodes.length+3*limit ≤ W) (hv : value ≤ W)
    (hD : RecoveryBoundedNativeUnaryJoin.budget limit (RecoveryBoundedSelectorLoop.capacity W) ≤ D) :
    let expression:=if bit then unaryEqualsExpr row start limit value hblock else .const false
    let compiled:=compileExpr b expression
    let emitted:=out++compiled.extension.suffix.flatMap PCPPRequestNodeSchema.native
    let index:=RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start
    let saved:=pushed compiled.output.val stack
    ∃ r,runFrom body (stepBudget W)
      ⟨body.start,heads out stack pos,data index b.nodes.length (RecoveryBoundedSelectorLoop.capacity W) D value limit false out source stack index⟩=some r ∧
      r.steps ≤ stepBudget W ∧ r.final.heads=heads emitted saved (pos+1) ∧
      r.final.tapes=data index compiled.final.nodes.length (RecoveryBoundedSelectorLoop.capacity W) D (value+1) limit false emitted source saved index := by
  let C:=RecoveryBoundedSelectorLoop.capacity W
  let index:=RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start
  let expression:=if bit then unaryEqualsExpr row start limit value hblock else .const false
  let compiled:=compileExpr b expression
  let emitted:=out++compiled.extension.suffix.flatMap PCPPRequestNodeSchema.native
  let flag:=bit && (RecoveryBoundedUnaryReuse.forward (n:=n) row start b.nodes.length value limit out).flag
  have hacc : compiled.output.val ≤ W:=child_output_bound b row start limit value W bit hblock hp
  have hindex : index ≤ W := by dsimp only [index];omega
  have hic : index+1 ≤ C := by dsimp only [C,RecoveryBoundedSelectorLoop.capacity];nlinarith [Nat.zero_le (W^2)]
  have hvc : value+1 ≤ C := by dsimp only [C,RecoveryBoundedSelectorLoop.capacity];nlinarith [Nat.zero_le (W^2)]
  have hac : 2*compiled.output.val+2 ≤ C := by dsimp only [C,RecoveryBoundedSelectorLoop.capacity];nlinarith [Nat.zero_le (W^2)]
  have hspent : (if bit then 0 else index) ≤ C := by split <;> omega
  obtain ⟨a,ha,as,ah,atapes⟩:=branch_run b row start limit value W C D pos index out source stack bit hread
    hblock hi hp (Nat.le_refl _) hD
  obtain ⟨z,hz,zs,zh,zt⟩:=tail_run index (if bit then 0 else index) compiled.output.val C D value limit pos flag
    emitted source stack hic hspent hvc hac
  have hz' : runFrom tailMachine (tailBudget compiled.output.val index value C)
      (restart a.final tailMachine.start)=some z := by
    change runFrom tailMachine _ ⟨tailMachine.start,a.final.heads,a.final.tapes⟩=some z
    rw [ah,atapes]
    exact hz
  have full:=Composition.run_join branch tailMachine _ _ _ a z ha hz'
  change runFrom body (bodyBudget compiled.output.val index value limit C) _=some (joinedReceipt a z) at full
  have hb : bodyBudget compiled.output.val index value limit C ≤ stepBudget W:=
    body_budget_cubic compiled.output.val index value limit W hacc hindex hv (by omega)
  have more:=runFrom_moreFuel body _ (stepBudget W-bodyBudget compiled.output.val index value limit C) _
    (joinedReceipt a z) full
  rw [Nat.add_sub_of_le hb] at more
  have hcount : compiled.output.val+1=compiled.final.nodes.length := by
    dsimp only [compiled]
    rw [compileExpr_output,compileExpr_length]
    have hpos:=nodeCount_pos expression
    omega
  refine ⟨joinedReceipt a z,more,?_,zh,?_⟩
  · change a.steps+1+z.steps ≤ stepBudget W
    change a.steps ≤ branchBudget limit C at as
    change z.steps ≤ tailBudget compiled.output.val index value C at zs
    unfold bodyBudget at hb
    omega
  · change z.final.tapes=data index compiled.final.nodes.length C D (value+1) limit false emitted source (pushed compiled.output.val stack) index
    rw [zt,hcount]

end NearCubicWires.RepairOrdinary.RecoveryBoundedAddress
