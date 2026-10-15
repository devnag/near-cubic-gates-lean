import Proof.PCP.PCPPNativeClauseDescriptorSource
import Proof.Circuits.BoundedOracleStructuralNodeSchedule

/-! Exact append schedule used by the original bounded verifier's grammar
and universal-query guards. Addresses are the original postorder compiler
addresses, including the terminal constants of its all/any expressions. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedNative
open SourceInterfaces FinitePredicateCircuit BoundedOracleStructuralCircuit
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def exprNodes {n : ℕ} (base : ℕ) : BoolExpr n→List (BooleanNode n)
  | .const b=>[.const b]
  | .input i=>[.input i]
  | .not e=>exprNodes base e++[.not (base+e.nodeCount-1)]
  | .and l r=>exprNodes base l++exprNodes (base+l.nodeCount) r++
      [.and (base+l.nodeCount-1) (base+l.nodeCount+r.nodeCount-1)]
  | .or l r=>exprNodes base l++exprNodes (base+l.nodeCount) r++
      [.or (base+l.nodeCount-1) (base+l.nodeCount+r.nodeCount-1)]

theorem compileExpr_length {n : ℕ} (b : BooleanDAGBuilder n) (e : BoolExpr n) :
    (compileExpr b e).final.nodes.length=b.nodes.length+e.nodeCount := by
  rw [(compileExpr b e).extension.nodes_eq,List.length_append,compileExpr_addedNodes]

theorem nodeCount_pos {n : ℕ} (e : BoolExpr n) : 0<e.nodeCount := by
  cases e <;> simp [BoolExpr.nodeCount]

theorem compileExpr_output {n : ℕ} (b : BooleanDAGBuilder n) (e : BoolExpr n) :
    (compileExpr b e).output.val=b.nodes.length+e.nodeCount-1 := by
  cases e with
  | const v=>rfl
  | input i=>rfl
  | not e=>
    change (compileExpr b e).final.nodes.length=_
    rw [compileExpr_length]
    simp [BoolExpr.nodeCount]
  | and l r=>
    change (compileExpr (compileExpr b l).final r).final.nodes.length=_
    rw [compileExpr_length,compileExpr_length]
    simp only [BoolExpr.nodeCount]
    omega
  | or l r=>
    change (compileExpr (compileExpr b l).final r).final.nodes.length=_
    rw [compileExpr_length,compileExpr_length]
    simp only [BoolExpr.nodeCount]
    omega

theorem compileExpr_nodes {n : ℕ} (b : BooleanDAGBuilder n) (e : BoolExpr n) :
    (compileExpr b e).extension.suffix=exprNodes b.nodes.length e := by
  induction e generalizing b with
  | const v=>rfl
  | input i=>rfl
  | not e ih=>
    change (compileExpr b e).extension.suffix++[.not (compileExpr b e).output.val]=_
    rw [ih,compileExpr_output]
    rfl
  | and l r ihl ihr=>
    change (compileExpr b l).extension.suffix++
      ((compileExpr (compileExpr b l).final r).extension.suffix++
        [.and (compileExpr b l).output.val (compileExpr (compileExpr b l).final r).output.val])=_
    rw [ihl,ihr,compileExpr_output,compileExpr_output,compileExpr_length]
    simp only [exprNodes,List.append_assoc]
  | or l r ihl ihr=>
    change (compileExpr b l).extension.suffix++
      ((compileExpr (compileExpr b l).final r).extension.suffix++
        [.or (compileExpr b l).output.val (compileExpr (compileExpr b l).final r).output.val])=_
    rw [ihl,ihr,compileExpr_output,compileExpr_output,compileExpr_length]
    simp only [exprNodes,List.append_assoc]

theorem exprNodes_length {n : ℕ} (base : ℕ) (e : BoolExpr n) :
    (exprNodes base e).length=e.nodeCount := by
  induction e generalizing base <;> simp_all [exprNodes,BoolExpr.nodeCount,Nat.add_assoc]

end NearCubicWires.RepairOrdinary.RecoveryBoundedNative
