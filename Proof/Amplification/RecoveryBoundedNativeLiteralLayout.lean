import Proof.Amplification.RecoveryBoundedNativeExpr

/-! The bounded verifier's unary equality grammar emits its actual input
node and, only when the runtime polarity cell says so, its original NOT
node. This two-call controller retains the original raw addresses. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedNativeLiteral
open LocalBitMultitape RepairRepresentation RecoveryExecution PCPPNativeClauseBank FinitePredicateCircuit
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def first := TapeEmbedding.machine 1 (nodeMachine 1 0 1 0 2)
noncomputable def second := TapeEmbedding.machine 1 (nodeMachine 2 0 3 0 2)
noncomputable def bank : Fin 2→Σ s,Machine 30 s := ![⟨_,first⟩,⟨_,second⟩]
noncomputable def sizes (j : Fin 2) := (bank j).1
noncomputable def programs (j : Fin 2) : Machine 30 (sizes j) := (bank j).2
def next (j : Fin 2) (_ : Fin (sizes j)) (bs : Fin 30→Bool) : Option (Fin 2) :=
  if j=0 then if bs 29 then some 1 else none else none
noncomputable def machine := RecoveryCalls.machine sizes programs 0 next

def values (index position : ℕ) : Fin 7→ℕ := ![0,index,0,position,0,0,0]
def heads (out : List Bool) : Fin 30→ℕ := Fin.addCases (m:=29) (n:=1) (motive:=fun _=>ℕ) (PCPPNativeClauseBank.heads out) (fun _=>0)
def data (index position C : ℕ) (negative : Bool) (out : List Bool) : Fin 30→List Bool :=
  Fin.addCases (m:=29) (n:=1) (motive:=fun _=>List Bool) (PCPPNativeClauseBank.data (values index position) C out) (fun _=>[negative])
noncomputable def boundary (j : Fin 2) (h : Fin 30→ℕ) (d : Fin 30→List Bool) :=
  controlConfig (RecoveryCalls.code sizes j) (RecoveryCalls.restarted (programs j) h d)
noncomputable def entry (index position C : ℕ) (negative : Bool) (out : List Bool) :=
  boundary 0 (heads out) (data index position C negative out)
def inputBits (index : ℕ) := natWord 1++natWord index++natWord 0
def notBits (position : ℕ) := natWord 2++natWord position++natWord 0
def emitted (index position : ℕ) (negative : Bool) := inputBits index++if negative then notBits position else []
def firstBudget (index position C : ℕ) := nodeBudget 1 0 1 0 2 (values index position) C
def secondBudget (index position C : ℕ) := nodeBudget 2 0 3 0 2 (values index position) C
def budget (index position C : ℕ) := firstBudget index position C+secondBudget index position C+2

theorem emitted_expr {n : ℕ} (index : Fin n) (position : ℕ) (negative : Bool) :
    emitted index.val position negative=
      (RecoveryBoundedNative.exprNodes position (if negative then
        BoolExpr.not (BoolExpr.input index) else BoolExpr.input index)).flatMap PCPPRequestNodeSchema.native := by
  cases negative <;> simp [emitted,inputBits,notBits,RecoveryBoundedNative.exprNodes,
    BoolExpr.nodeCount,PCPPRequestNodeSchema.native,PCPPRequestNodeSchema.fields,List.append_assoc]

theorem call_run (j l : Fin 2) (fuel : ℕ) (h : Fin 30→ℕ) (d : Fin 30→List Bool)
    (r : ExecutionReceipt 30 (sizes j))
    (hr : runFrom (programs j) fuel (RecoveryCalls.restarted (programs j) h d)=some r)
    (hn : next j r.final.control r.final.scanned=some l) :
    Timed machine (r.steps+1) (boundary j h d) (boundary l r.final.heads r.final.tapes) := by
  obtain ⟨hp,hh⟩:=prefix_of_run (programs j) fuel _ r hr
  have body:=RecoveryCalls.body_timed sizes programs 0 next j ⟨r.peakTapeCells,hp⟩
  have ret:=RecoveryCalls.return_step sizes programs 0 next j l r.final hh hn
  exact body.trans (Timed.single (by simp [RecoveryCalls.machine,controlConfig,RecoveryCalls.code]) ret)

theorem stop_run (j : Fin 2) (fuel : ℕ) (h : Fin 30→ℕ) (d : Fin 30→List Bool)
    (r : ExecutionReceipt 30 (sizes j))
    (hr : runFrom (programs j) fuel (RecoveryCalls.restarted (programs j) h d)=some r)
    (hn : next j r.final.control r.final.scanned=none) :
    Timed machine (r.steps+1) (boundary j h d) (RecoveryCalls.stopped sizes r.final.heads r.final.tapes) := by
  obtain ⟨hp,hh⟩:=prefix_of_run (programs j) fuel _ r hr
  have body:=RecoveryCalls.body_timed sizes programs 0 next j ⟨r.peakTapeCells,hp⟩
  have ret:=RecoveryCalls.stop_step sizes programs 0 next j r.final hh hn
  exact body.trans (Timed.single (by simp [RecoveryCalls.machine,controlConfig,RecoveryCalls.code]) ret)

end NearCubicWires.RepairOrdinary.RecoveryBoundedNativeLiteral
