import Proof.CaseAnalysis.RecoveryGrammarMetadata

/-! Canonical configurations for the fixed original row compositions.
The only sequencing operation is the existing ordinary machine composition. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarCold
open LocalBitMultitape Composition RecoveryRootRound SourceInterfaces RepairRepresentation
open FinitePredicateCircuit RecoveryBoundedNative
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure RowState where
  fields : Fin 78→List Bool
  node : ℕ
  out : List Bool
  stack : List Bool
  packet : List Bool

def RowState.configuration {s : ℕ} (a : RowState) (p : Machine 112 s)
    (B P : ℕ) (source : List Bool) (cold : Fin 33→List Bool):=
  entry p a.fields a.node B P a.out a.stack a.packet source cold
def Runs {s : ℕ} (p : Machine 112 s) (fuel B P : ℕ) (source : List Bool)
    (cold : Fin 33→List Bool) (a b : RowState) : Prop:=
  ∃ r,runFrom p fuel (a.configuration p B P source cold)=some r ∧ r.steps≤fuel ∧
    r.final.heads=heads b.out b.stack ∧
    r.final.tapes=data b.fields b.node B P b.out b.stack b.packet source cold

theorem Runs.join {s t u v B P : ℕ} {p : Machine 112 s} {q : Machine 112 t}
    {source : List Bool} {cold : Fin 33→List Bool} {a b c : RowState}
    (hp : Runs p u B P source cold a b) (hq : Runs q v B P source cold b c) :
    Runs (Composition.machine p q) (u+1+v) B P source cold a c := by
  obtain ⟨r,rr,rs,rh,rt⟩:=hp
  obtain ⟨d,dr,ds,dh,dt⟩:=hq
  have dr' : runFrom q v (restart r.final q.start)=some d := by
    change runFrom _ _ ⟨_,r.final.heads,r.final.tapes⟩=some d
    rw [rh,rt]
    exact dr
  have whole:=Composition.run_join p q _ _ _ r d rr dr'
  refine ⟨joinedReceipt r d,whole,?_,dh,dt⟩
  change r.steps+1+d.steps≤u+1+v
  omega

def expressionState {n : ℕ} (b : BooleanDAGBuilder n) (e : BoolExpr n)
    (out stack packet : List Bool) (fields : Fin 78→List Bool) : RowState:=
  ⟨fields,(compileExpr b e).final.nodes.length,
    out++(compileExpr b e).extension.suffix.flatMap PCPPRequestNodeSchema.native,
    RecoveryBoundedAddress.pushed (compileExpr b e).output.val stack,packet⟩

theorem expressionState_eq {n : ℕ} (b : BooleanDAGBuilder n) (e : BoolExpr n)
    (out stack packet : List Bool) (fields : Fin 78→List Bool) :
    expressionState b e out stack packet fields=
      ⟨fields,b.nodes.length+e.nodeCount,out++(exprNodes b.nodes.length e).flatMap PCPPRequestNodeSchema.native,
        RecoveryBoundedAddress.pushed (b.nodes.length+e.nodeCount-1) stack,packet⟩ := by
  simp only [expressionState,compileExpr_length,compileExpr_nodes,compileExpr_output]

end NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarCold
