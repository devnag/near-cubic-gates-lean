import Proof.CaseAnalysis.RecoverySelectorResetOriginal

/-! The reusable original selector executes in the retained bank beside the
next field index and saved first output. Both extra tapes are charged. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedSelectorPair
open LocalBitMultitape SourceInterfaces RepairRepresentation
open BoundedOracleStructuralCircuit FinitePredicateCircuit RecoveryBoundedNative
open RecoveryBoundedSelectorLoop RecoveryBoundedSelectorFinish
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def selector:=TapeEmbedding.machine 2 RecoveryBoundedSelectorReuse.machine

theorem selector_run {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (row : Fin (bound+1)) (start limit W D L : ℕ) (hblock : start+limit ≤ rowWidth n bound)
    (wires : List (LiveWire b)) (out tail : List Bool) (next : ℕ) (saved : List Bool)
    (hi : RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start+limit ≤ W)
    (hp : b.nodes.length+wires.length*(3*limit+2)+3*limit ≤ W)
    (hg : (compileFieldSelect b (fun row value=>unaryEqualsExpr row start limit value hblock) row wires).final.nodes.length ≤ W)
    (hc : wires.length ≤ W) (hD : 8388608*(W+1)^3 ≤ D) (hL : logCapacity W ≤ L) :
    let compiled:=compileFieldSelect b (fun row value=>unaryEqualsExpr row start limit value hblock) row wires
    let source:=sourceWord (wires.map (fun w=>w.output.val))++tail
    let result:=out++compiled.extension.suffix.flatMap PCPPRequestNodeSchema.native
    ∃ r,runFrom selector (RecoveryBoundedSelectorReuse.resetBudget wires.length W)
      ⟨selector.start,heads out,data (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start)
        b.nodes.length (capacity W) D 0 limit wires.length L out source next saved⟩=some r ∧
      r.steps ≤ RecoveryBoundedSelectorReuse.resetBudget wires.length W ∧ r.final.heads=heads result ∧
      r.final.tapes=data (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start)
        compiled.output.val (capacity W) D wires.length limit wires.length L result source next saved := by
  let source:=sourceWord (wires.map (fun w=>w.output.val))++tail
  let extra : Fin 2→List Bool:=![List.replicate next true,saved]
  obtain ⟨p,hpRun,ps,ph,pt⟩:=RecoveryBoundedSelectorReuse.reset_original_run
    b row start limit W D L hblock wires out tail hi hp hg hc hD hL
  let r:=TapeEmbedding.receipt (fun _ : Fin 2=>0) extra p
  have hr:=TapeEmbedding.run_embed RecoveryBoundedSelectorReuse.machine (fun _ : Fin 2=>0) extra _ _ p hpRun
  have he : TapeEmbedding.config (fun _ : Fin 2=>0) extra
      (RecoveryBoundedSelectorReuse.entry (n:=n) row start limit W D L b.nodes.length wires.length out source)=
      (⟨selector.start,heads out,data (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start)
        b.nodes.length (capacity W) D 0 limit wires.length L out source next saved⟩ : Configuration 46 _) := by
    apply configuration_ext
    · rfl
    · change Fin.addCases (m:=44) (n:=2) (motive:=fun _=>ℕ)
        (RecoveryBoundedSelectorReuse.entry (n:=n) row start limit W D L b.nodes.length wires.length out source).heads
        (fun _=>0)=heads out
      rw [RecoveryBoundedSelectorReuse.entry_heads]
      rfl
    · change Fin.addCases (m:=44) (n:=2) (motive:=fun _=>List Bool)
        (RecoveryBoundedSelectorReuse.entry (n:=n) row start limit W D L b.nodes.length wires.length out source).tapes
        extra=data (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start)
          b.nodes.length (capacity W) D 0 limit wires.length L out source next saved
      rw [RecoveryBoundedSelectorReuse.entry_tapes]
      exact data_embedding _ _ _ _ _ _ _ _ _ _ _ _
  rw [he] at hr
  refine ⟨r,hr,ps,?_,?_⟩
  · change Fin.addCases (m:=44) (n:=2) (motive:=fun _=>ℕ) p.final.heads (fun _=>0)=_
    rw [ph]
    rfl
  · change Fin.addCases (m:=44) (n:=2) (motive:=fun _=>List Bool) p.final.tapes extra=_
    rw [pt]
    exact data_embedding _ _ _ _ _ _ _ _ _ _ _ _

end NearCubicWires.RepairOrdinary.RecoveryBoundedSelectorPair
