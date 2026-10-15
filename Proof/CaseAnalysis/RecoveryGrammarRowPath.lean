import Proof.CaseAnalysis.RecoveryGrammarRepeatPadding

/-! The two finite original row sequences supply every actual driver step.
Prefix bounds come from the final original graph; no count prepass is used. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarCold
open LocalBitMultitape SourceInterfaces FinitePredicateCircuit BoundedOracleStructuralCircuit
open RecoveryBoundedNative RecoveryBoundedAddress
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem path_bounds {n W G : ℕ} (b : BooleanDAGBuilder n) (xs : List (BoolExpr n))
    (refs : List ℕ) (valid : ValidReferences b refs W) (hg : (children b xs).nodes.length≤G)
    (gw : G≤W) (i : ℕ) (hi : i<xs.length) :
    ValidReferences (children b (xs.take i)) (refs++references b.nodes.length (xs.take i)) W ∧
      (compileExpr (children b (xs.take i)) xs[i]).final.nodes.length≤G := by
  refine ⟨valid.children _ ((children_take_le b xs i).trans hg) gw,?_⟩
  rw [←children_take_step b xs i hi]
  exact (children_take_le b xs (i+1)).trans hg

theorem node_path_run {q bound G W C D L S B P : ℕ}
    (room : Room W C D L S B P) (alloc : Allocation q bound G W)
    (b : BooleanDAGBuilder (descriptionWidth q bound)) (count : Fin bound)
    (graphPre stackPre source : List Bool) (refs : List ℕ) (extra : Fin 12→List Bool)
    (valid : ValidReferences b refs W) (hg : (children b (countNodeRows count)).nodes.length≤G)
    (graphSupport : ∀ d : BooleanDAGBuilder (descriptionWidth q bound),d.nodes.length≤G → (graphWord graphPre d).length≤S)
    (stackSupport : stackPre.length+W*(2*W+1)≤S) (hs : source.length≤B)
    (width : extra 0=RecoveryBoundedGrammarScalarAdd.unary B (rowWidth q bound))
    (i : ℕ) (hi : i<count.val+1) :
    ∃ r,runFrom nodeBody (rowBodyBudget (nodeBudget B) B)
      (pathConfig nodeBody b (countNodeRows count) (tag 0) 0 C B P graphPre stackPre source refs extra i)=some r ∧
      r.steps≤rowBodyBudget (nodeBudget B) B ∧
      r.final.heads=(pathConfig nodeBody b (countNodeRows count) (tag 0) 0 C B P graphPre stackPre source refs extra (i+1)).heads ∧
      r.final.tapes=(pathConfig nodeBody b (countNodeRows count) (tag 0) 0 C B P graphPre stackPre source refs extra (i+1)).tapes := by
  have hrow : i<bound+1:=by have hc:=count.isLt;omega
  have hil : i<(countNodeRows (n:=q) count).length:=by simpa only [countNodeRows,List.length_ofFn] using hi
  have he : (countNodeRows (n:=q) count)[i]=nodeRowExpr (n:=q) ⟨i,hrow⟩:=by
    simp only [countNodeRows,List.getElem_ofFn]
  obtain ⟨vp,hp⟩:=path_bounds b (countNodeRows count) refs valid hg alloc.graph i hil
  rw [he] at hp
  have core:=node_run room alloc (children b ((countNodeRows count).take i)) ⟨i,hrow⟩ foldRows
    graphPre stackPre (ZeroPadding.pad B (selectedWord (tag 0) q bound i C)) source
    (refs++references b.nodes.length ((countNodeRows count).take i)) extra vp hp graphSupport stackSupport hs
    (room.pad_packet_length (alloc.scalars ⟨i,hrow⟩) (tag 0))
  apply path_step_run room alloc (nodeRow foldRows) (nodeBudget B) b (countNodeRows count) (tag 0) 0 i hil
    (by omega) graphPre stackPre source refs extra width
  rw [he]
  simpa only [pathState,Nat.zero_add] using core

theorem padding_path_run {q bound G W C D L S B P : ℕ}
    (room : Room W C D L S B P) (alloc : Allocation q bound G W)
    (b : BooleanDAGBuilder (descriptionWidth q bound)) (count : Fin bound)
    (graphPre stackPre source : List Bool) (refs : List ℕ) (extra : Fin 12→List Bool)
    (valid : ValidReferences b refs W) (hg : (children b (countPaddingRows count)).nodes.length≤G)
    (graphSupport : ∀ d : BooleanDAGBuilder (descriptionWidth q bound),d.nodes.length≤G → (graphWord graphPre d).length≤S)
    (stackSupport : stackPre.length+W*(2*W+1)≤S) (hs : source.length≤B)
    (width : extra 0=RecoveryBoundedGrammarScalarAdd.unary B (rowWidth q bound))
    (i : ℕ) (hi : i<bound-(count.val+1)) :
    ∃ r,runFrom paddingBody (rowBodyBudget (paddingBudget B) B)
      (pathConfig paddingBody b (countPaddingRows count) (tag 6) (count.val+2) C B P graphPre stackPre source refs extra i)=some r ∧
      r.steps≤rowBodyBudget (paddingBudget B) B ∧
      r.final.heads=(pathConfig paddingBody b (countPaddingRows count) (tag 6) (count.val+2) C B P graphPre stackPre source refs extra (i+1)).heads ∧
      r.final.tapes=(pathConfig paddingBody b (countPaddingRows count) (tag 6) (count.val+2) C B P graphPre stackPre source refs extra (i+1)).tapes := by
  have hrow : count.val+2+i<bound+1:=by have hc:=count.isLt;omega
  have hil : i<(countPaddingRows (n:=q) count).length:=by simpa only [countPaddingRows,List.length_ofFn] using hi
  have he : (countPaddingRows (n:=q) count)[i]=paddingRowExpr (n:=q) ⟨count.val+2+i,hrow⟩:=by
    simp only [countPaddingRows,List.getElem_ofFn]
  obtain ⟨vp,hp⟩:=path_bounds b (countPaddingRows count) refs valid hg alloc.graph i hil
  rw [he] at hp
  have core:=padding_run room alloc (children b ((countPaddingRows count).take i)) ⟨count.val+2+i,hrow⟩ foldRows
    graphPre stackPre (ZeroPadding.pad B (selectedWord (tag 6) q bound (count.val+2+i) C)) source
    (refs++references b.nodes.length ((countPaddingRows count).take i)) extra vp hp graphSupport stackSupport hs
    (room.pad_packet_length (alloc.scalars ⟨count.val+2+i,hrow⟩) (tag 6))
  apply path_step_run room alloc (padding foldRows) (paddingBudget B) b (countPaddingRows count) (tag 6) (count.val+2) i hil
    hrow graphPre stackPre source refs extra width
  rw [he]
  exact core

end NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarCold
