import Proof.CaseAnalysis.RecoverySelectorCanonical

/-! The reusable selector state records the original forward graph bytes and
the consumed prefix of its actual reference stream. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedSelectorLoop
open LocalBitMultitape SourceInterfaces RepairRepresentation Composition
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
    (hblock : start+limit≤rowWidth n bound) (ref : ℕ) (a : State) : State :=
  let acc:=a.position+prefixCount (unaryItems row start limit a.value hblock)+limit
  ⟨acc+2,a.value+1,
    a.out++(exprNodes a.position (unaryEqualsExpr row start limit a.value hblock)++
      [BooleanNode.and acc ref]).flatMap PCPPRequestNodeSchema.native,
    a.skipped++frame (List.replicate ref true),
    RecoveryBoundedSelectorReference.pushed acc a.stack⟩

def State.iterate {n bound : ℕ} (row : Fin (bound+1)) (start limit : ℕ)
    (hblock : start+limit≤rowWidth n bound) : List ℕ→State→State
  | [],a=>a
  | ref::rest,a=>State.iterate row start limit hblock rest (a.next row start limit hblock ref)

noncomputable def State.entry {n bound : ℕ} (row : Fin (bound+1))
    (start limit W D : ℕ) (a : State) (source : List Bool) :=
  stateConfig (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start)
    a.position (capacity W) D a.value limit a.skipped.length a.out source a.stack

def sourceWord (refs : List ℕ) := refs.flatMap fun ref=>frame (List.replicate ref true)

theorem raw_lift {n : ℕ} {b c : BooleanDAGBuilder n} (ex : BooleanDAGExtension b c)
    (wires : List (LiveWire b)) :
    (liftLiveWires ex wires).map (fun w=>w.output.val)=wires.map (fun w=>w.output.val) := by
  simp only [liftLiveWires,List.map_map]
  rfl

theorem next_position {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (row : Fin (bound+1)) (start limit : ℕ) (a : State) (wire : LiveWire b)
    (hblock : start+limit≤rowWidth n bound) (hp : a.position=b.nodes.length) :
    (a.next row start limit hblock wire.output.val).position=
      (head b (unaryEqualsExpr row start limit a.value hblock) wire).final.nodes.length := by
  rw [head_length]
  simp only [State.next,hp,RecoveryBoundedSelectorJoin.counter]

theorem next_bounds {n bound : ℕ} (row : Fin (bound+1)) (start limit : ℕ)
    (hblock : start+limit≤rowWidth n bound) (ref : ℕ) (a : State) :
    a.position≤(a.next row start limit hblock ref).position ∧
    (a.next row start limit hblock ref).position≤a.position+3*limit+2 := by
  have h:=prefixCount_bound (unaryItems row start limit a.value hblock)
  have hl : (unaryItems row start limit a.value hblock).length=limit := by simp [unaryItems]
  rw [hl] at h
  dsimp only [State.next]
  omega

theorem state_run {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (row : Fin (bound+1)) (start limit W D : ℕ) (a : State) (tail : List Bool)
    (wire : LiveWire b) (hblock : start+limit≤rowWidth n bound)
    (hb : a.position=b.nodes.length)
    (hi : RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start+limit≤W)
    (hp : a.position+3*limit≤W) (hv : a.value≤W) (hD : 8388608*(W+1)^3≤D) :
    ∃ r,runFrom machine (stepBudget W)
      (a.entry (n:=n) row start limit W D (a.skipped++frame (List.replicate wire.output.val true)++tail))=some r ∧
      r.steps ≤ stepBudget W ∧
      r.final.heads=((a.next row start limit hblock wire.output.val).entry (n:=n) row start limit W D
        (a.skipped++frame (List.replicate wire.output.val true)++tail)).heads ∧
      r.final.tapes=((a.next row start limit hblock wire.output.val).entry (n:=n) row start limit W D
        (a.skipped++frame (List.replicate wire.output.val true)++tail)).tapes := by
  rcases a with ⟨base,value,out,skipped,stack⟩
  dsimp only at hb hp hv
  subst base
  obtain ⟨r,hr,rs,rh,rt⟩:=canonical_run b row start limit value W D out skipped tail stack wire hblock hi hp hv hD
  have hout : nextOut b row start limit value wire.output.val out hblock=
      out++(exprNodes b.nodes.length (unaryEqualsExpr row start limit value hblock)++
        [BooleanNode.and (RecoveryBoundedSelectorJoin.counter b row start limit value hblock) wire.output.val]).flatMap
        PCPPRequestNodeSchema.native := by
    rw [nextOut_eq,head_suffix,compileExpr_nodes,condition_output]
  refine ⟨r,hr,rs,?_,?_⟩
  · rw [rh,hout]
    change stateHeads _ _ (skipped.length+2*wire.output.val+1)=stateHeads _ _
      (skipped++frame (List.replicate wire.output.val true)).length
    rw [List.length_append,frame_length,List.length_replicate]
    congr 1
  · rw [rt,hout]
    rfl

end NearCubicWires.RepairOrdinary.RecoveryBoundedSelectorLoop
