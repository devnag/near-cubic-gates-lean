import Proof.CaseAnalysis.RecoveryUnaryState

/-! One fixed ordinary graph compiler emits exactly the original unary
row-guard suffix: original forward literals, true seed and reverse ANDs. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedNativeUnaryJoin
open LocalBitMultitape SourceInterfaces RepairRepresentation Composition RecoveryBoundedNative
open BoundedOracleStructuralCircuit FinitePredicateCircuit
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def budget (limit C : ℕ) :=
  (limit*(32*C+106)+limit+3)+1+(RecoveryBoundedNativeUnaryPhase.trueBits.length+1+(2*C+4))+1+
    (limit*(24*C+66)+limit+3)
noncomputable def entry {n bound : ℕ} (row : Fin (bound+1)) (start base C value limit : ℕ)
    (out stack : List Bool) :=
  restart (RecoveryBoundedNativeUnaryLoop.configuration 0 C value
    (RecoveryBoundedNativeUnaryLoop.initial (n:=n) row start base out stack) limit 1) machine.start

noncomputable def finalState {n bound : ℕ} (row : Fin (bound+1))
    (start base C value limit : ℕ) (out pre : List Bool)
    (hblock : start+limit ≤ rowWidth n bound) :=
  let a := (RecoveryBoundedNativeUnaryLoop.initial (n:=n) row start base out pre).iterate value limit
  foldFinal a.position C a.flag (a.out++RecoveryBoundedNativeUnaryPhase.trueBits) pre
    (literalReferences base (unaryItems row start limit value hblock))

theorem original_run {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (row : Fin (bound+1)) (start limit value W C : ℕ) (out pre : List Bool)
    (hblock : start+limit ≤ rowWidth n bound)
    (hi : RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start+limit ≤ W)
    (hp : b.nodes.length+3*limit ≤ W) (hC : 16384*(W+1)^2 ≤ C) :
    ∃ r, runFrom machine (budget limit C) (entry (n:=n) row start b.nodes.length C value limit out pre)=some r ∧
      r.steps ≤ budget limit C ∧
      r.final.tapes 20=out++((compileExpr b (unaryEqualsExpr row start limit value hblock)).extension.suffix).flatMap
        PCPPRequestNodeSchema.native ∧
      r.final.tapes 25=List.replicate
        (b.nodes.length+prefixCount (unaryItems row start limit value hblock)+limit) true ∧
      r.final.heads 31=pre.length ∧ r.final.heads 34=limit ∧ r.final.heads 35=1 ∧
      (∀ j : Fin 29,
        r.final.heads (j.castAdd 7)=PCPPNativeClauseBank.heads
          (out++((compileExpr b (unaryEqualsExpr row start limit value hblock)).extension.suffix).flatMap
            PCPPRequestNodeSchema.native) j ∧
        r.final.tapes (j.castAdd 7)=RecoveryBoundedNativeFold.oldData 0
          (b.nodes.length+prefixCount (unaryItems row start limit value hblock)+limit) C
          (out++((compileExpr b (unaryEqualsExpr row start limit value hblock)).extension.suffix).flatMap
            PCPPRequestNodeSchema.native) j) ∧
      (∀ j : Fin 35,
        r.final.heads (foldSlots j)=
          (finalState row start b.nodes.length C value limit out pre hblock).heads j ∧
        r.final.tapes (foldSlots j)=
          (finalState row start b.nodes.length C value limit out pre hblock).tapes j) ∧
      r.final.tapes 34=List.replicate value true := by
  let initial:=RecoveryBoundedNativeUnaryLoop.initial (n:=n) row start b.nodes.length out pre
  let a:=initial.iterate value limit
  let items:=unaryItems row start limit value hblock
  let refs:=literalReferences b.nodes.length items
  have hlen : items.length=limit := by simp [items,unaryItems]
  have hrefs : refs.length=limit := by simp only [refs,references_length,hlen]
  obtain ⟨r0,hr0,rf0,rs0⟩:=RecoveryBoundedNativeUnaryLoop.loop_run limit W C value limit initial
    (by simp [initial,RecoveryBoundedNativeUnaryLoop.initial]) hi
    (by change b.nodes.length+2*limit ≤ W; omega) hC
  have hs:=RecoveryBoundedNativeUnaryLoop.iterate_schedule limit value initial
    (RecoveryBoundedNativeUnaryLoop.index_bound row start limit hblock)
  have select : RecoveryBoundedNativeUnaryLoop.items initial.index initial.offset value limit
      (RecoveryBoundedNativeUnaryLoop.index_bound row start limit hblock)=items :=
    RecoveryBoundedNativeUnaryLoop.items_unary row start limit value hblock
  dsimp only at hs
  rw [select] at hs
  have haPos : a.position=b.nodes.length+prefixCount items := hs.1
  have haOut : a.out=out++(literalPrefix b.nodes.length items).flatMap PCPPRequestNodeSchema.native := hs.2.1
  have haStack : a.stack=pre++RecoveryBoundedNativeUnaryLoop.stackWords refs := hs.2.2
  have indices:=RecoveryBoundedNativeUnaryLoop.iterate_indices limit value initial
  have haIndex : a.index=RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start+limit := indices.1
  have haOffset : a.offset=limit := by
    simpa only [a,initial,RecoveryBoundedNativeUnaryLoop.initial,Nat.zero_add] using indices.2
  have small : W ≤ C := PCPPNativeClauseCapacity.width_le_capacity W C hC
  obtain ⟨r1,hr1,rs1,rh1,rt1⟩:=phase_run C value limit a (by omega)
  have hr1' : runFrom second (RecoveryBoundedNativeUnaryPhase.trueBits.length+1+(2*C+4))
      (restart r0.final second.start)=some r1 := by
    rw [rf0]
    exact hr1
  have join01:=Composition.run_join first second _ _ _ r0 r1 hr0 hr1'
  have countBound:=prefixCount_bound items
  have capRef : ∀ v∈refs,v ≤ W := by
    intro v hv
    have h:=references_bound b.nodes.length items v hv
    omega
  obtain ⟨r2,hr2,rs2,ro2,ra2,rst2,rv2,rg2⟩:=reverse_run (n:=descriptionWidth n bound)
    a.position W C value a.offset a.flag (a.out++RecoveryBoundedNativeUnaryPhase.trueBits) pre refs
    capRef (by omega) hC
  have bank:=reverse_bank (n:=descriptionWidth n bound)
    a.position W C value a.offset a.flag (a.out++RecoveryBoundedNativeUnaryPhase.trueBits) pre refs
    capRef (by omega) hC r2 hr2
  have state:=reverse_state
    a.position W C value a.offset a.flag (a.out++RecoveryBoundedNativeUnaryPhase.trueBits) pre refs
    capRef (by omega) hC r2 hr2
  have sameOut : a.out++RecoveryBoundedNativeUnaryPhase.trueBits++
      (foldNodes (n:=descriptionWidth n bound) true a.position refs.reverse).flatMap PCPPRequestNodeSchema.native=
      out++((compileExpr b (unaryEqualsExpr row start limit value hblock)).extension.suffix).flatMap
        PCPPRequestNodeSchema.native := by
    rw [haOut,haPos,unary_schedule,allSuffix_reverse,List.flatMap_append]
    simp only [List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
      List.append_nil,List.append_assoc]
    rfl
  rw [sameOut,haPos,hrefs] at bank
  rw [hrefs] at hr2 rs2 ra2
  have hr2' : runFrom third (limit*(24*C+66)+limit+3)
      (restart (joinedReceipt r0 r1).final third.start)=some r2 := by
    change runFrom third _ ⟨third.start,r1.final.heads,r1.final.tapes⟩=some r2
    rw [rh1,rt1,haStack]
    exact hr2
  have full:=Composition.run_join (Composition.machine first second) third _ _ _ (joinedReceipt r0 r1) r2 join01 hr2'
  refine ⟨joinedReceipt (joinedReceipt r0 r1) r2,full,?_,?_,?_,rst2,?_,rg2,bank,state⟩
  · change r0.steps+1+r1.steps+1+r2.steps ≤ budget limit C
    unfold budget
    omega
  · change r2.final.tapes 20=_
    exact ro2.trans sameOut
  · change r2.final.tapes 25=_
    rw [ra2,haPos]
  · exact rv2.trans haOffset

end NearCubicWires.RepairOrdinary.RecoveryBoundedNativeUnaryJoin
