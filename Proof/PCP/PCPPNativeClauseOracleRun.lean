import Proof.PCP.PCPPNativeClauseOraclePrefix

/-! Whole original substituted-node emission from the original oracle,
original query/clause streams and their measured counts. Every native
offset, capacity and loop driver is produced by the physical program. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeClauseOracle
open LocalBitMultitape SourceInterfaces RepairSource ProjectionNormalization PCPPNativeClauseLoop
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def budget {R : ℕ} (oracle : BooleanCircuit R) (Q M Lq Lc : ℕ) := prefixBudget oracle Q M Lq Lc+1+
  PCPPNativeClauseRawRun.budget (PCPPNativeCapacityReady.C (PCPPNativeResources.W R Q oracle.size M Lq Lc)) M

theorem original_run (p : RawProjectionPCP) (R Q : ℕ)
    (hR : p.width≤R) (hQ : p.queries≤Q) {n : ℕ} (x : BitInput n)
    (oracle : BooleanCircuit R) (suffix : List Bool) (clauses : List (Fin 3→Literal Q)) :
    let Lq := (QueryBytes.framedCodes (normalizedRows p R Q).flatten).length
    let Lc := (sourceFields clauses).length
    let nodes := PCPPNative.substitutedNodes oracle ((p.normalized R Q hR hQ).queryAddressBits x) clauses
    ∃ result,run machine (budget oracle Q clauses.length Lq Lc)
      (input (PCPPNativeQueryConjunction.input (PCPPNative.descriptor oracle)
        (QueryBytes.framedCodes (normalizedRows p R Q).flatten++suffix) R Q oracle.size clauses.length Lq Lc)
        (sourceFields clauses))=some result ∧
      result.final.tapes 102=nodes.flatMap PCPPRequestNodeSchema.native ∧
      result.final.heads 102=(nodes.flatMap PCPPRequestNodeSchema.native).length ∧
      result.final.heads 14=0 ∧ result.final.tapes 14=List.replicate (PCPPNativeCount.outputIndex Q oracle.size clauses.length) true ∧
      result.final.heads 16=0 ∧ result.final.tapes 16=List.replicate (PCPPNativeCount.nativeSize Q oracle.size clauses.length) true ∧
      result.steps≤budget oracle Q clauses.length Lq Lc := by
  intro Lq Lc nodes
  let W:=PCPPNativeResources.W R Q oracle.size clauses.length Lq Lc
  let out:=PCPPNativeQueryConjunction.queryBytes p R Q hR hQ x oracle++PCPPNativeConjunctionStart.trueBits
  obtain ⟨a,ar,as,af,a14h,a14,a16h,a16⟩:=prefix_run p R Q hR hQ x oracle suffix (sourceFields clauses) clauses.length
  obtain ⟨_,_,_,hsize,hstride,_,hbytes⟩:=PCPPNativeResources.bounds R Q oracle.size clauses.length Lq Lc
  have hsize' : Q*(2*oracle.size+1)+3*clauses.length+1≤W := by
    simpa only [PCPPNativeCount.nativeSize,PCPPNativeCount.outputIndex,PCPPNativeCount.queryEnd,
      PCPPNativeCount.stride,Nat.mul_comm clauses.length 3] using hsize
  obtain ⟨b,br,bt,bh,_,bs⟩:=PCPPNativeClauseRawRun.original_run R W (PCPPNativeCapacityReady.C W)
    oracle clauses [] [] out hstride hsize' hbytes (by rfl)
  simp only [List.nil_append,List.append_nil,List.length_nil] at br
  obtain ⟨c,cr,_,cs,ch,ct,other⟩:=RecoveryFocus.dock clauseSlots clause_injective PCPPNativeClauseRawRun.machine _
    a.final.heads a.final.tapes _ (fun i=>(af i).1) (fun i=>(af i).2) b br
  have joined:=Composition.run_join beforeClauses last _ _ _ a c ar cr
  have bytes : out++(PCPPNative.clauseStreamNodes (r:=R) (Q*(2*oracle.size+1)+1)
      (Q*(2*oracle.size+1)) (PCPPNative.literalAddress oracle) clauses).flatMap PCPPRequestNodeSchema.native=
      nodes.flatMap PCPPRequestNodeSchema.native := by
    simp only [nodes,PCPPNative.substitutedNodes,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil]
    rfl
  rw [bytes] at bt bh
  refine ⟨Composition.joinedReceipt a c,joined,?_,?_,?_,?_,?_,?_,?_⟩
  · change c.final.tapes 102=_
    exact (ct 47).trans bt
  · change c.final.heads 102=_
    exact (ch 47).trans bh
  · change c.final.heads 14=0
    exact (other 14 clause_away14).1.trans a14h
  · change c.final.tapes 14=_
    exact (other 14 clause_away14).2.trans a14
  · change c.final.heads 16=0
    exact (other 16 clause_away16).1.trans a16h
  · change c.final.tapes 16=_
    exact (other 16 clause_away16).2.trans a16
  · change a.steps+1+c.steps≤budget oracle Q clauses.length Lq Lc
    rw [cs]
    exact Nat.add_le_add (Nat.add_le_add_right as 1) bs

end NearCubicWires.RepairOrdinary.PCPPNativeClauseOracle
