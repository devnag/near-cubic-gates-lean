import Proof.PCP.PCPPNativeCounterNodesDock

/-! Complete original native node emission after the actual metadata and
byte scans. No counter, capacity or literal-offset input is supplied. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeCounterNodes
open LocalBitMultitape SourceInterfaces RepairSource ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem nodes_run (p : RawProjectionPCP) (R Q : ℕ) (hR : p.width≤R) (hQ : p.queries≤Q)
    {n : ℕ} (x : BitInput n) (oracle : BooleanCircuit R) :
    ∃ result,runFrom machine (budget oracle p Q) (entry (PCPPNative.descriptor oracle) p R Q)=some result ∧
      result.steps≤budget oracle p Q ∧
      result.final.tapes 177=(PCPPNativeCompactNodes.nodes p R Q hR hQ x oracle).flatMap PCPPRequestNodeSchema.native ∧
      result.final.heads 177=((PCPPNativeCompactNodes.nodes p R Q hR hQ x oracle).flatMap PCPPRequestNodeSchema.native).length ∧
      result.final.heads 89=0 ∧ result.final.tapes 89=List.replicate (PCPPNativeCount.outputIndex Q oracle.size (Codec.clauses p).length) true ∧
      result.final.heads 91=0 ∧ result.final.tapes 91=List.replicate (PCPPNativeCount.nativeSize Q oracle.size (Codec.clauses p).length) true ∧
      result.final.heads 72=0 ∧ result.final.tapes 72=List.replicate R true := by
  obtain ⟨a,ha,as,af,a72h,a72t⟩ := PCPPNativeColdCounters.counters_run oracle p Q hR hQ
  let lifted := TapeEmbedding.receipt (fun _ : Fin 363=>0) (fun _=>[]) a
  have firstRun := TapeEmbedding.run_embed PCPPNativeColdCounters.machine (fun _ : Fin 363=>0) (fun _=>[]) _ _ a ha
  obtain ⟨b,hb,bt,bh,b14h,b14t,b16h,b16t,bs⟩ := PCPPNativeClauseOracle.original_run p R Q hR hQ x oracle []
    (PCPPNativeCompactNodes.clauses p R Q hR hQ x)
  simp only [List.append_nil,PCPPNativeCompactNodes.count,PCPPNativeCompactNodes.fields] at hb b14t b16t bs
  rw [node_input] at hb
  have hdata := dock_input oracle p Q a af
  obtain ⟨c,hc,_,cs,ch,ct,caway⟩ := RecoveryFocus.dock slots slots_injective PCPPNativeClauseOracle.machine _
    lifted.final.heads lifted.final.tapes
    (initialConfiguration PCPPNativeClauseOracle.machine
      (nodeInput (PCPPNative.descriptor oracle) (PCPPNativeMetadataMass.queryBytes p R Q) (DedupBytes.fields p)
        R Q oracle.size (Codec.clauses p).length (PCPPNativeMetadataMass.queryBytes p R Q).length (DedupBytes.fields p).length))
    (fun i=>(hdata i).1) (fun i=>(hdata i).2) b hb
  have joined := Composition.run_join first second _ _ _ lifted c firstRun hc
  refine ⟨Composition.joinedReceipt lifted c,joined,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · change a.steps+1+c.steps≤budget oracle p Q
    rw [cs]
    exact Nat.add_le_add (Nat.add_le_add_right as 1) bs
  · exact (ct 102).trans bt
  · exact (ch 102).trans bh
  · exact (ch 14).trans b14h
  · exact (ct 14).trans b14t
  · exact (ch 16).trans b16h
  · exact (ct 16).trans b16t
  · exact (caway 72 (by decide)).1.trans a72h
  · exact (caway 72 (by decide)).2.trans a72t

end NearCubicWires.RepairOrdinary.PCPPNativeCounterNodes
