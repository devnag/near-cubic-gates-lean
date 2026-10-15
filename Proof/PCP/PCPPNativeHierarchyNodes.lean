import Proof.PCP.PCPPNativeHierarchyNodesCircuit

/-! The original hierarchy/oracle input emits the exact native substituted
DAG, together with the actual arity, node count and output-index scalars. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeHierarchyNodes
open LocalBitMultitape SourceInterfaces RepairSource RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
theorem raw_run (k CH Cpad : ℕ) (code : List Bool) {n : ℕ} (x : BitInput n)
    (bound : List Bool) (hpad : k+3≤Cpad) (oracle : BooleanCircuit (width source k CH Cpad code x)) :
    let c:=circuit source k CH Cpad code x hpad oracle
    ∃ result,run (machine source k CH Cpad code) (budget source k CH Cpad code x bound oracle)
      (input source k (frame (List.ofFn x)++frame bound) (PCPPNative.descriptor oracle))=some result ∧
      result.steps≤budget source k CH Cpad code x bound oracle ∧
      result.final.tapes (slots source k 177)=c.nodes.flatMap PCPPRequestNodeSchema.native ∧
      result.final.heads (slots source k 177)=(c.nodes.flatMap PCPPRequestNodeSchema.native).length ∧
      result.final.heads (slots source k 89)=0 ∧ result.final.tapes (slots source k 89)=List.replicate c.output.val true ∧
      result.final.heads (slots source k 91)=0 ∧ result.final.tapes (slots source k 91)=List.replicate c.size true ∧
      result.final.heads (slots source k 72)=0 ∧ result.final.tapes (slots source k 72)=List.replicate (width source k CH Cpad code x) true := by
  intro actual
  obtain ⟨a,ha,as,af,aret⟩ := PCPPNativeHierarchy.raw_run source k CH Cpad code (List.ofFn x) bound (PCPPNative.descriptor oracle) hpad
  let lifted := TapeEmbedding.receipt (fun _ : Fin 438=>0) (fun _=>[]) a
  have firstRun := TapeEmbedding.run_embed (PCPPNativeHierarchy.machine source k CH Cpad code)
    (fun _ : Fin 438=>0) (fun _=>[]) _ _ a ha
  obtain ⟨b,hb,bs,bt,bh,b89h,b89t,b91h,b91t,b72h,b72t⟩ := PCPPNativeCounterNodes.nodes_run
    (pcp source k CH Cpad code x) (width source k CH Cpad code x) (queries source k CH Cpad code x)
    (width_fits source k CH Cpad code x hpad) (queries_fit source k CH Cpad code x hpad) x oracle
  have hdata := dock_input source k CH Cpad code (List.ofFn x) bound oracle a af (aret 2 (by decide))
  obtain ⟨lastReceipt,hl,_,ls,lh,lt,_⟩ := RecoveryFocus.dock (slots source k) (slots_injective source k)
    PCPPNativeCounterNodes.machine _ lifted.final.heads lifted.final.tapes
    (PCPPNativeCounterNodes.entry (PCPPNative.descriptor oracle) (pcp source k CH Cpad code x)
      (width source k CH Cpad code x) (queries source k CH Cpad code x))
    (fun i=>(hdata i).1) (fun i=>(hdata i).2) b hb
  have joined := Composition.run_join (first source k CH Cpad code) (second source k) _ _ _ lifted lastReceipt firstRun hl
  have hi : Composition.leftConfig _ (TapeEmbedding.config (fun _ : Fin 438=>0) (fun _=>[])
      (initialConfiguration (PCPPNativeHierarchy.machine source k CH Cpad code)
        (PCPPNativeHierarchy.input source k (frame (List.ofFn x)++frame bound) (PCPPNative.descriptor oracle))))=
      initialConfiguration (machine source k CH Cpad code)
        (input source k (frame (List.ofFn x)++frame bound) (PCPPNative.descriptor oracle)) := by
    apply configuration_ext
    · rfl
    · funext i
      refine Fin.addCases (m:=base source k) (n:=438) (fun _=>?_) (fun _=>?_) i <;>
        simp [base,Composition.leftConfig,TapeEmbedding.config,initialConfiguration]
    · rfl
  rw [hi] at joined
  have cn : actual.nodes=PCPPNativeCompactNodes.nodes (pcp source k CH Cpad code x)
      (width source k CH Cpad code x) (queries source k CH Cpad code x)
      (width_fits source k CH Cpad code x hpad) (queries_fit source k CH Cpad code x hpad) x oracle :=
    PCPPNativeCompactNodes.circuit_nodes _ _ _ _ _ _ _
  have csize : actual.size=PCPPNativeCount.nativeSize (queries source k CH Cpad code x) oracle.size
      (Codec.clauses (pcp source k CH Cpad code x)).length := PCPPNativeCompactNodes.circuit_size _ _ _ _ _ _ _
  have cout : actual.output.val=PCPPNativeCount.outputIndex (queries source k CH Cpad code x) oracle.size
      (Codec.clauses (pcp source k CH Cpad code x)).length := PCPPNativeCompactNodes.circuit_output _ _ _ _ _ _ _
  refine ⟨Composition.joinedReceipt lifted lastReceipt,joined,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · change a.steps+1+lastReceipt.steps≤budget source k CH Cpad code x bound oracle
    rw [ls]
    exact Nat.add_le_add (Nat.add_le_add_right as 1) bs
  · rw [cn]; exact (lt 177).trans bt
  · rw [cn]; exact (lh 177).trans bh
  · exact (lh 89).trans b89h
  · rw [cout]; exact (lt 89).trans b89t
  · exact (lh 91).trans b91h
  · rw [csize]; exact (lt 91).trans b91t
  · exact (lh 72).trans b72h
  · exact (lt 72).trans b72t

end
end NearCubicWires.RepairOrdinary.PCPPNativeHierarchyNodes
