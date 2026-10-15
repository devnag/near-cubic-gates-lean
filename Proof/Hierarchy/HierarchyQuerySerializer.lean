import Proof.PCP.PCPTraversalProducer
import Proof.Hierarchy.HierarchyStreamReady

/-! The one hierarchy/source/normalization prefix followed immediately by
the actual query-list encoding. Other source fields remain for clause/outer calls. -/
namespace NearCubicWires.RepairSource.ProjectionNormalization.HierarchyQuery
open LocalBitMultitape RepairOrdinary PCPSerializerMass
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section
variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)

def sourceSlot (k : ℕ) := HierarchyStreams.slots source k 29
def countSlot (k : ℕ) := HierarchyStreams.slots source k 25
theorem slots_ne (k : ℕ) : sourceSlot source k≠countSlot source k := by
  intro h
  have he := HierarchyStreams.slots_injective source k h
  contradiction
def fields (k CH Cpad : ℕ) (code x : List Bool) :=
  (normalizedRows (source.output (HierarchyStreams.request k CH Cpad code x))
    (HierarchyStreams.R source k CH Cpad code x) (HierarchyStreams.Q source k CH Cpad code x)).flatten.map Nat.bits
def machine (k CH Cpad : ℕ) (code : List Bool) :=
  PCPTraversalBank.producerMachine (sourceSlot source k) (countSlot source k)
    (HierarchyStreams.machine source k CH Cpad code)
def entry (k CH Cpad : ℕ) (code x bound : List Bool) :=
  let c := TapeEmbedding.config (fun _ : Fin 128 => 0) (fun _ : Fin 128 => [])
    (initialConfiguration (HierarchyStreams.machine source k CH Cpad code)
      (SourceHandoff.sourceTapes (frame x++frame bound)))
  (⟨(machine source k CH Cpad code).start,c.heads,c.tapes⟩ : Configuration (HierarchyStreams.tapes source k+128) _)
def budget (k CH Cpad : ℕ) (code x : List Bool) :=
  HierarchyStreams.budget source k CH Cpad code x+1+
    PCPTraversal.budget (mass (fields source k CH Cpad code x))

theorem query_run (k CH Cpad : ℕ) (code x bound : List Bool) (hpad : k+3 ≤ Cpad) :
    ∃ r p,runFrom (machine source k CH Cpad code) (budget source k CH Cpad code x)
      (entry source k CH Cpad code x bound)=some r ∧
      run (HierarchyStreams.machine source k CH Cpad code) (HierarchyStreams.budget source k CH Cpad code x)
        (SourceHandoff.sourceTapes (frame x++frame bound))=some p ∧
      HierarchyStreams.Fields source k CH Cpad code x bound p.final ∧
      r.final.tapes ((77 : Fin 128).natAdd (HierarchyStreams.tapes source k))=
        ZeroPadding.pad (PCPPairReusable.capacity (mass (fields source k CH Cpad code x)))
          (frame (PCPTraversal.code (fields source k CH Cpad code x)).bits) ∧
      r.final.tapes ((78 : Fin 128).natAdd (HierarchyStreams.tapes source k))=
        (PCPTraversal.code (fields source k CH Cpad code x)).bits ∧
      r.final.heads ((77 : Fin 128).natAdd (HierarchyStreams.tapes source k))=0 ∧
      r.final.heads ((78 : Fin 128).natAdd (HierarchyStreams.tapes source k))=0 ∧
      (∀ i : Fin (HierarchyStreams.tapes source k),r.final.tapes (i.castAdd 128)=p.final.tapes i) ∧
      (∀ i : Fin (HierarchyStreams.tapes source k),i≠sourceSlot source k →
        r.final.heads (i.castAdd 128)=p.final.heads i) ∧
      r.steps ≤ budget source k CH Cpad code x := by
  obtain ⟨p,hp,_ps,pf⟩ := HierarchyStreams.scalar_run source k CH Cpad code x bound hpad
  have hn : 1 ≤ (HierarchyStreams.request k CH Cpad code x).1 := by
    have h := (HierarchyPadding.linear_length k CH Cpad code x hpad).1
    change 1 ≤ (HierarchyPadding.rawInput k CH Cpad code x).length
    omega
  have hlen : (fields source k CH Cpad code x).length=
      HierarchyStreams.R source k CH Cpad code x*HierarchyStreams.Q source k CH Cpad code x := by
    rw [fields,List.length_map]
    exact Streams.query_count _ _ _
      (Dimensions.width_fits source (HierarchyStreams.request k CH Cpad code x) hn)
      (Dimensions.queries_fit source (HierarchyStreams.request k CH Cpad code x) hn)
  have hsource : p.final.tapes (sourceSlot source k)=[]++FieldList.stream (fields source k CH Cpad code x)++[] := by
    simpa only [sourceSlot,fields,QueryBytes.framedCodes,List.nil_append,List.append_nil] using pf.queryStream
  have hcount : p.final.tapes (countSlot source k)=VerifierDecoding.CompareMachine.word
      (fields source k CH Cpad code x).length := by
    rw [hlen]
    exact pf.queryCount
  obtain ⟨r,hr,r77,r78,rh77,rh78,rt,rh,rs⟩ := PCPTraversalBank.producer_run
    (sourceSlot source k) (countSlot source k) (slots_ne source k)
    (HierarchyStreams.machine source k CH Cpad code) _ _ p hp []
    (fields source k CH Cpad code x) [] pf.queryStreamHead pf.queryCountHead hsource hcount
  exact ⟨r,p,hr,hp,pf,r77,r78,rh77,rh78,rt,rh,rs⟩

end
end NearCubicWires.RepairSource.ProjectionNormalization.HierarchyQuery
