import Proof.PCP.PCPTraversalProducer
import Proof.PCP.PCPClauseListReset

/-! Whole two-level clause serialization: original M/native triples,
global counted serializer, paid stream reset, then the clause-code list. -/
namespace NearCubicWires.RepairOrdinary.PCPClauseList
open LocalBitMultitape PCPSerializerMass
open RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def fields (groups : List (List (List Bool))) : List (List Bool) :=
  groups.map (fun fs => (PCPTraversal.code fs).bits)
noncomputable def machine := PCPTraversalBank.producerMachine (177 : Fin 181) 0 resetMachine
noncomputable def entry (M : ℕ) (source : List Bool) :=
  let c := TapeEmbedding.config (fun _ : Fin 128 => 0) (fun _ : Fin 128 => [])
    (Rewind.recording (PCPTripleGlobal.entry M source 0) 0)
  (⟨machine.start,c.heads,c.tapes⟩ : Configuration 309 _)
def budget (groups : List (List (List Bool))) :=
  2*PCPTripleGlobal.budget (PCPTripleLoop.stream groups).length groups.length+3+
    PCPTraversal.budget (mass (fields groups))

theorem clause_list_run (groups : List (List (List Bool)))
    (hthree : ∀ fs∈groups,fs.length=3) :
    ∃ r,runFrom machine (budget groups) (entry groups.length (PCPTripleLoop.stream groups))=some r ∧
      r.final.tapes 258=ZeroPadding.pad (PCPPairReusable.capacity (mass (fields groups)))
        (frame (PCPTraversal.code (fields groups)).bits) ∧
      r.final.tapes 259=(PCPTraversal.code (fields groups)).bits ∧
      r.final.heads 258=0 ∧ r.final.heads 259=0 ∧
      r.final.tapes 0=RepairSource.VerifierDecoding.CompareMachine.word groups.length ∧
      r.final.heads 0=1 ∧ r.steps ≤ budget groups := by
  obtain ⟨p,hp,p0,ph0,po,pho,_ps⟩ := global_reset_run [] groups [] hthree
  simp only [List.nil_append,List.append_nil,List.length_nil] at hp
  have ht : p.final.tapes 177=[]++FieldList.stream (fields groups)++[] := by
    simpa only [PCPTripleLoop.encoded,fields,List.nil_append,List.append_nil] using po
  have hc : p.final.tapes 0=RepairSource.VerifierDecoding.CompareMachine.word (fields groups).length := by
    simpa only [fields,List.length_map] using p0
  obtain ⟨r,hr,r77,r78,rh77,rh78,rt,rh,rs⟩ := PCPTraversalBank.producer_run
    (177 : Fin 181) 0 (by decide) resetMachine _ _ p hp [] (fields groups) [] pho ph0 ht hc
  have he : (2*PCPTripleGlobal.budget (PCPTripleLoop.stream groups).length groups.length+2)+1+
      PCPTraversal.budget (mass (fields groups))=budget groups := by unfold budget; omega
  rw [he] at hr rs
  exact ⟨r,hr,r77,r78,rh77,rh78,(rt 0).trans p0,(rh 0 (by decide)).trans ph0,rs⟩

theorem fields_mass (groups : List (List (List Bool)))
    (hthree : ∀ fs∈groups,fs.length=3) :
    mass (fields groups) ≤ 512*(PCPTripleLoop.stream groups).length := by
  have h := PCPTripleGlobal.encoded_linear groups hthree
  change (FieldList.stream (fields groups)).length ≤ _ at h
  rw [PCPTraversal.stream_mass] at h
  exact h

end NearCubicWires.RepairOrdinary.PCPClauseList
