import Proof.CaseAnalysis.RowsRawAtomProducer
import Proof.CaseAnalysis.RowsRawAtomCache
import Proof.CaseAnalysis.WitnessFamilyRound

/-! The original family's actual per-sum count words drive the existing
absolute-index producer. These indices address original coefficient/native/
support terms, before decomposition; no decomposition source theorem is used. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsOriginalTerms
open LocalBitMultitape ExtDecompositionBatch CloseoutWitness
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def counts (fields : List (List Bool)) := fields.map SumFields.count
def cache (fields : List (List Bool)) := CloseoutRowsRawAtomCache.cache 0 (counts fields)
def word (fields : List (List Bool)) := fields.flatMap FamilyRound.countWord

theorem count_bytes (fields : List (List Bool)) :
    CloseoutRowsRawAtomBatch.countWord (counts fields)=word fields := by
  simp only [CloseoutRowsRawAtomBatch.countWord,counts,List.flatMap_map,word]
  rfl

theorem cache_bytes (fields : List (List Bool)) :
    CloseoutRowsRawAtomSeek.cacheWord (cache fields)=CloseoutRowsRawAtomBatch.atoms 0 (counts fields) :=
  CloseoutRowsRawAtomCache.cache_word 0 (counts fields)

theorem original_indices (fields : List (List Bool)) (i : ℕ) (hi : i < fields.length) :
    (cache fields)[i]'(by simpa [cache,CloseoutRowsRawAtomCache.cache_length,counts] using hi)=
      (List.range' ((fields.take i).map SumFields.count).sum (SumFields.count fields[i])).map (fun j=>[j]) := by
  have h:=CloseoutRowsRawAtomCache.cache_getElem 0 (counts fields) i (by simpa [counts] using hi)
  simpa only [cache,counts,List.length_map,List.map_take,List.getElem_map,Nat.zero_add,
    CloseoutRowsRawAtomLoop.indices] using h

noncomputable def machine := CloseoutRowsRawAtomProducer.machine

theorem producer_run (C B : ℕ) (fields : List (List Bool)) (out : List Bool)
    (hB : (counts fields).sum ≤ B) (hc : 64*(B+2)^2 ≤ C) :
    ∃ r,runFrom machine (CloseoutRowsRawAtomProducer.budget C fields.length)
      (CloseoutRowsRawAtomProducer.input C (word fields) out)=some r ∧
      r.final.heads=CloseoutRowsRawAtomReuse.heads (word fields).length (counts fields).sum
        (out++CloseoutRowsRawAtomSeek.cacheWord (cache fields)) ∧
      r.final.tapes=CloseoutRowsRawAtomReuse.data C (word fields) (counts fields).sum (counts fields).sum
        (out++CloseoutRowsRawAtomSeek.cacheWord (cache fields)) ∧
      r.steps ≤ CloseoutRowsRawAtomProducer.budget C fields.length := by
  have h:=CloseoutRowsRawAtomProducer.producer_run C B (counts fields) out hB hc
  rw [count_bytes,←cache_bytes] at h
  simpa only [machine,counts,List.length_map] using h

end NearCubicWires.RepairOrdinary.CloseoutRowsOriginalTerms
