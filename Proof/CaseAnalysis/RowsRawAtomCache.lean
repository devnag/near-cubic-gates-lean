import Proof.CaseAnalysis.RowsRawAtomRead

/-! The cache reader's polynomial list is exactly the output of the actual
source-count producer. Its indices are absolute positions in the SAME GS;
zero-child occurrences retain a cache slot. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsRawAtomCache
open CanonicalFourfoldRowProgram ExtDecompositionBatch SupplierPipeline
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def cache : ℕ→List ℕ→List (List (List ℕ))
  | _,[]=>[]
  | offset,n::ns=>CloseoutRowsRawAtomLoop.indices offset n::cache (offset+n) ns

theorem cache_length (offset : ℕ) (ns : List ℕ) : (cache offset ns).length=ns.length := by
  induction ns generalizing offset with
  | nil=>rfl
  | cons n ns ih=>simp [cache,ih]

theorem cache_word (offset : ℕ) (ns : List ℕ) :
    CloseoutRowsRawAtomSeek.cacheWord (cache offset ns)=CloseoutRowsRawAtomBatch.atoms offset ns := by
  induction ns generalizing offset with
  | nil=>rfl
  | cons n ns ih=>
    simp only [cache,CloseoutRowsRawAtomSeek.cacheWord,List.flatMap_cons,CloseoutRowsRawAtomBatch.atoms]
    exact congrArg (fun w=>ExtIncidence.stream (CloseoutRowsRawAtomLoop.indices offset n)++w) (ih (offset+n))

theorem cache_getElem (offset : ℕ) (ns : List ℕ) (i : ℕ) (hi : i<ns.length) :
    (cache offset ns)[i]'(by rw [cache_length];exact hi)=
      CloseoutRowsRawAtomLoop.indices (offset+(ns.take i).sum) ns[i] := by
  induction ns generalizing offset i with
  | nil=>simp at hi
  | cons n ns ih=>
    cases i with
    | zero=>simp [cache]
    | succ i=>
      have h:i<ns.length:=by simpa using hi
      simpa [cache,List.take_succ_cons,Nat.add_assoc] using ih (offset+n) i h

def sourceCache {q : ℕ} (a : RepairRepresentation.DecompositionAlgorithm)
    (occ : List (SupportedNormalizedGate q)):=cache 0 (counts a occ)

theorem source_length {q : ℕ} (a : RepairRepresentation.DecompositionAlgorithm)
    (occ : List (SupportedNormalizedGate q)) : (sourceCache a occ).length=occ.length := by
  simp [sourceCache,cache_length,counts_length]

theorem source_word {q : ℕ} (a : RepairRepresentation.DecompositionAlgorithm)
    (occ : List (SupportedNormalizedGate q)) :
    CloseoutRowsRawAtomSeek.cacheWord (sourceCache a occ)=CloseoutRowsRawAtomBatch.atoms 0 (counts a occ) :=
  cache_word 0 (counts a occ)

theorem source_getElem {q : ℕ} (a : RepairRepresentation.DecompositionAlgorithm)
    (occ : List (SupportedNormalizedGate q)) (i : ℕ) (hi : i<occ.length) :
    (sourceCache a occ)[i]'(by rw [source_length];exact hi)=
      CloseoutRowsRawAtomLoop.indices (offset a occ i) (children a occ[i]).length := by
  have h:=cache_getElem 0 (counts a occ) i (by simpa only [counts_length] using hi)
  simpa only [sourceCache,counts,offset,List.map_take,Nat.zero_add,List.getElem_map] using h

theorem source_value {q : ℕ} (a : RepairRepresentation.DecompositionAlgorithm)
    (occ : List (SupportedNormalizedGate q)) (i : Fin occ.length) (input : BitInput q) :
    evaluateStructuralGF2 (encodedFiniteBooleanAssignment
      (fun j : Fin (GS a occ).length=>(GS a occ).get j |>.eval input))
      ((sourceCache a occ)[i.val]'(by rw [source_length];exact i.isLt))=(occ.get i).eval input := by
  rw [source_getElem]
  exact CloseoutRowsRawAtomMeaning.value a occ i input

theorem indices_length (offset n B : ℕ) (h : offset+n≤B) :
    (ExtIncidence.stream (CloseoutRowsRawAtomLoop.indices offset n)).length≤n*(B+4)+1 := by
  induction n generalizing offset with
  | zero=>simp [CloseoutRowsRawAtomLoop.indices,ExtIncidence.stream]
  | succ n ih=>
    have hr:=ih (offset+1) (by omega)
    have word:ExtIncidence.stream (CloseoutRowsRawAtomLoop.indices offset (n+1))=
        ExtIncidence.monomialWord [offset]++
          ExtIncidence.stream (CloseoutRowsRawAtomLoop.indices (offset+1) n):=by
      simp only [CloseoutRowsRawAtomLoop.indices,List.range'_succ,List.map_cons,ExtIncidence.stream_cons]
    rw [word,List.length_append,ExtIncidence.monomialWord_length]
    simp only [List.flatMap_singleton,ExtIncidence.block_length]
    nlinarith

theorem word_length (offset B : ℕ) (ns : List ℕ) (h : offset+ns.sum≤B) :
    (CloseoutRowsRawAtomSeek.cacheWord (cache offset ns)).length≤ns.sum*(B+4)+ns.length := by
  induction ns generalizing offset with
  | nil=>simp [cache,CloseoutRowsRawAtomSeek.cacheWord]
  | cons n ns ih=>
    have first:=indices_length offset n B (by simp only [List.sum_cons] at h;omega)
    have rest:=ih (offset+n) (by simp only [List.sum_cons] at h;omega)
    simp only [cache,CloseoutRowsRawAtomSeek.cacheWord,List.flatMap_cons,List.length_append,
      List.sum_cons,List.length_cons] at rest ⊢
    nlinarith

theorem source_word_length {q : ℕ} (a : RepairRepresentation.DecompositionAlgorithm)
    (occ : List (SupportedNormalizedGate q)) :
    (CloseoutRowsRawAtomSeek.cacheWord (sourceCache a occ)).length≤
      B a occ*(B a occ+4)+occ.length := by
  have h:=word_length 0 (B a occ) (counts a occ) (by rw [Nat.zero_add,B_eq_sum])
  simpa only [sourceCache,←B_eq_sum,counts_length] using h

end NearCubicWires.RepairOrdinary.CloseoutRowsRawAtomCache
