import Proof.CaseAnalysis.RowsRawAtomBounds
import Proof.MachineModel.Semantics

/-! The physical source-count emitter names the SAME ordered exact children.
Only the address changes from the source's pair to its absolute cache index;
the list of monomial occurrences and its GF(2) value are unchanged. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsRawAtomMeaning
open LocalBitMultitape RepairRepresentation SupplierPipeline SupplierPrinter
open CanonicalFourfoldRowProgram ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem range_parity (offset n : ℕ) :
    CloseoutRowsRawAtomLoop.indices offset n=structuralGF2FinParity
      (fun j : Fin n=>structuralGF2Variable (offset+j.val)) := by
  induction n generalizing offset with
  | zero=>rfl
  | succ n ih=>
    rw [CloseoutRowsRawAtomLoop.indices,List.range'_succ,List.map_cons]
    change [offset]::CloseoutRowsRawAtomLoop.indices (offset+1) n=
      [offset]::structuralGF2FinParity (fun j : Fin n=>structuralGF2Variable (offset+j.succ.val))
    rw [ih]
    congr 2
    funext j
    congr 1
    simp only [Fin.val_succ]
    omega

theorem offset_next {q : ℕ} (a : DecompositionAlgorithm)
    (occ : List (SupportedNormalizedGate q)) (i : Fin occ.length) :
    offset a occ (i.val+1)=offset a occ i.val+(children a (occ.get i)).length := by
  unfold offset
  rw [List.take_succ_eq_append_getElem i.isLt,List.map_append,List.sum_append]
  simp only [List.map_singleton,List.sum_singleton,List.get_eq_getElem]

theorem child_range_bound {q : ℕ} (a : DecompositionAlgorithm)
    (occ : List (SupportedNormalizedGate q)) (i : Fin occ.length) :
    offset a occ i.val+(children a (occ.get i)).length≤B a occ := by
  rw [←offset_next]
  exact offset_le a occ _

theorem indices_valid {q : ℕ} (a : DecompositionAlgorithm)
    (occ : List (SupportedNormalizedGate q)) (i : Fin occ.length) :
    ∀ m∈CloseoutRowsRawAtomLoop.indices (offset a occ i.val) (children a (occ.get i)).length,
      ∀ d∈m,d<B a occ := by
  intro m hm d hd
  obtain ⟨j,hj,rfl⟩:=List.mem_map.mp hm
  have he:d=j:=List.mem_singleton.mp hd
  subst d
  obtain ⟨k,hk,hjk⟩:=List.mem_range'.mp hj
  have hj':j<offset a occ i.val+(children a (occ.get i)).length:=by omega
  exact hj'.trans_le (child_range_bound a occ i)

theorem value {q : ℕ} (a : DecompositionAlgorithm)
    (occ : List (SupportedNormalizedGate q)) (i : Fin occ.length) (input : BitInput q) :
    evaluateStructuralGF2 (encodedFiniteBooleanAssignment
      (fun j : Fin (GS a occ).length=>(GS a occ).get j |>.eval input))
      (CloseoutRowsRawAtomLoop.indices (offset a occ i.val) (children a (occ.get i)).length)=
      (occ.get i).eval input := by
  rw [range_parity,evaluateStructuralGF2_finParity]
  have same : (fun j : Fin (children a (occ.get i)).length=>
      evaluateStructuralGF2 (encodedFiniteBooleanAssignment
        (fun k : Fin (GS a occ).length=>(GS a occ).get k |>.eval input))
        (structuralGF2Variable (offset a occ i.val+j.val)))=
      (fun j : Fin (children a (occ.get i)).length=>(children a (occ.get i)).get j |>.eval input) := by
    funext j
    have bound:=GS_index_lt a occ i.val j.val i.isLt j.isLt
    change offset a occ i.val+j.val<(GS a occ).length at bound
    rw [evaluateStructuralGF2_variable,encodedFiniteBooleanAssignment,dif_pos bound]
    simp only [List.get_eq_getElem]
    rw [GS_getElem a occ i.val j.val i.isLt j.isLt]
  rw [same]
  exact RepairSource.CloseoutRawRows.occurrenceExactChildren_parity_eq a occ input i

def countWord {q : ℕ} (a : DecompositionAlgorithm) (occ : List (SupportedNormalizedGate q)):=
  (counts a occ).flatMap natWord

theorem count_split {q : ℕ} (a : DecompositionAlgorithm)
    (occ : List (SupportedNormalizedGate q)) (i : Fin occ.length) :
    countWord a occ=((counts a occ).take i.val).flatMap natWord++
      natWord (children a (occ.get i)).length++((counts a occ).drop (i.val+1)).flatMap natWord := by
  have hi:i.val<(counts a occ).length:=by simpa only [counts_length] using i.isLt
  have h:=congrArg (List.flatMap natWord) (List.take_append_drop (i.val+1) (counts a occ))
  rw [List.take_succ_eq_append_getElem hi,List.flatMap_append,List.flatMap_append,
    List.flatMap_singleton] at h
  have hc:(counts a occ)[i.val]=(children a (occ.get i)).length:=by
    simp only [counts,List.getElem_map,List.get_eq_getElem]
  simpa only [countWord,hc] using h.symm

theorem source_run {q : ℕ} (a : DecompositionAlgorithm)
    (occ : List (SupportedNormalizedGate q)) (i : Fin occ.length) (out : List Bool) :
    let offset:=offset a occ i.val
    let n:=(children a (occ.get i)).length
    let pre:=((counts a occ).take i.val).flatMap natWord
    ∃ r,runFrom CloseoutRowsRawAtomNative.machine (CloseoutRowsRawAtomNative.budget offset n)
      (CloseoutRowsRawAtomNative.input (countWord a occ) pre.length offset offset out)=some r ∧
      r.final.tapes 0=countWord a occ ∧ r.final.heads 0=pre.length+(natWord n).length ∧
      r.final.tapes 11=UnaryTemplate.tape (offset+n+1) ∧ r.final.heads 11=1 ∧
      r.final.tapes 12=out++ExtIncidence.stream (CloseoutRowsRawAtomLoop.indices offset n) ∧
      r.final.heads 12=(out++ExtIncidence.stream (CloseoutRowsRawAtomLoop.indices offset n)).length ∧
      r.steps≤64*(B a occ+2)^2 := by
  dsimp only
  obtain ⟨r,hr,t0,h0,_t10,_h10,t11,h11,t12,h12,_t13,_h13,hs⟩:=
    CloseoutRowsRawAtomNative.native_run (((counts a occ).take i.val).flatMap natWord)
      (((counts a occ).drop (i.val+1)).flatMap natWord) out (offset a occ i.val)
      (children a (occ.get i)).length (offset a occ i.val)
  rw [←count_split a occ i] at hr t0
  have hb:=CloseoutRowsRawAtomBounds.native_bound _ _ _ (child_range_bound a occ i)
  exact ⟨r,hr,t0,h0,t11,h11,t12,h12,by omega⟩

end NearCubicWires.RepairOrdinary.CloseoutRowsRawAtomMeaning
