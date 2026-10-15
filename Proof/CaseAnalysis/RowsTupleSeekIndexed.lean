import Proof.CaseAnalysis.RowsTupleSeekRawRun
import Proof.CaseAnalysis.RowsTupleSeekFamilyRewind

/-! One original term index selects all four outputs in lockstep. The raw
index belongs to the family-term carrier, before gate decomposition. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsTupleSeek
open LocalBitMultitape ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def familyWords (ts : List TermSlices) : Fin 3 → List Bool := fun i=>ts.flatMap (fun t=>t.words (i.castAdd 1))
def familyPosition (ts : List TermSlices) (j : ℕ) : Fin 3 → ℕ := fun i=>(familyWords (ts.take j) i).length
noncomputable def indexedMachine := Composition.machine (RawLoop.machine (familyTerm false))
  (TapeEmbedding.machine 1 (Composition.machine (familyTerm true) familyRewind))
def indexedCost (C D n : ℕ) := n*(4*C+11)+4*C+6*D+22

theorem family_term_run (keep : Bool) (t : TermSlices) (pre tail : Fin 3 → List Bool)
    (out : Fin 4 → List Bool) (C D : ℕ) (hC : t.cost+1 ≤ C) :
    Step (familyTerm keep) (4*C+7)
      (familyHeads (fun i=>(pre i).length) out) (familyData C D (sources t pre tail) out)
      (familyHeads (fun i=>(pre i).length+(t.words (i.castAdd 1)).length) (appended keep t out))
      (familyData C D (sources t pre tail) (appended keep t out)) :=
  (reusable_run keep t pre tail out C hC).embed (fun _ : Fin 2=>0)
    ![List.replicate D true,List.replicate (D+1) false]

theorem skip_prefix (before after : List TermSlices) (out : Fin 4 → List Bool) (C D : ℕ)
    (hC : ∀ t∈before,t.cost+1 ≤ C) (pre tail : List Bool) :
    Step (RawLoop.machine (familyTerm false)) (before.length*(4*C+11)+5)
      (RawLoop.heads (familyHeads (fun _=>0) out) pre.length)
      (RawLoop.data (familyData C D (familyWords (before++after)) out) (pre++ExtIncidence.block before.length++tail))
      (RawLoop.heads (familyHeads (familyPosition before before.length) out) (pre.length+(ExtIncidence.block before.length).length))
      (RawLoop.data (familyData C D (familyWords (before++after)) out) (pre++ExtIncidence.block before.length++tail)) := by
  have supplier (j : ℕ) (hj : j < before.length) :
      Step (familyTerm false) (4*C+7)
        (familyHeads (familyPosition before j) out) (familyData C D (familyWords (before++after)) out)
        (familyHeads (familyPosition before (j+1)) out) (familyData C D (familyWords (before++after)) out) := by
    have run := family_term_run false before[j] (familyWords (before.take j))
      (familyWords (before.drop (j+1)++after)) out C D (hC _ (List.getElem_mem hj))
    have split : before.take j++[before[j]]++before.drop (j+1)=before := by
      rw [←List.take_succ_eq_append_getElem hj,List.take_append_drop]
    have same : sources before[j] (familyWords (before.take j))
        (familyWords (before.drop (j+1)++after))=familyWords (before++after) := by
      funext i
      have h := congrArg (fun ts : List TermSlices=>familyWords (ts++after) i) split
      simpa only [sources,familyWords,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
        List.append_nil,List.append_assoc] using h
    have pos : (fun i=>(familyWords (before.take j) i).length+(before[j].words (i.castAdd 1)).length)=
        familyPosition before (j+1) := by
      funext i
      simp only [familyPosition,List.take_succ_eq_append_getElem hj,familyWords,List.flatMap_append,
        List.flatMap_cons,List.flatMap_nil,List.append_nil,List.length_append]
    have emitted : appended false before[j] out=out := by funext i;simp [appended,selected]
    rw [same,pos,emitted] at run
    exact run
  have h := RawLoop.raw_run (familyTerm false) (4*C+7) before.length
    (fun j=>familyHeads (familyPosition before j) out)
    (fun _=>familyData C D (familyWords (before++after)) out) supplier pre tail
  have zeroPos : familyPosition before 0=(fun _=>0) := by
    funext i;simp only [familyPosition,List.take_zero,familyWords,List.flatMap_nil,List.length_nil]
  rw [zeroPos,show 4*C+7+4=4*C+11 by omega] at h
  exact h

theorem indexed_run (before after : List TermSlices) (t : TermSlices) (out : Fin 4 → List Bool)
    (C D : ℕ) (hC : ∀ a∈before++[t],a.cost+1 ≤ C)
    (hD : ∀ i,(familyWords (before++t::after) i).length ≤ D) (pre tail : List Bool) :
    Step indexedMachine (indexedCost C D before.length)
      (RawLoop.heads (familyHeads (fun _=>0) out) pre.length)
      (RawLoop.data (familyData C D (familyWords (before++t::after)) out) (pre++ExtIncidence.block before.length++tail))
      (RawLoop.heads (familyHeads (fun _=>0) (appended true t out)) (pre.length+(ExtIncidence.block before.length).length))
      (RawLoop.data (familyData C D (familyWords (before++t::after)) (appended true t out)) (pre++ExtIncidence.block before.length++tail)) := by
  have first := skip_prefix before (t::after) out C D (by intro a ha;exact hC a (List.mem_append_left _ ha)) pre tail
  have copy := family_term_run true t (familyWords before) (familyWords after) out C D
    (hC t (by simp))
  have same : sources t (familyWords before) (familyWords after)=familyWords (before++t::after) := by
    funext i;simp [sources,familyWords,List.flatMap_append,List.append_assoc]
  rw [same] at copy
  have reset := family_rewind_run C D (familyWords (before++t::after))
    (fun i=>(familyWords before i).length+(t.words (i.castAdd 1)).length) (appended true t out)
    (by intro i;have h:=hD i
        simp only [familyWords,List.flatMap_append,List.flatMap_cons,List.length_append] at h ⊢
        omega)
  have last := (copy.seq reset).embed
    (fun _ : Fin 1=>pre.length+(ExtIncidence.block before.length).length)
    (fun _=>pre++ExtIncidence.block before.length++tail)
  have position : familyPosition before before.length=(fun i=>(familyWords before i).length) := by
    funext i;simp only [familyPosition,List.take_length]
  rw [position] at first
  have all := first.seq last
  have time : before.length*(4*C+11)+5+1+(4*C+7+1+(6*D+8))=indexedCost C D before.length := by
    unfold indexedCost;omega
  rw [time] at all
  exact all

end NearCubicWires.RepairOrdinary.CloseoutRowsTupleSeek
