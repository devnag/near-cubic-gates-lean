import Proof.PCP.PCPPQueryClause

/-! Exact same-source semantics of the complete clause reader. Clause
indices range over the actual source's finite clause family; list framing,
pair order and literal signs are preserved byte for byte. -/
namespace NearCubicWires.RepairOrdinary.PCPPQueryClause
open LocalBitMultitape RepairRepresentation SourceInterfaces PCPPQueryField
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def clausePairs {n0 : ℕ} (r : PCPPRequest n0) (p : PointwisePCPP r.circuit) : List (ℕ×ℕ) :=
  List.ofFn fun i : Fin (2^p.clauseBits) => (literalIndex (p.clauses i).left,literalIndex (p.clauses i).right)

theorem list_pairs_word (rows : List (ℕ×ℕ)) :
    natListWord (rows.flatMap (fun p => [p.1,p.2]))=
      natWord (2*rows.length)++PCPPQueryClauseRows.stream rows := by
  have hlen : (rows.flatMap (fun p => [p.1,p.2])).length=2*rows.length := by
    induction rows with
    | nil => simp
    | cons row rows ih => simp [ih]; omega
  have hfields : (rows.flatMap (fun p => [p.1,p.2])).flatMap natWord=PCPPQueryClauseRows.stream rows := by
    clear hlen
    induction rows with
    | nil => rfl
    | cons row rows ih =>
      simpa [PCPPQueryClauseRows.stream,pairBits,fieldBits,List.append_assoc]
        using congrArg (fun x => (natWord row.1++natWord row.2)++x) ih
  simp only [natListWord,hlen,hfields]

theorem tail_word {n0 : ℕ} (r : PCPPRequest n0) (p : PointwisePCPP r.circuit) :
    PCPPQuerySupport.clauseTail r p=natWord (2*2^p.clauseBits)++PCPPQueryClauseRows.stream (clausePairs r p) := by
  have he : (List.ofFn fun i : Fin (2^p.clauseBits) =>
      [literalIndex (p.clauses i).left,literalIndex (p.clauses i).right]).flatten=
      (clausePairs r p).flatMap (fun q => [q.1,q.2]) := by
    simp only [clausePairs,List.flatMap_def,List.map_ofFn]
    rfl
  unfold PCPPQuerySupport.clauseTail
  rw [he,list_pairs_word]
  simp [clausePairs]

theorem output_word {n0 : ℕ} (r : PCPPRequest n0) (p : PointwisePCPP r.circuit) :
    pcppOutput r p=fourBits 3 p.systematicBits p.auxiliaryBits p.clauseBits++
      (PCPPQuerySupport.supportRows r p).flatten++natWord (2*2^p.clauseBits)++
      PCPPQueryClauseRows.stream (clausePairs r p) := by
  rw [PCPPQuerySupport.output_word,tail_word]
  simp [PCPPQuerySupport.headerBits,List.append_assoc]

theorem stream_split (rows : List (ℕ×ℕ)) (i : ℕ) (hi : i<rows.length) :
    PCPPQueryClauseRows.stream (rows.take i)++pairBits rows[i].1 rows[i].2++
      PCPPQueryClauseRows.stream (rows.drop (i+1))=PCPPQueryClauseRows.stream rows := by
  have h := MatrixCropCells.split_at (rows.map (fun p => pairBits p.1 p.2)) i (by simpa using hi)
  simpa [PCPPQueryClauseRows.stream] using h

def queryBudget {n0 : ℕ} (r : PCPPRequest n0) (p : PointwisePCPP r.circuit) (i : Fin (2^p.clauseBits)) :=
  budget p.systematicBits p.auxiliaryBits p.clauseBits r.arity (2*2^p.clauseBits)
    ((clausePairs r p).take i.val) (literalIndex (p.clauses i).left) (literalIndex (p.clauses i).right)

theorem lookup_run {n0 : ℕ} (r : PCPPRequest n0) (p : PointwisePCPP r.circuit) (i : Fin (2^p.clauseBits)) :
    ∃ receipt,runFrom machine (queryBudget r p i) (entry (pcppOutput r p) r.arity i.val)=some receipt ∧
      receipt.steps≤queryBudget r p i ∧ receipt.final.tapes 15=
        natListWord [literalIndex (p.clauses i).left,literalIndex (p.clauses i).right] := by
  let rows := clausePairs r p
  have hi : i.val<rows.length := by simp [rows,clausePairs]
  have hm : rows[i.val]=(literalIndex (p.clauses i).left,literalIndex (p.clauses i).right) := by simp [rows,clausePairs]
  have hsplit := stream_split rows i.val hi
  rw [hm] at hsplit
  have hw : ∀ row∈PCPPQuerySupport.supportRows r p,row.length=r.arity := by
    intro row hrow
    obtain ⟨j,hj⟩ := List.mem_ofFn.mp hrow
    rw [← hj]
    simp [PCPPQuerySupport.mask]
  obtain ⟨base,hb,hbs,hbo⟩ := clause_run p.systematicBits p.auxiliaryBits p.clauseBits r.arity
    (PCPPQuerySupport.supportRows r p) (2*2^p.clauseBits) (rows.take i.val)
    (literalIndex (p.clauses i).left) (literalIndex (p.clauses i).right)
    (PCPPQueryClauseRows.stream (rows.drop (i.val+1))) (by simp [PCPPQuerySupport.supportRows]) hw
  have hword : fourBits 3 p.systematicBits p.auxiliaryBits p.clauseBits++
      (PCPPQuerySupport.supportRows r p).flatten++natWord (2*2^p.clauseBits)++
      PCPPQueryClauseRows.stream (rows.take i.val)++pairBits (literalIndex (p.clauses i).left)
        (literalIndex (p.clauses i).right)++PCPPQueryClauseRows.stream (rows.drop (i.val+1))=pcppOutput r p := by
    rw [output_word]
    rw [← hsplit]
    simp only [rows,List.append_assoc]
  have hlen : (rows.take i.val).length=i.val := by simp [List.length_take,Nat.min_eq_left hi.le]
  rw [hword,hlen] at hb
  exact ⟨base,hb,hbs,hbo⟩

end NearCubicWires.RepairOrdinary.PCPPQueryClause
