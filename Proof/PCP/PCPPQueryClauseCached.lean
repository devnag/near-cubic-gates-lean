import Proof.PCP.PCPPQueryClauseRetained

/-! The retained local clause reader on the SAME faithful PCPP object. -/
namespace NearCubicWires.RepairOrdinary.PCPPQueryClause
open LocalBitMultitape RepairRepresentation SourceInterfaces PCPPQueryField
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem lookup_retained_run {n0 : ℕ} (r : PCPPRequest n0) (p : PointwisePCPP r.circuit) (i : Fin (2^p.clauseBits)) :
    ∃ receipt,runFrom machine (queryBudget r p i) (entry (pcppOutput r p) r.arity i.val)=some receipt ∧
      receipt.steps≤queryBudget r p i ∧ receipt.final.tapes 15=
        natListWord [literalIndex (p.clauses i).left,literalIndex (p.clauses i).right] ∧
      receipt.final.tapes 0=pcppOutput r p ∧ receipt.final.tapes 13=UnaryTemplate.tape r.arity ∧
      receipt.final.heads 13=1 ∧ receipt.final.tapes 14=UnaryTemplate.tape i.val ∧ receipt.final.heads 14=1 := by
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
  obtain ⟨base,hb,hbs,hbo,hsource,harity,harityHead,hindex,hindexHead⟩ := clause_retained_run p.systematicBits p.auxiliaryBits p.clauseBits r.arity
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
  rw [hword] at hsource
  rw [hlen] at hindex
  exact ⟨base,hb,hbs,hbo,hsource,harity,harityHead,hindex,hindexHead⟩

end NearCubicWires.RepairOrdinary.PCPPQueryClause
