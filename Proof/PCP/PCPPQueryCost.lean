import Proof.PCP.PCPPQueryClauseSemantics

/-! Bit-time charges for the actual accessor programs. The common scalar
majorant includes both the source's explicit-object bound and the canonical
circuit encoding width; indices and fields are never unit-cost operations. -/
namespace NearCubicWires.RepairOrdinary.PCPPQueryCost
open RepairRepresentation PCPPQueryField
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem width_le (n : ℕ) : natBitLength n≤n+1 := by
  have h := Nat.log_le_self 2 n
  unfold natBitLength
  omega

theorem word_length (n : ℕ) : (natWord n).length=2*natBitLength n+1 :=
  fieldBits_length n

theorem natural_le (n M : ℕ) (hn : n≤M) : PCPPQueryNatural.budget n≤80*(M+1)^2 := by
  have hw := width_le n
  have hm := Nat.mul_le_mul hn (show 8*natBitLength n+10≤8*(M+1)+10 by omega)
  unfold PCPPQueryNatural.budget MatrixDimensionPrepare.budget
  nlinarith

theorem prepare_le (arity index : ℕ) (code : List Bool) (M : ℕ)
    (ha : arity≤M) (hi : index≤M) (hc : code.length≤M) :
    PCPPQueryPrepare.budget arity index code≤1000*(M+1)^2 := by
  have han := natural_le arity M ha
  have hin := natural_le index M hi
  have haw := width_le arity
  have hiw := width_le index
  simp only [PCPPQueryPrepare.budget,PCPPQueryPrepareCopy.budget,PCPPQueryInput.budget,
    PCPPQueryPrepare.word,List.length_append,frame_length,word_length]
  nlinarith

theorem support_le (a b c arity index M : ℕ)
    (ha : a≤M) (hb : b≤M) (hc : c≤M) (hw : arity≤M) (hi : index≤M) :
    PCPPQuerySupport.budget a b c arity index≤100*(M+1)^2 := by
  have hwa := width_le a
  have hwb := width_le b
  have hwc := width_le c
  have hm := Nat.mul_le_mul hi (show 2*arity+7≤2*M+7 by omega)
  simp only [PCPPQuerySupport.budget,PCPPQueryRows.budget,fourCost,pairCost,fieldCost]
  norm_num only [show natBitLength 3=2 by decide]
  nlinarith

theorem pair_length_le (a b M : ℕ) (ha : a≤4*M) (hb : b≤4*M) :
    (pairBits a b).length≤16*M+6 := by
  have hwa := width_le a
  have hwb := width_le b
  simp only [pairBits,List.length_append,fieldBits_length]
  omega

theorem stream_length_le (rows : List (ℕ×ℕ)) (M : ℕ)
    (hrows : ∀ p∈rows,p.1≤4*M ∧ p.2≤4*M) :
    (PCPPQueryClauseRows.stream rows).length≤rows.length*(16*M+6) := by
  induction rows with
  | nil => simp [PCPPQueryClauseRows.stream]
  | cons p rows ih =>
    have hp := hrows p (by simp)
    have ht := ih (fun q hq => hrows q (by simp [hq]))
    have hpair := pair_length_le p.1 p.2 M hp.1 hp.2
    simp only [PCPPQueryClauseRows.stream,List.map_cons,List.flatten_cons,List.length_append] at *
    simp only [List.length_cons]
    nlinarith

theorem clause_le (a b c arity count : ℕ) (rows : List (ℕ×ℕ)) (left right M : ℕ)
    (ha : a≤M) (hb : b≤M) (hc : c≤M) (hw : arity≤M) (hcount : count≤2*M)
    (hlen : rows.length≤M) (hrows : ∀ p∈rows,p.1≤4*M ∧ p.2≤4*M)
    (hl : left≤4*M) (hr : right≤4*M) :
    PCPPQueryClause.budget a b c arity count rows left right≤1000*(M+1)^2 := by
  have hn := natural_le a M ha
  have hwb := width_le b
  have hwc := width_le c
  have hwcount := width_le count
  have hpair := pair_length_le left right M hl hr
  have hstream := (stream_length_le rows M hrows).trans (Nat.mul_le_mul_right _ hlen)
  have hmatrix := Nat.mul_le_mul ha (show 2*arity+7≤2*M+7 by omega)
  simp only [PCPPQueryClause.budget,PCPPQueryClauseMatrix.budget,PCPPQueryClauseHeader.budget,
    PCPPQueryClauseLookup.budget,PCPPQueryClauseRows.budget,pairCost,fieldCost,
    PCPPQueryClauseLookup.prefixBits,word_length]
  norm_num only [show natBitLength 3=2 by decide,show natBitLength 2=2 by decide]
  nlinarith

end NearCubicWires.RepairOrdinary.PCPPQueryCost
