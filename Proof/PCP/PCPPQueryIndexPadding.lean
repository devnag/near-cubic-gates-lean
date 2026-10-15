import Proof.PCP.PCPPQueryCapacity

/-! Allocated index buffers for arbitrary repeated SAME-cache queries.
Only the existing index tape is padded. All operations use the same machines. -/
namespace NearCubicWires.RepairOrdinary.PCPPQueryIndexPadding
open LocalBitMultitape RepairRepresentation SourceInterfaces RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def supportCaps (C : ℕ) (j : Fin 9) := if j=5 then C else 0
def supportData (source : List Bool) (arity index C : ℕ) (result : List Bool) (j : Fin 9) :=
  if j=5 then ZeroPadding.pad C (UnaryTemplate.tape index) else PCPPQuerySupportReuse.data source arity index C result j
noncomputable def supportEntry (source : List Bool) (arity index C : ℕ) :=
  ZeroPadding.config (supportCaps C) (PCPPQuerySupportReuse.entry source arity index C)

theorem support_config (source : List Bool) (arity index C : ℕ) (result : List Bool)
    {states : ℕ} (q : Fin states) :
    ZeroPadding.config (supportCaps C) ⟨q,PCPPQuerySupportReuse.heads,PCPPQuerySupportReuse.data source arity index C result⟩=
      ⟨q,PCPPQuerySupportReuse.heads,supportData source arity index C result⟩ := by
  apply configuration_ext
  · rfl
  · rfl
  · funext j
    fin_cases j <;> simp [supportCaps,supportData,ZeroPadding.config,ZeroPadding.pad_zero]
    rfl

theorem support_entry (source : List Bool) (arity index C : ℕ) :
    supportEntry source arity index C=⟨PCPPQuerySupportReuse.machine.start,PCPPQuerySupportReuse.heads,supportData source arity index C []⟩ := by
  rw [supportEntry,PCPPQuerySupportReuse.entry_literal,support_config]

theorem support_run (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (i : Fin (a.output r).systematicBits) :
    let C := PCPPQueryCachedBounds.capacity a (r.circuit.size+r.arity)
    ∃ receipt,runFrom PCPPQuerySupportReuse.machine (PCPPQueryCachedBounds.callBudget a (r.circuit.size+r.arity))
      (supportEntry (pcppOutput r (a.output r)) r.arity i.val C)=some receipt ∧
      receipt.final.tapes=supportData (pcppOutput r (a.output r)) r.arity i.val C
        (PCPPQuerySupport.mask r (a.output r) i) ∧
      receipt.final.heads=PCPPQuerySupportReuse.heads ∧
      receipt.steps≤PCPPQueryCachedBounds.callBudget a (r.circuit.size+r.arity) := by
  dsimp only
  let C := PCPPQueryCachedBounds.capacity a (r.circuit.size+r.arity)
  obtain ⟨base,hb,bt,bh,bs⟩ := PCPPQueryCachedBounds.support_run a r i
  obtain ⟨out,hr,hf,hs,_⟩ := ZeroPadding.run_config PCPPQuerySupportReuse.machine (supportCaps C) _ _ base hb
  refine ⟨out,hr,?_,?_,hs.le.trans bs⟩
  · rw [hf]
    change (ZeroPadding.config (supportCaps C) base.final).tapes=_
    have he : base.final=⟨base.final.control,PCPPQuerySupportReuse.heads,PCPPQuerySupportReuse.data (pcppOutput r (a.output r)) r.arity i.val C
        (PCPPQuerySupport.mask r (a.output r) i)⟩ := by
      apply configuration_ext
      · rfl
      · exact bh
      · exact bt
    rw [he,support_config]
  · rw [hf]
    exact bh

theorem support_clear (source : List Bool) (arity index C : ℕ) (result : List Bool)
    (hresult : result.length≤C) :
    ∃ r,runFrom PCPPQuerySupportReuse.clearResult (2*C+4)
      ⟨PCPPQuerySupportReuse.clearResult.start,PCPPQuerySupportReuse.heads,supportData source arity index C result⟩=some r ∧
      r.final.heads=PCPPQuerySupportReuse.heads ∧ r.final.tapes=supportData source arity index C [] ∧ r.steps=2*C+4 := by
  obtain ⟨base,hb,bh,bt,bs⟩ := PCPPQuerySupportReuse.clear_result_run source arity index C result hresult
  obtain ⟨out,hr,hf,hs,_⟩ := ZeroPadding.run_config PCPPQuerySupportReuse.clearResult (supportCaps C) _ _ base hb
  rw [support_config] at hr
  refine ⟨out,hr,?_,?_,hs.trans bs⟩
  · rw [hf]
    exact bh
  · rw [hf]
    have he : base.final=⟨base.final.control,PCPPQuerySupportReuse.heads,PCPPQuerySupportReuse.data source arity index C []⟩ := by
      apply configuration_ext
      · rfl
      · exact bh
      · exact bt
    rw [he,support_config]

def clauseCaps (C : ℕ) (j : Fin 19) := if j=14 then C else 0
def clauseData (source : List Bool) (arity index C : ℕ) (result : List Bool) (j : Fin 19) :=
  if j=14 then ZeroPadding.pad C (UnaryTemplate.tape index) else PCPPQueryClauseReuse.data source arity index C result j
noncomputable def clauseEntry (source : List Bool) (arity index C : ℕ) :=
  ZeroPadding.config (clauseCaps C) (PCPPQueryClauseReuse.entry source arity index C)

theorem clause_config (source : List Bool) (arity index C : ℕ) (result : List Bool)
    {states : ℕ} (q : Fin states) :
    ZeroPadding.config (clauseCaps C) ⟨q,PCPPQueryClauseReuse.heads,PCPPQueryClauseReuse.data source arity index C result⟩=
      ⟨q,PCPPQueryClauseReuse.heads,clauseData source arity index C result⟩ := by
  apply configuration_ext
  · rfl
  · rfl
  · funext j
    fin_cases j <;> simp [clauseCaps,clauseData,ZeroPadding.config,ZeroPadding.pad_zero]
    rfl

theorem clause_entry (source : List Bool) (arity index C : ℕ) :
    clauseEntry source arity index C=⟨PCPPQueryClauseReuse.machine.start,PCPPQueryClauseReuse.heads,clauseData source arity index C []⟩ := by
  rw [clauseEntry,PCPPQueryClauseReuse.entry_literal,clause_config]

theorem clause_run (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (i : Fin (2^(a.output r).clauseBits)) :
    let C := PCPPQueryCachedBounds.capacity a (r.circuit.size+r.arity)
    ∃ receipt,runFrom PCPPQueryClauseReuse.machine (PCPPQueryCachedBounds.callBudget a (r.circuit.size+r.arity))
      (clauseEntry (pcppOutput r (a.output r)) r.arity i.val C)=some receipt ∧
      receipt.final.tapes=clauseData (pcppOutput r (a.output r)) r.arity i.val C
        (natListWord [literalIndex ((a.output r).clauses i).left,literalIndex ((a.output r).clauses i).right]) ∧
      receipt.final.heads=PCPPQueryClauseReuse.heads ∧
      receipt.steps≤PCPPQueryCachedBounds.callBudget a (r.circuit.size+r.arity) := by
  dsimp only
  let C := PCPPQueryCachedBounds.capacity a (r.circuit.size+r.arity)
  obtain ⟨base,hb,bt,bh,bs⟩ := PCPPQueryCachedBounds.clause_run a r i
  obtain ⟨out,hr,hf,hs,_⟩ := ZeroPadding.run_config PCPPQueryClauseReuse.machine (clauseCaps C) _ _ base hb
  refine ⟨out,hr,?_,?_,hs.le.trans bs⟩
  · rw [hf]
    change (ZeroPadding.config (clauseCaps C) base.final).tapes=_
    have he : base.final=⟨base.final.control,PCPPQueryClauseReuse.heads,PCPPQueryClauseReuse.data (pcppOutput r (a.output r)) r.arity i.val C
        (natListWord [literalIndex ((a.output r).clauses i).left,literalIndex ((a.output r).clauses i).right])⟩ := by
      apply configuration_ext
      · rfl
      · exact bh
      · exact bt
    rw [he,clause_config]
  · rw [hf]
    exact bh

theorem clause_clear (source : List Bool) (arity index C : ℕ) (result : List Bool)
    (hresult : result.length≤C) :
    ∃ r,runFrom PCPPQueryClauseReuse.clearResult (2*C+4)
      ⟨PCPPQueryClauseReuse.clearResult.start,PCPPQueryClauseReuse.heads,clauseData source arity index C result⟩=some r ∧
      r.final.heads=PCPPQueryClauseReuse.heads ∧ r.final.tapes=clauseData source arity index C [] ∧ r.steps=2*C+4 := by
  obtain ⟨base,hb,bh,bt,bs⟩ := PCPPQueryClauseReuse.clear_result_run source arity index C result hresult
  obtain ⟨out,hr,hf,hs,_⟩ := ZeroPadding.run_config PCPPQueryClauseReuse.clearResult (clauseCaps C) _ _ base hb
  rw [clause_config] at hr
  refine ⟨out,hr,?_,?_,hs.trans bs⟩
  · rw [hf]
    exact bh
  · rw [hf]
    have he : base.final=⟨base.final.control,PCPPQueryClauseReuse.heads,PCPPQueryClauseReuse.data source arity index C []⟩ := by
      apply configuration_ext
      · rfl
      · exact bh
      · exact bt
    rw [he,clause_config]

end NearCubicWires.RepairOrdinary.PCPPQueryIndexPadding
