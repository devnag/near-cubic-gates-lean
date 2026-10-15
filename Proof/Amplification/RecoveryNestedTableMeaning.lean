import Proof.Amplification.RecoveryNestedTableBudget

/-! Exact soundness and completeness bridges for the same prepared nested
execution, using one finite valuation parsed from the retained witness word. -/
namespace NearCubicWires.RepairOrdinary.RecoveryNestedTable
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRowStructure
open RepairSource.RecoveryOracle
open CompactCertificate CompactCertificate.Serialization BalancedCertificate
open private decodeClauseCodes from StatementSupport
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem valuation_predicate (x : State) (word : List Bool) (table : FiniteValuation.Table) (rest : List Bool)
    (hp : readList x.inner.base.extra.cap (readEntry x.inner.base.state.bits.length) word=some (table,rest)) :
    tableLeafPredicate x.inner word=clausePredicate (RadixSemantics.value x.inner.base.extra.committed)
      (RadixSemantics.value x.inner.base.extra.binaryCount) table := by
  funext code
  simp only [tableLeafPredicate,hp,Option.any_some]

theorem answer_meaning (x : State) (word innerBits outerBits : List Bool)
    (table : FiniteValuation.Table) (rest : List Bool)
    (hp : readList x.inner.base.extra.cap (readEntry x.inner.base.state.bits.length) word=some (table,rest))
    (ha : answer x word innerBits outerBits=true) :
    ∃ codes,BalancedCNFSATEncoding.decodeNestedBalancedCNFPayload (RadixSemantics.value x.outer.key)=some codes ∧
      compactMeaning ⟨decodeClauseCodes codes,RadixSemantics.value x.inner.base.extra.committed,
        RadixSemantics.value x.inner.base.extra.binaryCount⟩ := by
  obtain ⟨codes,hd,hc⟩ := answer_sound x word innerBits outerBits ha
  rw [valuation_predicate x word table rest hp,clause_codes_check] at hc
  exact ⟨codes,hd,FiniteValuation.check_sound _ table hc⟩

theorem answer_eq_nestedCheck (x : State) (word innerBits outerBits : List Bool)
    (inner outer : List Row) (innerRest outerRest : List Bool)
    (hi : readMany (readRow x.inner.base.state.bits.length) x.innerTotal innerBits=some (inner,innerRest))
    (ho : readMany (readRow x.outer.data.outer.base.state.bits.length) x.outer.total outerBits=some (outer,outerRest)) :
    answer x word innerBits outerBits=nestedCheck (tableLeafPredicate x.inner word) inner outer
      (RadixSemantics.value x.outer.key) := by
  unfold answer
  rw [hi,Option.any_some]
  unfold RecoveryOuterRoot.wholeAnswer
  rw [ho,Option.any_some,predicate_hasRoot]
  rfl

theorem nested_meaning_run (x : State) (limit : Nat) (word innerBits outerBits innerPre outerPre : List Bool)
    (hx : Prepared x limit word innerBits outerBits innerPre outerPre)
    (hl : limit ≤ 3*(x.inner.base.state.bits.length+1))
    (table : FiniteValuation.Table) (rest : List Bool)
    (hp : readList x.inner.base.extra.cap (readEntry x.inner.base.state.bits.length) word=some (table,rest)) :
    ∃ r,runFrom machine (budget x limit) (x.cfg machine.start)=some r ∧
      r.steps ≤ 134217728*(x.inner.base.state.bits.length+1)^3 ∧
      r.final.heads 50=0 ∧ r.final.tapes 50=[answer x word innerBits outerBits] ∧
      (r.final.tapes 50=[true] → ∃ codes,
        BalancedCNFSATEncoding.decodeNestedBalancedCNFPayload (RadixSemantics.value x.outer.key)=some codes ∧
        compactMeaning ⟨decodeClauseCodes codes,RadixSemantics.value x.inner.base.extra.committed,
          RadixSemantics.value x.inner.base.extra.binaryCount⟩) := by
  have hrun := nested_run x limit word innerBits outerBits innerPre outerPre hx
  obtain ⟨r,hr,hb,hh,ht,_⟩ := hrun
  refine ⟨r,hr,hb.trans (budget_le x limit word innerBits outerBits innerPre outerPre hx hl),hh,ht,?_⟩
  intro ha
  have he : answer x word innerBits outerBits=true := List.singleton_inj.mp (ht.symm.trans ha)
  exact answer_meaning x word innerBits outerBits table rest hp he

end NearCubicWires.RepairOrdinary.RecoveryNestedTable
