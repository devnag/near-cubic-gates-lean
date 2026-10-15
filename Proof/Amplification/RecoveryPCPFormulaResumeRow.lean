import Proof.Amplification.RecoveryPCPFormulaResumeRowLayout

/-! One ordinary row machine evaluates the actual normalized address batch
and then executes all original source clauses against that same physical
batch. The original-order formula append cursor is retained throughout. -/
namespace NearCubicWires.RepairSource.RecoveryPCPFormulaResumeRow
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound SourceInterfaces ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem list_tapes_other (cap : Nat) (source address out : List Bool) (sourcePos count : Nat) :
    ∀ i : Fin 281,i≠159 → (before cap source out sourcePos count).tapes i=
      (RecoverySourceClauseList.cfg 0 cap source address out sourcePos count 1).tapes i := by
  intro i
  refine Fin.addCases (m:=280) (n:=1) (fun i=>?_) (fun i=>?_) i
  · intro hi
    have hn : i.val≠159 := by
      intro hv
      apply hi
      exact Fin.ext hv
    simp only [before,RecoverySourceClauseList.cfg,VerifierDecoding.RepeatMachine.cfg,controlConfig,
      TapeEmbedding.config,Fin.addCases_left,RecoverySourceClauseReuse.data,hn,ite_false]
  · intro _hi
    simp only [before,RecoverySourceClauseList.cfg,VerifierDecoding.RepeatMachine.cfg,controlConfig,
      TapeEmbedding.config,Fin.addCases_right]

def budget (cap R Q count : Nat) := RecoveryProjectionRowsRewind.budget R Q+1+(count*(5*cap+12)+3)

theorem row_run (p : RawProjectionPCP) (R Q : Nat) (hr : p.width≤R) (hq : p.queries≤Q)
    {n : Nat} (x : BitInput n) (randomness : BitInput R) (cap logCap : Nat) (pre suffix out : List Bool)
    (hc : RecoverySourceClauseLoad.uniformBudget Q R≤cap)
    (hl : RecoveryProjectionRowsRewind.batchBudget R Q+2≤logCap) : ∃ r,
    runFrom machine (budget cap R Q (Codec.clauses p).length)
      ⟨machine.start,
        initialHeads cap (pre++DedupBytes.fields p++suffix) out pre.length (Codec.clauses p).length,
        initialTapes cap (pre++DedupBytes.fields p++suffix) out pre.length (Codec.clauses p).length
          p R Q randomness logCap⟩=some r ∧
      (∀ i : Fin 281,r.final.heads (clauseSlots i)=
        (RecoverySourceClauseList.cfg 3 cap (pre++DedupBytes.fields p++suffix)
          (FieldList.stream (RecoveryProjectionRows.addressFields p R Q hr hq x randomness))
          (out++FieldList.stream (RecoveryPCPFormulaResume.rowWords
            (compactProjectionPCP (p.normalized R Q hr hq)) x randomness))
          (pre++DedupBytes.fields p).length (Codec.clauses p).length 1).heads i) ∧
      (∀ i : Fin 281,r.final.tapes (clauseSlots i)=
        (RecoverySourceClauseList.cfg 3 cap (pre++DedupBytes.fields p++suffix)
          (FieldList.stream (RecoveryProjectionRows.addressFields p R Q hr hq x randomness))
          (out++FieldList.stream (RecoveryPCPFormulaResume.rowWords
            (compactProjectionPCP (p.normalized R Q hr hq)) x randomness))
          (pre++DedupBytes.fields p).length (Codec.clauses p).length 1).tapes i) ∧
      (∀ i : Fin 317,(∀ j,clauseSlots j≠i) →
        r.final.heads i=0 ∧ r.final.tapes i=
          (install addressSlots
            (initialTapes cap (pre++DedupBytes.fields p++suffix) out pre.length (Codec.clauses p).length
              p R Q randomness logCap)
            (Fin.addCases (m:=36) (n:=1) (motive:=fun _=>List Bool)
              (RecoveryProjectionRows.cfg 3 (RecoveryProjectionRows.capacity R) R
                (QueryBytes.framedCodes (normalizedRows p R Q).flatten) (List.ofFn randomness) []
                (FieldList.stream (RecoveryProjectionRows.addressFields p R Q hr hq x randomness))
                (QueryBytes.framedCodes (normalizedRows p R Q).flatten).length Q 1).tapes
              (fun _=>List.replicate logCap false))) i) ∧
      r.steps≤budget cap R Q (Codec.clauses p).length := by
  let source := pre++DedupBytes.fields p++suffix
  let count := (Codec.clauses p).length
  let address := FieldList.stream (RecoveryProjectionRows.addressFields p R Q hr hq x randomness)
  let H := initialHeads cap source out pre.length count
  let I := initialTapes cap source out pre.length count p R Q randomness logCap
  have ready := RecoveryProjectionRowsRewind.batch_ready p R Q hr hq x randomness logCap hl
  obtain ⟨a,ha,ah,atapes,asteps⟩ := ready.focus_at addressSlots address_injective H I
    (by intro i; exact install_slot addressSlots address_injective _ _ i)
    (address_heads cap source out pre.length count)
  obtain ⟨base,hbase,bf,bs⟩ := RecoverySourceClauseList.original_row_run p R Q hr hq x randomness cap pre suffix out hc
  have handH (i : Fin 281) : a.final.heads (clauseSlots i)=
      (RecoverySourceClauseList.cfg 0 cap source address out pre.length count 1).heads i := by
    rw [ah]
    change initialHeads cap source out pre.length count (clauseSlots i)=_
    simp only [initialHeads,clauseSlots,Fin.addCases_left]
    rfl
  have handT (i : Fin 281) : a.final.tapes (clauseSlots i)=
      (RecoverySourceClauseList.cfg 0 cap source address out pre.length count 1).tapes i := by
    rw [atapes]
    by_cases hi : i=159
    · subst i
      change install addressSlots _ _ (addressSlots 31)=_
      rw [install_slot addressSlots address_injective]
      rfl
    · rw [install_other _ _ _ _ (outside_address i hi)]
      exact (initial_other cap source out pre.length count p R Q randomness logCap i hi).trans
        (list_tapes_other cap source address out pre.length count i hi)
  obtain ⟨b,hb,_bc,bsteps,bh,bt,bkeep⟩ := RecoveryFocus.dock clauseSlots clause_injective
    RecoverySourceClauseList.machine _ a.final.heads a.final.tapes _ handH handT base hbase
  have hall:=Composition.run_join first last _ _ _ a b ha hb
  refine ⟨_,hall,?_,?_,?_,?_⟩
  · intro i
    change b.final.heads (clauseSlots i)=_
    rw [bh,bf]
  · intro i
    change b.final.tapes (clauseSlots i)=_
    rw [bt,bf]
  · intro i hi
    change b.final.heads i=0 ∧ b.final.tapes i=_
    rw [(bkeep i hi).1,(bkeep i hi).2,ah,atapes]
    refine ⟨?_,rfl⟩
    have hlarge : 281 ≤ i.val := by
      by_contra hn
      have hil : i.val<281 := by omega
      let j : Fin 281 := ⟨i.val,hil⟩
      exact hi j rfl
    let j : Fin 36 := ⟨i.val-281,by have hil:=i.isLt; omega⟩
    have he : i=j.natAdd 281 := by apply Fin.ext; dsimp [j]; omega
    change initialHeads cap source out pre.length count i=0
    rw [he]
    simp only [initialHeads,Fin.addCases_right]
  · change a.steps+1+b.steps≤budget cap R Q count
    unfold budget
    rw [bsteps]
    dsimp only [count]
    omega

end NearCubicWires.RepairSource.RecoveryPCPFormulaResumeRow
