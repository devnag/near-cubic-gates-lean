import Proof.Amplification.RecoveryPCPFormulaResumeRow

/-! The complete row has only two changing data tapes: the appended formula
and the current address batch. All source and arithmetic banks are reusable. -/
namespace NearCubicWires.RepairSource.RecoveryPCPFormulaResumeRow
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound SourceInterfaces ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def batchOutput (p : RawProjectionPCP) (R Q : Nat) (randomness : BitInput R)
    (logCap : Nat) (address : List Bool) : Fin 37→List Bool :=
  Fin.addCases (m:=36) (n:=1) (motive:=fun _=>List Bool)
    (RecoveryProjectionRows.cfg 3 (RecoveryProjectionRows.capacity R) R
      (QueryBytes.framedCodes (normalizedRows p R Q).flatten) (List.ofFn randomness) [] address
      (QueryBytes.framedCodes (normalizedRows p R Q).flatten).length Q 1).tapes
    (fun _=>List.replicate logCap false)

theorem batch_output (p : RawProjectionPCP) (R Q : Nat) (randomness : BitInput R)
    (logCap : Nat) (address : List Bool) :
    batchOutput p R Q randomness logCap address=Function.update (batchInput p R Q randomness logCap) 31 address := by
  funext i
  fin_cases i <;> rfl

theorem address_coverage (i : Fin 317) (hi : 281 ≤ i.val) : ∃ j,addressSlots j=i := by
  have hlt:=i.isLt
  by_cases h : i.val<312
  · refine ⟨⟨i.val-281,by omega⟩,?_⟩
    apply Fin.ext
    dsimp [addressSlots]
    split_ifs <;> omega
  · refine ⟨⟨i.val-280,by omega⟩,?_⟩
    apply Fin.ext
    dsimp [addressSlots]
    split_ifs <;> omega

theorem state_run (p : RawProjectionPCP) (R Q : Nat) (hr : p.width≤R) (hq : p.queries≤Q)
    {n : Nat} (x : BitInput n) (randomness : BitInput R) (cap logCap : Nat) (out : List Bool)
    (hc : RecoverySourceClauseLoad.uniformBudget Q R≤cap)
    (hl : RecoveryProjectionRowsRewind.batchBudget R Q+2≤logCap) : ∃ r,
    runFrom machine (budget cap R Q (Codec.clauses p).length)
      ⟨machine.start,initialHeads cap (DedupBytes.fields p) out 0 (Codec.clauses p).length,
        initialTapes cap (DedupBytes.fields p) out 0 (Codec.clauses p).length p R Q randomness logCap⟩=some r ∧
      r.final.heads=initialHeads cap (DedupBytes.fields p)
        (out++FieldList.stream (RecoveryPCPFormulaResume.rowWords
          (compactProjectionPCP (p.normalized R Q hr hq)) x randomness))
        (DedupBytes.fields p).length (Codec.clauses p).length ∧
      r.final.tapes=Function.update
        (initialTapes cap (DedupBytes.fields p)
          (out++FieldList.stream (RecoveryPCPFormulaResume.rowWords
            (compactProjectionPCP (p.normalized R Q hr hq)) x randomness))
          0 (Codec.clauses p).length p R Q randomness logCap) 159
        (FieldList.stream (RecoveryProjectionRows.addressFields p R Q hr hq x randomness)) ∧
      r.steps≤budget cap R Q (Codec.clauses p).length := by
  obtain ⟨r,hrun,rh,rt,rkeep,rs⟩ := row_run p R Q hr hq x randomness cap logCap [] [] out hc hl
  simp only [List.nil_append,List.append_nil,List.length_nil] at hrun rh rt rkeep
  refine ⟨r,hrun,?_,?_,rs⟩
  · funext i
    by_cases hi : i.val<281
    · let j : Fin 281 := ⟨i.val,hi⟩
      have he : clauseSlots j=i := Fin.ext rfl
      rw [←he,rh]
      simp only [initialHeads,clauseSlots,Fin.addCases_left]
      rfl
    · have hout : ∀ j,clauseSlots j≠i := by
        intro j h
        have hv:=congrArg (fun k : Fin 317=>k.val) h
        change j.val=i.val at hv
        have hj:=j.isLt; omega
      rw [(rkeep i hout).1]
      let j : Fin 36 := ⟨i.val-281,by have hil:=i.isLt; omega⟩
      have he : i=j.natAdd 281 := by apply Fin.ext; dsimp [j]; omega
      rw [he]
      simp only [initialHeads,Fin.addCases_right]
  · funext i
    by_cases hi : i.val<281
    · let j : Fin 281 := ⟨i.val,hi⟩
      have he : clauseSlots j=i := Fin.ext rfl
      rw [←he,rt]
      by_cases hj : j=159
      · rw [hj]; rfl
      · have hn : clauseSlots j≠159 := by
          intro h
          apply hj
          exact Fin.ext (congrArg (fun k : Fin 317=>k.val) h)
        rw [Function.update_of_ne hn,initial_other _ _ _ _ _ _ _ _ _ _ j hj]
        exact (list_tapes_other cap (DedupBytes.fields p) _ _ 0 (Codec.clauses p).length j hj).symm
    · have hlarge : 281 ≤ i.val := by omega
      have hn159 : i≠159 := by intro h; subst i; omega
      have hout : ∀ j,clauseSlots j≠i := by
        intro j h
        have hv:=congrArg (fun k : Fin 317=>k.val) h
        change j.val=i.val at hv
        have hj:=j.isLt; omega
      rw [(rkeep i hout).2,Function.update_of_ne hn159]
      obtain ⟨j,hj⟩ := address_coverage i hlarge
      rw [←hj,install_slot addressSlots address_injective]
      change batchOutput p R Q randomness logCap _ j=initialTapes _ _ _ _ _ _ _ _ _ _ (addressSlots j)
      rw [initialTapes,install_slot addressSlots address_injective,batch_output]
      have hn31 : j≠31 := by intro he; subst j; have hv:=congrArg Fin.val hj; change 159=i.val at hv; omega
      rw [Function.update_of_ne hn31]

end NearCubicWires.RepairSource.RecoveryPCPFormulaResumeRow
