import Proof.Amplification.RecoveryPCPFormulaResumeSparse

/-! The real row-loop entry has just nine potentially nonblank data tapes.
All remaining initial backing is implicit blank space, by checked inverse
padding; no unary driver or source byte is supplied by that observation. -/
namespace NearCubicWires.RepairSource.RecoveryPCPFormulaResumeSerialize
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound SourceInterfaces ProjectionNormalization VerifierDecoding
open RecoveryPCPFormulaResumeRow CanonicalRecoveryLanguage
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def rowData (p : RawProjectionPCP) (R Q cap : Nat) (i : Fin 319) : List Bool :=
  if i.val=272 then DedupBytes.fields p else
  if i.val=278 then List.replicate cap true else
  if i.val=280 then CompareMachine.word (Codec.clauses p).length else
  if i.val=309 then QueryBytes.framedCodes (normalizedRows p R Q).flatten else
  if i.val=310 then frame (List.ofFn (bitInputOfCode R 0)) else
  if i.val=312 then List.replicate (RecoveryProjectionRows.capacity R) true else
  if i.val=314 then CompareMachine.word R else
  if i.val=315 then CompareMachine.word Q else
  if i.val=318 then CompareMachine.word (2^R-1) else []

theorem reuse_data (p : RawProjectionPCP) (R Q cap : Nat) (i : Fin 280) :
    omitBlank (RecoverySourceClauseReuse.data (DedupBytes.fields p) [] [] cap i)=
      omitBlank (rowData p R Q cap (i.castAdd 39)) := by
  by_cases h272 : i.val=272
  · have he : i=272 := Fin.ext h272
    subst i; rfl
  by_cases h278 : i.val=278
  · have he : i=278 := Fin.ext h278
    subst i; rfl
  have hi:=i.isLt
  have h280 : i.val≠280 := by omega
  have h309 : i.val≠309 := by omega
  have h310 : i.val≠310 := by omega
  have h312 : i.val≠312 := by omega
  have h314 : i.val≠314 := by omega
  have h315 : i.val≠315 := by omega
  have h318 : i.val≠318 := by omega
  simp only [RecoverySourceClauseReuse.data,rowData,Fin.val_castAdd,h272,h278,h280,h309,h310,h312,h314,h315,h318,ite_false]
  split_ifs <;> first | rfl | (rw [omit_blank];rfl)

theorem batch_data (p : RawProjectionPCP) (R Q cap logCap : Nat) (j : Fin 37) :
    omitBlank (batchInput p R Q (bitInputOfCode R 0) logCap j)=
      omitBlank (rowData p R Q cap ((addressSlots j).castAdd 2)) := by
  fin_cases j
  · change omitBlank (List.replicate _ false)=omitBlank []
    rw [omit_blank]
    rfl
  · change omitBlank (List.replicate _ false)=omitBlank []
    rw [omit_blank]
    rfl
  · change omitBlank (List.replicate _ false)=omitBlank []
    rw [omit_blank]
    rfl
  · change omitBlank (List.replicate _ false)=omitBlank []
    rw [omit_blank]
    rfl
  · change omitBlank (List.replicate _ false)=omitBlank []
    rw [omit_blank]
    rfl
  · change omitBlank (List.replicate _ false)=omitBlank []
    rw [omit_blank]
    rfl
  · change omitBlank (List.replicate _ false)=omitBlank []
    rw [omit_blank]
    rfl
  · change omitBlank (List.replicate _ false)=omitBlank []
    rw [omit_blank]
    rfl
  · change omitBlank (List.replicate _ false)=omitBlank []
    rw [omit_blank]
    rfl
  · change omitBlank (List.replicate _ false)=omitBlank []
    rw [omit_blank]
    rfl
  · change omitBlank (List.replicate _ false)=omitBlank []
    rw [omit_blank]
    rfl
  · change omitBlank (List.replicate _ false)=omitBlank []
    rw [omit_blank]
    rfl
  · change omitBlank (List.replicate _ false)=omitBlank []
    rw [omit_blank]
    rfl
  · change omitBlank (List.replicate _ false)=omitBlank []
    rw [omit_blank]
    rfl
  · change omitBlank (List.replicate _ false)=omitBlank []
    rw [omit_blank]
    rfl
  · change omitBlank (List.replicate _ false)=omitBlank []
    rw [omit_blank]
    rfl
  · change omitBlank (List.replicate _ false)=omitBlank []
    rw [omit_blank]
    rfl
  · change omitBlank (List.replicate _ false)=omitBlank []
    rw [omit_blank]
    rfl
  · change omitBlank (List.replicate _ false)=omitBlank []
    rw [omit_blank]
    rfl
  · change omitBlank (List.replicate _ false)=omitBlank []
    rw [omit_blank]
    rfl
  · change omitBlank (List.replicate _ false)=omitBlank []
    rw [omit_blank]
    rfl
  · change omitBlank (List.replicate _ false)=omitBlank []
    rw [omit_blank]
    rfl
  · change omitBlank (List.replicate _ false)=omitBlank []
    rw [omit_blank]
    rfl
  · change omitBlank (List.replicate _ false)=omitBlank []
    rw [omit_blank]
    rfl
  · change omitBlank (List.replicate _ false)=omitBlank []
    rw [omit_blank]
    rfl
  · change omitBlank (List.replicate _ false)=omitBlank []
    rw [omit_blank]
    rfl
  · change omitBlank (List.replicate _ false)=omitBlank []
    rw [omit_blank]
    rfl
  · change omitBlank (List.replicate _ false)=omitBlank []
    rw [omit_blank]
    rfl
  · rfl
  · change omitBlank (frame (List.ofFn (bitInputOfCode R 0))++[])=omitBlank (frame (List.ofFn (bitInputOfCode R 0)))
    rw [List.append_nil]
  · change omitBlank (List.replicate _ false)=omitBlank []
    rw [omit_blank]
    rfl
  · rfl
  · rfl
  · change omitBlank (List.replicate _ false)=omitBlank []
    rw [omit_blank]
    rfl
  · rfl
  · rfl
  · change omitBlank (List.replicate _ false)=omitBlank []
    rw [omit_blank]
    rfl

theorem row_data (p : RawProjectionPCP) (R Q cap logCap resetCap : Nat) (i : Fin 319) :
    omitBlank ((RecoveryPCPFormulaResumeRows.inputCfg p R Q cap logCap resetCap (2^R-1) []).tapes i)=
      omitBlank (rowData p R Q cap i) := by
  refine Fin.addCases (m:=318) (n:=1) (fun i=>?_) (fun i=>?_) i
  · refine Fin.addCases (m:=317) (n:=1) (fun i=>?_) (fun i=>?_) i
    · simp only [RecoveryPCPFormulaResumeRows.inputCfg,RecoveryCalls.restarted,
        RecoveryPCPFormulaResumeRows.cfg,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,
        RecoveryPCPFormulaResumeRowReset.input,RecoveryPCPFormulaResumeRowReset.tapes,Fin.addCases_left]
      by_cases hi : i.val<281
      · let j : Fin 281 := ⟨i.val,hi⟩
        have he : clauseSlots j=i := Fin.ext rfl
        rw [←he]
        by_cases hj : j=159
        · rw [hj]
          change omitBlank (ZeroPadding.pad cap (initialTapes cap (DedupBytes.fields p) [] 0
            (Codec.clauses p).length p R Q (bitInputOfCode R 0) logCap (addressSlots 31)))=omitBlank []
          rw [initialTapes,install_slot addressSlots address_injective]
          change omitBlank (List.replicate cap false)=omitBlank []
          rw [omit_blank]
          rfl
        · have hn : clauseSlots j≠159 := by
            intro h; exact hj (Fin.ext (congrArg (fun i : Fin 317=>i.val) h))
          rw [show RecoveryPCPFormulaResumeRowReset.addressCaps cap (clauseSlots j)=0 by
            simp only [RecoveryPCPFormulaResumeRowReset.addressCaps,hn,ite_false],ZeroPadding.pad_zero,
            initial_other _ _ _ _ _ _ _ _ _ _ j hj]
          change omitBlank ((before cap (DedupBytes.fields p) [] 0 (Codec.clauses p).length).tapes j)=
            omitBlank (rowData p R Q cap ((clauseSlots j).castAdd 2))
          refine Fin.addCases (m:=280) (n:=1) (fun k=>?_) (fun k=>?_) j
          · have hk : ((k.castAdd 1).castAdd 36).castAdd 2=k.castAdd 39 := Fin.ext rfl
            simpa only [before,RecoverySourceClauseList.cfg,RepeatMachine.cfg,controlConfig,
              TapeEmbedding.config,Fin.addCases_left,clauseSlots,hk] using reuse_data p R Q cap k
          · fin_cases k; rfl
      · have hlarge : (281 : Nat)≤(i : Fin 317).val := by omega
        have hn : i≠159 := by intro h; subst i; omega
        rw [show RecoveryPCPFormulaResumeRowReset.addressCaps cap i=0 by
          simp only [RecoveryPCPFormulaResumeRowReset.addressCaps,hn,ite_false],ZeroPadding.pad_zero]
        obtain ⟨j,hj⟩ := address_coverage i hlarge
        rw [←hj,initialTapes,install_slot addressSlots address_injective]
        exact batch_data p R Q cap logCap j
    · fin_cases i
      change omitBlank (List.replicate resetCap false)=omitBlank []
      rw [omit_blank]
      rfl
  · fin_cases i; rfl

end NearCubicWires.RepairSource.RecoveryPCPFormulaResumeSerialize
