import Proof.Amplification.RecoveryPCPFormulaResumeRows

/-! The all-row producer changes its formula input only at the live output
port. These exact tape identities dock the cold prefix into the real loop. -/
namespace NearCubicWires.RepairSource.RecoveryPCPFormulaResumeRows
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound SourceInterfaces ProjectionNormalization VerifierDecoding
open RecoveryPCPFormulaResumeRow
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem before_tapes_output (cap : Nat) (source out : List Bool) (count : Nat) (i : Fin 281) :
    (before cap source out 0 count).tapes i=
      if i.val=276 then out else (before cap source [] 0 count).tapes i := by
  refine Fin.addCases (m:=280) (n:=1) (fun i=>?_) (fun i=>?_) i
  · by_cases hi : i.val=276
    · have he : i=276 := Fin.ext hi
      subst i; rfl
    · simp only [before,RecoverySourceClauseList.cfg,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,
        Fin.addCases_left,RecoverySourceClauseReuse.data,Fin.val_castAdd,hi,ite_false]
  · fin_cases i; rfl

theorem initial_tapes_output (cap : Nat) (source out : List Bool) (count : Nat)
    (p : RawProjectionPCP) (R Q : Nat) (randomness : BitInput R) (logCap : Nat) (i : Fin 317) :
    initialTapes cap source out 0 count p R Q randomness logCap i=
      if i.val=276 then out else initialTapes cap source [] 0 count p R Q randomness logCap i := by
  refine Fin.addCases (m:=281) (n:=36) (fun j=>?_) (fun j=>?_) i
  · change initialTapes _ _ _ _ _ _ _ _ _ _ (clauseSlots j)=_
    by_cases hj : j=159
    · rw [hj]
      change initialTapes _ _ _ _ _ _ _ _ _ _ (addressSlots 31)=
        initialTapes _ _ [] _ _ _ _ _ _ _ (addressSlots 31)
      simp only [initialTapes,install_slot addressSlots address_injective]
    · rw [initial_other _ _ _ _ _ _ _ _ _ _ j hj]
      rw [before_tapes_output]
      change (if j.val=276 then out else _)=if j.val=276 then out else _
      split_ifs
      · rfl
      · exact (initial_other _ _ _ _ _ _ _ _ _ _ j hj).symm
  · obtain ⟨k,hk⟩ := address_coverage (j.natAdd 281) (by change 281≤281+j.val; omega)
    have hn : (j.natAdd 281 : Fin 317).val≠276 := by change 281+j.val≠276; omega
    rw [if_neg hn,←hk]
    simp only [initialTapes,install_slot addressSlots address_injective]

theorem input_heads_output (p : RawProjectionPCP) (R Q cap logCap resetCap total : Nat)
    (out : List Bool) (i : Fin 319) :
    (inputCfg p R Q cap logCap resetCap total out).heads i=
      if i.val=276 then out.length else (inputCfg p R Q cap logCap resetCap total []).heads i := by
  refine Fin.addCases (m:=318) (n:=1) (fun i=>?_) (fun i=>?_) i
  · refine Fin.addCases (m:=317) (n:=1) (fun i=>?_) (fun i=>?_) i
    · refine Fin.addCases (m:=281) (n:=36) (fun i=>?_) (fun i=>?_) i
      · refine Fin.addCases (m:=280) (n:=1) (fun i=>?_) (fun i=>?_) i
        · by_cases hi : i.val=276
          · have he : i=276 := Fin.ext hi
            subst i; rfl
          · simp only [inputCfg,RecoveryCalls.restarted,cfg,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,
              RecoveryPCPFormulaResumeRowReset.heads,initialHeads,before,RecoverySourceClauseList.cfg,
              Fin.addCases_left,RecoverySourceClauseReuse.heads,Fin.val_castAdd,hi,ite_false]
        · fin_cases i; rfl
      · have hi:=i.isLt
        simp only [inputCfg,RecoveryCalls.restarted,cfg,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,
          RecoveryPCPFormulaResumeRowReset.heads,initialHeads,Fin.addCases_left,Fin.addCases_right,
          Fin.val_castAdd,Fin.val_natAdd]
        rw [if_neg (by omega)]
    · fin_cases i; rfl
  · fin_cases i; rfl

theorem input_tapes_output (p : RawProjectionPCP) (R Q cap logCap resetCap total : Nat)
    (out : List Bool) (i : Fin 319) :
    (inputCfg p R Q cap logCap resetCap total out).tapes i=
      if i.val=276 then out else (inputCfg p R Q cap logCap resetCap total []).tapes i := by
  refine Fin.addCases (m:=318) (n:=1) (fun i=>?_) (fun i=>?_) i
  · refine Fin.addCases (m:=317) (n:=1) (fun i=>?_) (fun i=>?_) i
    · simp only [inputCfg,RecoveryCalls.restarted,cfg,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,
        RecoveryPCPFormulaResumeRowReset.input,RecoveryPCPFormulaResumeRowReset.tapes,Fin.addCases_left,
        Fin.val_castAdd]
      rw [initial_tapes_output]
      split_ifs with hi
      · have he : i=276 := Fin.ext hi
        subst i
        exact ZeroPadding.pad_zero _
      · rfl
    · fin_cases i; rfl
  · fin_cases i; rfl

theorem input_output (p : RawProjectionPCP) (R Q cap logCap resetCap total : Nat) (out : List Bool) :
    (inputCfg p R Q cap logCap resetCap total out).heads 276=out.length ∧
    (inputCfg p R Q cap logCap resetCap total out).tapes 276=out := by
  constructor
  · exact input_heads_output p R Q cap logCap resetCap total out 276
  · exact input_tapes_output p R Q cap logCap resetCap total out 276

end NearCubicWires.RepairSource.RecoveryPCPFormulaResumeRows
