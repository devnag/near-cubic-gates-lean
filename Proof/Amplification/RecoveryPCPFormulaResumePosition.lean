import Proof.Amplification.RecoveryPCPFormulaResumeForward

/-! Pay the two repetition-driver head moves at the original formula
entry, so the complete producer starts from ordinary zero heads. -/
namespace NearCubicWires.RepairSource.RecoveryPCPFormulaResumePrefix
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound SourceInterfaces ProjectionNormalization VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def positionHeads (i : Fin 580) := if i.val=280 ∨ i.val=318 then 1 else 0
def position : Machine 580 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==1
  rule := fun q _=>if q=0 then some
    ⟨1,fun _=>none,fun i=>if i.val=280 ∨ i.val=318 then .right else .stay⟩ else none

theorem position_step (data : Fin 580→List Bool) :
    step position (initialConfiguration position data)=some ⟨1,positionHeads,data⟩ := by
  simp only [step,position,initialConfiguration,ite_true,Option.map_some]
  congr 1
  apply configuration_ext
  · rfl
  · funext i
    simp only [applyAction,positionHeads]
    split_ifs <;> rfl
  · funext i
    simp only [applyAction]

theorem initial_heads (p : RawProjectionPCP) (R Q cap logCap resetCap : Nat) :
    heads p R Q cap logCap resetCap=positionHeads := by
  funext i
  refine Fin.addCases (m:=319) (n:=261) (fun i=>?_) (fun i=>?_) i
  · refine Fin.addCases (m:=318) (n:=1) (fun i=>?_) (fun i=>?_) i
    · refine Fin.addCases (m:=317) (n:=1) (fun i=>?_) (fun i=>?_) i
      · refine Fin.addCases (m:=281) (n:=36) (fun i=>?_) (fun i=>?_) i
        · refine Fin.addCases (m:=280) (n:=1) (fun i=>?_) (fun i=>?_) i
          · have hi:=i.isLt
            simp only [heads,RecoveryPCPFormulaResumeRows.inputCfg,RecoveryCalls.restarted,
              RecoveryPCPFormulaResumeRows.cfg,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,
              RecoveryPCPFormulaResumeRowReset.heads,RecoveryPCPFormulaResumeRow.initialHeads,
              RecoveryPCPFormulaResumeRow.before,RecoverySourceClauseList.cfg,Fin.addCases_left,
              RecoverySourceClauseReuse.heads,List.length_nil,ite_self,positionHeads,Fin.val_castAdd]
            rw [if_neg (by omega)]
          · fin_cases i; rfl
        · have hi:=i.isLt
          simp only [heads,RecoveryPCPFormulaResumeRows.inputCfg,RecoveryCalls.restarted,
            RecoveryPCPFormulaResumeRows.cfg,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,
            RecoveryPCPFormulaResumeRowReset.heads,RecoveryPCPFormulaResumeRow.initialHeads,
            Fin.addCases_left,Fin.addCases_right,positionHeads,Fin.val_castAdd,Fin.val_natAdd]
          rw [if_neg (by omega)]
      · fin_cases i; rfl
    · fin_cases i; rfl
  · have hi:=i.isLt
    simp only [heads,Fin.addCases_right,positionHeads,Fin.val_natAdd]
    rw [if_neg (by omega)]

noncomputable def rawMachine := Composition.machine position machine
def rawBudget (cap R Q count : Nat) := budget cap R Q count+2

theorem raw_run (p : RawProjectionPCP) (R Q : Nat) (hr : p.width≤R) (hq : p.queries≤Q)
    {n : Nat} (x : BitInput n) (cap logCap resetCap : Nat)
    (hc : RecoverySourceClauseLoad.uniformBudget Q R≤cap)
    (hl : RecoveryProjectionRowsRewind.batchBudget R Q+2≤logCap)
    (hz : RecoveryPCPFormulaResumeRow.budget cap R Q (Codec.clauses p).length≤resetCap) : ∃ r,
    run rawMachine (rawBudget cap R Q (Codec.clauses p).length) (input p R Q cap logCap resetCap)=some r ∧
      r.final.tapes 276=FieldList.stream
        (RecoveryPCPFormulaResume.words (compactProjectionPCP (p.normalized R Q hr hq)) x) ∧
      r.final.heads 276=(FieldList.stream
        (RecoveryPCPFormulaResume.words (compactProjectionPCP (p.normalized R Q hr hq)) x)).length ∧
      r.steps≤rawBudget cap R Q (Codec.clauses p).length := by
  obtain ⟨first,hfirst,ff,fs⟩ := (Timed.single (by rfl)
    (position_step (input p R Q cap logCap resetCap))).run (by rfl)
  obtain ⟨last,hlast,lt,lh,ls⟩ := prefix_run p R Q hr hq x cap logCap resetCap hc hl hz
  have he : Composition.restart first.final machine.start=
      (⟨machine.start,heads p R Q cap logCap resetCap,input p R Q cap logCap resetCap⟩ : Configuration 580 _) := by
    rw [ff,initial_heads]
    rfl
  rw [←he] at hlast
  have hall:=Composition.run_join position machine _ _ _ first last hfirst hlast
  have hb : 1+1+budget cap R Q (Codec.clauses p).length=rawBudget cap R Q (Codec.clauses p).length := by
    unfold rawBudget; omega
  rw [hb] at hall
  refine ⟨_,hall,lt,lh,?_⟩
  change first.steps+1+last.steps≤_
  unfold rawBudget
  omega

theorem position_forward : CursorRestore.NoLeft position 276 := by
  intro q bits a ha
  fin_cases q <;> simp only [position] at ha
  · cases ha; decide
  · contradiction

end NearCubicWires.RepairSource.RecoveryPCPFormulaResumePrefix
