import Proof.Amplification.RecoveryPCPFormulaResumeRowsBody

/-! The actual binary randomness loop executes complete original PCP rows,
retaining the formula append cursor, original source and reusable banks. -/
namespace NearCubicWires.RepairSource.RecoveryPCPFormulaResumeRows
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound SourceInterfaces ProjectionNormalization VerifierDecoding
open RecoveryPCPFormulaResumeRowReset CanonicalRecoveryLanguage
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

private theorem cfg_data {t s : Nat} (phase : Fin 5) (c d : Configuration t s) (total driver : Nat)
    (hh : c.heads=d.heads) (ht : c.tapes=d.tapes) :
    RepeatMachine.cfg phase c total driver=RepeatMachine.cfg phase d total driver := by
  apply configuration_ext
  · rfl
  · simp only [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,hh]
  · simp only [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,ht]

private theorem iteration_data {t s fuel : Nat} (body : Machine t s)
    (c d : Configuration t s) (total pos : Nat) (r : ExecutionReceipt t s)
    (hc : c.control=body.start) (hp : pos<total) (hr : runFrom body fuel c=some r)
    (hh : r.final.heads=d.heads) (ht : r.final.tapes=d.tapes) :
    Timed (RepeatMachine.machine body (fun _ _=>true)) (r.steps+2)
      (RepeatMachine.cfg 0 c total (pos+1)) (RepeatMachine.cfg 0 d total (pos+2)) := by
  have h := RepeatMachine.iteration body (fun _ _=>true) c total pos r hc hp hr
  change Timed _ _ _ (RepeatMachine.cfg 0 r.final total (pos+2)) at h
  rw [cfg_data 0 r.final d total (pos+2) hh ht] at h
  exact h

private theorem exhaust_run {t s : Nat} (body : Machine t s) (c : Configuration t s) (total : Nat) :
    ∃ r,runFrom (RepeatMachine.machine body (fun _ _=>true)) (total+3)
      (RepeatMachine.cfg 0 c total (total+1))=some r ∧
      r.final=RepeatMachine.cfg 3 c total 1 ∧ r.steps=total+3 :=
  (RepeatMachine.exhaust body (fun _ _=>true) c total).run
    (by simp [RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])

noncomputable def loopMachine := RepeatMachine.machine bodyMachine (fun _ _=>true)
noncomputable def cfg (phase : Fin 5) (p : RawProjectionPCP) (R Q k cap logCap resetCap : Nat)
    (out : List Bool) (total driver : Nat) := RepeatMachine.cfg phase
      (⟨bodyMachine.start,heads cap (DedupBytes.fields p) out (Codec.clauses p).length,
        input cap (DedupBytes.fields p) out (Codec.clauses p).length p R Q (bitInputOfCode R k) logCap resetCap⟩ : Configuration 318 _)
      total driver
noncomputable def emitted (p : RawProjectionPCP) (R Q : Nat) (hr : p.width≤R) (hq : p.queries≤Q)
    {n : Nat} (x : BitInput n) (k count : Nat) := (List.range' k count).flatMap (rowWord p R Q hr hq x)

theorem remaining_run (p : RawProjectionPCP) (R Q : Nat) (hr : p.width≤R) (hq : p.queries≤Q)
    {n : Nat} (x : BitInput n) (remaining k cap logCap resetCap : Nat) (out : List Bool)
    (total pos : Nat) (hn : pos+remaining=total) (hk : k+remaining<2^R)
    (hc : RecoverySourceClauseLoad.uniformBudget Q R≤cap)
    (hl : RecoveryProjectionRowsRewind.batchBudget R Q+2≤logCap)
    (hz : RecoveryPCPFormulaResumeRow.budget cap R Q (Codec.clauses p).length≤resetCap) : ∃ r,
    runFrom loopMachine (remaining*(bodyBudget cap R Q (Codec.clauses p).length+2)+total+3)
      (cfg 0 p R Q k cap logCap resetCap out total (pos+1))=some r ∧
      r.final=cfg 3 p R Q (k+remaining) cap logCap resetCap
        (out++emitted p R Q hr hq x k remaining) total 1 ∧
      r.steps≤remaining*(bodyBudget cap R Q (Codec.clauses p).length+2)+total+3 := by
  induction remaining generalizing k out pos with
  | zero =>
    have hp : pos=total := by omega
    subst pos
    obtain ⟨r,hrun,rf,rs⟩ := exhaust_run bodyMachine
      (⟨bodyMachine.start,heads cap (DedupBytes.fields p) out (Codec.clauses p).length,
        input cap (DedupBytes.fields p) out (Codec.clauses p).length p R Q (bitInputOfCode R k) logCap resetCap⟩ : Configuration 318 _) total
    refine ⟨r,?_,?_,?_⟩
    · simpa only [loopMachine,cfg,Nat.zero_mul,Nat.zero_add] using hrun
    · simpa only [cfg,emitted,List.range'_zero,List.flatMap_nil,List.append_nil,Nat.add_zero] using rf
    · simpa only [Nat.zero_mul,Nat.zero_add] using rs.le
  | succ remaining ih =>
    obtain ⟨body,hbody,bh,bt,bs⟩ := body_run p R Q hr hq x k cap logCap resetCap out (by omega) hc hl hz
    let next := (⟨bodyMachine.start,
      heads cap (DedupBytes.fields p) (out++rowWord p R Q hr hq x k) (Codec.clauses p).length,
      input cap (DedupBytes.fields p) (out++rowWord p R Q hr hq x k) (Codec.clauses p).length
        p R Q (bitInputOfCode R (k+1)) logCap resetCap⟩ : Configuration 318 _)
    have hstep:=iteration_data bodyMachine _ next total pos body rfl (by omega) hbody bh bt
    change Timed loopMachine (body.steps+2)
      (cfg 0 p R Q k cap logCap resetCap out total (pos+1))
      (cfg 0 p R Q (k+1) cap logCap resetCap (out++rowWord p R Q hr hq x k) total (pos+2)) at hstep
    obtain ⟨rest,hrest,rf,rs⟩ := ih (k+1) (out++rowWord p R Q hr hq x k) (pos+1) (by omega) (by omega)
    have hmid : pos+2=(pos+1)+1 := by omega
    rw [hmid] at hstep
    rcases hstep with ⟨space,hprefix⟩
    obtain ⟨result,hresult,hf,hs,_⟩ := hprefix.followedBy rest hrest
    have hbound : (body.steps+2)+(remaining*(bodyBudget cap R Q (Codec.clauses p).length+2)+total+3)≤
        (remaining+1)*(bodyBudget cap R Q (Codec.clauses p).length+2)+total+3 := by
      rw [Nat.add_mul,Nat.one_mul]
      omega
    have hmore:=runFrom_moreFuel loopMachine _
      ((remaining+1)*(bodyBudget cap R Q (Codec.clauses p).length+2)+total+3-
        ((body.steps+2)+(remaining*(bodyBudget cap R Q (Codec.clauses p).length+2)+total+3))) _ result hresult
    rw [Nat.add_sub_of_le hbound] at hmore
    refine ⟨result,hmore,?_,?_⟩
    · rw [hf,rf]
      simp only [emitted,List.range'_succ,List.flatMap_cons,List.append_assoc,Nat.add_assoc,Nat.add_comm 1 remaining]
    · rw [hs]
      omega

theorem loop_run (p : RawProjectionPCP) (R Q : Nat) (hr : p.width≤R) (hq : p.queries≤Q)
    {n : Nat} (x : BitInput n) (total cap logCap resetCap : Nat) (out : List Bool)
    (hk : total<2^R) (hc : RecoverySourceClauseLoad.uniformBudget Q R≤cap)
    (hl : RecoveryProjectionRowsRewind.batchBudget R Q+2≤logCap)
    (hz : RecoveryPCPFormulaResumeRow.budget cap R Q (Codec.clauses p).length≤resetCap) : ∃ r,
    runFrom loopMachine (total*(bodyBudget cap R Q (Codec.clauses p).length+3)+3)
      (cfg 0 p R Q 0 cap logCap resetCap out total 1)=some r ∧
      r.final=cfg 3 p R Q total cap logCap resetCap (out++emitted p R Q hr hq x 0 total) total 1 ∧
      r.steps≤total*(bodyBudget cap R Q (Codec.clauses p).length+3)+3 := by
  have h:=remaining_run p R Q hr hq x total 0 cap logCap resetCap out total 0 (by omega) (by simpa using hk) hc hl hz
  have ht : total*(bodyBudget cap R Q (Codec.clauses p).length+2)+total+3=
      total*(bodyBudget cap R Q (Codec.clauses p).length+3)+3 := by ring
  simpa only [ht,Nat.zero_add] using h

end NearCubicWires.RepairSource.RecoveryPCPFormulaResumeRows
