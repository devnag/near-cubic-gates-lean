import Proof.Amplification.RecoveryPCPFormulaResumeRowsLoop

/-! Execute every original allBitInputs row, including the terminal row
and width zero. The exact original randomWords stream is physically emitted. -/
namespace NearCubicWires.RepairSource.RecoveryPCPFormulaResumeRows
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound SourceInterfaces ProjectionNormalization VerifierDecoding
open RecoveryPCPFormulaResumeRowReset CanonicalRecoveryLanguage
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tailSlots (i : Fin 318) : Fin 319 := i.castAdd 1
theorem tail_injective : Function.Injective tailSlots := by
  intro a b h; exact Fin.ext (congrArg (fun i : Fin 319=>i.val) h)
noncomputable def tailMachine := RecoveryFocus.machine tailSlots RecoveryPCPFormulaResumeRowReusable.machine
noncomputable def machine := Composition.machine loopMachine tailMachine
noncomputable def inputCfg (p : RawProjectionPCP) (R Q cap logCap resetCap total : Nat) (out : List Bool) :=
  RecoveryCalls.restarted machine
    (cfg 0 p R Q 0 cap logCap resetCap out total 1).heads
    (cfg 0 p R Q 0 cap logCap resetCap out total 1).tapes
noncomputable def outputCfg {s : Nat} (q : Fin s) (p : RawProjectionPCP) (R Q cap logCap resetCap total : Nat)
    (out : List Bool) : Configuration 319 s :=
  ⟨q,Fin.addCases (m:=318) (n:=1) (motive:=fun _=>Nat)
      (heads cap (DedupBytes.fields p) out (Codec.clauses p).length) (fun _=>1),
    Fin.addCases (m:=318) (n:=1) (motive:=fun _=>List Bool)
      (input cap (DedupBytes.fields p) out (Codec.clauses p).length p R Q (bitInputOfCode R total) logCap resetCap)
      (fun _=>CompareMachine.word total)⟩
def budget (cap R Q count total : Nat) := total*(bodyBudget cap R Q count+3)+4+
  RecoveryPCPFormulaResumeRowReusable.rowBudget cap R Q count

theorem emitted_append (p : RawProjectionPCP) (R Q : Nat) (hr : p.width≤R) (hq : p.queries≤Q)
    {n : Nat} (x : BitInput n) (k count : Nat) :
    emitted p R Q hr hq x k (count+1)=emitted p R Q hr hq x k count++rowWord p R Q hr hq x (k+count) := by
  simp only [emitted,List.range'_1_concat,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil]

theorem scan_run (p : RawProjectionPCP) (R Q : Nat) (hr : p.width≤R) (hq : p.queries≤Q)
    {n : Nat} (x : BitInput n) (total cap logCap resetCap : Nat) (out : List Bool)
    (hk : total<2^R) (hc : RecoverySourceClauseLoad.uniformBudget Q R≤cap)
    (hl : RecoveryProjectionRowsRewind.batchBudget R Q+2≤logCap)
    (hz : RecoveryPCPFormulaResumeRow.budget cap R Q (Codec.clauses p).length≤resetCap) : ∃ r,
    runFrom machine (budget cap R Q (Codec.clauses p).length total)
      (inputCfg p R Q cap logCap resetCap total out)=some r ∧
      r.final=outputCfg r.final.control p R Q cap logCap resetCap total
        (out++emitted p R Q hr hq x 0 (total+1)) ∧
      r.steps≤budget cap R Q (Codec.clauses p).length total := by
  obtain ⟨a,ha,af,asteps⟩ := loop_run p R Q hr hq x total cap logCap resetCap out hk hc hl hz
  obtain ⟨base,hbase,bh,bt,bs⟩ := RecoveryPCPFormulaResumeRowReusable.row_run p R Q hr hq x
    (bitInputOfCode R total) cap logCap resetCap (out++emitted p R Q hr hq x 0 total) hc hl hz
  obtain ⟨b,hb,_bc,bsteps,bheads,btapes,bkeep⟩ := RecoveryFocus.dock tailSlots tail_injective
    RecoveryPCPFormulaResumeRowReusable.machine _ a.final.heads a.final.tapes _
    (by intro i; rw [af]; simp only [cfg,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,tailSlots,Fin.addCases_left])
    (by intro i; rw [af]; simp only [cfg,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,tailSlots,Fin.addCases_left]) base hbase
  have hall:=Composition.run_join loopMachine tailMachine _ _ _ a b ha hb
  have ht : (total*(bodyBudget cap R Q (Codec.clauses p).length+3)+3)+1+
      RecoveryPCPFormulaResumeRowReusable.rowBudget cap R Q (Codec.clauses p).length=
      budget cap R Q (Codec.clauses p).length total := by unfold budget; omega
  rw [ht] at hall
  have hout : (out++emitted p R Q hr hq x 0 total)++rowWord p R Q hr hq x total=
      out++emitted p R Q hr hq x 0 (total+1) := by
    rw [emitted_append,Nat.zero_add]
    exact List.append_assoc _ _ _
  refine ⟨_,hall,?_,?_⟩
  · apply configuration_ext
    · rfl
    · funext i
      refine Fin.addCases (m:=318) (n:=1) (fun i=>?_) (fun i=>?_) i
      · change b.final.heads (tailSlots i)=_
        rw [bheads,bh]
        change heads _ _ ((out++emitted p R Q hr hq x 0 total)++rowWord p R Q hr hq x total) _ i=_
        rw [hout]
        simp only [outputCfg,Fin.addCases_left]
      · fin_cases i
        change b.final.heads 318=_
        rw [(bkeep 318 (by intro j h; have hv:=congrArg (fun i : Fin 319=>i.val) h; change j.val=318 at hv; have hj:=j.isLt; omega)).1,af]
        rfl
    · funext i
      refine Fin.addCases (m:=318) (n:=1) (fun i=>?_) (fun i=>?_) i
      · change b.final.tapes (tailSlots i)=_
        rw [btapes,bt]
        change input _ _ ((out++emitted p R Q hr hq x 0 total)++rowWord p R Q hr hq x total) _ _ _ _ _ _ _ i=_
        rw [hout]
        simp only [outputCfg,Fin.addCases_left]
      · fin_cases i
        change b.final.tapes 318=_
        rw [(bkeep 318 (by intro j h; have hv:=congrArg (fun i : Fin 319=>i.val) h; change j.val=318 at hv; have hj:=j.isLt; omega)).2,af]
        rfl
  · change a.steps+1+b.steps≤_
    unfold budget
    rw [bsteps]
    omega

theorem stream_flatMap {α : Type} (xs : List α) (f : α→List (List Bool)) :
    FieldList.stream (xs.flatMap f)=xs.flatMap (fun x=>FieldList.stream (f x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons,FieldList.stream,List.map_append,List.flatten_append] at *
    rw [ih]

theorem emitted_all (p : RawProjectionPCP) (R Q : Nat) (hr : p.width≤R) (hq : p.queries≤Q)
    {n : Nat} (x : BitInput n) :
    emitted p R Q hr hq x 0 (2^R)=FieldList.stream
      (RecoveryPCPFormulaResume.randomWords (compactProjectionPCP (p.normalized R Q hr hq)) x) := by
  simp only [emitted,RecoveryPCPFormulaResume.randomWords,allBitInputs,List.flatMap_map,stream_flatMap,
    List.range_eq_range']
  rfl

theorem rows_run (p : RawProjectionPCP) (R Q : Nat) (hr : p.width≤R) (hq : p.queries≤Q)
    {n : Nat} (x : BitInput n) (cap logCap resetCap : Nat) (out : List Bool)
    (hc : RecoverySourceClauseLoad.uniformBudget Q R≤cap)
    (hl : RecoveryProjectionRowsRewind.batchBudget R Q+2≤logCap)
    (hz : RecoveryPCPFormulaResumeRow.budget cap R Q (Codec.clauses p).length≤resetCap) : ∃ r,
    runFrom machine (budget cap R Q (Codec.clauses p).length (2^R-1))
      (inputCfg p R Q cap logCap resetCap (2^R-1) out)=some r ∧
      r.final=outputCfg r.final.control p R Q cap logCap resetCap (2^R-1)
        (out++FieldList.stream (RecoveryPCPFormulaResume.randomWords
          (compactProjectionPCP (p.normalized R Q hr hq)) x)) ∧
      r.steps≤budget cap R Q (Codec.clauses p).length (2^R-1) := by
  have hp : 0<2^R := Nat.two_pow_pos R
  have he : 2^R-1+1=2^R := by omega
  obtain ⟨r,hrun,rf,rs⟩ := scan_run p R Q hr hq x (2^R-1) cap logCap resetCap out (by omega) hc hl hz
  rw [he,emitted_all] at rf
  exact ⟨r,hrun,rf,rs⟩

end NearCubicWires.RepairSource.RecoveryPCPFormulaResumeRows
