import Proof.Amplification.RecoveryPCPFormulaResumeRowState
import Proof.MachineModel.OrdinaryMaskedReset

/-! Pay the original-clause source rewind while retaining the formula
append cursor. The address tape has reusable false backing from entry. -/
namespace NearCubicWires.RepairSource.RecoveryPCPFormulaResumeRowReset
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound SourceInterfaces ProjectionNormalization
open RecoveryPCPFormulaResumeRow
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def selected (i : Fin 317) : Bool := decide (i=272)
def addressCaps (cap : Nat) (i : Fin 317) := if i=159 then cap else 0
noncomputable def machine := MaskedReset.machine RecoveryPCPFormulaResumeRow.machine selected
noncomputable def tapes (cap : Nat) (source out : List Bool) (count : Nat)
    (p : RawProjectionPCP) (R Q : Nat) (randomness : BitInput R) (logCap : Nat) : Fin 317→List Bool :=
  fun i=>ZeroPadding.pad (addressCaps cap i)
    (initialTapes cap source out 0 count p R Q randomness logCap i)
noncomputable def heads (cap : Nat) (source out : List Bool) (count : Nat) : Fin 318→Nat :=
  Fin.addCases (m:=317) (n:=1) (motive:=fun _=>Nat)
    (initialHeads cap source out 0 count) (fun _=>0)
noncomputable def input (cap : Nat) (source out : List Bool) (count : Nat)
    (p : RawProjectionPCP) (R Q : Nat) (randomness : BitInput R) (logCap resetCap : Nat) : Fin 318→List Bool :=
  Fin.addCases (m:=317) (n:=1) (motive:=fun _=>List Bool)
    (tapes cap source out count p R Q randomness logCap) (fun _=>List.replicate resetCap false)

theorem head_reset (cap : Nat) (source out : List Bool) (count pos : Nat) :
    (fun i=>if selected i then 0 else initialHeads cap source out pos count i)=
      initialHeads cap source out 0 count := by
  funext i
  refine Fin.addCases (m:=281) (n:=36) (fun i=>?_) (fun i=>?_) i
  · refine Fin.addCases (m:=280) (n:=1) (fun i=>?_) (fun i=>?_) i
    · by_cases hi : i.val=272
      · have he : i=272 := Fin.ext hi
        subst i; rfl
      · have hn : ((i.castAdd 1).castAdd 36 : Fin 317)≠272 := by
          intro he; exact hi (congrArg (fun j : Fin 317=>j.val) he)
        simp only [selected,hn,decide_false,Bool.false_eq_true,ite_false,initialHeads,Fin.addCases_left,before,
          RecoverySourceClauseList.cfg,VerifierDecoding.RepeatMachine.cfg,controlConfig,TapeEmbedding.config,
          Fin.addCases_left,RecoverySourceClauseReuse.heads,hi,ite_false]
    · fin_cases i; rfl
  · have hn : (i.natAdd 281 : Fin 317)≠272 := by
      intro he; have hv:=congrArg (fun j : Fin 317=>j.val) he
      change 281+i.val=272 at hv; omega
    simp only [selected,hn,decide_false,Bool.false_eq_true,ite_false,initialHeads,Fin.addCases_right]

theorem padded_update (cap : Nat) (base : Fin 317→List Bool) (address : List Bool) :
    (fun i=>ZeroPadding.pad (addressCaps cap i) (Function.update base 159 address i))=
      Function.update (fun i=>ZeroPadding.pad (addressCaps cap i) (base i)) 159 (ZeroPadding.pad cap address) := by
  funext i
  by_cases hi : i=159
  · subst i; rw [Function.update_self,Function.update_self]; rfl
  · rw [Function.update_of_ne hi,Function.update_of_ne hi]

theorem reset_run (p : RawProjectionPCP) (R Q : Nat) (hr : p.width≤R) (hq : p.queries≤Q)
    {n : Nat} (x : BitInput n) (randomness : BitInput R) (cap logCap resetCap : Nat) (out : List Bool)
    (hc : RecoverySourceClauseLoad.uniformBudget Q R≤cap)
    (hl : RecoveryProjectionRowsRewind.batchBudget R Q+2≤logCap)
    (hz : budget cap R Q (Codec.clauses p).length≤resetCap) : ∃ r,
    runFrom machine (2*budget cap R Q (Codec.clauses p).length+2)
      ⟨machine.start,heads cap (DedupBytes.fields p) out (Codec.clauses p).length,
        input cap (DedupBytes.fields p) out (Codec.clauses p).length p R Q randomness logCap resetCap⟩=some r ∧
      r.final.heads=heads cap (DedupBytes.fields p)
        (out++FieldList.stream (RecoveryPCPFormulaResume.rowWords
          (compactProjectionPCP (p.normalized R Q hr hq)) x randomness)) (Codec.clauses p).length ∧
      r.final.tapes=Function.update
        (input cap (DedupBytes.fields p)
          (out++FieldList.stream (RecoveryPCPFormulaResume.rowWords
            (compactProjectionPCP (p.normalized R Q hr hq)) x randomness))
          (Codec.clauses p).length p R Q randomness logCap resetCap) 159
        (ZeroPadding.pad cap (FieldList.stream (RecoveryProjectionRows.addressFields p R Q hr hq x randomness))) ∧
      r.steps≤2*budget cap R Q (Codec.clauses p).length+2 := by
  obtain ⟨base,hbase,bh,bt,bs⟩ := state_run p R Q hr hq x randomness cap logCap out hc hl
  obtain ⟨padded,hp,pf,ps,_⟩ := ZeroPadding.run_config RecoveryPCPFormulaResumeRow.machine (addressCaps cap) _ _ base hbase
  obtain ⟨r,hrun,rf,rs,_⟩ := MaskedReset.workspace_run RecoveryPCPFormulaResumeRow.machine selected _ resetCap _ padded hp
    (by intro i hi
        have he : i=272 := by simpa only [selected,decide_eq_true_eq] using hi
        subst i; rfl) (by rw [ps]; exact bs.trans hz)
  have hb : 2*padded.steps+2≤2*budget cap R Q (Codec.clauses p).length+2 := by rw [ps]; omega
  have hm:=runFrom_moreFuel machine _
    (2*budget cap R Q (Codec.clauses p).length+2-(2*padded.steps+2)) _ r hrun
  rw [Nat.add_sub_of_le hb] at hm
  have hin : ZeroPadding.config (Rewind.Workspace.capacities 317 resetCap)
      (Rewind.recording (ZeroPadding.config (addressCaps cap)
        ⟨RecoveryPCPFormulaResumeRow.machine.start,
          initialHeads cap (DedupBytes.fields p) out 0 (Codec.clauses p).length,
          initialTapes cap (DedupBytes.fields p) out 0 (Codec.clauses p).length p R Q randomness logCap⟩) 0)=
      (⟨machine.start,heads cap (DedupBytes.fields p) out (Codec.clauses p).length,
        input cap (DedupBytes.fields p) out (Codec.clauses p).length p R Q randomness logCap resetCap⟩ : Configuration 318 _) := by
    apply configuration_ext
    · rfl
    · funext i
      refine Fin.addCases (m:=317) (n:=1) (fun i=>?_) (fun i=>?_) i
      all_goals simp only [ZeroPadding.config,Rewind.recording,Rewind.config,heads,Fin.addCases_left,Fin.addCases_right]
    · funext i
      refine Fin.addCases (m:=317) (n:=1) (fun i=>?_) (fun i=>?_) i
      · simp only [ZeroPadding.config,Rewind.Workspace.capacities,Rewind.recording,Rewind.config,
          Fin.addCases_left,ZeroPadding.pad_zero,input,Fin.addCases_left,tapes]
      · simp only [ZeroPadding.config,Rewind.Workspace.capacities,Rewind.recording,Rewind.config,
          Fin.addCases_right,ZeroPadding.pad,List.replicate_zero,List.length_nil,Nat.sub_zero,List.nil_append,
          input,Fin.addCases_right]
  rw [hin] at hm
  refine ⟨r,hm,?_,?_,by omega⟩
  · rw [rf,pf]
    change Fin.addCases (m:=317) (n:=1) (motive:=fun _=>Nat)
      (fun i=>if selected i then 0 else base.final.heads i) (fun _=>0)=_
    rw [bh,head_reset]
    rfl
  · rw [rf,pf]
    change Fin.addCases (m:=317) (n:=1) (motive:=fun _=>List Bool)
      (fun i=>ZeroPadding.pad (addressCaps cap i) (base.final.tapes i))
      (fun _=>List.replicate resetCap false)=_
    rw [bt,padded_update]
    funext i
    refine Fin.addCases (m:=317) (n:=1) (fun i=>?_) (fun i=>?_) i
    · simp only [Fin.addCases_left,input]
      by_cases hi : i=159
      · subst i; rfl
      · have hn : (i.castAdd 1 : Fin 318)≠159 := by
          intro he; apply hi; exact Fin.ext (congrArg (fun j : Fin 318=>j.val) he)
        rw [Function.update_of_ne hi,Function.update_of_ne hn]
        simp only [Fin.addCases_left]
        rfl
    · fin_cases i; rfl

end NearCubicWires.RepairSource.RecoveryPCPFormulaResumeRowReset
