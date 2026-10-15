import Proof.PCP.PCPPNativeClauseTyped

/-! The actual original compact clause list is emitted by one fixed ordinary
repeater. Both native counters and both live byte cursors come from execution. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeClauseLoop
open LocalBitMultitape SourceInterfaces RepairSource VerifierDecoding RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

private theorem cfg_data {t s : ℕ} (phase : Fin 5) (c d : Configuration t s) (total driver : ℕ)
    (hh : c.heads=d.heads) (ht : c.tapes=d.tapes) :
    RepeatMachine.cfg phase c total driver=RepeatMachine.cfg phase d total driver := by
  apply configuration_ext
  · rfl
  · simp only [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,hh]
  · simp only [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,ht]

private theorem iteration_data {t s fuel : ℕ} (body : Machine t s)
    (c d : Configuration t s) (total pos : ℕ) (r : ExecutionReceipt t s)
    (hc : c.control=body.start) (hp : pos<total) (hr : runFrom body fuel c=some r)
    (hh : r.final.heads=d.heads) (ht : r.final.tapes=d.tapes) :
    Timed (RepeatMachine.machine body (fun _ _=>true)) (r.steps+2)
      (RepeatMachine.cfg 0 c total (pos+1)) (RepeatMachine.cfg 0 d total (pos+2)) := by
  have h:=RepeatMachine.iteration body (fun _ _=>true) c total pos r hc hp hr
  change Timed _ _ _ (RepeatMachine.cfg 0 r.final total (pos+2)) at h
  rw [cfg_data 0 r.final d total (pos+2) hh ht] at h
  exact h

private theorem exhaust_run {t s : ℕ} (body : Machine t s) (c : Configuration t s) (total : ℕ) :
    ∃ r,runFrom (RepeatMachine.machine body (fun _ _=>true)) (total+3)
      (RepeatMachine.cfg 0 c total (total+1))=some r ∧
      r.final=RepeatMachine.cfg 3 c total 1 ∧ r.steps=total+3 :=
  (RepeatMachine.exhaust body (fun _ _=>true) c total).run
    (by simp [RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])

noncomputable def machine := RepeatMachine.machine PCPPNativeClauseReuse.machine (fun _ _=>true)
noncomputable def cfg (phase : Fin 5) (source : List Bool) (sourcePosition stride p n C base accumulator : ℕ)
    (out : List Bool) (total driver : ℕ) := RepeatMachine.cfg phase
      (PCPPNativeClauseReuse.entry PCPPNativeClauseReuse.machine source sourcePosition stride p n C base accumulator 0 (fun _=>0) out)
      total driver
def sourceFields {q : ℕ} (clauses : List (Fin 3→Literal q)) := clauses.flatMap PCPPNativeClauseTyped.fields
def emitted {q : ℕ} (r stride p n base accumulator : ℕ) (clauses : List (Fin 3→Literal q)) :=
  (PCPPNative.clauseStreamNodes (r:=r) base accumulator (PCPPNativeClauseTyped.reference stride p n) clauses).flatMap PCPPRequestNodeSchema.native
def finalAccumulator (base accumulator count : ℕ) := if count=0 then accumulator else base+3*count-1

theorem accumulator_step (base accumulator count : ℕ) :
    finalAccumulator (base+3) (base+2) count=finalAccumulator base accumulator (count+1) := by
  cases count <;> simp only [finalAccumulator,Nat.succ_ne_zero,ite_false,ite_true,Nat.mul_zero,Nat.add_zero] <;> omega

theorem remaining_run {q : ℕ} (r stride p n W C : ℕ)
    (hq : q≤W) (hstride : stride≤W) (hp : p≤W) (hn : n≤W) (hC : 16384*(W+1)^2≤C)
    (clauses : List (Fin 3→Literal q))
    (hl : ∀ clause∈clauses,∀ j,(PCPPNativeClauseTyped.bits clause j).length≤W)
    (href : ∀ clause∈clauses,∀ j,PCPPNativeClauseTyped.refs stride p n clause j≤W)
    (pre suffix out : List Bool) (base accumulator total pos : ℕ)
    (hlen : pos+clauses.length=total) (ha : accumulator≤base) (hb : base+3*clauses.length≤W) :
    ∃ result,runFrom machine (clauses.length*(48*C+130)+total+3)
      (cfg 0 (pre++sourceFields clauses++suffix) pre.length stride p n C base accumulator out total (pos+1))=some result ∧
      result.final=cfg 3 (pre++sourceFields clauses++suffix) (pre++sourceFields clauses).length
        stride p n C (base+3*clauses.length) (finalAccumulator base accumulator clauses.length)
        (out++emitted r stride p n base accumulator clauses) total 1 ∧
      result.steps≤clauses.length*(48*C+130)+total+3 := by
  induction clauses generalizing pre out base accumulator pos with
  | nil =>
    have hpos : pos=total := by simpa using hlen
    subst pos
    obtain ⟨a,ar,af,as⟩:=exhaust_run PCPPNativeClauseReuse.machine
      (PCPPNativeClauseReuse.entry PCPPNativeClauseReuse.machine (pre++suffix) pre.length stride p n C base accumulator 0 (fun _=>0) out) total
    refine ⟨a,?_,?_,?_⟩
    · simpa only [machine,cfg,sourceFields,List.flatMap_nil,List.append_nil,List.length_nil,Nat.zero_mul,Nat.zero_add] using ar
    · simpa only [cfg,sourceFields,emitted,PCPPNative.clauseStreamNodes,List.flatMap_nil,List.append_nil,
        List.length_nil,Nat.mul_zero,Nat.add_zero,finalAccumulator,ite_true] using af
    · simpa only [List.length_nil,Nat.zero_mul,Nat.zero_add] using as.le
  | cons clause clauses ih =>
    obtain ⟨body,bodyRun,bh,bt,bs⟩:=PCPPNativeClauseTyped.clause_run r stride p n W C base accumulator
      clause pre (sourceFields clauses++suffix) out hq hstride hp hn
      (hl clause (by simp)) (href clause (by simp)) ha (by simp only [List.length_cons,Nat.mul_add] at hb; omega) hC
    let word:=(PCPPNative.clauseNodes (r:=r) base accumulator (PCPPNativeClauseTyped.refs stride p n clause)).flatMap PCPPRequestNodeSchema.native
    let next:=PCPPNativeClauseReuse.entry PCPPNativeClauseReuse.machine
      (pre++PCPPNativeClauseTyped.fields clause++(sourceFields clauses++suffix))
      (pre++PCPPNativeClauseTyped.fields clause).length stride p n C (base+3) (base+2) 0 (fun _=>0) (out++word)
    have hstep:=iteration_data PCPPNativeClauseReuse.machine _ next total pos body rfl
      (by simp only [List.length_cons] at hlen; omega) bodyRun bh bt
    change Timed machine (body.steps+2)
      (cfg 0 (pre++PCPPNativeClauseTyped.fields clause++(sourceFields clauses++suffix)) pre.length stride p n C base accumulator out total (pos+1))
      (cfg 0 (pre++PCPPNativeClauseTyped.fields clause++(sourceFields clauses++suffix))
        (pre++PCPPNativeClauseTyped.fields clause).length stride p n C (base+3) (base+2) (out++word) total (pos+2)) at hstep
    obtain ⟨rest,restRun,rf,rs⟩:=ih
      (by intro cl hcl j; exact hl cl (List.mem_cons_of_mem clause hcl) j)
      (by intro cl hcl j; exact href cl (List.mem_cons_of_mem clause hcl) j)
      (pre++PCPPNativeClauseTyped.fields clause) (out++word) (base+3) (base+2) (pos+1)
      (by simp only [List.length_cons] at hlen; omega) (by omega)
      (by simp only [List.length_cons,Nat.mul_add] at hb; omega)
    have hmid : pos+2=(pos+1)+1 := by omega
    simp only [List.append_assoc,hmid] at hstep
    simp only [List.append_assoc] at restRun
    rcases hstep with ⟨space,hprefix⟩
    obtain ⟨result,hr,hf,hs,_⟩:=hprefix.followedBy rest restRun
    have hbound : (body.steps+2)+(clauses.length*(48*C+130)+total+3)≤
        (clause::clauses).length*(48*C+130)+total+3 := by
      simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
    have more:=runFrom_moreFuel machine _
      ((clause::clauses).length*(48*C+130)+total+3-((body.steps+2)+(clauses.length*(48*C+130)+total+3))) _ result hr
    rw [Nat.add_sub_of_le hbound] at more
    refine ⟨result,?_,?_,?_⟩
    · simpa only [sourceFields,List.flatMap_cons,List.append_assoc] using more
    · rw [hf,rf]
      rw [accumulator_step base accumulator clauses.length]
      have hbase : base+3+3*clauses.length=base+3*(clause::clauses).length := by simp only [List.length_cons]; omega
      simp only [sourceFields,List.flatMap_cons,List.append_assoc,hbase,List.length_cons,
        emitted,PCPPNative.clauseStreamNodes,List.flatMap_append]
      rfl
    · rw [hs]
      omega

theorem list_run {q : ℕ} (r stride p n W C : ℕ)
    (hq : q≤W) (hstride : stride≤W) (hp : p≤W) (hn : n≤W) (hC : 16384*(W+1)^2≤C)
    (clauses : List (Fin 3→Literal q))
    (hl : ∀ clause∈clauses,∀ j,(PCPPNativeClauseTyped.bits clause j).length≤W)
    (href : ∀ clause∈clauses,∀ j,PCPPNativeClauseTyped.refs stride p n clause j≤W)
    (pre suffix out : List Bool) (base accumulator : ℕ)
    (ha : accumulator≤base) (hb : base+3*clauses.length≤W) :
    ∃ result,runFrom machine (clauses.length*(48*C+131)+3)
      (cfg 0 (pre++sourceFields clauses++suffix) pre.length stride p n C base accumulator out clauses.length 1)=some result ∧
      result.final=cfg 3 (pre++sourceFields clauses++suffix) (pre++sourceFields clauses).length
        stride p n C (base+3*clauses.length) (finalAccumulator base accumulator clauses.length)
        (out++emitted r stride p n base accumulator clauses) clauses.length 1 ∧
      result.steps≤clauses.length*(48*C+131)+3 := by
  have h:=remaining_run r stride p n W C hq hstride hp hn hC clauses hl href pre suffix out
    base accumulator clauses.length 0 (by omega) ha hb
  have he : clauses.length*(48*C+130)+clauses.length+3=clauses.length*(48*C+131)+3 := by ring
  simpa only [he,Nat.zero_add] using h

end NearCubicWires.RepairOrdinary.PCPPNativeClauseLoop
