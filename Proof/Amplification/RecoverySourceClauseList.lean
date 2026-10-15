import Proof.Amplification.RecoverySourceClauseReusable

/-! One fixed ordinary machine reads the original source-clause list in
order, including repetitions, and appends the evaluated recovery clauses. -/
namespace NearCubicWires.RepairSource.RecoverySourceClauseList
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound VerifierDecoding
open SourceInterfaces ProjectionNormalization RecoverySourceClauseReuse
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

noncomputable def machine := RepeatMachine.machine RecoverySourceClauseReuse.machine (fun _ _=>true)
noncomputable def cfg (phase : Fin 5) (cap : Nat) (source address out : List Bool)
    (sourcePosition total driver : Nat) := RepeatMachine.cfg phase
      (⟨RecoverySourceClauseReuse.machine.start,heads sourcePosition out.length,data source address out cap⟩ : Configuration 280 _)
      total driver
def clauseFields {Q : Nat} (clause : Fin 3→Literal Q) :=
  RecoverySourceClauseRead.prefixes (fun i=>(literalCode (clause i)).bits) 3
def sourceFields {Q : Nat} (clauses : List (Fin 3→Literal Q)) := clauses.flatMap clauseFields
def emitted {M : TimedDecisionMachine} {T : Nat→Nat} (pcp : ProjectionPCP M T) {n : Nat}
    (x : BitInput n) (randomness : BitInput (pcp.nativeWidth n))
    (clauses : List (Fin 3→Literal (pcp.queryCount n))) :=
  clauses.flatMap (fun clause=>frame (RecoverySourceClauseCode.word pcp x randomness clause))

theorem source_split {Q : Nat} (pre suffix : List Bool) (clause : Fin 3→Literal Q) :
    RecoverySourceClauseRead.source pre (fun i=>(literalCode (clause i)).bits) suffix=
      pre++clauseFields clause++suffix := by
  simp [RecoverySourceClauseRead.source,clauseFields,RecoverySourceClauseRead.prefixes,
    List.append_assoc]

theorem remaining_run {M : TimedDecisionMachine} {T : Nat→Nat} (pcp : ProjectionPCP M T) {n : Nat}
    (x : BitInput n) (randomness : BitInput (pcp.nativeWidth n)) (cap : Nat)
    (clauses : List (Fin 3→Literal (pcp.queryCount n))) (pre suffix out : List Bool)
    (total pos : Nat) (hn : pos+clauses.length=total)
    (hc : RecoverySourceClauseLoad.uniformBudget (pcp.queryCount n) (pcp.nativeWidth n)≤cap) : ∃ r,
    runFrom machine (clauses.length*(5*cap+11)+total+3)
      (cfg 0 cap (pre++sourceFields clauses++suffix)
        (FieldList.stream (RecoverySourceLiteralMeaning.fields pcp x randomness)) out pre.length total (pos+1))=some r ∧
      r.final=cfg 3 cap (pre++sourceFields clauses++suffix)
        (FieldList.stream (RecoverySourceLiteralMeaning.fields pcp x randomness))
        (out++emitted pcp x randomness clauses) (pre++sourceFields clauses).length total 1 ∧
      r.steps≤clauses.length*(5*cap+11)+total+3 := by
  let address := FieldList.stream (RecoverySourceLiteralMeaning.fields pcp x randomness)
  induction clauses generalizing pre out pos with
  | nil =>
    have hp : pos=total := by simpa using hn
    subst pos
    obtain ⟨r,hr,hf,hs⟩ := exhaust_run RecoverySourceClauseReuse.machine
      (⟨RecoverySourceClauseReuse.machine.start,heads pre.length out.length,
        data (pre++suffix) address out cap⟩ : Configuration 280 _) total
    refine ⟨r,?_,?_,?_⟩
    · simpa only [machine,cfg,sourceFields,List.flatMap_nil,List.append_nil,List.length_nil,Nat.zero_mul,Nat.zero_add] using hr
    · simpa only [cfg,sourceFields,emitted,List.flatMap_nil,List.append_nil] using hf
    · simpa only [List.length_nil,Nat.zero_mul,Nat.zero_add] using hs.le
  | cons clause clauses ih =>
    obtain ⟨body,hbody,bh,bt,bs⟩ := body_run pcp x randomness clause pre (sourceFields clauses++suffix) out cap hc
    simp only [source_split] at hbody bt
    let next := (⟨RecoverySourceClauseReuse.machine.start,
      heads (pre++clauseFields clause).length
        (out++frame (RecoverySourceClauseCode.word pcp x randomness clause)).length,
      data (pre++clauseFields clause++(sourceFields clauses++suffix)) address
        (out++frame (RecoverySourceClauseCode.word pcp x randomness clause)) cap⟩ : Configuration 280 _)
    have hstep := iteration_data RecoverySourceClauseReuse.machine _ next total pos body rfl
      (by simp only [List.length_cons] at hn; omega) hbody bh bt
    change Timed machine (body.steps+2)
      (cfg 0 cap (pre++clauseFields clause++(sourceFields clauses++suffix)) address out pre.length total (pos+1))
      (cfg 0 cap (pre++clauseFields clause++(sourceFields clauses++suffix)) address
        (out++frame (RecoverySourceClauseCode.word pcp x randomness clause))
        (pre++clauseFields clause).length total (pos+2)) at hstep
    obtain ⟨rest,hrest,rf,rs⟩ := ih (pre++clauseFields clause)
      (out++frame (RecoverySourceClauseCode.word pcp x randomness clause)) (pos+1)
      (by simp only [List.length_cons] at hn; omega)
    have hmid : pos+2=(pos+1)+1 := by omega
    simp only [List.append_assoc,hmid] at hstep
    simp only [List.append_assoc] at hrest
    rcases hstep with ⟨space,hprefix⟩
    obtain ⟨result,hr,hf,hs,_hspace⟩ := hprefix.followedBy rest hrest
    have hbound : (body.steps+2)+(clauses.length*(5*cap+11)+total+3) ≤
        (clause::clauses).length*(5*cap+11)+total+3 := by
      simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
    have hmore := runFrom_moreFuel machine _
      ((clause::clauses).length*(5*cap+11)+total+3-
        ((body.steps+2)+(clauses.length*(5*cap+11)+total+3))) _ result hr
    rw [Nat.add_sub_of_le hbound] at hmore
    refine ⟨result,?_,?_,?_⟩
    · simpa only [sourceFields,List.flatMap_cons,List.append_assoc] using hmore
    · rw [hf,rf]
      simp only [sourceFields,emitted,List.flatMap_cons,List.append_assoc]
    · rw [hs]
      omega

theorem list_run {M : TimedDecisionMachine} {T : Nat→Nat} (pcp : ProjectionPCP M T) {n : Nat}
    (x : BitInput n) (randomness : BitInput (pcp.nativeWidth n)) (cap : Nat)
    (clauses : List (Fin 3→Literal (pcp.queryCount n))) (pre suffix out : List Bool)
    (hc : RecoverySourceClauseLoad.uniformBudget (pcp.queryCount n) (pcp.nativeWidth n)≤cap) : ∃ r,
    runFrom machine (clauses.length*(5*cap+12)+3)
      (cfg 0 cap (pre++sourceFields clauses++suffix)
        (FieldList.stream (RecoverySourceLiteralMeaning.fields pcp x randomness)) out pre.length clauses.length 1)=some r ∧
      r.final=cfg 3 cap (pre++sourceFields clauses++suffix)
        (FieldList.stream (RecoverySourceLiteralMeaning.fields pcp x randomness))
        (out++emitted pcp x randomness clauses) (pre++sourceFields clauses).length clauses.length 1 ∧
      r.steps≤clauses.length*(5*cap+12)+3 := by
  have h:=remaining_run pcp x randomness cap clauses pre suffix out clauses.length 0 (by omega) hc
  have he : clauses.length*(5*cap+11)+clauses.length+3=clauses.length*(5*cap+12)+3 := by
    ring
  simpa only [he,Nat.zero_add] using h

end NearCubicWires.RepairSource.RecoverySourceClauseList
