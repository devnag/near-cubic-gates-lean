import Proof.Amplification.RecoveryProjectionQueryFrame

/-! The physical outer query loop executes each normalized R-field address
row and retains the SAME width driver, source, randomness and cleared bank. -/
namespace NearCubicWires.RepairSource.RecoveryProjectionRows
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound VerifierDecoding
open ProjectionNormalization RecoveryProjectionField
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

def stream (rows : List (List (List Bool))) := rows.flatMap FieldList.stream
def output (rows : List (List (List Bool))) (randomness : List Bool) :=
  rows.flatMap (fun fields=>emitted fields randomness++[false])
noncomputable def machine := RepeatMachine.machine queryMachine (fun _ _=>true)
noncomputable def cfg (phase : Fin 5) (cap width : Nat) (source randomness tail out : List Bool)
    (pos total driver : Nat) := RepeatMachine.cfg phase
      (⟨queryMachine.start,queryHeads pos out.length,queryInput cap width source randomness tail out⟩ : Configuration 35 _)
      total driver

theorem remaining_run (cap width : Nat) (pre : List Bool) (rows : List (List (List Bool)))
    (suffix randomness tail out : List Bool) (total pos : Nat) (hn : pos+rows.length=total)
    (hw : ∀ row∈rows,row.length=width)
    (hc : ∀ row∈rows,∀ bits∈row,RecoveryProjectionEval.budget bits randomness+1 ≤ cap) : ∃ r,
    runFrom machine (rows.length*(width*(4*cap+11)+7)+total+3)
      (cfg 0 cap width (pre++stream rows++suffix) randomness tail out pre.length total (pos+1))=some r ∧
      r.final=cfg 3 cap width (pre++stream rows++suffix) randomness tail
        (out++output rows randomness) (pre.length+(stream rows).length) total 1 ∧
      r.steps ≤ rows.length*(width*(4*cap+11)+7)+total+3 := by
  induction rows generalizing pre out pos with
  | nil =>
    have hp : pos=total := by simpa using hn
    subst pos
    obtain ⟨r,hr,hf,hs⟩ := exhaust_run queryMachine
      (⟨queryMachine.start,queryHeads pre.length out.length,queryInput cap width (pre++suffix) randomness tail out⟩ : Configuration 35 _) total
    refine ⟨r,?_,?_,?_⟩
    · simpa only [machine,cfg,stream,List.flatMap_nil,List.append_nil,List.length_nil,Nat.zero_mul,Nat.zero_add] using hr
    · simpa only [cfg,stream,output,List.flatMap_nil,List.append_nil,List.length_nil,Nat.add_zero] using hf
    · simpa only [List.length_nil,Nat.zero_mul,Nat.zero_add] using hs.le
  | cons row rows ih =>
    have hrow := hw row (by simp)
    have htailw : ∀ r∈rows,r.length=width := fun r hr=>hw r (by simp [hr])
    have htailc : ∀ r∈rows,∀ b∈r,RecoveryProjectionEval.budget b randomness+1 ≤ cap :=
      fun r hr=>hc r (by simp [hr])
    obtain ⟨body,hbody,bh,bt,bs⟩ := query_run cap pre row (stream rows++suffix) randomness tail out
      (hc row (by simp))
    rw [hrow] at hbody bt bs
    let next := (⟨queryMachine.start,queryHeads (pre.length+(FieldList.stream row).length)
      (out++emitted row randomness++[false]).length,
      queryInput cap width (pre++FieldList.stream row++(stream rows++suffix)) randomness tail
        (out++emitted row randomness++[false])⟩ : Configuration 35 _)
    have hstep := iteration_data queryMachine _ next total pos body rfl
      (by simp only [List.length_cons] at hn; omega) hbody bh bt
    change Timed machine (body.steps+2)
      (cfg 0 cap width (pre++FieldList.stream row++(stream rows++suffix)) randomness tail out pre.length total (pos+1))
      (cfg 0 cap width (pre++FieldList.stream row++(stream rows++suffix)) randomness tail
        (out++emitted row randomness++[false]) (pre.length+(FieldList.stream row).length) total (pos+2)) at hstep
    obtain ⟨rest,hrest,rf,rs⟩ := ih (pre++FieldList.stream row)
      (out++emitted row randomness++[false]) (pos+1)
      (by simp only [List.length_cons] at hn; omega) htailw htailc
    have hmid : cfg 0 cap width (pre++FieldList.stream row++(stream rows++suffix)) randomness tail
        (out++emitted row randomness++[false]) (pre.length+(FieldList.stream row).length) total (pos+2)=
      cfg 0 cap width ((pre++FieldList.stream row)++stream rows++suffix) randomness tail
        (out++emitted row randomness++[false]) (pre++FieldList.stream row).length total ((pos+1)+1) := by
      simp only [List.append_assoc,List.length_append,Nat.add_assoc]
    rw [hmid] at hstep
    rcases hstep with ⟨space,hprefix⟩
    obtain ⟨result,hr,hf,hs,_hspace⟩ := hprefix.followedBy rest hrest
    have hbound : (body.steps+2)+(rows.length*(width*(4*cap+11)+7)+total+3) ≤
        (row::rows).length*(width*(4*cap+11)+7)+total+3 := by
      simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
    have hmore := runFrom_moreFuel machine _
      ((row::rows).length*(width*(4*cap+11)+7)+total+3-
        ((body.steps+2)+(rows.length*(width*(4*cap+11)+7)+total+3))) _ result hr
    rw [Nat.add_sub_of_le hbound] at hmore
    refine ⟨result,?_,?_,?_⟩
    · simpa only [stream,List.flatMap_cons,List.append_assoc] using hmore
    · rw [hf,rf]
      simp only [stream,output,List.flatMap_cons,List.append_assoc,List.length_append,Nat.add_assoc]
    · rw [hs]
      omega

theorem rows_run (cap width : Nat) (pre : List Bool) (rows : List (List (List Bool)))
    (suffix randomness tail out : List Bool)
    (hw : ∀ row∈rows,row.length=width)
    (hc : ∀ row∈rows,∀ bits∈row,RecoveryProjectionEval.budget bits randomness+1 ≤ cap) : ∃ r,
    runFrom machine (rows.length*(width*(4*cap+11)+8)+3)
      (cfg 0 cap width (pre++stream rows++suffix) randomness tail out pre.length rows.length 1)=some r ∧
      r.final=cfg 3 cap width (pre++stream rows++suffix) randomness tail
        (out++output rows randomness) (pre.length+(stream rows).length) rows.length 1 ∧
      r.steps ≤ rows.length*(width*(4*cap+11)+8)+3 := by
  have h := remaining_run cap width pre rows suffix randomness tail out rows.length 0 (by omega) hw hc
  have he : rows.length*(width*(4*cap+11)+7)+rows.length+3=rows.length*(width*(4*cap+11)+8)+3 := by
    simp only [Nat.mul_add]
    omega
  simpa only [he,Nat.zero_add] using h

end NearCubicWires.RepairSource.RecoveryProjectionRows
