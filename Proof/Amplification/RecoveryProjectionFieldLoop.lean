import Proof.Amplification.RecoveryProjectionFieldBody

/-! The actual bounded repeater executes every normalized projection field,
retains its source/randomness words, and returns the physical count driver.
Generic configuration equalities keep the large fixed evaluator graph opaque. -/
namespace NearCubicWires.RepairSource.RecoveryProjectionField
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound VerifierDecoding
open ProjectionNormalization
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
noncomputable def loopCfg (phase : Fin 5) (cap : Nat) (source randomness tail out : List Bool)
    (pos total driver : Nat) := RepeatMachine.cfg phase
      (⟨bodyMachine.start,bodyHeads pos out.length,bodyInput cap source randomness tail out⟩ : Configuration 34 _)
      total driver
def emitted (fields : List (List Bool)) (randomness : List Bool) :=
  fields.flatMap (fun bits=>[true,RecoveryProjectionEval.outputBit bits randomness])

theorem remaining_run (cap : Nat) (pre : List Bool) (fields : List (List Bool))
    (suffix randomness tail out : List Bool) (total pos : Nat) (hn : pos+fields.length=total)
    (hc : ∀ bits∈fields,RecoveryProjectionEval.budget bits randomness+1 ≤ cap) : ∃ r,
    runFrom loopMachine (fields.length*(bodyBudget cap+2)+total+3)
      (loopCfg 0 cap (pre++FieldList.stream fields++suffix) randomness tail out pre.length total (pos+1))=some r ∧
      r.final=loopCfg 3 cap (pre++FieldList.stream fields++suffix) randomness tail
        (out++emitted fields randomness) (pre.length+(FieldList.stream fields).length) total 1 ∧
      r.steps ≤ fields.length*(bodyBudget cap+2)+total+3 := by
  induction fields generalizing pre out pos with
  | nil =>
    have hp : pos=total := by simpa using hn
    subst pos
    obtain ⟨r,hr,hf,hs⟩ := exhaust_run bodyMachine
      (⟨bodyMachine.start,bodyHeads pre.length out.length,bodyInput cap (pre++suffix) randomness tail out⟩ : Configuration 34 _) total
    refine ⟨r,?_,?_,?_⟩
    · simpa only [loopMachine,loopCfg,FieldList.stream_nil,List.append_nil,List.length_nil,Nat.zero_mul,Nat.zero_add] using hr
    · simpa only [loopCfg,FieldList.stream_nil,emitted,List.flatMap_nil,List.append_nil,List.length_nil,Nat.add_zero] using hf
    · simpa only [List.length_nil,Nat.zero_mul,Nat.zero_add] using hs.le
  | cons bits fields ih =>
    have hbits := hc bits (by simp)
    have htail : ∀ b∈fields,RecoveryProjectionEval.budget b randomness+1 ≤ cap := fun b hb=>hc b (by simp [hb])
    obtain ⟨body,hbody,bh,bt,bs⟩ := body_run cap pre bits (FieldList.stream fields++suffix) randomness tail out hbits
    let next := (⟨bodyMachine.start,bodyHeads (pre.length+2*bits.length+1)
      (out++[true,RecoveryProjectionEval.outputBit bits randomness]).length,
      bodyInput cap (pre++RepairOrdinary.frame bits++(FieldList.stream fields++suffix)) randomness tail
        (out++[true,RecoveryProjectionEval.outputBit bits randomness])⟩ : Configuration 34 _)
    have hstep := iteration_data bodyMachine _ next total pos body rfl
      (by simp only [List.length_cons] at hn; omega) hbody bh bt
    change Timed loopMachine (body.steps+2)
      (loopCfg 0 cap (pre++RepairOrdinary.frame bits++(FieldList.stream fields++suffix)) randomness tail out pre.length total (pos+1))
      (loopCfg 0 cap (pre++RepairOrdinary.frame bits++(FieldList.stream fields++suffix)) randomness tail
        (out++[true,RecoveryProjectionEval.outputBit bits randomness]) (pre.length+2*bits.length+1) total (pos+2)) at hstep
    obtain ⟨rest,hrest,rf,rs⟩ := ih (pre++RepairOrdinary.frame bits)
      (out++[true,RecoveryProjectionEval.outputBit bits randomness]) (pos+1)
      (by simp only [List.length_cons] at hn; omega) htail
    have hmid : loopCfg 0 cap (pre++RepairOrdinary.frame bits++(FieldList.stream fields++suffix)) randomness tail
        (out++[true,RecoveryProjectionEval.outputBit bits randomness]) (pre.length+2*bits.length+1) total (pos+2)=
      loopCfg 0 cap ((pre++RepairOrdinary.frame bits)++FieldList.stream fields++suffix) randomness tail
        (out++[true,RecoveryProjectionEval.outputBit bits randomness]) (pre++RepairOrdinary.frame bits).length total ((pos+1)+1) := by
      simp only [List.append_assoc,List.length_append,frame_length,Nat.add_assoc]
    rw [hmid] at hstep
    rcases hstep with ⟨space,hprefix⟩
    obtain ⟨result,hr,hf,hs,_hspace⟩ := hprefix.followedBy rest hrest
    have hbound : (body.steps+2)+(fields.length*(bodyBudget cap+2)+total+3) ≤
        (bits::fields).length*(bodyBudget cap+2)+total+3 := by
      simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
    have hmore := runFrom_moreFuel loopMachine _
      ((bits::fields).length*(bodyBudget cap+2)+total+3-
        ((body.steps+2)+(fields.length*(bodyBudget cap+2)+total+3))) _ result hr
    rw [Nat.add_sub_of_le hbound] at hmore
    refine ⟨result,?_,?_,?_⟩
    · simpa only [FieldList.stream_cons,List.append_assoc] using hmore
    · rw [hf,rf]
      simp only [FieldList.stream_cons,emitted,List.flatMap_cons,List.append_assoc,List.length_append,frame_length,Nat.add_assoc]
    · rw [hs]
      omega

theorem loop_run (cap : Nat) (pre : List Bool) (fields : List (List Bool))
    (suffix randomness tail out : List Bool)
    (hc : ∀ bits∈fields,RecoveryProjectionEval.budget bits randomness+1 ≤ cap) : ∃ r,
    runFrom loopMachine (fields.length*(4*cap+11)+3)
      (loopCfg 0 cap (pre++FieldList.stream fields++suffix) randomness tail out pre.length fields.length 1)=some r ∧
      r.final=loopCfg 3 cap (pre++FieldList.stream fields++suffix) randomness tail
        (out++emitted fields randomness) (pre.length+(FieldList.stream fields).length) fields.length 1 ∧
      r.steps ≤ fields.length*(4*cap+11)+3 := by
  have h := remaining_run cap pre fields suffix randomness tail out fields.length 0 (by omega) hc
  have he : fields.length*(bodyBudget cap+2)+fields.length+3=fields.length*(4*cap+11)+3 := by
    simp only [bodyBudget,Nat.mul_add]
    omega
  simpa only [he,Nat.zero_add] using h

end NearCubicWires.RepairSource.RecoveryProjectionField
