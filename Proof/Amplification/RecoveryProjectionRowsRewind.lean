import Proof.Amplification.RecoveryProjectionColdRows

/-! The reusable normalized address batch begins and ends with all heads at
zero. The existing execution logger pays the complete source/output rewind,
so the following literal lookup can read addresses and the next randomness
batch can reuse exactly the same source and dimension drivers. -/
namespace NearCubicWires.RepairSource.RecoveryProjectionRowsRewind
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
open SourceInterfaces ProjectionNormalization RecoveryProjectionRows
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def raw := Composition.machine RecoveryProjectionInitialize.position RecoveryProjectionRows.machine
noncomputable def machine := Rewind.machine raw
def batchBudget (R Q : Nat) := Q*(R*(4*capacity R+11)+8)+3
def budget (R Q : Nat) := 2*(batchBudget R Q+2)+2
noncomputable def batchInput (p : RawProjectionPCP) (R Q : Nat) (randomness : BitInput R) :=
  (cfg 0 (capacity R) R (QueryBytes.framedCodes (normalizedRows p R Q).flatten)
    (List.ofFn randomness) [] [] 0 Q 1).tapes

theorem heads (cap R Q : Nat) (source randomness : List Bool) :
    RecoveryProjectionInitialize.readyHeads=(cfg 0 cap R source randomness [] [] 0 Q 1).heads := by
  funext i; fin_cases i <;> rfl

theorem raw_run (p : RawProjectionPCP) (R Q : Nat) (hr : p.width≤R) (hq : p.queries≤Q)
    {n : Nat} (x : BitInput n) (randomness : BitInput R) : ∃ r,
    run raw (batchBudget R Q+2) (batchInput p R Q randomness)=some r ∧
      r.final.tapes=(cfg 3 (capacity R) R (QueryBytes.framedCodes (normalizedRows p R Q).flatten)
        (List.ofFn randomness) [] (FieldList.stream (addressFields p R Q hr hq x randomness))
        (QueryBytes.framedCodes (normalizedRows p R Q).flatten).length Q 1).tapes ∧
      r.steps≤batchBudget R Q+2 := by
  obtain ⟨first,hfirst,ff,fs⟩ := (Timed.single (by rfl)
    (RecoveryProjectionInitialize.position_step (batchInput p R Q randomness))).run (by rfl)
  obtain ⟨last,hlast,lf,ls⟩ := normalized_run p R Q hr hq x randomness [] [] [] []
  simp only [List.nil_append,List.append_nil,List.length_nil,Nat.zero_add] at hlast lf
  have hi : Composition.restart first.final RecoveryProjectionRows.machine.start=
      cfg 0 (capacity R) R (QueryBytes.framedCodes (normalizedRows p R Q).flatten)
        (List.ofFn randomness) [] [] 0 Q 1 := by
    rw [ff]
    apply configuration_ext
    · rfl
    · exact heads _ _ _ _ _
    · rfl
  rw [←hi] at hlast
  have hall := Composition.run_join RecoveryProjectionInitialize.position RecoveryProjectionRows.machine 1 _ _ first last hfirst hlast
  have ht : 1+1+(Q*(R*(4*capacity R+11)+8)+3)=batchBudget R Q+2 := by unfold batchBudget; omega
  rw [ht] at hall
  refine ⟨_,hall,?_,?_⟩
  · change last.final.tapes=_
    rw [lf]
  · change first.steps+1+last.steps≤_
    unfold batchBudget
    omega

theorem batch_ready (p : RawProjectionPCP) (R Q : Nat) (hr : p.width≤R) (hq : p.queries≤Q)
    {n : Nat} (x : BitInput n) (randomness : BitInput R) (logCap : Nat)
    (hlog : batchBudget R Q+2≤logCap) :
    ClockJoin.ReadyRun machine (budget R Q)
      (fun i=>Fin.addCases (m:=36) (n:=1) (motive:=fun _=>List Bool)
        (batchInput p R Q randomness) (fun _=>List.replicate logCap false) i)
      (fun i=>Fin.addCases (m:=36) (n:=1) (motive:=fun _=>List Bool)
        (cfg 3 (capacity R) R (QueryBytes.framedCodes (normalizedRows p R Q).flatten)
          (List.ofFn randomness) [] (FieldList.stream (addressFields p R Q hr hq x randomness))
          (QueryBytes.framedCodes (normalizedRows p R Q).flatten).length Q 1).tapes
        (fun _=>List.replicate logCap false) i) := by
  obtain ⟨base,hbase,bt,bs⟩ := raw_run p R Q hr hq x randomness
  obtain ⟨r,hrun,rt,rc,rh,rs,_peak⟩ := Rewind.Workspace.reset_workspace raw _ _ base hbase logCap
  have hb : 2*base.steps+2≤budget R Q := by unfold budget; omega
  have hm := run_moreFuel machine _ (budget R Q-(2*base.steps+2)) _ r hrun
  rw [Nat.add_sub_of_le hb] at hm
  refine ⟨r,hm,?_,rh,by omega⟩
  funext i
  refine Fin.addCases (m:=36) (n:=1) (fun j=>?_) (fun j=>?_) i
  · rw [rt j,bt]
    simp only [Fin.addCases_left]
  · fin_cases j
    simp only [Fin.addCases_right]
    change r.final.tapes 36=List.replicate logCap false
    change r.final.tapes 36=List.replicate (max logCap base.steps) false at rc
    simpa only [max_eq_left (by omega : base.steps≤logCap)] using rc

end NearCubicWires.RepairSource.RecoveryProjectionRowsRewind
