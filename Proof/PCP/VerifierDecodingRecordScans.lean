import Proof.PCP.VerifierDecodingRecordRange

/-! The absent-field and action-tag scans at the enclosing record's retained
eight-tape boundary. Rejection preserves the physical false result bit; only
success needs the exact reusable endpoint. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.RecordMachine
open LocalBitMultitape RepairOrdinary RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def selectedSlots (tags : Bool) : Fin 2 → Fin 8 := if tags then tagSlots else zeroSlots
def selectedCount (tags : Bool) (j t : ℕ) := if tags then t else j

theorem selected_injective (tags : Bool) : Function.Injective (selectedSlots tags) := by
  cases tags <;> decide

theorem selected_pick (tags : Bool) (i : Fin 8) :
    RecoveryFocus.pick (selectedSlots tags) i =
      if i=0 then some 0 else if i=(if tags then 6 else 2) then some 1 else none := by
  cases tags <;> fin_cases i
  all_goals first
    | exact RecoveryFocus.pick_slot _ (selected_injective _) 0
    | exact RecoveryFocus.pick_slot _ (selected_injective _) 1
    | simp [RecoveryFocus.pick,selectedSlots,zeroSlots,tagSlots]

theorem scan_checked (tags : Bool) (limit : Fin 5) (test : TagMachine.Word → Bool)
    (pre bits backing bound : List Bool) (j t cap : ℕ) (rangeFlag : Bool) :
    let count := selectedCount tags j t
    let p := RecoveryFocus.machine (selectedSlots tags) (TagScan.machine limit test)
    ∃ r, runFrom p (count*(2*limit.val+4)+3)
        (cfg p.start (pre++frame bits) backing bound pre.length j t cap rangeFlag false)=some r ∧
      r.steps≤count*(2*limit.val+4)+3 ∧ r.final.tapes 7=[false] ∧
      (if TagScan.tests limit test count bits then
        r.final=cfg (RepeatMachine.phaseCode (Fintype.card TagMachine.Control) 3)
          (pre++frame bits) backing bound (pre.length+2*limit.val*count) j t cap rangeFlag false
       else r.final.control=RepeatMachine.phaseCode (Fintype.card TagMachine.Control) 4) := by
  let count := selectedCount tags j t
  let p := RecoveryFocus.machine (selectedSlots tags) (TagScan.machine limit test)
  let ambient := cfg p.start (pre++frame bits) backing bound pre.length j t cap rangeFlag false
  obtain ⟨base,hr,hs,hf⟩ := TagScan.checked_run pre bits count limit test
  obtain ⟨r,hrun,hfinal,hsteps⟩ := RecoveryFocus.run_config (selectedSlots tags) (selected_injective tags)
    (TagScan.machine limit test) ambient.heads ambient.tapes _ _ base hr
  have hi : RecoveryFocus.config (selectedSlots tags) ambient.heads ambient.tapes
      (TagScan.initial pre bits count) = ambient := by
    apply configuration_ext
    · rfl
    · funext i
      simp only [RecoveryFocus.config,selected_pick]
      cases tags <;> fin_cases i <;>
        simp [ambient,cfg,TagScan.initial,RepeatMachine.cfg,TagMachine.cfg,count,selectedCount,
          controlConfig,TapeEmbedding.config,Fin.addCases]
    · funext i
      simp only [RecoveryFocus.config,selected_pick]
      cases tags <;> fin_cases i <;>
        simp [ambient,cfg,TagScan.initial,RepeatMachine.cfg,TagMachine.cfg,count,selectedCount,
          controlConfig,TapeEmbedding.config,Fin.addCases]
  rw [hi] at hrun
  refine ⟨r,hrun,?_,?_,?_⟩
  · exact hsteps.trans_le hs
  · cases tags <;> simp [hfinal,RecoveryFocus.config,selected_pick,ambient,cfg]
  · cases ht : TagScan.tests limit test count bits with
    | false =>
      simp only [TagScan.CheckedResult,ht,Bool.false_eq_true,↓reduceIte] at hf
      simpa only [ht,Bool.false_eq_true,↓reduceIte,hfinal,RecoveryFocus.config] using hf
    | true =>
      simp only [TagScan.CheckedResult,ht,↓reduceIte] at hf
      simp only [↓reduceIte,hfinal,hf]
      apply configuration_ext
      · rfl
      · funext i
        simp only [RecoveryFocus.config,selected_pick]
        cases tags <;> fin_cases i <;>
          simp [ambient,cfg,TagScan.finished,RepeatMachine.cfg,TagMachine.cfg,count,selectedCount,
            controlConfig,TapeEmbedding.config,Fin.addCases]
      · funext i
        simp only [RecoveryFocus.config,selected_pick]
        cases tags <;> fin_cases i <;>
          simp [ambient,cfg,TagScan.finished,RepeatMachine.cfg,TagMachine.cfg,count,selectedCount,
            controlConfig,TapeEmbedding.config,Fin.addCases]

theorem zero_checked (pre bits backing bound : List Bool) (j t cap : ℕ) :
    ∃ r, runFrom zeroProgram (6*j+3)
        (cfg zeroProgram.start (pre++frame bits) backing bound pre.length j t cap false false)=some r ∧
      r.steps≤6*j+3 ∧ r.final.tapes 7=[false] ∧
      (if j≤bits.length ∧ bits.take j=List.replicate j false then
        r.final=cfg (RepeatMachine.phaseCode (Fintype.card TagMachine.Control) 3)
          (pre++frame bits) backing bound (pre.length+2*j) j t cap false false
       else r.final.control=RepeatMachine.phaseCode (Fintype.card TagMachine.Control) 4) := by
  simpa only [zeroProgram,selectedCount,Bool.false_eq_true,↓reduceIte,selectedSlots,
    show (1 : Fin 5).val=1 from rfl,show 2*1+4=6 from rfl,Nat.mul_comm j 6,
    Nat.mul_one,TagScan.zeros_test] using
    scan_checked false 1 (fun word => !(word 0)) pre bits backing bound j t cap false

theorem tags_checked (pre bits backing bound : List Bool) (j t cap : ℕ) (present rangeFlag : Bool) :
    ∃ r, runFrom (tagProgram present) (12*t+3)
        (cfg (tagProgram present).start (pre++frame bits) backing bound pre.length j t cap rangeFlag false)=some r ∧
      r.steps≤12*t+3 ∧ r.final.tapes 7=[false] ∧
      (if TagScan.tests 4 (TagMachine.valid present) t bits then
        r.final=cfg (RepeatMachine.phaseCode (Fintype.card TagMachine.Control) 3)
          (pre++frame bits) backing bound (pre.length+8*t) j t cap rangeFlag false
       else r.final.control=RepeatMachine.phaseCode (Fintype.card TagMachine.Control) 4) := by
  simpa only [tagProgram,selectedCount,↓reduceIte,selectedSlots,show (4 : Fin 5).val=4 from rfl,
    show 2*4+4=12 from rfl,Nat.mul_comm t 12,show 2*4=8 from rfl] using
    scan_checked true 4 (TagMachine.valid present) pre bits backing bound j t cap rangeFlag

end NearCubicWires.RepairSource.VerifierDecoding.RecordMachine
