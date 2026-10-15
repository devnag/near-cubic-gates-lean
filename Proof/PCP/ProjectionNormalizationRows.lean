import Proof.PCP.ProjectionNormalizationRow

/-! The physically counted native-query traversal. Every row consumes its
actual fields, pads it, and restores the width drivers before the next row.
The query driver is rewound only when the complete traversal finishes. -/
namespace NearCubicWires.RepairSource.ProjectionNormalization.Rows
open LocalBitMultitape RepairOrdinary RecoveryExecution VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def stream (rows : List (List (List Bool))) := (rows.map FieldList.stream).flatten
def padded (rows : List (List (List Bool))) (padding : ℕ) := rows.map (fun row => Row.paddedFields row padding)
noncomputable def machine := RepeatMachine.machine Row.machine (fun _ _ => true)
noncomputable def cfg (phase : Fin 5) (source : List Bool) (pos : ℕ) (out : List Bool)
    (native padding total driver : ℕ) :=
  RepeatMachine.cfg phase (Row.cfg Row.machine.start source pos out native padding) total driver

@[simp] theorem stream_nil : stream []=[] := rfl
@[simp] theorem stream_cons (row : List (List Bool)) (rows : List (List (List Bool))) :
    stream (row::rows)=FieldList.stream row++stream rows := rfl
@[simp] theorem padded_nil (padding : ℕ) : padded [] padding=[] := rfl
@[simp] theorem padded_cons (row : List (List Bool)) (rows : List (List (List Bool))) (padding : ℕ) :
    padded (row::rows) padding=Row.paddedFields row padding::padded rows padding := rfl

theorem remaining (pre : List Bool) (rows : List (List (List Bool))) (suffix out : List Bool)
    (native padding total pos : ℕ) (hn : pos+rows.length=total)
    (hrows : ∀ row∈rows,row.length=native) :
    ∃ r,runFrom machine ((stream rows).length+rows.length*(3*native+10*padding+9)+total+3)
      (cfg 0 (pre++stream rows++suffix) pre.length out native padding total (pos+1))=some r ∧
      r.steps≤(stream rows).length+rows.length*(3*native+10*padding+9)+total+3 ∧
      r.final=cfg 3 (pre++stream rows++suffix) (pre.length+(stream rows).length)
        (out++stream (padded rows padding)) native padding total 1 := by
  induction rows generalizing pre out pos with
  | nil =>
    have hp : pos=total := by simpa using hn
    subst pos
    obtain ⟨r,hr,hf,hs⟩ := (RepeatMachine.exhaust Row.machine (fun _ _ => true)
      (Row.cfg Row.machine.start (pre++suffix) pre.length out native padding) total).run
      (by simp [RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])
    refine ⟨r,?_,?_,?_⟩
    · simpa only [machine,cfg,stream_nil,List.length_nil,List.append_nil,Nat.zero_mul,Nat.zero_add] using hr
    · simpa only [stream_nil,List.length_nil,Nat.zero_mul,Nat.zero_add] using hs.le
    · simpa only [cfg,stream_nil,padded_nil,List.length_nil,List.append_nil,Nat.add_zero] using hf
  | cons row rows ih =>
    have hrow : row.length=native := hrows row (by simp)
    have htailrows : ∀ r∈rows,r.length=native := fun r hr => hrows r (by simp [hr])
    obtain ⟨body,hb,hbf,hbt⟩ := Row.row_run pre row (stream rows++suffix) out padding
    rw [hrow] at hb hbf hbt
    have hstep := RepeatMachine.iteration Row.machine (fun _ _ => true)
      (Row.cfg Row.machine.start (pre++FieldList.stream row++(stream rows++suffix)) pre.length out native padding)
      total pos body (by rfl) (by simp only [List.length_cons] at hn; omega) hb
    rw [hbf] at hstep
    change Timed machine (body.steps+2)
      (cfg 0 (pre++FieldList.stream row++(stream rows++suffix)) pre.length out native padding total (pos+1))
      (cfg 0 (pre++FieldList.stream row++(stream rows++suffix))
        (pre.length+(FieldList.stream row).length) (out++FieldList.stream (Row.paddedFields row padding))
        native padding total (pos+2)) at hstep
    obtain ⟨tail,ht,htt,htf⟩ := ih (pre++FieldList.stream row)
      (out++FieldList.stream (Row.paddedFields row padding)) (pos+1)
      (by simp only [List.length_cons] at hn; omega) htailrows
    have hmid : cfg 0 (pre++FieldList.stream row++(stream rows++suffix))
        (pre.length+(FieldList.stream row).length) (out++FieldList.stream (Row.paddedFields row padding))
        native padding total (pos+2)=
      cfg 0 ((pre++FieldList.stream row)++stream rows++suffix)
        (pre++FieldList.stream row).length (out++FieldList.stream (Row.paddedFields row padding))
        native padding total ((pos+1)+1) := by
      simp only [List.append_assoc,List.length_append,Nat.add_assoc]
    rw [hmid] at hstep
    rcases hstep with ⟨space,hstep⟩
    obtain ⟨result,hr,hf,hs,_⟩ := hstep.followedBy tail ht
    have htime : (body.steps+2)+((stream rows).length+rows.length*(3*native+10*padding+9)+total+3)≤
        (stream (row::rows)).length+(row::rows).length*(3*native+10*padding+9)+total+3 := by
      simp only [stream_cons,List.length_append,List.length_cons]
      nlinarith
    have hm := runFrom_moreFuel machine _
      ((stream (row::rows)).length+(row::rows).length*(3*native+10*padding+9)+total+3-
        ((body.steps+2)+((stream rows).length+rows.length*(3*native+10*padding+9)+total+3))) _ result hr
    rw [Nat.add_sub_of_le htime] at hm
    refine ⟨result,?_,?_,?_⟩
    · simpa only [stream_cons,List.append_assoc] using hm
    · rw [hs]
      omega
    · rw [hf,htf]
      simp only [stream_cons,padded_cons,List.append_assoc,List.length_append,Nat.add_assoc]

theorem rows_run (pre : List Bool) (rows : List (List (List Bool))) (suffix out : List Bool)
    (native padding : ℕ) (hrows : ∀ row∈rows,row.length=native) :
    ∃ r,runFrom machine ((stream rows).length+rows.length*(3*native+10*padding+10)+3)
      (cfg 0 (pre++stream rows++suffix) pre.length out native padding rows.length 1)=some r ∧
      r.steps≤(stream rows).length+rows.length*(3*native+10*padding+10)+3 ∧
      r.final=cfg 3 (pre++stream rows++suffix) (pre.length+(stream rows).length)
        (out++stream (padded rows padding)) native padding rows.length 1 := by
  have h := remaining pre rows suffix out native padding rows.length 0 (by omega) hrows
  have he : (stream rows).length+rows.length*(3*native+10*padding+9)+rows.length+3=
      (stream rows).length+rows.length*(3*native+10*padding+10)+3 := by ring
  simpa only [he,Nat.zero_add] using h

end NearCubicWires.RepairSource.ProjectionNormalization.Rows
