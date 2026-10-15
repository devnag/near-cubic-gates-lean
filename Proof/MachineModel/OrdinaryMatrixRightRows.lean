import Proof.MachineModel.OrdinaryMatrixRightSelect

/-! Complete inner-row selection from a physical count driver. Each row
executes skip-A/keep-B, reuses the U template and retains global cursors. -/
namespace NearCubicWires.RepairOrdinary.MatrixRightRows
open LocalBitMultitape RecoveryExecution
open StablePartition (Record recordsBits)
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev Row := List Record × List Record
def fields (rows : List Row) := rows.flatMap (fun r => recordsBits r.1++recordsBits r.2)
def output (rows : List Row) := rows.flatMap (fun r => r.2.map Prod.fst)
noncomputable def machine := RepeatMachine.machine MatrixRightSelect.machine (fun _ _ => true)
def core (source : List Bool) (pos : ℕ) (out : List Bool) (U : ℕ) :=
  PayloadCounted.config MatrixRightSelect.machine.start source pos out 1 (UnaryTemplate.tape U)

theorem rows_run (U total processed : ℕ) (rows : List Row) (pre suffix out : List Bool)
    (hw : ∀ row ∈ rows,row.1.length=U ∧ row.2.length=U) (hn : processed+rows.length=total) :
    ∃ actual,runFrom machine ((fields rows).length+rows.length*(6*U+11)+total+3)
      (RepeatMachine.cfg 0 (core (pre++fields rows++suffix) pre.length out U) total (processed+1))=some actual ∧
      actual.final=RepeatMachine.cfg 3
        (core (pre++fields rows++suffix) (pre.length+(fields rows).length) (out++output rows) U) total 1 ∧
      actual.steps ≤ (fields rows).length+rows.length*(6*U+11)+total+3 := by
  induction rows generalizing processed pre out with
  | nil =>
    have he : processed=total := by simpa using hn
    subst processed
    obtain ⟨r,hr,hf,hs⟩ := (RepeatMachine.exhaust MatrixRightSelect.machine (fun _ _ => true)
      (core (pre++suffix) pre.length out U) total).run
      (by simp [RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])
    exact ⟨r,by simpa [machine,fields] using hr,by simpa [fields,output] using hf,by simpa [fields] using hs.le⟩
  | cons row rows ih =>
    have hrow := hw row (by simp)
    have hrows : ∀ r ∈ rows,r.1.length=U ∧ r.2.length=U := fun r h => hw r (by simp [h])
    let source := pre++fields (row::rows)++suffix
    let next := pre.length+(recordsBits row.1).length+(recordsBits row.2).length
    let appended := out++row.2.map Prod.fst
    obtain ⟨body,hbody,hbf,hbs⟩ := MatrixRightSelect.row_run pre row.1 row.2 (fields rows++suffix) out
      (hrow.1.trans hrow.2.symm)
    have hsource : pre++recordsBits row.1++recordsBits row.2++(fields rows++suffix)=source := by
      simp [source,fields,List.append_assoc]
    rw [hsource] at hbody hbf
    rw [hrow.2] at hbody hbf hbs
    obtain ⟨tail,htail,htf,hts⟩ := ih (processed+1)
      (pre++recordsBits row.1++recordsBits row.2) appended hrows (by simp at hn; omega)
    have hsource' : (pre++recordsBits row.1++recordsBits row.2)++fields rows++suffix=source := by
      simp [source,fields,List.append_assoc]
    have hpos : (pre++recordsBits row.1++recordsBits row.2).length=next := by simp [next,Nat.add_assoc]
    rw [hsource',hpos] at htail htf
    have hp := RepeatMachine.iteration MatrixRightSelect.machine (fun _ _ => true)
      (core source pre.length out U) total processed body rfl (by simp at hn; omega) hbody
    simp only [↓reduceIte] at hp
    rw [hbf] at hp
    have he : RepeatMachine.cfg 0
        (PayloadCounted.config (33 : Fin 34) source next appended 1 (UnaryTemplate.tape U)) total (processed+2)=
        RepeatMachine.cfg 0 (core source next appended U) total (processed+2) := rfl
    rw [he] at hp
    rcases hp with ⟨space,hp⟩
    have ht : runFrom machine ((fields rows).length+rows.length*(6*U+11)+total+3)
        (RepeatMachine.cfg 0 (core source next appended U) total (processed+2))=some tail := by
      simpa only [Nat.add_assoc] using htail
    obtain ⟨actual,hrun,hf,hs,_⟩ := hp.followedBy tail ht
    have hfields : (fields (row::rows)).length=
        (recordsBits row.1).length+(recordsBits row.2).length+(fields rows).length := by simp [fields]; omega
    have htime : body.steps+2+((fields rows).length+rows.length*(6*U+11)+total+3)=
        (fields (row::rows)).length+(row::rows).length*(6*U+11)+total+3 := by
      rw [hbs,hfields]
      simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
    rw [htime] at hrun
    refine ⟨actual,hrun,?_,?_⟩
    · rw [hf,htf]
      have hend : next+(fields rows).length=pre.length+(fields (row::rows)).length := by
        rw [hfields]
        dsimp [next]
        omega
      have hout : appended++output rows=out++output (row::rows) := by simp [appended,output,List.append_assoc]
      rw [hend,hout]
    · rw [hs]
      rw [hfields]
      simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
      nlinarith only [hbs,hts]

theorem complete_run (U : ℕ) (rows : List Row) (pre suffix out : List Bool)
    (hw : ∀ row ∈ rows,row.1.length=U ∧ row.2.length=U) :
    ∃ actual,runFrom machine ((fields rows).length+rows.length*(6*U+12)+3)
      (RepeatMachine.cfg 0 (core (pre++fields rows++suffix) pre.length out U) rows.length 1)=some actual ∧
      actual.final=RepeatMachine.cfg 3
        (core (pre++fields rows++suffix) (pre.length+(fields rows).length) (out++output rows) U) rows.length 1 ∧
      actual.steps ≤ (fields rows).length+rows.length*(6*U+12)+3 := by
  have h := rows_run U rows.length 0 rows pre suffix out hw (by omega)
  have ht : (fields rows).length+rows.length*(6*U+11)+rows.length+3=
      (fields rows).length+rows.length*(6*U+12)+3 := by ring
  simpa only [ht,Nat.zero_add] using h

end NearCubicWires.RepairOrdinary.MatrixRightRows
