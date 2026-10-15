import Proof.Hierarchy.CompetitorOddRowSliceRow

/-! The physical U counter controls all row selections. The H-byte inner
counter is restored by every row body; the complete raw source is scanned
once and the result is appended in original row order. -/
namespace NearCubicWires.RepairOrdinary.CompetitorOddRowSlice
open LocalBitMultitape RecoveryExecution
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev Row := List Bool × List Bool
def rowWord (row : Row) := row.1++row.2
def sourceRows (rows : List Row) := rows.flatMap rowWord
def selectedRows (rows : List Row) := rows.flatMap Prod.fst
def rowValid (h : ℕ) (row : Row) := row.1.length=h ∧ row.2.length=h
def accepted {s : ℕ} (_ : Fin s) (_ : Fin 3 → Bool) := true
noncomputable def loopProgram := RepeatMachine.machine rowProgram accepted
def loopBudget (h n : ℕ) := n*(rowBudget h+3)+3

theorem loop_driver_run (h : ℕ) (rows : List Row) (total pos : ℕ)
    (pre suffix out : List Bool) (hpos : pos+rows.length=total)
    (hv : ∀ row∈rows,rowValid h row) :
    ∃ r,runFrom loopProgram (rows.length*(rowBudget h+2)+total+3)
      (RepeatMachine.cfg 0 (MatrixRawBlock.config rowProgram.start (UnaryTemplate.tape h) 1
        (pre++sourceRows rows++suffix) pre.length out) total (pos+1))=some r ∧
      r.steps≤rows.length*(rowBudget h+2)+total+3 ∧
      r.final=RepeatMachine.cfg 3 (MatrixRawBlock.config rowProgram.start (UnaryTemplate.tape h) 1
        (pre++sourceRows rows++suffix) (pre.length+(sourceRows rows).length)
        (out++selectedRows rows)) total 1 := by
  induction rows generalizing pos pre out with
  | nil =>
    have hp : pos=total := by simpa using hpos
    subst pos
    obtain ⟨r,hr,hf,hs⟩ := (RepeatMachine.exhaust rowProgram accepted
      (MatrixRawBlock.config rowProgram.start (UnaryTemplate.tape h) 1 (pre++suffix) pre.length out) total).run
      (by simp [RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])
    exact ⟨r,by simpa [loopProgram,sourceRows] using hr,by simpa using hs.le,
      by simpa [sourceRows,selectedRows] using hf⟩
  | cons row rows ih =>
    have ha := hv row (by simp)
    obtain ⟨body,hbody,hbf,hbs⟩ := row_run pre row.1 row.2 (sourceRows rows++suffix) out (ha.2.trans ha.1.symm)
    rw [ha.1] at hbody hbf hbs
    have hbody' : runFrom rowProgram (rowBudget h)
        (MatrixRawBlock.config rowProgram.start (UnaryTemplate.tape h) 1
          (pre++sourceRows (row::rows)++suffix) pre.length out)=some body := by
      simpa [sourceRows,rowWord,List.append_assoc] using hbody
    have iteration := RepeatMachine.iteration rowProgram accepted
      (MatrixRawBlock.config rowProgram.start (UnaryTemplate.tape h) 1
        (pre++sourceRows (row::rows)++suffix) pre.length out) total pos body rfl
      (by simp only [List.length_cons] at hpos; omega) hbody'
    simp only [accepted,if_true] at iteration
    have hend : RepeatMachine.cfg 0 body.final total (pos+2)=
        RepeatMachine.cfg 0 (MatrixRawBlock.config rowProgram.start (UnaryTemplate.tape h) 1
          ((pre++rowWord row)++sourceRows rows++suffix) (pre++rowWord row).length
          (out++row.1)) total (pos+2) := by
      rw [hbf]
      simp [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,MatrixRawBlock.config,rowWord,
        List.append_assoc,ha.1,ha.2,two_mul]
    rw [hend] at iteration
    obtain ⟨tail,htail,hts,htf⟩ := ih (pos+1) (pre++rowWord row) (out++row.1)
      (by simp only [List.length_cons] at hpos; omega) (fun r hr => hv r (by simp [hr]))
    have htail' : runFrom loopProgram (rows.length*(rowBudget h+2)+total+3)
        (RepeatMachine.cfg 0 (MatrixRawBlock.config rowProgram.start (UnaryTemplate.tape h) 1
          ((pre++rowWord row)++sourceRows rows++suffix) (pre++rowWord row).length
          (out++row.1)) total (pos+2))=some tail := by simpa only [Nat.add_assoc] using htail
    rcases iteration with ⟨space,hprefix⟩
    obtain ⟨r,hr,hf,hs,_⟩ := hprefix.followedBy tail htail'
    have htime : (body.steps+2)+(rows.length*(rowBudget h+2)+total+3)≤
        (row::rows).length*(rowBudget h+2)+total+3 := by
      simp only [List.length_cons]
      nlinarith
    have hmore := runFrom_moreFuel loopProgram _
      ((row::rows).length*(rowBudget h+2)+total+3-
        ((body.steps+2)+(rows.length*(rowBudget h+2)+total+3))) _ r hr
    rw [Nat.add_sub_of_le htime] at hmore
    refine ⟨r,hmore,?_,?_⟩
    · rw [hs]
      simp only [List.length_cons]
      nlinarith
    · rw [hf,htf]
      simp [sourceRows,selectedRows,List.length_append,List.append_assoc,Nat.add_assoc]

theorem loop_run (h : ℕ) (rows : List Row) (suffix : List Bool)
    (hv : ∀ row∈rows,rowValid h row) :
    ∃ r,runFrom loopProgram (loopBudget h rows.length)
      (RepeatMachine.cfg 0 (MatrixRawBlock.config rowProgram.start (UnaryTemplate.tape h) 1
        (sourceRows rows++suffix) 0 []) rows.length 1)=some r ∧
      r.steps≤loopBudget h rows.length ∧
      r.final=RepeatMachine.cfg 3 (MatrixRawBlock.config rowProgram.start (UnaryTemplate.tape h) 1
        (sourceRows rows++suffix) (sourceRows rows).length (selectedRows rows)) rows.length 1 := by
  obtain ⟨r,hr,hs,hf⟩ := loop_driver_run h rows rows.length 0 [] suffix [] (by omega) hv
  have he : rows.length*(rowBudget h+2)+rows.length+3=loopBudget h rows.length := by
    unfold loopBudget
    ring
  exact ⟨r,by simpa only [he,List.nil_append,List.length_nil,Nat.zero_add] using hr,
    by simpa only [he] using hs,by simpa using hf⟩

end NearCubicWires.RepairOrdinary.CompetitorOddRowSlice
