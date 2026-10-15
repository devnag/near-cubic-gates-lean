import Proof.CaseAnalysis.RowsEstimatorPrepare

/-! The actual emitted cut stream and raw retained d,p,odd fields now reach
EquationRowRaw's exact framed source. No G or length driver is input. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Framed
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots (j : Fin 59) : Fin 68:=
  if h:j.val<55 then ⟨j.val,by omega⟩ else ⟨j.val+9,by omega⟩
theorem injective : Function.Injective slots:=by
  intro i j he
  have h:=congrArg Fin.val he
  simp only [slots] at h
  split_ifs at h <;> dsimp at h <;> apply Fin.ext <;> omega

def extend (A : Fin 64→List Bool) : Fin 68→List Bool:=
  fun i=>Fin.addCases (m:=64) (n:=4) (motive:=fun _=>List Bool) A (fun _=>[]) i
def input (row : EquationRow.Input):=extend (Prepare.input row)
noncomputable def first:=TapeEmbedding.machine 4 Prepare.machine
noncomputable def last:=RecoveryFocus.machine slots Header.framed
noncomputable def machine:=Composition.machine first last
def budget (row : EquationRow.Input):=Prepare.budget row+1+Header.framedBudget row

theorem projected_input (row : EquationRow.Input) (j : Fin 59) :
    extend (Prepare.output row) (slots j)=Header.framedInput row j:=by
  by_cases hj:j.val<55
  · let i : Fin 55:=⟨j.val,hj⟩
    change extend (Prepare.output row) (slots (((i.castAdd 1).castAdd 1).castAdd 2))=
      Header.framedInput row (((i.castAdd 1).castAdd 1).castAdd 2)
    have hs:slots (((i.castAdd 1).castAdd 1).castAdd 2)=(i.castAdd 9).castAdd 4:=by
      apply Fin.ext
      simp [slots,i.isLt]
    rw [hs]
    simp only [extend,Fin.addCases_left,Header.framedInput,AppendOutputFrame.input,
      AppendOutputLength.input]
    exact Prepare.header_input row i
  · have hv : j.val=55 ∨ j.val=56 ∨ j.val=57 ∨ j.val=58:=by omega
    rcases hv with h | h | h | h
    · have he:j=55:=Fin.ext h
      rw [he];rfl
    · have he:j=56:=Fin.ext h
      rw [he];rfl
    · have he:j=57:=Fin.ext h
      rw [he];rfl
    · have he:j=58:=Fin.ext h
      rw [he];rfl

theorem run (row : EquationRow.Input) : ∃ actual,
    LocalBitMultitape.run machine (budget row) (input row)=some actual ∧
    actual.final.tapes 66=frame (EquationRowRaw.source row) ∧
    (∀ i,actual.final.heads i=0) ∧ actual.steps≤budget row:=by
  obtain ⟨base,hbase,bt,bh,bs⟩:=Prepare.ready row
  let before:=TapeEmbedding.receipt (fun _ : Fin 4=>0) (fun _ : Fin 4=>[]) base
  have hf:=TapeEmbedding.run_embed Prepare.machine (fun _ : Fin 4=>0) (fun _ : Fin 4=>[])
    _ _ base hbase
  have bht:∀ i,before.final.heads i=0:=by
    intro i
    refine Fin.addCases (fun j=>?_) (fun j=>?_) i
    · exact (TapeEmbedding.receipt_heads_old _ _ _ j).trans (bh j)
    · exact TapeEmbedding.receipt_heads_new _ _ base j
  have btt:before.final.tapes=extend (Prepare.output row):=by
    funext i
    refine Fin.addCases (fun j=>?_) (fun j=>?_) i
    · simp only [extend,Fin.addCases_left]
      exact (TapeEmbedding.receipt_tapes_old _ _ _ j).trans (congrFun bt j)
    · simp only [extend,Fin.addCases_right]
      exact TapeEmbedding.receipt_tapes_new _ _ base j
  obtain ⟨child,ch,ct,chh,cs⟩:=Header.framed_run row
  obtain ⟨tail,ht,_,ts,th,tt,keep⟩:=RecoveryFocus.dock slots injective Header.framed
    (Header.framedBudget row) before.final.heads before.final.tapes _
    (fun j=>bht _) (fun j=>by rw [btt];exact projected_input row j) child ch
  have htail:runFrom last (Header.framedBudget row)
      (Composition.restart before.final last.start)=some tail:=ht
  have hj:=Composition.run_join first last _ _ _ before tail hf htail
  have hi:Composition.leftConfig _ (TapeEmbedding.config (fun _ : Fin 4=>0) (fun _ : Fin 4=>[])
      (initialConfiguration Prepare.machine (Prepare.input row)))=
      initialConfiguration machine (input row):=by
    apply configuration_ext
    · rfl
    · funext i
      refine Fin.addCases (fun j=>?_) (fun j=>?_) i
      all_goals simp [Composition.leftConfig,TapeEmbedding.config,initialConfiguration]
    · rfl
  rw [hi] at hj
  refine ⟨Composition.joinedReceipt before tail,hj,(tt 57).trans ct,?_,?_⟩
  · intro i
    change tail.final.heads i=0
    by_cases hs:∃ j,slots j=i
    · obtain ⟨j,rfl⟩:=hs
      exact (th j).trans (chh j)
    · exact (keep i (by simpa only [not_exists] using hs)).1.trans (bht i)
  · change base.steps+1+tail.steps≤_
    rw [ts]
    unfold budget
    omega

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Framed
