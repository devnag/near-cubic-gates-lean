import Proof.CaseAnalysis.RowsEstimatorTail

/-! The scanner's two actual unary outputs feed the existing three-header
printer and the literal parity/cut append. The same checked outer framer
then supplies EquationRowRaw's original source codec. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Header
open LocalBitMultitape RecoveryExecution MatrixScoreBatch
open RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def values (row : EquationRow.Input) : Fin 3→ℕ:=![row.d,row.p,row.cuts.length]
def stream (row : EquationRow.Input):=row.cuts.flatMap (cutWord row.p)
def extra (row : EquationRow.Input) : Fin 3→List Bool:=
  ![stream row,List.replicate (stream row).length true,[row.odd]]
def input (row : EquationRow.Input) : Fin 55→List Bool:=
  fun i=>Fin.addCases (m:=52) (n:=3) (motive:=fun _=>List Bool)
    (EquationHeaders.input (values row) []) (extra row) i
def slots : Fin 4→Fin 55:=![52,53,54,51]
noncomputable def first:=TapeEmbedding.machine 3 EquationHeaders.machine
noncomputable def last:=RecoveryFocus.machine slots Tail.machine
noncomputable def machine:=Composition.machine first last
def budget (row : EquationRow.Input):=EquationHeaders.budget (values row)+1+(stream row).length+2

theorem source_eq (row : EquationRow.Input) :
    EquationHeaders.output (values row)++row.odd::stream row=EquationRowRaw.source row:=by
  simp [EquationHeaders.output,values,stream,EquationRowRaw.source,EquationHeaderRead.word,
    EquationHeaderRead.header,List.append_assoc,EquationRowCuts.stream]

theorem raw_run (row : EquationRow.Input) : ∃ actual,
    run machine (budget row) (input row)=some actual ∧
    actual.final.tapes 51=EquationRowRaw.source row ∧
    actual.final.heads 51=(EquationRowRaw.source row).length ∧
    actual.steps≤budget row:=by
  obtain ⟨base,hbase,bt,bh,bs⟩:=EquationHeaders.headers_run (values row) []
  have hi:EquationHeaders.entry (values row) []=
      initialConfiguration EquationHeaders.machine (EquationHeaders.input (values row) []):=by
    apply configuration_ext
    · rfl
    · funext i;simp [EquationHeaders.entry,EquationHeaders.heads,initialConfiguration]
    · rfl
  rw [hi] at hbase
  simp only [List.nil_append] at bt bh
  let before:=TapeEmbedding.receipt (fun _ : Fin 3=>0) (extra row) base
  have hfirst:=TapeEmbedding.run_embed EquationHeaders.machine (fun _ : Fin 3=>0) (extra row)
    _ _ base hbase
  obtain ⟨child,ch,cf,cs⟩:=Tail.append_run (stream row) (EquationHeaders.output (values row)) row.odd
  have hd:RecoveryFocus.config slots before.final.heads before.final.tapes
      (Tail.cfg 0 (stream row) row.odd 0 (EquationHeaders.output (values row)))=
      Composition.restart before.final last.start:=by
    apply WilliamsSourceCrop.focus_same
    · intro j;fin_cases j
      · rfl
      · rfl
      · rfl
      · exact (TapeEmbedding.receipt_heads_old _ _ base 51).trans bh
    · intro j;fin_cases j
      · rfl
      · rfl
      · rfl
      · exact (TapeEmbedding.receipt_tapes_old _ _ base 51).trans bt
  obtain ⟨focused,hf,ff,fs⟩:=RecoveryFocus.run_config slots (by decide) Tail.machine
    before.final.heads before.final.tapes _ _ child ch
  rw [hd] at hf
  have hj:=Composition.run_join first last _ _ _ before focused hfirst hf
  have hin:Composition.leftConfig _ (TapeEmbedding.config (fun _ : Fin 3=>0) (extra row)
      (initialConfiguration EquationHeaders.machine (EquationHeaders.input (values row) [])))=
      initialConfiguration machine (input row):=by
    apply configuration_ext
    · rfl
    · funext i
      refine Fin.addCases (fun j=>?_) (fun j=>?_) i
      all_goals simp [Composition.leftConfig,TapeEmbedding.config,initialConfiguration]
    · rfl
  rw [hin] at hj
  have ht:focused.final.tapes 51=EquationRowRaw.source row:=by
    change focused.final.tapes (slots 3)=_
    rw [ff]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots (by decide),cf,Tail.cfg]
    exact source_eq row
  have hh:focused.final.heads 51=(EquationRowRaw.source row).length:=by
    change focused.final.heads (slots 3)=_
    rw [ff]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots (by decide),cf,Tail.cfg]
    exact congrArg List.length (source_eq row)
  have hfuel:EquationHeaders.budget (values row)+1+((stream row).length+2)=budget row:=by
    unfold budget;omega
  rw [hfuel] at hj
  refine ⟨Composition.joinedReceipt before focused,hj,ht,hh,?_⟩
  change base.steps+1+focused.steps≤_
  rw [fs,cs]
  unfold budget
  omega

theorem forward : CursorRestore.NoLeft machine 51:=
  CursorRestore.composition_forward first last 51
    (EquationRowCuts.embedded_forward 3 EquationHeaders.machine 51 EquationRowRaw.headers_forward)
    (CursorRestore.focus_forward slots (by decide) Tail.machine 3 Tail.forward)

noncomputable def framed:=AppendOutputFrame.machine machine 51
def framedInput (row : EquationRow.Input):=AppendOutputFrame.input (input row)
def framedBudget (row : EquationRow.Input):=6*budget row+7

theorem framed_run (row : EquationRow.Input) : ∃ actual,
    run framed (framedBudget row) (framedInput row)=some actual ∧
    actual.final.tapes 57=frame (EquationRowRaw.source row) ∧
    (∀ i,actual.final.heads i=0) ∧ actual.steps≤framedBudget row:=by
  obtain ⟨base,hb,bt,bh,bs⟩:=raw_run row
  have hlen:(EquationRowRaw.source row).length≤base.steps:=by
    obtain ⟨hp,_⟩:=prefix_of_run machine (budget row) (initialConfiguration machine (input row)) base hb
    have h:=SelectiveReset.prefix_head hp 51
    rw [bh] at h
    simpa only [initialConfiguration,Nat.zero_add] using h
  obtain ⟨actual,ha,atape,ah,ast⟩:=AppendOutputFrame.frame_run machine 51 forward
    (budget row) (input row) base hb (EquationRowRaw.source row) bt bh
  have ht:2*base.steps+4*(EquationRowRaw.source row).length+7≤framedBudget row:=by
    unfold framedBudget;omega
  have hm:=run_moreFuel framed _
    (framedBudget row-(2*base.steps+4*(EquationRowRaw.source row).length+7)) _ actual ha
  rw [Nat.add_sub_of_le ht] at hm
  exact ⟨actual,hm,atape,ah,ast.trans ht⟩

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Header
