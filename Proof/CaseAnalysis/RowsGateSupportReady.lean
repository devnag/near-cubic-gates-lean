import Proof.CaseAnalysis.RowsGateSupportLoop

/-! The retained native weights, bitmap and actual weight-count word feed
the whole support pass directly. A paid bootstrap supplies its flag and
driver head, and a paid rewind restores every final physical head. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsGateSupport
open LocalBitMultitape RecoveryExecution RadixSemantics
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def input (fields : List (Bool×List Bool)) (membership : List Bool) : Fin 6→List Bool:=
  ![fields.flatMap fieldWord,[],[],frame membership,[],CompareMachine.word fields.length]
def bootstrap : Machine 6 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==1
  rule:=fun q _=>if q.val=0 then
    some ⟨1,fun i=>if i=4 then some true else none,fun i=>if i=5 then .right else .stay⟩ else none
def booted (fields : List (Bool×List Bool)) (membership : List Bool) : Configuration 6 2:=
  ⟨1,![0,0,0,0,0,1],![fields.flatMap fieldWord,[],[],frame membership,[true],CompareMachine.word fields.length]⟩
noncomputable def preparedMachine (compressed : Bool):=Composition.machine bootstrap (loop compressed)
def preparedBudget (w count : ℕ):=loopBudget w count+2
noncomputable def readyMachine (compressed : Bool):=Rewind.machine (preparedMachine compressed)
def readyInput (fields : List (Bool×List Bool)) (membership : List Bool) : Fin 7→List Bool:=
  Fin.addCases (motive:=fun _ : Fin (6+1)=>List Bool) (input fields membership) (fun _=>[])
def readyBudget (w count : ℕ):=2*preparedBudget w count+2

theorem bootstrap_run (fields : List (Bool×List Bool)) (membership : List Bool) :
    ∃ actual,run bootstrap 1 (input fields membership)=some actual ∧
      actual.final=booted fields membership ∧ actual.steps=1:=by
  have hs:step bootstrap (initialConfiguration bootstrap (input fields membership))=some (booted fields membership):=by
    simp [step,bootstrap,input,initialConfiguration]
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
  exact (Timed.single (by rfl) hs).run (by rfl)

theorem prepared_run (compressed : Bool) (fields : List (Bool×List Bool))
    (membership : List Bool) (w : ℕ) (hw : ∀ field∈fields,field.2.length≤w) :
    ∃ actual,run (preparedMachine compressed) (preparedBudget w fields.length) (input fields membership)=some actual ∧
      actual.steps≤preparedBudget w fields.length ∧
      actual.final.tapes 0=fields.flatMap fieldWord ∧
      actual.final.tapes 2=(List.range fields.length).flatMap (emission compressed fields membership) ∧
      actual.final.tapes 3=frame membership ∧
      actual.final.tapes 4=[validity fields membership true fields.length] ∧
      actual.final.tapes 5=CompareMachine.word fields.length:=by
  obtain ⟨a,ha,af,as⟩:=bootstrap_run fields membership
  obtain ⟨b,hb,bf,bs⟩:=loop_run compressed fields membership [] [] [] [] true w hw
  have hi:RepeatMachine.cfg 0 (entry fields membership [] [] [] true 0 []) fields.length 1=
      Composition.restart a.final (loop compressed).start:=by
    rw [af]
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> simp [RepeatMachine.cfg,controlConfig,entry,cfg,scratch,validity,booted,
        TapeEmbedding.config,Composition.restart,Fin.addCases]
  rw [hi] at hb
  have h:=Composition.run_join bootstrap (loop compressed) _ _ _ a b ha hb
  have he:1+1+loopBudget w fields.length=preparedBudget w fields.length:=by unfold preparedBudget;omega
  rw [he] at h
  refine ⟨Composition.joinedReceipt a b,h,?_,?_,?_,?_,?_,?_⟩
  · change a.steps+1+b.steps≤_
    unfold preparedBudget
    omega
  all_goals change b.final.tapes _=_
  all_goals rw [bf]
  all_goals simp [RepeatMachine.cfg,controlConfig,entry,cfg,TapeEmbedding.config,Fin.addCases]

theorem ready_run (compressed : Bool) (fields : List (Bool×List Bool))
    (membership : List Bool) (w : ℕ) (hw : ∀ field∈fields,field.2.length≤w) :
    ∃ output,ClockJoin.ReadyRun (readyMachine compressed) (readyBudget w fields.length)
      (readyInput fields membership) output ∧
      output 0=fields.flatMap fieldWord ∧
      output 2=(List.range fields.length).flatMap (emission compressed fields membership) ∧
      output 3=frame membership ∧ output 5=CompareMachine.word fields.length ∧
      (readTapeBit (output 4) 0=true ↔
        ∀ k<fields.length,membership.getD k false=false → value (fields.getD k (false,[])).2=0):=by
  obtain ⟨a,ha,as,a0,a2,a3,a4,a5⟩:=prepared_run compressed fields membership w hw
  obtain ⟨r,hr,rt,_,rh,rs,_⟩:=Rewind.Workspace.reset_workspace (preparedMachine compressed) _ _ a ha 0
  have hb:2*a.steps+2≤readyBudget w fields.length:=by unfold readyBudget;omega
  have more:=run_moreFuel (readyMachine compressed) _ (readyBudget w fields.length-(2*a.steps+2))
    (readyInput fields membership) r hr
  rw [Nat.add_sub_of_le hb] at more
  refine ⟨r.final.tapes,⟨r,more,rfl,rh,rs.le.trans hb⟩,
    (rt 0).trans a0,(rt 2).trans a2,(rt 3).trans a3,(rt 5).trans a5,?_⟩
  change readTapeBit (r.final.tapes ((4 : Fin 6).castAdd 1)) 0=true ↔_
  rw [rt,a4]
  change validity fields membership true fields.length=true ↔_
  rw [validity_iff]
  simp only [true_and]

end NearCubicWires.RepairOrdinary.CloseoutRowsGateSupport
