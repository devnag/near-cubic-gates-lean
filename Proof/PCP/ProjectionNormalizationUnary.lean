import Proof.PCP.ProjectionNormalizationUnaryCore

/-! Cold binary-to-unary dimension production. Blank work is initialized by
real writes, the binary predecessor drives all marks, and a paid rewind plus
one move establishes the sentinel-counter head1 endpoint. -/
namespace NearCubicWires.RepairSource.ProjectionNormalization.Unary
open LocalBitMultitape RepairOrdinary RecoveryExecution RadixSemantics VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def input4 (bits : List Bool) : Fin 4 → List Bool := ![frame bits,[],[],[]]
def input (bits : List Bool) : Fin 5 → List Bool :=
  Fin.addCases (motive := fun _ : Fin (4+1) => List Bool) (input4 bits) (fun _ : Fin 1 => [])
def boot : Machine 4 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun q _ => if q.val=0 then some ⟨1,![none,some false,none,some false],![.stay,.stay,.stay,.right]⟩ else none
noncomputable def raw := Composition.machine boot UnaryCore.machine
noncomputable def reset := Rewind.machine raw
def advance : Machine 5 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun q _ => if q.val=0 then some ⟨1,fun _ => none,fun i => if i=3 then .right else .stay⟩ else none
noncomputable def machine := Composition.machine reset advance
def rawBudget (bits : List Bool) := value bits*(4*bits.length+7)+4*bits.length+7
def budget (bits : List Bool) := 24*(value bits+1)*(bits.length+1)

theorem boot_run (bits : List Bool) :
    ∃ r,run boot 1 (input4 bits)=some r ∧ r.final=UnaryCore.cfg 1 bits false 0 [false] ∧ r.steps=1 := by
  have h : step boot (initialConfiguration boot (input4 bits))=some (UnaryCore.cfg 1 bits false 0 [false]) := by
    simp [step,boot,initialConfiguration]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  exact (Timed.single (by rfl) h).run (by rfl)

theorem raw_run (bits : List Bool) :
    ∃ r,run raw (rawBudget bits) (input4 bits)=some r ∧
      r.final.tapes 3=CompareMachine.word (value bits) ∧ r.steps=rawBudget bits := by
  obtain ⟨a,ha,haf,hat⟩ := boot_run bits
  obtain ⟨finalBits,_,hloop⟩ := UnaryCore.loop (value bits) bits [false] false 0 rfl
  obtain ⟨b,hb,hbf,hbt⟩ := hloop.run
    (by simp [UnaryCore.machine,UnaryCore.stopped,UnaryCore.cfg,RecoveryCalls.machine,RecoveryCalls.controlCode])
  have hmid : Composition.restart a.final UnaryCore.machine.start=UnaryCore.nodeCfg 0 bits false 0 [false] := by
    rw [haf]
    rfl
  rw [←hmid] at hb
  have h := Composition.run_join boot UnaryCore.machine 1 _ _ a b ha hb
  have he : 1+1+(value bits*(4*bits.length+7)+4*bits.length+5)=rawBudget bits := by
    dsimp only [rawBudget]
    omega
  rw [he] at h
  refine ⟨Composition.joinedReceipt a b,h,?_,?_⟩
  · change b.final.tapes 3=_
    rw [hbf]
    rfl
  · change a.steps+1+b.steps=rawBudget bits
    rw [hat,hbt,←he]

theorem advance_run (tapes : Fin 5 → List Bool) :
    ∃ r,run advance 1 tapes=some r ∧ r.final.tapes=tapes ∧
      (∀ i,r.final.heads i=if i=3 then 1 else 0) ∧ r.steps=1 := by
  let final : Configuration 5 2 := ⟨1,(fun i => if i=3 then 1 else 0),tapes⟩
  have h : step advance (initialConfiguration advance tapes)=some final := by
    simp [step,advance,initialConfiguration]
    apply configuration_ext
    · rfl
    · funext i; by_cases hi : i=3 <;> simp [applyAction,HeadMove.apply,final,hi]
    · rfl
  obtain ⟨r,hr,hf,hs⟩ := (Timed.single (by rfl) h).run (by rfl)
  exact ⟨r,hr,by rw [hf],by intro i; rw [hf],hs⟩

theorem unary_run (bits : List Bool) :
    ∃ r,run machine (budget bits) (input bits)=some r ∧
      r.final.tapes 3=CompareMachine.word (value bits) ∧
      (∀ i,r.final.heads i=if i=3 then 1 else 0) ∧ r.steps≤budget bits := by
  obtain ⟨base,hbase,hout,hbs⟩ := raw_run bits
  obtain ⟨a,ha,hat,_,hah,has,_⟩ := Rewind.Workspace.reset_workspace raw _ _ base hbase 0
  obtain ⟨b,hb,hbt,hbh,hbs'⟩ := advance_run a.final.tapes
  have hmid : Composition.restart a.final advance.start=initialConfiguration advance a.final.tapes := by
    apply configuration_ext
    · rfl
    · exact funext hah
    · rfl
  unfold run at hb
  rw [←hmid] at hb
  have h := Composition.run_join reset advance (2*base.steps+2) 1 _ a b ha hb
  have hbound : (2*base.steps+2)+1+1≤budget bits := by
    rw [hbs]
    dsimp only [rawBudget,budget]
    nlinarith
  have hm := runFrom_moreFuel machine _ (budget bits-((2*base.steps+2)+1+1))
    _ (Composition.joinedReceipt a b) h
  rw [Nat.add_sub_of_le hbound] at hm
  refine ⟨Composition.joinedReceipt a b,hm,?_,?_,?_⟩
  · change b.final.tapes 3=_
    rw [hbt]
    exact (hat 3).trans hout
  · intro i
    exact hbh i
  · change a.steps+1+b.steps≤budget bits
    rw [has,hbs']
    exact hbound

end NearCubicWires.RepairSource.ProjectionNormalization.Unary
