import Proof.PCP.ProjectionNormalizationDedupBytes
import Proof.MachineModel.ClockUnaryProduct

/-! Paid sentinel product for the query-padding and total-field drivers.
The first operand is the actual raw unary R produced by dimensions. -/
namespace NearCubicWires.RepairSource.ProjectionNormalization.Product
open LocalBitMultitape RepairOrdinary RecoveryExecution VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def boot : Machine 3 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun q _ => if q.val=0 then
    some ⟨1,![none,none,some false],![.stay,.stay,.right]⟩ else none
def input3 (d e : ℕ) : Fin 3 → List Bool := ![List.replicate d true,CompareMachine.word e,[]]
def raw := Composition.machine boot ClockUnaryProduct.raw
def reset := Rewind.machine raw
def advance : Machine 4 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun q _ => if q.val=0 then some ⟨1,fun _ => none,
    fun i => if i=1 ∨ i=2 then .right else .stay⟩ else none
def machine := Composition.machine reset advance
def input (d e : ℕ) : Fin 4 → List Bool :=
  Fin.addCases (motive := fun _ : Fin (3+1) => List Bool) (input3 d e) (fun _ : Fin 1 => [])
def budget (d e : ℕ) := 2*(d*(2*e+3)+4)+4

theorem raw_run (d e : ℕ) :
    ∃ r,run raw (d*(2*e+3)+4) (input3 d e)=some r ∧
      r.final.tapes=![List.replicate d true,CompareMachine.word e,CompareMachine.word (d*e)] ∧
      r.steps=d*(2*e+3)+4 := by
  let middle : Configuration 3 2 := ⟨1,![0,0,1],![List.replicate d true,CompareMachine.word e,[false]]⟩
  have hs : step boot (initialConfiguration boot (input3 d e))=some middle := by
    simp [step,boot,initialConfiguration]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  obtain ⟨a,ha,haf,hat⟩ := (Timed.single (by rfl) hs).run (by rfl)
  have hs' : step ClockUnaryProduct.raw (ClockUnaryProduct.config 0 d e 0 0 [false])=
      some (ClockUnaryProduct.config 1 d e 0 1 [false]) := by
    simp [step,ClockUnaryProduct.raw,ClockUnaryProduct.config]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  have hp : Timed ClockUnaryProduct.raw (d*(2*e+3)+1)
      (ClockUnaryProduct.config 1 d e 0 1 [false])
      (ClockUnaryProduct.config 4 d e d 1 (CompareMachine.word (d*e))) := by
    exact ⟨_,ClockUnaryProduct.loop_prefix d e 0 d [false] (by simp)⟩
  obtain ⟨b,hb,hbf,hbt⟩ := ((Timed.single (by rfl) hs').trans hp).run (by rfl)
  have he : Composition.restart a.final ClockUnaryProduct.raw.start=ClockUnaryProduct.config 0 d e 0 0 [false] := by
    rw [haf]
    rfl
  rw [←he] at hb
  have h := Composition.run_join boot ClockUnaryProduct.raw 1 _ _ a b ha hb
  have ht : 1+1+(1+(d*(2*e+3)+1))=d*(2*e+3)+4 := by omega
  rw [ht] at h
  refine ⟨Composition.joinedReceipt a b,h,?_,?_⟩
  · change b.final.tapes=_
    rw [hbf]
    rfl
  · change a.steps+1+b.steps=_
    omega

theorem advance_run (tapes : Fin 4 → List Bool) :
    ∃ r,run advance 1 tapes=some r ∧ r.final.tapes=tapes ∧
      (∀ i,r.final.heads i=if i=1 ∨ i=2 then 1 else 0) ∧ r.steps=1 := by
  let f : Configuration 4 2 := ⟨1,(fun i => if i=1 ∨ i=2 then 1 else 0),tapes⟩
  have h : step advance (initialConfiguration advance tapes)=some f := by
    simp [step,advance,initialConfiguration]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · rfl
  obtain ⟨r,hr,hf,hs⟩ := (Timed.single (by rfl) h).run (by rfl)
  exact ⟨r,hr,by rw [hf],by intro i; rw [hf],hs⟩

theorem product_run (d e : ℕ) :
    ∃ r,run machine (budget d e) (input d e)=some r ∧
      r.final.tapes 0=List.replicate d true ∧ r.final.tapes 1=CompareMachine.word e ∧
      r.final.tapes 2=CompareMachine.word (d*e) ∧
      (∀ i,r.final.heads i=if i=1 ∨ i=2 then 1 else 0) ∧ r.steps=budget d e := by
  obtain ⟨base,hbase,hout,hbs⟩ := raw_run d e
  obtain ⟨a,ha,hat,_,hah,has,_⟩ := Rewind.Workspace.reset_workspace raw _ _ base hbase 0
  obtain ⟨b,hb,hbt,hbh,hbs'⟩ := advance_run a.final.tapes
  have he : Composition.restart a.final advance.start=initialConfiguration advance a.final.tapes := by
    apply configuration_ext
    · rfl
    · exact funext hah
    · rfl
  unfold run at hb
  rw [←he] at hb
  have h := Composition.run_join reset advance (2*base.steps+2) 1 _ a b ha hb
  have ht : (2*base.steps+2)+1+1=budget d e := by rw [hbs]; rfl
  rw [ht] at h
  refine ⟨Composition.joinedReceipt a b,h,?_,?_,?_,hbh,?_⟩
  · change b.final.tapes 0=_
    rw [hbt]
    exact (hat 0).trans (by rw [hout]; rfl)
  · change b.final.tapes 1=_
    rw [hbt]
    exact (hat 1).trans (by rw [hout]; rfl)
  · change b.final.tapes 2=_
    rw [hbt]
    exact (hat 2).trans (by rw [hout]; rfl)
  · change a.steps+1+b.steps=_
    rw [has,hbs']
    exact ht

end NearCubicWires.RepairSource.ProjectionNormalization.Product
