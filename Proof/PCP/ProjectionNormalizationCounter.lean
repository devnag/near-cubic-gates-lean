import Proof.PCP.ProjectionNormalizationDifference

/-! The physical raw R/Q outputs of dimension production are converted to
sentinel counters by a paid product with a physically written unary unit. -/
namespace NearCubicWires.RepairSource.ProjectionNormalization.Counter
open LocalBitMultitape RepairOrdinary RecoveryExecution VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def input (n : ℕ) : Fin 4 → List Bool := ![List.replicate n true,[],[],[]]
def boot : Machine 4 3 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==2
  rule := fun q _ => if q.val=0 then some ⟨1,
    fun i => if i=1 then some false else none,fun i => if i=1 then .right else .stay⟩
    else if q.val=1 then some ⟨2,
      fun i => if i=1 then some true else none,fun i => if i=1 then .left else .stay⟩ else none
def machine := Composition.machine boot Product.reset
def budget (n : ℕ) := 10*n+13

theorem boot_run (n : ℕ) :
    ∃ r,run boot 2 (input n)=some r ∧ r.final.heads=(fun _ => 0) ∧
      r.final.tapes=Product.input n 1 ∧ r.steps=2 := by
  let middle : Configuration 4 3 := ⟨1,![0,1,0,0],![List.replicate n true,[false],[],[]]⟩
  let last : Configuration 4 3 := ⟨2,(fun _ => 0),Product.input n 1⟩
  have h0 : step boot (initialConfiguration boot (input n))=some middle := by
    simp [step,boot,initialConfiguration]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  have h1 : step boot middle=some last := by
    simp [step,boot,middle]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  obtain ⟨r,hr,hf,hs⟩ := ((Timed.single (by rfl) h0).trans (Timed.single (by rfl) h1)).run (by rfl)
  exact ⟨r,hr,by rw [hf],by rw [hf],hs⟩

theorem counter_run (n : ℕ) :
    ∃ r,run machine (budget n) (input n)=some r ∧
      r.final.tapes 0=List.replicate n true ∧ r.final.tapes 2=CompareMachine.word n ∧
      (∀ i,r.final.heads i=0) ∧ r.steps=budget n := by
  obtain ⟨a,ha,hah,hat,has⟩ := boot_run n
  obtain ⟨base,hbase,hout,hbs⟩ := Product.raw_run n 1
  obtain ⟨b,hb,hbt,_,hbh,hbs',_⟩ := Rewind.Workspace.reset_workspace Product.raw _ _ base hbase 0
  have he : Composition.restart a.final Product.reset.start=initialConfiguration Product.reset (Product.input n 1) := by
    apply configuration_ext
    · rfl
    · exact hah
    · exact hat
  have hb' : runFrom Product.reset (2*base.steps+2) (Composition.restart a.final Product.reset.start)=some b := by
    rw [he]
    exact hb
  have h := Composition.run_join boot Product.reset 2 (2*base.steps+2) _ a b ha hb'
  have ht : 2+1+(2*base.steps+2)=budget n := by rw [hbs]; dsimp [budget]; ring
  rw [ht] at h
  refine ⟨Composition.joinedReceipt a b,h,?_,?_,hbh,?_⟩
  · exact (hbt 0).trans (by rw [hout]; rfl)
  · exact (hbt 2).trans (by rw [hout]; simp)
  · change a.steps+1+b.steps=_
    rw [has,hbs']
    exact ht

end NearCubicWires.RepairSource.ProjectionNormalization.Counter
