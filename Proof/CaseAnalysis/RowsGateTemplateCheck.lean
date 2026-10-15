import Proof.CaseAnalysis.RowsGateArityCheck
import Proof.MachineModel.OrdinaryUnaryTemplate

/-! Compare a decoded gate count with the already public source-domain
template at head one. Both inputs retain their original head positions;
the padded source arity is neither copied nor serialized. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsGateTemplateCheck
open LocalBitMultitape RecoveryExecution RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def machine : Machine 3 4 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==3
  rule := fun q bits => if q.val=0 then
      some ⟨1,fun _ => none,![.right,.stay,.stay]⟩
    else if q.val=1 then
      if bits 0 && bits 1 then some ⟨1,fun _ => none,![.right,.right,.stay]⟩
      else some ⟨2,![none,none,some (bits 0==bits 1)],![.left,.left,.stay]⟩
    else if q.val=2 then
      if bits 0 then some ⟨2,fun _ => none,![.left,.left,.stay]⟩
      else some ⟨3,fun _ => none,![.stay,.right,.stay]⟩
    else none
def data (n m : ℕ) (flag : List Bool) : Fin 3 → List Bool :=
  ![CompareMachine.word n,UnaryTemplate.tape m,flag]
def entry (n m : ℕ) : Configuration 3 4 := ⟨0,![0,1,0],data n m []⟩
def scan (n m j : ℕ) : Configuration 3 4 := ⟨1,![j+1,j+1,0],data n m []⟩
def back (n m j : ℕ) : Configuration 3 4 := ⟨2,![j,j,0],data n m [decide (n=m)]⟩
def final (n m : ℕ) : Configuration 3 4 := ⟨3,![0,1,0],data n m [decide (n=m)]⟩

theorem template_read (m j : ℕ) : readTapeBit (UnaryTemplate.tape m) (j+1)=decide (j < m) := by
  have he : UnaryTemplate.tape m=ZeroPadding.pad (m+2) (CompareMachine.word m) := by
    simp [UnaryTemplate.tape,ZeroPadding.pad,CompareMachine.word]
  rw [he,ZeroPadding.read_pad,CompareMachine.read_mark]

theorem first_step (n m : ℕ) : step machine (entry n m)=some (scan n m 0) := by
  apply congrArg some
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;> rfl
  · rfl

theorem scan_step (n m j : ℕ) (hn : j < n) (hm : j < m) :
    step machine (scan n m j)=some (scan n m (j+1)) := by
  simp [step,machine,scan,data,Configuration.scanned,template_read,hn,hm]
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;> rfl
  · rfl

theorem scan_run (n m j k : ℕ) (hn : j+k ≤ n) (hm : j+k ≤ m) :
    Timed machine k (scan n m j) (scan n m (j+k)) := by
  induction k generalizing j with
  | zero => simpa using Timed.refl machine (scan n m j)
  | succ k ih =>
    have h := Timed.step (by rfl) (scan_step n m j (by omega) (by omega))
      (ih (j+1) (by omega) (by omega))
    simpa only [Nat.add_assoc,Nat.add_comm 1 k] using h

theorem turn_step (n m : ℕ) : step machine (scan n m (min n m))=some (back n m (min n m)) := by
  by_cases he : n=m
  · subst m
    simp [step,machine,scan,data,Configuration.scanned]
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;> simp [applyAction,back,HeadMove.apply]
    · funext i;fin_cases i <;> simp [applyAction,back,data,writeTapeBit]
  · by_cases hl : n < m
    · simp [step,machine,scan,data,Configuration.scanned,template_read,min_eq_left hl.le,hl]
      apply configuration_ext
      · rfl
      · funext i;fin_cases i <;> simp [applyAction,back,HeadMove.apply]
      · funext i;fin_cases i <;> simp [applyAction,back,data,he,writeTapeBit]
    · have hr : m < n := by omega
      simp [step,machine,scan,data,Configuration.scanned,min_eq_right hr.le,hr]
      apply configuration_ext
      · rfl
      · funext i;fin_cases i <;> simp [applyAction,back,HeadMove.apply]
      · funext i;fin_cases i <;> simp [applyAction,back,data,he,writeTapeBit]

theorem back_step (n m j : ℕ) (hj : j < n) :
    step machine (back n m (j+1))=some (back n m j) := by
  simp [step,machine,back,data,Configuration.scanned,hj]
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;> simp [applyAction,HeadMove.apply]
  · rfl

theorem stop_step (n m : ℕ) : step machine (back n m 0)=some (final n m) := by
  simp [step,machine,back,data,Configuration.scanned]
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;> rfl
  · rfl

theorem back_run (n m j : ℕ) (hj : j ≤ n) :
    Timed machine (j+1) (back n m j) (final n m) := by
  induction j with
  | zero => exact Timed.single (by rfl) (stop_step n m)
  | succ j ih =>
    exact Timed.step (by rfl) (back_step n m j (by omega)) (ih (by omega))

theorem template_run (n m : ℕ) : ∃ r,
    runFrom machine (2*min n m+3) (entry n m)=some r ∧
      r.final=final n m ∧ r.steps=2*min n m+3 := by
  have middle := scan_run n m 0 (min n m) (by omega) (by omega)
  simp only [Nat.zero_add] at middle
  have whole := (((Timed.single (by rfl) (first_step n m)).trans middle).trans
    (Timed.single (by rfl) (turn_step n m))).trans (back_run n m (min n m) (by omega))
  have ht : 1+min n m+1+(min n m+1)=2*min n m+3 := by omega
  rw [ht] at whole
  exact whole.run (by rfl)

end NearCubicWires.RepairOrdinary.CloseoutRowsGateTemplateCheck
