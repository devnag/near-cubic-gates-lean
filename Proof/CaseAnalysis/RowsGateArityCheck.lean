import Proof.PCP.VerifierDecodingCompare
import Proof.Amplification.RecoveryReadyCalls
import Proof.MachineModel.ClockJoin

/-! Compare a retained decoder count directly with the actual source's
raw unary arity. The different starting offsets are handled by one paid
head move; neither operand is serialized or expanded again. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsGateArityCheck
open LocalBitMultitape RecoveryExecution
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def raw : Machine 3 3 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==2
  rule := fun q bits => if q.val=0 then
      some ⟨1,fun _ => none,![.right,.stay,.stay]⟩
    else if q.val=1 then
      if bits 0 && bits 1 then some ⟨1,fun _ => none,![.right,.right,.stay]⟩
      else some ⟨2,![none,none,some (bits 0==bits 1)],fun _ => .stay⟩
    else none
def data (n m : ℕ) : Fin 3 → List Bool := ![CompareMachine.word n,List.replicate m true,[]]
def scan (n m j : ℕ) : Configuration 3 3 := ⟨1,![j+1,j,0],data n m⟩
def final (n m : ℕ) : Configuration 3 3 :=
  ⟨2,![min n m+1,min n m,0],![CompareMachine.word n,List.replicate m true,[decide (n=m)]]⟩

theorem first_step (n m : ℕ) : step raw (initialConfiguration raw (data n m))=some (scan n m 0) := by
  apply congrArg some
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;> rfl
  · rfl

theorem scan_step (n m j : ℕ) (hn : j < n) (hm : j < m) :
    step raw (scan n m j)=some (scan n m (j+1)) := by
  simp [step,raw,scan,data,Configuration.scanned,CompareMachine.read_mark,SliceMachine.read_unary,hn,hm]
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;> rfl
  · rfl

theorem scan_run (n m j k : ℕ) (hn : j+k ≤ n) (hm : j+k ≤ m) :
    Timed raw k (scan n m j) (scan n m (j+k)) := by
  induction k generalizing j with
  | zero => simpa using Timed.refl raw (scan n m j)
  | succ k ih =>
    have h := Timed.step (by rfl) (scan_step n m j (by omega) (by omega))
      (ih (j+1) (by omega) (by omega))
    simpa only [Nat.add_assoc,Nat.add_comm 1 k] using h

theorem last_step (n m : ℕ) : step raw (scan n m (min n m))=some (final n m) := by
  by_cases he : n=m
  · subst m
    simp [step,raw,scan,data,Configuration.scanned,SliceMachine.read_unary]
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;> simp [applyAction,final,HeadMove.apply]
    · funext i;fin_cases i <;> simp [applyAction,final,writeTapeBit]
  · by_cases hl : n < m
    · simp [step,raw,scan,data,Configuration.scanned,SliceMachine.read_unary,min_eq_left hl.le,hl]
      apply configuration_ext
      · rfl
      · funext i;fin_cases i <;> simp [applyAction,final,min_eq_left hl.le,HeadMove.apply]
      · funext i;fin_cases i <;> simp [applyAction,final,he,writeTapeBit]
    · have hr : m < n := by omega
      simp [step,raw,scan,data,Configuration.scanned,SliceMachine.read_unary,min_eq_right hr.le,hr]
      apply configuration_ext
      · rfl
      · funext i;fin_cases i <;> simp [applyAction,final,min_eq_right hr.le,HeadMove.apply]
      · funext i;fin_cases i <;> simp [applyAction,final,he,writeTapeBit]

theorem raw_run (n m : ℕ) : ∃ r,
    run raw (min n m+2) (data n m)=some r ∧ r.final=final n m ∧ r.steps=min n m+2 := by
  have middle := scan_run n m 0 (min n m) (by omega) (by omega)
  simp only [Nat.zero_add] at middle
  have whole := ((Timed.single (by rfl) (first_step n m)).trans middle).trans
    (Timed.single (by rfl) (last_step n m))
  have ht : 1+min n m+1=min n m+2 := by omega
  rw [ht] at whole
  exact whole.run (by rfl)

def machine := Rewind.machine raw
def input (n m : ℕ) : Fin 4 → List Bool := ![CompareMachine.word n,List.replicate m true,[],[]]
def output (n m : ℕ) : Fin 4 → List Bool :=
  ![CompareMachine.word n,List.replicate m true,[decide (n=m)],List.replicate (min n m+2) false]

theorem arity_run (n m : ℕ) : ClockJoin.ReadyRun machine (2*min n m+6) (input n m) (output n m) := by
  obtain ⟨base,hb,bf,bs⟩ := raw_run n m
  obtain ⟨r,hr,rt,rc,rh,rs,_⟩ := Rewind.Workspace.reset_workspace raw _ _ base hb 0
  have he : 2*base.steps+2=2*min n m+6 := by omega
  rw [he] at hr
  refine ⟨r,?_,?_,rh,by omega⟩
  · convert hr using 2
    all_goals first | rfl | (funext i;fin_cases i <;> rfl)
  · funext i
    fin_cases i
    · exact (rt 0).trans (by rw [bf];rfl)
    · exact (rt 1).trans (by rw [bf];rfl)
    · exact (rt 2).trans (by rw [bf];rfl)
    · simpa [bs,output] using rc

end NearCubicWires.RepairOrdinary.CloseoutRowsGateArityCheck
