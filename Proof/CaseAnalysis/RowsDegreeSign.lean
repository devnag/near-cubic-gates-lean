import Proof.MachineModel.ClockFields
import Proof.Supplier.RowCoefficientEmit

/-! A fixed unary scan computes the binLift degree sign. It returns the
degree word and the sign with both heads reset, paying its recording tape. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsDegreeSign
open LocalBitMultitape RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def positive : ℕ → Bool
  | 0 => true
  | j+1 => !(positive j)
def phase (b : Bool) : Fin 3 := if b then 0 else 1
def raw : Machine 2 3 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==2
  rule := fun q bits => if q.val=2 then none else some
    (if bits 0 then ⟨if q.val=0 then 1 else 0,![none,none],![.right,.stay]⟩
     else ⟨2,![none,some (q.val==0)],![.stay,.stay]⟩)
def cfg (j k : ℕ) : Configuration 2 3 :=
  ⟨phase (positive k),![k,0],![List.replicate j true,[]]⟩
def finished (j : ℕ) : Configuration 2 3 :=
  ⟨2,![j,0],![List.replicate j true,[positive j]]⟩
def input2 (j : ℕ) : Fin 2 → List Bool := ![List.replicate j true,[]]
def machine := Rewind.machine raw
def input (j : ℕ) : Fin 3 → List Bool := ![List.replicate j true,[],[]]
def output (j : ℕ) : Fin 3 → List Bool :=
  ![List.replicate j true,[positive j],List.replicate (j+1) false]

theorem next_step (j k : ℕ) (hk : k<j) : step raw (cfg j k)=some (cfg j (k+1)) := by
  cases hp : positive k <;>
    simp [step,raw,cfg,phase,positive,Configuration.scanned,ClockUnaryProduct.read_unary,hk,hp]
  all_goals apply configuration_ext
  all_goals first | rfl | (funext i; fin_cases i <;> simp [applyAction,HeadMove.apply])

theorem stop_step (j : ℕ) : step raw (cfg j j)=some (finished j) := by
  cases hp : positive j <;>
    simp [step,raw,cfg,phase,Configuration.scanned,ClockUnaryProduct.read_unary,hp]
  all_goals apply configuration_ext
  all_goals first | rfl | (funext i; fin_cases i <;> simp [applyAction,finished,HeadMove.apply,writeTapeBit,hp])

theorem path (j k remaining : ℕ) (h : k+remaining=j) :
    Timed raw (remaining+1) (cfg j k) (finished j) := by
  induction remaining generalizing k with
  | zero =>
    have hk : k=j := by omega
    subst k
    exact Timed.single (by cases hp : positive j <;> simp [raw,cfg,phase,hp]) (stop_step j)
  | succ remaining ih =>
    have hn : raw.halted (cfg j k).control=false := by
      cases hp : positive k <;> simp [raw,cfg,phase,hp]
    have first := Timed.single hn (next_step j k (by omega))
    have tail := ih (k+1) (by omega)
    simpa only [Nat.succ_eq_add_one,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using first.trans tail

theorem raw_run (j : ℕ) : ∃ r,run raw (j+1) (input2 j)=some r ∧
    r.final=finished j ∧ r.steps=j+1 := by
  obtain ⟨r,hr,hf,hs⟩ := (path j 0 j (by omega)).run (by rfl)
  have hi : cfg j 0=initialConfiguration raw (input2 j) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · rfl
  rw [hi] at hr
  exact ⟨r,hr,hf,hs⟩

theorem sign_ready (j : ℕ) :
    RecoveryRootRound.ReadyRun machine (2*j+4) (input j) (output j) := by
  obtain ⟨base,hb,hf,hs⟩ := raw_run j
  obtain ⟨r,hr,rt,rl,rh,rs,_⟩ := Rewind.Workspace.reset_workspace raw _ _ base hb 0
  have hi : Fin.addCases (m := 2) (n := 1) (motive := fun _ => List Bool)
      (input2 j) (fun _ => List.replicate 0 false)=input j := by
    funext i; fin_cases i <;> simp [input,input2,Fin.addCases]
  have htime : 2*base.steps+2=2*j+4 := by omega
  rw [hi,htime] at hr
  refine ⟨r,hr,?_,rh,rs.trans htime⟩
  funext i
  fin_cases i
  · simpa [hf,finished,output] using rt 0
  · simpa [hf,finished,output] using rt 1
  · simpa [hs,output] using rl

theorem signed_power (j : ℕ) :
    (-2 : ℤ)^j=if positive j then (2 : ℤ)^j else -((2 : ℤ)^j) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [pow_succ,ih]
    cases hp : positive j <;> simp [positive,hp,pow_succ]

theorem power_sign (j : ℕ) : decide ((-2 : ℤ)^j<0)=!(positive j) := by
  rw [signed_power]
  have hp : (0 : ℤ)<2^j := by positivity
  cases positive j <;> simp [hp,not_lt_of_ge hp.le]

end NearCubicWires.RepairOrdinary.CloseoutRowsDegreeSign
