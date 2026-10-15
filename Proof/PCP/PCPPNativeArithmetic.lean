import Proof.PCP.PCPPNativeFrame
import Proof.MachineModel.ClockUnarySum

/-! One physical scan computes the padded native size and its exact padding
from retained raw counters. The two inputs survive, and every head is reset. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeColdArithmetic
open LocalBitMultitape RecoveryRootRound RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def raw : Machine 4 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun q bits => if q.val=0 then
    if bits 0 || bits 1 then
      some ⟨0,![none,none,some true,if bits 1 then none else some true],
        ![.right,.right,.right,if bits 1 then .stay else .right]⟩
    else some ⟨1,fun _ => none,fun _ => .stay⟩
    else none
def cfg (phase : Fin 2) (n m k : ℕ) : Configuration 4 2 :=
  ⟨phase,![k,k,k,k-m],![List.replicate n true,List.replicate m true,
    List.replicate k true,List.replicate (k-m) true]⟩

theorem scan_step (n m k : ℕ) (hk : k < max n m) :
    step raw (cfg 0 n m k)=some (cfg 0 n m (k+1)) := by
  have hrn := ClockUnaryProduct.read_unary n k
  have hrm := ClockUnaryProduct.read_unary m k
  have hu : k < n ∨ k < m := by omega
  simp [step,raw,cfg,Configuration.scanned,hrn,hrm,hu]
  apply configuration_ext
  · rfl
  · funext i
    fin_cases i <;> simp [applyAction,HeadMove.apply]
    by_cases hm : k < m <;> simp [hm] <;> omega
  · funext i
    fin_cases i
    · rfl
    · rfl
    · change writeTapeBit (List.replicate k true) k true=List.replicate (k+1) true
      simp [List.replicate_add]
    · by_cases hm : k < m
      · have h0 : k-m=0 := by omega
        have h1 : k+1-m=0 := by omega
        simp [applyAction,hm,h0,h1]
      · have he : k+1-m=(k-m)+1 := by omega
        simp [applyAction,hm,he]

theorem stop_step (n m : ℕ) :
    step raw (cfg 0 n m (max n m))=some (cfg 1 n m (max n m)) := by
  have hn : ¬max n m < n := by omega
  have hm : ¬max n m < m := by omega
  simp [step,raw,cfg,Configuration.scanned,ClockUnaryProduct.read_unary,hn,hm]
  rfl

theorem scan_timed (n m k remaining : ℕ) (he : k+remaining=max n m) :
    Timed raw (remaining+1) (cfg 0 n m k) (cfg 1 n m (max n m)) := by
  induction remaining generalizing k with
  | zero =>
    have hk : k=max n m := by omega
    subst k
    exact Timed.single (by rfl) (stop_step n m)
  | succ remaining ih =>
    exact Timed.step (by rfl) (scan_step n m k (by omega))
      (ih (k+1) (by omega))

def input (n m : ℕ) : Fin 5 → List Bool :=
  ![List.replicate n true,List.replicate m true,[],[],[]]
def output (n m : ℕ) : Fin 5 → List Bool :=
  ![List.replicate n true,List.replicate m true,List.replicate (max n m) true,
    List.replicate (n-m) true,List.replicate (max n m+1) false]
def machine := Rewind.machine raw
def budget (n m : ℕ) := 2*max n m+4

theorem ready (n m : ℕ) :
    ReadyRun machine (budget n m) (input n m) (output n m) := by
  obtain ⟨base,hb,hf,hs⟩ := (scan_timed n m 0 (max n m) (by omega)).run (by rfl)
  have initial : initialConfiguration raw
      ![List.replicate n true,List.replicate m true,[],[]]=cfg 0 n m 0 := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [initialConfiguration,cfg]
    · simp [initialConfiguration,cfg]
  rw [←initial] at hb
  obtain ⟨r,hr,ht,hc,hh,hsteps,_⟩ := Rewind.Workspace.reset_workspace raw _ _ base hb 0
  have hi : Fin.addCases (motive := fun _ : Fin 5 => List Bool)
      ![List.replicate n true,List.replicate m true,[],[]]
      (fun _ : Fin 1 => List.replicate 0 false)=input n m := by
    funext i; fin_cases i <;> rfl
  have he : 2*base.steps+2=budget n m := by rw [hs]; unfold budget; omega
  rw [hi,he] at hr
  refine ⟨r,hr,?_,hh,by rw [hsteps,he]⟩
  funext i
  fin_cases i
  · simpa [hf,cfg,output] using ht 0
  · simpa [hf,cfg,output] using ht 1
  · simpa [hf,cfg,output] using ht 2
  · have hd : max n m-m=n-m := by omega
    simpa [hf,cfg,output,hd] using ht 3
  · simpa [hs,output] using hc

end NearCubicWires.RepairOrdinary.PCPPNativeColdArithmetic
