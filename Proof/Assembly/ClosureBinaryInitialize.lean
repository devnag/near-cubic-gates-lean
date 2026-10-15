import Proof.MachineModel.Runs
import Proof.Amplification.RecoveryPCPFormulaResumeRandom

/-! Runtime initialization for A.12's outer hardwiring loop. The retained
unary width physically generates both the exponential repeat driver and
the zero binary assignment. Only a fixed empty frame is initially present;
all work tapes start empty. Actual count scratch is retained explicitly. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.BinaryInitialize
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound ExtDecompositionBatch
open RepairSource.VerifierDecoding

def input (K : Nat) : Fin 10 → List Bool :=
  ![CompareMachine.word K,[],[],[],[],[],[],frame [],[],[]]
def counted (result : Fin 7 → List Bool) : Fin 10 → List Bool :=
  Fin.addCases (m:=7) (n:=3) (motive:=fun _=>List Bool) result (![frame [],[],[]] : Fin 3 → List Bool)
def output (K : Nat) (scratch : Fin 5 → List Bool) : Fin 10 → List Bool :=
  ![CompareMachine.word K,scratch 0,scratch 1,scratch 2,CompareMachine.word (2^K-1),
    scratch 3,scratch 4,frame [],frame (SignedSortKey.binary K 0),List.replicate (2*K+3) false]
def heads : Fin 10 → Nat := ![0,0,0,0,1,0,0,0,0,0]
def seedSlots : Fin 4 → Fin 10 := ![7,8,0,9]
noncomputable def count := TapeEmbedding.machine 3 RepairSource.RecoveryPCPFormulaResumeCountCold.readyMachine
noncomputable def seed := RecoveryFocus.machine seedSlots RecoveryColdPaddedCopy.machine
def position : Machine 10 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => decide (q=1)
  rule := fun q _ => if q=0 then
    some ⟨1,fun _=>none,fun i=>if i=4 then .right else .stay⟩ else none
noncomputable def machine := Composition.machine (Composition.machine count seed) position
def budget (K : Nat) := RepairSource.RecoveryPCPFormulaResumeCountCold.budget K+4*K+11

theorem position_step (A : Fin 10 → List Bool) :
    Step position 1 (fun _=>0) A heads A := by
  have h : step position (⟨position.start,fun _=>0,A⟩ : Configuration 10 2) =
      some ⟨1,heads,A⟩ := by
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · rfl
  obtain ⟨r,hr,hf,_⟩ := (Timed.single (by rfl) h).run rfl
  exact Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)

theorem count_step (K : Nat) : ∃ result : Fin 7 → List Bool,
    Step count (RepairSource.RecoveryPCPFormulaResumeCountCold.budget K) (fun _=>0) (input K) (fun _=>0) (counted result) ∧
      result 0=CompareMachine.word K ∧ result 4=CompareMachine.word (2^K-1) := by
  obtain ⟨result,⟨r,hr,ht,hh,_⟩,h0,h4⟩ := RepairSource.RecoveryPCPFormulaResumeCountCold.count_ready K
  have h := (Step.of_run hr (funext hh) ht).embed (fun _ : Fin 3=>0)
    (![frame [],[],[]] : Fin 3 → List Bool)
  refine ⟨result,(h.congr_in ?_ ?_).congr ?_ rfl,h0,h4⟩
  all_goals funext i; fin_cases i <;> rfl

theorem seed_step (K : Nat) (result : Fin 7 → List Bool)
    (h0 : result 0=CompareMachine.word K) (h4 : result 4=CompareMachine.word (2^K-1)) :
    Step seed (4*K+8) (fun _=>0) (counted result) (fun _=>0)
      (output K (![result 1,result 2,result 3,result 5,result 6] : Fin 5 → List Bool)) := by
  have localRun := Step.of_ready (RecoveryColdPaddedCopy.copy_ready [] K)
  have hz : SignedSortKey.binary K 0=List.replicate K false := by
    clear h0 h4 localRun result
    induction K with
    | zero => rfl
    | succ K ih => simp [SignedSortKey.binary,ih,List.replicate_succ]
  rw [RepairSource.RecoveryPCPFormulaResumeRandomCold.zero_data,←hz] at localRun
  have h := localRun.focus seedSlots (by decide) (fun _=>0) (counted result)
  refine (h.congr_in ?_ ?_).congr ?_ ?_
  · funext i
    fin_cases i <;> first
      | exact dockH_slot seedSlots (by decide) _ _ 0
      | exact dockH_slot seedSlots (by decide) _ _ 1
      | exact dockH_slot seedSlots (by decide) _ _ 2
      | exact dockH_slot seedSlots (by decide) _ _ 3
      | exact dockH_other seedSlots _ _ _ (by decide)
  · apply HierarchyAllocation.install_eq seedSlots (by decide)
    · intro j; fin_cases j <;> first | rfl | exact h0
    · intros; rfl
  · funext i
    fin_cases i <;> first
      | exact dockH_slot seedSlots (by decide) _ _ 0
      | exact dockH_slot seedSlots (by decide) _ _ 1
      | exact dockH_slot seedSlots (by decide) _ _ 2
      | exact dockH_slot seedSlots (by decide) _ _ 3
      | exact dockH_other seedSlots _ _ _ (by decide)
  · apply HierarchyAllocation.install_eq seedSlots (by decide)
    · intro j; fin_cases j <;> rfl
    · intro i hi
      fin_cases i <;> first
        | rfl
        | exact h0
        | exact h4.symm
        | exact False.elim (hi 0 rfl)
        | exact False.elim (hi 1 rfl)
        | exact False.elim (hi 2 rfl)
        | exact False.elim (hi 3 rfl)

theorem initialize_run (K : Nat) : ∃ scratch : Fin 5 → List Bool,
    Step machine (budget K) (fun _=>0) (input K) heads (output K scratch) := by
  obtain ⟨result,first,h0,h4⟩ := count_step K
  have second := seed_step K result h0 h4
  have final := (first.seq second).seq (position_step _)
  have hb : RepairSource.RecoveryPCPFormulaResumeCountCold.budget K+1+(4*K+8)+1+1=budget K := by unfold budget; omega
  exact ⟨_,by simpa only [machine,hb] using final⟩

theorem budget_le (K : Nat) : budget K ≤ 80*(K+1)*2^K := by
  have hp := Nat.two_pow_pos K
  have hm : K+1 ≤ (K+1)*2^K := Nat.le_mul_of_pos_right _ hp
  unfold budget RepairSource.RecoveryPCPFormulaResumeCountCold.budget RepairSource.RecoveryPCPFormulaResumeCount.budget
  nlinarith

end NearCubicWires.P1Closure.BinaryInitialize
