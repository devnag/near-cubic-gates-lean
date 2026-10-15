import Proof.PCP.VerifierDecodingTableBound

/-! The table-size test consumes only the three paid input counters. Every
other tape begins blank at head zero; a real setup transition moves those
heads, and zero-padding reverse simulation removes proof-only backing. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.TableBoundEntry
open LocalBitMultitape RepairOrdinary RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def setup : Machine 7 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val = 1
  rule := fun q _ => if q.val = 0 then
    some ⟨1,fun _ => none,![.right,.right,.stay,.stay,.right,.stay,.stay]⟩ else none
noncomputable def machine := Composition.machine setup TableBoundMachine.machine

def tapes (c t s : ℕ) : Fin 7 → List Bool :=
  ![[],[],CompareMachine.word c,CompareMachine.word t,[],CompareMachine.word s,[]]
def initial (c t s : ℕ) : Configuration 7 2 := ⟨0,![0,0,1,1,0,1,0],tapes c t s⟩
def prepared (c t s : ℕ) : Configuration 7 2 := ⟨1,![1,1,1,1,1,1,0],tapes c t s⟩
def capacity (c : ℕ) : Fin 7 → ℕ := ![c+2,c+2,c+2,c+2,c+2,c+2,1]

theorem setup_step (c t s : ℕ) : step setup (initial c t s) = some (prepared c t s) := by
  simp [step,setup,initial]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply,prepared]
  · rfl

theorem padded_input (c t s : ℕ) :
    ZeroPadding.config (capacity c) (Composition.restart (prepared c t s) TableBoundMachine.machine.start) =
      controlConfig (RecoveryCalls.code TableBoundMachine.sizes 0) (TableBoundMachine.initial c t s) := by
  apply configuration_ext
  · rfl
  · rfl
  · funext i; fin_cases i <;> simp [ZeroPadding.config,capacity,Composition.restart,prepared,tapes,
      controlConfig,TableBoundMachine.initial,TableBoundMachine.store,CapMachine.counter,
      CompareMachine.word,ZeroPadding.pad]
    all_goals rw [List.replicate_succ]

/-- All non-input marks and cursor moves are produced inside this program.
Padding in the endpoint is observational only and does not allocate cells. -/
theorem table_bound_run (c t s : ℕ) (hc : 1 ≤ c) (ht : t ≤ c) (hs : s ≤ c) (hspos : 0 < s) :
    ∃ receipt final,
      runFrom machine (TableBoundMachine.budget c+2)
        (Composition.leftConfig _ (initial c t s)) = some receipt ∧
      receipt.steps ≤ TableBoundMachine.budget c+2 ∧
      TableBoundMachine.Result c t s final ∧
      ZeroPadding.config (capacity c) receipt.final = Composition.rightConfig 2 final := by
  obtain ⟨base,hbase,hbt,hbf⟩ := TableBoundMachine.table_bound_run c t s hc ht hs hspos
  rw [←padded_input c t s] at hbase
  obtain ⟨actual,ha,haf,hat,_⟩ := ZeroPadding.run_unpad TableBoundMachine.machine (capacity c) _ _ base hbase
  obtain ⟨first,hfirst,hff,hft⟩ := (Timed.single (by rfl : setup.halted (0 : Fin 2) = false) (setup_step c t s)).run (by rfl)
  have hcall : runFrom TableBoundMachine.machine (TableBoundMachine.budget c)
      (Composition.restart first.final TableBoundMachine.machine.start) = some actual := by rw [hff]; exact ha
  have hj := Composition.run_join setup TableBoundMachine.machine 1 (TableBoundMachine.budget c) _ first actual hfirst hcall
  have htime : 1+1+TableBoundMachine.budget c = TableBoundMachine.budget c+2 := by omega
  rw [htime] at hj
  refine ⟨Composition.joinedReceipt first actual,base.final,hj,?_,hbf,?_⟩
  · change first.steps+1+actual.steps ≤ _
    rw [hft,hat]
    omega
  · change ZeroPadding.config (capacity c) (Composition.rightConfig 2 actual.final) = Composition.rightConfig 2 base.final
    have he : ZeroPadding.config (capacity c) (Composition.rightConfig 2 actual.final) =
        Composition.rightConfig 2 (ZeroPadding.config (capacity c) actual.final) := rfl
    rw [he,haf]

end NearCubicWires.RepairSource.VerifierDecoding.TableBoundEntry
