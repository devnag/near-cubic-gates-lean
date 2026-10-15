import Proof.MachineModel.UWalkBootstrapRun

/-! Whole ordinary prefix through physical walk bootstrap. Failed front
guards stop; successful initialization is followed by numeric/head preparation. -/
namespace NearCubicWires.RepairOrdinary.UPrepared
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev frontStates := Fintype.card (RecoveryCalls.Control UInitialized.sizes)
noncomputable def sizes : Fin 2 → ℕ := ![frontStates,Fintype.card (RecoveryCalls.Control UWalkArray.sizes)]
noncomputable def programs : (j : Fin 2) → Machine 139 (sizes j)
  | ⟨0,_⟩ => TapeEmbedding.machine 42 UInitialized.machine
  | ⟨1,_⟩ => UWalkArray.machine
  | ⟨n+2,h⟩ => False.elim (by omega)
def next : (j : Fin 2) → Fin (sizes j) → (Fin 139 → Bool) → Option (Fin 2)
  | ⟨0,_⟩,_,bits => if bits 79 then some 1 else none
  | ⟨1,_⟩,_,_ => none
  | ⟨n+2,h⟩,_,_ => False.elim (by omega)
noncomputable def machine := RecoveryCalls.machine sizes programs 0 next
def input (raw witness : List Bool) : Fin 139 → List Bool :=
  fun i => Fin.addCases (UInitialized.input raw witness) (fun _ : Fin 42 => []) i
def bootstrapBudget (raw : List Bool) := 32768*(Nat.log 2 raw.length+1)*(ClockDyadicLedger.width raw.length+1)
def budget (raw : List Bool) := UInitialized.budget raw+bootstrapBudget raw+2

def Prepared {s : ℕ} (raw witness : List Bool) (final : Configuration 139 s) : Prop :=
  ∃ base : Configuration 97 frontStates,∃ c t j,
    UInitialized.Prepared raw witness base ∧ base.scanned 79=true ∧
    c ≤ Nat.log 2 raw.length ∧ t ≤ c ∧ j ≤ c ∧
    ZeroPadding.pad (c+2) (base.tapes 50)=RepairSource.VerifierDecoding.CapMachine.counter c t ∧
    base.tapes 58=RepairSource.VerifierDecoding.CompareMachine.word j ∧
    UWalkArray.Numeric (ClockDyadicLedger.width raw.length) t j c
      (ZeroPadding.config (UWalkBootstrap.capacity c) final) ∧
    (∀ i : Fin 97,i.val≠20 → i.val≠50 → i.val≠58 → i.val≠73 →
      final.tapes (i.castAdd 42)=base.tapes i ∧ final.heads (i.castAdd 42)=base.heads i) ∧
    final.tapes 136=(List.replicate t (frame (binary (ClockDyadicLedger.width raw.length) 0))).flatten ∧
    (∀ i,135 ≤ i.val → final.heads i=0)

theorem bootstrap_budget (raw : List Bool) (c t j : ℕ)
    (hc : c ≤ Nat.log 2 raw.length) (ht : t ≤ c) (hj : j ≤ c) :
    UWalkArray.budget (ClockDyadicLedger.width raw.length) t j ≤ bootstrapBudget raw :=
  (UWalkArray.budget_short _ _ _ c ht hj).trans
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.add_le_add_right hc 1)))

end NearCubicWires.RepairOrdinary.UPrepared
