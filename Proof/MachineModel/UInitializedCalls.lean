import Proof.MachineModel.UInitializationAmbient

/-! The same ordinary front continues into initialization only on success.
Rejection halts immediately, retaining the already computed false result. -/
namespace NearCubicWires.RepairOrdinary.UInitialized
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev frontStates := Fintype.card (RecoveryCalls.Control UFront.sizes)
def sizes : Fin 2 → ℕ := ![frontStates,179]
noncomputable def programs : (j : Fin 2) → Machine 97 (sizes j)
  | ⟨0,_⟩ => TapeEmbedding.machine 16 UFront.machine
  | ⟨1,_⟩ => UInitializationAmbient.machine
  | ⟨n+2,h⟩ => False.elim (by omega)
def next : (j : Fin 2) → Fin (sizes j) → (Fin 97 → Bool) → Option (Fin 2)
  | ⟨0,_⟩,_,bits => if bits 79 then some 1 else none
  | ⟨1,_⟩,_,_ => none
  | ⟨n+2,h⟩,_,_ => False.elim (by omega)
noncomputable def machine := RecoveryCalls.machine sizes programs 0 next
def input (raw witness : List Bool) : Fin 97 → List Bool :=
  fun i => Fin.addCases (UFront.input raw witness) (fun _ : Fin 16 => []) i
def initBudget (raw : List Bool) := 131*(2*ClockDyadicLedger.limit raw.length+1)*(ClockDyadicLedger.width raw.length+1)
def budget (raw : List Bool) := UFront.budget raw+initBudget raw+2

def memoryEndpoint (w : ℕ) (x choices : List Bool) : Configuration 11 154 :=
  MemoryInitialSources.config 153 (2*w) (2*w+2) ((frame x).length+(frame choices).length)
    (frame x).length (2^w+(frame choices).length) (4*w+5)
    (MemoryInitialEmission.fields (2*w) (2*w+2) w 0 (MemoryInitialization.events x choices))
    (frame x) (frame choices) (frame x).length (frame choices).length false

def LocalResult (w : ℕ) (x choices : List Bool) (localFinal : Configuration 21 179) : Prop :=
  ∃ small : Configuration 11 154,
    localFinal.heads=(RecoveryFocus.config UInitialization.memorySlots (fun _ : Fin 21 => 0)
      (UInitialization.afterKey w x choices) small).heads ∧
    localFinal.tapes=(RecoveryFocus.config UInitialization.memorySlots (fun _ : Fin 21 => 0)
      (UInitialization.afterKey w x choices) small).tapes ∧
    ZeroPadding.config (MemoryInitializationCarrier.capacities w) small=memoryEndpoint w x choices

def Prepared {s : ℕ} (raw witness : List Bool) (final : Configuration 97 s) : Prop :=
  ∃ base : Configuration 81 frontStates,∃ x choices : List Bool,∃ localFinal : Configuration 21 179,
    UFront.Successful raw witness base ∧ base.scanned 79=true ∧
    x.length≤choices.length ∧ choices.length≤ClockDyadicLedger.limit raw.length ∧
    base.tapes 8=frame x ∧ base.tapes 78=frame choices ∧
    final.heads=(RecoveryFocus.config UInitializationAmbient.slots
      (UInitializationAmbient.extended base).heads (UInitializationAmbient.extended base).tapes localFinal).heads ∧
    final.tapes=(RecoveryFocus.config UInitializationAmbient.slots
      (UInitializationAmbient.extended base).heads (UInitializationAmbient.extended base).tapes localFinal).tapes ∧
    LocalResult (ClockDyadicLedger.width raw.length) x choices localFinal ∧
    final.tapes 92=MemoryInitialEmission.fields (2*ClockDyadicLedger.width raw.length)
      (2*ClockDyadicLedger.width raw.length+2) (ClockDyadicLedger.width raw.length) 0
      (MemoryInitialization.events x choices)

theorem initialization_budget (raw : List Bool) (x choices : List Bool)
    (hn : x.length≤choices.length) (hB : choices.length≤ClockDyadicLedger.limit raw.length) :
    UInitialization.budget (ClockDyadicLedger.width raw.length) x.length choices.length≤ initBudget raw := by
  have hl : x.length+choices.length+1≤2*ClockDyadicLedger.limit raw.length+1 := by omega
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hl)

theorem initialized_bit {s : ℕ} (base : Configuration 81 s) (localFinal : Configuration 21 179) :
    (RecoveryFocus.config UInitializationAmbient.slots
      (UInitializationAmbient.extended base).heads (UInitializationAmbient.extended base).tapes localFinal).scanned 79=
      base.scanned 79 := by
  have hnone := UWitness.pick_other UInitializationAmbient.slots (79 : Fin 97)
    (by intro j; fin_cases j <;> decide)
  simp [RecoveryFocus.config,Configuration.scanned,hnone,UInitializationAmbient.extended,TapeEmbedding.config,Fin.addCases]

end NearCubicWires.RepairOrdinary.UInitialized
