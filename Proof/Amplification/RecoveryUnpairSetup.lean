import Proof.Amplification.RecoveryUnpairFinish

namespace NearCubicWires.RepairOrdinary.RecoveryUnpair
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def bootSlots : Fin 4 → Fin 15 := ![0, 1, 13, 14]
def initializeSlots : Fin 4 → Fin 15 := ![2, 3, 9, 8]
theorem bootSlots_injective : Function.Injective bootSlots := by decide
theorem initializeSlots_injective : Function.Injective initializeSlots := by decide

def input (bits : List Bool) (i : Fin 15) : List Bool :=
  if i.val = 0 then frame bits else []

def booted (bits : List Bool) (i : Fin 15) : List Bool :=
  match i.val with
  | 0 => frame bits
  | 1 => frame (RecoveryRadixInput.prepared bits)
  | 13 => List.replicate (2 * bits.length) false
  | 14 => List.replicate (4 * bits.length + 2) false
  | _ => []

def initialStore (bits : List Bool) : Store where
  root := RecoveryRootInitialization.zeroWord
  remainder := RecoveryRootInitialization.zeroWord
  lowCandidate := []
  highCandidate := []
  trial := []
  shifted := []
  candidateCapacity := 7
  flag := false
  compareCapacity := 0
  difference := []
  subtractCapacity := 0
  copyCapacity := 2 * bits.length
  resetCapacity := 4 * bits.length + 2

def initialTapes (bits : List Bool) := RecoveryRootLoop.tapes
  (frame bits) (frame (RecoveryRadixInput.prepared bits)) (initialStore bits)

noncomputable def bootMachine := RecoveryFocus.machine bootSlots RecoveryRadixInput.entryMachine
noncomputable def initializeMachine := RecoveryFocus.machine initializeSlots RecoveryRootInitialization.machine

theorem boot_ready (bits : List Bool) : ReadyRun bootMachine (8 * bits.length + 6)
    (input bits) (booted bits) := by
  obtain ⟨r, hr, h0, h1, h2, h3, hh, hs, _⟩ := RecoveryRadixInput.entry_run bits
  have hl : ReadyRun RecoveryRadixInput.entryMachine (8 * bits.length + 6)
      (fun i => if i.val = 0 then frame bits else [])
      ![frame bits, frame (RecoveryRadixInput.prepared bits),
        List.replicate (2 * bits.length) false, List.replicate (4 * bits.length + 2) false] := by
    refine ⟨r, hr, ?_, hh, hs⟩
    funext i; fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  have h := hl.focus bootSlots bootSlots_injective (input bits) (by intro j; fin_cases j <;> rfl)
  have he : install bootSlots (input bits)
      ![frame bits, frame (RecoveryRadixInput.prepared bits),
        List.replicate (2 * bits.length) false, List.replicate (4 * bits.length + 2) false] = booted bits := by
    funext i
    fin_cases i
    all_goals first
      | exact install_slot bootSlots bootSlots_injective _ _ 0
      | exact install_slot bootSlots bootSlots_injective _ _ 1
      | exact install_slot bootSlots bootSlots_injective _ _ 2
      | exact install_slot bootSlots bootSlots_injective _ _ 3
      | exact install_other bootSlots _ _ _ (by intro j; fin_cases j <;> decide)
  rw [he] at h
  exact h

theorem initialize_ready (bits : List Bool) : ReadyRun initializeMachine 16
    (booted bits) (initialTapes bits) := by
  have h := RecoveryRootInitialization.initialize_ready.focus initializeSlots initializeSlots_injective
    (booted bits) (by intro j; fin_cases j <;> rfl)
  have he : install initializeSlots (booted bits)
      ![frame RecoveryRootInitialization.zeroWord, frame RecoveryRootInitialization.zeroWord,
        [false], List.replicate 7 false] = initialTapes bits := by
    funext i
    fin_cases i
    all_goals first
      | exact install_slot initializeSlots initializeSlots_injective _ _ 0
      | exact install_slot initializeSlots initializeSlots_injective _ _ 1
      | exact install_slot initializeSlots initializeSlots_injective _ _ 2
      | exact install_slot initializeSlots initializeSlots_injective _ _ 3
      | exact install_other initializeSlots _ _ _ (by intro j; fin_cases j <;> decide)
  rw [he] at h
  exact h

theorem initial_valid (bits : List Bool) : RecoveryRootIteration.Valid (initialStore bits) := by
  refine ⟨rfl, ?_, by change 0 ≤ 7; decide⟩
  intro i
  fin_cases i <;> change 0 ≤ 7 <;> decide

theorem initial_numeric (bits : List Bool) : (initialStore bits).numeric =
    RepairSource.RecoveryOracle.RestoringRoot.zero := by rfl

theorem initial_width (bits : List Bool) : (initialStore bits).root.length = 3 := by rfl

end NearCubicWires.RepairOrdinary.RecoveryUnpair
