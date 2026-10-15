import Proof.Amplification.RecoveryFieldCopy

/-! Concrete global layout for unpair with a preserved original field width.
The width producer and two bounded copies consume the actual unpair output. -/
namespace NearCubicWires.RepairOrdinary.RecoveryFixedUnpair
open LocalBitMultitape RecoveryExecution RecoveryRootRound RadixSemantics
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def unpairTime (bits : List Bool) := 2 * RecoveryUnpair.rawTime bits + 2

def unpairOutput (bits : List Bool) : Fin 16 → List Bool :=
  Fin.addCases (m := 15) (n := 1) (motive := fun _ => List Bool)
    (RecoveryRootLoop.tapes (frame bits) (frame (RecoveryRadixInput.prepared bits)) (RecoveryUnpair.resultStore bits))
    (fun _ => List.replicate (RecoveryUnpair.rawTime bits) false)

theorem unpair_ready (bits : List Bool) :
    ReadyRun RecoveryUnpair.machine (unpairTime bits)
      (fun i => if i.val = 0 then frame bits else []) (unpairOutput bits) := by
  obtain ⟨source, hr, ht, _, hs⟩ := RecoveryUnpair.raw_run bits
  obtain ⟨r, hrun, htapes, hc, hh, hsteps, _⟩ := Rewind.Workspace.reset_workspace
    RecoveryUnpair.rawMachine _ _ source hr 0
  have he : 2 * source.steps + 2 = unpairTime bits := by rw [hs]; rfl
  rw [he] at hrun
  refine ⟨r, ?_, ?_, hh, hsteps.trans he⟩
  · convert hrun using 2
    all_goals first | rfl | (funext i; fin_cases i <;> rfl)
  · funext i
    refine Fin.addCases (m := 15) (n := 1) (motive := fun j : Fin 16 =>
      r.final.tapes j = unpairOutput bits j) ?_ ?_ i
    · intro j
      simpa only [unpairOutput, Fin.addCases_left, ht] using htapes j
    · intro j
      fin_cases j
      change r.final.tapes (Fin.natAdd 15 (0 : Fin 1)) =
        List.replicate (RecoveryUnpair.rawTime bits) false
      simpa only [hs, Nat.zero_max] using hc

def nativeSlots (i : Fin 16) : Fin 21 := i.castAdd 5
def widthSlots : Fin 3 → Fin 21 := ![0, 16, 19]
def leftSlots : Fin 4 → Fin 21 := ![2, 17, 16, 20]
def rightSlots : Fin 4 → Fin 21 := ![3, 18, 16, 20]
theorem nativeSlots_injective : Function.Injective nativeSlots := by
  intro i j h
  have hv := congrArg (fun k : Fin 21 => k.val) h
  exact Fin.ext hv
theorem widthSlots_injective : Function.Injective widthSlots := by decide
theorem leftSlots_injective : Function.Injective leftSlots := by decide
theorem rightSlots_injective : Function.Injective rightSlots := by decide

def input (bits : List Bool) (i : Fin 21) : List Bool := if i.val = 0 then frame bits else []
def output0 (bits : List Bool) : Fin 21 → List Bool :=
  Fin.addCases (m := 16) (n := 5) (motive := fun _ => List Bool) (unpairOutput bits) (fun _ => [])
def output1 (bits : List Bool) (i : Fin 21) : List Bool :=
  if i.val = 16 then CompareMachine.word bits.length
  else if i.val = 19 then List.replicate (4 * bits.length + 3) false else output0 bits i

def leftWord (bits : List Bool) := SignedSortKey.binary bits.length (Nat.unpair (value bits)).1
def rightWord (bits : List Bool) := SignedSortKey.binary bits.length (Nat.unpair (value bits)).2

def output2 (bits : List Bool) (i : Fin 21) : List Bool :=
  if i.val = 17 then frame (leftWord bits)
  else if i.val = 20 then List.replicate (4 * bits.length + 4) false else output1 bits i

def output3 (bits : List Bool) (i : Fin 21) : List Bool :=
  if i.val = 18 then frame (rightWord bits) else output2 bits i

noncomputable def nativeMachine := RecoveryFocus.machine nativeSlots RecoveryUnpair.machine
noncomputable def widthMachine := RecoveryFocus.machine widthSlots RecoveryFieldCopy.widthMachine
noncomputable def leftMachine := RecoveryFocus.machine leftSlots RecoveryFieldCopy.machine
noncomputable def rightMachine := RecoveryFocus.machine rightSlots RecoveryFieldCopy.machine

theorem native_ready (bits : List Bool) : ReadyRun nativeMachine (unpairTime bits) (input bits) (output0 bits) := by
  have h := (unpair_ready bits).focus nativeSlots nativeSlots_injective (input bits) (by intro j; rfl)
  have he : install nativeSlots (input bits) (unpairOutput bits) = output0 bits := by
    funext i
    refine Fin.addCases (m := 16) (n := 5) (motive := fun j : Fin 21 =>
      install nativeSlots (input bits) (unpairOutput bits) j = output0 bits j) ?_ ?_ i
    · intro j
      rw [output0, Fin.addCases_left]
      change install nativeSlots (input bits) (unpairOutput bits) (nativeSlots j) = unpairOutput bits j
      exact install_slot nativeSlots nativeSlots_injective _ _ j
    · intro j
      rw [install_other nativeSlots _ _ _ (by
        intro k h
        have hv := congrArg Fin.val h
        simp only [nativeSlots, Fin.val_castAdd, Fin.val_natAdd] at hv
        omega)]
      simp [input, output0]
  rw [he] at h
  exact h

theorem width_ready (bits : List Bool) : ReadyRun widthMachine (8 * bits.length + 8)
    (output0 bits) (output1 bits) := by
  have h := (RecoveryFieldCopy.width_ready bits 0).focus widthSlots widthSlots_injective (output0 bits)
    (by intro j; fin_cases j <;> rfl)
  simp only [Nat.zero_max] at h
  have he : install widthSlots (output0 bits)
      ![frame bits, CompareMachine.word bits.length, List.replicate (4 * bits.length + 3) false] = output1 bits := by
    funext i
    fin_cases i
    all_goals first
      | exact install_slot widthSlots widthSlots_injective _ _ 0
      | exact install_slot widthSlots widthSlots_injective _ _ 1
      | exact install_slot widthSlots widthSlots_injective _ _ 2
      | exact install_other widthSlots _ _ _ (by intro j; fin_cases j <;> decide)
  rw [he] at h
  exact h

theorem left_ready (bits : List Bool) : ReadyRun leftMachine (8 * bits.length + 10)
    (output1 bits) (output2 bits) := by
  have hw : bits.length ≤ (RecoveryUnpair.leftWord bits).length := by
    rw [(RecoveryUnpair.word_lengths bits).1]; omega
  have h := (RecoveryFieldCopy.take_ready (RecoveryUnpair.leftWord bits) [] bits.length 0 hw (by simp)).focus
    leftSlots leftSlots_injective (output1 bits) (by
      intro j; fin_cases j
      · exact congrArg frame (RecoveryUnpair.result_words bits).1
      · rfl
      · rfl
      · rfl)
  rw [(RecoveryFixedWidth.unpair_low_words bits).1] at h
  simp only [Nat.zero_max] at h
  have he : install leftSlots (output1 bits)
      ![frame (RecoveryUnpair.leftWord bits), frame (leftWord bits), CompareMachine.word bits.length,
        List.replicate (4 * bits.length + 4) false] = output2 bits := by
    funext i
    fin_cases i
    all_goals first
      | exact (install_slot leftSlots leftSlots_injective _ _ 0).trans
          (congrArg frame (RecoveryUnpair.result_words bits).1.symm)
      | exact install_slot leftSlots leftSlots_injective _ _ 1
      | exact install_slot leftSlots leftSlots_injective _ _ 2
      | exact install_slot leftSlots leftSlots_injective _ _ 3
      | exact install_other leftSlots _ _ _ (by intro j; fin_cases j <;> decide)
  change install leftSlots (output1 bits)
    ![frame (RecoveryUnpair.leftWord bits), frame (SignedSortKey.binary bits.length (Nat.unpair (value bits)).1),
      CompareMachine.word bits.length, List.replicate (4 * bits.length + 4) false] = _ at he
  rw [he] at h
  exact h

theorem right_ready (bits : List Bool) : ReadyRun rightMachine (8 * bits.length + 10)
    (output2 bits) (output3 bits) := by
  have hw : bits.length ≤ (RecoveryUnpair.rightWord bits).length := by
    rw [(RecoveryUnpair.word_lengths bits).2]; omega
  have h := (RecoveryFieldCopy.take_ready (RecoveryUnpair.rightWord bits) [] bits.length
      (4 * bits.length + 4) hw (by simp)).focus
    rightSlots rightSlots_injective (output2 bits) (by
      intro j; fin_cases j
      · exact congrArg frame (RecoveryUnpair.result_words bits).2
      · rfl
      · rfl
      · rfl)
  rw [(RecoveryFixedWidth.unpair_low_words bits).2] at h
  simp only [Nat.max_self] at h
  have he : install rightSlots (output2 bits)
      ![frame (RecoveryUnpair.rightWord bits), frame (rightWord bits), CompareMachine.word bits.length,
        List.replicate (4 * bits.length + 4) false] = output3 bits := by
    funext i
    fin_cases i
    all_goals first
      | exact (install_slot rightSlots rightSlots_injective _ _ 0).trans
          (congrArg frame (RecoveryUnpair.result_words bits).2.symm)
      | exact install_slot rightSlots rightSlots_injective _ _ 1
      | exact install_slot rightSlots rightSlots_injective _ _ 2
      | exact install_slot rightSlots rightSlots_injective _ _ 3
      | exact install_other rightSlots _ _ _ (by intro j; fin_cases j <;> decide)
  change install rightSlots (output2 bits)
    ![frame (RecoveryUnpair.rightWord bits), frame (SignedSortKey.binary bits.length (Nat.unpair (value bits)).2),
      CompareMachine.word bits.length, List.replicate (4 * bits.length + 4) false] = _ at he
  rw [he] at h
  exact h

end NearCubicWires.RepairOrdinary.RecoveryFixedUnpair
