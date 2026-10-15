import Proof.Amplification.RecoveryRootCandidates
import Proof.Amplification.RecoveryCallController
import Proof.MachineModel.OrdinaryCompare
import Proof.MachineModel.OrdinaryFrameLoad

namespace NearCubicWires.RepairOrdinary.RecoveryRootRound
open LocalBitMultitape RecoveryExecution RadixSemantics
open StablePartition.Workspace (overlay)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def ReadyRun {t s : Nat} (p : Machine t s) (time : Nat)
    (input output : Fin t → List Bool) : Prop :=
  ∃ r : ExecutionReceipt t s, run p time input = some r ∧
    r.final.tapes = output ∧ (∀ i, r.final.heads i = 0) ∧ r.steps = time

abbrev candidateMachine (lo hi : Bool) := Rewind.machine (RecoveryRootCandidates.machine lo hi)
def candidateInput (left right : List Bool) (backing : Fin 4 → List Bool) (capacity : Nat) : Fin 7 → List Bool :=
  ![frame left, frame right, backing 0, backing 1, backing 2, backing 3, List.replicate capacity false]
def candidateOutput (lo hi : Bool) (left right : List Bool) (capacity : Nat) : Fin 7 → List Bool :=
  ![frame left, frame right,
    frame (RecoveryRootCandidates.words lo hi left right 0),
    frame (RecoveryRootCandidates.words lo hi left right 1),
    frame (RecoveryRootCandidates.words lo hi left right 2),
    frame (RecoveryRootCandidates.words lo hi left right 3),
    List.replicate (max capacity (2 * left.length + 7)) false]

theorem candidate_ready (lo hi : Bool) (left right : List Bool) (backing : Fin 4 → List Bool)
    (capacity : Nat) (hw : left.length = right.length)
    (hb : ∀ i, (backing i).length ≤ 2 * (left.length + 2) + 1) :
    ReadyRun (candidateMachine lo hi) (4 * left.length + 16)
      (candidateInput left right backing capacity) (candidateOutput lo hi left right capacity) := by
  obtain ⟨base, hr, hf, hs⟩ := RecoveryRootCandidates.candidates_run lo hi left right backing hw
  obtain ⟨r, hrun, ht, hc, hh, hsteps, _⟩ := Rewind.Workspace.reset_workspace
    (RecoveryRootCandidates.machine lo hi) _ _ base hr capacity
  have he : 2 * base.steps + 2 = 4 * left.length + 16 := by rw [hs]; omega
  have hin : Fin.addCases (motive := fun _ : Fin 7 => List Bool)
      ![frame left, frame right, backing 0, backing 1, backing 2, backing 3]
      (fun _ : Fin 1 => List.replicate capacity false) = candidateInput left right backing capacity := by
    funext i; fin_cases i <;> rfl
  rw [he, hin] at hrun
  refine ⟨r, hrun, ?_, hh, hsteps.trans he⟩
  have hcore (i : Fin 6) : r.final.tapes (i.castAdd 1) =
      (RecoveryRootCandidates.config 8 (frame left) (frame right) (2 * left.length) (2 * right.length)
        (fun j => frame (RecoveryRootCandidates.words lo hi left right j)) backing).tapes i := by rw [ht, hf]
  have ho (i : Fin 4) : overlay (frame (RecoveryRootCandidates.words lo hi left right i)) (backing i) =
      frame (RecoveryRootCandidates.words lo hi left right i) := by
    have hlen : (backing i).length ≤ (frame (RecoveryRootCandidates.words lo hi left right i)).length := by
      rw [frame_length, RecoveryRootCandidates.words_length lo hi left right hw]
      exact hb i
    simp only [overlay, List.drop_eq_nil_of_le hlen, List.append_nil]
  funext i
  fin_cases i
  · exact hcore 0
  · exact hcore 1
  · simpa [RecoveryRootCandidates.config, candidateOutput, ho] using hcore 2
  · simpa [RecoveryRootCandidates.config, candidateOutput, ho] using hcore 3
  · simpa [RecoveryRootCandidates.config, candidateOutput, ho] using hcore 4
  · simpa [RecoveryRootCandidates.config, candidateOutput, ho] using hcore 5
  · simpa [candidateOutput, hs] using hc

abbrev subtractMachine := Rewind.machine RepairSource.RecoveryOracle.Subtract.machine

theorem subtract_ready (width a b : Nat) (backing : List Bool) (capacity : Nat)
    (hba : b ≤ a) (ha : a < 2 ^ width) (hb : backing.length ≤ 2 * width + 1) :
    ReadyRun subtractMachine (4 * width + 4)
      ![frame (SignedSortKey.binary width a), frame (SignedSortKey.binary width b),
        backing, List.replicate capacity false]
      ![frame (SignedSortKey.binary width a), frame (SignedSortKey.binary width b),
        frame (SignedSortKey.binary width (a - b)), List.replicate (max capacity (2 * width + 1)) false] := by
  obtain ⟨base, hr, h0, h1, h2, _, _, _, hs, _⟩ :=
    RepairSource.RecoveryOracle.Subtract.subtract_run width a b backing ha hba hb
  have hin : initialConfiguration RepairSource.RecoveryOracle.Subtract.machine
      ![frame (SignedSortKey.binary width a), frame (SignedSortKey.binary width b), backing] =
      RepairSource.RecoveryOracle.Subtract.config (RepairSource.RecoveryOracle.Subtract.scanState false)
        (frame (SignedSortKey.binary width a)) (frame (SignedSortKey.binary width b)) 0 0 [] backing := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · simp [initialConfiguration, RepairSource.RecoveryOracle.Subtract.config, overlay]
  have hr' : run RepairSource.RecoveryOracle.Subtract.machine (2 * width + 1)
      ![frame (SignedSortKey.binary width a), frame (SignedSortKey.binary width b), backing] = some base := by
    rw [run, hin]; exact hr
  obtain ⟨r, hrun, ht, hc, hh, hsteps, _⟩ := Rewind.Workspace.reset_workspace
    RepairSource.RecoveryOracle.Subtract.machine _ _ base hr' capacity
  have he : 2 * base.steps + 2 = 4 * width + 4 := by rw [hs]; omega
  rw [he] at hrun
  refine ⟨r, ?_, ?_, hh, hsteps.trans he⟩
  · convert hrun using 2
    funext i; fin_cases i <;> rfl
  · funext i; fin_cases i
    · exact (ht 0).trans h0
    · exact (ht 1).trans h1
    · exact (ht 2).trans h2
    · simpa [hs] using hc

abbrev copyMachine := Rewind.machine FrameLoad.machine

theorem copy_ready (bits backing : List Bool) (capacity resetCapacity : Nat)
    (hb : backing.length ≤ 2 * bits.length + 1) :
    ReadyRun copyMachine (8 * bits.length + 8)
      ![frame bits, backing, List.replicate capacity false, List.replicate resetCapacity false]
      ![frame bits, frame bits, List.replicate (max capacity (2 * bits.length + 1)) false,
        List.replicate (max resetCapacity (4 * bits.length + 3)) false] := by
  obtain ⟨base, hr, hf, hs, _⟩ := FrameLoad.load_run [] bits [] backing hb
  obtain ⟨padded, hp, hpf, hps, _⟩ := ZeroPadding.run_config FrameLoad.machine ![0, 0, capacity] _ _ base hr
  have hin : ZeroPadding.config ![0, 0, capacity]
      (FrameLoad.scan 0 ([] ++ frame bits ++ []) 0 [] backing) =
      initialConfiguration FrameLoad.machine ![frame bits, backing, List.replicate capacity false] := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> simp [ZeroPadding.config, ZeroPadding.pad, FrameLoad.scan, initialConfiguration, overlay]
  simp only [List.length_nil] at hp
  rw [hin] at hp
  have h0 : padded.final.tapes 0 = frame bits := by simp [hpf, hf, ZeroPadding.config, FrameLoad.reset]
  have h1 : padded.final.tapes 1 = frame bits := by simp [hpf, hf, ZeroPadding.config, FrameLoad.reset]
  have h2 : padded.final.tapes 2 = List.replicate (max capacity (2 * bits.length + 1)) false := by
    simp [hpf, hf, ZeroPadding.config, FrameLoad.reset, Rewind.Workspace.pad_zeros]
  have htime : padded.steps = 4 * bits.length + 3 := hps.trans hs
  obtain ⟨r, hrun, ht, hc, hh, hsteps, _⟩ := Rewind.Workspace.reset_workspace
    FrameLoad.machine _ _ padded hp resetCapacity
  have he : 2 * padded.steps + 2 = 8 * bits.length + 8 := by rw [htime]; omega
  rw [he] at hrun
  refine ⟨r, ?_, ?_, hh, hsteps.trans he⟩
  · convert hrun using 2
    funext i; fin_cases i <;> rfl
  · funext i; fin_cases i
    · exact (ht 0).trans h0
    · exact (ht 1).trans h1
    · exact (ht 2).trans h2
    · simpa [htime] using hc

abbrev compareMachine := Rewind.machine Compare.machine

theorem compare_ready (left right : List Bool) (capacity : Nat) (hw : left.length = right.length) :
    ReadyRun compareMachine (4 * left.length + 4)
      ![frame left, frame right, [false], List.replicate capacity false]
      ![frame left, frame right, [decide (value left ≤ value right)],
        List.replicate (max capacity (2 * left.length + 1)) false] := by
  have hp := Compare.scan_prefix [] [] left right [] [] [] true hw
  obtain ⟨base, hr, hf, hs, _⟩ := hp.run (by rfl) (by simp)
  obtain ⟨padded, hrun, hpf, hps, _⟩ := ZeroPadding.run_config Compare.machine ![0, 0, 1] _ _ base hr
  have hin : ZeroPadding.config ![0, 0, 1]
      (Compare.config (Compare.scanState true) ([] ++ frame left ++ []) ([] ++ frame right ++ []) 0 0 []) =
      initialConfiguration Compare.machine ![frame left, frame right, [false]] := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> simp [ZeroPadding.config, ZeroPadding.pad, Compare.config, initialConfiguration]
  simp only [List.length_nil] at hrun
  rw [hin] at hrun
  have h0 : padded.final.tapes 0 = frame left := by simp [hpf, hf, ZeroPadding.config, Compare.config]
  have h1 : padded.final.tapes 1 = frame right := by simp [hpf, hf, ZeroPadding.config, Compare.config]
  have h2 : padded.final.tapes 2 = [decide (value left ≤ value right)] := by
    simp [hpf, hf, ZeroPadding.config, Compare.config, ZeroPadding.pad, Compare.decision_le left right hw]
  have htime : padded.steps = 2 * left.length + 1 := hps.trans hs
  obtain ⟨r, hrun, ht, hc, hh, hsteps, _⟩ := Rewind.Workspace.reset_workspace
    Compare.machine _ _ padded hrun capacity
  have he : 2 * padded.steps + 2 = 4 * left.length + 4 := by rw [htime]; omega
  rw [he] at hrun
  refine ⟨r, ?_, ?_, hh, hsteps.trans he⟩
  · convert hrun using 2
    funext i; fin_cases i <;> rfl
  · funext i; fin_cases i
    · exact (ht 0).trans h0
    · exact (ht 1).trans h1
    · exact (ht 2).trans h2
    · simpa [htime] using hc

end NearCubicWires.RepairOrdinary.RecoveryRootRound
