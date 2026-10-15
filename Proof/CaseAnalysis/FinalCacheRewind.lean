import Proof.CaseAnalysis.FinalCacheAtAdmission
import Proof.Circuits.DecompositionCountPosition
import Proof.MachineModel.Runs

/-! One paid cold rewind, starting with an empty recording log, followed by
fixed cache-head positioning. Every original cache byte and the admission flag
are preserved. This does not assume a preallocated rewind capacity. -/
namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10ColdCacheRewind

open NearCubicWires LocalBitMultitape ExtDecompositionBatch SourceInterfaces
open RepairSource RepairRepresentation ProjectionNormalization CloseoutWitness
open CloseoutFinalC10ColdCacheAtAdmission

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def machine {t s : ℕ} (p : Machine t s) := MaskedReset.machine p (fun _ => true)

/-- First execution allocates its own recording log; all old data survive. -/
theorem rewind_run {t s : ℕ} (p : Machine t s) (fuel : ℕ) (input : Fin t → List Bool)
    (source : ExecutionReceipt t s) (hr : run p fuel input = some source) (hs : source.steps ≤ fuel) :
    Step (machine p) (2 * fuel + 2) (fun _ => 0)
      (Fin.addCases input (fun _ : Fin 1 => [])) (fun _ => 0)
      (Fin.addCases source.final.tapes (fun _ : Fin 1 => List.replicate source.steps false)) := by
  have hhead : ∀ i : Fin t, (true : Bool) = true → source.final.heads i ≤ source.steps := by
    intro i _
    have h := SelectiveReset.prefix_head (prefix_of_run p fuel _ source hr).1 i
    simpa only [initialConfiguration, Nat.zero_add] using h
  obtain ⟨r, hrun, hfinal, hsteps, _hpeak⟩ :=
    MaskedReset.reset_run p (fun _ => true) fuel _ source hr hhead
  have hentry : Rewind.recording (initialConfiguration p input) 0 =
      (⟨(machine p).start, fun _ => 0, Fin.addCases input (fun _ : Fin 1 => [])⟩ :
        Configuration (t + 1) (s + 2)) := by
    apply configuration_ext
    · rfl
    · funext i
      exact Fin.addCases (m := t) (n := 1)
        (fun _ => by simp [Rewind.recording, Rewind.config, initialConfiguration])
        (fun _ => by simp [Rewind.recording, Rewind.config]) i
    · rfl
  rw [hentry] at hrun
  have base : Step (machine p) (2 * source.steps + 2) (fun _ => 0)
      (Fin.addCases input (fun _ : Fin 1 => [])) (fun _ => 0)
      (Fin.addCases source.final.tapes (fun _ : Fin 1 => List.replicate source.steps false)) := by
    refine ⟨r, hrun, ?_, ?_, hsteps.le⟩
    · rw [hfinal]
      funext i
      exact Fin.addCases (m := t) (n := 1)
        (fun _ => by simp [SelectiveReset.finished, Rewind.config])
        (fun _ => by simp [SelectiveReset.finished, Rewind.config]) i
    · rw [hfinal]
      rfl
  exact base.enlarge (by omega)

attribute [local irreducible] BoundedFamilySupport.actualMachine ColdFamilySupport.actualMachine

/-- The actual bounded original-input machine, with one fresh empty log, now
ends at zero heads. The existential old heads only specify retained cache bytes;
they are not claimed to be the new physical heads. -/
theorem bounded_zero (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
    (a : PointwisePCPPAlgorithm) (k CH Cpad cutoff D G copies E K symDen thrDen : ℕ)
    (delta : ℚ) (code : List Bool) {n : ℕ} (x : BitInput n) (bits : List Bool)
    (hpad : k + 3 ≤ Cpad) (hD : 1 ≤ D) (hsym : 0 < symDen) (hthr : 0 < thrDen) (hK : 0 < K)
    (hcut : 2 ^ a.minimumArity ≤ cutoff) (hd : 0 < delta) (hh : delta < 1 / 2) (hc : 1 ≤ copies)
    (hbudget : ∀ N, FamilyResources.capacity (ColdFamily.scale source a G D copies delta N)
      ≤ K * (N + 1) ^ E) :
    let cold := BoundedFamilySupport.actualMachine source a k CH Cpad cutoff D G copies E K symDen thrDen
      (CloseoutMassThreshold.literalWidth delta copies) delta (CloseoutSampledWitness.massCap delta copies) code
    let oldBudget := 2 * BoundedFamily.budget source a k CH Cpad cutoff D G copies E K symDen thrDen
      delta code x bits hpad
    ∃ data logSize, logSize ≤ oldBudget ∧
      Step (machine cold) (2 * oldBudget + 2) (fun _ => 0)
        (Fin.addCases (BoundedFamilySupport.input source a k D G E (List.ofFn x) bits)
          (fun _ : Fin 1 => [])) (fun _ => 0)
        (Fin.addCases data (fun _ : Fin 1 => List.replicate logSize false)) ∧
      readTapeBit (data (BoundedFamilySupport.flag source a k D G E)) 0 =
        BoundedFamily.passed source a k CH Cpad cutoff D G copies symDen thrDen delta code x bits hpad ∧
      (BoundedFamily.passed source a k CH Cpad cutoff D G copies symDen thrDen delta code x bits hpad = true →
        ∃ oldHeads, Cached source a k CH Cpad D G E code x bits hpad oldHeads data) := by
  let existence := bounded_cache source a k CH Cpad cutoff D G copies E K symDen thrDen delta code x bits
    hpad hD hsym hthr hK hcut hd hh hc hbudget
  let actual := Classical.choose existence
  have facts := Classical.choose_spec existence
  refine ⟨actual.final.tapes, actual.steps, facts.2.1,
    rewind_run _ _ _ actual facts.1 facts.2.1, facts.2.2.2.1, ?_⟩
  intro admitted
  exact ⟨actual.final.heads, facts.2.2.2.2.2 admitted⟩

/-- A fixed program moves exactly the chosen cache arity/index ports. The map
is a program parameter, independent of the current request and source length. -/
def entryDirections {t : ℕ} (slots : Fin 19 → Fin t) (i : Fin t) : HeadMove :=
  if i = slots 13 ∨ i = slots 14 then .right else .stay

def entryMachine {t : ℕ} (slots : Fin 19 → Fin t) :=
  DecompositionCountPosition.move (entryDirections slots)

def entryHeads {t : ℕ} (slots : Fin 19 → Fin t) (i : Fin t) : ℕ :=
  if i = slots 13 ∨ i = slots 14 then 1 else 0

theorem entry_step {t : ℕ} (slots : Fin 19 → Fin t) (data : Fin t → List Bool) :
    Step (entryMachine slots) 1 (fun _ => 0) data (entryHeads slots) data := by
  obtain ⟨r, hr, hf, hs⟩ := DecompositionCountPosition.move_run (entryDirections slots) (fun _ => 0) data
  refine ⟨r, hr, ?_, ?_, hs.le⟩
  · rw [hf]
    funext i
    simp only [entryDirections, entryHeads]
    split_ifs <;> rfl
  · rw [hf]

/-- Immediate physical composition: cold rewind, bridge, then reader entry. -/
theorem rewind_then_entry {t s : ℕ} (p : Machine t s) (fuel : ℕ) (input : Fin t → List Bool)
    (source : ExecutionReceipt t s) (hr : run p fuel input = some source) (hs : source.steps ≤ fuel)
    (slots : Fin 19 → Fin (t + 1)) :
    Step (Composition.machine (machine p) (entryMachine slots)) (2 * fuel + 4) (fun _ => 0)
      (Fin.addCases input (fun _ : Fin 1 => [])) (entryHeads slots)
      (Fin.addCases source.final.tapes (fun _ : Fin 1 => List.replicate source.steps false)) :=
  ((rewind_run p fuel input source hr hs).seq (entry_step slots _)).enlarge (by omega)

/-- The existing cache-head facts certify the two selected ports are distinct
from every cache port that must stay at zero. No new tape equality is assumed. -/
theorem entry_heads_at_cache {t : ℕ} (slots : Fin 19 → Fin t) (oldHeads : Fin t → ℕ)
    (h : ∀ j, oldHeads (slots j) = PCPPQueryClauseReuse.heads j) :
    ∀ j, entryHeads slots (slots j) = PCPPQueryClauseReuse.heads j := by
  intro j
  by_cases hj : j = 13 ∨ j = 14
  · rcases hj with rfl | rfl <;> simp [entryHeads, PCPPQueryClauseReuse.heads]
  · have hzero : oldHeads (slots j) = 0 := by
      simpa only [PCPPQueryClauseReuse.heads, if_neg hj] using h j
    have hn : ¬ (slots j = slots 13 ∨ slots j = slots 14) := by
      rintro (he | he)
      · have hone := h 13
        rw [← he, hzero] at hone
        simp [PCPPQueryClauseReuse.heads] at hone
      · have hone := h 14
        rw [← he, hzero] at hone
        simp [PCPPQueryClauseReuse.heads] at hone
    simp only [entryHeads, if_neg hn, PCPPQueryClauseReuse.heads, if_neg hj]

end
end NearCubicWires.RepairOrdinary.CloseoutFinalC10ColdCacheRewind
