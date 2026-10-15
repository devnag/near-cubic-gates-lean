import Proof.Hierarchy.CompetitorComparisonEmit
import Proof.Hierarchy.HierarchyFixedWord

/-! A fixed rational threshold field is physically printed by the finite
program, then normalized using the runtime width tape. Only the fixed bit
word indexes the program; the runtime width does not index its control. -/
namespace NearCubicWires.RepairOrdinary.CompetitorFixedScalar
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey RadixSemantics
open CompetitorRationalProducts
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def printSlots : Fin 2 → Fin 6 := ![1,5]
def normalizeSlots (i : Fin 5) : Fin 6 := i.castAdd 1
def input (w : ℕ) : Fin 6 → List Bool := fun i => if i.val=0 then List.replicate w true else []
noncomputable def printProgram (bits : List Bool) :=
  RecoveryFocus.machine printSlots (HierarchyFixedWord.machine (frame bits))
noncomputable def normalizeProgram := RecoveryFocus.machine normalizeSlots ClockNormalize.machine
noncomputable def machine (bits : List Bool) := Composition.machine (printProgram bits) normalizeProgram
def budget (w : ℕ) (bits : List Bool) := 4*bits.length+4*w+9

theorem scalar_run (w : ℕ) (bits : List Bool) (hfit : bits.length≤w) :
    ∃ out,ClockJoin.ReadyRun (machine bits) (budget w bits) (input w) out ∧
      out 0=List.replicate w true ∧ out 2=frame (binary w (value bits)) := by
  obtain ⟨printed,hp,hpt,hph,hps⟩ := HierarchyFixedWord.word_ready (frame bits)
  have printReady : ClockJoin.ReadyRun (HierarchyFixedWord.machine (frame bits))
      (2*(frame bits).length+2) (fun _ => []) ![frame bits,List.replicate (frame bits).length false] :=
    ⟨printed,hp,hpt,hph,hps.le⟩
  let first := install printSlots (input w) ![frame bits,List.replicate (frame bits).length false]
  have hfirst := bounded_focus printSlots (by decide) _ _ _ printReady (input w)
    (by intro i; fin_cases i <;> rfl)
  obtain ⟨normalized,hn,hn0,_,hn2,_,_,hnh,hns⟩ := ClockScalarFields.scalar_run w bits hfit
  have normalReady : ClockJoin.ReadyRun ClockNormalize.machine (4*w+4)
      (ClockNormalize.input w bits) normalized.final.tapes := ⟨normalized,hn,rfl,hnh,hns.le⟩
  have hi : ∀ i,first (normalizeSlots i)=ClockNormalize.input w bits i := by
    intro i
    fin_cases i
    · exact install_other printSlots _ _ 0 (by decide)
    · exact install_slot printSlots (by decide) _ _ 0
    · exact install_other printSlots _ _ 2 (by decide)
    · exact install_other printSlots _ _ 3 (by decide)
    · exact install_other printSlots _ _ 4 (by decide)
  let out := install normalizeSlots first normalized.final.tapes
  have hnormal := bounded_focus normalizeSlots (by decide) _ _ _ normalReady first hi
  have hall := ClockJoin.join (printProgram bits) normalizeProgram _ _ _ _ _ hfirst hnormal
  have hc : (2*(frame bits).length+2)+1+(4*w+4)=budget w bits := by simp [budget]; omega
  rw [hc] at hall
  refine ⟨out,hall,?_,?_⟩
  · exact (install_slot normalizeSlots (by decide) _ _ 0).trans hn0
  · exact (install_slot normalizeSlots (by decide) _ _ 2).trans hn2

theorem number_run (w k n : ℕ) (hk : k≤w) (hn : n<2^k) :
    ∃ out,ClockJoin.ReadyRun (machine (binary k n)) (4*k+4*w+9) (input w) out ∧
      out 0=List.replicate w true ∧ out 2=frame (binary w n) := by
  obtain ⟨out,hr,h0,h2⟩ := scalar_run w (binary k n) (by simpa using hk)
  refine ⟨out,?_,h0,?_⟩
  · simpa only [budget,binary_length] using hr
  · simpa only [binary_value k n hn] using h2

end NearCubicWires.RepairOrdinary.CompetitorFixedScalar
