import Proof.CaseAnalysis.WitnessSourceCounts
import Proof.CaseAnalysis.CloseoutScheduleMetadata
import Proof.CaseAnalysis.ScheduleCompare

/-! The weak machine owns its finite input cutoff, independently of the
later refuter onset. The actual original N is counted once and retained;
the fixed threshold and comparison are physical preprocessing calls. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.InputGuard
open LocalBitMultitape RecoveryRootRound RepairSource.CloseoutSchedule
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def literalSlots : Fin 2→Fin 8:=![4,5]
def compareSlots : Fin 4→Fin 8:=![4,2,6,7]
noncomputable def counted:=Composition.machine Metadata.lengthProgram Metadata.copyProgram
noncomputable def literal (cutoff : ℕ):=
  RecoveryFocus.machine literalSlots (HierarchyFixedWord.machine (UnaryTemplate.tape cutoff))
noncomputable def compare:=RecoveryFocus.machine compareSlots MatrixBucketDimensions.Compare.machine
noncomputable def first (cutoff : ℕ):=Composition.machine counted (literal cutoff)
noncomputable def machine (cutoff : ℕ):=Composition.machine (first cutoff) compare
def input:=Metadata.input
def literalOut (cutoff : ℕ) : Fin 2→List Bool:=
  ![UnaryTemplate.tape cutoff,List.replicate (cutoff+2) false]
noncomputable def middle (cutoff : ℕ) (bits : List Bool):=
  install literalSlots (Metadata.copied bits) (literalOut cutoff)
def budget (cutoff : ℕ) (bits : List Bool):=
  (4*bits.length+5)+1+(2*bits.length+6)+1+(2*(cutoff+2)+2)+1+(2*min cutoff bits.length+6)

theorem guard_run (cutoff : ℕ) (bits : List Bool) : ∃ output,
    ClockJoin.ReadyRun (machine cutoff) (budget cutoff bits) (input bits) output ∧
      output 0=frame bits ∧ output 1=CompareMachine.word bits.length ∧
      output 2=List.replicate bits.length true ∧ output 6=[decide (cutoff ≤ bits.length)]:=by
  have hc:=ClockJoin.join Metadata.lengthProgram Metadata.copyProgram _ _ _ _ _
    (Metadata.length_run bits) (Metadata.copy_run bits)
  have hl:ClockJoin.ReadyRun (HierarchyFixedWord.machine (UnaryTemplate.tape cutoff)) (2*(cutoff+2)+2)
      (fun _=>[]) (literalOut cutoff):=by
    simpa [UnaryTemplate.tape,literalOut,Nat.add_assoc] using literal_ready (UnaryTemplate.tape cutoff)
  have hlf:=hl.focus literalSlots (by decide) (Metadata.copied bits) (by intro j;fin_cases j <;> rfl)
  have hcomp:=(RawCompare.compare_cold cutoff bits.length).focus compareSlots (by decide)
      (middle cutoff bits) (by
    intro j;fin_cases j
    · exact install_slot literalSlots (by decide) _ _ 0
    all_goals rw [middle,install_other _ _ _ _ (by decide)];rfl)
  have hall:=ClockJoin.join (first cutoff) compare _ _ _ _ _
    (ClockJoin.join counted (literal cutoff) _ _ _ _ _ hc hlf) hcomp
  refine ⟨_,hall,?_,?_,?_,?_⟩
  · rw [install_other _ _ _ _ (by decide),middle,install_other _ _ _ _ (by decide)]
    rfl
  · rw [install_other _ _ _ _ (by decide),middle,install_other _ _ _ _ (by decide)]
    rfl
  · exact install_slot compareSlots (by decide) _ _ 1
  · exact install_slot compareSlots (by decide) _ _ 2

end NearCubicWires.RepairOrdinary.CloseoutWitness.InputGuard
