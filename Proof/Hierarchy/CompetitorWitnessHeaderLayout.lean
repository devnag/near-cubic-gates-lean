import Proof.Hierarchy.CompetitorWitnessKind
import Proof.Hierarchy.CompetitorWitnessTripleSemantics

/-! Five disjoint cold classifiers consume the actual extracted header
fields. Their flags occupy fresh physical tapes, with no supplied metadata. -/
namespace NearCubicWires.RepairOrdinary.CompetitorWitnessHeader
open LocalBitMultitape RecoveryRootRound RecoveryExecution RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def source : Fin 5 → Fin 148 := ![18,58,98,119,38]
def values (bits : List Bool) : Fin 5 → List Bool :=
  ![RecoveryFixedUnpair.leftWord (CompetitorWitnessTriple.word bits 0),
    RecoveryFixedUnpair.leftWord (CompetitorWitnessTriple.word bits 2),
    RecoveryFixedUnpair.leftWord (CompetitorWitnessTriple.word bits 4),
    CompetitorWitnessTriple.word bits 6,
    RecoveryFixedUnpair.leftWord (CompetitorWitnessTriple.word bits 1)]
def slots (j : Fin 5) (i : Fin 6) : Fin 148 := if i.val=0 then source j else ⟨121+5*j.val+i.val,by omega⟩

theorem source_lt (j : Fin 5) : (source j).val<122 := by fin_cases j <;> decide
theorem source_injective : Function.Injective source := by decide
theorem slots_injective (j : Fin 5) : Function.Injective (slots j) := by
  intro i k h
  have hv := congrArg Fin.val h
  have hs := source_lt j
  simp only [slots] at hv
  split_ifs at hv <;> apply Fin.ext <;> simp_all <;> omega

theorem slots_disjoint (j k : Fin 5) (hjk : j≠k) (i z : Fin 6) : slots j i≠slots k z := by
  intro h
  have hv := congrArg Fin.val h
  have hj := source_lt j
  have hk := source_lt k
  simp only [slots] at hv
  split_ifs at hv with hi hz hz
  · exact hjk (source_injective (Fin.ext hv))
  · change (source j).val=121+5*k.val+z.val at hv
    omega
  · change 121+5*j.val+i.val=(source k).val at hv
    omega
  · change 121+5*j.val+i.val=121+5*k.val+z.val at hv
    apply hjk
    apply Fin.ext
    omega

noncomputable def start (x bits : List Bool) : Fin 148 → List Bool := Fin.addCases
  (m := 122) (n := 26) (motive := fun _=>List Bool) (CompetitorWitnessTriple.stage x bits 6) (fun _=>[])
noncomputable def before (x bits : List Bool) : ℕ → Fin 148 → List Bool
  | 0=>start x bits
  | k+1=>if hk : k<5 then install (slots ⟨k,hk⟩) (before x bits k)
      (CompetitorWitnessKind.tapes (CompetitorWitnessKind.after (values bits ⟨k,hk⟩))
        (CompetitorWitnessKind.flags (values bits ⟨k,hk⟩)) (2*(values bits ⟨k,hk⟩).length+1)) else before x bits k

theorem start_input (x bits : List Bool) (j : Fin 5) (i : Fin 6) :
    start x bits (slots j i)=CompetitorWitnessKind.input (values bits j) i := by
  by_cases hi : i.val=0
  · have he : i=0 := Fin.ext hi
    subst i
    fin_cases j
    · exact CompetitorWitnessTriple.field_output x bits 0
    · exact CompetitorWitnessTriple.field_output x bits 2
    · exact CompetitorWitnessTriple.field_output x bits 4
    · exact CompetitorWitnessTriple.tail_output x bits
    · exact CompetitorWitnessTriple.field_output x bits 1
  · let k : Fin 26 := ⟨5*j.val+i.val-1,by omega⟩
    have he : slots j i=k.natAdd 122 := by apply Fin.ext;simp [slots,hi,k];omega
    rw [he]
    rw [start,Fin.addCases_right,CompetitorWitnessKind.input,if_neg hi]

theorem before_unused (x bits : List Bool) (k : ℕ) (j : Fin 5) (hk : k≤j.val) (i : Fin 6) :
    before x bits k (slots j i)=start x bits (slots j i) := by
  induction k with
  | zero=>rfl
  | succ k ih=>
    rw [before,dif_pos (show k<5 by omega),install_other]
    · exact ih (by omega)
    · intro z
      exact slots_disjoint ⟨k,by omega⟩ j (by intro he;have hv:=congrArg Fin.val he;change k=j.val at hv;omega) z i

noncomputable def program (j : Fin 5) := RecoveryFocus.machine (slots j) CompetitorWitnessKind.machine

theorem step_ready (x bits : List Bool) (j : Fin 5) :
    ReadyRun (program j) (16*(values bits j).length+27) (before x bits j.val) (before x bits (j.val+1)) := by
  have h := (CompetitorWitnessKind.kind_ready (values bits j)).focus (slots j) (slots_injective j)
    (before x bits j.val) (by intro i;rw [before_unused x bits j.val j (by rfl),start_input])
  simpa only [before,dif_pos j.isLt,program] using h

theorem values_length (bits : List Bool) (j : Fin 5) : (values bits j).length=bits.length := by
  fin_cases j <;> simp [values,RecoveryFixedUnpair.word_lengths,CompetitorWitnessTriple.word_length]

end NearCubicWires.RepairOrdinary.CompetitorWitnessHeader
