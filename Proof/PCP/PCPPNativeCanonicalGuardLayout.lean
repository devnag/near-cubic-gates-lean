import Proof.PCP.PCPPNativeCanonicalHeader
import Proof.Hierarchy.CompetitorWitnessKind

/-! Three paid existing cold classifiers test the canonical circuit's
two tagged cells and zero tail, preserving both live payloads. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeCanonicalGuard
open LocalBitMultitape RecoveryRootRound RecoveryExecution RadixSemantics CompetitorWitnessTriple
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def source : Fin 3→Fin 138 := ![18,58,79]
def values (bits : List Bool) : Fin 3→List Bool :=
  ![RecoveryFixedUnpair.leftWord (word bits 0),RecoveryFixedUnpair.leftWord (word bits 2),word bits 4]
def slots (j : Fin 3) (i : Fin 6) : Fin 138 := if i.val=0 then source j else ⟨121+5*j.val+i.val,by omega⟩
theorem slots_injective (j : Fin 3) : Function.Injective (slots j) := by fin_cases j <;> decide
theorem slots_disjoint : ∀ j k : Fin 3,j≠k→∀ i z : Fin 6,slots j i≠slots k z := by decide

noncomputable def start (x bits : List Bool) : Fin 138→List Bool :=
  Fin.addCases (m:=122) (n:=16) (CompetitorWitnessTriple.stage x bits 6) (fun _=>[])
def result (bits : List Bool) (j : Fin 3) := CompetitorWitnessKind.tapes
  (CompetitorWitnessKind.after (values bits j)) (CompetitorWitnessKind.flags (values bits j)) (2*(values bits j).length+1)
noncomputable def before (x bits : List Bool) : ℕ→Fin 138→List Bool
  | 0=>start x bits
  | k+1=>if hk:k<3 then install (slots ⟨k,hk⟩) (before x bits k) (result bits ⟨k,hk⟩) else before x bits k

theorem start_input (x bits : List Bool) (j : Fin 3) (i : Fin 6) :
    start x bits (slots j i)=CompetitorWitnessKind.input (values bits j) i := by
  by_cases hi:i.val=0
  · have he:i=0:=Fin.ext hi
    subst i
    fin_cases j
    · exact field_output x bits 0
    · exact field_output x bits 2
    · exact PCPPNativeCanonical.tail_retained x bits
  · let k:Fin 16:=⟨5*j.val+i.val-1,by omega⟩
    have he:slots j i=k.natAdd 122:=by apply Fin.ext;simp [slots,hi,k];omega
    rw [he,start,Fin.addCases_right,CompetitorWitnessKind.input,if_neg hi]

theorem before_unused (x bits : List Bool) (k : ℕ) (j : Fin 3) (hk:k≤j.val) (i : Fin 6) :
    before x bits k (slots j i)=start x bits (slots j i) := by
  induction k with
  | zero=>rfl
  | succ k ih=>
    rw [before,dif_pos (show k<3 by omega),install_other]
    · exact ih (by omega)
    · intro z
      exact slots_disjoint ⟨k,by omega⟩ j (by intro he;have hv:=congrArg Fin.val he;change k=j.val at hv;omega) z i

noncomputable def program (j : Fin 3) := RecoveryFocus.machine (slots j) CompetitorWitnessKind.machine
theorem step_ready (x bits : List Bool) (j : Fin 3) : ReadyRun (program j) (16*(values bits j).length+27)
    (before x bits j.val) (before x bits (j.val+1)) := by
  have h:=(CompetitorWitnessKind.kind_ready (values bits j)).focus (slots j) (slots_injective j)
    (before x bits j.val) (by intro i;rw [before_unused x bits j.val j (by rfl),start_input])
  simpa only [before,dif_pos j.isLt,program,result] using h

theorem values_length (bits : List Bool) (j : Fin 3) : (values bits j).length=bits.length := by
  fin_cases j <;> simp [values,RecoveryFixedUnpair.word_lengths,CompetitorWitnessTriple.word_length]

theorem before_output (x bits : List Bool) (k : ℕ) (j : Fin 3) (hk:j.val<k) (h3:k≤3) (i : Fin 6) :
    before x bits k (slots j i)=result bits j i := by
  induction k with
  | zero=>omega
  | succ k ih=>
    rw [before,dif_pos (show k<3 by omega)]
    by_cases he:k=j.val
    · have hj:(⟨k,by omega⟩ : Fin 3)=j:=Fin.ext he
      rw [hj,install_slot _ (slots_injective j)]
    · rw [install_other]
      · exact ih (by omega) (by omega)
      · intro z
        exact slots_disjoint ⟨k,by omega⟩ j (by intro hh;exact he (congrArg Fin.val hh)) z i

theorem before_other (x bits : List Bool) (k : ℕ) (i : Fin 138)
    (hi:∀ j z,slots j z≠i) : before x bits k i=start x bits i := by
  induction k with
  | zero=>rfl
  | succ k ih=>
    rw [before]
    split_ifs with hk
    · rw [install_other _ _ _ _ (hi _)];exact ih
    · exact ih

def tests (bits : List Bool) : Fin 3→Bool :=
  ![decide (field bits 0=1),decide (field bits 2=1),decide (node bits 4=0)]
def selected : Fin 3→Fin 6 := ![2,2,1]
def gateSlots : Fin 4→Fin 138 := ![123,128,132,137]

theorem physical_tests (x bits : List Bool) (j : Fin 3) :
    before x bits 3 (slots j (selected j))=[tests bits j] := by
  rw [before_output x bits 3 j j.isLt (by rfl) (selected j)]
  fin_cases j <;> rfl
theorem output_blank (x bits : List Bool) : before x bits 3 137=[] := by
  rw [before_other x bits 3 137 (by intro j i;fin_cases j <;> fin_cases i <;> decide)]
  change start x bits ((15 : Fin 16).natAdd 122)=[]
  rw [start,Fin.addCases_right]
theorem nodes_retained (x bits : List Bool) : before x bits 3 38=frame (PCPPNativeCanonical.nodeWord bits) := by
  rw [before_other x bits 3 38 (by intro j i;fin_cases j <;> fin_cases i <;> decide)]
  exact field_output x bits 1
theorem output_retained (x bits : List Bool) : before x bits 3 78=frame (PCPPNativeCanonical.outputWord bits) := by
  rw [before_other x bits 3 78 (by intro j i;fin_cases j <;> fin_cases i <;> decide)]
  exact field_output x bits 3

end NearCubicWires.RepairOrdinary.PCPPNativeCanonicalGuard
