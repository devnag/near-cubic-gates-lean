import Proof.Hierarchy.CompetitorWitnessHeaderLayout

/-! Physical retained classifier flags are exactly the canonical witness
header predicate. The oracle and legal-sum payload words survive unchanged. -/
namespace NearCubicWires.RepairOrdinary.CompetitorWitnessHeader
open LocalBitMultitape RecoveryRootRound RecoveryExecution RadixSemantics CompetitorWitnessTriple
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def result (bits : List Bool) (j : Fin 5) := CompetitorWitnessKind.tapes
  (CompetitorWitnessKind.after (values bits j)) (CompetitorWitnessKind.flags (values bits j)) (2*(values bits j).length+1)

theorem before_output (x bits : List Bool) (k : ℕ) (j : Fin 5) (hk : j.val<k) (h5 : k≤5) (i : Fin 6) :
    before x bits k (slots j i)=result bits j i := by
  induction k with
  | zero=>omega
  | succ k ih=>
    rw [before,dif_pos (show k<5 by omega)]
    by_cases he : k=j.val
    · have hj : (⟨k,by omega⟩ : Fin 5)=j := Fin.ext he
      rw [hj,install_slot _ (slots_injective j)]
      rfl
    · rw [install_other]
      · exact ih (by omega) (by omega)
      · intro z
        exact slots_disjoint ⟨k,by omega⟩ j (by intro hh;exact he (congrArg Fin.val hh)) z i

theorem before_other (x bits : List Bool) (k : ℕ) (i : Fin 148)
    (hi : ∀ j z,slots j z≠i) : before x bits k i=start x bits i := by
  induction k with
  | zero=>rfl
  | succ k ih=>
    rw [before]
    split_ifs with hk
    · rw [install_other _ _ _ _ (hi _)];exact ih
    · exact ih

def testBits (bits : List Bool) : Fin 5 → Bool :=
  ![decide (field bits 0=1),decide (field bits 2=1),decide (field bits 4=1),
    decide (node bits 6=0),decide (field bits 1=0 ∨ field bits 1=3)]
def selected : Fin 5 → Fin 6 := ![2,2,2,1,5]
def gateSlots : Fin 6 → Fin 148 := ![123,128,133,137,146,147]

theorem physical_tests (x bits : List Bool) (j : Fin 5) :
    before x bits 5 (slots j (selected j))=[testBits bits j] := by
  rw [before_output x bits 5 j j.isLt (by rfl) (selected j)]
  fin_cases j <;> rfl

theorem output_blank (x bits : List Bool) : before x bits 5 147=[] := by
  rw [before_other x bits 5 147 (by intro j i;fin_cases j <;> fin_cases i <;> decide)]
  change start x bits ((25 : Fin 26).natAdd 122)=[]
  rw [start,Fin.addCases_right]

theorem oracle_retained (x bits : List Bool) :
    before x bits 5 78=frame (RecoveryFixedUnpair.leftWord (word bits 3)) := by
  rw [before_other x bits 5 78 (by intro j i;fin_cases j <;> fin_cases i <;> decide)]
  exact field_output x bits 3

theorem sum_retained (x bits : List Bool) :
    before x bits 5 118=frame (RecoveryFixedUnpair.leftWord (word bits 5)) := by
  rw [before_other x bits 5 118 (by intro j i;fin_cases j <;> fin_cases i <;> decide)]
  exact field_output x bits 5

def allTests (bs : Fin 5 → Bool) := (((bs 0 && bs 1) && bs 2) && bs 3) && bs 4

theorem allTests_iff (bits : List Bool) : allTests (testBits bits)=true ↔ headerValid bits := by
  simp [allTests,testBits,headerValid,structural,and_assoc]

def gateInput (bs : Fin 5 → Bool) : Fin 6 → List Bool := ![[bs 0],[bs 1],[bs 2],[bs 3],[bs 4],[]]
def gateOutput (bs : Fin 5 → Bool) : Fin 6 → List Bool := ![[bs 0],[bs 1],[bs 2],[bs 3],[bs 4],[allTests bs]]
def gate : Machine 6 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==1
  rule := fun q scanned=>if q.val=0 then some ⟨1,
    ![none,none,none,none,none,some ((((scanned 0 && scanned 1) && scanned 2) && scanned 3) && scanned 4)],fun _=>.stay⟩ else none

theorem gate_ready (bs : Fin 5 → Bool) : ReadyRun gate 1 (gateInput bs) (gateOutput bs) := by
  let final : Configuration 6 2 := ⟨1,fun _=>0,gateOutput bs⟩
  have h : step gate (initialConfiguration gate (gateInput bs))=some final := by
    apply congrArg some
    apply configuration_ext
    · rfl
    · rfl
    · funext i;fin_cases i <;> rfl
  obtain ⟨r,hr,hf,hs⟩ := (Timed.single (by rfl) h).run (by rfl)
  exact ⟨r,hr,by rw [hf],by intro i;rw [hf],hs⟩

noncomputable def last := RecoveryFocus.machine gateSlots gate
noncomputable def output (x bits : List Bool) := install gateSlots (before x bits 5) (gateOutput (testBits bits))

theorem last_ready (x bits : List Bool) : ReadyRun last 1 (before x bits 5) (output x bits) := by
  exact (gate_ready (testBits bits)).focus gateSlots (by decide) (before x bits 5) (by
    intro i;fin_cases i
    · exact physical_tests x bits 0
    · exact physical_tests x bits 1
    · exact physical_tests x bits 2
    · exact physical_tests x bits 3
    · exact physical_tests x bits 4
    · exact output_blank x bits)

theorem output_passes (x bits : List Bool) : readTapeBit (output x bits 147) 0=true ↔ headerValid bits := by
  have h := install_slot gateSlots (by decide) (before x bits 5) (gateOutput (testBits bits)) 5
  change output x bits 147=[allTests (testBits bits)] at h
  rw [h]
  exact allTests_iff bits

end NearCubicWires.RepairOrdinary.CompetitorWitnessHeader
