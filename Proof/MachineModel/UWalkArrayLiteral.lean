import Proof.MachineModel.UWalkArrayReady

/-! Literal97-tape initialized state with42 appended blank tapes. This
boundary directly supplies the actual139-tape walk bootstrap consumer. -/
namespace NearCubicWires.RepairOrdinary.UWalkArray
open LocalBitMultitape RepairSource.VerifierDecoding SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def extendHeads (H : Fin 97 → ℕ) : Heads :=
  fun i => Fin.addCases (motive := fun _ : Fin (97+42) => ℕ) H (fun _ : Fin 42 => 0) i
def extendTapes (T : Fin 97 → List Bool) : Store :=
  fun i => Fin.addCases (motive := fun _ : Fin (97+42) => List Bool) T (fun _ : Fin 42 => []) i
noncomputable def entry97 (H : Fin 97 → ℕ) (T : Fin 97 → List Bool) := entry (extendHeads H) (extendTapes T)

theorem extend_fresh (H : Fin 97 → ℕ) (T : Fin 97 → List Bool) : Fresh (extendHeads H) (extendTapes T) := by
  intro i hi
  have hnot : ¬i.val<97 := by omega
  simp [extendHeads,extendTapes,Fin.addCases,hnot]

theorem literal_run (w t j c : ℕ) (hw : 1 ≤ w)
    (H : Fin 97 → ℕ) (T : Fin 97 → List Bool)
    (hh : H 20=0 ∧ H 50=1 ∧ H 58=1 ∧ H 73=1)
    (ht : T 20=List.replicate w true ∧ T 50=CapMachine.counter c t ∧
      T 58=CompareMachine.word j ∧ T 73=CompareMachine.word w) :
    ∃ r,runFrom machine (budget w t j) (entry97 H T)=some r ∧ Numeric w t j c r.final ∧
      (∀ i : Fin 97,i.val≠20 → i.val≠50 → i.val≠58 → i.val≠73 →
        r.final.tapes (i.castAdd 42)=T i ∧ r.final.heads (i.castAdd 42)=H i) ∧
      r.final.tapes 136=(List.replicate t (frame (binary w 0))).flatten ∧
      (∀ i,135 ≤ i.val → r.final.heads i=0) ∧ r.steps ≤ budget w t j := by
  obtain ⟨r,hr,hnum,hpres,harray,hheads,hsteps⟩ := entry_run w t j c hw
    (extendHeads H) (extendTapes T) hh ht (extend_fresh H T)
  refine ⟨r,hr,hnum,?_,harray.trans (initial_array w t),hheads,hsteps⟩
  intro i hi20 hi50 hi58 hi73
  have h := hpres (i.castAdd 42) i.isLt hi20 hi50 hi58 hi73
  simpa [extendHeads,extendTapes] using h

end NearCubicWires.RepairOrdinary.UWalkArray
