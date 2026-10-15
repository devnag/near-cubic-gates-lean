import Proof.MachineModel.UWalkArrayHead

/-! One actual139-tape controller executes numeric preparation followed by
the initial head array. Both return transitions are explicitly charged. -/
namespace NearCubicWires.RepairOrdinary.UWalkArray
open LocalBitMultitape RecoveryRootRound RecoveryExecution RepairSource.VerifierDecoding SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def statesOf {a b : ℕ} (_ : Machine a b) : ℕ := b
noncomputable def sizes : Fin 2 → ℕ := ![statesOf numericPhase,statesOf arrayPhase]
noncomputable def programs : (k : Fin 2) → Machine 139 (sizes k)
  | ⟨0,_⟩ => numericPhase
  | ⟨1,_⟩ => arrayPhase
  | ⟨n+2,h⟩ => False.elim (by omega)
def next (k : Fin 2) (_ : Fin (sizes k)) (_ : Fin 139 → Bool) : Option (Fin 2) :=
  if k.val=0 then some 1 else none
noncomputable def machine := RecoveryCalls.machine sizes programs 0 next
noncomputable def entry (H : Heads) (T : Store) := RecoveryCalls.restarted machine H T
def budget (w t j : ℕ) := UWalkNumbers.budget w t j+arrayBudget w t+2

theorem entry_run (w t j c : ℕ) (hw : 1 ≤ w) (H : Heads) (T : Store)
    (hh : H 20=0 ∧ H 50=1 ∧ H 58=1 ∧ H 73=1)
    (ht : T 20=List.replicate w true ∧ T 50=CapMachine.counter c t ∧
      T 58=CompareMachine.word j ∧ T 73=CompareMachine.word w)
    (hfresh : Fresh H T) :
    ∃ r,runFrom machine (budget w t j) (entry H T)=some r ∧
      Numeric w t j c r.final ∧ Preserved H T r.final ∧
      r.final.tapes 136=UHeadArray.fields w t ∧
      (∀ i,135 ≤ i.val → r.final.heads i=0) ∧ r.steps ≤ budget w t j := by
  obtain ⟨first,hfirst,hnum,hpres,hfresh4,hsteps⟩ := numeric_run w t j c hw H T hh ht hfresh
  obtain ⟨n,hn,hcall⟩ := call_receipt sizes programs 0 next 0 1
    (UWalkNumbers.budget w t j) _ first hfirst (by simp [next])
  obtain ⟨last,hlast,hlh,hlt,hlarray,_,hlsteps⟩ := array_run w t j c first.final hnum hfresh4
  obtain ⟨m,hm,hstop⟩ := stop_receipt sizes programs 0 next 1 (arrayBudget w t)
    _ last hlast (by simp [next])
  have h := hcall.trans hstop
  change Timed machine (n+m) (entry H T)
    (RecoveryCalls.stopped sizes last.final.heads last.final.tapes) at h
  obtain ⟨r,hr,hrf,hrs⟩ := h.run (by simp [machine,RecoveryCalls.machine,RecoveryCalls.stopped])
  have hcost : n+m ≤ budget w t j := by dsimp [budget]; omega
  have hmore := runFrom_moreFuel machine (n+m) (budget w t j-(n+m)) _ r hr
  rw [Nat.add_sub_of_le hcost] at hmore
  have hnumlast := array_preserves_numeric w t j c first.final last.final hnum hlh hlt
  have hpreslast := array_preserves_old H T first.final last.final hpres hlh hlt
  refine ⟨r,hmore,?_,?_,?_,?_,by omega⟩
  · rw [hrf]
    exact hnumlast
  · rw [hrf]
    exact hpreslast
  · rw [hrf]
    exact hlarray
  · intro i hi
    rw [hrf]
    change last.final.heads i=0
    rw [hlh]
    exact (hfresh4 i hi).1

theorem initial_array (w t : ℕ) : UHeadArray.fields w t=
    (List.replicate t (frame (binary w 0))).flatten := by
  have hz : binary w 0=List.replicate w false := by
    simpa using BoundedCounter.binary_of_value (List.replicate w false)
  simp [UHeadArray.fields,UHeadArray.field,hz]

theorem array_fits_cap (w t j : ℕ) : (UHeadArray.fields w t).length<UWalkCapacity.amount w t j := by
  rw [UHeadArray.fields_length]
  have h := (UWalkCapacity.amount_bounds w t j).1
  nlinarith

theorem budget_short (w t j c : ℕ) (ht : t ≤ c) (hj : j ≤ c) :
    budget w t j ≤ 32768*(c+1)*(w+1) := by
  dsimp [budget,UWalkNumbers.budget,arrayBudget,UHeadArray.budget]
  nlinarith

end NearCubicWires.RepairOrdinary.UWalkArray
