import Proof.CaseAnalysis.CapacityBudget
import Proof.Amplification.RecoveryScratchErase

/-! The common dispatcher clears its actual oracle query using a capacity
physically produced from the final address. Other machine work is untouched. -/
namespace NearCubicWires.RepairSource.CloseoutCommonQueryClear
open LocalBitMultitape RepairOrdinary RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def old (i : Fin 26) : Fin 28 := i.castAdd 2
def slots : Fin 3→Fin 28 := ![26,24,27]
def input (bits query : List Bool) : Fin 28→List Bool :=
  Fin.addCases (m := 26) (n := 2) (motive := fun _=>List Bool)
    (CloseoutCapacity.input bits) ![query,[]]
def first (A B : ℕ) := RecoveryFocus.machine old (CloseoutCapacity.machine A B)
def last := RecoveryFocus.machine slots (RecoveryScratchErase.resetMachine 1)
def machine (A B : ℕ) := Composition.machine (first A B) last
def budget (A B : ℕ) (bits : List Bool) :=
  CloseoutCapacity.budget A B bits+1+(2*CloseoutCapacity.capacity A B bits.length+4)

theorem old_injective : Function.Injective old := by
  intro i j h
  exact Fin.ext (congrArg (fun i : Fin 28=>i.val) h)
theorem slots_injective : Function.Injective slots := by decide
theorem outside_old (i : Fin 28) (hi : 26 ≤ i.val) : ∀ j,old j≠i := by
  intro j he
  have h:=congrArg Fin.val he
  have hj:=j.isLt
  simp only [old,Fin.val_castAdd] at h
  omega

theorem clear_run (A B : ℕ) (bits query : List Bool)
    (hq : query.length ≤ CloseoutCapacity.capacity A B bits.length) :
    ∃ out,ClockJoin.ReadyRun (machine A B) (budget A B bits) (input bits query) out ∧
      out 26=List.replicate (CloseoutCapacity.capacity A B bits.length) false ∧
      out 0=frame bits := by
  let C:=CloseoutCapacity.capacity A B bits.length
  obtain ⟨prepared,hp,hraw,_ht,haddress⟩:=CloseoutCapacity.capacity_run A B bits
  have hfirst:=hp.focus old old_injective (input bits query)
    (by intro j;simp only [input,old,Fin.addCases_left])
  let middle:=install old (input bits query) prepared
  have hquery:middle 26=query := by
    change install old (input bits query) prepared 26=query
    rw [install_other _ _ _ _ (outside_old 26 (by decide))]
    rfl
  have hscratch:middle 27=[] := by
    change install old (input bits query) prepared 27=[]
    rw [install_other _ _ _ _ (outside_old 27 (by decide))]
    rfl
  have hdriver:middle 24=List.replicate C true := by
    change install old (input bits query) prepared (old 24)=_
    rw [install_slot _ old_injective]
    exact hraw
  let erased : Fin 3→List Bool:=Fin.addCases (m := 2) (n := 1) (motive := fun _=>List Bool)
    (Fin.addCases (m := 1) (n := 1) (motive := fun _=>List Bool)
      (fun _ : Fin 1=>List.replicate C false) (fun _ : Fin 1=>List.replicate C true))
    (fun _ : Fin 1=>List.replicate (max 0 (C+1)) false)
  have he:=RecoveryScratchErase.erase_ready C 0 (fun _ : Fin 1=>query) (fun _=>hq)
  have hlast:=he.focus slots slots_injective middle (by
    intro j
    fin_cases j
    · exact hquery
    · exact hdriver
    · exact hscratch)
  obtain ⟨lastReceipt, lastRun, lastTapes, lastHeads, lastSteps⟩ := hlast
  have hlastBound : ClockJoin.ReadyRun last (2*C+4) middle
      (install slots middle erased) :=
    ⟨lastReceipt, lastRun, lastTapes, lastHeads, lastSteps.le⟩
  refine ⟨install slots middle erased,ClockJoin.join _ _ _ _ _ _ _ hfirst hlastBound,?_,?_⟩
  · change install slots middle erased (slots 0)=_
    rw [install_slot _ slots_injective]
    rfl
  · rw [install_other _ _ _ _ (by intro j;fin_cases j <;> decide)]
    change install old (input bits query) prepared (old 0)=_
    rw [install_slot _ old_injective]
    exact haddress

end
end NearCubicWires.RepairSource.CloseoutCommonQueryClear
