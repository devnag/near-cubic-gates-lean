import Proof.MachineModel.CountIndexCopy

/-! One shared-capacity sweep erases every count-conversion private cell.
Both copies of the actual index, the width and driver remain available. -/
namespace NearCubicWires.ExtIncidence.CountIndexClean
open LocalBitMultitape RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairOrdinary.SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def work : Fin 13→Fin 18:=![0,1,2,3,4,5,6,7,8,9,12,13,14]
def slots : Fin 15→Fin 18:=![0,1,2,3,4,5,6,7,8,9,12,13,14,16,17]
def erased (C : ℕ) : Fin 15→List Bool:=
  Fin.addCases (m:=14) (n:=1) (motive:=fun _=>List Bool)
    (Fin.addCases (m:=13) (n:=1) (motive:=fun _=>List Bool) (fun _ : Fin 13=>List.replicate C false)
    (fun _ : Fin 1=>List.replicate C true)) (fun _ : Fin 1=>List.replicate (C+1) false)
noncomputable def erase:=RecoveryFocus.machine slots (RecoveryScratchErase.resetMachine 13)
noncomputable def machine:=Composition.machine CountIndexCopy.machine erase
def budget (C w M : ℕ):=CountIndex.budget w M+4*C+10
def output (C w M : ℕ) (i : Fin 18) : List Bool:=
  if i=10 then ZeroPadding.pad C (List.replicate w true)
  else if i=11 ∨ i=15 then ZeroPadding.pad C (frame (binary w (M-1)))
  else if i=16 then List.replicate C true else if i=17 then List.replicate (C+1) false
  else List.replicate C false

theorem ready (C w M : ℕ) (hM : 0<M) (hw : M<2^w)
    (hC : CountIndex.budget w M+1≤C) :
    ClockJoin.ReadyRun machine (budget C w M) (CountIndexCopy.input C w M) (output C w M) := by
  obtain ⟨a,ca,a10,a11,a15,a16,a17,ab⟩:=CountIndexCopy.copy_run C w M hM hw hC
  have bound (j : Fin 13) : (a (work j)).length≤C:=by
    apply ab
    fin_cases j <;> decide
  have localRun:=RecoveryScratchErase.erase_ready C (C+1) (fun j=>a (work j)) bound
  have focused:=localRun.focus slots (by decide) a (by
    intro j
    fin_cases j
    all_goals first | exact a16 | exact a17 | rfl)
  have final : install slots a (erased C)=output C w M:=by
    funext i
    fin_cases i
    all_goals first
      | exact (install_slot slots (by decide) a (erased C) 0)
      | exact (install_slot slots (by decide) a (erased C) 1)
      | exact (install_slot slots (by decide) a (erased C) 2)
      | exact (install_slot slots (by decide) a (erased C) 3)
      | exact (install_slot slots (by decide) a (erased C) 4)
      | exact (install_slot slots (by decide) a (erased C) 5)
      | exact (install_slot slots (by decide) a (erased C) 6)
      | exact (install_slot slots (by decide) a (erased C) 7)
      | exact (install_slot slots (by decide) a (erased C) 8)
      | exact (install_slot slots (by decide) a (erased C) 9)
      | exact (install_slot slots (by decide) a (erased C) 10)
      | exact (install_slot slots (by decide) a (erased C) 11)
      | exact (install_slot slots (by decide) a (erased C) 12)
      | exact (install_slot slots (by decide) a (erased C) 13)
      | exact (install_slot slots (by decide) a (erased C) 14)
      | exact (install_other slots a (erased C) _ (by decide)).trans a10
      | exact (install_other slots a (erased C) _ (by decide)).trans a11
      | exact (install_other slots a (erased C) _ (by decide)).trans (a15.trans a11)
  have clean : ClockJoin.ReadyRun erase (2*C+4) a (output C w M):=by
    obtain ⟨r,hr,rt,rh,rs⟩:=focused
    refine ⟨r,hr,?_,rh,rs.le⟩
    exact rt.trans (by simpa only [Nat.max_self,erased] using final)
  have whole:=ClockJoin.join CountIndexCopy.machine erase _ _ _ _ _ ca clean
  have ht : CountIndexCopy.budget C w M+1+(2*C+4)=budget C w M:=by
    unfold CountIndexCopy.budget budget
    omega
  rw [ht] at whole
  exact whole

end NearCubicWires.ExtIncidence.CountIndexClean
