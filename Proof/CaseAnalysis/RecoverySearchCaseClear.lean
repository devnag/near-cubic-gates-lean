import Proof.CaseAnalysis.RecoverySearchCaseBank
import Proof.Amplification.RecoveryFocusRetained

/-! The actual SAT query word is erased before sharing its oracle port with
the total search. The retained request, answer and capacity are all paid. -/
namespace NearCubicWires.RepairSource.RecoveryBoundedSearchCase
open LocalBitMultitape RepairOrdinary OrdinaryOracleCompose RecoveryExecution RecoveryRootRound
open RecoveryPrefixCold RecoveryOracle
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def clearSlots : Fin 3→Fin 389 := ![344,4,5]
noncomputable def clearMachine := RecoveryFocus.machine clearSlots (RecoveryScratchErase.resetMachine 1)
noncomputable def cleared (cap : Nat) (ambient : Fin 389→List Bool) :=
  install clearSlots ambient ![List.replicate cap false,List.replicate cap true,
    List.replicate (cap+1) false]

theorem clear_ready (cap : Nat) (ambient : Fin 389→List Bool)
    (hw : (ambient 344).length ≤ cap)
    (hd : ambient 4=List.replicate cap true)
    (hl : ambient 5=List.replicate (cap+1) false) :
    Ready correctedSat (RecoveryPrefixCold.ports.program (ordinary clearMachine))
      (2*cap+4) ambient (cleared cap ambient) := by
  have h:= (RecoveryScratchErase.erase_ready cap (cap+1) (fun _ : Fin 1=>ambient 344)
    (fun _=>hw)).focus clearSlots (by decide) ambient (by
      intro i;fin_cases i;rfl;exact hd;exact hl)
  have outEq : install clearSlots ambient
      (Fin.addCases (m:=2) (n:=1)
        (Fin.addCases (m:=1) (n:=1) (fun _=>List.replicate cap false)
          (fun _=>List.replicate cap true))
        (fun _=>List.replicate (max (cap+1) (cap+1)) false))=cleared cap ambient := by
    apply congrArg (install clearSlots ambient)
    simp only [Nat.max_self]
    funext i
    fin_cases i <;> rfl
  rw [outEq] at h
  exact Ready.ordinary RecoveryPrefixCold.ports h

theorem cleared_fields (cap : Nat) (ambient : Fin 389→List Bool) :
    cleared cap ambient 344=List.replicate cap false ∧
    cleared cap ambient 0=ambient 0 ∧ cleared cap ambient 357=ambient 357 := by
  refine ⟨?_,?_,?_⟩
  · change install clearSlots ambient _ (clearSlots 0)=_
    rw [install_slot _ (by decide : Function.Injective clearSlots)]
    rfl
  · exact install_other _ _ _ _ (by decide)
  · exact install_other _ _ _ _ (by decide)

theorem prepare_request (C payload total : Nat) (out : Fin 389→List Bool)
    (h : ClockJoin.ReadyRun (prepare C) (RecoveryPrefixColdPrepare.budget C payload total)
      (unwrapped payload total) out) :
    out 0=frame (RecoveryPrefixMeasure.request payload total) := by
  obtain ⟨r,hr,ht,_,_⟩:=h
  have keep:=RecoveryFocus.run_other coldSlots (RecoveryPrefixColdPrepare.machine C) 0
    (by
      intro j he
      have hv:=congrArg (fun i : Fin 389=>i.val) he
      change j.val+1=0 at hv
      omega) _ _ r hr
  rw [ht] at keep
  refine keep.trans ?_
  change unwrapped payload total 0=frame (RecoveryPrefixMeasure.request payload total)
  unfold RecoveryPrefixCold.unwrapped
  change install unwrapSlots (input payload total)
    ![frame (RecoveryPrefixMeasure.request payload total),RecoveryPrefixMeasure.request payload total,
      List.replicate (RecoveryPrefixMeasure.request payload total).length false] (unwrapSlots 0)=_
  rw [install_slot _ unwrap_injective]
  rfl

end NearCubicWires.RepairSource.RecoveryBoundedSearchCase
