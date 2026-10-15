import Proof.Amplification.RecoveryPrefixSearch

/-! The unchanged total prefix search runs on the same request after the
single SAT flag. Its shared query port contains physically erased backing;
the existing zero-padding theorem accounts for that exact input. -/
namespace NearCubicWires.RepairSource.RecoveryBoundedSearchTail
open LocalBitMultitape RepairOrdinary OrdinaryOracleCompose RecoveryExecution RecoveryRootRound
open RecoveryPrefixCold RecoveryOracle
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots (i : Fin 389) : Fin 778 :=
  ⟨if i.val=0 then 0 else if i.val=344 then 344 else 389+i.val,
    by have hi:=i.isLt;split_ifs <;> omega⟩
theorem injective : Function.Injective slots := by
  intro a b he
  apply Fin.ext
  have hv:=congrArg (fun i : Fin 778=>i.val) he
  have ha:=a.isLt
  have hb:=b.isLt
  dsimp only [slots] at hv
  split_ifs at hv <;> omega
def ports : Ports 778 := ⟨by decide,775,by decide,344,by decide⟩
def caps (cap : Nat) (i : Fin 389) := if i.val=344 then cap else 0
noncomputable abbrev piece (C : Nat) := focused (RecoveryPrefixCold.program C true) slots
noncomputable abbrev program (C : Nat) := ports.program (piece C)

theorem ready (C payload total cap : Nat) (hC : 1073741824 ≤ C)
    (ambient : Fin 778→List Bool)
    (h0 : ambient 0=frame (RecoveryPrefixMeasure.request payload total))
    (hq : ambient 344=List.replicate cap false)
    (hfresh : ∀ i : Fin 389,i.val≠0 → i.val≠344 → ambient (slots i)=[]) :
    ∃ cost ≤ RecoveryPrefixCold.budget C payload total,∃ out : Fin 778→List Bool,
      Ready correctedSat (program C) cost ambient out ∧
      out 775=frame (RecoveryPrefixBody.search true payload total []) ∧
      out 357=ambient 357 := by
  classical
  obtain ⟨cost,hcost,out,hr,hout⟩:=whole_ready C payload total true hC
  have padded:=hr.padding (caps cap)
  have hinput : ∀ i : Fin 389,ambient (slots i)=
      ZeroPadding.pad (caps cap i) (input payload total i) := by
    intro i
    by_cases hz : i.val=0
    · have he : i=0:=Fin.ext hz
      subst i
      simpa [slots,caps,input,ZeroPadding.pad] using h0
    · by_cases hq' : i.val=344
      · have he : i=344:=Fin.ext hq'
        subst i
        simpa [slots,caps,input,ZeroPadding.pad] using hq
      · rw [hfresh i hz hq']
        simp [caps,input,hz,hq',ZeroPadding.pad]
  have full:=padded.focus ports slots injective rfl ambient hinput
  refine ⟨cost,hcost,_,full,?_,?_⟩
  · change install slots ambient _ (slots 386)=_
    rw [install_slot _ injective]
    simpa [caps,ZeroPadding.pad] using hout
  · exact install_other slots ambient _ (357 : Fin 778) (by
      intro j he
      have hv:=congrArg (fun i : Fin 778=>i.val) he
      change (if j.val=0 then 0 else if j.val=344 then 344 else 389+j.val)=357 at hv
      split_ifs at hv <;> omega)

end NearCubicWires.RepairSource.RecoveryBoundedSearchTail
