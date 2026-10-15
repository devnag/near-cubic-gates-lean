import Proof.CaseAnalysis.CaseTwoFieldClear
import Proof.CaseAnalysis.CaseTwoAdvance

/-! One complete traversal field: append its original native natural,
physically clear the work bank, and advance the shared paid source offset. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.FieldStep
open LocalBitMultitape RepairRepresentation OuterPCPRecovery RecoveryRootRound
open FieldClear
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def advanceSlots : Fin 3→Fin 25:=![3,2,22]
noncomputable def advance:=RecoveryFocus.machine advanceSlots Advance.machine
noncomputable def machine:=Composition.machine FieldClear.machine advance
def budget (offset width value C : ℕ):=FieldClear.budget offset width value C+2*(width+offset)+7

theorem field_run (pre tail : List Bool) (limit value C : ℕ) (out : List Bool)
    (hv : value≤limit) (hsource : 2*(pre++orderedNatBits limit value++tail).length+1≤C)
    (hoffset : pre.length+limit+2≤C)
    (hbudget : FieldNative.budget pre.length limit value+1≤C) :
    let source:=pre++orderedNatBits limit value++tail
    ∃ r,runFrom machine (budget pre.length limit value C)
      ⟨machine.start,heads out,data C source pre.length limit out⟩=some r ∧
      r.steps≤budget pre.length limit value C ∧
      r.final.heads=heads (out++natWord value) ∧
      r.final.tapes=data C source (pre.length+limit) limit (out++natWord value) := by
  let source:=pre++orderedNatBits limit value++tail
  obtain ⟨a,ar,asteps,ah,atapes⟩:=FieldClear.field_run pre tail limit value C out hv hsource
    (by omega) (by omega) hbudget
  obtain ⟨b,br,bh,bt,bs⟩:=(Advance.ready limit pre.length C (by omega)).focus_at advanceSlots
    (by decide) a.final.heads a.final.tapes
    (by intro j;rw [atapes];fin_cases j <;> rfl)
    (by intro j;rw [ah];fin_cases j <;> rfl)
  have whole:=Composition.run_join FieldClear.machine advance _ _ _ a b ar br
  have hb:FieldClear.budget pre.length limit value C+1+(2*(limit+pre.length)+6)=
      budget pre.length limit value C:=by unfold budget;omega
  rw [hb] at whole
  refine ⟨Composition.joinedReceipt a b,whole,?_,bh.trans ah,?_⟩
  · change a.steps+1+b.steps≤budget pre.length limit value C
    unfold budget;omega
  · change b.final.tapes=_
    rw [bt]
    apply HierarchyAllocation.install_eq advanceSlots (by decide)
    · intro j;fin_cases j <;> rfl
    · intro i hi
      rw [atapes]
      have hn : i≠2:=fun h=>hi 1 h.symm
      simp only [data,hn,if_false]

end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.FieldStep
