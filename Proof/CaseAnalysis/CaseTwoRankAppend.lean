import Proof.CaseAnalysis.CaseTwoRankSlice
import Proof.PCP.PCPPNativeNaturalAppend

/-! Direct original unary-rank field to the existing native-number appender.
Trailing false field cells are explicit padding; no extra binary-width
producer or second native serializer is required. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.RankAppend
open LocalBitMultitape RepairRepresentation OuterPCPRecovery
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def capacities (limit : ℕ) (i : Fin 18) := if i=0 then limit else 0
def data (limit value : ℕ) (out : List Bool) (i : Fin 18) :=
  if i=0 then orderedNatBits limit value else if i=17 then out else []
noncomputable def entry (limit value : ℕ) (out : List Bool) :=
  (⟨PCPPNativeNaturalAppend.machine.start,PCPPNativeNaturalAppend.heads out,data limit value out⟩ :
    Configuration 18 _)

theorem append_run (limit value : ℕ) (out : List Bool) (hv : value ≤ limit) :
    ∃ r,runFrom PCPPNativeNaturalAppend.machine (PCPPNativeNaturalAppend.budget value)
      (entry limit value out)=some r ∧ r.steps ≤ PCPPNativeNaturalAppend.budget value ∧
      r.final.tapes 17=out++natWord value ∧ r.final.heads 17=(out++natWord value).length ∧
      r.final.tapes 1=List.replicate value true ∧ r.final.heads 1=0 := by
  obtain ⟨base,hr,hs,hout,hhead,hvalue,hvhead⟩:=PCPPNativeNaturalAppend.append_run value out
  obtain ⟨r,rr,rf,rs,_⟩:=ZeroPadding.run_config PCPPNativeNaturalAppend.machine
    (capacities limit) _ _ base hr
  have hi : ZeroPadding.config (capacities limit) (PCPPNativeNaturalAppend.entry value out)=
      entry limit value out := by
    apply configuration_ext
    · rfl
    · rfl
    · funext i
      by_cases hz : i=0
      · subst i
        exact (RankField.ordered_eq_pad limit value hv).symm
      · simp only [ZeroPadding.config,PCPPNativeNaturalAppend.entry,entry,
          PCPPNativeNaturalAppend.data,data,capacities,hz,ite_false,ZeroPadding.pad_zero]
  rw [hi] at rr
  refine ⟨r,rr,rs.trans_le hs,?_,?_,?_,?_⟩
  · rw [rf]
    change ZeroPadding.pad 0 (base.final.tapes 17)=_
    simpa only [ZeroPadding.pad_zero] using hout
  · rw [rf]
    exact hhead
  · rw [rf]
    change ZeroPadding.pad 0 (base.final.tapes 1)=_
    simpa only [ZeroPadding.pad_zero] using hvalue
  · rw [rf]
    exact hvhead

end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.RankAppend
