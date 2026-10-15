import Proof.CaseAnalysis.RowsCountBinary
import Proof.PCP.VerifierDecodingSlice
import Proof.CaseAnalysis.CaseTwoDirect

/-! The original canonical description uses unary-rank fields.  Their
literal trailing false bits are allocation, so the existing total unary
converter consumes them without a new decoder or a numeric-value loop. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.RankField
open LocalBitMultitape RepairSource.VerifierDecoding OuterPCPRecovery
open RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem ordered_eq_pad (limit value : Nat) (hvalue : value ≤ limit) :
    orderedNatBits limit value = ZeroPadding.pad limit (List.replicate value true) := by
  apply List.ext_getElem
  · simp [orderedNatBits,ZeroPadding.pad_length,Nat.max_eq_left hvalue]
  · intro i hi hj
    have hil : i < limit := by simpa [orderedNatBits] using hi
    simp only [orderedNatBits,List.getElem_map,List.getElem_range]
    by_cases hiv : i < value
    · simp [ZeroPadding.pad,List.getElem_append_left,hiv]
    · simp only [decide_eq_false hiv,ZeroPadding.pad,List.length_replicate]
      rw [List.getElem_append_right (by simpa using Nat.le_of_not_gt hiv)]
      simp

def capacities (limit : Nat) (i : Fin 10) := if i=0 then limit else 0
def input (limit value : Nat) (i : Fin 10) :=
  if i=0 then orderedNatBits limit value else []

theorem binary_run (limit value : Nat) (hvalue : value ≤ limit) : ∃ out,
    ClockJoin.ReadyRun CloseoutRowsCountBinary.machine (CloseoutRowsCountBinary.budget value)
      (input limit value) out ∧
      out 1=List.replicate value true ∧
      out 3=UnaryTemplate.tape value ∧
      out 5=frame (CloseoutRowsCountBinary.bits value) := by
  obtain ⟨out,⟨base,hr,ht,hh,hs⟩,h1,h3,h5⟩ := CloseoutRowsCountBinary.count_run value
  obtain ⟨r,rr,rf,rs,_⟩ := ZeroPadding.run_config CloseoutRowsCountBinary.machine
    (capacities limit) _ _ base hr
  have hin : ZeroPadding.config (capacities limit)
      (initialConfiguration CloseoutRowsCountBinary.machine (CloseoutRowsCountBinary.input value)) =
      initialConfiguration CloseoutRowsCountBinary.machine (input limit value) := by
    apply configuration_ext
    · rfl
    · rfl
    · funext i
      by_cases hi : i=0
      · subst i
        exact (ordered_eq_pad limit value hvalue).symm
      · simp [ZeroPadding.config,initialConfiguration,capacities,input,CloseoutRowsCountBinary.input,hi]
  rw [hin] at rr
  refine ⟨r.final.tapes,⟨r,rr,rfl,?_,rs.trans_le hs⟩,?_,?_,?_⟩
  · intro i;rw [rf];exact hh i
  · rw [rf]
    change ZeroPadding.pad 0 (base.final.tapes 1)=_
    simpa only [ZeroPadding.pad_zero,ht] using h1
  · rw [rf]
    change ZeroPadding.pad 0 (base.final.tapes 3)=_
    simpa only [ZeroPadding.pad_zero,ht] using h3
  · rw [rf]
    change ZeroPadding.pad 0 (base.final.tapes 5)=_
    simpa only [ZeroPadding.pad_zero,ht] using h5

end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.RankField
