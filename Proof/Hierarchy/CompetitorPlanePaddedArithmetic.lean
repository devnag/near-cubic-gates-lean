import Proof.Hierarchy.CompetitorPlaneArithmetic

/-! The aligned-plane arithmetic consumes its actual finite zero workspace.
Its local support bound never includes the global count or accumulator stream. -/
namespace NearCubicWires.RepairOrdinary.CompetitorPlane
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def capacity (w : ℕ) := 4096*(w+1)^2
def arithmeticPadding (w : ℕ) (i : Fin 17) := if i.val=0 ∨ i.val=9 then 0 else capacity w
def paddedArithmeticInput (w count positive negative : ℕ) (bits : List Bool) : Fin 17 → List Bool :=
  fun i => ZeroPadding.pad (arithmeticPadding w i) (arithmeticInput w count positive negative bits i)

theorem arithmetic_budget_bound (w : ℕ) (bits : List Bool) (hb : bits.length≤w) :
    arithmeticBudget w bits≤256*(w+1)^2 := by
  unfold arithmeticBudget HierarchyMultiplyEntry.budget
  nlinarith

theorem arithmetic_input_support (w count positive negative : ℕ) (bits : List Bool)
    (hb : bits.length≤w) (i : Fin 17) :
    (arithmeticInput w count positive negative bits i).length≤capacity w := by
  have hw : 2*w+1≤capacity w := by unfold capacity; nlinarith
  refine Fin.addCases (m := 14) (n := 3) ?_ ?_ i
  · intro j
    simp only [arithmeticInput,Fin.addCases_left,CompetitorRationalProducts.input14_cases]
    split
    · simp; omega
    · split
      · simpa using hw
      · split
        · simp; omega
        · simp
  · intro j
    simp only [arithmeticInput,Fin.addCases_right]
    fin_cases j <;> simp <;> omega

theorem padded_arithmetic_run (sign : Bool) (w count positive negative : ℕ) (bits : List Bool)
    (hb : bits.length≤w) (hshift : count*2^bits.length<2^w)
    (hadd : count*value bits+(if sign then negative else positive)<2^w) :
    ∃ out,ClockJoin.ReadyRun (arithmeticProgram sign) (arithmeticBudget w bits)
        (paddedArithmeticInput w count positive negative bits) out ∧
      out (positiveTape sign)=ZeroPadding.pad (capacity w) (frame (binary w (nextPositive sign positive count bits))) ∧
      out (negativeTape sign)=ZeroPadding.pad (capacity w) (frame (binary w (nextNegative sign negative count bits))) ∧
      out 0=frame bits ∧ out 9=List.replicate w true ∧ out 12=List.replicate (capacity w) false ∧
      (∀ i,(out i).length≤capacity w) := by
  obtain ⟨out,ready,hp,hn,h0,_,h9,h12⟩ := arithmetic_run sign w count positive negative bits hshift hadd
  obtain ⟨base,hr,ht,hh,hs⟩ := ready
  have hs' := hs.trans (arithmetic_budget_bound w bits hb)
  have hend : base.steps+1≤capacity w := by unfold capacity; nlinarith
  have support := RecoveryTapeSupport.run_support (arithmeticProgram sign) _ _ base hr (capacity w) 0
    (by intro i; exact Nat.zero_le _) (by intro i; exact (arithmetic_input_support w count positive negative bits hb i).trans (Nat.le_max_left _ _))
  have hbound (i : Fin 17) : (base.final.tapes i).length≤capacity w := by
    simpa only [Nat.zero_add,max_eq_left hend] using support i
  obtain ⟨r,hrun,hf,hsteps,_⟩ := ZeroPadding.run_config (arithmeticProgram sign) (arithmeticPadding w) _ _ base hr
  have hi : ZeroPadding.config (arithmeticPadding w) (initialConfiguration (arithmeticProgram sign)
      (arithmeticInput w count positive negative bits))=
      initialConfiguration (arithmeticProgram sign) (paddedArithmeticInput w count positive negative bits) := rfl
  rw [hi] at hrun
  refine ⟨r.final.tapes,⟨r,hrun,rfl,?_,hsteps.trans_le hs⟩,?_,?_,?_,?_,?_,?_⟩
  · intro i
    rw [hf]
    exact hh i
  · cases sign <;> simpa [hf,ZeroPadding.config,ht,arithmeticPadding,positiveTape] using congrArg (ZeroPadding.pad (capacity w)) hp
  · cases sign <;> simpa [hf,ZeroPadding.config,ht,arithmeticPadding,negativeTape] using congrArg (ZeroPadding.pad (capacity w)) hn
  · simpa [hf,ZeroPadding.config,ht,arithmeticPadding] using h0
  · simpa [hf,ZeroPadding.config,ht,arithmeticPadding] using h9
  · have hw : 2*w+1≤capacity w := by unfold capacity; nlinarith
    simp [hf,ZeroPadding.config,ht,h12,arithmeticPadding,CompetitorReusableDecision.pad_zeros,max_eq_left hw]
  · intro i
    rw [hf]
    simp only [ZeroPadding.config,ZeroPadding.pad_length]
    exact max_le (by unfold arithmeticPadding; split <;> omega) (hbound i)

end NearCubicWires.RepairOrdinary.CompetitorPlane
