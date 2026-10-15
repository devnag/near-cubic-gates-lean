import Proof.Hierarchy.CompetitorDimensionConstants

/-! From the one supplied raw scalar width, the actual prefix constructs
its successor and its reusable sentinel template. All private tapes start
blank; the finite width/capacity coefficients are physically printed. -/
namespace NearCubicWires.RepairOrdinary.CompetitorDimensions
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open CompetitorRationalProducts
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def constantSlots (i : Fin 6) : Fin 13 := ⟨i.val+1,by omega⟩
def sumSlots : Fin 4 → Fin 13 := ![0,1,7,8]
def templateSlots : Fin 5 → Fin 13 := ![7,9,10,11,12]
def bootstrapInput (b : ℕ) : Fin 13 → List Bool := fun i => if i.val=0 then List.replicate b true else []
noncomputable def constantsProgram := RecoveryFocus.machine constantSlots CompetitorDimensionConstants.machine
noncomputable def sumProgram := RecoveryFocus.machine sumSlots ClockUnarySum.machine
noncomputable def templateProgram := RecoveryFocus.machine templateSlots MatrixRawDimension.resetMachine
noncomputable def bootstrapProgram := Composition.machine constantsProgram (Composition.machine sumProgram templateProgram)
def bootstrapBudget (b : ℕ) := 6*b+8236

theorem bootstrap_run (b : ℕ) : ∃ out,ClockJoin.ReadyRun bootstrapProgram (bootstrapBudget b) (bootstrapInput b) out ∧
    out 0=List.replicate b true ∧ out 3=UnaryTemplate.tape 2 ∧ out 5=UnaryTemplate.tape 4096 ∧
    out 9=List.replicate (b+1) true ∧ out 10=List.replicate (b+1) true ∧ out 11=UnaryTemplate.tape (b+1) := by
  obtain ⟨constants,hconstants,hc0,hc2,hc4⟩ := CompetitorDimensionConstants.constants_run
  let first := install constantSlots (bootstrapInput b) constants
  have hfirst := bounded_focus constantSlots (by decide) _ _ _ hconstants (bootstrapInput b)
    (by intro i; fin_cases i <;> rfl)
  have hiSum : ∀ i,first (sumSlots i)=![List.replicate b true,List.replicate 1 true,[],[]] i := by
    intro i
    fin_cases i
    · exact install_other constantSlots _ _ 0 (by decide)
    · exact (install_slot constantSlots (by decide) _ constants 0).trans hc0
    · exact install_other constantSlots _ _ 7 (by decide)
    · exact install_other constantSlots _ _ 8 (by decide)
  let sumOut := ![List.replicate b true,List.replicate 1 true,List.replicate (b+1) true,List.replicate (b+1+2) false]
  let second := install sumSlots first sumOut
  have hsecond := bounded_focus sumSlots (by decide) _ _ _ (ClockUnarySum.sum_ready b 1) first hiSum
  obtain ⟨templated,ht,ht1,ht2,ht3,hth,hts⟩ := MatrixRawDimension.reset_run (b+1)
  have templateReady : ClockJoin.ReadyRun MatrixRawDimension.resetMachine (4*(b+1)+8)
      (MatrixRawDimension.resetInput (b+1)) templated.final.tapes := ⟨templated,ht,rfl,hth,hts.le⟩
  have hiTemplate : ∀ i,second (templateSlots i)=MatrixRawDimension.resetInput (b+1) i := by
    intro i
    fin_cases i
    · exact install_slot sumSlots (by decide) _ sumOut 2
    · exact (install_other sumSlots _ _ 9 (by decide)).trans (install_other constantSlots _ _ 9 (by decide))
    · exact (install_other sumSlots _ _ 10 (by decide)).trans (install_other constantSlots _ _ 10 (by decide))
    · exact (install_other sumSlots _ _ 11 (by decide)).trans (install_other constantSlots _ _ 11 (by decide))
    · exact (install_other sumSlots _ _ 12 (by decide)).trans (install_other constantSlots _ _ 12 (by decide))
  let out := install templateSlots second templated.final.tapes
  have hlast := bounded_focus templateSlots (by decide) _ _ _ templateReady second hiTemplate
  have htail := ClockJoin.join sumProgram templateProgram _ _ _ _ _ hsecond hlast
  have hall := ClockJoin.join constantsProgram (Composition.machine sumProgram templateProgram) _ _ _ _ _ hfirst htail
  have hcost : 8214+1+((2*(b+1)+6)+1+(4*(b+1)+8))=bootstrapBudget b := by unfold bootstrapBudget; omega
  rw [hcost] at hall
  refine ⟨out,hall,?_,?_,?_,?_,?_,?_⟩
  · exact (install_other templateSlots _ _ 0 (by decide)).trans (install_slot sumSlots (by decide) _ sumOut 0)
  · exact (install_other templateSlots _ _ 3 (by decide)).trans
      ((install_other sumSlots _ _ 3 (by decide)).trans ((install_slot constantSlots (by decide) _ constants 2).trans hc2))
  · exact (install_other templateSlots _ _ 5 (by decide)).trans
      ((install_other sumSlots _ _ 5 (by decide)).trans ((install_slot constantSlots (by decide) _ constants 4).trans hc4))
  · exact (install_slot templateSlots (by decide) _ templated.final.tapes 1).trans ht1
  · exact (install_slot templateSlots (by decide) _ templated.final.tapes 2).trans ht2
  · exact (install_slot templateSlots (by decide) _ templated.final.tapes 3).trans ht3

end NearCubicWires.RepairOrdinary.CompetitorDimensions
