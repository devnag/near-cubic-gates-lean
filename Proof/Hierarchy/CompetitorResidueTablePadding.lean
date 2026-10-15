import Proof.Hierarchy.CompetitorResidueTableEntry

/-! Retained native drivers have real zero tails. Both transports preserve
exact executions; a paid width copy removes its tail on a fresh output. -/
namespace NearCubicWires.RepairOrdinary.CompetitorResidueTable
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open RepairSource.VerifierDecoding
open CompetitorPlaneStream (Cell oldWords)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def driverPadding (d : ℕ) : Fin 47 → ℕ := fun i => if i=27 then d else 0
def paddedReadyInput (d w q n : ℕ) (source : List Bool) : Fin 47 → List Bool :=
  fun i => ZeroPadding.pad (driverPadding d i) (readyInput w q n source i)

theorem padded_driver_run (d w q : ℕ) (xs : List Cell) (suffix : List Bool)
    (hq : q≤w) (hv : ∀ a∈xs,Valid w a) :
    ∃ out,ClockJoin.ReadyRun machine (budget w q xs.length)
      (paddedReadyInput d w q xs.length (oldWords w xs++suffix)) out ∧
      out 8=residueWords w q xs ∧ out 19=oldWords w xs++suffix ∧
      out 9=List.replicate w true ∧ out 4=List.replicate q true ∧
      out 27=ZeroPadding.pad d (CompareMachine.word xs.length) := by
  obtain ⟨produced,⟨base,hr,ht,hh,hs⟩,h8,h19,h9,h4,h27⟩ := ready_run w q xs suffix hq hv
  obtain ⟨r,hrun,hf,hsteps,_⟩ := ZeroPadding.run_config machine (driverPadding d) _ _ base hr
  refine ⟨r.final.tapes,⟨r,hrun,rfl,?_,hsteps.trans_le hs⟩,?_,?_,?_,?_,?_⟩
  · intro i
    rw [hf]
    exact hh i
  all_goals simp [hf,ZeroPadding.config,ht,driverPadding,h8,h19,h9,h4,h27]

def widthInput (d w : ℕ) : Fin 4 → List Bool :=
  ![ZeroPadding.pad d (List.replicate w true),[],[],[]]
def widthOutput (d w : ℕ) : Fin 4 → List Bool :=
  ![ZeroPadding.pad d (List.replicate w true),[],List.replicate w true,List.replicate (w+2) false]

theorem width_copy_run (d w : ℕ) :
    ClockJoin.ReadyRun ClockUnarySum.machine (2*w+6) (widthInput d w) (widthOutput d w) := by
  obtain ⟨base,hr,ht,hh,hs⟩ := ClockUnarySum.sum_ready w 0
  obtain ⟨r,hrun,hf,hsteps,_⟩ := ZeroPadding.run_config ClockUnarySum.machine ![d,0,0,0] _ _ base hr
  have hin : ZeroPadding.config ![d,0,0,0]
      (initialConfiguration ClockUnarySum.machine ![List.replicate w true,List.replicate 0 true,[],[]])=
      initialConfiguration ClockUnarySum.machine (widthInput d w) := by
    apply configuration_ext
    · rfl
    · rfl
    · funext i; fin_cases i <;> simp [ZeroPadding.config,initialConfiguration,widthInput]
  rw [hin] at hrun
  refine ⟨r,by simpa [run] using hrun,?_,?_,?_⟩
  · rw [hf]
    funext i
    fin_cases i <;> simp [ZeroPadding.config,ht,widthOutput]
  · intro i
    rw [hf]
    exact hh i
  · omega

end NearCubicWires.RepairOrdinary.CompetitorResidueTable
