import Proof.MachineModel.OrdinaryMatrixPacketController
import Proof.MachineModel.OrdinaryMatrixPacketBudget
import Proof.PCP.PCPSerializerTapeSupport

/-! One global rewind closes the actual all-plane cold controller. The
same executed run gives finite per-tape support for its caller's reuse. -/
namespace NearCubicWires.RepairOrdinary.MatrixPacketReset
open LocalBitMultitape MatrixScoreBatch RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine (a : WilliamsAlgorithm) (E C : ℕ) := Rewind.machine (MatrixPacketController.machine a E C)
noncomputable def input (a : WilliamsAlgorithm) (E : ℕ) (r : Request) : Fin (MatrixPacketHeader.tapes a E+1) → List Bool :=
  Fin.addCases (MatrixPacketHeader.input a E r) (fun _ : Fin 1 => [])
noncomputable def budget (a : WilliamsAlgorithm) (E C : ℕ) (r : Request) := 2*MatrixPacketController.budget a E C r+2
noncomputable def original (a : WilliamsAlgorithm) (E : ℕ) := (MatrixPacketController.original a E).castAdd 1
noncomputable def outputTape (a : WilliamsAlgorithm) (E : ℕ) := (MatrixPacketController.outputTape a E).castAdd 1

theorem input_bound (a : WilliamsAlgorithm) (E : ℕ) (r : Request)
    (i : Fin (MatrixPacketHeader.tapes a E+1)) : (input a E r i).length≤(physicalInput r).length := by
  refine Fin.addCases (m := MatrixPacketHeader.tapes a E) (n := 1) (fun j => ?_) (fun j => ?_) i
  · simp only [input,Fin.addCases_left]
    refine Fin.addCases (m := MatrixPacketRestore.tapes a E) (n := 22) (fun k => ?_) (fun k => ?_) j
    · rw [show MatrixPacketHeader.input a E r (k.castAdd 22)=MatrixPacketColdPrepare.cold a E r k from MatrixPacketHeader.input_old a E r k]
      unfold MatrixPacketColdPrepare.cold
      split <;> simp
    · rw [show MatrixPacketHeader.input a E r (k.natAdd (MatrixPacketRestore.tapes a E))=[] from MatrixPacketHeader.input_extra a E r k]
      simp
  · simp only [input,Fin.addCases_right,List.length_nil]
    exact Nat.zero_le _

theorem reset_run (a : WilliamsAlgorithm) (E C : ℕ) (r : Request)
    (hcap : ∀ j<r.p,∀ negative,MatrixVariablePacketWorkspace.footprint a r j negative≤MatrixPacketBootstrapState.capacity E C r) :
    ∃ actual,run (machine a E C) (budget a E C r) (input a E r)=some actual ∧
      actual.final.tapes (outputTape a E)=MatrixScoreBatch.output r ∧
      actual.final.tapes (original a E)=physicalInput r ∧
      (∀ i,actual.final.heads i=0) ∧
      (∀ i,(actual.final.tapes i).length≤ max (physicalInput r).length (budget a E C r+1)) ∧
      actual.steps≤budget a E C r := by
  obtain ⟨base,hb,bout,bsrc,_,bs⟩:=MatrixPacketController.controller_run a E C r hcap
  obtain ⟨actual,ha,ht,hh,hs,_⟩:=Rewind.reset_run (MatrixPacketController.machine a E C)
    (MatrixPacketController.budget a E C r) (MatrixPacketHeader.input a E r) base hb
  have hbound : 2*base.steps+2≤budget a E C r := by unfold budget; omega
  have hmore:=run_moreFuel (machine a E C) (2*base.steps+2) (budget a E C r-(2*base.steps+2)) _ actual ha
  rw [Nat.add_sub_of_le hbound] at hmore
  refine ⟨actual,hmore,(ht _).trans bout,(ht _).trans bsrc,hh,?_,hs.le.trans hbound⟩
  intro i
  have h:=PCPSerializerReuse.tape_support (machine a E C) (budget a E C r)
    (initialConfiguration (machine a E C) (input a E r)) actual hmore i (physicalInput r).length 0
    (by rfl) ((input_bound a E r i).trans (Nat.le_max_left _ _))
  have hb' : actual.steps≤budget a E C r := hs.le.trans hbound
  exact h.trans (by gcongr; omega)

end NearCubicWires.RepairOrdinary.MatrixPacketReset
