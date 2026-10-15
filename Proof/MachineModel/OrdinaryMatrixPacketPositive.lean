import Proof.MachineModel.OrdinaryMatrixPacketNativeLoop

/-! The whole positive-width packet family. The enclosing header guard
supplies its real p sentinel after consuming the first mark; this branch
produces every other driver and all source workspace from blank tapes. -/
namespace NearCubicWires.RepairOrdinary.MatrixPacketPositive
open LocalBitMultitape MatrixScoreBatch RepairRepresentation
open MatrixPacketState (State)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def states {t s : ℕ} (_ : Machine t s) := s
noncomputable def first (a : WilliamsAlgorithm) (E C : ℕ) :=
  TapeEmbedding.machine 1 (MatrixPacketFirstBit.machine a E C)
noncomputable def machine (a : WilliamsAlgorithm) (E C : ℕ) :=
  Composition.machine (first a E C) (MatrixPacketLoop.machine a E)
noncomputable def input (a : WilliamsAlgorithm) (E C : ℕ) (r : Request) :=
  Composition.restart (TapeEmbedding.config (fun _ : Fin 1 => 2) (fun _ => UnaryTemplate.tape r.p)
    (initialConfiguration (MatrixPacketFirstBit.machine a E C) (MatrixPacketColdPrepare.cold a E r)))
    (machine a E C).start
noncomputable def budget (a : WilliamsAlgorithm) (E C : ℕ) (r : Request) :=
  MatrixPacketFirstBit.budget a E C r+1+
    MatrixPacketLoop.budget r (MatrixPacketBootstrapState.capacity E C r) (r.p-1)

theorem positive_run (a : WilliamsAlgorithm) (E C : ℕ) (r : Request) (hp : 0<r.p)
    (hcap : ∀ j<r.p,∀ negative,MatrixVariablePacketWorkspace.footprint a r j negative≤MatrixPacketBootstrapState.capacity E C r) :
    ∃ st : State a E (MatrixPacketBootstrapState.capacity E C r) r r.p
        (MatrixPacketLoop.appendPackets r 1 (r.p-1) (MatrixPacketSignPair.wordPair r 0)),∃ actual,
      runFrom (machine a E C) (budget a E C r) (input a E C r)=some actual ∧
      actual.final=Composition.rightConfig (states (first a E C)) (MatrixPacketNativeLoop.cfg 3
        (MatrixPacketSignPair.input a E (MatrixPacketBootstrapState.capacity E C r) r r.p
          (MatrixPacketLoop.appendPackets r 1 (r.p-1) (MatrixPacketSignPair.wordPair r 0)) st) r.p 1) ∧
      actual.steps≤budget a E C r := by
  obtain ⟨initial,base,hb,bh,bt,bs⟩:=MatrixPacketFirstBit.cold_run a E C r hp (hcap 0 hp)
  have he:=TapeEmbedding.run_embed (MatrixPacketFirstBit.machine a E C)
    (fun _ : Fin 1 => 2) (fun _ => UnaryTemplate.tape r.p) _ _ base hb
  let entered:=TapeEmbedding.receipt (fun _ : Fin 1 => 2) (fun _ => UnaryTemplate.tape r.p) base
  obtain ⟨st,tail,ht,tf,ts⟩:=MatrixPacketNativeLoop.loop_run a E (MatrixPacketBootstrapState.capacity E C r)
    r (r.p-1) 1 (MatrixPacketSignPair.wordPair r 0) initial (by omega) hcap
  have hi : Composition.restart entered.final (MatrixPacketLoop.machine a E).start=
      MatrixPacketNativeLoop.cfg 0
        (MatrixPacketSignPair.input a E (MatrixPacketBootstrapState.capacity E C r) r 1
          (MatrixPacketSignPair.wordPair r 0) initial) r.p 2 := by
    apply configuration_ext
    · rfl
    · change (Fin.addCases (m := MatrixPacketRestore.tapes a E) (n := 1) (motive := fun _ => ℕ)
        base.final.heads (fun _ => 2))=Fin.addCases initial.heads (fun _ => 2)
      exact congrArg (fun h => Fin.addCases (motive := fun _ => ℕ) h (fun _ : Fin 1 => 2)) bh
    · change (Fin.addCases (m := MatrixPacketRestore.tapes a E) (n := 1) (motive := fun _ => List Bool)
        base.final.tapes (fun _ => UnaryTemplate.tape r.p))=Fin.addCases initial.tapes (fun _ => UnaryTemplate.tape r.p)
      exact congrArg (fun t => Fin.addCases (motive := fun _ => List Bool) t (fun _ : Fin 1 => UnaryTemplate.tape r.p)) bt
  rw [←hi] at ht
  have whole:=Composition.run_join (first a E C) (MatrixPacketLoop.machine a E) _ _ _ entered tail he ht
  refine ⟨st,Composition.joinedReceipt entered tail,whole,?_,?_⟩
  · exact congrArg (Composition.rightConfig (states (first a E C))) tf
  · change base.steps+1+tail.steps≤budget a E C r
    unfold budget
    omega

theorem output_run (a : WilliamsAlgorithm) (E C : ℕ) (r : Request) (hp : 0<r.p)
    (hcap : ∀ j<r.p,∀ negative,MatrixVariablePacketWorkspace.footprint a r j negative≤MatrixPacketBootstrapState.capacity E C r) :
    ∃ actual,runFrom (machine a E C) (budget a E C r) (input a E C r)=some actual ∧
      actual.final.tapes ((MatrixPacketRestoreDock.slots a E (MatrixPacketState.output a)).castAdd 1)=MatrixScoreBatch.output r ∧
      actual.final.tapes ((MatrixPacketRestoreControls.controls a E 2).castAdd 1)=physicalInput r ∧
      actual.final.heads ((MatrixPacketRestoreControls.controls a E 2).castAdd 1)=0 ∧
      actual.steps≤budget a E C r := by
  obtain ⟨st,actual,ha,hf,hs⟩:=positive_run a E C r hp hcap
  have oldT (i : Fin (MatrixPacketRestore.tapes a E)) : actual.final.tapes (i.castAdd 1)=st.tapes i := by
    rw [hf]
    exact Fin.addCases_left (motive := fun _ => List Bool) (left := st.tapes) (right := fun _ : Fin 1 => UnaryTemplate.tape r.p) i
  have oldH (i : Fin (MatrixPacketRestore.tapes a E)) : actual.final.heads (i.castAdd 1)=st.heads i := by
    rw [hf]
    exact Fin.addCases_left (motive := fun _ => ℕ) (left := st.heads) (right := fun _ : Fin 1 => 1) i
  exact ⟨actual,ha,((oldT _).trans st.outputT).trans (MatrixPacketNativeLoop.first_tail_output r hp),
    (oldT _).trans (st.controlT 2),(oldH _).trans (st.controlH 2),hs⟩

end NearCubicWires.RepairOrdinary.MatrixPacketPositive
