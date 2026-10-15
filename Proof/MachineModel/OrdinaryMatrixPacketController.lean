import Proof.MachineModel.OrdinaryMatrixPacketBranch

/-! One cold finite controller physically branches on the parsed p
sentinel. Zero width emits no packets; positive width executes all 2p. -/
namespace NearCubicWires.RepairOrdinary.MatrixPacketController
open LocalBitMultitape RecoveryExecution RecoveryRootRound MatrixScoreBatch RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def sizes (a : WilliamsAlgorithm) (E C : ℕ) : Fin 2 → ℕ :=
  ![MatrixPacketPositive.states (MatrixPacketHeader.machine a E),MatrixPacketPositive.states (MatrixPacketBranch.machine a E C)]
noncomputable def programs (a : WilliamsAlgorithm) (E C : ℕ) : (j : Fin 2) → Machine (MatrixPacketHeader.tapes a E) (sizes a E C j)
  | ⟨0,_⟩ => MatrixPacketHeader.machine a E
  | ⟨1,_⟩ => MatrixPacketBranch.machine a E C
  | ⟨n+2,h⟩ => False.elim (by omega)
noncomputable def next (a : WilliamsAlgorithm) (E C : ℕ) (j : Fin 2) (_ : Fin (sizes a E C j))
    (bits : Fin (MatrixPacketHeader.tapes a E) → Bool) : Option (Fin 2) :=
  if j=0 then if bits (MatrixPacketHeader.extra a E 0) then some 1 else none else none
noncomputable def machine (a : WilliamsAlgorithm) (E C : ℕ) :=
  RecoveryCalls.machine (sizes a E C) (programs a E C) 0 (next a E C)
noncomputable def outputTape (a : WilliamsAlgorithm) (E : ℕ) :=
  MatrixPacketHeader.old a E (MatrixPacketRestoreDock.slots a E (MatrixPacketState.output a))
noncomputable def original (a : WilliamsAlgorithm) (E : ℕ) :=
  MatrixPacketHeader.old a E (MatrixPacketRestoreControls.controls a E 2)
noncomputable def budget (a : WilliamsAlgorithm) (E C : ℕ) (r : Request) :=
  MatrixPacketHeader.budget r+1+if r.p=0 then 0 else MatrixPacketBranch.budget a E C r+1

theorem original_input (a : WilliamsAlgorithm) (E : ℕ) (r : Request) :
    MatrixPacketColdPrepare.cold a E r (MatrixPacketRestoreControls.controls a E 2)=physicalInput r := by
  simp [MatrixPacketColdPrepare.cold,MatrixPacketRestoreControls.controls]
theorem output_input (a : WilliamsAlgorithm) (E : ℕ) (r : Request) :
    MatrixPacketColdPrepare.cold a E r (MatrixPacketRestoreDock.slots a E (MatrixPacketState.output a))=[] := by
  exact if_neg (MatrixPacketRestoreControls.controls_outside a E 2 (MatrixPacketState.output a))

theorem controller_run (a : WilliamsAlgorithm) (E C : ℕ) (r : Request)
    (hcap : ∀ j<r.p,∀ negative,MatrixVariablePacketWorkspace.footprint a r j negative≤MatrixPacketBootstrapState.capacity E C r) :
    ∃ actual,run (machine a E C) (budget a E C r) (MatrixPacketHeader.input a E r)=some actual ∧
      actual.final.tapes (outputTape a E)=MatrixScoreBatch.output r ∧
      actual.final.tapes (original a E)=physicalInput r ∧ actual.final.heads (original a E)=0 ∧
      actual.steps≤budget a E C r := by
  obtain ⟨base,hb,old,pT,pH,bs⟩:=MatrixPacketHeader.header_run a E r
  have flag : base.final.scanned (MatrixPacketHeader.extra a E 0)=decide (0<r.p) := by
    simp only [Configuration.scanned,pT,pH]
    cases hp : r.p with
    | zero => rfl
    | succ n => exact UnaryTemplate.tape_mark (n+1) 0 (by omega)
  by_cases hz : r.p=0
  · obtain ⟨n,hn,path⟩:=stop_receipt (sizes a E C) (programs a E C) 0 (next a E C) 0
      (MatrixPacketHeader.budget r) (initialConfiguration (programs a E C 0) (MatrixPacketHeader.input a E r)) base hb
      (by simp [next]; exact flag.trans (by simp [hz]))
    obtain ⟨actual,ha,hf,hs⟩:=path.run (by simp [RecoveryCalls.machine,RecoveryCalls.stopped])
    have hbound : n≤budget a E C r := by unfold budget; rw [if_pos hz]; omega
    have ha' : run (machine a E C) n (MatrixPacketHeader.input a E r)=some actual := ha
    have hm:=run_moreFuel (machine a E C) n (budget a E C r-n) _ actual ha'
    rw [Nat.add_sub_of_le hbound] at hm
    refine ⟨actual,hm,?_,?_,?_,hs.le.trans hbound⟩
    · rw [hf]
      exact ((old _).1.trans (output_input a E r)).trans (by simp [MatrixScoreBatch.output,hz])
    · rw [hf]
      exact (old _).1.trans (original_input a E r)
    · rw [hf]
      exact (old _).2
  · have hp : 0<r.p := by omega
    obtain ⟨last,hl,lo,lt,lh,ls⟩:=MatrixPacketBranch.branch_run a E C r hp hcap base.final.heads base.final.tapes
      (fun i => (old i).1) (fun i => (old i).2) pT pH
    obtain ⟨n,hn,path0⟩:=call_receipt (sizes a E C) (programs a E C) 0 (next a E C) 0 1
      (MatrixPacketHeader.budget r) (initialConfiguration (programs a E C 0) (MatrixPacketHeader.input a E r)) base hb
      (by simp [next]; exact flag.trans (by simp [hp]))
    obtain ⟨m,hm,path1⟩:=stop_receipt (sizes a E C) (programs a E C) 0 (next a E C) 1
      (MatrixPacketBranch.budget a E C r)
      (RecoveryCalls.restarted (programs a E C 1) base.final.heads base.final.tapes) last hl (by simp [next])
    obtain ⟨actual,ha,hf,hs⟩:=(path0.trans path1).run (by simp [RecoveryCalls.machine,RecoveryCalls.stopped])
    have hbound : n+m≤budget a E C r := by unfold budget; rw [if_neg hz]; omega
    have ha' : run (machine a E C) (n+m) (MatrixPacketHeader.input a E r)=some actual := ha
    have he:=run_moreFuel (machine a E C) (n+m) (budget a E C r-(n+m)) _ actual ha'
    rw [Nat.add_sub_of_le hbound] at he
    exact ⟨actual,he,by rw [hf]; exact lo,by rw [hf]; exact lt,by rw [hf]; exact lh,hs.le.trans hbound⟩

end NearCubicWires.RepairOrdinary.MatrixPacketController
