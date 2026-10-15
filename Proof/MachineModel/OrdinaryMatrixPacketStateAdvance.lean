import Proof.MachineModel.OrdinaryMatrixPacketState

/-! The bit advance acts only on the physical offset sentinel. The next
packet receives the same capacity, source, local work and append cursor. -/
namespace NearCubicWires.RepairOrdinary.MatrixPacketStateAdvance
open LocalBitMultitape RecoveryRootRound MatrixScoreBatch RepairRepresentation
open MatrixPacketState (State)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def slot (a : WilliamsAlgorithm) (E : ℕ) : Fin 1 → Fin (MatrixPacketRestore.tapes a E) :=
  fun _ => MatrixPacketRestoreDock.slots a E (MatrixPacketState.offset a)
theorem slot_injective (a : WilliamsAlgorithm) (E : ℕ) : Function.Injective (slot a E) :=
  fun _ _ _ => Subsingleton.elim _ _
noncomputable def machine (a : WilliamsAlgorithm) (E : ℕ) :=
  RecoveryFocus.machine (slot a E) MatrixPacketOffset.machine
noncomputable def input (a : WilliamsAlgorithm) (E cap : ℕ) (r : Request) (bit : ℕ) (out : List Bool)
    (st : State a E cap r bit out) := RecoveryCalls.restarted (machine a E) st.heads st.tapes

theorem state_run (a : WilliamsAlgorithm) (E cap : ℕ) (r : Request) (bit : ℕ) (out : List Bool)
    (st : State a E cap r bit out) :
    ∃ next : State a E cap r (bit+1) out,∃ actual,
      runFrom (machine a E) (MatrixPacketOffset.budget bit) (input a E cap r bit out st)=some actual ∧
      actual.final.heads=next.heads ∧ actual.final.tapes=next.tapes ∧
      actual.steps≤MatrixPacketOffset.budget bit := by
  obtain ⟨body,hb,bt,bh,bs⟩ := MatrixPacketOffset.advance_run bit
  let entry := input a E cap r bit out st
  have hi : RecoveryFocus.config (slot a E) st.heads st.tapes (MatrixPacketOffset.input bit)=entry := by
    apply WilliamsSourceCrop.focus_same (slot a E) entry (MatrixPacketOffset.input bit)
    · intro j
      fin_cases j
      exact st.offsetH
    · intro j
      fin_cases j
      exact st.offsetT
  obtain ⟨actual,ha,hf,hs⟩ := RecoveryFocus.run_config (slot a E) (slot_injective a E)
    MatrixPacketOffset.machine st.heads st.tapes _ _ body hb
  rw [hi] at ha
  have localT : actual.final.tapes (slot a E 0)=UnaryTemplate.tape (2*(bit+1)) := by
    rw [hf]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot (slot a E) (slot_injective a E),bt]
  have localH : actual.final.heads (slot a E 0)=1 := by
    rw [hf]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot (slot a E) (slot_injective a E),bh]
  have other (i : Fin (MatrixPacketRestore.tapes a E)) (no : ∀ j,slot a E j≠i) :
      actual.final.tapes i=st.tapes i ∧ actual.final.heads i=st.heads i := by
    have pk : RecoveryFocus.pick (slot a E) i=none := by
      simp only [RecoveryFocus.pick,dif_neg (not_exists.mpr no)]
    rw [hf]
    simp only [RecoveryFocus.config,pk]
    trivial
  have workNo (i : Fin (MatrixVariablePacketWorkspace.tapes a)) (hw : MatrixVariablePacketWorkspace.working a i) :
      ∀ j,slot a E j≠MatrixPacketRestoreDock.slots a E i := by
    intro j he
    have h:=MatrixPacketRestoreDock.slots_injective a E he
    exact hw.1 (congrArg (fun k : Fin (MatrixVariablePacketWorkspace.tapes a) => k.val) h.symm)
  have outNo : ∀ j,slot a E j≠MatrixPacketRestoreDock.slots a E (MatrixPacketState.output a) := by
    intro j he
    have h:=MatrixPacketRestoreDock.slots_injective a E he
    have hv:=congrArg (fun k : Fin (MatrixVariablePacketWorkspace.tapes a) => k.val) h
    change (424 : ℕ)=MatrixVariableProduct.tapes a+16 at hv
    have hK : 425≤MatrixVariableProduct.tapes a := by unfold MatrixVariableProduct.tapes; omega
    omega
  let next : State a E cap r (bit+1) out :=
    ⟨actual.final.heads,actual.final.tapes,
      (fun i hw => (congrArg List.length (other _ (workNo i hw)).1).le.trans (st.bounded i hw)),
      (fun i hw => (other _ (workNo i hw)).2.trans (st.workHeads i hw)),
      localT,localH,(other _ outNo).1.trans st.outputT,(other _ outNo).2.trans st.outputH,
      (fun j => (other _ (fun _ => MatrixPacketRestoreControls.controls_outside a E j (MatrixPacketState.offset a))).1.trans (st.controlT j)),
      (fun j => (other _ (fun _ => MatrixPacketRestoreControls.controls_outside a E j (MatrixPacketState.offset a))).2.trans (st.controlH j))⟩
  exact ⟨next,actual,ha,rfl,rfl,hs.trans_le bs⟩

end NearCubicWires.RepairOrdinary.MatrixPacketStateAdvance
