import Proof.MachineModel.OrdinarySourceSATLiftKernel

/-! The fixed finite source-query replacement graph. Source local rules
remain the original rules. Query states call the marker kernel and an actual
corrected-oracle ask before resuming the selected original control state. -/
namespace NearCubicWires.RepairSource.OrdinarySourceSATLift
open LocalBitMultitape RepairOrdinary RecoveryExecution OrdinaryOracleCompose
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure Wiring (p : OrdinaryOracleProgram) (t : ℕ) where
  core : Fin p.base.tapeCount → Fin t
  kernel : Fin 156 → Fin t
  core_injective : Function.Injective core
  kernel_injective : Function.Injective kernel
  shared : kernel 0=core p.queryTape
  disjoint : ∀ i j,j≠0 → core i≠kernel j

namespace QueryGraph
abbrev Phase (p : OrdinaryOracleProgram) :=
  Sum (Fin p.base.stateCount) (Sum (Fin p.base.stateCount) (Fin p.base.stateCount))
noncomputable def phaseCode (p : OrdinaryOracleProgram) :
    Phase p ≃ Fin (Fintype.card (Phase p)) := Fintype.equivFin _
noncomputable def sourceNode (p : OrdinaryOracleProgram) (q : Fin p.base.stateCount) :=
  phaseCode p (.inl q)
noncomputable def kernelNode (p : OrdinaryOracleProgram) (q : Fin p.base.stateCount) :=
  phaseCode p (.inr (.inl q))
noncomputable def askNode (p : OrdinaryOracleProgram) (q : Fin p.base.stateCount) :=
  phaseCode p (.inr (.inr q))

noncomputable def paused (p : OrdinaryOracleProgram) (entry : Fin p.base.stateCount) :
    Machine p.base.tapeCount p.base.stateCount where
  descriptionBits := 0
  start := entry
  halted := fun q => p.base.machine.halted q || (p.query q).isSome
  rule := p.base.machine.rule

def askMachine (t : ℕ) : Machine t 3 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val≠0
  rule := fun _ _ => none

noncomputable def askPiece (p : OrdinaryOracleProgram) (t : ℕ)
    (q : Fin p.base.stateCount) : Piece t :=
  ⟨3,askMachine t,fun state =>
    if state.val=0 then (p.query q).map (fun _ => ⟨1,2⟩) else none⟩

noncomputable def pieces {p : OrdinaryOracleProgram} {t : ℕ} (w : Wiring p t)
    (node : Fin (Fintype.card (Phase p))) : Piece t :=
  match (phaseCode p).symm node with
  | .inl q => ordinary (RecoveryFocus.machine w.core (paused p q))
  | .inr (.inl _) => ordinary (RecoveryFocus.machine w.kernel Kernel.machine)
  | .inr (.inr q) => askPiece p t q

noncomputable def next {p : OrdinaryOracleProgram} {t : ℕ} (w : Wiring p t)
    (node : Fin (Fintype.card (Phase p))) (state : Fin (pieces w node).states)
    (_ : Fin t → Bool) : Option (Fin (Fintype.card (Phase p))) :=
  match (phaseCode p).symm node with
  | .inl _ =>
      if h : state.val < p.base.stateCount then
        let q : Fin p.base.stateCount := ⟨state.val,h⟩
        if p.base.machine.halted q then none else some (kernelNode p q)
      else none
  | .inr (.inl q) => some (askNode p q)
  | .inr (.inr q) =>
      (p.query q).map (fun r => sourceNode p (if state.val=2 then r.onTrue else r.onFalse))

noncomputable abbrev piece {p : OrdinaryOracleProgram} {t : ℕ} (w : Wiring p t) : Piece t :=
  graph (pieces w) (sourceNode p p.base.machine.start) (next w)

@[simp] theorem pieces_source {p : OrdinaryOracleProgram} {t : ℕ} (w : Wiring p t)
    (q : Fin p.base.stateCount) :
    pieces w (sourceNode p q)=ordinary (RecoveryFocus.machine w.core (paused p q)) := by
  simp [pieces,sourceNode]
@[simp] theorem pieces_kernel {p : OrdinaryOracleProgram} {t : ℕ} (w : Wiring p t)
    (q : Fin p.base.stateCount) :
    pieces w (kernelNode p q)=ordinary (RecoveryFocus.machine w.kernel Kernel.machine) := by
  simp [pieces,kernelNode]
@[simp] theorem pieces_ask {p : OrdinaryOracleProgram} {t : ℕ} (w : Wiring p t)
    (q : Fin p.base.stateCount) : pieces w (askNode p q)=askPiece p t q := by
  simp [pieces,askNode]

end QueryGraph
end NearCubicWires.RepairSource.OrdinarySourceSATLift
