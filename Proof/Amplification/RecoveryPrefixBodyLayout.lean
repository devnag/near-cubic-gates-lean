import Proof.Amplification.RecoveryPrefixUpdate
import Proof.MachineModel.OrdinaryWilliamsSourceCropLayout

/-! One fixed ordinary-oracle prefix iteration: the reusable query followed
by the three physically executed field updates. -/
namespace NearCubicWires.RepairSource.RecoveryPrefixBody
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound OrdinaryOracleCompose
open RecoveryPrefixUpdate
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def ports : Ports 360 := ⟨by decide,357,by decide,343,by decide⟩
noncomputable def pieces (flat : Bool) : Fin 2→Piece 360
  | ⟨0,_⟩ => focused (RecoveryQueryStep.program flat) querySlots
  | ⟨1,_⟩ => ordinary RecoveryPrefixUpdate.machine
  | ⟨n+2,h⟩ => False.elim (by omega)
def next (flat : Bool) (j : Fin 2) (_ : Fin (pieces flat j).states) (_ : Fin 360→Bool) : Option (Fin 2) :=
  if j.val=0 then some 1 else none
noncomputable abbrev piece (flat : Bool) := graph (pieces flat) 0 (next flat)
noncomputable abbrev program (flat : Bool) := ports.program (piece flat)
noncomputable def start (flat : Bool) (ambient : Fin 360→List Bool) :=
  controlConfig (RecoveryCalls.code (fun j => (pieces flat j).states) 0)
    (RecoveryFocus.config querySlots (fun _=>0) ambient (RecoveryQueryStep.start flat (ambient ∘ querySlots)))
noncomputable def stopped (flat : Bool) (out : Fin 360→List Bool) :=
  RecoveryCalls.stopped (fun j => (pieces flat j).states) (fun _=>0) out

noncomputable def queryOutput (ambient : Fin 360→List Bool) (out : Fin 357→List Bool) :=
  install querySlots ambient out

theorem query_output_slot (ambient : Fin 360→List Bool) (out : Fin 357→List Bool) (i : Fin 357) :
    queryOutput ambient out (querySlots i)=out i := install_slot querySlots query_injective ambient out i

theorem query_output_other (ambient : Fin 360→List Bool) (out : Fin 357→List Bool)
    (i : Fin 360) (hi : 357 ≤ i.val) : queryOutput ambient out i=ambient i := by
  apply install_other
  intro j he
  have hv := congrArg (fun k : Fin 360=>k.val) he
  change j.val=i.val at hv
  omega

theorem query_final (flat : Bool) (ambient : Fin 360→List Bool) (out : Fin 357→List Bool) :
    RecoveryFocus.config querySlots (fun _=>0) ambient (RecoveryQueryStep.stopped flat out)=
      (⟨(RecoveryQueryStep.stopped flat out).control,fun _=>0,queryOutput ambient out⟩ :
        Configuration 360 (RecoveryQueryStep.program flat).base.stateCount) := by
  apply configuration_ext
  · rfl
  · funext i
    simp only [RecoveryFocus.config,RecoveryQueryStep.stopped,RecoveryQueryCall.stopped,RecoveryCalls.stopped]
    split <;> rfl
  · rfl

end NearCubicWires.RepairSource.RecoveryPrefixBody
