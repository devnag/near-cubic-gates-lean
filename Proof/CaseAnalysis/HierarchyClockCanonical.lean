import Proof.Circuits.CanonicalBinaryOutput
import Proof.MachineModel.OrdinaryOracleCompose

/-! Canonical framed hierarchy clock from its existing positive fixed-width
field. Reuse the paid trim and framed-copy programs directly, avoiding a raw
payload extraction followed by a separate length count and serialization. -/
namespace NearCubicWires.RepairSource.CloseoutHierarchyClock
open LocalBitMultitape RepairOrdinary RecoveryRootRound SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def copy:=RecoveryFocus.machine CanonicalPositiveOutput.copySlots PCPFieldMoves.readyMachine
def machine:=Composition.machine CanonicalPositiveOutput.trimPhase copy

theorem canonical_run (w n : Nat) (hn : 0<n) (hfit : n<2^w) :
    ∃ out,ClockJoin.ReadyRun machine (8*w+11)
      (CanonicalPositiveOutput.input (binary w n)) out ∧ out 2=frame n.bits:=by
  obtain ⟨pre,hpre⟩:=CanonicalPositiveOutput.nat_bits_suffix n hn
  let z:=w-n.bits.length
  have hlen:pre.length+1=n.bits.length:=by rw [hpre]; simp
  have hw:=CanonicalPositiveOutput.nat_bits_length_le w n hfit
  have he:binary w n=pre++[true]++List.replicate z false:=by
    rw [CanonicalPositiveOutput.binary_padding w n hfit]
    exact congrArg (fun bits=>bits++List.replicate z false) hpre
  let mid:=CanonicalPositiveOutput.middle pre z
  have ha:=CanonicalPositiveOutput.trim_phase pre z
  obtain ⟨r,hr,rt,rh,rs⟩:=OrdinaryOracleCompose.copy_ready CanonicalPositiveOutput.copySlots
    CanonicalPositiveOutput.copy_injective mid (pre++[true]) (List.replicate (2*z) false)
    (CanonicalPositiveOutput.back_tape pre z) rfl rfl
  have hb : ClockJoin.ReadyRun copy (4*(pre++[true]).length+4) mid
      (Function.update (Function.update mid 2 (frame (pre++[true]))) 3
        (List.replicate (2*(pre++[true]).length+1) false)):=⟨r,hr,rt,rh,rs.le⟩
  have whole:=ClockJoin.join _ _ _ _ _ _ _ ha hb
  have hc:2*CanonicalPositiveOutput.trimCost pre z+2+1+(4*(pre++[true]).length+4)=8*w+11:=by
    simp only [CanonicalPositiveOutput.trimCost,List.length_append,List.length_singleton]
    dsimp [z]
    omega
  rw [hc,←he] at whole
  refine ⟨_,whole,?_⟩
  simp [Function.update,hpre]

end
end NearCubicWires.RepairSource.CloseoutHierarchyClock
