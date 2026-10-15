import Proof.Amplification.RecoveryOuterRow

/-! Physical four-field outer-row reading preserves the independent inner
bank. Truncation is exposed to the enclosing rejecting gate. -/
namespace NearCubicWires.RepairOrdinary.RecoveryOuterLeaf
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRowStream RecoveryRowStructure
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RepairSource.RecoveryOracle.BalancedCertificate
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def readMachine := onOuter rowReadMachine
def readState (x : State) (input : List Bool) := withOuter x (readChildren x.outer input)

theorem read_valid (x : State) (word outerBits innerBits input : List Bool)
    (hx : x.Valid word outerBits innerBits) (hi : 4*x.outer.base.state.bits.length ≤ input.length) :
    (readState x input).Valid word outerBits innerBits :=
  withOuter_valid x _ word outerBits innerBits hx (read_children_valid x.outer word outerBits input hx.1 hi)
    (afterRead_width x.outer.base input hi) rfl

theorem read_run (x : State) (word pre input : List Bool) (hx : x.outer.base.Valid word)
    (hs : x.outer.base.source=pre++frame input) (hp : x.outer.base.pos=pre.length) :
    ∃ r,runFrom readMachine (RecoveryRowFields.budget x.outer.base.state.bits.length)
        (x.cfg readMachine.start)=some r ∧
      r.steps ≤ RecoveryRowFields.budget x.outer.base.state.bits.length ∧ r.final.heads 50=0 ∧
      r.final.tapes 50=[(readRow x.outer.base.state.bits.length input).isSome] ∧
      ((readRow x.outer.base.state.bits.length input).isSome=true →
        r.final=(readState x input).cfg r.final.control) := by
  obtain ⟨base,hr,hb,hh,ht,hout⟩ := read_ambient_run x.outer word pre input hx hs hp
  let r := TapeEmbedding.receipt (fun _ : Fin 16=>0) x.extra base
  have h := TapeEmbedding.run_embed rowReadMachine (fun _ : Fin 16=>0) x.extra
    (RecoveryRowFields.budget x.outer.base.state.bits.length) _ base hr
  refine ⟨r,h,hb,hh,ht,?_⟩
  intro ha
  change TapeEmbedding.config (fun _ : Fin 16=>0) x.extra base.final=_
  rw [hout ha]
  rfl

end NearCubicWires.RepairOrdinary.RecoveryOuterLeaf
