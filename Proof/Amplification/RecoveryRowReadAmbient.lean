import Proof.Amplification.RecoveryRowChecked

/-! The actual four-field reader in the shared row/table workspace. The
parse-result cell survives embedding, including every truncated input. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRowStructure
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRowStream
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def rowReadMachine := onBase (TapeEmbedding.machine 1 RecoveryRowStream.readMachine)
def readChildren (x : Children) (input : List Bool) : Children := {x with base:=x.base.afterRead input}

theorem read_children_valid (x : Children) (word bits input : List Bool) (hx : x.Valid word bits)
    (hi : 4*x.base.state.bits.length ≤ input.length) : (readChildren x input).Valid word bits := by
  have hw := afterRead_width x.base input hi
  refine ⟨afterRead_valid x.base word input hx.1 hi,?_,hx.2.2.1,hx.2.2.2.1,?_,hx.2.2.2.2.2⟩
  · change RecoveryRowLookupTable.Inv (x.base.afterRead input).state.bits.length ⟨x.bank,bits⟩
    rw [hw]
    exact hx.2.1
  · change 2*(x.base.afterRead input).state.bits.length+1 ≤ x.copyCapacity
    rw [hw]
    exact hx.2.2.2.2.1

theorem read_children_widths (x : Children) (input : List Bool)
    (hi : 4*x.base.state.bits.length ≤ input.length) :
    (readChildren x input).base.code.length=(readChildren x input).base.state.bits.length ∧
    (readChildren x input).base.kind.length=(readChildren x input).base.state.bits.length ∧
    (readChildren x input).base.count.length=(readChildren x input).base.state.bits.length := by
  have hw := afterRead_width x.base input hi
  dsimp only [readChildren]
  rw [hw]
  exact ⟨words_length _ _ 1 hi,words_length _ _ 0 hi,words_length _ _ 2 hi⟩

theorem read_ambient_run (x : Children) (word pre input : List Bool) (hx : x.base.Valid word)
    (hs : x.base.source=pre++frame input) (hp : x.base.pos=pre.length) :
    ∃ r,runFrom rowReadMachine (RecoveryRowFields.budget x.base.state.bits.length)
        (x.cfg rowReadMachine.start)=some r ∧
      r.steps ≤ RecoveryRowFields.budget x.base.state.bits.length ∧ r.final.heads 50=0 ∧
      r.final.tapes 50=[(readRow x.base.state.bits.length input).isSome] ∧
      ((readRow x.base.state.bits.length input).isSome=true →
        r.final=(readChildren x input).cfg r.final.control) := by
  obtain ⟨base,hr,hb,hh,ht,hf⟩ := RecoveryRowStream.read_run x.base word pre input hx hs hp
  let copy := fun _ : Fin 1=>List.replicate x.copyCapacity false
  let middle := TapeEmbedding.receipt (fun _ : Fin 1=>0) copy base
  have hm := TapeEmbedding.run_embed RecoveryRowStream.readMachine (fun _ : Fin 1=>0) copy _ _ base hr
  let bank := RecoveryRowLookupTable.readyTapes x.bank x.total x.lookupCapacity
  let result := TapeEmbedding.receipt (fun _ : Fin 16=>0) bank middle
  have h := TapeEmbedding.run_embed (TapeEmbedding.machine 1 RecoveryRowStream.readMachine)
    (fun _ : Fin 16=>0) bank _ _ middle hm
  refine ⟨result,h,hb,hh,ht,?_⟩
  intro ha
  have he : result.final=(readChildren x input).cfg (RecoveryCalls.controlCode RecoveryRowFields.sizes none) := by
    change TapeEmbedding.config (fun _ : Fin 16=>0) bank
      (TapeEmbedding.config (fun _ : Fin 1=>0) copy base.final)=_
    rw [hf ha]
    rfl
  rw [he]
  rfl

end NearCubicWires.RepairOrdinary.RecoveryRowStructure
