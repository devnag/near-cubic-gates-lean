import Proof.Amplification.RecoveryRowLeafGate

namespace NearCubicWires.RepairOrdinary.RecoveryRowStructure
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRowStream
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def leafWholeMachine := Composition.machine rowLeafMachine leafGate
def leafWholeTime (x : Children) := 8388608*(x.base.state.bits.length+1)^2+2
def leafAnswer (x : Children) (word : List Bool) :=
  RecoveryRowLeaf.leafWordCheck x.base.state x.base.extra x.base.kind word

theorem leaf_whole_run (x : Children) (word bits : List Bool) (hx : x.Valid word bits) :
    ∃ r,runFrom leafWholeMachine (leafWholeTime x) (x.cfg leafWholeMachine.start)=some r ∧
      r.steps≤leafWholeTime x ∧ r.final.heads=x.heads ∧ r.final.tapes 50=[leafAnswer x word] ∧
      (leafAnswer x word=true →
        ∃ out : RecoveryRowLeaf.LeafResult x.base.state x.base.extra x.base.kind word,
          r.final=(leafFinished x word out).cfg r.final.control ∧ (leafFinished x word out).Valid word bits) := by
  obtain ⟨small,hs,hsb,hsh,hst,hsout⟩ := RecoveryRowLeaf.leaf_run x.base.state x.base.extra x.base.kind word x.base.flags
    hx.1.1 hx.1.2.1 hx.1.2.2.1
  obtain ⟨first,hr0,hheads,htapes,hsteps⟩ := leaf_embed RecoveryRowLeaf.machine x
    (8388608*(x.base.state.bits.length+1)^2) small hs hsh
  have h50 : first.final.heads 50=0 := by rw [hheads]; rfl
  have h27 : first.final.heads 27=0 := by rw [hheads]; rfl
  have t50 : first.final.tapes 50=[x.base.valid] := by rw [htapes]; rfl
  have t27 : first.final.tapes 27=[leafAnswer x word] := by rw [htapes]; exact hst
  obtain ⟨last,hr1,hf1,hs1⟩ := leaf_gate_run first.final.heads first.final.tapes x.base.valid (leafAnswer x word) h50 h27 t50 t27
  have hrnext : runFrom leafGate 1 (Composition.restart first.final leafGate.start)=some last := hr1
  have hall := Composition.run_join rowLeafMachine leafGate (8388608*(x.base.state.bits.length+1)^2) 1
    _ first last hr0 hrnext
  refine ⟨Composition.joinedReceipt first last,hall,?_,?_,?_,?_⟩
  · change first.steps+1+last.steps≤leafWholeTime x
    rw [hsteps,hs1]
    unfold leafWholeTime
    omega
  · change last.final.heads=x.heads
    rw [hf1]
    exact hheads
  · change last.final.tapes 50=[leafAnswer x word]
    rw [hf1]
    simp
  · intro ha
    obtain ⟨out,hout⟩ := hsout ha
    have hreturned : first.final.tapes=(leafReturned x word out).tapes := by
      rw [htapes,hout]
      exact leafReturned_tapes x word out
    refine ⟨out,?_,leafReturned_valid x word bits hx out⟩
    change Composition.rightConfig _ last.final=(leafFinished x word out).cfg _
    apply configuration_ext
    · rfl
    · change last.final.heads=(leafFinished x word out).heads
      rw [hf1]
      exact hheads
    · change last.final.tapes=(leafFinished x word out).tapes
      rw [hf1]
      change Function.update first.final.tapes 50 [leafAnswer x word]=(leafFinished x word out).tapes
      rw [hreturned,ha]
      exact (leafFinished_tapes x word out).symm

end NearCubicWires.RepairOrdinary.RecoveryRowStructure
