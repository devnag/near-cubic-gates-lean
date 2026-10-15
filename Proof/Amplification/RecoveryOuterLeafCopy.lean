import Proof.Amplification.RecoveryOuterLeafLookup

/-! Copy the original outer-row payload into the independent inner lookup
key. Every copy and rewind is executed, leaving both source tables intact. -/
namespace NearCubicWires.RepairOrdinary.RecoveryOuterLeaf
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRowStream RecoveryRowStructure
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RepairSource.RecoveryOracle.BalancedCertificate
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def copySlots : Fin 4→Fin 84 := ![0,75,51,22]
theorem copySlots_injective : Function.Injective copySlots := by decide
noncomputable def copyMachine := RecoveryFocus.machine copySlots RecoveryRootRound.copyMachine
noncomputable def machine := Composition.machine copyMachine lookupMachine
def cost (x : State) := 8*x.outer.base.state.bits.length+9+time x
def result (x : State) (bits : List Bool) := output (keyed x) bits

open private install_eq from Proof.Amplification.RecoveryRowLookupCell

theorem copy_run (x : State) (word outerBits innerBits : List Bool) (hx : x.Valid word outerBits innerBits) :
    ∃ r,runFrom copyMachine (8*x.outer.base.state.bits.length+8) (x.cfg copyMachine.start)=some r ∧
      r.final=(keyed x).cfg r.final.control ∧ r.steps=8*x.outer.base.state.bits.length+8 ∧
      (keyed x).Valid word outerBits innerBits := by
  have hw : x.inner.key.length=x.outer.base.state.bits.length := hx.2.2.1.1.2.1.trans hx.2.2.1.2.1
  have hc : 2*x.outer.base.state.bits.length+1 ≤ x.outer.copyCapacity := hx.1.2.2.2.2.1
  have hr : 4*x.outer.base.state.bits.length+3 ≤ x.outer.base.state.capacity := by
    have h := hx.1.1.2.1.reset
    change 8192*(x.outer.base.state.bits.length+1)^2+1 ≤ x.outer.base.state.capacity at h
    nlinarith
  have h := RecoveryRootRound.copy_ready x.outer.base.state.bits (frame x.inner.key)
    x.outer.copyCapacity x.outer.base.state.capacity (by rw [frame_length,hw])
  rw [Nat.max_eq_left hc,Nat.max_eq_left hr] at h
  obtain ⟨r,hrun,hheads,htapes,hsteps⟩ := h.focus_at copySlots copySlots_injective x.heads x.tapes
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  have he : install copySlots x.tapes ![frame x.outer.base.state.bits,frame x.outer.base.state.bits,
      List.replicate x.outer.copyCapacity false,List.replicate x.outer.base.state.capacity false]=
      Function.update x.tapes 75 (frame x.outer.base.state.bits) := by
    apply install_eq copySlots copySlots_injective
    · intro j
      fin_cases j
      · rfl
      · simp [copySlots]
      · rfl
      · rfl
    · intro i hi
      have hn : i≠75 := by intro he; exact hi 1 he.symm
      simp only [Function.update_of_ne hn]
  refine ⟨r,hrun,?_,hsteps,keyed_valid x word outerBits innerBits hx⟩
  apply configuration_ext
  · rfl
  · exact hheads
  · exact htapes.trans (he.trans (keyed_tapes x).symm)

theorem member_run (x : State) (word outerBits innerBits : List Bool) (rows : List Row) (rest : List Bool)
    (hx : x.Valid word outerBits innerBits)
    (hp : readMany (readRow x.inner.row.width) x.total innerBits=some (rows,rest)) :
    ∃ r,runFrom machine (cost x) (x.cfg machine.start)=some r ∧
      r.final=(result x innerBits).cfg r.final.control ∧ r.steps ≤ cost x ∧
      (result x innerBits).Valid word outerBits innerBits ∧
      (result x innerBits).inner.found=rows.any (fun row=>decide (RadixSemantics.value x.outer.base.state.bits=row.code)) := by
  obtain ⟨first,hr0,hf0,hs0,hv0⟩ := copy_run x word outerBits innerBits hx
  obtain ⟨last,hr1,hf1,hs1,hv1,ha⟩ := lookup_run (keyed x) word outerBits innerBits rows rest hv0 hp
  have hnext : Composition.restart first.final lookupMachine.start=(keyed x).cfg lookupMachine.start := by
    rw [hf0]; rfl
  rw [←hnext] at hr1
  have hall := Composition.run_join copyMachine lookupMachine (8*x.outer.base.state.bits.length+8) (time x) _ first last hr0 hr1
  refine ⟨Composition.joinedReceipt first last,hall,?_,?_,hv1,ha⟩
  · apply configuration_ext
    · rfl
    · change last.final.heads=(result x innerBits).heads
      rw [hf1]; rfl
    · change last.final.tapes=(result x innerBits).tapes
      rw [hf1]; rfl
  · change first.steps+1+last.steps ≤ cost x
    rw [hs0]
    unfold cost
    change last.steps ≤ time x at hs1
    omega

end NearCubicWires.RepairOrdinary.RecoveryOuterLeaf
