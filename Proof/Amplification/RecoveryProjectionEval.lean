import Proof.Amplification.RecoveryProjectionLookup

/-! One whole normalized projection evaluation: actual unpair, actual
random-bit lookup, then the original positive/negative/constant meaning.
This is the local call used by the actual source-field emitter. -/
namespace NearCubicWires.RepairSource.RecoveryProjectionEval
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound RadixSemantics SourceInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine := Composition.machine (Composition.machine unpairMachine lookupMachine) selectMachine
def time (bits randomness : List Bool) := RecoveryFixedUnpair.time bits+1+
  (2*RecoveryCommittedBit.rawCost (RecoveryFixedUnpair.rightWord bits) randomness+2)+1+10
def budget (bits randomness : List Bool) := 8192*(bits.length+randomness.length+1)^2
def outputBit (bits randomness : List Bool) :=
  RecoveryProjectionSelect.result (RecoveryFixedUnpair.leftWord bits) bits (pickedBit bits randomness)

theorem whole_ready (bits randomness : List Bool) (flag picked old : Bool) (cap : Nat)
    (hw : 2*bits.length+1 ≤ cap)
    (hc : RecoveryCommittedBit.rawCost (RecoveryFixedUnpair.rightWord bits) randomness ≤ cap) : ∃ out,
    ClockJoin.ReadyRun machine (time bits randomness) (input bits randomness flag picked old cap) out ∧
      out 26=[outputBit bits randomness] := by
  have hfirst := unpair_ready bits randomness flag picked old cap
  obtain ⟨middle,hsecond,hselected⟩ := lookup_ready bits randomness flag picked old cap hw hc
  have hthird := (RecoveryProjectionSelect.ready (RecoveryFixedUnpair.leftWord bits) bits
    (pickedBit bits randomness) old).focus selectSlots select_injective middle hselected
  have hwhole := ClockJoin.join _ _ _ _ _ _ _ (ClockJoin.join _ _ _ _ _ _ _ hfirst hsecond) hthird
  refine ⟨_,hwhole,?_⟩
  change install selectSlots _ _ (selectSlots 3)=_
  rw [install_slot _ select_injective]
  rfl

theorem time_bound (bits randomness : List Bool) : time bits randomness ≤ budget bits randomness := by
  have ht := RecoveryFixedUnpair.time_bound bits
  dsimp only [RecoveryFixedUnpair.budget] at ht
  simp only [time,RecoveryCommittedBit.rawCost,(RecoveryFixedUnpair.word_lengths bits).2,budget]
  nlinarith

theorem capacity_covers (bits randomness : List Bool) (cap : Nat) (hc : budget bits randomness ≤ cap) :
    2*bits.length+1 ≤ cap ∧ RecoveryCommittedBit.rawCost (RecoveryFixedUnpair.rightWord bits) randomness ≤ cap := by
  have hsize : bits.length+randomness.length+1 ≤ (bits.length+randomness.length+1)^2 :=
    Nat.le_self_pow (by decide) _
  simp only [budget] at hc
  simp only [RecoveryCommittedBit.rawCost,(RecoveryFixedUnpair.word_lengths bits).2]
  constructor <;> nlinarith

theorem bounded_ready (bits randomness : List Bool) (flag picked old : Bool) (cap : Nat)
    (hc : budget bits randomness ≤ cap) : ∃ out,
    ClockJoin.ReadyRun machine (budget bits randomness) (input bits randomness flag picked old cap) out ∧
      out 26=[outputBit bits randomness] := by
  obtain ⟨hw,hlookup⟩ := capacity_covers bits randomness cap hc
  obtain ⟨out,hr,hout⟩ := whole_ready bits randomness flag picked old cap hw hlookup
  exact ⟨out,ClockJoin.enlarge _ _ _ _ _ hr (time_bound bits randomness),hout⟩

theorem projection_bit {n : Nat} (p : ProjectedRandomBit n) (randomness : BitInput n) :
    outputBit (projectionCode p).bits (List.ofFn randomness)=p.eval randomness := by
  unfold outputBit pickedBit
  rw [CanonicalPositiveOutput.nat_bits_value]
  exact RecoveryProjectionSelect.projection_meaning p randomness

theorem projection_ready {n : Nat} (p : ProjectedRandomBit n) (randomness : BitInput n)
    (flag picked old : Bool) (cap : Nat)
    (hc : budget (projectionCode p).bits (List.ofFn randomness) ≤ cap) : ∃ out,
    ClockJoin.ReadyRun machine (budget (projectionCode p).bits (List.ofFn randomness))
      (input (projectionCode p).bits (List.ofFn randomness) flag picked old cap) out ∧
      out 26=[p.eval randomness] := by
  obtain ⟨out,hr,hout⟩ := bounded_ready (projectionCode p).bits (List.ofFn randomness) flag picked old cap hc
  rw [projection_bit] at hout
  exact ⟨out,hr,hout⟩

end NearCubicWires.RepairSource.RecoveryProjectionEval
