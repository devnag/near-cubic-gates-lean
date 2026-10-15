import Proof.PCP.VerifierDecodingStartFlagsRun

/-! The successful dimension producer supplies every literal start/flags
input: source suffix, actual binary state bound, width and capped state driver. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.Front
open LocalBitMultitape RepairOrdinary RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def bound (s : ℕ) := VerifierEncoding.fixedBits (natBitLength s) s
theorem bound_length (s : ℕ) : (bound s).length=natBitLength s := by simp [bound]

theorem dimension_entry (word fields : List Bool) (limit t s x y : ℕ)
    (hp : HeaderMachine.parts word=some (t,s,fields)) (hs : 0<s) :
    StartLayout.Entry (Dimensions.endpoint word limit t s x y)
      (StartLayout.headerPrefix t s) fields (bound s) := by
  obtain ⟨hsource,hlen⟩ := StartLayout.header_source hp
  have hb := PreparedWidth.output_binary (GuardedPreparation.endpoint word limit t s) s x y hs
  constructor
  · change 2*t+2*s+4=(StartLayout.headerPrefix t s).length
    exact hlen.symm
  · change frame word=StartLayout.headerPrefix t s++frame fields
    exact hsource
  · rfl
  · exact hb.1
  · rfl
  · rw [bound_length]
    exact hb.2

theorem dimension_count (word : List Bool) (limit t s x y : ℕ) :
    (Dimensions.endpoint word limit t s x y).heads 2=1 ∧
      (Dimensions.endpoint word limit t s x y).tapes 2=CapMachine.counter word.length s := by
  exact ⟨rfl,rfl⟩

theorem start_budget (word fields : List Bool) (t s : ℕ)
    (hp : HeaderMachine.parts word=some (t,s,fields)) (hs : 0<s) :
    8*(bound s).length+8*s+20≤16*word.length+20 := by
  have hj : natBitLength s ≤ s := by
    rw [←BitWidthMachine.width_eq s hs]
    exact ClockBinary.length_bound s s Nat.lt_two_pow_self
  have hlen := GuardedPreparation.parts_lengths hp
  rw [bound_length]
  omega

end NearCubicWires.RepairSource.VerifierDecoding.Front
