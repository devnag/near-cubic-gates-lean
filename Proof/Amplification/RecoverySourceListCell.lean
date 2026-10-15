import Proof.Amplification.RecoverySourceLiteralMeaning

/-! Original Encodable list cell from arbitrary binary field words. The
existing pair and increment run physically; their exact untrimmed framed
result can feed the next cell without zero tests or canonicalization. -/
namespace NearCubicWires.RepairSource.RecoverySourceListCell
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound RadixSemantics SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def pairSlots (i : Fin 35) : Fin 36 := i.castAdd 1
def incrementSlots : Fin 2→Fin 36 := ![26,35]
theorem pair_injective : Function.Injective pairSlots := by
  intro a b h; exact Fin.ext (congrArg (fun i : Fin 36=>i.val) h)
theorem increment_injective : Function.Injective incrementSlots := by decide
noncomputable def pairMachine := RecoveryFocus.machine pairSlots PCPPairCold.machine
noncomputable def incrementMachine := RecoveryFocus.machine incrementSlots ClockIncrement.machine
noncomputable def machine := Composition.machine pairMachine incrementMachine
def input (left right : List Bool) (i : Fin 36) :=
  if i.val=2 then RepairOrdinary.frame left else if i.val=3 then RepairOrdinary.frame right else []
def pairedWord (left right : List Bool) := binary (PCPPair.width left right) (Nat.pair (value left) (value right))
def word (left right : List Bool) := ClockIncrement.next (pairedWord left right)
def budget (left right : List Bool) := PCPPairCold.budget left right+1+(2*ClockIncrement.work (pairedWord left right)+2)

theorem cell_run (left right : List Bool) : ∃ out,
    ClockJoin.ReadyRun machine (budget left right) (input left right) out ∧
      out 26=RepairOrdinary.frame (word left right) := by
  obtain ⟨paired,hPair,hField⟩ := PCPPairCold.pair_run left right
  have first := hPair.focus pairSlots pair_injective (input left right) (by intro i; fin_cases i <;> rfl)
  obtain ⟨r,hr,hBits,hLog,hh,hs,_space⟩ := ClockIncrement.increment_run (pairedWord left right) 0
  have hi : ClockJoin.ReadyRun ClockIncrement.machine (2*ClockIncrement.work (pairedWord left right)+2)
      ![RepairOrdinary.frame (pairedWord left right),[]]
      ![RepairOrdinary.frame (word left right),List.replicate (ClockIncrement.work (pairedWord left right)) false] := by
    refine ⟨r,?_,?_,hh,hs.le⟩
    · convert hr using 2
      all_goals first | rfl | (funext i; fin_cases i <;> rfl)
    · funext i; fin_cases i
      · exact hBits
      · change r.final.tapes 1=List.replicate (ClockIncrement.work (pairedWord left right)) false
        simpa only [Nat.zero_max] using hLog
  have second := hi.focus incrementSlots increment_injective (install pairSlots (input left right) paired) (by
    intro i; fin_cases i
    · change install pairSlots _ _ (pairSlots 26)=_
      rw [install_slot _ pair_injective]
      exact hField
    · rw [install_other _ _ _ _ (by intro j; fin_cases j <;> decide)]
      rfl)
  have hall := ClockJoin.join _ _ _ _ _ _ _ first second
  refine ⟨_,hall,?_⟩
  change install incrementSlots _ _ (incrementSlots 0)=_
  rw [install_slot _ increment_injective]
  rfl

theorem word_value (left right : List Bool) :
    value (word left right)=Nat.pair (value left) (value right)+1 := by
  rw [word,ClockIncrement.next_value,pairedWord,binary_value _ _ (PCPPair.pair_bound left right)]

end NearCubicWires.RepairSource.RecoverySourceListCell
