import Proof.CaseAnalysis.FinalTailFeedUniform
import Proof.CaseAnalysis.FinalTailVerdict

namespace NearCubicWires.RepairSource.CloseoutFinal.C10TailSlotsUniform

open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule
open NearCubicWires.RepairSource.CloseoutFinal.C10TailSlots
open NearCubicWires.RepairSource.CloseoutFinal.C10TailUniformSlots
open NearCubicWires.RepairSource.CloseoutFinal.C10TailVerdict (tailBank scratchT)

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev feedSlots := C10TailVerdict.feedSlots

theorem feedSlots_inj (k : Fin 3) : Function.Injective (feedSlots k) :=
  C10TailVerdict.feedSlots_injective k

def prefixSlot (i : Fin bank) : Fin tailBank :=
  ⟨i.val, by have := i.isLt; unfold bank ext at this; unfold tailBank; omega⟩

def widthSlotT (ph : Phase) (j : Fin 2) : Fin tailBank := prefixSlot (widthSlot ph j)
def privateSlotT (ph : Phase) (j : Fin 29) : Fin tailBank := prefixSlot (privateSlot ph j)

theorem feedSlots_low (k : Fin 3) (i : Fin bank) (hi : i.val < 221) :
    feedSlots k i = prefixSlot i := by
  apply Fin.ext
  simp only [C10TailVerdict.feedSlots, C10TailVerdict.feedIdx, if_pos hi, prefixSlot]

theorem feedSlots_width (k : Fin 3) (ph : Phase) (j : Fin 2) :
    feedSlots k (widthSlot ph j) = widthSlotT ph j :=
  feedSlots_low k _ (by have := (widthSlot_range ph j).2; omega)

theorem feedSlots_private (k : Fin 3) (ph : Phase) (j : Fin 29) :
    feedSlots k (privateSlot ph j) = privateSlotT ph j :=
  feedSlots_low k _ (by have := (privateSlot_range ph j).2; omega)

theorem widthSlotT_range (ph : Phase) (j : Fin 2) :
    2 ≤ (widthSlotT ph j).val ∧ (widthSlotT ph j).val < 8 := widthSlot_range ph j

theorem privateSlotT_range (ph : Phase) (j : Fin 29) :
    15 ≤ (privateSlotT ph j).val ∧ (privateSlotT ph j).val < 102 := privateSlot_range ph j

theorem privateSlotT_disjoint {ph ph' : Phase} (hph : ph ≠ ph') (i j : Fin 29) :
    privateSlotT ph i ≠ privateSlotT ph' j := by
  intro h
  apply privateSlot_disjoint hph i j
  have hv := congrArg (fun x : Fin tailBank => x.val) h
  exact Fin.ext hv

def PublicPrefix (i : Fin tailBank) : Prop :=
  i.val < 221 ∧ ∀ ph j, privateSlotT ph j ≠ i

theorem width_public (ph : Phase) (j : Fin 2) : PublicPrefix (widthSlotT ph j) := by
  have hw := (widthSlotT_range ph j).2
  refine ⟨by omega, ?_⟩
  intro ph' k h
  have hp := (privateSlotT_range ph' k).1
  have := congrArg Fin.val h
  omega

theorem scratch_public (ph : Phase) : PublicPrefix (scratchT ph) := by
  refine ⟨C10TailVerdict.scratchT_lt ph, ?_⟩
  intro ph' j h
  have hp := (privateSlotT_range ph' j).2
  have hs : 218 ≤ (scratchT ph).val := by cases ph <;> decide
  have := congrArg Fin.val h
  omega

end NearCubicWires.RepairSource.CloseoutFinal.C10TailSlotsUniform
