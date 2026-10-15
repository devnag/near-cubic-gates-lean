import Proof.Hierarchy.CompetitorSameBucketGroupTapeCases
import Proof.Hierarchy.CompetitorSameBucketGroupArithmetic

/-! The actual reusable accumulator update in the fixed grouping bank.
Only the selected P or N field changes; the streaming source/output cursors,
width drivers and all other retained fields survive the paid add/reset. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketGroupMachine
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def arithmeticProgram (negative : Bool) :=
  RecoveryFocus.machine (arithmeticSlots negative) CompetitorSameBucketGroupArithmetic.machine

theorem arithmetic_injective (negative : Bool) : Function.Injective (arithmeticSlots negative) := by
  cases negative <;> decide

def arithmeticPicks (negative : Bool) : Fin 24 → Option (Fin 11) :=
  ![none,some 0,none,none,none,none,none,some 1,none,none,none,none,none,
    if negative then none else some 5,if negative then some 5 else none,none,
    some 2,some 3,some 4,some 6,some 7,some 8,some 9,some 10]

theorem arithmetic_pick (negative : Bool) (i : Fin 24) :
    RecoveryFocus.pick (arithmeticSlots negative) i=arithmeticPicks negative i := by
  cases negative
  · fin_cases i
    · decide
    · exact RecoveryFocus.pick_slot (arithmeticSlots false) (arithmetic_injective _) 0
    · decide
    · decide
    · decide
    · decide
    · decide
    · exact RecoveryFocus.pick_slot (arithmeticSlots false) (arithmetic_injective _) 1
    · decide
    · decide
    · decide
    · decide
    · decide
    · exact RecoveryFocus.pick_slot (arithmeticSlots false) (arithmetic_injective _) 5
    · decide
    · decide
    · exact RecoveryFocus.pick_slot (arithmeticSlots false) (arithmetic_injective _) 2
    · exact RecoveryFocus.pick_slot (arithmeticSlots false) (arithmetic_injective _) 3
    · exact RecoveryFocus.pick_slot (arithmeticSlots false) (arithmetic_injective _) 4
    · exact RecoveryFocus.pick_slot (arithmeticSlots false) (arithmetic_injective _) 6
    · exact RecoveryFocus.pick_slot (arithmeticSlots false) (arithmetic_injective _) 7
    · exact RecoveryFocus.pick_slot (arithmeticSlots false) (arithmetic_injective _) 8
    · exact RecoveryFocus.pick_slot (arithmeticSlots false) (arithmetic_injective _) 9
    · exact RecoveryFocus.pick_slot (arithmeticSlots false) (arithmetic_injective _) 10
  · fin_cases i
    · decide
    · exact RecoveryFocus.pick_slot (arithmeticSlots true) (arithmetic_injective _) 0
    · decide
    · decide
    · decide
    · decide
    · decide
    · exact RecoveryFocus.pick_slot (arithmeticSlots true) (arithmetic_injective _) 1
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · exact RecoveryFocus.pick_slot (arithmeticSlots true) (arithmetic_injective _) 5
    · decide
    · exact RecoveryFocus.pick_slot (arithmeticSlots true) (arithmetic_injective _) 2
    · exact RecoveryFocus.pick_slot (arithmeticSlots true) (arithmetic_injective _) 3
    · exact RecoveryFocus.pick_slot (arithmeticSlots true) (arithmetic_injective _) 4
    · exact RecoveryFocus.pick_slot (arithmeticSlots true) (arithmetic_injective _) 6
    · exact RecoveryFocus.pick_slot (arithmeticSlots true) (arithmetic_injective _) 7
    · exact RecoveryFocus.pick_slot (arithmeticSlots true) (arithmetic_injective _) 8
    · exact RecoveryFocus.pick_slot (arithmeticSlots true) (arithmetic_injective _) 9
    · exact RecoveryFocus.pick_slot (arithmeticSlots true) (arithmetic_injective _) 10

theorem arithmetic_heads (negative : Bool) (pos opos : ℕ) (j : Fin 11) :
    heads pos opos (arithmeticSlots negative j)=0 := by
  cases negative <;> fin_cases j <;> rfl

theorem arithmetic_input (negative : Bool) (s : Store) (cap w p m : ℕ)
    (source out : List Bool) (j : Fin 11) :
    s.tapes cap w p m source out (arithmeticSlots negative j)=
      CompetitorSameBucketGroupArithmetic.data cap w s.magnitude (selected s negative)
        (CompetitorSameBucketGroupArithmetic.clean cap) j := by
  cases negative <;> fin_cases j <;> rfl

theorem arithmetic_output (negative : Bool) (s : Store) (cap w p m : ℕ) (source out : List Bool) :
    install (arithmeticSlots negative) (s.tapes cap w p m source out)
      (CompetitorSameBucketGroupArithmetic.data cap w s.magnitude
        (value s.magnitude+selected s negative) (CompetitorSameBucketGroupArithmetic.clean cap))=
      (accumulated s negative).tapes cap w p m source out := by
  funext i
  cases negative <;> fin_cases i <;>
    simp only [install,arithmetic_pick,arithmeticPicks] <;>
    simp only [Store.tapes_at] <;> rfl

theorem arithmetic_run (negative : Bool) (s : Store) (cap w p m pos : ℕ) (source out : List Bool)
    (hw : s.magnitude.length≤w) (hc : 4*w+3≤cap)
    (hfit : value s.magnitude+selected s negative<2^w) :
    Run (arithmeticProgram negative) (2*cap+16*w+23) cap w p m pos pos source out out
      s (accumulated s negative) := by
  have h := CompetitorSameBucketGroupArithmetic.accumulate_ready cap w s.magnitude (selected s negative) hw hc hfit
  obtain ⟨r,hr,hh,ht,hs⟩ := HierarchyBinary.focused_run (arithmeticSlots negative)
    (arithmetic_injective negative) _ _ _ h (heads pos out.length) (s.tapes cap w p m source out)
    (arithmetic_heads negative pos out.length) (arithmetic_input negative s cap w p m source out)
  refine ⟨r,hr,hh,?_,hs⟩
  exact ht.trans (arithmetic_output negative s cap w p m source out)

end NearCubicWires.RepairOrdinary.CompetitorSameBucketGroupMachine
