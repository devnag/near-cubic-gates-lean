import Proof.MachineModel.OrdinaryMatrixScoreWeightBody

/-! Exact reusable endpoint of the executed selected-weight body. It exposes
both partial signed sums and bounds only local storage, excluding streams. -/
namespace NearCubicWires.RepairOrdinary.MatrixScoreWeight
open LocalBitMultitape RecoveryRootRound SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slotPick (negative : Bool) : Fin 15 → Option (Fin 5) :=
  ![none,none,none,none,none,none,none,some 0,none,none,
    if negative then none else some 1,if negative then some 1 else none,some 2,some 3,some 4]

theorem pick_slots (negative : Bool) (i : Fin 15) : RecoveryFocus.pick (slots negative) i=slotPick negative i := by
  cases negative <;> fin_cases i
  all_goals first
    | decide
    | exact RecoveryFocus.pick_slot (slots false) (slots_injective false) 0
    | exact RecoveryFocus.pick_slot (slots false) (slots_injective false) 1
    | exact RecoveryFocus.pick_slot (slots false) (slots_injective false) 2
    | exact RecoveryFocus.pick_slot (slots false) (slots_injective false) 3
    | exact RecoveryFocus.pick_slot (slots false) (slots_injective false) 4
    | exact RecoveryFocus.pick_slot (slots true) (slots_injective true) 0
    | exact RecoveryFocus.pick_slot (slots true) (slots_injective true) 1
    | exact RecoveryFocus.pick_slot (slots true) (slots_injective true) 2
    | exact RecoveryFocus.pick_slot (slots true) (slots_injective true) 3
    | exact RecoveryFocus.pick_slot (slots true) (slots_injective true) 4

def nextPositive (p x : ℕ) (sign bit : Bool) := p+if bit && !sign then x else 0
def nextNegative (n x : ℕ) (sign bit : Bool) := n+if bit && sign then x else 0

theorem after_tapes (source assignment bits : List Bool) (c w p n : ℕ) (sign bit : Bool) :
    after source assignment bits c w p n sign bit=
      ![source,assignment,ZeroPadding.pad c [bit && !sign],ZeroPadding.pad c [bit && sign],
        ZeroPadding.pad c (frame bits),zeros c,List.replicate w true,
        scalar c w (RadixSemantics.value bits),ZeroPadding.pad c [true],zeros c,
        scalar c w (nextPositive p (RadixSemantics.value bits) sign bit),
        scalar c w (nextNegative n (RadixSemantics.value bits) sign bit),
        if bit then scalar c w (RadixSemantics.value bits+(if sign then n else p)) else zeros c,zeros c,zeros c] := by
  cases bit <;> cases sign <;> funext i <;> fin_cases i <;>
    simp [after,updated,install,pick_slots,slotPick,tapes,scalar,nextPositive,nextNegative,Nat.add_comm]

theorem after_source (source assignment bits : List Bool) (c w p n : ℕ) (sign bit : Bool) :
    after source assignment bits c w p n sign bit 0=source := by rw [after_tapes]; rfl

theorem after_assignment (source assignment bits : List Bool) (c w p n : ℕ) (sign bit : Bool) :
    after source assignment bits c w p n sign bit 1=assignment := by rw [after_tapes]; rfl

theorem after_width (source assignment bits : List Bool) (c w p n : ℕ) (sign bit : Bool) :
    after source assignment bits c w p n sign bit 6=List.replicate w true := by rw [after_tapes]; rfl

theorem after_positive (source assignment bits : List Bool) (c w p n : ℕ) (sign bit : Bool) :
    after source assignment bits c w p n sign bit 10=
      scalar c w (nextPositive p (RadixSemantics.value bits) sign bit) := by rw [after_tapes]; rfl

theorem after_negative (source assignment bits : List Bool) (c w p n : ℕ) (sign bit : Bool) :
    after source assignment bits c w p n sign bit 11=
      scalar c w (nextNegative n (RadixSemantics.value bits) sign bit) := by rw [after_tapes]; rfl

theorem after_support (source assignment bits : List Bool) (c w p n : ℕ) (sign bit : Bool)
    (hw : bits.length≤w) (hc : 2*w+1≤c) (i : Fin 15) (hi : (2 : ℕ) ≤ i.val) :
    (after source assignment bits c w p n sign bit i).length≤c := by
  rw [after_tapes]
  fin_cases i <;> simp at hi
  all_goals simp [scalar,zeros,ZeroPadding.pad_length]
  all_goals first | omega | (split <;> simp_all)

end NearCubicWires.RepairOrdinary.MatrixScoreWeight
