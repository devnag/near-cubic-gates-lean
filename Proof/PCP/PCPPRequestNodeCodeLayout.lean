import Proof.PCP.PCPPRequestNodeCons

/-! The Boolean-node tagged list has at most three cons cells. These fixed
work banks consume each retained canonical operand once. -/
namespace NearCubicWires.RepairOrdinary.PCPPRequestNodeCode
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def offset (bank : Fin 3) := 6+76*bank.val
def slots (bank : Fin 3) (left right : Fin 234) (j : Fin 76) : Fin 234 :=
  if j=2 then left else if j=3 then right else ⟨offset bank+j.val,by have hb := bank.isLt; have hj := j.isLt; unfold offset; omega⟩
theorem slots_injective (bank : Fin 3) (left right : Fin 234)
    (hl : left.val<offset bank) (hr : right.val<offset bank) (hne : left≠right) :
    Function.Injective (slots bank left right) := by
  intro i j h
  have hv := congrArg Fin.val h
  have hn : left.val≠right.val := fun he => hne (Fin.ext he)
  apply Fin.ext
  simp only [slots] at hv
  split_ifs at hv <;> simp_all only [Fin.ext_iff]
  all_goals omega

theorem outside (bank : Fin 3) (left right i : Fin 234)
    (hl : left≠i) (hr : right≠i)
    (hf : i.val < offset bank ∨ offset bank+76 ≤ i.val) :
    ∀ j,slots bank left right j≠i := by
  intro j he
  have hv := congrArg Fin.val he
  have hlv : left.val≠i.val := fun h => hl (Fin.ext h)
  have hrv : right.val≠i.val := fun h => hr (Fin.ext h)
  have hj := j.isLt
  simp only [slots] at hv
  split_ifs at hv
  all_goals try dsimp only at hv
  all_goals omega

noncomputable def cons (bank : Fin 3) (left right : Fin 234) :=
  RecoveryFocus.machine (slots bank left right) PCPPRequestTaggedCons.machine
def printSlots : Fin 2 → Fin 234 := ![3,4]
theorem printSlots_injective : Function.Injective printSlots := by decide
noncomputable def printer := RecoveryFocus.machine printSlots (HierarchyFixedWord.machine [false])
def input (a b c : ℕ) (binary : Bool) (pa pb pc : ℕ) : Fin 234 → List Bool := fun i =>
  if i=0 then frame a.bits++List.replicate pa false
  else if i=1 then frame b.bits++List.replicate pb false
  else if i=2 then frame c.bits++List.replicate pc false
  else if i=5 then [binary] else []
def middle (b c : ℕ) (binary : Bool) :=
  Nat.pair 1 (Nat.pair b (if binary then Nat.pair 1 (Nat.pair c 0) else 0))
def result (a b c : ℕ) (binary : Bool) := Nat.pair 1 (Nat.pair a (middle b c binary))

end NearCubicWires.RepairOrdinary.PCPPRequestNodeCode
