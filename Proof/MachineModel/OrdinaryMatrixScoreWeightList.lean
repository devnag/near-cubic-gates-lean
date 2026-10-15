import Proof.MachineModel.OrdinaryMatrixScoreWeightCycle

/-! The physical weight-loop payload and its exact two partial-sum invariants.
Each record carries the sign/magnitude field and one actual assignment bit. -/
namespace NearCubicWires.RepairOrdinary.MatrixScoreWeightList
open LocalBitMultitape MatrixScoreWeight
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure Item where
  sign : Bool
  magnitude : List Bool
  selected : Bool

def Item.word (e : Item) := frame (e.sign::e.magnitude)
def Item.assignment (e : Item) := [true,e.selected]
def Item.positive (e : Item) := if e.selected && !e.sign then RadixSemantics.value e.magnitude else 0
def Item.negative (e : Item) := if e.selected && e.sign then RadixSemantics.value e.magnitude else 0
def word (es : List Item) := es.flatMap Item.word
def assignment (es : List Item) := es.flatMap Item.assignment
def positive (es : List Item) := (es.map Item.positive).sum
def negative (es : List Item) := (es.map Item.negative).sum

@[simp] theorem word_nil : word []=[] := rfl
@[simp] theorem word_cons (e : Item) (es : List Item) : word (e::es)=e.word++word es := rfl
@[simp] theorem assignment_nil : assignment []=[] := rfl
@[simp] theorem assignment_cons (e : Item) (es : List Item) : assignment (e::es)=e.assignment++assignment es := rfl
@[simp] theorem positive_nil : positive []=0 := rfl
@[simp] theorem negative_nil : negative []=0 := rfl
@[simp] theorem positive_cons (e : Item) (es : List Item) : positive (e::es)=e.positive+positive es := by simp [positive]
@[simp] theorem negative_cons (e : Item) (es : List Item) : negative (e::es)=e.negative+negative es := by simp [negative]
@[simp] theorem assignment_length (es : List Item) : (assignment es).length=2*es.length := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [Item.assignment,ih]; omega

theorem selected_fit (e : Item) (es : List Item) (w p n : ℕ)
    (hp : p+positive (e::es)<2^w) (hn : n+negative (e::es)<2^w)
    (hb : e.selected=true) : RadixSemantics.value e.magnitude+(if e.sign then n else p)<2^w := by
  obtain ⟨sign,mag,selected⟩ := e
  cases selected <;> simp at hb
  cases sign <;> simp [Item.positive,Item.negative] at hp hn ⊢ <;> omega

theorem positive_tail (e : Item) (es : List Item) (p : ℕ) :
    nextPositive p (RadixSemantics.value e.magnitude) e.sign e.selected+positive es=p+positive (e::es) := by
  simp [nextPositive,Item.positive,Nat.add_assoc]
theorem negative_tail (e : Item) (es : List Item) (n : ℕ) :
    nextNegative n (RadixSemantics.value e.magnitude) e.sign e.selected+negative es=n+negative (e::es) := by
  simp [nextNegative,Item.negative,Nat.add_assoc]

end NearCubicWires.RepairOrdinary.MatrixScoreWeightList
