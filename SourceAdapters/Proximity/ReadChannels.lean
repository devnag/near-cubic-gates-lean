import SourceAdapters.Code.CountedParsing
import Proof.MachineModel.OrdinaryRadixSemantics

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": paid bit reads from the constructor input or the
callee output. The choice is fixed in the program, and all other data survive. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.FrameReading

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells
open NearCubicGates.Adapters.Code
variable {V M : ℕ}

def readOp (call : Bool) (x : Fin V) : Op V M := if call then .rdK x else .rdI x
def word (C : Ctx) (call : Bool) (a : DS V M) : List Bool := if call then a.kout else C.inp
def pos (call : Bool) (a : DS V M) : ℕ := if call then a.kc else a.ip

def position (call : Bool) (a : DS V M) (n : ℕ) : DS V M :=
  if call then {a with kc := n} else {a with ip := n}

@[simp] theorem word_set (C : Ctx) (call : Bool) (a : DS V M) (x : Fin V) (v : ℕ) :
    word C call (a.set x v) = word C call a := by cases call <;> rfl
@[simp] theorem word_position (C : Ctx) (call : Bool) (a : DS V M) (n : ℕ) :
    word C call (position call a n) = word C call a := by cases call <;> rfl
@[simp] theorem pos_set (call : Bool) (a : DS V M) (x : Fin V) (v : ℕ) :
    pos call (a.set x v) = pos call a := by cases call <;> rfl
@[simp] theorem pos_position (call : Bool) (a : DS V M) (n : ℕ) :
    pos call (position call a n) = n := by cases call <;> rfl
@[simp] theorem position_env (call : Bool) (a : DS V M) (n : ℕ) :
    (position call a n).env = a.env := by cases call <;> rfl
@[simp] theorem position_position (call : Bool) (a : DS V M) (n m : ℕ) :
    position call (position call a n) m = position call a m := by cases call <;> rfl

def readState (call : Bool) (x : Fin V) (a : DS V M) (b : Bool) : DS V M :=
  position call (a.set x b.toNat) (pos call a + 1)

theorem read_bit (C : Ctx) (call : Bool) (x : Fin V) (a : DS V M) (b : Bool)
    (hi : pos call a < (word C call a).length) (hb : (word C call a).getD (pos call a) false = b) :
    Ex C (.op (readOp call x)) a (readState call x a b) 1 := by
  cases call
  · simpa only [readOp, readState, position, pos, word, if_false, Bool.false_eq_true, ↓reduceIte,
      CountedParsing.readState] using CountedParsing.read_bit C x a b hi hb
  · change a.kout.getD a.kc false = b at hb
    simpa only [readOp, readState, position, pos, word, if_true, bitOf, hb]
      using Ex.op (OpEx.rdK (C := C) x a hi)

theorem read_prefix (C : Ctx) (call : Bool) (x : Fin V) (a : DS V M)
    (pre : List Bool) (b : Bool) (tail : List Bool)
    (hin : word C call a = pre ++ b :: tail) (hip : pos call a = pre.length) :
    Ex C (.op (readOp call x)) a (readState call x a b) 1 := by
  apply read_bit C call x a b
  · rw [hin, hip]; simp
  · rw [hin, hip]; simp

theorem read_frame_flag (C : Ctx) (call : Bool) (x : Fin V) (a : DS V M)
    (pre bits tail : List Bool) (hin : word C call a = pre ++ frame bits ++ tail)
    (hip : pos call a = pre.length) :
    Ex C (.op (readOp call x)) a (readState call x a (!bits.isEmpty)) 1 := by
  apply read_bit C call x a (!bits.isEmpty)
  · rw [hin, hip]
    have h := Parsing.frame_nonempty bits
    simp only [List.length_append]
    omega
  · rw [hin, hip, List.append_assoc, List.getD_append_right _ _ _ _ (by omega)]
    simpa using Parsing.frame_first bits tail

end NearCubicGates.Adapters.Proximity.FrameReading
