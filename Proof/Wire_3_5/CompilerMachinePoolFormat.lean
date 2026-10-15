import Proof.Wire_3_5.CompilerMachinePoolSpec
import Proof.Wire_3_5.CompilerMachineKit4

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Pool
open NearCubicWires NearCubicWires.SupplierPipeline NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairRepresentation NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicWires.WireExponent3_5.Block
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)

/-- A P/N pair as two framed `h`-bit words. -/
def pairEnc (h : ℕ) (v : ℕ × ℕ) : List Bool := frame (binary h v.1) ++ frame (binary h v.2)

/-- The normalized child: its weights as P/N pairs, then `false`, then its target's pair. -/
def origRec (h : ℕ) {n : ℕ} (e : ExactThresholdGate n) : List Bool :=
  (List.ofFn e.weight).flatMap (fun z => pairEnc h (pn z)) ++ false :: pairEnc h (pn e.target)

/-- The normalized children, then `false`. -/
def normTape (h : ℕ) {n : ℕ} (gs : List (ExactThresholdGate n)) : List Bool := gs.flatMap (origRec h) ++ [false]

/-- The dense child's fields as the records of the pool stream: P then N word of each field `p ≤ 2·width`. -/
def denseRecs (h : ℕ) {n : ℕ} (side f : List Bool) (width : ℕ) (e : ExactThresholdGate n) : List (List Bool) :=
  (List.range (width + width + 1)).flatMap fun p =>
    [binary h (fieldPN side f width e p).1, binary h (fieldPN side f width e p).2]

variable (a : DecompositionAlgorithm)

/-- **The pool stream's records** (word (1)): the dense fields of every pool child in label order. -/
def poolRecs (h : ℕ) {n : ℕ} (gates : List (SupportedNormalizedGate n)) (side : List Bool) (width : ℕ)
    (flips : List (List Bool)) : List (List Bool) :=
  (poolChildren a gates flips).flatMap fun fe => denseRecs h side fe.1 width fe.2

theorem denseRecs_length (h : ℕ) {n : ℕ} (side f : List Bool) (width : ℕ) (e : ExactThresholdGate n) :
    (denseRecs h side f width e).length = 2 * (width + width + 1) := by
  unfold denseRecs
  rw [List.length_flatMap]
  simp only [List.length_cons, List.length_nil, List.map_const', List.sum_replicate, List.length_range,
    smul_eq_mul]
  ring

theorem denseRecs_width (h : ℕ) {n : ℕ} (side f : List Bool) (width : ℕ) (e : ExactThresholdGate n) :
    ∀ r ∈ denseRecs h side f width e, r.length = h := by
  intro r hr
  unfold denseRecs at hr
  obtain ⟨p, _, hp⟩ := List.mem_flatMap.mp hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl <;> simp

/-! ## The ripple-carry adder as a 1-bit transducer -/

/-- The sum bit. -/
def addOut (x y c : Bool) : Bool := xor (xor x y) c

/-- The carry bit. -/
def addNxt (x y c : Bool) : Bool := (x && y) || (c && xor x y)

/-- **The ripple-carry map is addition** of `h`-bit words (modulo `2^h`). -/
theorem map_add : ∀ (h x y : ℕ) (c : Bool),
    ZipMap.map addOut addNxt (binary h x) (binary h y) c = binary h (x + y + c.toNat)
  | 0, _, _, _ => rfl
  | h + 1, x, y, c => by
    simp only [binary, ZipMap.map]
    have key : ∀ (x y : ℕ) (c : Bool),
        addOut (x % 2 == 1) (y % 2 == 1) c = ((x + y + c.toNat) % 2 == 1) ∧
        (x / 2 + y / 2 + (addNxt (x % 2 == 1) (y % 2 == 1) c).toNat) = (x + y + c.toNat) / 2 := by
      intro x y c
      have hx := Nat.mod_two_eq_zero_or_one x
      have hy := Nat.mod_two_eq_zero_or_one y
      rcases hx with hx | hx <;> rcases hy with hy | hy <;> cases c <;>
        simp [addOut, addNxt, hx, hy, Bool.toNat] <;> omega
    obtain ⟨k1, k2⟩ := key x y c
    rw [k1, map_add h (x / 2) (y / 2), k2]

end NearCubicWires.WireExponent3_5.CompilerMachine.Pool
