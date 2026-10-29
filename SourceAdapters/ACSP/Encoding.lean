import NineInputs
import SourceAdapters.ACSP.Model
import Proof.Wire_3_5.Shared.GF

/-!
# Bit-level encodings of affine constraint instances, and the clock request

The shared codecs of the reduction to an affine constraint instance (proof of `thm:short-pcp-ours`, Step 1;
`def:acsp`, `ACSP/Affine.lean`) and the request format of `cor:short-pcp-clock`.

- `CodeGate`, `codeCircuit`: a gate of an arithmetic circuit whose constants are bit masks of field elements (bit
  `j` is the coefficient of `X^j`, `GF.toPoly`), and the circuit read over `F₂[X]`.
- `listWord`, `gateWord`: the self-delimiting list and gate words (all numbers as `natWord`s) in which
  `Instance.word` writes the description and the constraint-circuit printer writes its output
  (`Joins/TermsCircuit.lean`).
- `lsbElt`: the paragraph before `def:acsp`, "its `i`-th element, `0 ≤ i < 2^m`, is `o + Σ_j i_j b_j`, where
  `i_1, i_2, …` are the binary digits of `i`, least significant first", on bit-mask data.
- `ClockRequest`, `ClockRequest.word`, `RunsWithin`: a request `(x, t)` of `cor:short-pcp-clock`, its word
  `frame x ++ frame (bits t)` ("The exact Lean interface"), and the promise that `t` bounds the running time of
  `V(x,y)` for every witness `y`, on the actual framed tapes.
-/

set_option autoImplicit false

noncomputable section

namespace NearCubicGates.Adapters.Joins

open NearCubicWires NearCubicWires.RepairSource NearCubicWires.RepairRepresentation
open NearCubicWires.LocalBitMultitape
open NearCubicGates.Adapters.ACSP Polynomial

/-! ## Circuits with bit-mask constants -/

/-- One gate of an arithmetic circuit with constants given as bit masks of field elements. -/
inductive CodeGate where
  | input (index : ℕ)
  | const (value : ℕ)
  | add (left right : ℕ)
  | mul (left right : ℕ)

/-- The circuit with its constants read as polynomials over `F2` (`GF.toPoly`). -/
def codeCircuit (gates : List CodeGate) : ArithCircuit (Polynomial (ZMod 2)) :=
  ⟨gates.map fun
    | .input i => .input i
    | .const v => .const (WireExponent3_5.GF.toPoly v)
    | .add a b => .add a b
    | .mul a b => .mul a b⟩

/-! ## Words -/

/-- A self-delimiting list word. -/
def listWord {α : Type} (g : α → List Bool) (l : List α) : List Bool :=
  natWord l.length ++ (l.map g).flatten

/-- The word of a gate (tag, then two numbers, `0` when unused; all `natWord`s). -/
def gateWord : CodeGate → List Bool
  | .input i => natWord 0 ++ natWord i ++ natWord 0
  | .const v => natWord 1 ++ natWord v ++ natWord 0
  | .add a b => natWord 2 ++ natWord a ++ natWord b
  | .mul a b => natWord 3 ++ natWord a ++ natWord b

/-! ## Subspace elements -/

/-- **Orientation (LSB first).** The `i`-th element (from `0`) of the affine subspace with basis list `basis` and
offset `offset`: `offset + Σ_{j < κ} (bit j of i)·basis[j]`. -/
def lsbElt (irr : ℕ) (κ : ℕ) (basis : List ℕ) (offset : ℕ) (i : ℕ) :
    Field2 (WireExponent3_5.GF.toPoly irr) :=
  elt _ (WireExponent3_5.GF.toPoly offset) +
    ∑ j : Fin κ, if i.testBit j.val then elt _ (WireExponent3_5.GF.toPoly (basis.getD j.val 0)) else 0

/-! ## The clock request and the promise -/

/-- A clock request `(x, t)`: an input `x ∈ {0,1}^n` and a binary integer `t` (`cor:short-pcp-clock`). -/
abbrev ClockRequest := InputRequest × ℕ

/-- Its word, exactly the target's input encoding with `t` in place of `T(n)` ("The exact Lean interface"). -/
def ClockRequest.word (r : ClockRequest) : List Bool := frame (List.ofFn r.1.2) ++ frame r.2.bits

/-- "provided `t` bounds the running time of `V(x,y)` for every witness `y`" (`cor:short-pcp-clock`), on the actual
framed tapes ("The exact Lean interface"; the pointwise form of `RunsInTime`). -/
def RunsWithin (V : OrdinaryVerifier) {n : ℕ} (x : BitInput n) (t : ℕ) : Prop :=
  ∀ y : List Bool, ∃ receipt, run V.machine t (V.inputTapes (List.ofFn x) y) = some receipt

end NearCubicGates.Adapters.Joins
