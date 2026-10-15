import Proof.Gates.Main.ShortPCP
import Proof.Gates.Outer.CircuitEval

set_option autoImplicit false

namespace NearCubicGates.Close.ENP.TCirc

open NearCubicWires NearCubicWires.Bindings.MW20 NearCubicWires.SourceInterfaces

variable {ℓ : ℕ} (C : OracleCircuit ℓ ℓ)

/-- `T = 2^ℓ`, the number of oracle addresses (= seeds). -/
abbrev T (ℓ : ℕ) : ℕ := 2 ^ ℓ
/-- The block size. -/
abbrev K (ℓ : ℕ) : ℕ := T ℓ * (2 * ℓ + 1)
/-- The start region: zero wire, `T` inputs, the constant `true`. -/
abbrev S (ℓ : ℕ) : ℕ := T ℓ + 2
/-- The seed length. -/
abbrev L : ℕ := C.nodes.length * K ℓ + 2
/-- The first node of seed `z`. -/
abbrev base (z : ℕ) : ℕ := S ℓ + z * L C
/-- The image of node `c` of `C` at seed `z`. -/
abbrev img (z c : ℕ) : ℕ := base C z + c * K ℓ + (K ℓ - 1)
/-- The first node of the block of node `c` at seed `z`. -/
abbrev bs (z c : ℕ) : ℕ := base C z + c * K ℓ
/-- The first node of group `a` in an oracle block. -/
abbrev gs (z c a : ℕ) : ℕ := bs C z c + a * (2 * ℓ + 1)

/-- The literal `[w = b]`. -/
def lit (b : Bool) (w : ℕ) : BooleanNode (T ℓ) := if b then .or w w else .not w

/-- The node holding `t_a ∧ ⋀_{j' < j} [args_{j'} = a_{j'}]`. -/
def gIdx (z c a j : ℕ) : ℕ := if j = 0 then 1 + a else gs C z c a + 2 * j - 1

/-- The previous running disjunction (`0`, the zero wire, before group `0`). -/
def oPrev (z c a : ℕ) : ℕ := if a = 0 then 0 else gs C z c a - 1

/-- Group `a` of the multiplexer of an oracle gate with arguments `args` (paper §11.6, stage 2: one variable per
oracle address). -/
def group (z c : ℕ) (args : Fin ℓ → ℕ) (a : ℕ) : List (BooleanNode (T ℓ)) :=
  (List.range ℓ).flatMap (fun j =>
    [lit (a.testBit j) (img C z (if h : j < ℓ then args ⟨j, h⟩ else 0)),
      .and (gIdx C z c a j) (gs C z c a + 2 * j)]) ++
    [.or (oPrev C z c a) (gIdx C z c a ℓ)]

/-- A non-oracle node of `C` at seed `z`. -/
def translate (z : ℕ) : OracleNode ℓ ℓ → BooleanNode (T ℓ)
  | .const b => .const b
  | .input i => .const (z.testBit i.val)
  | .not c => .not (img C z c)
  | .and l r => .and (img C z l) (img C z r)
  | .or l r => .or (img C z l) (img C z r)
  | .oracle _ => .const false

/-- The block of node `c` (with value `nd`) at seed `z`. -/
def block (z c : ℕ) : OracleNode ℓ ℓ → List (BooleanNode (T ℓ))
  | .oracle args => (List.range (T ℓ)).flatMap (group C z c args)
  | nd => List.replicate (K ℓ - 1) (.const false) ++ [translate C z nd]

/-- Seed `z`: every node's block, then `¬C(z)` and the running conjunction. -/
def seed (z : ℕ) : List (BooleanNode (T ℓ)) :=
  (List.range C.nodes.length).flatMap (fun c => block C z c (C.nodes.getD c (.const false))) ++
    [.not (img C z C.output.val), .and (base C z - 1) (base C z + C.nodes.length * K ℓ)]

/-- The start region. -/
def start (ℓ : ℕ) : List (BooleanNode (T ℓ)) :=
  [.const false] ++ List.ofFn (fun a : Fin (T ℓ) => .input a) ++ [.const true]

/-- All nodes of `c_T`. -/
def nodes : List (BooleanNode (T ℓ)) := start ℓ ++ (List.range (T ℓ)).flatMap (seed C)

end NearCubicGates.Close.ENP.TCirc
