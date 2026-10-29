import SourceAdapters.Amplification.Assembly

/-!
# Join: the truth table of the rounded STV code as an ordinary machine

Consumer: input 8, the construction of the amplifier `ampG` in its middle regime (`ConstructionObligation`,
`Amplification/Assembly.lean`).

Paper sentences ("Full-range amplification interface"):
* "in the construction of [STV, Lemmas 25 and 28] choose a binary extension field, rounding its size up to the
  required scale, and round the number of polynomial variables up. The evaluation domain is then `F^m`;
  concatenation with a Hadamard block indexes the binary codeword by a product of binary cubes. … Since `S < U(n)`,
  we have `1/δ = 2^{O(n)}`, so the output has `O(n)` input bits and its entire truth table is computable in
  `2^{O(n)}` time."
* "Initialization, the capped simulation, integer operations, and reading and writing the framed arities and truth
  tables all take `2^{O(n)}` time."

Quantity delivered: the full truth table of `stvEncode C n k f` (`Amplification/GateA.lean`) over the field
`𝔽₂[X]/(toPoly (firstPrimitive t))` of the join `Joins/BinaryFieldArithmetic.lean`, with its framed arity
`ℓ = (m+1)·t`, i.e. exactly `truthTableWord` of the middle-regime output `stvOutput C n k f`, from the request word
`frame (binary k) ++ frame (binary n) ++ table f`, within `2^{e(n+k+1)}` steps (`e` may depend on the rounding
constant `C` only). In the middle regime `k ≤ n + 3` (`dyadicExp_le`), so this is `2^{O(n)}`.

What a producer builds: the modulus search (`PrimAsm.Modulus.modM`), field products (`fmulW`) and inverses, the
values of the low-degree extension `innerPoly` at every point of `F^m` (e.g. `Σ_{f(i)=1} Π_j L_{grid(i)_j}(z_j)` with
Lagrange bases over `H`), the Hadamard bits `⟨eltWord y, u⟩`, and the output order of `boolFunctionTable` through
`layoutEquiv`.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Joins

open NearCubicWires NearCubicWires.ExecutableInterfaces NearCubicWires.RepairSource NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicGates.Adapters.Amplification

/-- The middle-regime output at exponent `k`: the rounded STV code of `f` over `𝔽₂[X]/(toPoly (firstPrimitive t))`
(`midOutput` with `k` given; `midOutput C c hc S n f = stvOutput C n (dyadicExp c S hc) f`). -/
noncomputable def stvOutput (C n k : ℕ) (f : BoolFunction n) : AmplifierOutput :=
  letI : Fact (Irreducible (GF.toPoly (GF.firstPrimitive (tParam C n k)))) :=
    ⟨(stvField _ (one_le_tParam C n k)).2.1⟩
  ⟨(mParam n k + 1) * tParam C n k,
    stvEncode C n k (stvField _ (one_le_tParam C n k)).1 (stvField _ (one_le_tParam C n k)).2.2 f⟩

/-- An encoder request: the exponent `k` and the message truth table. -/
structure EncoderRequest where
  k : ℕ
  n : ℕ
  msg : BoolFunction n

/-- The request word: `frame (binary k)` followed by the amplifier input of `msg`. -/
def encoderInput (r : EncoderRequest) : List Bool :=
  RepairOrdinary.frame r.k.bits ++ amplifierInput ⟨r.n, r.msg⟩

/-- The output word: the framed arity and the truth table of the code. -/
noncomputable def encoderOutput (C : ℕ) (r : EncoderRequest) : List Bool :=
  RepairOrdinary.frame (stvOutput C r.n r.k r.msg).arity.bits ++
    boolFunctionTable (stvOutput C r.n r.k r.msg).function

/-- **The join** ("Full-range amplification interface"): for every rounding constant `C`, an ordinary machine writes the truth
table of the rounded STV code in `2^{O(n+k)}` steps. -/
def STVEncoderTable : Prop :=
  ∀ C : ℕ, ∃ e : ℕ,
    Nonempty (WordFunction EncoderRequest encoderInput (encoderOutput C) (fun r => 2 ^ (e * (r.n + r.k + 1))))

theorem midOutput_eq_stvOutput (C c : ℕ) (hc : 1 ≤ c) (S n : ℕ) (f : BoolFunction n) :
    midOutput C c hc S n f = stvOutput C n (dyadicExp c S hc) f := rfl

end NearCubicGates.Adapters.Joins
