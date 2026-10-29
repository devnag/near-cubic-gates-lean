import SourceAdapters.ACSP.Encoding

/-!
# Affine constraint instances (`def:acsp`)

The target of the reduction of the proof of `thm:short-pcp-ours`, Step 1, in bit-level form. The paragraph before
`def:acsp`: "Let `irr ∈ F₂[X]` be irreducible of degree `f`, and let `F = F₂[X]/(irr)`, the field with `2^f`
elements. An affine subspace of `F` over `F₂` is given by a basis `b_1, …, b_m` and an offset `o`; its `i`-th
element, `0 ≤ i < 2^m`, is `o + Σ_j i_j b_j`, where `i_1, i_2, …` are the binary digits of `i`, least significant
first."

`def:acsp`: "An affine constraint instance consists of an irreducible `irr` of degree `f`, an affine subspace
`H ⊆ F` of dimension `m_H`, neighbors `N_ν(X) = a_ν X + b_ν` with `a_ν ≠ 0`, for `1 ≤ ν ≤ c_N` and some `c_N ≥ 1`, a
constraint polynomial `P(X, Y_1, …, Y_{c_N})` over `F` given by an arithmetic circuit, and an affine subspace
`I ⊆ H` of dimension `m`. Give `X` weight `1` and each `Y_ν` weight `2^{m_H} − 1`. The instance has degree bound
`d_B` if every monomial of `P` has weight at most `d_B`; we require `4 d_B ≤ 2^f`. The instance accepts a binary
string `x̄` of length `2^m` if some `A ∈ F[X]` of degree less than `2^{m_H}` satisfies
`P(α, A(N_1(α)), …, A(N_{c_N}(α))) = 0` for every `α ∈ H`, and `A(α_i) = x̄_i` for every `i < 2^m`, where `α_i` is
the `i`-th element of `I` and the bits `0, 1` are read in `F`."

Representation. A field element is a bit mask (bit `j` is the coefficient of `X^j`; `GF.toPoly`); the neighbors are
the pairs `(a_ν, b_ν)`, indexed from `0`; the constraint polynomial is the circuit `cons` with its constants as masks
(`codeCircuit`), variable `0` being `X` and variable `ν + 1` being `Y_{ν+1}`. The circuit and list encodings
(`CodeGate`, `codeCircuit`, `listWord`, `gateWord`; `ACSP/Encoding.lean`) are the ones the constraint-circuit printer
writes (`Joins/TermsCircuit.lean`).

`Instance.IsValid` is `def:acsp` clause by clause, `Instance.Accepts` its acceptance, `Instance.WellFormed` the
canonical bit-level form, and `Instance.word` the description. The bound on every composition `B_A` (the paragraph
after `def:acsp`) is a theorem about this definition (`ACSP/AffineDegree.lean`), not part of it.
-/

set_option autoImplicit false

noncomputable section

namespace NearCubicGates.Adapters.ACSP.Affine

open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Adapters.Joins (CodeGate codeCircuit listWord gateWord lsbElt)
open Polynomial

/-- **An affine constraint instance** (`def:acsp`) with field elements as bit masks: the degree `f` and the modulus
`irr`; the basis and offset of `H`; the neighbors `N_ν(X) = a_ν X + b_ν` as the pairs `(a_ν, b_ν)`; the circuit of
the constraint polynomial `P`; the basis and offset of `I`. -/
structure Instance where
  f : ℕ
  irr : ℕ
  hBasis : List ℕ
  hOffset : ℕ
  nbr : List (ℕ × ℕ)
  cons : List CodeGate
  iBasis : List ℕ
  iOffset : ℕ

namespace Instance

variable (c : Instance)

/-- `irr ∈ F₂[X]`. -/
def irrPoly : (ZMod 2)[X] := NearCubicWires.WireExponent3_5.GF.toPoly c.irr

/-- "`F = F₂[X]/(irr)`". -/
abbrev Fld : Type := Field2 c.irrPoly

/-- The field element of a mask. -/
def elt (a : ℕ) : c.Fld := NearCubicGates.Adapters.ACSP.elt c.irrPoly (NearCubicWires.WireExponent3_5.GF.toPoly a)

/-- `m_H`, the dimension of `H`. -/
def mH : ℕ := c.hBasis.length

/-- `m`, the dimension of `I`. -/
def m : ℕ := c.iBasis.length

/-- `c_N`, the number of neighbors. -/
def cN : ℕ := c.nbr.length

/-- The basis of `H`, as polynomials over `F₂`. -/
def hBasisPoly (j : ℕ) : (ZMod 2)[X] := NearCubicWires.WireExponent3_5.GF.toPoly (c.hBasis.getD j 0)

/-- The basis of `I`, as polynomials over `F₂`. -/
def iBasisPoly (j : ℕ) : (ZMod 2)[X] := NearCubicWires.WireExponent3_5.GF.toPoly (c.iBasis.getD j 0)

/-- The element of `H` with coefficient vector `coeff`. -/
def hElt (coeff : Fin c.mH → Bool) : c.Fld :=
  affineElt c.irrPoly c.mH c.hBasisPoly (NearCubicWires.WireExponent3_5.GF.toPoly c.hOffset) coeff

/-- The element of `I` with coefficient vector `coeff`. -/
def iEltOf (coeff : Fin c.m → Bool) : c.Fld :=
  affineElt c.irrPoly c.m c.iBasisPoly (NearCubicWires.WireExponent3_5.GF.toPoly c.iOffset) coeff

/-- "`α_i` is the `i`-th element of `I`" (the binary digits of `i`, least significant first). -/
def iElt (i : ℕ) : c.Fld :=
  indexedElt c.irrPoly c.m c.iBasisPoly (NearCubicWires.WireExponent3_5.GF.toPoly c.iOffset) i

/-- The slope `a_ν` of neighbor `ν` (from `0`). -/
def slope (ν : ℕ) : c.Fld := c.elt (c.nbr.getD ν (0, 0)).1

/-- The offset `b_ν` of neighbor `ν` (from `0`). -/
def shift (ν : ℕ) : c.Fld := c.elt (c.nbr.getD ν (0, 0)).2

/-- "`N_ν(X) = a_ν X + b_ν`". -/
def nbrFn (ν : Fin c.cN) (α : c.Fld) : c.Fld := c.slope ν.val * α + c.shift ν.val

/-- "a constraint polynomial `P(X, Y_1, …, Y_{c_N})` over `F` given by an arithmetic circuit". -/
def consPoly : MvPolynomial (Fin (c.cN + 1)) c.Fld := fieldPoly c.irrPoly (codeCircuit c.cons) (c.cN + 1)

/-- "Give `X` weight `1` and each `Y_ν` weight `2^{m_H} − 1`." -/
def weight (j : Fin (c.cN + 1)) : ℕ := if j.val = 0 then 1 else 2 ^ c.mH - 1

/-- "The instance has degree bound `d_B` if every monomial of `P` has weight at most `d_B`." -/
def HasDegreeBound (dB : ℕ) : Prop := ∀ s ∈ c.consPoly.support, Finsupp.weight c.weight s ≤ dB

/-- **`def:acsp`**, clause by clause. -/
def IsValid : Prop :=
  -- "an irreducible `irr` of degree `f`"
  (Irreducible c.irrPoly ∧ c.irrPoly.natDegree = c.f) ∧
  -- "an affine subspace `H ⊆ F` of dimension `m_H`"
  AffineIndependent c.irrPoly c.mH c.hBasisPoly (NearCubicWires.WireExponent3_5.GF.toPoly c.hOffset) ∧
  -- "neighbors `N_ν(X) = a_ν X + b_ν` with `a_ν ≠ 0`, for `1 ≤ ν ≤ c_N` and some `c_N ≥ 1`"
  (1 ≤ c.cN ∧ ∀ p ∈ c.nbr, c.elt p.1 ≠ 0) ∧
  -- "an affine subspace `I ⊆ H` of dimension `m`"
  (AffineIndependent c.irrPoly c.m c.iBasisPoly (NearCubicWires.WireExponent3_5.GF.toPoly c.iOffset) ∧
    ∀ coeff : Fin c.m → Bool, ∃ coeff' : Fin c.mH → Bool, c.iEltOf coeff = c.hElt coeff') ∧
  -- "The instance has degree bound `d_B` if …; we require `4 d_B ≤ 2^f`"
  ∃ dB : ℕ, c.HasDegreeBound dB ∧ 4 * dB ≤ 2 ^ c.f

/-- **Acceptance** (`def:acsp`): "The instance accepts a binary string `x̄` of length `2^m` if some `A ∈ F[X]` of
degree less than `2^{m_H}` satisfies `P(α, A(N_1(α)), …, A(N_{c_N}(α))) = 0` for every `α ∈ H`, and `A(α_i) = x̄_i`
for every `i < 2^m`, where `α_i` is the `i`-th element of `I` and the bits `0, 1` are read in `F`." -/
def Accepts (xbar : List Bool) : Prop :=
  xbar.length = 2 ^ c.m ∧
  ∃ A : c.Fld[X], A.degree < (2 ^ c.mH : ℕ) ∧
    (∀ coeff : Fin c.mH → Bool,
      MvPolynomial.eval (Fin.cons (c.hElt coeff) fun ν : Fin c.cN => A.eval (c.nbrFn ν (c.hElt coeff)))
        c.consPoly = 0) ∧
    ∀ i (hi : i < xbar.length), A.eval (c.iElt i) = if xbar[i] then 1 else 0

/-- "`B_A(X) = P(X, A(N_1(X)), …, A(N_{c_N}(X)))`" (the paragraph after `def:acsp`). -/
def composed (A : c.Fld[X]) : c.Fld[X] :=
  MvPolynomial.aeval (Fin.cons (X : c.Fld[X]) fun ν : Fin c.cN =>
    A.comp (Polynomial.C (c.slope ν.val) * X + Polynomial.C (c.shift ν.val))) c.consPoly

/-! ## The bit-level form -/

/-- **The canonical bit-level form** of the field elements of the instance (the paragraph before `def:acsp`:
"`F = F₂[X]/(irr)`, the field with `2^f` elements", each element written as its residue of degree `< f`): the
modulus has bit `f` set and no higher bit, and every mask and every circuit constant is below `2^f`. -/
def WellFormed : Prop :=
  c.irr.testBit c.f = true ∧ c.irr < 2 ^ (c.f + 1) ∧
  (∀ a ∈ c.hBasis, a < 2 ^ c.f) ∧ c.hOffset < 2 ^ c.f ∧
  (∀ p ∈ c.nbr, p.1 < 2 ^ c.f ∧ p.2 < 2 ^ c.f) ∧
  (∀ g ∈ c.cons, ∀ v, g = CodeGate.const v → v < 2 ^ c.f) ∧
  (∀ a ∈ c.iBasis, a < 2 ^ c.f) ∧ c.iOffset < 2 ^ c.f

/-- The word of a neighbor `(a_ν, b_ν)`. -/
def pairWord (p : ℕ × ℕ) : List Bool := natWord p.1 ++ natWord p.2

/-- **The description** of the instance (`lem:generator`: "outputs `x̄` and the instance"): every field in order,
each self-delimiting. -/
def word : List Bool :=
  natWord c.f ++ natWord c.irr ++ listWord natWord c.hBasis ++ natWord c.hOffset ++
    listWord pairWord c.nbr ++ listWord gateWord c.cons ++
    listWord natWord c.iBasis ++ natWord c.iOffset

/-- **Transport.** The `i`-th element of `I` is `lsbElt` on the bit-level data: `iOffset` plus the basis
masks selected by the binary digits of `i`, least significant first. -/
theorem iElt_eq_lsbElt (i : ℕ) : c.iElt i = lsbElt c.irr c.m c.iBasis c.iOffset i := by
  simp only [iElt, indexedElt, affineElt, lsbElt]
  rfl

end Instance

end NearCubicGates.Adapters.ACSP.Affine
