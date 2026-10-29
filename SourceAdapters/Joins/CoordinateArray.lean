import SourceAdapters.RAMACSP.ConstraintEmit

/-!
# Join `CoordinateArray`: the coordinate array of the succinct-ACSP generator as an ordinary machine

The succinct-ACSP constraint selects coordinates of the subspace `H` of dimension `mH` with the monomial basis
`e_b = α^b` by the linearized coordinate polynomials `λ_a(X) = Σ_{r<mH} c_{a,r} X^{2^r}`, `λ_a(e_b) = [a = b]`.
Their coefficients `c_{a,r}` solve an `mH × mH` Moore system over `F = 𝔽₂[x]/(irr)`, in `poly(mH)` field operations
of `poly(f)` steps each; every coefficient is written as a reduced mask `< 2^f`.

Consumer: the generator of the succinct-ACSP instance (`RAMACSP/Gen*`), which prints the constraint circuit
`ownCons` (`RAMACSP/ConstraintEmit.lean`): its `compileCoordinates` prefix writes the masks of `coords.coeff a r`, and
its input-record address checks write the rows `coords.coeff j` again (`lamExpr`), with
`coords = Routing.explicitCoordinates (monoBasis irr m) _` (the triangular solver of `Routing/Coordinates*`).
Producer: an ordinary machine computing that array.

Interface (data only; no producer here):
- `CoordReq`, `CoordOk`: the request `(f, irr, m)`: `irr` irreducible of degree `f` (the modulus of BCGT13
  Algorithm 17), and `H` of dimension `mH = m` with the monomial basis, `1 ≤ m`, `m + 2 ≤ f`;
- `coordInput`: the request word `natWord f ++ natWord irr ++ natWord m`;
- `coordMask`, `coordWord`: the output, the `m²` reduced masks of `coeff a r`, row-major (`a` outer), each `f` bits
  least significant first, exactly the constant `gateMask` writes;
- `CoordArrayWF`: an ordinary machine (`RepairOrdinary.WordFunction`) printing it within `K·(|input| + 1)^e` steps
  (`poly(mH)` field operations, each `poly(f)` steps; `m < f`).
-/

set_option autoImplicit false

noncomputable section

namespace NearCubicGates.Adapters.Joins

open NearCubicGates.Adapters NearCubicGates.Adapters.ACSP NearCubicGates.Adapters.RAMACSP NearCubicWires
open NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open Polynomial

/-- The request of the coordinate array: `(f, irr, m)`, `m` the dimension `mH` of `H`. -/
structure CoordReq where
  f : ℕ
  irr : ℕ
  m : ℕ

/-- Its validity: `irr` is the mask of an irreducible polynomial of degree `f` (the modulus of BCGT13 Algorithm 17),
and `1 ≤ m`, `m + 2 ≤ f` (`mH + 2 ≤ f`). -/
def CoordOk (p : CoordReq) : Prop :=
  Irreducible (WireExponent3_5.GF.toPoly p.irr) ∧ (WireExponent3_5.GF.toPoly p.irr).natDegree = p.f ∧
    1 ≤ p.m ∧ p.m + 2 ≤ p.f

/-- The input word (`natWord` encoding). -/
def coordInput (p : CoordReq) : List Bool := natWord p.f ++ natWord p.irr ++ natWord p.m

/-- The reduced `f`-bit mask of `coeff a r` of the explicit coordinate array of the monomial basis `1, α, …, α^{m−1}`
of `F₂[x]/(irr)` (the coordinate polynomials of the header; the constant `gateMask` writes). -/
def coordMask (p : CoordReq) (h : CoordOk p) (a r : Fin p.m) : ℕ :=
  haveI : Fact (Irreducible (WireExponent3_5.GF.toPoly p.irr)) := ⟨h.1⟩
  WireExponent3_5.GF.ofPoly (AdjoinRoot.modByMonicHom (modulus_monic h.1)
    ((Routing.explicitCoordinates (monoBasis (WireExponent3_5.GF.toPoly p.irr) p.m)
      (monoBasis_independent _ p.m (by rw [h.2.1]; have := h.2.2.2; omega))).coeff a r)) p.f

/-- The output word: the masks of the array, row-major, each as `f` bits, least significant first. -/
def coordWord (p : CoordReq) (h : CoordOk p) : List Bool :=
  (List.finRange p.m).flatMap fun a => (List.finRange p.m).flatMap fun r =>
    WilliamsLoaderForms.fixedWidthNatBits p.f (coordMask p h a r)

/-- **The join**: an ordinary machine printing the coordinate array within a polynomial budget in its input
(`poly(mH)` field operations, each `poly(f)` steps). -/
def CoordArrayWF : Prop :=
  ∃ K e : ℕ, Nonempty (WordFunction {p : CoordReq // CoordOk p} (fun p => coordInput p.1)
    (fun p => coordWord p.1 p.2) (fun p => K * ((coordInput p.1).length + 1) ^ e))

end NearCubicGates.Adapters.Joins
