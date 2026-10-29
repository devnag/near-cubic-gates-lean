import SourceAdapters.Joins.CoordinateArray

/-!
# Join `TermsCircuit`: the serialized constraint circuit `compileTerms` as an ordinary machine

`lem:generator` (G5): the generator prints the constraint circuit `cons` of the succinct-ACSP instance
(`RAMACSP/ConstraintEmit.lean`: `ownCons = (compileTerms l e coords items).gates.map gateMask`, `e` the monomial
basis of `H`, `coords = Routing.explicitCoordinates e _`, `items = routingPairs l ++ machineItems …`), every constant
written as its reduced `f`-bit mask (`lem:generator` (G4)).

Consumer: the generator (`RAMACSP/Gen*`): it prints the request word `termsInput` (its own catalog enumeration and the
coordinate array of `Joins/CoordinateArray`), then runs this machine.
Producer: an ordinary machine replaying `compileTerms` on that word: the coordinate prefix (`compileCoordinates`), then
per item the guard (`compilePattern`), the equation (`compileExpr`, postorder), and the two accumulator gates.

Interface (data only; no producer here):
- `TermsReq`, `TermsOk`: the request `(f, irr, l, items)`, `irr` irreducible of degree `f`, `1 ≤ mH`, `mH + 2 ≤ f`;
- `termsMask`, `termsCoeff`, `termsCoordWord`: reduced `f`-bit masks (exactly the constants `gateMask` writes) and the
  coordinate array of `Joins/CoordinateArray` as words;
- `TermTok`, `exprToks`, `exprWord`: an equation in postorder (the push order of `compileExpr`), constants as masks,
  reads as raw variables (`varCode`), closed by an end token; `guardCode`, `patternWord`, `itemWord`: one item, led by
  the continuation flag `1`;
- `termsInput`: `natWord f ++ natWord mH ++ coordinate masks ++ listWord natWord (globalBank l) ++ items ++ natWord 0`;
- `termsCircuit`, `termsOutput`: the serialized circuit `listWord gateWord (compileTerms … ).gates.map gateMask`;
- `TermsCircuitWF`: an ordinary machine (`RepairOrdinary.WordFunction`) printing it within `K·(|input| + 1)^e` steps.
-/

set_option autoImplicit false

noncomputable section

namespace NearCubicGates.Adapters.Joins

open NearCubicGates.Adapters NearCubicGates.Adapters.ACSP NearCubicGates.Adapters.RAMACSP NearCubicWires
open NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open Polynomial

/-- The request: field degree `f`, modulus `irr`, routing layout `l` (`mH = l.m`), and the guarded items over
`F₂[x]/(irr)` (`app:affine-embedding` `ItemList`). -/
structure TermsReq where
  f : ℕ
  irr : (ZMod 2)[X]
  l : Routing.Layout
  items : List (Routing.Pattern l.m × Routing.Expr (Field2 irr))

/-- Its validity: `irr` irreducible of degree `f` (BCGT13 Algorithm 17), `1 ≤ mH`, `mH + 2 ≤ f` (as `CoordOk`). -/
def TermsOk (p : TermsReq) : Prop :=
  Irreducible p.irr ∧ p.irr.natDegree = p.f ∧ 1 ≤ p.l.m ∧ p.l.m + 2 ≤ p.f

/-- The reduced `f`-bit mask of a field element (the constant `gateMask` writes). -/
def termsMask (p : TermsReq) (h : TermsOk p) (c : Field2 p.irr) : ℕ :=
  WireExponent3_5.GF.ofPoly (AdjoinRoot.modByMonicHom (modulus_monic h.1) c) p.f

/-- The independence of the monomial basis of `H` (`mH < f`). -/
theorem termsIndependent (p : TermsReq) (h : TermsOk p) [Fact (Irreducible p.irr)] :
    Routing.Independent p.l.m (monoBasis p.irr p.l.m) :=
  monoBasis_independent _ p.l.m (by
    have h1 : p.irr.natDegree = p.f := h.2.1
    have h2 : p.l.m + 2 ≤ p.f := h.2.2.2
    omega)

/-- The coefficient `c_{a,r}` of the explicit coordinate array of the monomial basis `1, α, …, α^{mH−1}` of `H`
(the triangular solver). -/
def termsCoeff (p : TermsReq) (h : TermsOk p) (a r : Fin p.l.m) : Field2 p.irr :=
  haveI : Fact (Irreducible p.irr) := ⟨h.1⟩
  (Routing.explicitCoordinates (monoBasis p.irr p.l.m) (termsIndependent p h)).coeff a r

/-- The coordinate array as words: the `mH²` masks of `coeff a r`, row-major, each `f` bits least significant first
(the output word `coordWord` of `Joins/CoordinateArray` at `(f, mask of irr, mH)`). -/
def termsCoordWord (p : TermsReq) (h : TermsOk p) : List Bool :=
  (List.finRange p.l.m).flatMap fun a => (List.finRange p.l.m).flatMap fun r =>
    WilliamsLoaderForms.fixedWidthNatBits p.f (termsMask p h (termsCoeff p h a r))

/-- One token of an equation in postorder. -/
inductive TermTok where
  | const (value : ℕ)
  | read (v : Routing.Vars)
  | add
  | mul
  | square

/-- The code of a read variable: `none ↦ 0`, `some b ↦ b + 1` (`b` the raw bank mask). -/
def varCode : Routing.Vars → ℕ
  | none => 0
  | some b => b + 1

/-- The word of a token (tag, then one number, `0` when unused; all `natWord`s). -/
def termTokWord : TermTok → List Bool
  | .const v => natWord 0 ++ natWord v
  | .read v => natWord 1 ++ natWord (varCode v)
  | .add => natWord 2 ++ natWord 0
  | .mul => natWord 3 ++ natWord 0
  | .square => natWord 4 ++ natWord 0

/-- An equation in postorder (the push order of `compileExpr`), constants as masks `mk c`, reads as their raw
variable (the printer resolves `Routing.readIndex l v = 1 + idxOf b (globalBank l)` against the bank in its input). -/
def exprToks {F : Type} (mk : F → ℕ) : Routing.Expr F → List TermTok
  | .const c => [.const (mk c)]
  | .read v => [.read v]
  | .add a b => exprToks mk a ++ exprToks mk b ++ [.add]
  | .mul a b => exprToks mk a ++ exprToks mk b ++ [.mul]
  | .square a => exprToks mk a ++ [.square]

/-- The word of an equation: its tokens, then the end token (tag `5`). -/
def exprWord {F : Type} (mk : F → ℕ) (e : Routing.Expr F) : List Bool :=
  (exprToks mk e).flatMap termTokWord ++ (natWord 5 ++ natWord 0)

/-- A guard entry: `none ↦ 0`, `some false ↦ 1`, `some true ↦ 2`. -/
def guardCode : Option Bool → ℕ
  | none => 0
  | some false => 1
  | some true => 2

/-- The word of a guard pattern: its `mH` entries in order (no count; `mH` is in the header). -/
def patternWord {m : ℕ} (g : Routing.Pattern m) : List Bool :=
  (List.ofFn g).flatMap fun o => natWord (guardCode o)

/-- The word of one item: the continuation flag `1`, its guard, its equation. -/
def itemWord {F : Type} (mk : F → ℕ) {m : ℕ} (x : Routing.Pattern m × Routing.Expr F) : List Bool :=
  natWord 1 ++ (patternWord x.1 ++ exprWord mk x.2)

/-- The input word: `f`, `mH`, the coordinate array (`Joins/CoordinateArray`), the variable bank `globalBank l`,
the items (each led by the flag `1`), the end flag `0`. -/
def termsInput (p : TermsReq) (h : TermsOk p) : List Bool :=
  natWord p.f ++ natWord p.l.m ++ termsCoordWord p h ++ listWord natWord (Routing.globalBank p.l) ++
    (p.items.flatMap (itemWord (termsMask p h)) ++ natWord 0)

/-- The serialized circuit: `compileTerms` over `F₂[x]/(irr)` with the monomial basis of `H` and its explicit
coordinate array, every constant as its reduced `f`-bit mask (`gateMask`). -/
def termsCircuit (p : TermsReq) (h : TermsOk p) : List CodeGate :=
  haveI : Fact (Irreducible p.irr) := ⟨h.1⟩
  (Routing.Circuit.compileTerms p.l (monoBasis p.irr p.l.m)
    (Routing.explicitCoordinates (monoBasis p.irr p.l.m) (termsIndependent p h)) p.items).gates.map
    (gateMask p.irr (modulus_monic h.1) p.f)

/-- The output word. -/
def termsOutput (p : TermsReq) (h : TermsOk p) : List Bool :=
  listWord gateWord (termsCircuit p h)

/-- **The join**: an ordinary machine printing the serialized constraint circuit within a polynomial budget in its
input. -/
def TermsCircuitWF : Prop :=
  ∃ K e : ℕ, Nonempty (WordFunction {p : TermsReq // TermsOk p} (fun p => termsInput p.1 p.2)
    (fun p => termsOutput p.1 p.2) (fun p => K * ((termsInput p.1 p.2).length + 1) ^ e))

end NearCubicGates.Adapters.Joins
