import SourceAdapters.RAMACSP.ConstraintCatalog
import SourceAdapters.RAMACSP.CheckClauses
import SourceAdapters.Routing.CoordinateJoin
import SourceAdapters.Routing.CircuitTerms

/-!
# The emitted constraint circuit `cons` (route B)

Paper: `thm:embedding`, `lem:acsp-degree` and `lem:generator`. The circuit
emits the sum of selector-times-equation terms. Coordinates are linearized
polynomials `λ_a(X) = Σ_r c_(a,r) X^(2^r)` sharing a squaring chain; each
pattern is the product of its selected coordinate factors. Constants are
written as reduced masks below `2^f`.

The circuit is the routing area's shared-prefix compiler `Routing.Circuit.compileTerms` (the join's
`compileCoordinates`, then per item `compilePattern`, `compileExpr`, product, accumulated sum — the loop of
`compileRouting` over an arbitrary item list; correctness theorem `Routing.Circuit.compileTerms_correct`) over the item list
`routingItems ++ machineItems`
(`ConstraintCatalog`), with the coordinate array `Routing.explicitCoordinates` (the triangular-solver array of
`Routing/Coordinates*`, which the generator prints). Its field constants are then written as reduced masks
(`p mod irr` as an `f`-bit mask). The input-record address check (B5) uses `λ_j(X)` written on its own squaring
chain (`lamExpr`).

For a modulus that is not irreducible of degree `f` (never the case for Shoup's choice) the circuit is empty.
-/

set_option autoImplicit false

noncomputable section

namespace NearCubicGates.Adapters.RAMACSP

open NearCubicGates.Adapters NearCubicGates.Adapters.ACSP NearCubicGates.Adapters.ShortPCP
open NearCubicGates.Adapters.Joins
open NearCubicWires NearCubicWires.RepairOrdinary Polynomial

section Builders

variable {F : Type} [Field F] [CharP F 2]

/-- `X^{2^r}` as an expression: `r` squarings of `X`. -/
def squares : ℕ → Routing.Expr F
  | 0 => .read none
  | r + 1 => .square (squares r)

/-- `λ(X) = Σ_r c_r X^{2^r}` for a coefficient row `c` (`app:affine-embedding` Coordinate and row selectors). -/
def lamExpr {m : ℕ} (row : Fin m → F) : Routing.Expr F :=
  (List.finRange m).foldr (fun r acc => .add (.mul (.const (row r)) (squares r.val)) acc) (.const 0)

/-- The routing items of the join as (guard, equation) pairs. -/
def routingPairs (l : Routing.Layout) : List (Routing.Pattern l.m × Routing.Expr F) :=
  (Routing.routingItems l).map fun t => (t.guard l, t.expr l)

end Builders

/-- A gate over `F₂[x]/(irr)` written with its constant as the reduced `f`-bit mask (`lem:generator` (G4): all results are
reduced masks `< 2^f`). -/
def gateMask (irr : (ZMod 2)[X]) (hm : irr.Monic) (f : ℕ) : ArithGate (AdjoinRoot irr) → CodeGate
  | .input i => .input i
  | .const c => .const (WireExponent3_5.GF.ofPoly (AdjoinRoot.modByMonicHom hm c) f)
  | .add a b => .add a b
  | .mul a b => .mul a b

variable (V : Verifier)

/-- The instance's modulus (Shoup's polynomial of degree `f`, read back from its mask) — the modulus field of the
instance frame, which does not depend on the constraint circuit (definitionally that of every `ownInst`). -/
def baseIrr (irrPoly : ℕ → (ZMod 2)[X]) (r : ClockRequest) : (ZMod 2)[X] :=
  (ownInst V irrPoly (fun _ => []) r).irrPoly

theorem modulus_monic {irr : (ZMod 2)[X]} (h : Irreducible irr) : irr.Monic := by
  have hl : irr.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr h.ne_zero
  exact WireExponent3_5.GF.zmod2_ne_zero _ hl

/-- The input-record exponent `a = log₂ N_A = m − ω` (`app:affine-embedding` Position data). -/
def inRecExp (r : ClockRequest) : ℕ := inExp V r - wordExp V r.2

/-- The full item list at a clock request, over the field of `irr` with coordinate rows `coeff`. -/
def ownItems {F : Type} [Field F] [CharP F 2] (r : ClockRequest) (lam : ℕ → Routing.Expr F) :
    List (Routing.Pattern (ownLayout V r.2).m × Routing.Expr F) :=
  routingPairs (ownLayout V r.2) ++
    machineItems (ownLayout V r.2) (wordExp V r.2) (regCount V) (codeLen V) (ownRam V r) RAMTrace.mnKind
      (tau V r.2) (inRecExp V r) lam

/-- The modulus condition: `irr` irreducible of degree `f` (Shoup's choice satisfies it). -/
def ModulusGood (irrPoly : ℕ → (ZMod 2)[X]) (r : ClockRequest) : Prop :=
  Irreducible (baseIrr V irrPoly r) ∧ (baseIrr V irrPoly r).natDegree = fieldExp V r.2

/-- The circuit over the field `F₂[x]/(irr)` (before serialization). -/
def ownCircuit (irrPoly : ℕ → (ZMod 2)[X]) (r : ClockRequest) (h : ModulusGood V irrPoly r) :
    ArithCircuit (Field2 (baseIrr V irrPoly r)) :=
  haveI : Fact (Irreducible (baseIrr V irrPoly r)) := ⟨h.1⟩
  let l := ownLayout V r.2
  let e : Fin l.m → Field2 (baseIrr V irrPoly r) := monoBasis (baseIrr V irrPoly r) l.m
  let hi : Routing.Independent l.m e := monoBasis_independent _ _ (by
    rw [h.2, ownLayout_m]; have := domExp_add_two_le_fieldExp V r.2; omega)
  let coords := Routing.explicitCoordinates e hi
  let lam : ℕ → Routing.Expr (Field2 (baseIrr V irrPoly r)) := fun j =>
    if hj : j < l.m then lamExpr (coords.coeff ⟨j, hj⟩) else .const 0
  Routing.Circuit.compileTerms l e coords (ownItems V r lam)

/-- The serialized circuit (constants as reduced `f`-bit masks). -/
def ownConsOf (irrPoly : ℕ → (ZMod 2)[X]) (r : ClockRequest) (h : ModulusGood V irrPoly r) : List CodeGate :=
  (ownCircuit V irrPoly r h).gates.map (gateMask (baseIrr V irrPoly r) (modulus_monic h.1) (fieldExp V r.2))

open Classical in
/-- **The constraint circuit `cons`** of the instance at the clock request `r` (`app:affine-embedding`, `lem:acsp-degree`, `lem:generator` (G5)). -/
def ownCons (irrPoly : ℕ → (ZMod 2)[X]) (r : ClockRequest) : List CodeGate :=
  if h : ModulusGood V irrPoly r then ownConsOf V irrPoly r h else []

/-! ## The constants of `cons` are reduced field-word masks (`lem:generator`) -/

theorem ownInst_cons (irrPoly : ℕ → (ZMod 2)[X]) (cons : ClockRequest → List CodeGate) (r : ClockRequest) :
    (ownInst V irrPoly cons r).cons = cons r := by
  unfold ownInst; rfl

theorem gateMask_const_lt (irr : (ZMod 2)[X]) (hm : irr.Monic) (f : ℕ) (g0 : ArithGate (AdjoinRoot irr)) (v : ℕ)
    (h : gateMask irr hm f g0 = CodeGate.const v) : v < 2 ^ f := by
  cases g0 with
  | const c =>
    simp only [gateMask, CodeGate.const.injEq] at h
    rw [← h]; exact WireExponent3_5.GF.ofPoly_lt _ _
  | input i => simp [gateMask] at h
  | add a b => simp [gateMask] at h
  | mul a b => simp [gateMask] at h

theorem ownCons_const_lt (irrPoly : ℕ → (ZMod 2)[X]) (r : ClockRequest) :
    ∀ g ∈ ownCons V irrPoly r, ∀ v, g = CodeGate.const v → v < 2 ^ fieldExp V r.2 := by
  intro g hg v hv
  by_cases h : ModulusGood V irrPoly r
  · have e : ownCons V irrPoly r = ownConsOf V irrPoly r h := by unfold ownCons; exact dif_pos h
    rw [e, ownConsOf] at hg
    obtain ⟨g0, -, hg0⟩ := List.mem_map.mp hg
    rw [hv] at hg0
    exact gateMask_const_lt _ _ _ g0 v hg0
  · have e : ownCons V irrPoly r = [] := by unfold ownCons; exact dif_neg h
    rw [e] at hg
    exact absurd hg (List.not_mem_nil)

/-- **Reduced circuit constants:** every serialized constant is below `2^f`, as required
by the field-word encoding of the generator (`lem:generator`). -/
theorem constraintConstantsReduced (irrPoly : ℕ → (ZMod 2)[X]) :
    ConstraintConstantsReduced V irrPoly (ownCons V irrPoly) := by
  intro r _ _ g hg v hv
  rw [ownInst_cons] at hg
  rw [ownInst_f]
  exact ownCons_const_lt V irrPoly r g hg v hv

end NearCubicGates.Adapters.RAMACSP
