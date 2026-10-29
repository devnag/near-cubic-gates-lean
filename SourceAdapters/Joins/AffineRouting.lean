import SourceAdapters.ACSP.Model
import Mathlib.Data.Nat.Log
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Combinatorics.Hall.Finite

/-!
# The affine routing interface

The layout, translation bank, selectors, routing equations and interpolation
used in `app:affine-embedding`, together with the degree bounds of
`lem:acsp-degree`. The definitions and propositions in this module expose
separate mathematical conclusions for the coordinate polynomials, whole-record
routing, field semantics and explicit circuit construction.
-/
set_option autoImplicit false

noncomputable section

namespace NearCubicGates.Adapters.Routing

open scoped BigOperators
open Polynomial
open NearCubicGates.Adapters.ACSP

/-! Shared finite routing definitions. BitVec is LSB-oriented and has exactly 2^k lanes. -/
abbrev Lane (k : ℕ) := BitVec k

def switchCount (k : ℕ) : ℕ := 2 * k - 1

def dimension (k j : ℕ) : ℕ := min j (2 * k - 2 - j)

def partner (k d : ℕ) (x : Lane k) : Lane k := x ^^^ BitVec.ofNat k (2 ^ d)

abbrev Settings (k : ℕ) := ℕ → Lane k → Bool

def Coherent (k : ℕ) (s : Settings k) : Prop :=
  ∀ j < switchCount k, ∀ x, s j (partner k (dimension k j) x) = s j x

def stageMap (k : ℕ) (s : Settings k) (j : ℕ) (x : Lane k) : Lane k :=
  if s j x then partner k (dimension k j) x else x

def path (k : ℕ) (s : Settings k) (x : Lane k) : Lane k :=
  (List.range (switchCount k)).foldl (fun y j => stageMap k s j y) x

/-- The complete permutation, not merely a set of reachable output lanes. -/
def BenesCompleteness : Prop :=
  ∀ k, 1 ≤ k → ∀ π : Equiv.Perm (Lane k),
    ∃ s : Settings k, Coherent k s ∧ ∀ x, path k s x = π x

/-- One permutation transports arbitrary whole records; repeated record values are permitted. -/
def BenesSoundness : Prop :=
  ∀ k, 1 ≤ k → ∀ s : Settings k, Coherent k s →
    Function.Bijective (path k s) ∧
    ∀ (R : Type) (D : ℕ → Lane k → R),
      (∀ j < switchCount k, ∀ x, D (j + 1) (stageMap k s j x) = D j x) →
      ∀ x, D (switchCount k) (path k s x) = D 0 x

/-! Shared binary layout; C=2^q. The machine specializes q=omega+ceilLog2(32+3K+2L). -/
structure Layout where
  k : ℕ
  ell : ℕ
  q : ℕ
  k_pos : 1 ≤ k
  stages_fit : 2 * k ≤ 2 ^ ell

def Layout.m (l : Layout) : ℕ := l.k + l.ell + l.q + 4

def Layout.C (l : Layout) : ℕ := 2 ^ l.q

def Layout.h (l : Layout) : ℕ := 2 ^ l.m

def cellMask (l : Layout) (x s c r a : ℕ) : ℕ :=
  x + 2 ^ l.k * (s + 2 ^ l.ell * (c + 2 ^ l.q * (r + 8 * a)))

def InRange (l : Layout) (x s c r a : ℕ) : Prop :=
  x < 2 ^ l.k ∧ s < 2 ^ l.ell ∧ c < l.C ∧ r < 8 ∧ a < 2

def eta (l : Layout) (r : ℕ) : ℕ := cellMask l 0 0 0 r 0

def areaMask (l : Layout) : ℕ := cellMask l 0 0 0 0 1

def stageDelta (l : Layout) (j : ℕ) : ℕ :=
  cellMask l 0 j 0 0 0 ^^^ cellMask l 0 (j + 1) 0 0 0

def columnCarry (l : Layout) (t : ℕ) : ℕ :=
  cellMask l 0 0 (2 ^ (t + 1) - 1) 0 0

def laneCarry (t : ℕ) : ℕ := 2 ^ (t + 1) - 1

/-- Fixed explicit list, with duplicates retained. Identity is first. -/
def routingBank (l : Layout) : List ℕ :=
  [0] ++ (List.range (switchCount l.k)).map (stageDelta l) ++
  (List.range (switchCount l.k)).map (fun j => stageDelta l j ^^^ 2 ^ dimension l.k j) ++
  (List.range l.k).map (fun d => 2 ^ d) ++
  [eta l 1, eta l 2, eta l 3 ^^^ eta l 1, eta l 4 ^^^ eta l 1] ++
  (List.range l.k).map (fun d => eta l 4 ^^^ eta l 1 ^^^ 2 ^ d) ++
  (List.range l.q).map (columnCarry l)

/-- All 16C local offsets and precisely two aligned predecessor families. -/
def globalBank (l : Layout) : List ℕ :=
  routingBank l ++
  (List.range (16 * l.C)).map (fun b => 2 ^ (l.k + l.ell) * b) ++
  (List.range l.k).map (fun t => laneCarry t ^^^ eta l 5 ^^^ eta l 1) ++
  (List.range l.k).map (fun t => laneCarry t ^^^ areaMask l ^^^ eta l 6)

variable {F : Type} [Field F] [CharP F 2]

def maskEval (m : ℕ) (e : Fin m → F) (v : ℕ) : F :=
  ∑ b : Fin m, if v.testBit b.val then e b else 0

def cubeEval (m : ℕ) (e : Fin m → F) (v : Fin m → Bool) : F :=
  ∑ b : Fin m, if v b then e b else 0

def label (l : Layout) (e : Fin l.m → F) (x s c r a : ℕ) : F :=
  maskEval l.m e (cellMask l x s c r a)

def InH (m : ℕ) (e : Fin m → F) (z : F) : Prop :=
  ∃ v : Fin m → Bool, cubeEval m e v = z

/-- Independent input data, not a hypothesized affine graph embedding. -/
def Independent (m : ℕ) (e : Fin m → F) : Prop := Function.Injective (cubeEval m e)

def linearized (m : ℕ) (coeff : Fin m → F) : F[X] :=
  ∑ r : Fin m, Polynomial.C (coeff r) * Polynomial.X ^ (2 ^ r.val)

/-- The coordinate coefficient array, with its values on every cube point and
its degree bounds. Ordinary generation of this array is a separate theorem. -/
structure Coordinates (m : ℕ) (e : Fin m → F) where
  coeff : Fin m → Fin m → F
  on_cube : ∀ a v, (linearized m (coeff a)).eval (cubeEval m e v) = if v a then 1 else 0
  degree_le : ∀ a, (linearized m (coeff a)).natDegree ≤ 2 ^ (m - 1)

/-- Coordinate existence and interpolation are separate from routing and machine equations. -/
def CoordinateExistence : Prop :=
  ∀ m, 1 ≤ m → ∀ e : Fin m → F, Independent m e → Nonempty (Coordinates m e)

def TableInterpolation : Prop :=
  ∀ m (e : Fin m → F), Independent m e → ∀ a : F → F,
    ∃ A : F[X], A.degree < (2 ^ m : ℕ) ∧ ∀ z, InH m e z → A.eval z = a z

/-! Formal normalized selectors and explicit routing polynomial.
Variable none is X; some b is A(X+maskEval e b). Assembly reindexes b into globalBank.
This keyed form prevents a hidden choice of a different polynomial or neighbor bank. -/
abbrev Vars := Option ℕ
abbrev MP (F : Type) [CommSemiring F] := MvPolynomial Vars F
abbrev Pattern (m : ℕ) := Fin m → Option Bool

def patternMasks (m known value : ℕ) : Pattern m :=
  fun a => if known.testBit a.val then some (value.testBit a.val) else none

def patternHolds {m : ℕ} (p : Pattern m) (v : Fin m → Bool) : Prop :=
  ∀ a b, p a = some b → v a = b

def liftX (p : F[X]) : MP F := Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X none) p

def selector {m : ℕ} {e : Fin m → F} (coords : Coordinates m e) (p : Pattern m) : MP F :=
  ∏ a : Fin m, match p a with
    | none => 1
    | some true => liftX (linearized m (coords.coeff a))
    | some false => 1 + liftX (linearized m (coords.coeff a))

def Y (b : ℕ) : MP F := MvPolynomial.X (some b)

def routePattern (l : Layout) (j role colKnown colValue : ℕ) : Pattern l.m :=
  patternMasks l.m
    (cellMask l 0 (2 ^ l.ell - 1) colKnown 7 1)
    (cellMask l 0 j colValue role 0)

structure Term (m : ℕ) (F : Type) [Field F] where
  guard : Pattern m
  equation : MP F

/-- Small equation syntax; powers are explicit squares and are compiled with sharing. -/
inductive Expr (F : Type) where
  | const (c : F)
  | read (v : Vars)
  | add (a b : Expr F)
  | mul (a b : Expr F)
  | square (a : Expr F)

def Expr.poly : Expr F → MP F
  | .const c => MvPolynomial.C c
  | .read v => MvPolynomial.X v
  | .add a b => a.poly + b.poly
  | .mul a b => a.poly * b.poly
  | .square a => a.poly ^ 2

inductive RoutingItem where
  | route (j : ℕ)
  | switchBit (j : ℕ)
  | pair (j : ℕ)
  | column (j t : ℕ)
  | dataBit (j : ℕ)

def routingItems (l : Layout) : List RoutingItem :=
  (List.range (switchCount l.k)).flatMap (fun j =>
    [.route j, .switchBit j, .pair j] ++ (List.range l.q).map (.column j)) ++
  (List.range (2 * l.k)).map .dataBit

def RoutingItem.guard (l : Layout) : RoutingItem → Pattern l.m
  | .route j => routePattern l j 0 0 0
  | .switchBit j => routePattern l j 3 0 0
  | .pair j => routePattern l j 4 0 0
  | .column j t => routePattern l j 1
      (if t + 1 < l.q then 2 ^ (t + 1) - 1 else 2 ^ t - 1) (2 ^ t - 1)
  | .dataBit j => routePattern l j 2 0 0

def RoutingItem.expr (l : Layout) : RoutingItem → Expr F
  | .route j => .add (.add (.read (some 0)) (.read (some (stageDelta l j))))
      (.mul (.read (some (eta l 1)))
        (.add (.read (some (stageDelta l j)))
          (.read (some (stageDelta l j ^^^ 2 ^ dimension l.k j)))))
  | .switchBit _ => .add (.square (.read (some (eta l 3 ^^^ eta l 1))))
      (.read (some (eta l 3 ^^^ eta l 1)))
  | .pair j => .add (.read (some (eta l 4 ^^^ eta l 1)))
      (.read (some (eta l 4 ^^^ eta l 1 ^^^ 2 ^ dimension l.k j)))
  | .column _ t => .add (.read (some 0)) (.read (some (columnCarry l t)))
  | .dataBit _ => .add (.square (.read (some (eta l 2)))) (.read (some (eta l 2)))

def routingTerms (l : Layout) : List (Term l.m F) :=
  (routingItems l).map fun t => ⟨t.guard l, (t.expr l).poly⟩

def emit {m : ℕ} {e : Fin m → F} (coords : Coordinates m e) (ts : List (Term m F)) : MP F :=
  (ts.map fun t => selector coords t.guard * t.equation).sum

def evaluate (l : Layout) (e : Fin l.m → F) (a : F → F) (z : F) (p : MP F) : F :=
  MvPolynomial.eval (fun v => match v with
    | none => z
    | some b => a (z + maskEval l.m e b)) p

def weight (m : ℕ) : Vars → ℕ
  | none => 1
  | some _ => 2 ^ m - 1

/-- No simultaneous-error cancellation: guards are a pointwise disjoint family. -/
def DisjointTerms {m : ℕ} (ts : List (Term m F)) : Prop :=
  ∀ i j : Fin ts.length, i ≠ j → ∀ v, ¬ (patternHolds ts[i].guard v ∧ patternHolds ts[j].guard v)

/-- General compiler lemma assembly uses for its own explicit machine catalog as well as routing.
It is not an assertion that the RAM catalog is correct or disjoint. -/
def NormalizedEmission : Prop :=
  ∀ m, 1 ≤ m → ∀ (e : Fin m → F) (coords : Coordinates m e) (ts : List (Term m F)),
    DisjointTerms ts →
    (∀ t ∈ ts, MvPolynomial.weightedTotalDegree (weight m) t.equation ≤ 2 * (2 ^ m - 1)) →
    (MvPolynomial.weightedTotalDegree (weight m) (emit coords ts) ≤
      m * 2 ^ (m - 1) + 2 * (2 ^ m - 1)) ∧
    (∀ v (reads : Vars → F), reads none = cubeEval m e v →
      (MvPolynomial.eval reads (emit coords ts) = 0 ↔
        ∀ t ∈ ts, patternHolds t.guard v → MvPolynomial.eval reads t.equation = 0))

/-! Local field semantics: five independent equation families, including both coherence conditions. -/
def dataValue (l : Layout) (e : Fin l.m → F) (a : F → F) (j : ℕ)
    (x : Lane l.k) (c : Fin l.C) : F := label l e x.toNat j c.val 0 0 |> a

def switchValue (l : Layout) (e : Fin l.m → F) (a : F → F) (j : ℕ)
    (x : Lane l.k) (c : Fin l.C) : F := label l e x.toNat j c.val 1 0 |> a

def IsBit (z : F) : Prop := z = 0 ∨ z = 1

def LocalRouting (l : Layout) (e : Fin l.m → F) (a : F → F) : Prop :=
  (∀ j < 2 * l.k, ∀ x c, IsBit (dataValue l e a j x c)) ∧
  (∀ j < switchCount l.k, ∀ x c, IsBit (switchValue l e a j x c)) ∧
  (∀ j < switchCount l.k, ∀ x c c', switchValue l e a j x c = switchValue l e a j x c') ∧
  (∀ j < switchCount l.k, ∀ x c,
    switchValue l e a j (partner l.k (dimension l.k j) x) c = switchValue l e a j x c) ∧
  (∀ j < switchCount l.k, ∀ x c,
    dataValue l e a j x c + dataValue l e a (j + 1) x c + switchValue l e a j x c *
      (dataValue l e a (j + 1) x c +
        dataValue l e a (j + 1) (partner l.k (dimension l.k j) x) c) = 0)

/-- The only points the routing completion may overwrite; check hosts are not stored data. -/
def RoutingWritable (l : Layout) (e : Fin l.m → F) (z : F) : Prop :=
  (∃ j < 2 * l.k, ∃ x : Lane l.k, ∃ c : Fin l.C, z = label l e x.toNat j c.val 0 0) ∨
  (∃ j < switchCount l.k, ∃ x : Lane l.k, ∃ c : Fin l.C, z = label l e x.toNat j c.val 1 0)

/-- Fixed polynomial ↔ local equations, for every table, not just honest assignments. -/
def RoutingPolynomialCorrect (l : Layout) (e : Fin l.m → F) (coords : Coordinates l.m e) : Prop :=
  ∀ a : F → F,
    (∀ z, InH l.m e z → evaluate l e a z (emit coords (routingTerms l)) = 0) ↔ LocalRouting l e a

/-- Soundness produces ONE permutation for all payload columns, without distinctness assumptions. -/
def FieldRoutingSoundness (l : Layout) (e : Fin l.m → F) : Prop :=
  ∀ a : F → F, LocalRouting l e a → ∃ π : Equiv.Perm (Lane l.k),
    ∀ x c, dataValue l e a (switchCount l.k) (π x) c = dataValue l e a 0 x c

/-- Completeness preserves the entire machine area and every other non-routing-data point.
Assembly supplies its ET endpoints and arbitrary machine table, then interpolates once. -/
def FieldRoutingCompletion (l : Layout) (e : Fin l.m → F) : Prop :=
  ∀ U V : Lane l.k → Fin l.C → F,
    (∀ x c, IsBit (U x c)) → (∀ x c, IsBit (V x c)) →
    (∃ π : Equiv.Perm (Lane l.k), ∀ x c, V (π x) c = U x c) →
    ∀ background : F → F, ∃ a : F → F,
      LocalRouting l e a ∧
      (∀ x c, dataValue l e a 0 x c = U x c) ∧
      (∀ x c, dataValue l e a (switchCount l.k) x c = V x c) ∧
      (∀ z, ¬ RoutingWritable l e z → a z = background z)

/-! Exact layout and resource conditions. Every translation has literal slope one. -/
def LayoutCorrect (l : Layout) (e : Fin l.m → F) : Prop :=
  (∀ x s c r a, InRange l x s c r a → cellMask l x s c r a < l.h) ∧
  (∀ x s c r a x' s' c' r' a', InRange l x s c r a → InRange l x' s' c' r' a' →
    (label l e x s c r a = label l e x' s' c' r' a' ↔
      x = x' ∧ s = s' ∧ c = c' ∧ r = r' ∧ a = a')) ∧
  (∀ u v, u < l.h → v < l.h → maskEval l.m e (u ^^^ v) = maskEval l.m e u + maskEval l.m e v) ∧
  (globalBank l).length = 8 * l.k + l.q + 16 * l.C + 3 ∧
  0 ∈ globalBank l ∧
  (∀ b ∈ globalBank l, b < l.h ∧ ∀ z, InH l.m e z → InH l.m e (z + maskEval l.m e b)) ∧
  l.h = 16 * 2 ^ l.k * 2 ^ l.ell * l.C

/-- No missing affine access is supplied through an arbitrary neighbor oracle. -/
def AccessCoverage (l : Layout) : Prop :=
  (∀ j < switchCount l.k, stageDelta l j ∈ globalBank l ∧
    (stageDelta l j ^^^ 2 ^ dimension l.k j) ∈ globalBank l) ∧
  (∀ c < l.C, ∀ r < 8, ∀ a < 2, cellMask l 0 0 c r a ∈ globalBank l) ∧
  (∀ t < l.k, (laneCarry t ^^^ eta l 5 ^^^ eta l 1) ∈ globalBank l ∧
    (laneCarry t ^^^ areaMask l ^^^ eta l 6) ∈ globalBank l)

def DegreeBudget (m : ℕ) : ℕ := (m + 4) * 2 ^ m

def fieldExponent (m : ℕ) : ℕ := m + Nat.clog 2 (4 * (m + 4))

/-- Exact direct-input basis, in the LSB order used by ACSP.indexedElt. -/
def inputBasis (l : Layout) (e : Fin l.m → F) (omega j : ℕ) : F :=
  maskEval l.m e (2 ^ (if j < omega then l.k + l.ell + j else j - omega))

def inputPoint (l : Layout) (e : Fin l.m → F) (omega m i : ℕ) : F :=
  maskEval l.m e (2 ^ (l.k - 1)) +
    ∑ j : Fin m, if i.testBit j.val then inputBasis l e omega j.val else 0

def InputEmbedding (l : Layout) (e : Fin l.m → F) : Prop :=
  ∀ omega m, omega ≤ l.q → omega ≤ m → m - omega ≤ l.k - 1 →
    (∀ i < 2 ^ m, inputPoint l e omega m i =
      label l e (2 ^ (l.k - 1) + i / 2 ^ omega) 0 (i % 2 ^ omega) 0 0) ∧
    Function.Injective (fun v : Fin m → Bool =>
      maskEval l.m e (2 ^ (l.k - 1)) +
        ∑ j : Fin m, if v j then inputBasis l e omega j.val else 0) ∧
    (∀ i < 2 ^ m, InH l.m e (inputPoint l e omega m i))

def ColumnCase (q t c : ℕ) : Prop :=
  t < q ∧ c % 2 ^ t = 2 ^ t - 1 ∧ (t + 1 < q → c.testBit t = false)

/-- Exact landings, rather than an arbitrary graph-affine realization premise. -/
def TranslationLanding (l : Layout) (e : Fin l.m → F) : Prop :=
  (∀ x s c r a c' r' a', InRange l x s c r a → InRange l x s c' r' a' →
    label l e x s c r a + maskEval l.m e (cellMask l 0 0 (c ^^^ c') (r ^^^ r') (a ^^^ a')) =
      label l e x s c' r' a') ∧
  (∀ j < switchCount l.k, ∀ x : Lane l.k, ∀ c < l.C, ∀ r < 8, ∀ a < 2,
    label l e x.toNat j c r a + maskEval l.m e (stageDelta l j) = label l e x.toNat (j + 1) c r a ∧
    label l e x.toNat j c r a + maskEval l.m e (stageDelta l j ^^^ 2 ^ dimension l.k j) =
      label l e (partner l.k (dimension l.k j) x).toNat (j + 1) c r a) ∧
  (∀ x s c r a t, InRange l x s c r a → ColumnCase l.q t c →
    label l e x s c r a + maskEval l.m e (columnCarry l t) =
      label l e x s ((c + 1) % l.C) r a) ∧
  (∀ x s c r a t r' a', InRange l x s c r a → r' < 8 → a' < 2 →
    t < l.k → x % 2 ^ (t + 1) = 2 ^ t →
    label l e x s c r a +
      maskEval l.m e (laneCarry t ^^^ eta l (r ^^^ r') ^^^ cellMask l 0 0 0 0 (a ^^^ a')) =
      label l e (x - 1) s c r' a')

/-! Actual finite straight-line circuit constructor. Its proof and paid serialization are separate.
The builder shares the m Frobenius powers and the m coordinate outputs. It enumerates only routingItems,
coordinates, and the bank, never the 2^m-point domain or a witness permutation. -/
abbrev Builder (F : Type) := StateM (List (ArithGate F))

def pushGate (g : ArithGate F) : Builder F ℕ := do
  let gates ← get
  set (gates ++ [g])
  return gates.length

def readIndex (l : Layout) : Vars → ℕ
  | none => 0
  | some b => 1 + (globalBank l).idxOf b

def compileExpr (l : Layout) : Expr F → Builder F ℕ
  | .const c => pushGate (.const c)
  | .read v => pushGate (.input (readIndex l v))
  | .add a b => do
      let ia ← compileExpr l a
      let ib ← compileExpr l b
      pushGate (.add ia ib)
  | .mul a b => do
      let ia ← compileExpr l a
      let ib ← compileExpr l b
      pushGate (.mul ia ib)
  | .square a => do
      let ia ← compileExpr l a
      pushGate (.mul ia ia)

def compileCoordinates {m : ℕ} {e : Fin m → F} (coords : Coordinates m e) : Builder F (List ℕ) := do
  let x ← pushGate (.input 0)
  let mut powers := [x]
  for _ in List.range (m - 1) do
    let prev := powers.getLastD x
    let next ← pushGate (.mul prev prev)
    powers := powers ++ [next]
  let mut outputs := []
  for a in List.finRange m do
    let mut acc ← pushGate (.const 0)
    for r in List.finRange m do
      let c ← pushGate (.const (coords.coeff a r))
      let term ← pushGate (.mul c (powers.getD r.val x))
      acc ← pushGate (.add acc term)
    outputs := outputs ++ [acc]
  return outputs

def compilePattern {m : ℕ} (coordIndices : List ℕ) (p : Pattern m) : Builder F ℕ := do
  let one ← pushGate (.const 1)
  let mut acc := one
  for a in List.finRange m do
    match p a with
    | none => pure ()
    | some b =>
        let coord := coordIndices.getD a.val one
        let factor ← if b then pure coord else pushGate (.add one coord)
        acc ← pushGate (.mul acc factor)
  return acc

def compileRouting (l : Layout) (e : Fin l.m → F) (coords : Coordinates l.m e) : ArithCircuit F :=
  ⟨((do
    let coordIndices ← compileCoordinates coords
    let mut acc ← pushGate (.const 0)
    for t in routingItems l do
      let guard ← compilePattern coordIndices (t.guard l)
      let equation ← compileExpr l (t.expr l)
      let term ← pushGate (.mul guard equation)
      acc ← pushGate (.add acc term)
    return acc : Builder F ℕ).run []).2⟩

def WellFormedCircuit (arity : ℕ) (c : ArithCircuit F) : Prop :=
  ∀ i : Fin c.gates.length, match c.gates[i] with
    | .input v => v < arity
    | .const _ => True
    | .add a b | .mul a b => a < i.val ∧ b < i.val

/-- Exact variable encoding; valid read masks have their bank index, default variables are irrelevant.
`min` makes this total without silently assuming a support-membership lemma. -/
def encodeVar (l : Layout) (v : Vars) : Fin ((globalBank l).length + 1) :=
  ⟨min (readIndex l v) (globalBank l).length, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩

def circuitBound (l : Layout) : ℕ :=
  8 * (l.m + 1) ^ 2 + (2 * l.m + 20) * (routingItems l).length + 2

/-- The actual constructor's polynomial, valid back-references, support, and polynomial size.
No ordinary-machine witness or target serialization is supplied by this mathematical contract. -/
def CircuitCorrect (l : Layout) (e : Fin l.m → F) (coords : Coordinates l.m e) : Prop :=
  (∀ v ∈ (emit coords (routingTerms l)).vars, ∀ b, v = some b → b ∈ globalBank l) ∧
  WellFormedCircuit ((globalBank l).length + 1) (compileRouting l e coords) ∧
  (compileRouting l e coords).poly ((globalBank l).length + 1) =
    MvPolynomial.rename (encodeVar l) (emit coords (routingTerms l)) ∧
  (compileRouting l e coords).size ≤ circuitBound l ∧
  (routingItems l).length ≤ 2 * l.k * (l.q + 4)

/-- Numerical conclusions consumed by J2/J4/J5; no ACSP reduction premise occurs. -/
def ResourceArithmetic : Prop :=
  ∀ m, 1 ≤ m →
    m * 2 ^ (m - 1) + 2 * (2 ^ m - 1) ≤ DegreeBudget m ∧
    m + 2 ≤ fieldExponent m ∧
    4 * DegreeBudget m ≤ 2 ^ fieldExponent m ∧
    2 ^ fieldExponent m < 8 * (m + 4) * 2 ^ m

/-- The generic routing conclusions, with separate coordinate, interpolation,
field-semantics and circuit fields. The RAM event-trace embedding is proved
using this interface, rather than assumed by it. -/
structure Contract : Prop where
  benes_complete : BenesCompleteness
  benes_sound : BenesSoundness
  coordinates : CoordinateExistence (F := F)
  interpolation : TableInterpolation (F := F)
  normalized_emission : NormalizedEmission (F := F)
  resource_arithmetic : ResourceArithmetic
  layout : ∀ l (e : Fin l.m → F), Independent l.m e → LayoutCorrect l e
  access : ∀ l, AccessCoverage l
  translations : ∀ l (e : Fin l.m → F), Independent l.m e → TranslationLanding l e
  input : ∀ l (e : Fin l.m → F), Independent l.m e → InputEmbedding l e
  circuit : ∀ l (e : Fin l.m → F), Independent l.m e →
    ∀ coords : Coordinates l.m e, CircuitCorrect l e coords
  routing_degree : ∀ l (e : Fin l.m → F), Independent l.m e →
    ∀ coords : Coordinates l.m e,
      MvPolynomial.weightedTotalDegree (weight l.m) (emit coords (routingTerms l)) ≤
        l.m * 2 ^ (l.m - 1) + 2 * (l.h - 1)
  polynomial : ∀ l (e : Fin l.m → F), Independent l.m e →
    ∀ coords : Coordinates l.m e, RoutingPolynomialCorrect l e coords
  soundness : ∀ l (e : Fin l.m → F), Independent l.m e → FieldRoutingSoundness l e
  completion : ∀ l (e : Fin l.m → F), Independent l.m e → FieldRoutingCompletion l e

end NearCubicGates.Adapters.Routing

namespace NearCubicGates.Adapters.Joins

/-- Public proposition shape. Assembly specializes F to ACSP.Field2 irr after installing
the irreducibility instance. The mathematical suppliers are assembled separately from this interface. -/
def AffineRouting : Prop := ∀ (F : Type) [Field F] [CharP F 2], Routing.Contract (F := F)

end NearCubicGates.Adapters.Joins

end
