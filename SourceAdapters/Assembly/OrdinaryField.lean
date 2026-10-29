import NineInputs

/-!
# Input 6 in the ordinary machine model: the statement

`OrdinaryOracleCircuitPCP` is the short-PCP input (`MW20_OracleCircuitPCP_TM2`) with its algorithm `A` an ordinary
polynomial-time word function (`OrdinaryPolyTime`) instead of a Mathlib TM2 machine: for every verifier `V` and
time bound `T`, an output map, the binary clock `T(n)` read with `x`, and the four printed properties, unchanged.
Both definitions are word for word those of the same names in `NearCubicWires.Bindings.MW20`, where
`OrdinaryOracleCircuitPCP` is the type of the `shortPCP` field of `NineInputs`; the adapter of input 6
(`Assembly.field6Ordinary`) is stated with the copies here, which are the same definitions.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Assembly

open NearCubicWires NearCubicWires.CanonicalBinary NearCubicWires.ExecutableInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairRepresentation NearCubicWires.LocalBitMultitape
open NearCubicWires.Bindings.MW20

/-- A polynomial-time ordinary word function from `input` to `output`: an ordinary program that, started on
`frame (input a)`, writes `output a` within `K · (|input a| + 1)^e` steps. -/
def OrdinaryPolyTime {A : Type} (input output : A → List Bool) : Prop :=
  ∃ K e : ℕ, Nonempty (NearCubicWires.RepairOrdinary.WordFunction A input output
    (fun a => K * ((input a).length + 1) ^ e))

/-- Input 6 in the ordinary machine model (`app:short-pcp-proof`, "The exact Lean interface", with the algorithm an ordinary word function). -/
def OrdinaryOracleCircuitPCP : Prop :=
  ∀ (V : OrdinaryVerifier) (T : ℕ → ℕ), (∀ n, n ≤ T n) → RunsInTime V T →
  ∃ out : InputRequest → OracleOutput,
    -- "an algorithm A running in poly(n, log T(n)) time which, given x ∈ {0,1}^n, outputs an oracle
    -- circuit C^O_x"
    OrdinaryPolyTime
      (fun x : InputRequest => frame (List.ofFn x.2) ++ frame (T x.1).bits)
      (fun x => (out x).word) ∧
    -- "ℓ = log2(T(n)) + O(log log T(n)) inputs"
    (∃ K e : ℕ, ∀ x : InputRequest, 1 ≤ x.1 →
      2 ^ (out x).ell ≤ K * T x.1 * logScale (T x.1) ^ e) ∧
    -- "poly(n, log T(n)) size"
    (∃ K e : ℕ, ∀ x : InputRequest, 1 ≤ x.1 →
      (out x).circuit.size ≤ K * (x.1 + natBitLength (T x.1) + 1) ^ e) ∧
    -- "If there is a y of length T(n) such that V(x, y) accepts, then there is an oracle
    -- O : {0,1}^ℓ → {0,1} such that C^O_x is unsatisfiable."
    (∀ x : InputRequest, 1 ≤ x.1 →
      (∃ y : BitInput (T x.1), V.accepts (List.ofFn x.2) (List.ofFn y)) →
      ∃ O : BitInput (out x).ell → Bool, ∀ z, (out x).circuit.eval O z = false) ∧
    -- "If V(x, y) rejects on all y of length T(n), then for every oracle O : {0,1}^ℓ → {0,1}, C^O_x has
    -- at least 2^ℓ · (1 − 1/n) satisfying assignments."
    (∀ x : InputRequest, 1 ≤ x.1 →
      (¬ ∃ y : BitInput (T x.1), V.accepts (List.ofFn x.2) (List.ofFn y)) →
      ∀ O : BitInput (out x).ell → Bool,
        (2 : ℝ) ^ (out x).ell * (1 - 1 / (x.1 : ℝ)) ≤ ((out x).satCount O : ℝ))

end NearCubicGates.Adapters.Assembly
