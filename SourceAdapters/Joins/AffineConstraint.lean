import SourceAdapters.ACSP.Affine

/-!
# Join: the affine constraint instance of Step 1

The reduction of the proof of `thm:short-pcp-ours`, Step 1 ("reduction to an affine constraint instance"), with the
clock supplied as data (`cor:short-pcp-clock` and the paragraph "The exact Lean interface" after it). The instance
is `def:acsp` (`ACSP/Affine.lean`, `Instance`). Consumers: the single-run verifier of Step 2 and the assembly of
Steps 3 and 4. The word function writes `frame (frame x̄ ++ word)`, `x̄` first, the form that `composeFramed`
(`Code/Composition.lean`) consumes.

Paper sentences stated here:
- Step 1: "`V(x,y)` accepts for some `y` of length `T` if and only if the affine constraint instance
  `I_x = I(M_n, τ_n, x̄)` accepts `x̄`; here `|x̄| = 2^m` …"; "Its neighbors are translations, `m_H + 2 ≤ f`, its
  input subspace has dimension `lg |x̄|`, with `1 ≤ lg |x̄| ≤ τ_n < m_H`, and, by `lem:acsp-degree`,
  `f = log T + O(log log T)`, `1 ≤ c_N = O(log T)`."
- `def:acsp`: the instance conditions (`Instance.IsValid`, including the weighted degree bound `4 d_B ≤ 2^f`) and
  acceptance (`Instance.Accepts`). The bound on every composition `B_A` that Step 2 uses is the one-way theorem
  `Instance.degB_of_isValid` (`ACSP/AffineDegree.lean`), not a clause of this join.
- `lem:tm-ram`: "`x̄ = x10^j` be its padding".
- `lem:acsp-degree`: "`2^f = O(T(n) log^3 T(n))`, `f = log T(n) + O(log log T(n))`, `c_N = O(log T(n))`".
- Step 2, "The instance": "`|x̄| = O(n + log T)`".
- `lem:generator`: "outputs `x̄` and the instance `I_x` … in `poly(n, log t)` steps. The description of `I_x` has
  `poly(log t)` bits".
- `cor:short-pcp-clock`: "provided `t` bounds the running time of `V(x,y)` for every witness `y`"; "The
  construction does not test the promise."

`m_H + 2 ≤ f` and `1 ≤ m < m_H` are facts of Step 1, not of `def:acsp`; they are separate conjuncts. `c_N = O(f)`
is the form of `c_N = O(log T)` that Step 3 uses (with `f = log T + O(log log T)`).

**Totality of the generator (not an extra clause).** The word function is total on every clock request, including
`n < 2` and `n > t`, where none of the per-request facts is claimed. The input subspace is chosen by an explicit formula: its basis has a closed form that the generator prints on every
request (for instance `ω` column coordinates, then `m − ω` lane coordinates, with `m − ω` read as truncated
subtraction when `m < ω` outside the promise), so that the program halts within the budget on malformed requests too.
-/

set_option autoImplicit false

noncomputable section

namespace NearCubicGates.Adapters.Joins

open NearCubicWires NearCubicWires.RepairSource NearCubicWires.RepairRepresentation
open NearCubicWires.LocalBitMultitape
open NearCubicGates.Adapters.ACSP.Affine

/-- **The join.** For a fixed verifier `V`: an affine constraint instance (`def:acsp`) and a padded input for every
clock request; on every request with `2 ≤ n ≤ t` the equivalence of Step 1 under the promise of
`cor:short-pcp-clock`, the conditions of `def:acsp`, the facts of Step 1, and the bounds of `lem:acsp-degree`,
Step 2 and `lem:generator`; and the generator of `lem:generator` as one ordinary word function on
`frame x ++ frame (bits t)`, total on every request. -/
def AffineConstraintReduction (V : OrdinaryVerifier) : Prop :=
  ∃ (inst : ClockRequest → Instance) (xbar : ClockRequest → List Bool) (K e : ℕ),
    (∀ r : ClockRequest, 2 ≤ r.1.1 → r.1.1 ≤ r.2 →
      -- `thm:short-pcp-ours`, Step 1, with `cor:short-pcp-clock`: "`V(x,y)` accepts for some `y` of length `T` if
      -- and only if the affine constraint instance `I_x` accepts `x̄`", pointwise in `(x, t)`, under the promise
      (RunsWithin V r.1.2 r.2 →
        ((∃ y : BitInput r.2, V.accepts (List.ofFn r.1.2) (List.ofFn y)) ↔ (inst r).Accepts (xbar r))) ∧
      -- `def:acsp`: `I_x` is an affine constraint instance
      (inst r).IsValid ∧
      -- the paragraph before `def:acsp`, "`F = F₂[X]/(irr)`, the field with `2^f` elements": every mask and
      -- every circuit constant is a reduced field element
      (inst r).WellFormed ∧
      -- `lem:tm-ram`: "`x̄ = x10^j`"
      (∃ j, xbar r = List.ofFn r.1.2 ++ true :: List.replicate j false) ∧
      -- Step 1: "`|x̄| = 2^m`"; "its input subspace has dimension `lg |x̄|`, with `1 ≤ lg |x̄| ≤ τ_n < m_H`"
      (xbar r).length = 2 ^ (inst r).m ∧ 1 ≤ (inst r).m ∧ (inst r).m < (inst r).mH ∧
      -- Step 1: "`m_H + 2 ≤ f`"
      (inst r).mH + 2 ≤ (inst r).f ∧
      -- `lem:acsp-degree`: "`2^f = O(T(n) log^3 T(n))`, `f = log T(n) + O(log log T(n))`, `c_N = O(log T(n))`"
      -- (upper halves, with `t` for `T(n)` and `L = logScale`; `c_N = O(f)`)
      2 ^ (inst r).f ≤ K * r.2 * logScale r.2 ^ e ∧ (inst r).f ≤ K * (logScale r.2 + 1) ∧
      (inst r).cN ≤ K * (inst r).f ∧
      -- Step 2, "The instance": "`|x̄| = O(n + log T)`"
      (xbar r).length ≤ K * (r.1.1 + logScale r.2) ∧
      -- `lem:generator`: "The description of `I_x` has `poly(log t)` bits"
      (inst r).word.length ≤ K * (logScale r.2 + 1) ^ e) ∧
    -- `lem:generator`: "outputs `x̄` and the instance `I_x` … in `poly(n, log t)` steps", given `(x, t)`;
    -- `cor:short-pcp-clock`: "The construction does not test the promise" (total on every request)
    Nonempty (OrdinaryWordFunction ClockRequest ClockRequest.word
      (fun r => frame (frame (xbar r) ++ (inst r).word))
      (fun r => K * (r.1.1 + natBitLength r.2 + 1) ^ e))

end NearCubicGates.Adapters.Joins
