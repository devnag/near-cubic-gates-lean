import Proof.Foundations.HierarchySourceContract
import StatementSupport

/-!
# Binding: CLW20 Theorem 1.13 (refuter with an NP oracle) → `RepairSource.HierarchyRefuterSource`

Source PDF: `CLW20_Chen_Lyu_Williams_AE_Circuit_Lower_Bounds_ECCC_TR20-150.pdf`.
Quotations are from the text layer. Its line-broken superscripts are restored as `2^{poly(n)}`,
`1^n` and `{0,1}^n`, and its glyph `6=` is `≠`.

* PDF page 6 (printed p.5), §1.2.1, verbatim:
  "Theorem 1.13 (Refuter with an NP Oracle, Informal). For every time-constructible function T(n)
  such that n ≤ T(n) ≤ 2^{poly(n)}, there is a language L ∈ NTIME[T(n)] and an algorithm R such
  that:
  1. Input. The input to R is a pair (M, 1^n), with the promise that M describes a
  nondeterministic Turing machine running in o(T(n)) time and guessing at most n/10 bits.
  2. Output. For every fixed M and every sufficiently large n, R(M, 1^n) outputs a string
  x ∈ {0,1}^n such that M(x) ≠ L(x).
  3. Complexity. R runs in poly(T(n)) time with adaptive access to an SAT oracle."
* Same page, the classes: "Let NTIMEGUESS[t(n), g(n)] be the class of languages decided by
  nondeterministic algorithms running in O(t(n)) steps and guessing at most g(n) bits. Fortnow
  and Santhanam proved there is a language L in nondeterministic O(T(n)) time that is not
  decidable, even infinitely-often, by nondeterministic o(T(n))-time n/10-guess machines".
* PDF page 19 (printed p.18), §4.1, the model: "We fix a natural enumeration of all (multitape)
  nondeterministic Turing machines. Note that the specific model does not really matter, see the
  discussion in [Wil13], Section 2.1." It also gives the meaning of M(x): "Note that for an M using
  o(T(n)) time and g(n) guesses, we have M(x) = 1 ⇔ ∨_{w∈{0,1}^{g(n)}} V_M(x, T(n), w) = 1."
* FS16 (`FS16_Fortnow_Santhanam_New_Nonuniform_Lower_Bounds.pdf`), PDF page 13:
  "Since we can universally simulate t(n)-time nondeterministic multitape Turing machines on an
  O(t(n))-time 2-tape nondeterministic Turing machine".

## Why Theorem 1.13 and not Theorem 4.6
The formal Theorem 4.6 (PDF p.22) refutes the specific language of Definition 4.2 (PDF p.20).
That definition runs the M-th machine for T(n) of its own steps. PDF p.19 adds "For simplicity, we
assume all machines are random-access machines in the following". So the claim that this language
is in NTIME[T(n)] uses an O(1)-per-step universal random-access simulation. Theorem 1.13 only says
"there is a language L ∈ NTIME[T(n)]". A multitape reading may therefore take L to be a clocked
variant: FS16's universal 2-tape simulation, run for O(T(n)) of its own steps. Each fixed promise
machine runs in o(T(n)), so its simulation completes for all large n, and every guarantee of the
theorem is eventual in n.

## Transcription choices (weakest faithful reading)
* **Tier 1 machine model: the ONE step not checked by the kernel.** "Turing machine", "NTIME" and
  "algorithm R" are read in the repository's multitape model (`Proof/Foundations/LocalBitMultitapeCore.lean`:
  finite control, one-sided binary tapes, one scanned bit, one write and one unit move per tape per
  step). CLW20 p.19 ("the specific model does not really matter") and FS16 p.13 justify this
  reading. Lean does not. Each algorithmic clause is its own definition or conjunct
  (`TimeConstructible`, `InNTIME`, the `OrdinaryOracleRuns` conjunct), so Tier 2 can replace each
  one alone.
* **Quantifier order, as printed.** The order is `∀ T` (time-constructible, in range), `∃ L ∈ NTIME[T]`,
  then `∃ R` with one degree `d`, then `∀ M` under the promise. Next come the coefficient `C` and the
  onset of "sufficiently large n", which may depend on `M`. Last come `∀ n ≥ onset` and `∃ x ∈ {0,1}^n`.
* **"time-constructible"** is not defined in CLW20. The literal uses the standard notion: a machine
  that, given `1^n`, outputs `T(n)` in binary within `O(T(n))` steps. In Lean this is
  `TimeConstructible`: an `OrdinaryWordFunction` from the word `1^n` to `(T n).bits` (binary digits,
  least significant first) within `C·(T n + 1)` steps. The register-program reading
  `SourceInterfaces.TimeConstructible` is not used: the hypothesis is discharged by the import's own
  multitape clock computer `OrdinaryClock.computer`, so the multitape form is the one the import
  supplies.
* **"n ≤ T(n) ≤ 2^{poly(n)}"** becomes `∀ n, n ≤ T n` and `T n ≤ 2^(C·(n+1)^k)` for constants
  `C, k`. Every polynomial bound is of this form.
* **"L ∈ NTIME[T(n)]"** (nondeterministic `O(T(n))` time, p.6) becomes `InNTIME T L`: `L` is the
  language of an `OrdinaryHierarchy T` (`Proof/Foundations/SourceCore.lean`). That is a verifier with a
  framed input tape and a framed witness tape. It halts within `c·(T n + 1)` steps on every witness
  of length `c·(T n + 1)`, and it accepts `x` iff some witness of that length is accepted. `Language`
  is Boolean-valued (`Proof/Foundations/Semantics.lean`).
* **"M describes a nondeterministic Turing machine running in o(T(n)) time and guessing at most
  n/10 bits."** `M` ranges over the import's `OrdinaryWeakMachine` (`Proof/Foundations/SourceCore.lean`).
  That is a verifier with a framed witness of exactly ⌊n/16⌋ bits and a step bound `runtime n` valid
  on every input and every witness. The o(T(n)) promise is `OrdinaryLittleO M T`: for every
  `m > 0`, eventually `m·runtime n ≤ T n`. Since ⌊n/16⌋ ≤ n/10 (`witness_bits_within_promise`), the
  promise class is a SUBCLASS of the printed one. This makes the literal weaker, never stronger.
  `M(x)` has the p.19 meaning: some witness is accepted (`OrdinaryWeakMachine.accepts`).
* **The input (M, 1^n)** is the word `pairInput M n = frame (code M.verifier) ++ frame 1^n`. Here
  `VerifierEncoding.code` (`Proof/Foundations/VerifierEncoding.lean`) lists, in unary, the tape count and
  the state count. It then gives the start state, the halting and accepting flags of every state, and
  one fixed-width record for each (state, scanned-bit mask) pair of the transition table. `code`
  determines everything that `step`, `run` and acceptance read. It omits only the annotation
  `Machine.descriptionBits` and the proof field `twoTapes`, and nothing reads either. So the input word determines the language of `M`:
  two promise machines with the same input word have the same language, and one output refutes both.
  The literal is therefore not made false by an encoding collision. `pairInput` is `rfl`-equal to the
  import's `refuterInput` (`pairInput_eq_refuterInput`).
* **"R … with adaptive access to an SAT oracle"**: `R` is an `OrdinaryOracleProgram`
  (`Proof/Foundations/RecoveryOracleContracts.lean`). It is a deterministic multitape program with query
  states, and its next state depends on the oracle's answer, so access is adaptive. A query costs its
  framed length plus one step. The oracle is `RecoveryOracle.sourceSAT`
  (`Proof/Foundations/RecoverySourceSAT.lean`): satisfiability of explicit 3-CNF formulas in the conventional
  balanced encoding. Reading "SAT" as 3SAT is part of the model reading: the Tseitin reduction makes
  the two interreducible in polynomial time, and a `poly(T(n))` budget absorbs that cost.
* **"R(M, 1^n) outputs a string x ∈ {0,1}^n"**: `R` halts within the budget with `frame x` on its
  output tape (`OrdinaryOracleRuns`).
* **"M(x) ≠ L(x)"** is literally a Boolean inequality, `machineValue M n x ≠ L n x`, where
  `machineValue` is the truth value of `M(x)`.
* **"R runs in poly(T(n)) time"**: at most `C·(T n + 1)^d` steps. The degree `d` belongs to `R`:
  item 3 is a property of the one algorithm `R` and lies outside item 2's "for every fixed M". The
  coefficient `C` may depend on `M`, whose description is part of the input of `R`. The bound is
  claimed only for promise machines and for `n` past the onset. This is the weakest reading.

## What is proved
* `clw20_theorem1_13_to_import`: literal → `HierarchyRefuterSource`. The import's clock gives both
  domain hypotheses (`clock_timeConstructible`, `clock_inClockRange`). The hierarchy is the one
  behind `InNTIME`. The adapter absorbs the per-M coefficient: it uses coefficient 1, degree `d+1` and
  onset `max onset_M C_M`. From `C_M ≤ n` it gets `C_M·(T n + 1)^d ≤ (T n + n + |code M| + 1)^(d+1)`
  (`budget_absorb`). The import's output function chooses an `x` that the literal guarantees.
* `import_iff_on_clocks`: the import is EQUIVALENT to the literal's conclusion restricted to the
  import's clocks (ordinary-computable, polynomially bounded, `T n ≥ n`). So the import narrows only
  the T-domain.
-/

namespace NearCubicWires.Bindings.CLW20Theorem113

open NearCubicWires NearCubicWires.RepairSource NearCubicWires.SourceInterfaces

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option warningAsError true
set_option maxRecDepth 120000

/-! ## Readings, proved -/

/-- The literal input word is the import's refuter input. -/
theorem pairInput_eq_refuterInput (M : OrdinaryWeakMachine) (n : ℕ) :
    pairInput M n = refuterInput M n := rfl

/-- The promise machines guess ⌊n/16⌋ bits, within the printed "at most n/10 bits". -/
theorem witness_bits_within_promise (n : ℕ) : n / 16 ≤ n / 10 :=
  actualWitnessBound n

/-- `M(x) ≠ b` says: `M` accepts `x` exactly when `b` is false. -/
theorem machineValue_ne_iff (M : OrdinaryWeakMachine) (n : ℕ) (x : BitInput n) (b : Bool) :
    machineValue M n x ≠ b ↔ (M.accepts n x ↔ b = false) := by
  classical
  unfold machineValue
  by_cases h : M.accepts n x <;> cases b <;> simp [h]

/-- A language in `NTIME` through the hierarchy `H` is `H`'s semantic decision view. -/
theorem language_eq_timedView {T : ℕ → ℕ} (H : OrdinaryHierarchy T) (L : Language)
    (hL : ∀ n (x : BitInput n), L n x = true ↔ H.verifier.language H.time n x)
    (n : ℕ) (x : BitInput n) : L n x = H.timedView.accepts n x :=
  Bool.eq_iff_iff.mpr ((hL n x).trans (hierarchy_language_exact H n x).symm)

/-- The import's clock is time-constructible in the literal's sense. -/
theorem clock_timeConstructible {T : ℕ → ℕ} (clock : OrdinaryClock T) : TimeConstructible T :=
  ⟨clock.coefficient, clock.coefficientPositive, ⟨clock.computer⟩⟩

/-- The import's clock lies in the literal's range `n ≤ T(n) ≤ 2^{poly(n)}`. -/
theorem clock_inClockRange {T : ℕ → ℕ} (clock : OrdinaryClock T) : InClockRange T := by
  obtain ⟨c, k, -, hb⟩ := clock.polynomial
  exact ⟨clock.atLeastInput, c, k, fun n => (hb n).trans Nat.lt_two_pow_self.le⟩

/-- Past the onset `n ≥ C`, the per-machine coefficient is absorbed by one extra degree of the
import's budget. -/
theorem budget_absorb (C d t n k : ℕ) (hC : C ≤ n) :
    C * (t + 1) ^ d ≤ 1 * (t + n + k + 1) ^ (d + 1) := by
  have h1 : t + 1 ≤ t + n + k + 1 := by omega
  have h2 : C ≤ t + n + k + 1 := by omega
  calc C * (t + 1) ^ d ≤ (t + n + k + 1) * (t + n + k + 1) ^ d :=
        Nat.mul_le_mul h2 (Nat.pow_le_pow_left h1 d)
    _ = 1 * (t + n + k + 1) ^ (d + 1) := by rw [pow_succ]; ring

/-! ## The import's output function, chosen from the literal -/

/-- What the import asks of one output at `(M, n)`: a run of `R` within the import's budget
(coefficient 1, degree `d+1`), and disagreement with the hierarchy. -/
def ImportGood {T : ℕ → ℕ} (H : OrdinaryHierarchy T) (R : OrdinaryOracleProgram) (d : ℕ)
    (M : OrdinaryWeakMachine) (n : ℕ) (x : BitInput n) : Prop :=
  OrdinaryOracleRuns RecoveryOracle.sourceSAT R (refuterInput M n) (List.ofFn x)
      (1 * (T n + n + (VerifierEncoding.code M.verifier).length + 1) ^ (d + 1)) ∧
    (M.accepts n x ↔ H.timedView.accepts n x = false)

/-- A good output when one exists, and the all-false string otherwise. -/
noncomputable def chosenOutput {T : ℕ → ℕ} (H : OrdinaryHierarchy T) (R : OrdinaryOracleProgram)
    (d : ℕ) (M : OrdinaryWeakMachine) (n : ℕ) : BitInput n := by
  classical
  exact if h : ∃ x, ImportGood H R d M n x then Classical.choose h else fun _ => false

theorem chosenOutput_good {T : ℕ → ℕ} (H : OrdinaryHierarchy T) (R : OrdinaryOracleProgram)
    (d : ℕ) (M : OrdinaryWeakMachine) (n : ℕ) (h : ∃ x, ImportGood H R d M n x) :
    ImportGood H R d M n (chosenOutput H R d M n) := by
  unfold chosenOutput
  rw [dif_pos h]
  exact Classical.choose_spec h

/-! ## The adapter and the converse on the import's clocks -/

/-- The literal's conclusion at `T` yields the import's refuter algorithm at `T`. -/
theorem at_to_algorithm {T : ℕ → ℕ} (h : Theorem1_13At T) :
    Nonempty (HierarchyRefuterAlgorithm T) := by
  obtain ⟨L, ⟨H, hL⟩, R, d, refutes⟩ := h
  refine ⟨{ hierarchy := H
            output := chosenOutput H R d
            program := R
            coefficient := 1
            degree := d + 1
            coefficientPositive := Nat.one_pos
            eventual := ?_ }⟩
  intro M hM
  obtain ⟨C, onset, hrun⟩ := refutes M hM
  refine ⟨max onset C, fun n hn => ?_⟩
  obtain ⟨x, hx, hne⟩ := hrun n (by omega)
  refine chosenOutput_good H R d M n
    ⟨x, hx.enlarge (budget_absorb C d (T n) n _ (by omega)), ?_⟩
  rw [← language_eq_timedView H L hL]
  exact (machineValue_ne_iff M n x (L n x)).mp hne

/-- On the import's clocks, the import's algorithm yields the literal's conclusion. -/
theorem algorithm_to_at {T : ℕ → ℕ} (clock : OrdinaryClock T)
    (A : HierarchyRefuterAlgorithm T) : Theorem1_13At T := by
  refine ⟨A.hierarchy.timedView.accepts,
    ⟨A.hierarchy, fun n x => hierarchy_language_exact A.hierarchy n x⟩,
    A.program, A.degree, ?_⟩
  intro M hM
  obtain ⟨onset, hcall⟩ := hierarchy_refuter_call A clock M hM
  refine ⟨A.coefficient * ((VerifierEncoding.code M.verifier).length + 3) ^ A.degree, onset,
    fun n hn => ⟨A.output M n, (hcall n hn).1, ?_⟩⟩
  exact (machineValue_ne_iff M n _ _).mpr (hcall n hn).2

/-- **Adapter.** CLW20 Theorem 1.13 (literal) implies the imported `HierarchyRefuterSource`. -/
theorem clw20_theorem1_13_to_import : CLW20_Theorem1_13 → HierarchyRefuterSource := by
  intro literal T clock
  exact at_to_algorithm (literal T (clock_timeConstructible clock) (clock_inClockRange clock))

/-- The import is exactly the literal's conclusion on the import's clocks: it narrows only the
T-domain (polynomially bounded ordinary clocks with `T n ≥ n`), not the refuter's guarantee. -/
theorem import_iff_on_clocks :
    HierarchyRefuterSource ↔ ∀ T : ℕ → ℕ, OrdinaryClock T → Theorem1_13At T := by
  constructor
  · intro source T clock
    obtain ⟨A⟩ := source T clock
    exact algorithm_to_at clock A
  · intro h T clock
    exact at_to_algorithm (h T clock)

end NearCubicWires.Bindings.CLW20Theorem113
