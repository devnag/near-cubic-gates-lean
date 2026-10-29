import SourceAdapters.ShortPCP.Machines.OracleStages
import SourceAdapters.Joins.SingleRunTime
import StatementChecks.ENPDeterminism
import Proof.MachineModel.OrdinarySignedSortKey

/-!
# Single-run time from three stage interfaces

The runtime interface of `app:short-pcp-proof` requires one oracle program taking
`frame data ++ frame R` to the verifier's verdict within `K·(|data| + |R| + 1)^e` steps.
The implementation composes four stages (`compose4_runs`). A cell program needs fresh work
streams, and the field degree is bounded using the serialized modulus and data length, so
an ordinary prefix stage first supplies the cell width. The verifier is non-adaptive
(`thm:short-pcp-ours`, Steps 2–4); its oracle reads can be placed between two ordinary stages.

1. `PrefixStage` writes `prefixWord w = 1^(size |w|) 0 ++ w`.
2. The query half of `CellStages` writes `readerWord s L xs (q.input R)`, with
   every proof-bit address in `xs` below `2^L`.
3. `ReaderStage` asks each address once as `frame (binary L a)` and writes its
   answer into the corresponding entry of `readWord`.
4. The decision half of `CellStages` computes the verdict from those answers.

`singleRunTime_of_stages` supplies the runtime interface from `PrefixStage`,
`ReaderStage` and `CellStages`. All four stages and their composition overhead are charged.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.ShortPCP.Time

open NearCubicWires NearCubicWires.RepairSource NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicGates.Adapters.Joins NearCubicGates.Adapters.Joins.SingleRun NearCubicGates.Adapters.ShortPCP.Machines

/-- The width prefix: `1^s 0 ++ w` with `s = size |w|`, so `2^s > |w|` (the cell width `Sz.W s = 2^(c1·s)·a1`). -/
def prefixWord (w : List Bool) : List Bool := List.replicate (Nat.size w.length) true ++ false :: w

/-- The reader's input: `1^s 0`, then for each address `a` the entry `1 U P V ++ frame (binary L a)` with
`U P V = 1 0 0` (not yet asked), then `0`, then `rest`. -/
def readerWord (s L : ℕ) (xs : List ℕ) (rest : List Bool) : List Bool :=
  List.replicate s true ++ false ::
    ((xs.flatMap fun a => true :: true :: false :: false :: RepairOrdinary.frame (binary L a)) ++ false :: rest)

/-- The reader's word after the reads: entry `i` is `1 0 0 bᵢ ++ frame (binary L aᵢ)`, `bᵢ` the answer. -/
def readWord (s L : ℕ) (xs : List ℕ) (ans : List Bool) (rest : List Bool) : List Bool :=
  List.replicate s true ++ false ::
    ((List.zipWith (fun a b => true :: false :: false :: b :: RepairOrdinary.frame (binary L a)) xs ans).flatten ++
      false :: rest)

/-- **Stage 1 (ordinary).** The width prefix, in polynomial time. -/
def PrefixStage : Prop :=
  ∃ (p : OrdinaryOracleProgram) (K e : ℕ), ∀ (o : ℕ → Bool) (w : List Bool),
    OrdinaryOracleRuns o p w (prefixWord w) (K * (w.length + 1) ^ e)

/-- **Stage 3 (oracle, generic).** Every address of the reader word is asked once, in order, as `frame (binary L a)`;
the output is the read word, each answer in its entry (proof of `thm:short-pcp-ours`). -/
def ReaderStage : Prop :=
  ∃ (p : OrdinaryOracleProgram) (K e : ℕ), ∀ (o : ℕ → Bool) (s L : ℕ) (xs : List ℕ) (rest : List Bool),
    (∀ a ∈ xs, a < 2 ^ L) →
    OrdinaryOracleRuns o p (readerWord s L xs rest) (readWord s L xs (xs.map o) rest)
      (K * ((readerWord s L xs rest).length + 1) ^ e)

/-- **Stages 2 and 4 (ordinary, cell language over `FieldCells`).** For every valid request: the query half writes
the address list of `V1` on coins `R` (proof of `thm:short-pcp-ours`), the decision half outputs the patched verdict from the
answers (proof of `thm:short-pcp-ours`), both within `K·(|data| + |R| + 1)^e`, and the reader word is that long at
most. -/
def CellStages : Prop :=
  ∃ (p2 p4 : OrdinaryOracleProgram) (L : Request → List Bool → ℕ) (xs : Request → List Bool → List ℕ) (K e : ℕ),
    ∀ q : Request, q.Valid → ∀ R : List Bool,
      (∀ a ∈ xs q R, a < 2 ^ L q R) ∧
      (readerWord (Nat.size (q.input R).length) (L q R) (xs q R) (q.input R)).length ≤
        K * (q.data.length + R.length + 1) ^ e ∧
      (∀ o : ℕ → Bool, OrdinaryOracleRuns o p2 (prefixWord (q.input R))
        (readerWord (Nat.size (q.input R).length) (L q R) (xs q R) (q.input R)) (K * (q.data.length + R.length + 1) ^ e)) ∧
      ∀ (F : Type) [Field F] [DecidableEq F] (φ : AdjoinRoot (WireExponent3_5.GF.toPoly q.code.irr) →+* F),
        Function.Bijective φ → ∀ o : ℕ → Bool,
          OrdinaryOracleRuns o p4
            (readWord (Nat.size (q.input R).length) (L q R) (xs q R) ((xs q R).map o) (q.input R))
            [q.patchedVerdict φ (q.decode φ o) R] (K * (q.data.length + R.length + 1) ^ e)

theorem input_length_le (q : Request) (R : List Bool) :
    (q.input R).length + 1 ≤ 3 * (q.data.length + R.length + 1) := by
  have h : ∀ u : List Bool, (RepairOrdinary.frame u).length = 2 * u.length + 1 := by
    intro u; induction u with
    | nil => rfl
    | cons b u ih => simp [RepairOrdinary.frame, ih]; ring
  simp only [Request.input, List.length_append, h]; omega

theorem runs_mono {o : ℕ → Bool} {p : OrdinaryOracleProgram} {i out : List Bool} {b b' : ℕ}
    (h : OrdinaryOracleRuns o p i out b) (hb : b ≤ b') : OrdinaryOracleRuns o p i out b' := by
  obtain ⟨c, f, hc, rest⟩ := h
  exact ⟨c, f, hc.trans hb, rest⟩

/-- **The join from the three stages.** -/
theorem singleRunTime_of_stages (h1 : PrefixStage) (h3 : ReaderStage) (hc : CellStages) : SingleRunTime := by
  obtain ⟨p1, K1, e1, r1⟩ := h1
  obtain ⟨p3, K3, e3, r3⟩ := h3
  obtain ⟨p2, p4, L, xs, K, e, rc⟩ := hc
  -- the exponent and the constant
  refine ⟨OrdinaryOracleCompose.compose (OrdinaryOracleCompose.compose (OrdinaryOracleCompose.compose p1 p2) p3) p4,
    16 * (16 * (16 * (K1 * 3 ^ e1 + K + 1) + K3 * (K + 1) ^ e3 + 1) + K + 1), e1 + e + e * e3 + 1, ?_⟩
  intro q hq F _ _ φ hφ o R
  obtain ⟨hxs, hlen, hQ, hD⟩ := rc q hq R
  set n := q.data.length + R.length + 1 with hn
  have hn1 : 1 ≤ n := by omega
  have hrun := compose4_runs (r1 o (q.input R)) (hQ o)
    (r3 o (Nat.size (q.input R).length) (L q R) (xs q R) (q.input R) hxs) (hD F φ hφ o)
  refine ⟨runs_mono hrun ?_, fun out budget hout =>
    NearCubicGates.StatementChecks.ENPDeterminism.oracleRuns_output_unique hout hrun⟩
  -- the budget
  set E := e1 + e + e * e3 + 1
  have hE : ∀ k, k ≤ E → n ^ k ≤ n ^ E := fun k hk => Nat.pow_le_pow_right hn1 hk
  have hnE : 1 ≤ n ^ E := Nat.one_le_pow _ _ hn1
  have b1 : K1 * ((q.input R).length + 1) ^ e1 ≤ K1 * 3 ^ e1 * n ^ E := by
    calc K1 * ((q.input R).length + 1) ^ e1 ≤ K1 * (3 * n) ^ e1 :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (input_length_le q R) _)
      _ = K1 * 3 ^ e1 * n ^ e1 := by rw [mul_pow, mul_assoc]
      _ ≤ K1 * 3 ^ e1 * n ^ E := Nat.mul_le_mul_left _ (hE _ (by omega))
  have b2 : K * n ^ e ≤ K * n ^ E := Nat.mul_le_mul_left _ (hE _ (by omega))
  have b3 : K3 * ((readerWord (Nat.size (q.input R).length) (L q R) (xs q R) (q.input R)).length + 1) ^ e3 ≤
      K3 * (K + 1) ^ e3 * n ^ E := by
    have h1 : (readerWord (Nat.size (q.input R).length) (L q R) (xs q R) (q.input R)).length + 1 ≤
        (K + 1) * n ^ e := by
      have := Nat.one_le_pow e n hn1; nlinarith
    calc K3 * ((readerWord (Nat.size (q.input R).length) (L q R) (xs q R) (q.input R)).length + 1) ^ e3
        ≤ K3 * ((K + 1) * n ^ e) ^ e3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 _)
      _ = K3 * (K + 1) ^ e3 * n ^ (e * e3) := by rw [mul_pow, ← pow_mul, mul_assoc]
      _ ≤ K3 * (K + 1) ^ e3 * n ^ E := Nat.mul_le_mul_left _ (hE _ (by omega))
  have key : 16 * (16 * (16 * (K1 * 3 ^ e1 * n ^ E + K * n ^ E + 1) + K3 * (K + 1) ^ e3 * n ^ E + 1) +
      K * n ^ E + 1) ≤ 16 * (16 * (16 * (K1 * 3 ^ e1 + K + 1) + K3 * (K + 1) ^ e3 + 1) + K + 1) * n ^ E := by
    nlinarith
  calc 16 * (16 * (16 * (K1 * ((q.input R).length + 1) ^ e1 + K * n ^ e + 1) +
        K3 * ((readerWord (Nat.size (q.input R).length) (L q R) (xs q R) (q.input R)).length + 1) ^ e3 + 1) +
        K * n ^ e + 1)
      ≤ 16 * (16 * (16 * (K1 * 3 ^ e1 * n ^ E + K * n ^ E + 1) + K3 * (K + 1) ^ e3 * n ^ E + 1) +
        K * n ^ E + 1) := by omega
    _ ≤ _ := key

end NearCubicGates.Adapters.ShortPCP.Time
