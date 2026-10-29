import SourceAdapters.Joins.ComputationToCNF
import SourceAdapters.Compile.WitnessRanks
import SourceAdapters.Refuter.Witnesses

/-!
# The refuter's membership and prefix queries from `ComputationToCNF`

The compiler interface `Joins/ComputationToCNF.lean` accepts a half-open witness prefix `[0, high)`.
Its consumer here is `DiagonalSearch.refuterIndex`.

Step 3 of `lem:multitape-refuter` lists hierarchy-acceptance queries, acceptance of `M` with a witness
in a lexicographic interval, and fixed-witness bounded-acceptance queries. The search implemented here
uses the interval family, with the framing and witness length of `cor:framed-refuter`:

* `memberRequest` asks whether some witness of exactly `⌊N/16⌋` bits makes the framed run of `M`
  accept `x_i` within `T(N)` steps. It uses the full prefix, `high = 2^⌊N/16⌋`.
* `intervalRequest` uses the prefix `[0, k)`, with `high = k`, to find the least accepting witness
  index as in Step 4. Its answer is `DiagonalSearch.intervalHit`.

The implemented search requires neither a hierarchy-acceptance query nor a fixed-witness query.
The verifier code is copied unchanged from the refuter's input `pairInput M n`.
`intervalRequest_accepts` identifies the prefix answer with `intervalHit (hitData M T N) k` for
`k ≤ 2^⌊N/16⌋`; `memberRequest_accepts_eventually` identifies the full-prefix answer with `memberData`
at all large `N`. `cnf_dock` packages the compiler and these two equivalences.
-/

namespace NearCubicGates.Adapters.Refuter

open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairOrdinary
open NearCubicWires.RepairSource NearCubicWires.TseitinCNF
open NearCubicWires.Bindings.CLW20Theorem113
open NearCubicGates.Adapters.Compile

set_option autoImplicit false

/-- **The compiler, as the refuter consumes it.** One global coefficient and degree; for every
request, the source SAT oracle on the compiled code answers exactly the bounded framed acceptance
with a witness of rank below `high`, the code has polynomial bit length, and one ordinary word
function writes the framed query. -/
theorem member_dock (h : ComputationToCNF) :
    ∃ K d : ℕ, ∃ query : CNFCompilationRequest → ℕ, 1 ≤ K ∧
      (∀ r, RecoveryOracle.sourceSAT (query r) = true ↔ r.accepts) ∧
      (∀ r, natBitLength (query r) ≤ K * r.measure ^ d) ∧
      Nonempty (WordFunction CNFCompilationRequest CNFCompilationRequest.word
        (fun r => RepairOrdinary.frame (query r).bits) (fun r => K * r.measure ^ d)) := by
  obtain ⟨K, d, formula, hK, _, _, _, hsat, _, hbits, hword⟩ := h
  exact ⟨K, d, fun r => RecoveryOracle.sourceSATCode (formula r), hK, hsat, hbits, hword⟩

/-! ## Ranks of the enumerated witnesses -/

/-- The enumeration `unrank` and the join's rank are inverse (proof of `cor:framed-refuter`: `w_i` is the witness
of rank `i`, first bit most significant). -/
theorem witnessRank_unrank (g : ℕ) : ∀ i, i < 2 ^ g → witnessRank (unrank g i) = i := by
  induction g with
  | zero =>
    intro i hi
    have : i = 0 := by simpa using hi
    subst this
    rfl
  | succ g ih =>
    intro i hi
    have hhalf : i / 2 < 2 ^ g := by rw [pow_succ] at hi; omega
    have hl : List.ofFn (unrank (g + 1) i) = List.ofFn (unrank g (i / 2)) ++ [i.testBit 0] := by
      rw [List.ofFn_succ', List.concat_eq_append]
      congr 1
      · congr 1
        funext j
        show i.testBit (g + 1 - 1 - (Fin.castSucc j).val) = (i / 2).testBit (g - 1 - j.val)
        rw [Nat.testBit_div_two]
        congr 1
        simp only [Fin.val_castSucc]
        have := j.isLt
        omega
      · show [i.testBit (g + 1 - 1 - g)] = [i.testBit 0]
        simp
    have ih' := ih (i / 2) hhalf
    unfold witnessRank at ih' ⊢
    rw [hl, List.foldl_append, ih']
    simp only [List.foldl_cons, List.foldl_nil, Nat.testBit_zero]
    by_cases h : i % 2 = 1
    · simp [h]; omega
    · simp [h]; omega

/-- Every witness is the enumerated witness of its rank. -/
theorem unrank_witnessRank (g : ℕ) (w : BitInput g) : unrank g (witnessRank w) = w := by
  obtain ⟨j, hj, rfl⟩ := unrank_surjective g w
  rw [witnessRank_unrank g j hj]

/-! ## (Q-interval): the least accepting witness -/

/-- The interval request of proof of `lem:multitape-refuter` at the search's prefix `[0, k)`: the framed run of `M` on
`x_1` within `T(N)` steps, with a witness of exactly `⌊N/16⌋` bits and rank below `k`. -/
def intervalRequest (M : OrdinaryWeakMachine) (T : ℕ → ℕ) (N k : ℕ) : CNFCompilationRequest where
  verifier := M.verifier
  input := List.ofFn (record M N 0)
  witnessLength := N / 16
  fuel := T N
  high := k

/-- **(Q-interval) is a direct instance** (proof of `lem:multitape-refuter`): the request accepts exactly
when some enumerated witness below `k` is a hit, i.e. the search's `intervalHit`. -/
theorem intervalRequest_accepts (M : OrdinaryWeakMachine) (T : ℕ → ℕ) (N k : ℕ)
    (hk : k ≤ 2 ^ (N / 16)) :
    (intervalRequest M T N k).accepts ↔ intervalHit (hitData M T N) k = true := by
  show (∃ w : BitInput (N / 16), witnessRank w < k ∧
    M.verifier.acceptsAt (T N) (List.ofFn (record M N 0)) (List.ofFn w)) ↔ _
  rw [intervalHit_iff]
  constructor
  · rintro ⟨w, hrank, hacc⟩
    refine ⟨witnessRank w, hrank, ?_⟩
    unfold hitData
    rw [unrank_witnessRank]
    simpa using hacc
  · rintro ⟨i, hi, hv⟩
    have hi' : i < 2 ^ (N / 16) := lt_of_lt_of_le hi hk
    refine ⟨unrank (N / 16) i, ?_, ?_⟩
    · rw [witnessRank_unrank _ i hi']
      exact hi
    · unfold hitData at hv
      simpa using hv

/-! ## (Q-member): `M(x_i)` -/

/-- The weak-machine membership request (proof of `lem:multitape-refuter`): exact framed tapes, exactly `⌊n/16⌋`
witness bits, fuel `fuel`, the full witness range. -/
def memberRequest (M : OrdinaryWeakMachine) (n : ℕ) (x : BitInput n) (fuel : ℕ) :
    CNFCompilationRequest where
  verifier := M.verifier
  input := List.ofFn x
  witnessLength := n / 16
  fuel := fuel
  high := 2 ^ (n / 16)

theorem memberRequest_accepts (M : OrdinaryWeakMachine) (n : ℕ) (x : BitInput n) (fuel : ℕ) :
    (memberRequest M n x fuel).accepts ↔
      ∃ w : BitInput (n / 16), M.verifier.acceptsAt fuel (List.ofFn x) (List.ofFn w) :=
  fullWitnessRange (memberRequest M n x fuel) rfl

/-- **(Q-member) at the clock is `M(x)`** at all large `N` (proof of `lem:multitape-refuter`: every run halts within
`t_M(N) ≤ T(N)` steps). -/
theorem memberRequest_accepts_eventually (T : ℕ → ℕ) (M : OrdinaryWeakMachine)
    (hM : OrdinaryLittleO M T) :
    ∃ onset, ∀ N, onset ≤ N → ∀ x : BitInput N,
      ((memberRequest M N x (T N)).accepts ↔ machineValue M N x = true) := by
  obtain ⟨onset, hon⟩ := hM 1 (by norm_num)
  refine ⟨onset, fun N hN x => ?_⟩
  have hrt : M.runtime N ≤ T N := by simpa using hon N hN
  rw [memberRequest_accepts]
  unfold machineValue
  simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨w, ⟨r, hr, hacc⟩⟩
    exact ⟨w, T N, r, hr, hacc⟩
  · intro hacc
    obtain ⟨w, hw⟩ := (accepts_iff_bounded M N x).mp hacc
    exact ⟨w, acceptsAt_mono _ hrt _ _ hw⟩

/-- The records' membership lists, through the request (`memberData`, proof of `lem:multitape-refuter`). -/
theorem memberRequest_record (T : ℕ → ℕ) (M : OrdinaryWeakMachine) (hM : OrdinaryLittleO M T) :
    ∃ onset, ∀ N, onset ≤ N → ∀ i,
      ((memberRequest M N (record M N i) (T N)).accepts ↔ memberData M N i = true) := by
  obtain ⟨onset, h⟩ := memberRequest_accepts_eventually T M hM
  exact ⟨onset, fun N hN i => h N hN (record M N i)⟩

/-- **The dock (both kinds), from the join.** One compiled-query map with a global coefficient and
degree answers (Q-interval) exactly as `intervalHit` on the search's prefixes, and (Q-member) exactly
as `memberData` at all large `N`. -/
theorem cnf_dock (h : ComputationToCNF) :
    ∃ K d : ℕ, ∃ query : CNFCompilationRequest → ℕ, 1 ≤ K ∧
      (∀ (M : OrdinaryWeakMachine) (T : ℕ → ℕ) (N k : ℕ), k ≤ 2 ^ (N / 16) →
        (RecoveryOracle.sourceSAT (query (intervalRequest M T N k)) = true ↔
          intervalHit (hitData M T N) k = true)) ∧
      (∀ (T : ℕ → ℕ) (M : OrdinaryWeakMachine), OrdinaryLittleO M T →
        ∃ onset, ∀ N, onset ≤ N → ∀ i,
          (RecoveryOracle.sourceSAT (query (memberRequest M N (record M N i) (T N))) = true ↔
            memberData M N i = true)) ∧
      (∀ r, natBitLength (query r) ≤ K * r.measure ^ d) ∧
      Nonempty (WordFunction CNFCompilationRequest CNFCompilationRequest.word
        (fun r => RepairOrdinary.frame (query r).bits) (fun r => K * r.measure ^ d)) := by
  obtain ⟨K, d, query, hK, hsat, hbits, hword⟩ := member_dock h
  refine ⟨K, d, query, hK, fun M T N k hk => (hsat _).trans (intervalRequest_accepts M T N k hk),
    fun T M hM => ?_, hbits, hword⟩
  obtain ⟨onset, hmem⟩ := memberRequest_record T M hM
  exact ⟨onset, fun N hN i => (hsat _).trans (hmem N hN i)⟩

end NearCubicGates.Adapters.Refuter
