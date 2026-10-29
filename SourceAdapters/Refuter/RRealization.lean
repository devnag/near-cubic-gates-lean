import SourceAdapters.Refuter.CNFDock
import SourceAdapters.Refuter.RSearch
import SourceAdapters.Refuter.RProgram
import Proof.Foundations.CanonicalBinary

/-!
# `RefuterRealization T` from the compiler dock and the two machines of R (input 7, F05/F06)

Consumer: the internal join `RefuterRealization T` (`Refuter/Assembly.lean`): one oracle program `R`
and one degree, fixed before `M`, output the record `x_p` selected by the CLW20 search within
`C(T(N)+1)^d` (proof of `lem:multitape-refuter`; proof of `cor:framed-refuter`).

This file assembles `R` from contracts for its two ordinary machines:

* `stateRequest`: the request R's round protocol (`RSearch.lean`) poses in a state (membership of the
  record `x_q`; the interval prefix `[0,q)` for the least hit), and `stateRequest_answer`: through the compiler of join X5(b) (`cnf_dock`) the source
  SAT oracle answers exactly the protocol's `answer` (at all large `N`).
* `RoundMachines T query`: the contract of the loader `INIT` and the round machine `STEP` of
  `Loop.program` (one degree before `M`; coefficient, onset and the tape encoding after `M`).
* `refuterRealization_of_machines`: the dock + `InClockRange T` + a `RoundMachines` package give
  `RefuterRealization T`, with `O(N)` rounds and every query and output paid.
-/

namespace NearCubicGates.Adapters.Refuter

open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairOrdinary
open NearCubicWires.RepairSource NearCubicWires.LocalBitMultitape
open NearCubicWires.Bindings.CLW20Theorem113
open NearCubicGates.Adapters.Compile
open NearCubicWires.RepairSource.OrdinaryOracleCompose (Ports)

set_option autoImplicit false

/-! ## The posed requests and their answers -/

/-- The request posed in state `S` (proof of `lem:multitape-refuter`): the interval prefix `[0, q)` in the
least-hit phase, membership of the record `x_q` otherwise. -/
def stateRequest (M : OrdinaryWeakMachine) (T : ℕ → ℕ) (N : ℕ) (S : SS) : CNFCompilationRequest :=
  if S.ph = 3 then intervalRequest M T N S.q else memberRequest M N (record M N S.q) (T N)

/-- The protocol's ranges: the interval never leaves `[0, s]`. -/
def Range (s : ℕ) (S : SS) : Prop := S.lo ≤ S.hi ∧ S.hi ≤ s ∧ (2 ≤ S.ph → S.lo < S.hi)

/-- The states STEP is run on: fresh, or posed within range. -/
def Good (s : ℕ) (S : SS) : Prop := S = SS.fresh ∨ (Posed S ∧ Range s S)

theorem absorb_range (s F : ℕ) (hs : 1 ≤ s) (S : SS) (hS : Posed S) (hR : Range s S) (a : Bool) :
    ((absorb s F S a).ph = 2 ∨ (absorb s F S a).ph = 3 ∨ (absorb s F S a).ph = 4) ∧
      Range s (absorb s F S a) ∧ (absorb s F S a).lo < (absorb s F S a).hi := by
  obtain ⟨hlh0, hhs, hlt⟩ := hR
  rcases hS with ⟨h1, hlo, hhi⟩ | ⟨hph, hf, hlh⟩
  · simp only [absorb, h1, if_true]
    split_ifs
    · exact ⟨Or.inr (Or.inl rfl), ⟨Nat.zero_le _, le_rfl, fun _ => hs⟩, hs⟩
    · exact ⟨Or.inl rfl, ⟨Nat.zero_le _, le_rfl, fun _ => hs⟩, hs⟩
  · have hn1 : S.ph ≠ 1 := by omega
    simp only [absorb, hn1, if_false, SS.q]
    split_ifs
    · refine ⟨hph, ⟨by dsimp only; omega, hhs, fun _ => by dsimp only; omega⟩, by dsimp only; omega⟩
    · refine ⟨hph, ⟨by dsimp only; omega, by dsimp only; omega, fun _ => by dsimp only; omega⟩,
        by dsimp only; omega⟩

theorem round_range (s F : ℕ) (hs : 1 ≤ s) (S : SS) (hS : Posed S) (hR : Range s S) (a : Bool)
    (S' : SS) (h : round s F S a = .inl S') : Posed S' ∧ Range s S' := by
  have h0 : S.ph ≠ 0 := by rcases hS with ⟨h1, _⟩ | ⟨h2, _⟩ <;> omega
  simp only [round, h0, if_false] at h
  obtain ⟨hTph, hTR, hTlt⟩ := absorb_range s F hs S hS hR a
  generalize absorb s F S a = T at h hTph hTR hTlt
  unfold settle at h
  by_cases he : T.fuel = 0 ∨ T.hi ≤ T.lo + 1
  · rw [if_pos he] at h
    by_cases h3 : T.ph = 3
    · rw [if_pos h3] at h
      by_cases hc : F = 0 ∨ T.lo + 1 ≤ 1
      · rw [if_pos hc] at h; cases h
      · rw [if_neg hc] at h
        cases h
        have := hTR.2.1
        refine ⟨Or.inr ⟨Or.inr (Or.inr rfl), ?_, ?_⟩, ?_, ?_, fun _ => ?_⟩ <;> dsimp only <;> omega
    · rw [if_neg h3] at h; cases h
  · rw [if_neg he] at h
    cases h
    exact ⟨Or.inr ⟨hTph, by omega, by omega⟩, hTR⟩

/-- The oracle's answer on R's query word is the protocol's answer (proof of `lem:multitape-refuter` with
), at all large `N`. -/
theorem stateRequest_answer (query : CNFCompilationRequest → ℕ)
    (hint : ∀ (M : OrdinaryWeakMachine) (T : ℕ → ℕ) (N k : ℕ), k ≤ 2 ^ (N / 16) →
      (RecoveryOracle.sourceSAT (query (intervalRequest M T N k)) = true ↔
        intervalHit (hitData M T N) k = true))
    (M : OrdinaryWeakMachine) (T : ℕ → ℕ) (N : ℕ)
    (hmem : ∀ i, (RecoveryOracle.sourceSAT (query (memberRequest M N (record M N i) (T N))) = true ↔
      memberData M N i = true))
    (S : SS) (hR : Range (2 ^ (N / 16)) S) :
    RecoveryOracle.sourceSAT (CanonicalBinary.bitsValue (query (stateRequest M T N S)).bits) =
      answer (memberData M N) (hitData M T N) S := by
  rw [CanonicalBinary.bitsValue_natBits]
  unfold stateRequest answer
  split_ifs with h3
  · have hq : S.q ≤ 2 ^ (N / 16) := by simp only [SS.q]; have := hR.1; have := hR.2.1; omega
    exact Bool.eq_iff_iff.mpr (hint M T N S.q hq)
  · exact Bool.eq_iff_iff.mpr (hmem S.q)

/-! ## Sizes of the posed requests -/

theorem natBitLength_le_of_le {a b : ℕ} (h : a ≤ b) : natBitLength a ≤ natBitLength b := by
  unfold natBitLength
  exact Nat.add_le_add_right (Nat.log_mono_right h) 1

theorem natBitLength_two_pow (g : ℕ) : natBitLength (2 ^ g) = g + 1 := by
  unfold natBitLength
  rw [Nat.log_pow (by norm_num)]

theorem bits_length_le (n : ℕ) : n.bits.length ≤ natBitLength n := by
  have hsz := Nat.size_eq_bits_len n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · unfold natBitLength
    have := Nat.size_le.mpr (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) n)
    omega

theorem frame_len (w : List Bool) : (RepairOrdinary.frame w).length = 2 * w.length + 1 := by
  induction w with
  | nil => rfl
  | cons b w ih => simp [RepairOrdinary.frame, ih]; ring

/-- Every posed request has measure at most `|code(M)| + 3(T(N)+1)` (proof of `lem:multitape-refuter`). -/
theorem stateRequest_measure (M : OrdinaryWeakMachine) (T : ℕ → ℕ) (hT : ∀ n, n ≤ T n) (N : ℕ)
    (S : SS) (hR : Range (2 ^ (N / 16)) S) :
    (stateRequest M T N S).measure ≤ (VerifierEncoding.code M.verifier).length + 3 * (T N + 1) := by
  have hN := hT N
  have hhi : natBitLength (2 ^ (N / 16)) = N / 16 + 1 := natBitLength_two_pow _
  unfold stateRequest
  split_ifs
  · have hq : S.q ≤ 2 ^ (N / 16) := by simp only [SS.q]; have := hR.1; have := hR.2.1; omega
    have := natBitLength_le_of_le hq
    simp only [CNFCompilationRequest.measure, intervalRequest, List.length_ofFn]
    omega
  · simp only [CNFCompilationRequest.measure, memberRequest, List.length_ofFn, hhi]
    omega

/-! ## The machine contract -/

/-- What `STEP` must do from tapes encoding `S` with answer `β` written: the protocol's round. On
`inr p` it sets DONE and the output tape holds `frame (x_p)` (proof of `lem:multitape-refuter`); on `inl S'` it clears
DONE, the query tape holds the full framed query word of `S'`, and after the oracle
writes any answer `β'` the tapes encode `S'` with `β'`. -/
def StepOutcome {t : ℕ} (ports : Ports t) (ans done : Fin t) (Enc : SS → Bool → (Fin t → List Bool) → Prop)
    (query : CNFCompilationRequest → ℕ) (M : OrdinaryWeakMachine) (T : ℕ → ℕ) (N : ℕ)
    (b : Fin t → List Bool) : SS ⊕ ℕ → Prop
  | .inr p => readTapeBit (b done) 0 = true ∧ b ports.outputTape = RepairOrdinary.frame (List.ofFn (record M N p))
  | .inl S' => readTapeBit (b done) 0 = false ∧
      (∃ pad, b ports.queryTape = RepairOrdinary.frame (query (stateRequest M T N S')).bits ++ pad) ∧
      ∀ β', Enc S' β' (RecoveryQueryAnswer.output ans b β')

/-- **The two machines of R and their contract.** One tape set, one degree (before `M`); per `M` a
coefficient, an onset and a tape encoding `Enc N S β` of the protocol state. -/
structure RoundMachines (T : ℕ → ℕ) (query : CNFCompilationRequest → ℕ) where
  t : ℕ
  sI : ℕ
  sS : ℕ
  ports : Ports t
  MI : Machine t sI
  MS : Machine t sS
  ans : Fin t
  done : Fin t
  degree : ℕ
  spec : ∀ M : OrdinaryWeakMachine, OrdinaryLittleO M T →
    ∃ (C onset : ℕ) (Enc : ℕ → SS → Bool → (Fin t → List Bool) → Prop), ∀ N, onset ≤ N →
      (∃ a, ClockJoin.ReadyRun MI (C * (T N + 1) ^ degree)
          ((Loop.program ports MI MS ans done).base.inputTapes (pairInput M N)) a ∧
        Enc N SS.fresh false a) ∧
      (∀ S β a, Enc N S β a → Good (2 ^ (N / 16)) S →
        ∃ b, ClockJoin.ReadyRun MS (C * (T N + 1) ^ degree) a b ∧
          StepOutcome ports ans done (Enc N) query M T N b (round (2 ^ (N / 16)) (N / 16 + 1) S β))

/-! ## The assembly -/

theorem pow_le_pow_of_one_le {X a D : ℕ} (hX : 1 ≤ X) (h : a ≤ D) : X ^ a ≤ X ^ D :=
  Nat.pow_le_pow_right hX h

/-- **`RefuterRealization T` from the compiler dock and the machine package.** -/
theorem refuterRealization_of_machines (T : ℕ → ℕ) (hT : InClockRange T)
    (K dC : ℕ) (query : CNFCompilationRequest → ℕ)
    (hint : ∀ (M : OrdinaryWeakMachine) (T : ℕ → ℕ) (N k : ℕ), k ≤ 2 ^ (N / 16) →
      (RecoveryOracle.sourceSAT (query (intervalRequest M T N k)) = true ↔
        intervalHit (hitData M T N) k = true))
    (hmem : ∀ (T : ℕ → ℕ) (M : OrdinaryWeakMachine), OrdinaryLittleO M T →
      ∃ onset, ∀ N, onset ≤ N → ∀ i,
        (RecoveryOracle.sourceSAT (query (memberRequest M N (record M N i) (T N))) = true ↔
          memberData M N i = true))
    (hbits : ∀ r, natBitLength (query r) ≤ K * r.measure ^ dC)
    (pkg : RoundMachines T query) : RefuterRealization T := by
  refine ⟨Loop.program pkg.ports pkg.MI pkg.MS pkg.ans pkg.done, pkg.degree + dC + 1, fun M hM => ?_⟩
  obtain ⟨C, o1, Enc, hspec⟩ := pkg.spec M hM
  obtain ⟨o2, hm2⟩ := hmem T M hM
  set c := (VerifierEncoding.code M.verifier).length
  refine ⟨C + 6 * C + 12 * K * (c + 3) ^ dC + 31, max o1 o2, fun N hN => ?_⟩
  have hN1 : o1 ≤ N := le_of_max_le_left hN
  have hN2 : o2 ≤ N := le_of_max_le_right hN
  obtain ⟨hinit, hstep⟩ := hspec N hN1
  set s := 2 ^ (N / 16) with hs
  set F := N / 16 + 1 with hF
  set m := memberData M N
  set v := hitData M T N
  set pstar := (refuterIndex m v s F).1 with hpstar
  set X := T N + 1 with hX
  have hX1 : 1 ≤ X := by omega
  have hs1 : 1 ≤ s := Nat.one_le_two_pow
  set B := C * X ^ pkg.degree with hB
  set Q := 2 * (K * (c + 3 * X) ^ dC) + 1 with hQ
  -- the round predicate
  let P : ℕ → (Fin pkg.t → List Bool) → Prop := fun k a =>
    ∃ S β, Enc N S β a ∧ Good s S ∧ (S = SS.fresh ∨ β = answer m v S) ∧
      value m v s F S = pstar ∧ μ F S < k
  have hround : ∀ k a, P (k + 1) a →
      (∃ b, ClockJoin.ReadyRun pkg.MS B a b ∧ readTapeBit (b pkg.done) 0 = true ∧
          b pkg.ports.outputTape = RepairOrdinary.frame (List.ofFn (record M N pstar))) ∨
      (∃ b bits pad, ClockJoin.ReadyRun pkg.MS B a b ∧ readTapeBit (b pkg.done) 0 = false ∧
          b pkg.ports.queryTape = RepairOrdinary.frame bits ++ pad ∧
          (RepairOrdinary.frame bits).length ≤ Q ∧
          P k (RecoveryQueryAnswer.output pkg.ans b
            (RecoveryOracle.sourceSAT (CanonicalBinary.bitsValue bits)))) := by
    intro k a ⟨S, β, hEnc, hGood, hβ, hval, hμ⟩
    obtain ⟨b, hb, hout⟩ := hstep S β a hEnc hGood
    -- the query branch, shared by the fresh and the posed case
    have query_branch : ∀ S', Posed S' → Range s S' → value m v s F S' = pstar → μ F S' < k →
        StepOutcome pkg.ports pkg.ans pkg.done (Enc N) query M T N b (.inl S') →
        ∃ b bits pad, ClockJoin.ReadyRun pkg.MS B a b ∧ readTapeBit (b pkg.done) 0 = false ∧
          b pkg.ports.queryTape = RepairOrdinary.frame bits ++ pad ∧
          (RepairOrdinary.frame bits).length ≤ Q ∧
          P k (RecoveryQueryAnswer.output pkg.ans b
            (RecoveryOracle.sourceSAT (CanonicalBinary.bitsValue bits))) := by
      intro S' hP' hR' hv' hμ' ⟨hd, ⟨pad, hq⟩, hE⟩
      refine ⟨b, _, pad, hb, hd, hq, ?_, S', _, hE _, Or.inr ⟨hP', hR'⟩,
        Or.inr (stateRequest_answer query hint M T N (hm2 N hN2) S' hR'), hv', hμ'⟩
      -- the query length
      have hlen := bits_length_le (query (stateRequest M T N S'))
      have hb2 := hbits (stateRequest M T N S')
      have hmeas := stateRequest_measure M T hT.1 N S' hR'
      have hmono : (stateRequest M T N S').measure ^ dC ≤ (c + 3 * X) ^ dC :=
        Nat.pow_le_pow_left (by omega) dC
      have : K * (stateRequest M T N S').measure ^ dC ≤ K * (c + 3 * X) ^ dC :=
        Nat.mul_le_mul_left K hmono
      rw [frame_len]
      omega
    rcases hGood with h0 | ⟨hP, hR⟩
    · -- fresh: pose `M(x_0)`
      subst h0
      have hr : round s F SS.fresh β = .inl SS.first := fresh_round s F β
      rw [hr] at hout
      refine Or.inr (query_branch SS.first first_posed ⟨le_rfl, by simp [SS.first], fun h => by
        simp [SS.first] at h⟩ ?_ ?_ hout)
      · rw [← hval]; simp [value, SS.first, SS.fresh]
      · have : μ F SS.first < μ F SS.fresh := first_μ F
        omega
    · have hβ' : β = answer m v S := by
        rcases hβ with h0 | h
        · rcases hP with ⟨h1, _⟩ | ⟨h2, _⟩ <;> (subst h0; simp_all [SS.fresh])
        · exact h
      subst hβ'
      rcases round_spec m v s F S hP with ⟨p, hr, hp⟩ | ⟨S', hr, hP', hv', hμ'⟩
      · rw [hr] at hout
        obtain ⟨hd, ho⟩ := hout
        refine Or.inl ⟨b, hb, hd, ?_⟩
        rw [ho, hp, hval]
      · rw [hr] at hout
        exact Or.inr (query_branch S' hP' (round_range s F hs1 S hP hR _ S' hr).2
          (by rw [hv', hval]) (by omega) hout)
  have h0 : ∀ a, ¬ P 0 a := fun a ⟨_, _, _, _, _, _, hμ⟩ => Nat.not_lt_zero _ hμ
  obtain ⟨a0, ha0, hEnc0⟩ := hinit
  have hP0 : P (μ F SS.fresh + 1) a0 :=
    ⟨SS.fresh, false, hEnc0, Or.inl rfl, Or.inl rfl, fresh_value m v s F, Nat.lt_succ_self _⟩
  have hruns := Loop.runs_of_rounds RecoveryOracle.sourceSAT pkg.ports pkg.MI pkg.MS pkg.ans pkg.done
    (pairInput M N) (List.ofFn (record M N pstar)) B B Q (μ F SS.fresh + 1) P hround h0 ⟨a0, ha0, hP0⟩
  -- the budget
  obtain ⟨cost, final, hcost, htr, hh, hout⟩ := hruns
  refine ⟨cost, final, le_trans hcost ?_, htr, hh, hout⟩
  have hk : μ F SS.fresh + 1 ≤ 6 * X := by
    have := hT.1 N; simp only [μ, SS.fresh, if_true]; omega
  set D := pkg.degree + dC + 1
  have hXd : X ^ pkg.degree ≤ X ^ D := pow_le_pow_of_one_le hX1 (by omega)
  have hXdC : X ^ dC * X ≤ X ^ D := by
    rw [← pow_succ]; exact pow_le_pow_of_one_le hX1 (by omega)
  have hXdX : X ^ pkg.degree * X ≤ X ^ D := by
    rw [← pow_succ]; exact pow_le_pow_of_one_le hX1 (by omega)
  have hX1D : X ≤ X ^ D := by
    calc X = X ^ 1 := (pow_one X).symm
      _ ≤ X ^ D := pow_le_pow_of_one_le hX1 (by omega)
  have hcX : (c + 3 * X) ^ dC ≤ (c + 3) ^ dC * X ^ dC := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left (by nlinarith) dC
  -- each piece of `B + 1 + k (B + Q + 4)`
  have e1 : B ≤ C * X ^ D := Nat.mul_le_mul_left C hXd
  have e2 : (μ F SS.fresh + 1) * B ≤ 6 * C * X ^ D := by
    calc (μ F SS.fresh + 1) * B ≤ (6 * X) * (C * X ^ pkg.degree) := Nat.mul_le_mul_right _ hk
      _ = 6 * C * (X ^ pkg.degree * X) := by ring
      _ ≤ 6 * C * X ^ D := Nat.mul_le_mul_left _ hXdX
  have e3 : (μ F SS.fresh + 1) * Q ≤ 12 * K * (c + 3) ^ dC * X ^ D + 6 * X ^ D := by
    calc (μ F SS.fresh + 1) * Q ≤ (6 * X) * Q := Nat.mul_le_mul_right _ hk
      _ = 12 * K * ((c + 3 * X) ^ dC * X) + 6 * X := by rw [hQ]; ring
      _ ≤ 12 * K * ((c + 3) ^ dC * X ^ dC * X) + 6 * X := by
          gcongr
      _ = 12 * K * (c + 3) ^ dC * (X ^ dC * X) + 6 * X := by ring
      _ ≤ 12 * K * (c + 3) ^ dC * X ^ D + 6 * X ^ D := by gcongr
  have e4 : (μ F SS.fresh + 1) * 4 ≤ 24 * X ^ D := by nlinarith
  have hsplit : B + 1 + (μ F SS.fresh + 1) * (B + Q + 4) =
      B + 1 + (μ F SS.fresh + 1) * B + (μ F SS.fresh + 1) * Q + (μ F SS.fresh + 1) * 4 := by ring
  rw [hsplit]
  have h1D : 1 ≤ X ^ D := Nat.one_le_pow _ _ hX1
  calc B + 1 + (μ F SS.fresh + 1) * B + (μ F SS.fresh + 1) * Q + (μ F SS.fresh + 1) * 4
      ≤ C * X ^ D + X ^ D + 6 * C * X ^ D + (12 * K * (c + 3) ^ dC * X ^ D + 6 * X ^ D) +
          24 * X ^ D := by omega
    _ ≤ (C + 6 * C + 12 * K * (c + 3) ^ dC + 31) * X ^ D := by nlinarith

/-! ## From the join -/

/-- **The machine-construction contract.** For the compiler of join X5(b) — any query
map with its paid word function (proof of `lem:multitape-refuter`) — the loader and round machines of R exist. -/
def MachinesFromCompiler (T : ℕ → ℕ) : Prop :=
  ∀ (K d : ℕ) (query : CNFCompilationRequest → ℕ),
    WordFunction CNFCompilationRequest CNFCompilationRequest.word
      (fun r => RepairOrdinary.frame (query r).bits) (fun r => K * r.measure ^ d) →
    Nonempty (RoundMachines T query)

/-- **`RefuterRealization T` from the `ComputationToCNF` interface** and the machine construction. -/
theorem refuterRealization_of_compiler (T : ℕ → ℕ) (hT : InClockRange T) (h : ComputationToCNF)
    (hm : MachinesFromCompiler T) : RefuterRealization T := by
  obtain ⟨K, d, query, _, hint, hmem, hbits, ⟨wf⟩⟩ := cnf_dock h
  obtain ⟨pkg⟩ := hm K d query wf
  exact refuterRealization_of_machines T hT K d query hint hmem hbits pkg

/-- The full range (the form `clw20_theorem1_13_of_joins` consumes). -/
theorem refuterRealization_all (h : ComputationToCNF)
    (hm : ∀ T : ℕ → ℕ, Bindings.CLW20Theorem113.TimeConstructible T → InClockRange T → MachinesFromCompiler T) :
    ∀ T : ℕ → ℕ, Bindings.CLW20Theorem113.TimeConstructible T → InClockRange T → RefuterRealization T :=
  fun T hTc hTr => refuterRealization_of_compiler T hTr h (hm T hTc hTr)

end NearCubicGates.Adapters.Refuter
