import SourceAdapters.Refuter.DiagonalSearch

/-!
# Input 7 skeleton: the exact consumer from two internal joins (F06)

Consumer: `CLW20_Theorem1_13` (`L/Statement.lean:1079`), body `Theorem1_13At` (l.1059–1067).

Paper anchors: `cor:framed-refuter`; the records `x_i = ⟨M,N,w_i⟩` of CLW20 §4.1
(`adapters/sourcetext/CLW20.txt` l.1056–1061: "`⟨M,n,z⟩ = 1^M 0 1^{n−M−2−|z|} 0 z`");
the recurrence; Step 4; the hierarchy convention.

The two internal joins, each naming the paper quantity it delivers:

* `HierarchyRecurrence T H` — the hierarchy verifier `H` (framed, time and witness
  length `c(T(N)+1)`) satisfies, for each promised `M` at all large `N`, the exact recurrence of
  `cor:framed-refuter` on the records of `M`.
* `RefuterRealization T` — one oracle program `R` and one degree `d`, fixed before `M`, output the
  record `x_p` selected by the CLW20 search (`refuterIndex`, proof of `lem:multitape-refuter`) within `C(T(N)+1)^d`
  (`C` and the onset after `M`).

`WitnessesComplete T` is a third, `M`-only condition (every run of `M` halts
within `t_M(N) ≤ T(N)` and reads only its `⌊N/16⌋` witness bits, so `M(x_1)` is the disjunction
over the enumerated witnesses); it involves neither `H` nor `R` and is left as a hypothesis here.

`theorem1_13At_of_joins` proves the consumer body from these three; no hypothesis mentions
`Theorem1_13At` or `NineInputs`.
-/

namespace NearCubicGates.Adapters.Refuter

open NearCubicWires NearCubicWires.RepairSource NearCubicWires.Bindings.CLW20Theorem113

set_option autoImplicit false

/-! ## Records and enumerated witnesses -/

/-- The enumeration index of a weak machine: its verifier code read as a binary numeral behind a
leading `1` (injective in the code). It is the integer `M` of CLW20's `⟨M,n,z⟩`. -/
def machineIndex (M : OrdinaryWeakMachine) : ℕ :=
  (VerifierEncoding.code M.verifier).foldl (fun acc b => 2 * acc + if b then 1 else 0) 1

/-- The `i`-th `g`-bit string in lexicographic order (first bit most significant), proof of `cor:framed-refuter`. -/
def unrank (g i : ℕ) : BitInput g := fun j => i.testBit (g - 1 - j.val)

/-- The record `⟨M, N, w_i⟩ = 1^M 0 1^{N−M−2−g} 0 w_i` with `g = ⌊N/16⌋` (CLW20 §4.1 with the paper's
`g(N)`, proof of `cor:framed-refuter`). It has length exactly `N`; it is a valid record when `M + 2 + g ≤ N`. -/
def record (M : OrdinaryWeakMachine) (N i : ℕ) : BitInput N := fun j =>
  if j.val < machineIndex M then true
  else if j.val = machineIndex M then false
  else if h3 : j.val + 1 < N - N / 16 then true
  else if h4 : j.val + 1 = N - N / 16 then false
  else (unrank (N / 16) i) ⟨j.val - (N - N / 16), by have := j.isLt; omega⟩

/-! ## The three lists of the recurrence -/

/-- `M(x_i)`. -/
noncomputable def memberData (M : OrdinaryWeakMachine) (N : ℕ) (i : ℕ) : Bool :=
  machineValue M N (record M N i)

/-- `[V_M^fr(x_1, T(N), w_i) = 1]` (proof of `cor:framed-refuter`: exactly the two framed tapes, at most `T(N)`
steps). -/
noncomputable def hitData (M : OrdinaryWeakMachine) (T : ℕ → ℕ) (N : ℕ) (i : ℕ) : Bool := by
  classical
  exact decide (M.verifier.acceptsAt (T N) (List.ofFn (record M N 0))
    (List.ofFn (unrank (N / 16) i)))

/-- The hierarchy language of a verifier `H` (the convention of `InNTIME`). -/
noncomputable def hierarchyLanguage {T : ℕ → ℕ} (H : OrdinaryHierarchy T) : Language := by
  classical
  exact fun n x => decide (H.verifier.language H.time n x)

/-- `L^fr_T(x_i)`. -/
noncomputable def diagData {T : ℕ → ℕ} (H : OrdinaryHierarchy T) (M : OrdinaryWeakMachine)
    (N : ℕ) (i : ℕ) : Bool :=
  hierarchyLanguage H N (record M N i)

/-! ## The internal joins -/

/-- **Join F03/F04 (hierarchy).** For each promised `M`, at all sufficiently large `N`, the
hierarchy language obeys the exact recurrence of proof of `cor:framed-refuter` on the `2^{⌊N/16⌋}` records. -/
def HierarchyRecurrence (T : ℕ → ℕ) (H : OrdinaryHierarchy T) : Prop :=
  ∀ M : OrdinaryWeakMachine, OrdinaryLittleO M T →
    ∃ onset, ∀ N, onset ≤ N →
      DiagonalRecurrence (2 ^ (N / 16)) (memberData M N) (hitData M T N) (diagData H M N)

/-- **Join F05/F06 (refuter).** One program and one degree, fixed before `M`, write the record
selected by the CLW20 search (proof of `lem:multitape-refuter`) within `C(T(N)+1)^d`. -/
def RefuterRealization (T : ℕ → ℕ) : Prop :=
  ∃ (R : OrdinaryOracleProgram) (d : ℕ),
    ∀ M : OrdinaryWeakMachine, OrdinaryLittleO M T →
      ∃ C onset : ℕ, ∀ N, onset ≤ N →
        OrdinaryOracleRuns RecoveryOracle.sourceSAT R (pairInput M N)
          (List.ofFn (record M N
            (refuterIndex (memberData M N) (hitData M T N) (2 ^ (N / 16)) (N / 16 + 1)).1))
          (C * (T N + 1) ^ d)

/-- **Condition on `M`.** At large `N`, `M(x_1)` is the disjunction of the enumerated verdicts
(proof of `lem:multitape-refuter`, CLW20 p.18). -/
def WitnessesComplete (T : ℕ → ℕ) : Prop :=
  ∀ M : OrdinaryWeakMachine, OrdinaryLittleO M T →
    ∃ onset, ∀ N, onset ≤ N →
      CompleteWitnesses (2 ^ (N / 16)) (memberData M N) (hitData M T N)

/-! ## Assembly -/

theorem inNTIME_hierarchyLanguage {T : ℕ → ℕ} (H : OrdinaryHierarchy T) :
    InNTIME T (hierarchyLanguage H) :=
  ⟨H, fun n x => by simp [hierarchyLanguage]⟩

/-- **F06 at one clock** (`cor:framed-refuter` quantifier order): the consumer body from the joins. -/
theorem theorem1_13At_of_joins (T : ℕ → ℕ) (H : OrdinaryHierarchy T)
    (hrec : HierarchyRecurrence T H) (hR : RefuterRealization T) (hwit : WitnessesComplete T) :
    Theorem1_13At T := by
  obtain ⟨R, d, hrun⟩ := hR
  refine ⟨hierarchyLanguage H, inNTIME_hierarchyLanguage H, R, d, fun M hM => ?_⟩
  obtain ⟨C, o1, h1⟩ := hrun M hM
  obtain ⟨o2, h2⟩ := hrec M hM
  obtain ⟨o3, h3⟩ := hwit M hM
  refine ⟨C, max o1 (max o2 o3), fun N hN => ?_⟩
  have hN1 : o1 ≤ N := le_of_max_le_left hN
  have hN2 : o2 ≤ N := le_of_max_le_left (le_of_max_le_right hN)
  have hN3 : o3 ≤ N := le_of_max_le_right (le_of_max_le_right hN)
  have hs : 0 < 2 ^ (N / 16) := Nat.two_pow_pos _
  have hfuel : 2 ^ (N / 16) + 1 ≤ 2 ^ (N / 16 + 1) := by rw [pow_succ]; omega
  obtain ⟨_, hne⟩ := refuterIndex_spec (2 ^ (N / 16)) (N / 16 + 1) (memberData M N)
    (hitData M T N) (diagData H M N) hs hfuel (h2 N hN2) (h3 N hN3)
  exact ⟨_, h1 N hN1, hne⟩

/-- **F06, the full field** (`CLW20_Theorem1_13`, every clock in range) from the joins at every
admissible clock. -/
theorem clw20_theorem1_13_of_joins
    (parts : ∀ T : ℕ → ℕ, TimeConstructible T → InClockRange T →
      ∃ H : OrdinaryHierarchy T, HierarchyRecurrence T H ∧ RefuterRealization T)
    (hwit : ∀ T : ℕ → ℕ, InClockRange T → WitnessesComplete T) :
    CLW20_Theorem1_13 := by
  intro T hT hR
  obtain ⟨H, hrec, hreal⟩ := parts T hT hR
  exact theorem1_13At_of_joins T H hrec hreal (hwit T hR)

end NearCubicGates.Adapters.Refuter
