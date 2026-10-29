import NineInputs

/-!
# The diagonal recurrence forces a discrepancy, found by `O(log s)` queries (input 7, F04 search)

Paper anchor: `cor:framed-refuter`, the recurrence, and `lem:multitape-refuter`
Step 4:

* proof of `cor:framed-refuter`: "`L^fr_T(x_i) = [V_M^fr(x_1,T(N),w_i)=0] · (M(x_{i+1}) if i<s, 1 if i=s)`".
* proof of `lem:multitape-refuter`: "`R_T` first asks whether `M` accepts `x^(N)_1`. If not, it runs the binary search of
  [CLW20, Corollary 4.5] on the lists `D(x^(N)_i)` and `M(x^(N)_i)`, `1≤i≤2^{g}`. If so, it finds by
  binary search the least `j` with `V_M(x^(N)_1,T(N),w^(N)_j)=1` and runs the same search on the
  first `j` entries. Either way it makes `O(N)` adaptive queries".
* proof of `lem:multitape-refuter` (Step 3, second query kind): "whether `M` accepts a given input within `T(N)` steps
  with some witness in a given lexicographic interval" — the interval query used here for the
  least `j`.

The finite search theorem is proved abstractly from the recurrence. Its algorithm uses membership
and interval-existence queries to find the first relevant accepting witness or a discrepancy interval.
The interval invariants and endpoint cases give a discrepancy after `O(N)` queries, without
enumerating the `2^g` witnesses.

Indices are 0-based: `x_0, …, x_{s-1}` and `w_0, …, w_{s-1}`. The data are three Boolean lists:
`m i = M(x_i)`, `v i = [V_M^fr(x_0, T(N), w_i) = 1]` and `d i = L^fr_T(x_i)`. At the lengths where
the recurrence is used every run of `M` halts within `T(N)`, so `V` is never `⊥`
and `[V = 0] = !v i`.

The procedures below query only `m` and the interval predicate of `v`; `d` occurs only in the
correctness theorems. The query lists are returned so that their lengths can be charged.
-/

namespace NearCubicGates.Adapters.Refuter

set_option autoImplicit false

/-! ## CLW20 Lemma 4.4: bisection on a list with different ends -/

/-- Bisection with fuel (CLW20 Lemma 4.4, `adapters/sourcetext/CLW20.txt` l.1205–1218): on
`lo < hi` with `e lo ≠ e hi`, it returns `p` with `lo ≤ p < hi` and `e p ≠ e (p+1)`, together with
the positions it queried (one per round). -/
def bisect (e : ℕ → Bool) : ℕ → ℕ → ℕ → ℕ × List ℕ
  | 0, lo, _ => (lo, [])
  | fuel + 1, lo, hi =>
      if hi ≤ lo + 1 then (lo, [])
      else
        let q := (lo + hi) / 2
        let rest := if e q = e lo then bisect e fuel q hi else bisect e fuel lo q
        (rest.1, q :: rest.2)

theorem bisect_queries_length (e : ℕ → Bool) :
    ∀ fuel lo hi, (bisect e fuel lo hi).2.length ≤ fuel := by
  intro fuel
  induction fuel with
  | zero => intro lo hi; simp [bisect]
  | succ fuel ih =>
    intro lo hi
    simp only [bisect]
    split_ifs with h1 h2
    · simp
    · simp only [List.length_cons]; exact Nat.succ_le_succ (ih _ _)
    · simp only [List.length_cons]; exact Nat.succ_le_succ (ih _ _)

/-- **Interval invariant** (CLW20 Lemma 4.4 proof, step 2: "the invariant `a_L ≠ a_R` always
holds"). -/
theorem bisect_spec (e : ℕ → Bool) :
    ∀ fuel lo hi, lo < hi → e lo ≠ e hi → hi - lo ≤ 2 ^ fuel →
      lo ≤ (bisect e fuel lo hi).1 ∧ (bisect e fuel lo hi).1 < hi ∧
        e (bisect e fuel lo hi).1 ≠ e ((bisect e fuel lo hi).1 + 1) := by
  intro fuel
  induction fuel with
  | zero =>
    intro lo hi hlt hne hlen
    simp only [pow_zero] at hlen
    have : hi = lo + 1 := by omega
    subst this
    simp [bisect, hne]
  | succ fuel ih =>
    intro lo hi hlt hne hlen
    simp only [bisect]
    split_ifs with h1 h2
    · have : hi = lo + 1 := by omega
      subst this
      exact ⟨le_rfl, by omega, hne⟩
    · have hq1 : lo < (lo + hi) / 2 := by omega
      have hq2 : (lo + hi) / 2 < hi := by omega
      have hne' : e ((lo + hi) / 2) ≠ e hi := by rw [h2]; exact hne
      have hlen' : hi - (lo + hi) / 2 ≤ 2 ^ fuel := by rw [pow_succ] at hlen; omega
      obtain ⟨a, b, c⟩ := ih _ _ hq2 hne' hlen'
      exact ⟨by omega, b, c⟩
    · have hq1 : lo < (lo + hi) / 2 := by omega
      have hne' : e lo ≠ e ((lo + hi) / 2) := fun h => h2 h.symm
      have hlen' : (lo + hi) / 2 - lo ≤ 2 ^ fuel := by rw [pow_succ] at hlen; omega
      obtain ⟨a, b, c⟩ := ih _ _ hq1 hne' hlen'
      exact ⟨a, by omega, c⟩

/-! ## The least accepting witness, by interval queries -/

/-- The interval-existence query (proof of `lem:multitape-refuter`): some witness among `w_0, …, w_{k-1}` makes `M`
accept `x_0` within the clock. -/
def intervalHit (v : ℕ → Bool) (k : ℕ) : Bool := (List.range k).any v

theorem intervalHit_iff (v : ℕ → Bool) (k : ℕ) : intervalHit v k = true ↔ ∃ i < k, v i = true := by
  simp [intervalHit]

theorem intervalHit_mono (v : ℕ → Bool) {k k' : ℕ} (h : k ≤ k') (hk : intervalHit v k = true) :
    intervalHit v k' = true := by
  rw [intervalHit_iff] at hk ⊢
  obtain ⟨i, hi, hv⟩ := hk
  exact ⟨i, by omega, hv⟩

/-- The least accepting witness index, by bisection on the monotone list
`intervalHit v 0, …, intervalHit v s` (proof of `lem:multitape-refuter`). -/
def leastHit (v : ℕ → Bool) (s fuel : ℕ) : ℕ × List ℕ := bisect (intervalHit v) fuel 0 s

theorem leastHit_spec (v : ℕ → Bool) (s fuel : ℕ) (hs : s ≤ 2 ^ fuel) (hhit : ∃ i < s, v i = true) :
    (leastHit v s fuel).1 < s ∧ v (leastHit v s fuel).1 = true ∧
      ∀ i < (leastHit v s fuel).1, v i = false := by
  have h0 : intervalHit v 0 = false := by simp [intervalHit]
  have hs' : intervalHit v s = true := (intervalHit_iff v s).mpr hhit
  have hpos : 0 < s := by obtain ⟨i, hi, _⟩ := hhit; omega
  obtain ⟨_, hp, hne⟩ := bisect_spec (intervalHit v) fuel 0 s hpos (by rw [h0, hs']; simp)
    (by omega)
  set p := (bisect (intervalHit v) fuel 0 s).1 with hpdef
  have hp' : (leastHit v s fuel).1 = p := rfl
  rw [hp']
  -- monotone list with different neighbours: `intervalHit v p = false`, `intervalHit v (p+1) = true`
  have hfalse : intervalHit v p = false := by
    cases hpv : intervalHit v p with
    | false => rfl
    | true =>
      exfalso
      have := intervalHit_mono v (Nat.le_succ p) hpv
      rw [hpv, this] at hne
      exact hne rfl
  have htrue : intervalHit v (p + 1) = true := by
    cases hpv : intervalHit v (p + 1) with
    | true => rfl
    | false => rw [hfalse, hpv] at hne; exact absurd rfl hne
  refine ⟨hp, ?_, ?_⟩
  · obtain ⟨i, hi, hv⟩ := (intervalHit_iff v _).mp htrue
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
    · exfalso
      have : intervalHit v p = true := (intervalHit_iff v p).mpr ⟨i, hi, hv⟩
      rw [hfalse] at this
      exact Bool.noConfusion this
    · rw [← hi]; exact hv
  · intro i hi
    cases hv : v i with
    | false => rfl
    | true =>
      have : intervalHit v p = true := (intervalHit_iff v p).mpr ⟨i, hi, hv⟩
      rw [hfalse] at this
      exact absurd this (by simp)

/-! ## The refuter's index: CLW20 Corollary 4.5 and Theorem 4.6 -/

/-- The recurrence of proof of `cor:framed-refuter` (0-based), for the `s` records of one length. -/
def DiagonalRecurrence (s : ℕ) (m v d : ℕ → Bool) : Prop :=
  ∀ i < s, d i = (!v i && if i + 1 < s then m (i + 1) else true)

/-- `M(x_0)` is the existential acceptance over the complete enumeration of witnesses (proof of `cor:framed-refuter`, CLW20 p.18: `M(x) = 1 ⇔ ∨_w V_M(x,T(n),w) = 1`). -/
def CompleteWitnesses (s : ℕ) (m v : ℕ → Bool) : Prop :=
  (m 0 = true ↔ ∃ i < s, v i = true)

/-- The chain searched by the refuter: in the first case `M(x_0), …, M(x_{s-1})` followed by the
end value `1`; in the second case `M(x_0), …, M(x_j)` followed by `0` (proof of `lem:multitape-refuter`). -/
def refuterChain (m : ℕ → Bool) (last : ℕ) (endValue : Bool) : ℕ → Bool :=
  fun i => if i ≤ last then m i else endValue

/-- The refuter's index and its queries (proof of `lem:multitape-refuter`): one membership query `M(x_0)`; if it is
`0`, bisection of the chain `M(x_0), …, M(x_{s-1}), 1`; if it is `1`, the least `j` by interval
queries, then bisection of `M(x_0), …, M(x_j), 0`. The first list holds the indices of membership
queries `M(x_i)`, the second the endpoints of interval queries. -/
def refuterIndex (m v : ℕ → Bool) (s fuel : ℕ) : ℕ × List ℕ × List ℕ :=
  if m 0 = false then
    let r := bisect (refuterChain m (s - 1) true) fuel 0 s
    (r.1, 0 :: r.2, [])
  else
    let j := leastHit v s fuel
    let r := bisect (refuterChain m j.1 false) fuel 0 (j.1 + 1)
    (r.1, 0 :: r.2, j.2)

/-- **The query count** (proof of `lem:multitape-refuter`, Step 4, "`O(N)` adaptive queries"): at most `fuel + 1` membership
queries and at most `fuel` interval queries. With `s = 2^g` and `fuel = g + 1` this is `O(g)`. -/
theorem refuterIndex_queries (m v : ℕ → Bool) (s fuel : ℕ) :
    (refuterIndex m v s fuel).2.1.length ≤ fuel + 1 ∧ (refuterIndex m v s fuel).2.2.length ≤ fuel := by
  unfold refuterIndex
  split_ifs
  · simp only [List.length_cons, List.length_nil]
    exact ⟨Nat.succ_le_succ (bisect_queries_length _ _ _ _), Nat.zero_le _⟩
  · simp only [List.length_cons]
    exact ⟨Nat.succ_le_succ (bisect_queries_length _ _ _ _), bisect_queries_length _ _ _ _⟩

/-- **The discrepancy** (CLW20 Theorem 4.6, proof of `lem:multitape-refuter`, Step 4 "it returns a word `x^(N)_p` with
`D(x^(N)_p) ≠ M(x^(N)_p)`"): under the recurrence and complete witness enumeration, the refuter's
index `p` is a record index (`p < s`) with `M(x_p) ≠ L^fr_T(x_p)`. Here `s + 1 ≤ 2^fuel`. -/
theorem refuterIndex_spec (s fuel : ℕ) (m v d : ℕ → Bool) (hs : 0 < s) (hfuel : s + 1 ≤ 2 ^ fuel)
    (hrec : DiagonalRecurrence s m v d) (hwit : CompleteWitnesses s m v) :
    (refuterIndex m v s fuel).1 < s ∧ m (refuterIndex m v s fuel).1 ≠ d (refuterIndex m v s fuel).1 := by
  unfold refuterIndex
  split_ifs with hm0
  · -- Case `M(x_0) = 0`: no witness is accepted, so `d i` is the next chain entry.
    have hnone : ∀ i < s, v i = false := by
      intro i hi
      cases hv : v i with
      | false => rfl
      | true => exact absurd (hwit.mpr ⟨i, hi, hv⟩) (by rw [hm0]; simp)
    set e := refuterChain m (s - 1) true with he
    have he0 : e 0 = false := by simp [he, refuterChain, hm0]
    have hes : e s = true := by simp [he, refuterChain]; omega
    obtain ⟨_, hp, hne⟩ := bisect_spec e fuel 0 s hs (by rw [he0, hes]; simp) (by omega)
    set p := (bisect e fuel 0 s).1
    refine ⟨hp, ?_⟩
    have hmp : m p = e p := by simp [he, refuterChain]; omega
    have hdp : d p = e (p + 1) := by
      rw [hrec p hp, hnone p hp]
      simp only [Bool.not_false, Bool.true_and, he, refuterChain]
      split_ifs <;> first | rfl | omega
    rw [hmp, hdp]
    exact hne
  · -- Case `M(x_0) = 1`: the least accepting witness `j` closes the chain with `d j = 0`.
    have hm1 : m 0 = true := by simpa using hm0
    have hhit := hwit.mp hm1
    obtain ⟨hj, hvj, hleast⟩ := leastHit_spec v s fuel (by omega) hhit
    set j := (leastHit v s fuel).1
    set e := refuterChain m j false with he
    have he0 : e 0 = true := by simp [he, refuterChain, hm1]
    have hej : e (j + 1) = false := by simp [he, refuterChain]
    obtain ⟨_, hp, hne⟩ := bisect_spec e fuel 0 (j + 1) (by omega) (by rw [he0, hej]; simp)
      (by omega)
    set p := (bisect e fuel 0 (j + 1)).1
    refine ⟨by omega, ?_⟩
    have hmp : m p = e p := by simp [he, refuterChain]; omega
    have hdp : d p = e (p + 1) := by
      rw [hrec p (by omega)]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hp with hlt | heq
      · rw [hleast p hlt]
        simp only [Bool.not_false, Bool.true_and, he, refuterChain]
        split_ifs <;> first | rfl | omega
      · rw [heq, hvj]
        simp [he, refuterChain]
    rw [hmp, hdp]
    exact hne

/-- Without any procedure: the recurrence alone already forces a discrepancy among the `s`
records (the existence half of CLW20 Theorem 1.12's argument). -/
theorem discrepancy_exists (s : ℕ) (m v d : ℕ → Bool) (hs : 0 < s)
    (hrec : DiagonalRecurrence s m v d) (hwit : CompleteWitnesses s m v) :
    ∃ p < s, m p ≠ d p := by
  have hfuel : s + 1 ≤ 2 ^ (s + 1) := (Nat.lt_two_pow_self).le
  exact ⟨_, (refuterIndex_spec s (s + 1) m v d hs hfuel hrec hwit).1,
    (refuterIndex_spec s (s + 1) m v d hs hfuel hrec hwit).2⟩

end NearCubicGates.Adapters.Refuter
