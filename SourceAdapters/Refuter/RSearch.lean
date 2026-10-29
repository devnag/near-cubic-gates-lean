import SourceAdapters.Refuter.DiagonalSearch

/-!
# The refuter's search as a round protocol (input 7, R: the algorithm the program runs)

Paper anchor: `lem:multitape-refuter` Step 4: "`R_T` first asks whether `M` accepts
`x^(N)_1`. If not, it runs the binary search of [CLW20, Corollary 4.5] on the lists `D(x^(N)_i)` and
`M(x^(N)_i)`, `1≤i≤2^{g}`. If so, it finds by binary search the least `j` with
`V_M(x^(N)_1,T(N),w^(N)_j)=1` and runs the same search on the first `j` entries. Either way it makes
`O(N)` adaptive queries"; the query kinds are those of Step 3, (membership; acceptance
with a witness in a lexicographic interval).

`DiagonalSearch.refuterIndex` is the search as a function of the two answer lists. A machine asks one
query per round, so this file restates it as a **round protocol** on a small state `SS` (phase,
bisection interval, remaining fuel, the known chain value at the left end) and proves:

* `refuterIndex_fst`: the index is `bis …` (bisection that only remembers the left-end value);
* `round_spec`: one round (absorb the answer to the posed query, then settle) keeps the eventual
  index `value` and strictly decreases the measure `μ`, or ends with exactly `value`;
* `fresh_value`: from the fresh state the eventual index is `(refuterIndex m v s F).1`.

The posed query of a state is at `q = (lo+hi)/2`: membership `M(x_q)` in phases 1, 2, 4 and the
interval query `intervalHit v q` (prefix `[0,q)`) in phase 3.
-/

namespace NearCubicGates.Adapters.Refuter

set_option autoImplicit false

/-! ## Bisection that remembers only the left-end value -/

/-- Bisection on `[lo, hi)` where the left-end chain value `elo` is known; the chain is read only
through `ask` at midpoints (CLW20 Lemma 4.4, as in `bisect`). -/
def bis (ask : ℕ → Bool) (elo : Bool) : ℕ → ℕ → ℕ → ℕ
  | 0, lo, _ => lo
  | f + 1, lo, hi =>
      if hi ≤ lo + 1 then lo
      else if ask ((lo + hi) / 2) = elo then bis ask elo f ((lo + hi) / 2) hi
      else bis ask elo f lo ((lo + hi) / 2)

theorem bis_zero (ask : ℕ → Bool) (elo : Bool) (lo hi : ℕ) : bis ask elo 0 lo hi = lo := rfl

theorem bis_ended (ask : ℕ → Bool) (elo : Bool) (f lo hi : ℕ) (h : f = 0 ∨ hi ≤ lo + 1) :
    bis ask elo f lo hi = lo := by
  rcases h with rfl | h
  · rfl
  · cases f with
    | zero => rfl
    | succ f => simp [bis, h]

theorem bis_succ (ask : ℕ → Bool) (elo : Bool) (f lo hi : ℕ) (h : lo + 1 < hi) :
    bis ask elo (f + 1) lo hi =
      if ask ((lo + hi) / 2) = elo then bis ask elo f ((lo + hi) / 2) hi
      else bis ask elo f lo ((lo + hi) / 2) := by
  simp only [bis, show ¬ hi ≤ lo + 1 by omega, if_false]

/-- `bisect` with a chain `e` agreeing with `ask` on `[lo, hi)` and `e lo = elo` is `bis`. -/
theorem bisect_eq_bis (e ask : ℕ → Bool) (elo : Bool) :
    ∀ fuel lo hi, e lo = elo → (∀ q, lo ≤ q → q < hi → e q = ask q) →
      (bisect e fuel lo hi).1 = bis ask elo fuel lo hi := by
  intro fuel
  induction fuel with
  | zero => intro lo hi _ _; rfl
  | succ f ih =>
    intro lo hi hlo hag
    by_cases h : hi ≤ lo + 1
    · simp [bisect, bis, h]
    · have hq1 : lo < (lo + hi) / 2 := by omega
      have hq2 : (lo + hi) / 2 < hi := by omega
      rw [bis_succ ask elo f lo hi (by omega)]
      simp only [bisect, h, if_false]
      rw [hag _ (by omega) hq2, hlo]
      split_ifs with ha
      · exact ih _ _ (by rw [hag _ (by omega) hq2, ha]) (fun q h1 h2 => hag q (by omega) h2)
      · exact ih _ _ hlo (fun q h1 h2 => hag q h1 (by omega))

/-- **The refuter's index through `bis`** (proof of `lem:multitape-refuter`). -/
theorem refuterIndex_fst (m v : ℕ → Bool) (s F : ℕ) :
    (refuterIndex m v s F).1 =
      if m 0 = false then bis m false F 0 s
      else bis m true F 0 (bis (intervalHit v) false F 0 s + 1) := by
  unfold refuterIndex leastHit
  split_ifs with hm
  · exact bisect_eq_bis _ m false F 0 s (by simp [refuterChain, hm])
      (fun q _ hq => by simp [refuterChain]; omega)
  · have hm1 : m 0 = true := by simpa using hm
    have hj := bisect_eq_bis (intervalHit v) (intervalHit v) false F 0 s (by simp [intervalHit])
      (fun _ _ _ => rfl)
    show (bisect (refuterChain m (bisect (intervalHit v) F 0 s).1 false) F 0
      ((bisect (intervalHit v) F 0 s).1 + 1)).1 = _
    rw [hj]
    exact bisect_eq_bis _ m true F 0 _ (by simp [refuterChain, hm1])
      (fun q _ hq => by simp [refuterChain]; omega)

/-! ## The round protocol -/

/-- The search state between two queries. Phases: `0` fresh (nothing asked), `1` the first membership
query `M(x_0)` is posed, `2` the chain search after `M(x_0)=0`, `3` the least-hit search after
`M(x_0)=1`, `4` the chain search on the first `j+1` entries. -/
structure SS where
  ph : ℕ
  lo : ℕ
  hi : ℕ
  fuel : ℕ
  elo : Bool

/-- The posed query point. -/
def SS.q (S : SS) : ℕ := (S.lo + S.hi) / 2

/-- The fresh state left by the loader. -/
def SS.fresh : SS := ⟨0, 0, 0, 0, false⟩

/-- The state posing `M(x_0)`. -/
def SS.first : SS := ⟨1, 0, 0, 0, false⟩

variable (m v : ℕ → Bool) (s F : ℕ)

/-- The oracle's answer to the posed query: interval in phase 3, membership otherwise. -/
def answer (S : SS) : Bool := if S.ph = 3 then intervalHit v S.q else m S.q

/-- Absorb the answer `a` to the posed query. -/
def absorb (S : SS) (a : Bool) : SS :=
  if S.ph = 1 then (if a then ⟨3, 0, s, F, false⟩ else ⟨2, 0, s, F, false⟩)
  else if a = S.elo then ⟨S.ph, S.q, S.hi, S.fuel - 1, S.elo⟩
  else ⟨S.ph, S.lo, S.q, S.fuel - 1, S.elo⟩

/-- Settle after an answer: a finished bisection ends the search (phases 2, 4) or starts the final
chain search on the first `j+1` entries (phase 3, `j` the least hit). -/
def settle (T : SS) : SS ⊕ ℕ :=
  if T.fuel = 0 ∨ T.hi ≤ T.lo + 1 then
    (if T.ph = 3 then (if F = 0 ∨ T.lo + 1 ≤ 1 then .inr 0 else .inl ⟨4, 0, T.lo + 1, F, true⟩)
     else .inr T.lo)
  else .inl T

/-- One round: from the fresh state pose `M(x_0)`; otherwise absorb and settle. -/
def round (S : SS) (a : Bool) : SS ⊕ ℕ :=
  if S.ph = 0 then .inl SS.first else settle F (absorb s F S a)

/-- A state with a well-defined posed query. -/
def Posed (S : SS) : Prop :=
  (S.ph = 1 ∧ S.lo = 0 ∧ S.hi = 0) ∨
    ((S.ph = 2 ∨ S.ph = 3 ∨ S.ph = 4) ∧ S.fuel ≠ 0 ∧ S.lo + 1 < S.hi)

/-- The eventual index from a state. -/
def value (S : SS) : ℕ :=
  if S.ph = 0 ∨ S.ph = 1 then
    (if m 0 = false then bis m false F 0 s else bis m true F 0 (bis (intervalHit v) false F 0 s + 1))
  else if S.ph = 3 then bis m true F 0 (bis (intervalHit v) S.elo S.fuel S.lo S.hi + 1)
  else bis m S.elo S.fuel S.lo S.hi

/-- The number of rounds still possible. -/
def μ (S : SS) : ℕ :=
  if S.ph = 0 then 2 * F + 3
  else if S.ph = 1 then 2 * F + 2
  else if S.ph = 3 then S.fuel + F + 1
  else S.fuel

theorem fresh_value : value m v s F SS.fresh = (refuterIndex m v s F).1 := by
  simp [value, SS.fresh, refuterIndex_fst]

theorem fresh_round (a : Bool) : round s F SS.fresh a = .inl SS.first := by
  simp [round, SS.fresh]

theorem first_posed : Posed SS.first := Or.inl ⟨rfl, rfl, rfl⟩

theorem first_value : value m v s F SS.first = value m v s F SS.fresh := by
  simp [value, SS.first, SS.fresh]

theorem first_μ : μ F SS.first < μ F SS.fresh := by simp [μ, SS.first, SS.fresh]

theorem settle_spec (T : SS) (hT : T.ph = 2 ∨ T.ph = 3 ∨ T.ph = 4) :
    (∃ p, settle F T = .inr p ∧ p = value m v s F T) ∨
      (∃ T', settle F T = .inl T' ∧ Posed T' ∧ value m v s F T' = value m v s F T ∧
        μ F T' ≤ μ F T) := by
  unfold settle
  by_cases he : T.fuel = 0 ∨ T.hi ≤ T.lo + 1
  · rw [if_pos he]
    by_cases h3 : T.ph = 3
    · rw [if_pos h3]
      have hj : bis (intervalHit v) T.elo T.fuel T.lo T.hi = T.lo := bis_ended _ _ _ _ _ he
      by_cases hc : F = 0 ∨ T.lo + 1 ≤ 1
      · rw [if_pos hc]
        refine Or.inl ⟨0, rfl, ?_⟩
        simp only [value, h3, hj]
        simp only [show ¬ (3 = 0 ∨ 3 = 1) by omega, if_false, if_true]
        rw [bis_ended _ _ _ _ _ (by omega)]
      · rw [if_neg hc]
        refine Or.inr ⟨_, rfl, Or.inr ⟨Or.inr (Or.inr rfl), by dsimp only; omega, by dsimp only; omega⟩, ?_, ?_⟩
        · simp [value, h3, hj]
        · simp [μ, h3]; omega
    · rw [if_neg h3]
      refine Or.inl ⟨T.lo, rfl, ?_⟩
      have h01 : ¬ (T.ph = 0 ∨ T.ph = 1) := by omega
      simp only [value, h01, h3, if_false]
      rw [bis_ended _ _ _ _ _ he]
  · rw [if_neg he]
    exact Or.inr ⟨T, rfl, Or.inr ⟨hT, by omega, by omega⟩, rfl, le_rfl⟩

/-- **One round keeps the eventual index** and strictly decreases `μ`, or ends with it. -/
theorem round_spec (S : SS) (hS : Posed S) :
    (∃ p, round s F S (answer m v S) = .inr p ∧ p = value m v s F S) ∨
      (∃ S', round s F S (answer m v S) = .inl S' ∧ Posed S' ∧
        value m v s F S' = value m v s F S ∧ μ F S' < μ F S) := by
  rcases hS with ⟨h1, hlo, hhi⟩ | ⟨hph, hf, hlh⟩
  · -- phase 1: the answer is `M(x_0)`
    have hq : S.q = 0 := by simp [SS.q, hlo, hhi]
    have hr : round s F S (answer m v S) = settle F (absorb s F S (m 0)) := by
      simp [round, answer, h1, hq]
    rw [hr]
    have hv : value m v s F S =
        (if m 0 = false then bis m false F 0 s else bis m true F 0 (bis (intervalHit v) false F 0 s + 1)) := by
      simp [value, h1]
    cases hm : m 0
    · have ha : absorb s F S false = ⟨2, 0, s, F, false⟩ := by simp [absorb, h1]
      rw [ha]
      rcases settle_spec m v s F ⟨2, 0, s, F, false⟩ (Or.inl rfl) with ⟨p, h, hp⟩ | ⟨T', h, hP, hv', hμ⟩
      · exact Or.inl ⟨p, h, by rw [hp, hv, hm]; simp [value]⟩
      · refine Or.inr ⟨T', h, hP, by rw [hv', hv, hm]; simp [value], ?_⟩
        have : μ F ⟨2, 0, s, F, false⟩ = F := by simp [μ]
        have : μ F S = 2 * F + 2 := by simp [μ, h1]
        omega
    · have ha : absorb s F S true = ⟨3, 0, s, F, false⟩ := by simp [absorb, h1]
      rw [ha]
      rcases settle_spec m v s F ⟨3, 0, s, F, false⟩ (Or.inr (Or.inl rfl)) with ⟨p, h, hp⟩ | ⟨T', h, hP, hv', hμ⟩
      · exact Or.inl ⟨p, h, by rw [hp, hv, hm]; simp [value]⟩
      · refine Or.inr ⟨T', h, hP, by rw [hv', hv, hm]; simp [value], ?_⟩
        have : μ F ⟨3, 0, s, F, false⟩ = F + F + 1 := by simp [μ]
        have : μ F S = 2 * F + 2 := by simp [μ, h1]
        omega
  · -- phases 2, 3, 4: one bisection step
    have h0 : S.ph ≠ 0 := by omega
    have hn1 : S.ph ≠ 1 := by omega
    obtain ⟨f, hfe⟩ : ∃ f, S.fuel = f + 1 := ⟨S.fuel - 1, by omega⟩
    set a := answer m v S with ha
    have hT : absorb s F S a =
        if a = S.elo then (⟨S.ph, S.q, S.hi, f, S.elo⟩ : SS) else ⟨S.ph, S.lo, S.q, f, S.elo⟩ := by
      simp only [absorb, hn1, if_false, hfe, Nat.add_sub_cancel]
    have hr : round s F S a = settle F (absorb s F S a) := by simp [round, h0]
    rw [hr]
    set T := absorb s F S a with hTdef
    have hTph : T.ph = S.ph := by rw [hT]; split_ifs <;> rfl
    have hTelo : T.elo = S.elo := by rw [hT]; split_ifs <;> rfl
    have hTf : T.fuel = f := by rw [hT]; split_ifs <;> rfl
    -- the bisection step on the phase's chain
    have hstep : ∀ ask : ℕ → Bool, a = ask S.q →
        bis ask S.elo S.fuel S.lo S.hi = bis ask T.elo T.fuel T.lo T.hi := by
      intro ask hask
      rw [hfe, bis_succ ask S.elo f S.lo S.hi hlh, hTelo, hTf, hT]
      simp only [SS.q] at hask ⊢
      rw [← hask]
      split_ifs <;> rfl
    have hval : value m v s F T = value m v s F S := by
      by_cases h3 : S.ph = 3
      · have := hstep (intervalHit v) (by simp [ha, answer, h3])
        simp only [value, hTph, h3, show ¬ (3 = 0 ∨ 3 = 1) by omega, if_false, if_true, this]
      · have := hstep m (by simp [ha, answer, h3])
        have h01 : ¬ (S.ph = 0 ∨ S.ph = 1) := by omega
        simp only [value, hTph, h01, h3, if_false, this]
    have hμ : μ F T < μ F S := by
      simp only [μ, hTph, h0, hn1, if_false, hTf, hfe]
      split_ifs <;> omega
    rcases settle_spec m v s F T (by omega) with ⟨p, h, hp⟩ | ⟨T', h, hP, hv', hμ'⟩
    · exact Or.inl ⟨p, h, by rw [hp, hval]⟩
    · exact Or.inr ⟨T', h, hP, by rw [hv', hval], by omega⟩

/-! ## Sizes -/

/-- In every posed state the interval stays inside `[0, s]` (`s ≥ 1`), so every query point is
below `s` and every number the machine stores is at most `s`. -/
def InRange (S : SS) : Prop := S.lo ≤ S.hi ∧ S.hi ≤ s ∧ S.fuel ≤ F

end NearCubicGates.Adapters.Refuter
