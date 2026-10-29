import SourceAdapters.RAMACSP.CheckReads
import SourceAdapters.Routing.RoutingPatternsCover
import SourceAdapters.Routing.TranslationLanding

/-!
# Embedding theorem, part 1: guards, lane classes, catalog blocks

Paper: `app:affine-embedding`, "Selectors" and "Placement". HOST fixes the
stage, column, role and area. TIME, FIRST, PREV, EARLY_TIME, LAST_TIME,
INPUT and DUMMY impose the corresponding lane conditions. DUMMY partitions
high-half lanes past the input records; EARLY_TIME excludes the last time
lane; PREV partitions nonzero lanes by their least set bit. Distinct active
slots occupy distinct catalog points.

Contents:
- the exact host/lane semantics of a machine guard (`guardAt_iff`, `guardAt_cube_iff`);
- the arithmetic meaning of every lane mask of the guard library (`lane_time`, `lane_first`, …, `lane_dummy`);
- `Blk`: a list whose elements are pairwise related and whose integer keys lie in an interval; blocks with disjoint
  key intervals concatenate (used for the catalog lists, which list their templates in increasing tag order);
- injectivity of the catalog placement on active slots (`tCell_inj`, `sCell_inj`).
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.RAMACSP

open NearCubicGates.Adapters NearCubicGates.Adapters.RAMTrace

namespace Guards

open Routing Routing.Patterns

/-- The lane mask is the only unfixed coordinate of a machine guard. The bounds prevent carries between its packed
lane, stage, column, role and area blocks. -/
theorem guardAt_iff (l : Layout) (om laneKnown laneValue stage : ℕ) (host : Cell)
    (x s c r a : ℕ) (hpoint : InRange l x s c r a)
    (hknown : laneKnown < 2 ^ l.k) (hvalue : laneValue < 2 ^ l.k)
    (hstage : stage < 2 ^ l.ell) (hcol : host.col om < l.C)
    (hrole : host.role < 8) (harea : host.area < 2) :
    patternHolds (guardAt l om laneKnown laneValue stage host)
      (bits l.m (cellMask l x s c r a)) ↔
      s = stage ∧ c = host.col om ∧ r = host.role ∧ a = host.area ∧
        x &&& laneKnown = laneValue &&& laneKnown := by
  have hk : InRange l laneKnown (2 ^ l.ell - 1) (2 ^ l.q - 1) 7 1 :=
    ⟨hknown, by have := Nat.two_pow_pos l.ell; omega,
      by change 2 ^ l.q - 1 < 2 ^ l.q; have := Nat.two_pow_pos l.q; omega,
      by decide, by decide⟩
  have hv : InRange l laneValue stage (host.col om) host.role host.area :=
    ⟨hvalue, hstage, hcol, hrole, harea⟩
  have hs : s &&& (2 ^ l.ell - 1) = s :=
    Nat.and_two_pow_sub_one_of_lt_two_pow hpoint.2.1
  have hstage' : stage &&& (2 ^ l.ell - 1) = stage :=
    Nat.and_two_pow_sub_one_of_lt_two_pow hstage
  have hc : c &&& (2 ^ l.q - 1) = c :=
    Nat.and_two_pow_sub_one_of_lt_two_pow hpoint.2.2.1
  have hcol' : host.col om &&& (2 ^ l.q - 1) = host.col om :=
    Nat.and_two_pow_sub_one_of_lt_two_pow hcol
  have hr : r &&& 7 = r :=
    Nat.and_two_pow_sub_one_of_lt_two_pow (n := 3) hpoint.2.2.2.1
  have hrole' : host.role &&& 7 = host.role :=
    Nat.and_two_pow_sub_one_of_lt_two_pow (n := 3) hrole
  have ha : a &&& 1 = a :=
    Nat.and_two_pow_sub_one_of_lt_two_pow (n := 1) hpoint.2.2.2.2
  have harea' : host.area &&& 1 = host.area :=
    Nat.and_two_pow_sub_one_of_lt_two_pow (n := 1) harea
  rw [guardAt, patternMasks_iff _ _ _ _ (LayoutFacts.cellMask_lt l _ _ _ _ _ hk),
    cellMask_and l _ _ _ _ _ _ _ _ _ _ hpoint hk,
    cellMask_and l _ _ _ _ _ _ _ _ _ _ hv hk]
  simp only [hs, hstage', hc, hcol', hr, hrole', ha, harea']
  constructor
  · intro he
    have hl : InRange l (x &&& laneKnown) s c r a :=
      ⟨Nat.and_lt_two_pow x hknown, hpoint.2⟩
    have hv' : InRange l (laneValue &&& laneKnown) stage (host.col om) host.role host.area :=
      ⟨Nat.and_lt_two_pow laneValue hknown, hv.2⟩
    obtain ⟨hx, hs', hc', hr', ha'⟩ :=
      LayoutFacts.cellMask_injective l _ _ _ _ _ _ _ _ _ _ hl hv' he
    exact ⟨hs', hc', hr', ha', hx⟩
  · rintro ⟨rfl, rfl, rfl, rfl, hx⟩
    rw [hx]

/-- Every Boolean cube point admits packed coordinates, so the packed-cell characterization loses no points of the
guard's domain. -/
theorem guardAt_cube_iff (l : Layout) (om laneKnown laneValue stage : ℕ) (host : Cell)
    (v : Fin l.m → Bool)
    (hknown : laneKnown < 2 ^ l.k) (hvalue : laneValue < 2 ^ l.k)
    (hstage : stage < 2 ^ l.ell) (hcol : host.col om < l.C)
    (hrole : host.role < 8) (harea : host.area < 2) :
    patternHolds (guardAt l om laneKnown laneValue stage host) v ↔
      ∃ x, x < 2 ^ l.k ∧ x &&& laneKnown = laneValue &&& laneKnown ∧
        bits l.m (cellMask l x stage (host.col om) host.role host.area) = v := by
  constructor
  · intro hg
    obtain ⟨x, s, c, r, a, hp, he⟩ := cube_bits_cell l v
    rw [← he] at hg
    obtain ⟨rfl, rfl, rfl, rfl, hx⟩ :=
      (guardAt_iff l om laneKnown laneValue stage host x s c r a hp
        hknown hvalue hstage hcol hrole harea).mp hg
    exact ⟨x, hp.1, hx, he⟩
  · rintro ⟨x, hx, hm, rfl⟩
    exact (guardAt_iff l om laneKnown laneValue stage host x stage (host.col om)
      host.role host.area ⟨hx, hstage, hcol, hrole, harea⟩
      hknown hvalue hstage hcol hrole harea).mpr ⟨rfl, rfl, rfl, rfl, hm⟩

/-- The range conditions of a guard `guardAt l om K V s h` (lane masks, stage, column, role, area). -/
structure GuardOk (l : Layout) (om K V s : ℕ) (h : Cell) : Prop where
  known : K < 2 ^ l.k
  value : V < 2 ^ l.k
  stage : s < 2 ^ l.ell
  col : h.col om < l.C
  role : h.role < 8
  area : h.area < 2

/-- Two lane masks conflict: some lane bit is fixed by both to different values. -/
def LaneConflict (K V K' V' : ℕ) : Prop :=
  ∃ b, K.testBit b = true ∧ K'.testBit b = true ∧ V.testBit b ≠ V'.testBit b

theorem land_eq_land_iff (x K V : ℕ) :
    x &&& K = V &&& K ↔ ∀ b, K.testBit b = true → x.testBit b = V.testBit b := by
  constructor
  · intro h b hb
    have := congrArg (fun z : ℕ => z.testBit b) h
    simpa [Nat.testBit_and, hb] using this
  · intro h
    apply Nat.eq_of_testBit_eq
    intro b
    rw [Nat.testBit_and, Nat.testBit_and]
    cases hb : K.testBit b
    · simp
    · simp [h b hb]

theorem laneConflict_false {K V K' V' : ℕ} (hc : LaneConflict K V K' V') (x : ℕ)
    (h : x &&& K = V &&& K) (h' : x &&& K' = V' &&& K') : False := by
  obtain ⟨b, hb, hb', hne⟩ := hc
  exact hne (((land_eq_land_iff x K V).mp h b hb).symm.trans ((land_eq_land_iff x K' V').mp h' b hb'))

/-- **Disjointness of two machine guards**: different hosts (stage, column, role, area), or conflicting lane masks,
select no common cube point. -/
theorem guardAt_disjoint (l : Layout) (om K V s K' V' s' : ℕ) (h h' : Cell)
    (hg : GuardOk l om K V s h) (hg' : GuardOk l om K' V' s' h')
    (hd : s ≠ s' ∨ h.col om ≠ h'.col om ∨ h.role ≠ h'.role ∨ h.area ≠ h'.area ∨ LaneConflict K V K' V')
    (v : Fin l.m → Bool) :
    ¬ (patternHolds (guardAt l om K V s h) v ∧ patternHolds (guardAt l om K' V' s' h') v) := by
  rintro ⟨h1, h2⟩
  obtain ⟨x, s0, c, r, a, hp, rfl⟩ := cube_bits_cell l v
  obtain ⟨e1, e2, e3, e4, e5⟩ :=
    (guardAt_iff l om K V s h x s0 c r a hp hg.known hg.value hg.stage hg.col hg.role hg.area).mp h1
  obtain ⟨f1, f2, f3, f4, f5⟩ :=
    (guardAt_iff l om K' V' s' h' x s0 c r a hp hg'.known hg'.value hg'.stage hg'.col hg'.role hg'.area).mp h2
  rcases hd with hd | hd | hd | hd | hd
  · exact hd (e1.symm.trans f1)
  · exact hd (e2.symm.trans f2)
  · exact hd (e3.symm.trans f3)
  · exact hd (e4.symm.trans f4)
  · exact laneConflict_false hd x e5 f5

end Guards

/-! ## The lane masks of the guard library -/

namespace Lanes

theorem testBit_hi_add (τ M b : ℕ) (hM : M < 2 ^ τ) :
    (2 ^ τ + M).testBit b = (decide (b = τ) || M.testBit b) := by
  rcases lt_trichotomy b τ with hb | rfl | hb
  · rw [Nat.testBit_two_pow_add_gt hb]; simp [Nat.ne_of_lt hb]
  · rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hM]; simp
  · have h1 : 2 ^ τ + M < 2 ^ b := by
      have : 2 ^ (τ + 1) ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hb
      rw [pow_succ] at this; omega
    rw [Nat.testBit_lt_two_pow h1, Nat.testBit_lt_two_pow (hM.trans (Nat.pow_lt_pow_right (by norm_num) hb))]
    simp [Nat.ne_of_gt hb]

theorem testBit_range (τ n b : ℕ) (hn : n ≤ τ) :
    (2 ^ τ - 2 ^ n).testBit b = decide (n ≤ b ∧ b < τ) := by
  have e : 2 ^ τ - 2 ^ n = 2 ^ n * (2 ^ (τ - n) - 1) := by
    rw [Nat.mul_sub, mul_one, ← pow_add, Nat.add_sub_cancel' hn]
  rw [e, Nat.testBit_two_pow_mul, Nat.testBit_two_pow_sub_one]
  by_cases h : n ≤ b
  · simp only [ge_iff_le, h, decide_true, Bool.true_and, true_and]
    apply decide_eq_decide.mpr; omega
  · simp [h]

theorem testBit_top (x τ : ℕ) (hx : x < 2 ^ (τ + 1)) : x.testBit τ = false ↔ x < 2 ^ τ := by
  constructor
  · intro h
    apply Nat.lt_pow_two_of_testBit
    intro i hi
    rcases Nat.eq_or_lt_of_le hi with rfl | hi
    · exact h
    · exact Nat.testBit_lt_two_pow (hx.trans_le (Nat.pow_le_pow_right (by norm_num) hi))
  · intro h; exact Nat.testBit_lt_two_pow h

theorem mod_eq_iff_bits (x c n : ℕ) (hc : c < 2 ^ n) :
    x % 2 ^ n = c ↔ ∀ b < n, x.testBit b = c.testBit b := by
  constructor
  · intro h b hb
    have := congrArg (fun z : ℕ => z.testBit b) h
    simp only [Nat.testBit_mod_two_pow, hb, decide_true, Bool.true_and] at this
    exact this
  · intro h
    apply Nat.eq_of_testBit_eq
    intro b
    rw [Nat.testBit_mod_two_pow]
    by_cases hb : b < n
    · simp [hb, h b hb]
    · simp only [hb, decide_false, Bool.false_and]
      exact (Nat.testBit_lt_two_pow (hc.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega)))).symm

theorem div_eq_iff_bits (x c n : ℕ) : x / 2 ^ n = c / 2 ^ n ↔ ∀ b, n ≤ b → x.testBit b = c.testBit b := by
  constructor
  · intro h b hb
    have := congrArg (fun z : ℕ => z.testBit (b - n)) h
    simp only [Nat.testBit_div_two_pow, Nat.sub_add_cancel hb] at this
    exact this
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_div_two_pow, Nat.testBit_div_two_pow]
    exact h _ (by omega)

open Guards

/-- `TIME` (lane bit `τ` is `0`): the time lanes `x < T`. -/
theorem lane_time (x τ : ℕ) (hx : x < 2 ^ (τ + 1)) : x &&& 2 ^ τ = 0 &&& 2 ^ τ ↔ x < 2 ^ τ := by
  rw [land_eq_land_iff, ← testBit_top x τ hx]
  constructor
  · intro h; have := h τ (by simp); simpa using this
  · intro h b hb
    rw [Nat.testBit_two_pow] at hb
    have : τ = b := of_decide_eq_true hb
    subst this; simpa using h

/-- A low mask `2^n − 1` with value `c`: the lane is `c` modulo `2^n` (`FIRST`, `LAST_TIME`, sorted `PREV_t`). -/
theorem lane_low (x c n : ℕ) : x &&& (2 ^ n - 1) = c &&& (2 ^ n - 1) ↔ x % 2 ^ n = c % 2 ^ n := by
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod]

/-- A low mask `2^n − 1` plus the time bit `τ` (`n ≤ τ`), value `c < 2^n` (the time `PREV_t`, `EARLY_TIME`). -/
theorem lane_low_time (x c n τ : ℕ) (hn : n ≤ τ) (hc : c < 2 ^ n) (hx : x < 2 ^ (τ + 1)) :
    x &&& (2 ^ τ + (2 ^ n - 1)) = c &&& (2 ^ τ + (2 ^ n - 1)) ↔ x % 2 ^ n = c ∧ x < 2 ^ τ := by
  have hM : 2 ^ n - 1 < 2 ^ τ := by
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hn
    have := Nat.two_pow_pos n
    omega
  have hcτ : c.testBit τ = false := Nat.testBit_lt_two_pow (hc.trans_le (Nat.pow_le_pow_right (by norm_num) hn))
  rw [land_eq_land_iff, mod_eq_iff_bits x c n hc, ← testBit_top x τ hx]
  simp only [testBit_hi_add τ _ _ hM, Nat.testBit_two_pow_sub_one, Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · intro h
    exact ⟨fun b hb => h b (Or.inr hb), (h τ (Or.inl rfl)).trans hcτ⟩
  · rintro ⟨h1, h2⟩ b (rfl | hb)
    · rw [h2, hcτ]
    · exact h1 b hb

/-- The block mask of lane bits `n, …, τ` (`INPUT`, `DUMMY`): the lane agrees with `c` above bit `n`. -/
theorem lane_block (x c n τ : ℕ) (hn : n ≤ τ) (hx : x < 2 ^ (τ + 1)) (hc : c < 2 ^ (τ + 1)) :
    x &&& (2 ^ τ + (2 ^ τ - 2 ^ n)) = c &&& (2 ^ τ + (2 ^ τ - 2 ^ n)) ↔ x / 2 ^ n = c / 2 ^ n := by
  have hM : 2 ^ τ - 2 ^ n < 2 ^ τ := Nat.sub_lt (Nat.two_pow_pos τ) (Nat.two_pow_pos n)
  rw [land_eq_land_iff, div_eq_iff_bits]
  simp only [testBit_hi_add τ _ _ hM, testBit_range τ n _ hn, Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · intro h b hb
    rcases Nat.lt_or_ge τ b with hτ | hτ
    · have h1 : x.testBit b = false :=
        Nat.testBit_lt_two_pow (hx.trans_le (Nat.pow_le_pow_right (by norm_num) hτ))
      have h2 : c.testBit b = false :=
        Nat.testBit_lt_two_pow (hc.trans_le (Nat.pow_le_pow_right (by norm_num) hτ))
      rw [h1, h2]
    · rcases Nat.eq_or_lt_of_le hτ with rfl | hτ
      · exact h b (Or.inl rfl)
      · exact h b (Or.inr ⟨hb, hτ⟩)
  · intro h b hb
    rcases hb with rfl | ⟨hb, -⟩
    · exact h b hn
    · exact h b hb

theorem lane_input (x a τ : ℕ) (ha : a ≤ τ) (hx : x < 2 ^ (τ + 1)) :
    x &&& (2 ^ τ + (2 ^ τ - 2 ^ a)) = 2 ^ τ &&& (2 ^ τ + (2 ^ τ - 2 ^ a)) ↔ 2 ^ τ ≤ x ∧ x < 2 ^ τ + 2 ^ a := by
  have hc : 2 ^ τ < 2 ^ (τ + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  rw [lane_block x _ a τ ha hx hc]
  have e : 2 ^ τ = 2 ^ (τ - a) * 2 ^ a := by rw [← pow_add, Nat.sub_add_cancel ha]
  rw [e, Nat.mul_div_cancel _ (Nat.two_pow_pos a), Nat.div_eq_iff (Nat.two_pow_pos a)]
  have := Nat.two_pow_pos a
  omega

theorem lane_dummy (x n τ : ℕ) (hn : n < τ) (hx : x < 2 ^ (τ + 1)) :
    x &&& (2 ^ τ + (2 ^ τ - 2 ^ n)) = (2 ^ τ + 2 ^ n) &&& (2 ^ τ + (2 ^ τ - 2 ^ n)) ↔
      2 ^ τ + 2 ^ n ≤ x ∧ x < 2 ^ τ + 2 ^ (n + 1) := by
  have hnτ : 2 ^ n < 2 ^ τ := Nat.pow_lt_pow_right (by norm_num) hn
  have hc : 2 ^ τ + 2 ^ n < 2 ^ (τ + 1) := by rw [pow_succ]; omega
  rw [lane_block x _ n τ hn.le hx hc]
  have e : 2 ^ τ + 2 ^ n = (2 ^ (τ - n) + 1) * 2 ^ n := by
    rw [Nat.add_mul, ← pow_add, Nat.sub_add_cancel hn.le, one_mul]
  rw [e, Nat.mul_div_cancel _ (Nat.two_pow_pos n), Nat.div_eq_iff (Nat.two_pow_pos n), ← e, pow_succ]
  have := Nat.two_pow_pos n
  omega

end Lanes


/-! ## Blocks: pairwise relations along lists whose keys increase block by block -/

namespace Blocks

variable {α : Type}

/-- `l` is pairwise `R`-related and every key lies in `[lo, hi)`. -/
def Blk (key : α → ℕ) (R : α → α → Prop) (lo hi : ℕ) (l : List α) : Prop :=
  l.Pairwise R ∧ ∀ a ∈ l, lo ≤ key a ∧ key a < hi

variable {key : α → ℕ} {R : α → α → Prop}

theorem Blk.app {lo m1 m2 hi : ℕ} {l1 l2 : List α} (h1 : Blk key R lo m1 l1) (h2 : Blk key R m2 hi l2)
    (hR : ∀ a b, key a < key b → R a b) (h12 : m1 ≤ m2) (hlo : lo ≤ m2) (hhi : m1 ≤ hi) :
    Blk key R lo hi (l1 ++ l2) := by
  refine ⟨List.pairwise_append.mpr ⟨h1.1, h2.1, fun a ha b hb => hR a b ?_⟩, fun a ha => ?_⟩
  · have := (h1.2 a ha).2; have := (h2.2 b hb).1; omega
  · rcases List.mem_append.mp ha with ha | ha
    · have := h1.2 a ha; omega
    · have := h2.2 a ha; omega

theorem Blk.single (a : α) (t : ℕ) (h : key a = t) : Blk key R t (t + 1) [a] :=
  ⟨List.pairwise_singleton _ _, fun b hb => by
    rw [List.mem_singleton.mp hb, h]; omega⟩

/-- A block of constant key `t`, indexed by `j < n`. -/
theorem Blk.mapConst (n t : ℕ) (C : ℕ → α) (hk : ∀ j, key (C j) = t) (hR : ∀ i j, i < j → R (C i) (C j)) :
    Blk key R t (t + 1) ((List.range n).map C) := by
  refine ⟨List.pairwise_map.mpr (List.pairwise_lt_range.imp fun h => hR _ _ h), fun a ha => ?_⟩
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp ha
  rw [hk]; omega

/-- A block whose key is `t + j` at index `j < n`. -/
theorem Blk.mapStep (n t : ℕ) (C : ℕ → α) (hk : ∀ j, key (C j) = t + j) (hR : ∀ a b, key a < key b → R a b) :
    Blk key R t (t + n) ((List.range n).map C) := by
  refine ⟨List.pairwise_map.mpr (List.pairwise_lt_range.imp fun h => hR _ _ (by rw [hk, hk]; omega)),
    fun a ha => ?_⟩
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ha
  rw [hk]; have := List.mem_range.mp hj; omega

/-- A two-level block whose key is `t + r` at index `(r, j)`, `r < n`, `j < m`. -/
theorem Blk.flatStep (n m t : ℕ) (C : ℕ → ℕ → α) (hk : ∀ r j, key (C r j) = t + r)
    (hR : ∀ a b, key a < key b → R a b) (hR' : ∀ r i j, i < j → R (C r i) (C r j)) :
    Blk key R t (t + n) ((List.range n).flatMap fun r => (List.range m).map (C r)) := by
  refine ⟨List.pairwise_flatMap.mpr ⟨fun r _ => List.pairwise_map.mpr
    (List.pairwise_lt_range.imp fun h => hR' _ _ _ h), ?_⟩, fun a ha => ?_⟩
  · refine List.pairwise_lt_range.imp fun {r r'} h => ?_
    intro x hx y hy
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hy
    exact hR _ _ (by rw [hk, hk]; omega)
  · obtain ⟨r, hr, hx⟩ := List.mem_flatMap.mp ha
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx
    rw [hk]; have := List.mem_range.mp hr; omega

/-- A two-level block of constant key `t`. -/
theorem Blk.flatConst (n m t : ℕ) (C : ℕ → ℕ → α) (hk : ∀ r j, key (C r j) = t)
    (hR : ∀ r r' i j, (r < r' ∨ (r = r' ∧ i < j)) → R (C r i) (C r' j)) :
    Blk key R t (t + 1) ((List.range n).flatMap fun r => (List.range m).map (C r)) := by
  refine ⟨List.pairwise_flatMap.mpr ⟨fun r _ => List.pairwise_map.mpr
    (List.pairwise_lt_range.imp fun h => hR _ _ _ _ (Or.inr ⟨rfl, h⟩)), ?_⟩, fun a ha => ?_⟩
  · refine List.pairwise_lt_range.imp fun {r r'} h => ?_
    intro x hx y hy
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hy
    exact hR _ _ _ _ (Or.inl h)
  · obtain ⟨r, -, hx⟩ := List.mem_flatMap.mp ha
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx
    rw [hk]; omega

end Blocks

end NearCubicGates.Adapters.RAMACSP
