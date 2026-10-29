import SourceAdapters.RAMACSP.EmbedCatalog
import SourceAdapters.RAMACSP.ConstraintEmit
import SourceAdapters.Routing.RoutingDisjoint

/-!
# Embedding theorem, part 3 (E2): the emitted terms have pairwise disjoint guards

Paper: the proof of `thm:embedding`: at every point of H at most one selector
is nonzero. Area separates routing and machine checks; roles separate local,
Booleanity, copy and boundary checks; stages separate time and sorted uses;
tags and bit indices separate equation instances. Shared boundary hosts use
disjoint FIRST/PREV, INPUT/DUMMY or EARLY/LAST lane conditions.

Consumer: `Routing.NormalizedEmission` (the `normalized_emission` field of the `AffineRouting` contract),
whose semantic half needs `DisjointTerms` of the emitted term list; used in the soundness direction of the embedding
theorem (`EmbedSound`).

Export: `ownItems_disjoint : DisjointTerms (termList (ownItems V r lam))` for `2 ≤ n ≤ t`.
-/

set_option autoImplicit false

noncomputable section

namespace NearCubicGates.Adapters.RAMACSP

open NearCubicGates.Adapters NearCubicGates.Adapters.RAMTrace Blocks Guards Lanes
open Routing Routing.Patterns

/-- Two items whose guards select no common cube point. -/
def ItemDisj {m : ℕ} {F : Type} (t t' : Pattern m × Routing.Expr F) : Prop :=
  ∀ v, ¬ (patternHolds t.1 v ∧ patternHolds t'.1 v)

theorem itemDisj_symm {m : ℕ} {F : Type} {t t' : Pattern m × Routing.Expr F} (h : ItemDisj t t') :
    ItemDisj t' t := fun v hv => h v ⟨hv.2, hv.1⟩

/-- Pairwise disjoint items give `DisjointTerms` of their term list. -/
theorem disjointTerms_of_pairwise {m : ℕ} {F : Type} [Field F] (items : List (Pattern m × Routing.Expr F))
    (h : items.Pairwise ItemDisj) : DisjointTerms (Circuit.termList items) := by
  intro i j hij v hv
  have hlen : (Circuit.termList items).length = items.length := by simp [Circuit.termList]
  have hi : i.val < items.length := hlen ▸ i.isLt
  have hj : j.val < items.length := hlen ▸ j.isLt
  have gi : (Circuit.termList items)[i].guard = items[i.val].1 := by
    rw [Fin.getElem_fin]; simp [Circuit.termList]
  have gj : (Circuit.termList items)[j].guard = items[j.val].1 := by
    rw [Fin.getElem_fin]; simp [Circuit.termList]
  rw [gi, gj] at hv
  have hne : i.val ≠ j.val := fun he => hij (Fin.ext he)
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact List.pairwise_iff_getElem.mp h _ _ hi hj hlt v hv
  · exact List.pairwise_iff_getElem.mp h _ _ hj hi hlt v ⟨hv.2, hv.1⟩

theorem pairwise_of_disjointTerms {m : ℕ} {F : Type} [Field F] (ts : List (Term m F)) (h : DisjointTerms ts) :
    ts.Pairwise (fun t t' => ∀ v, ¬ (patternHolds t.guard v ∧ patternHolds t'.guard v)) := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hlt v hv
  exact h ⟨i, hi⟩ ⟨j, hj⟩ (fun he => by have := congrArg Fin.val he; simp at this; omega) v hv

/-! ## Column codes and guard ranges -/

theorem col_ne {om : ℕ} {c c' : Cell} (hb : c.bit < 2 ^ om) (hb' : c'.bit < 2 ^ om)
    (h : (c.tag, c.bit) ≠ (c'.tag, c'.bit)) : c.col om ≠ c'.col om := by
  intro he
  obtain ⟨h1, h2⟩ := LayoutFacts.block_injective om _ _ _ _ hb hb' he
  exact h (by rw [h1, h2])

theorem guardOk_of (l : Layout) (om dt K V s : ℕ) (h : Cell) (hq : l.q = dt + om) (hK : K < 2 ^ l.k)
    (hV : V < 2 ^ l.k) (hs : s < 2 ^ l.ell) (hc : h.Ok om dt) : GuardOk l om K V s h :=
  ⟨hK, hV, hs, by rw [Layout.C, hq]; exact Cell.col_lt hc, hc.2.2.1, hc.2.2.2⟩

/-- The common setting of the machine items: `k = τ + 1` lanes, the column split `q = d + ω`, the stage room. -/
structure Setting (l : Layout) (om dt τ : ℕ) : Prop where
  hk : l.k = τ + 1
  hq : l.q = dt + om
  fin : 2 * l.k - 1 < 2 ^ l.ell

theorem Setting.stage0 {l : Layout} {om dt τ : ℕ} (_ : Setting l om dt τ) : 0 < 2 ^ l.ell := Nat.two_pow_pos _

theorem two_pow_succ' (n : ℕ) : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ]; ring

theorem pow_le_of_lt {a b : ℕ} (h : a < b) : 2 ^ (a + 1) ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) h

/-! ## Lane conflicts of the guard library -/

theorem tb_low (n b : ℕ) : (2 ^ n - 1).testBit b = decide (b < n) := Nat.testBit_two_pow_sub_one n b

theorem tb_pow (n b : ℕ) : (2 ^ n).testBit b = decide (n = b) := Nat.testBit_two_pow

theorem tb_lowTime (t τ b : ℕ) (ht : t < τ) :
    (2 ^ (t + 1) - 1 + 2 ^ τ).testBit b = (decide (b = τ) || decide (b < t + 1)) := by
  rw [Nat.add_comm, testBit_hi_add τ _ b (by have := pow_le_of_lt ht; have := Nat.two_pow_pos (t + 1); omega),
    tb_low]

theorem tb_early (b0 τ b : ℕ) (hb : b0 < τ) :
    (2 ^ τ + (2 ^ (b0 + 1) - 1)).testBit b = (decide (b = τ) || decide (b < b0 + 1)) := by
  rw [testBit_hi_add τ _ b (by have := pow_le_of_lt hb; have := Nat.two_pow_pos (b0 + 1); omega), tb_low]

theorem tb_block (n τ b : ℕ) (hn : n ≤ τ) :
    (2 ^ τ + (2 ^ τ - 2 ^ n)).testBit b = (decide (b = τ) || decide (n ≤ b ∧ b < τ)) := by
  rw [testBit_hi_add τ _ b (Nat.sub_lt (Nat.two_pow_pos τ) (Nat.two_pow_pos n)), testBit_range τ n b hn]

theorem tb_dummyV (n τ b : ℕ) (hn : n < τ) :
    (2 ^ τ + 2 ^ n).testBit b = (decide (b = τ) || decide (n = b)) := by
  rw [testBit_hi_add τ _ b (Nat.pow_lt_pow_right (by norm_num) hn), tb_pow]

theorem conflict_first_prevT (τ t : ℕ) (ht : t < τ) :
    LaneConflict (2 ^ (τ + 1) - 1) 0 (2 ^ (t + 1) - 1 + 2 ^ τ) (2 ^ t) :=
  ⟨t, by rw [tb_low]; simp; omega, by rw [tb_lowTime t τ t ht]; simp, by simp⟩

theorem conflict_prevT (τ t t' : ℕ) (ht : t < t') (ht' : t' < τ) :
    LaneConflict (2 ^ (t + 1) - 1 + 2 ^ τ) (2 ^ t) (2 ^ (t' + 1) - 1 + 2 ^ τ) (2 ^ t') :=
  ⟨t, by rw [tb_lowTime t τ t (by omega)]; simp, by rw [tb_lowTime t' τ t ht']; simp; omega,
    by simp [tb_pow]; omega⟩

theorem conflict_early (τ b b' : ℕ) (hb : b < b') (hb' : b' < τ) :
    LaneConflict (2 ^ τ + (2 ^ (b + 1) - 1)) (2 ^ b - 1) (2 ^ τ + (2 ^ (b' + 1) - 1)) (2 ^ b' - 1) :=
  ⟨b, by rw [tb_early b τ b (by omega)]; simp, by rw [tb_early b' τ b hb']; simp; omega,
    by simp; omega⟩

theorem conflict_early_last (τ b : ℕ) (hb : b < τ) :
    LaneConflict (2 ^ τ + (2 ^ (b + 1) - 1)) (2 ^ b - 1) (2 ^ (τ + 1) - 1) (2 ^ τ - 1) :=
  ⟨b, by rw [tb_early b τ b hb]; simp, by rw [tb_low]; simp; omega, by simp; omega⟩

theorem conflict_first_prev4 (k t : ℕ) (ht : t < k) :
    LaneConflict (2 ^ k - 1) 0 (2 ^ (t + 1) - 1) (2 ^ t) :=
  ⟨t, by rw [tb_low]; simp; omega, by rw [tb_low]; simp, by simp⟩

theorem conflict_prev4 (t t' : ℕ) (ht : t < t') :
    LaneConflict (2 ^ (t + 1) - 1) (2 ^ t) (2 ^ (t' + 1) - 1) (2 ^ t') :=
  ⟨t, by rw [tb_low]; simp, by rw [tb_low]; simp; omega, by simp [tb_pow]; omega⟩

theorem conflict_input_dummy (τ a i : ℕ) (hi : a + i < τ) :
    LaneConflict (2 ^ τ + (2 ^ τ - 2 ^ a)) (2 ^ τ) (2 ^ τ + (2 ^ τ - 2 ^ (a + i))) (2 ^ τ + 2 ^ (a + i)) :=
  ⟨a + i, by rw [tb_block a τ _ (by omega)]; simp; omega, by rw [tb_block (a + i) τ _ (by omega)]; simp; omega,
    by rw [tb_dummyV (a + i) τ _ hi, tb_pow]; simp; omega⟩

theorem conflict_dummy (τ a i i' : ℕ) (hi : i < i') (hi' : a + i' < τ) :
    LaneConflict (2 ^ τ + (2 ^ τ - 2 ^ (a + i))) (2 ^ τ + 2 ^ (a + i)) (2 ^ τ + (2 ^ τ - 2 ^ (a + i')))
      (2 ^ τ + 2 ^ (a + i')) :=
  ⟨a + i', by rw [tb_block (a + i) τ _ (by omega)]; simp; omega, by rw [tb_block (a + i') τ _ (by omega)]; simp; omega,
    by rw [tb_dummyV (a + i) τ _ (by omega), tb_dummyV (a + i') τ _ hi']; simp; omega⟩

/-! ## Mask ranges -/

section Ranges

variable (τ : ℕ)

theorem rk_time : 2 ^ τ < 2 ^ (τ + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
theorem rk_zero : 0 < 2 ^ (τ + 1) := Nat.two_pow_pos _
theorem rk_first : 2 ^ (τ + 1) - 1 < 2 ^ (τ + 1) := Nat.sub_lt (Nat.two_pow_pos _) (by norm_num)
theorem rk_last : 2 ^ τ - 1 < 2 ^ (τ + 1) := lt_of_le_of_lt (Nat.sub_le _ _) (rk_time τ)
theorem rk_pow (t : ℕ) (ht : t ≤ τ) : 2 ^ t < 2 ^ (τ + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
theorem rk_powSub (t : ℕ) (ht : t ≤ τ) : 2 ^ t - 1 < 2 ^ (τ + 1) := lt_of_le_of_lt (Nat.sub_le _ _) (rk_pow τ t ht)
theorem rk_lowTime (t : ℕ) (ht : t < τ) : 2 ^ (t + 1) - 1 + 2 ^ τ < 2 ^ (τ + 1) := by
  have := pow_le_of_lt ht; have := two_pow_succ' τ; have := Nat.two_pow_pos (t + 1); omega
theorem rk_early (b : ℕ) (hb : b < τ) : 2 ^ τ + (2 ^ (b + 1) - 1) < 2 ^ (τ + 1) := by
  have := pow_le_of_lt hb; have := two_pow_succ' τ; have := Nat.two_pow_pos (b + 1); omega
theorem rk_low (t : ℕ) (ht : t < τ + 1) : 2 ^ (t + 1) - 1 < 2 ^ (τ + 1) := by
  have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show t + 1 ≤ τ + 1 by omega)
  have := Nat.two_pow_pos (t + 1); omega
theorem rk_block (n : ℕ) : 2 ^ τ + (2 ^ τ - 2 ^ n) < 2 ^ (τ + 1) := by
  have := two_pow_succ' τ; have := Nat.two_pow_pos n; have := Nat.two_pow_pos τ; omega
theorem rk_dummyV (n : ℕ) (hn : n < τ) : 2 ^ τ + 2 ^ n < 2 ^ (τ + 1) := by
  have := two_pow_succ' τ; have := Nat.pow_lt_pow_right (show 1 < 2 by norm_num) hn; omega

end Ranges


/-! ## Signatures: a guard with a known stage and host class -/

section Sig

variable {F : Type} (l : Layout) (om : ℕ)

/-- The item's guard is a well-formed machine guard at stage `s` whose host satisfies `P`. -/
def Sig (t : Pattern l.m × Routing.Expr F) (s : ℕ) (P : Cell → Prop) : Prop :=
  ∃ K V h, t.1 = guardAt l om K V s h ∧ GuardOk l om K V s h ∧ P h

variable {l om}

theorem disj_of_sig {t t' : Pattern l.m × Routing.Expr F} {s s' : ℕ} {P P' : Cell → Prop}
    (ht : Sig l om t s P) (ht' : Sig l om t' s' P')
    (hd : ∀ h h', P h → P' h' → s ≠ s' ∨ h.col om ≠ h'.col om ∨ h.role ≠ h'.role) : ItemDisj t t' := by
  obtain ⟨K, V, h, e, g, p⟩ := ht
  obtain ⟨K', V', h', e', g', p'⟩ := ht'
  intro v
  rw [e, e']
  rcases hd h h' p p' with h1 | h1 | h1
  · exact guardAt_disjoint l om K V s K' V' s' h h' g g' (Or.inl h1) v
  · exact guardAt_disjoint l om K V s K' V' s' h h' g g' (Or.inr (Or.inl h1)) v
  · exact guardAt_disjoint l om K V s K' V' s' h h' g g' (Or.inr (Or.inr (Or.inl h1))) v

theorem disj_same_host {K V K' V' s : ℕ} {h : Cell} {E E' : Routing.Expr F} (g : GuardOk l om K V s h)
    (g' : GuardOk l om K' V' s h) (hc : LaneConflict K V K' V') :
    ItemDisj (guardAt l om K V s h, E) (guardAt l om K' V' s h, E') := fun v =>
  guardAt_disjoint l om K V s K' V' s h h g g' (Or.inr (Or.inr (Or.inr (Or.inr hc)))) v

theorem disj_host {K V K' V' s : ℕ} {h h' : Cell} {E E' : Routing.Expr F} (g : GuardOk l om K V s h)
    (g' : GuardOk l om K' V' s h') (hc : h.col om ≠ h'.col om) :
    ItemDisj (guardAt l om K V s h, E) (guardAt l om K' V' s h', E') := fun v =>
  guardAt_disjoint l om K V s K' V' s h h' g g' (Or.inr (Or.inl hc)) v

/-- The eight regions of the machine items (`app:affine-embedding` census): `(stage, role)` and, for role `7`, the column class. -/
def InReg (fin : ℕ) (t : Pattern l.m × Routing.Expr F) : ℕ → Prop
  | 0 => Sig l om t 0 fun h => h.area = 1 ∧ h.role = 2
  | 1 => Sig l om t 0 fun h => h.area = 1 ∧ (h.role = 3 ∨ h.role = 4)
  | 2 => Sig l om t 0 fun h => h.area = 1 ∧ h.role = 5
  | 3 => Sig l om t 0 fun h => h.area = 1 ∧ h.role = 7 ∧ h.col om = 2 ^ om * 7
  | 4 => Sig l om t fin fun h => h.area = 1 ∧ h.role = 2
  | 5 => Sig l om t fin fun h => h.area = 1 ∧ (h.role = 3 ∨ h.role = 4)
  | 6 => Sig l om t fin fun h => h.area = 1 ∧ h.role = 6
  | 7 => Sig l om t 0 fun h => h.area = 1 ∧ h.role = 7 ∧ h.col om < 2 ^ om * 7
  | _ => False

theorem inReg_disj {fin : ℕ} (hfin : 0 < fin) {t t' : Pattern l.m × Routing.Expr F} {i j : ℕ}
    (hi : InReg (l := l) (om := om) fin t i) (hj : InReg (l := l) (om := om) fin t' j) (hij : i < j) :
    ItemDisj t t' := by
  have hj8 : j < 8 := by
    rcases j with _ | _ | _ | _ | _ | _ | _ | _ | j
    all_goals first | omega | exact absurd hj id
  interval_cases j <;> interval_cases i <;>
    exact disj_of_sig hi hj fun h h' p p' => by
      first
      | exact Or.inl (by omega)
      | exact Or.inr (Or.inr (by omega))
      | exact Or.inr (Or.inl (by omega))

end Sig

/-! ## Blocks with a member predicate -/

section BlkG

variable {α : Type}

/-- Pairwise `R`, and every member lies in a region `i ∈ [lo, hi)` (`G a i`). -/
def BlkG (G : α → ℕ → Prop) (R : α → α → Prop) (lo hi : ℕ) (l : List α) : Prop :=
  l.Pairwise R ∧ ∀ a ∈ l, ∃ i, lo ≤ i ∧ i < hi ∧ G a i

variable {G : α → ℕ → Prop} {R : α → α → Prop}

theorem BlkG.app {lo m1 m2 hi : ℕ} {l1 l2 : List α} (h1 : BlkG G R lo m1 l1) (h2 : BlkG G R m2 hi l2)
    (hR : ∀ a b i j, G a i → G b j → i < j → R a b) (h12 : m1 ≤ m2) (hlo : lo ≤ m2) (hhi : m1 ≤ hi) :
    BlkG G R lo hi (l1 ++ l2) := by
  refine ⟨List.pairwise_append.mpr ⟨h1.1, h2.1, fun a ha b hb => ?_⟩, fun a ha => ?_⟩
  · obtain ⟨i, -, hi, gi⟩ := h1.2 a ha
    obtain ⟨j, hj, -, gj⟩ := h2.2 b hb
    exact hR a b i j gi gj (by omega)
  · rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨i, h1', h2', g⟩ := h1.2 a ha; exact ⟨i, h1', by omega, g⟩
    · obtain ⟨i, h1', h2', g⟩ := h2.2 a ha; exact ⟨i, by omega, h2', g⟩

theorem BlkG.of {i : ℕ} {l : List α} (h : l.Pairwise R) (hg : ∀ a ∈ l, G a i) : BlkG G R i (i + 1) l :=
  ⟨h, fun a ha => ⟨i, le_rfl, by omega, hg a ha⟩⟩

end BlkG


/-! ## The eight machine blocks -/

/-- The setting of the machine items: lanes `k = τ + 1`, columns `q = d + ω`, the final stage in range, the RAM
dimensions (`K` registers, code length `L ≥ 1`, word width `w = 2^ω > τ`, `Ftags ≤ 2^d`) and `a ≤ τ`. -/
structure Ctx (l : Layout) (om dt K L τ a : ℕ) (M : ACSP.Ram) : Prop where
  hk : l.k = τ + 1
  hq : l.q = dt + om
  hfin : 2 * l.k - 1 < 2 ^ l.ell
  hK : (dims M τ).K = K
  hL : (dims M τ).L = L
  hw : (dims M τ).w = 2 ^ om
  hτw : τ < (dims M τ).w
  hF : 32 + 3 * K + 2 * L ≤ 2 ^ dt
  hL1 : 1 ≤ L
  ha : a ≤ τ

theorem dims_β_le (M : ACSP.Ram) (τ : ℕ) : (dims M τ).β ≤ (dims M τ).τ := Nat.sub_le _ _

section Hosts

variable {F : Type} {l : Layout} {om : ℕ}

/-- Membership in a host's lane-case list `x :: map` (all at host `h`, well-formed). -/
theorem mem_hostList {s : ℕ} {h : Cell} {K0 V0 : ℕ} {E0 : Routing.Expr F} {n : ℕ} {Kf Vf : ℕ → ℕ}
    {Ef : ℕ → Routing.Expr F} (g0 : GuardOk l om K0 V0 s h) (gf : ∀ t < n, GuardOk l om (Kf t) (Vf t) s h)
    (x : Pattern l.m × Routing.Expr F)
    (hx : x ∈ (guardAt l om K0 V0 s h, E0) :: (List.range n).map fun t => (guardAt l om (Kf t) (Vf t) s h, Ef t)) :
    ∃ K V, x.1 = guardAt l om K V s h ∧ GuardOk l om K V s h := by
  rcases List.mem_cons.mp hx with rfl | hx
  · exact ⟨_, _, rfl, g0⟩
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
    exact ⟨_, _, rfl, gf t (List.mem_range.mp ht)⟩

/-- The lane cases of one host: a first case and `n` indexed cases, pairwise in conflict. -/
theorem pw_hostList {s : ℕ} {h : Cell} {K0 V0 : ℕ} {E0 : Routing.Expr F} {n : ℕ} {Kf Vf : ℕ → ℕ}
    {Ef : ℕ → Routing.Expr F} (g0 : GuardOk l om K0 V0 s h) (gf : ∀ t < n, GuardOk l om (Kf t) (Vf t) s h)
    (h0 : ∀ t < n, LaneConflict K0 V0 (Kf t) (Vf t))
    (h1 : ∀ t t', t < t' → t' < n → LaneConflict (Kf t) (Vf t) (Kf t') (Vf t')) :
    ((guardAt l om K0 V0 s h, E0) :: (List.range n).map fun t => (guardAt l om (Kf t) (Vf t) s h, Ef t)).Pairwise
      ItemDisj := by
  refine List.pairwise_cons.mpr ⟨fun y hy => ?_, List.pairwise_map.mpr
    ((List.Pairwise.and_mem.mp List.pairwise_lt_range).imp fun {t t'} ht => ?_)⟩
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hy
    have ht := List.mem_range.mp ht
    exact disj_same_host g0 (gf t ht) (h0 t ht)
  · obtain ⟨ha, hb, hlt⟩ := ht
    have ha := List.mem_range.mp ha
    have hb := List.mem_range.mp hb
    exact disj_same_host (gf t ha) (gf t' hb) (h1 t t' hlt hb)

/-- Cross-host disjointness of the lane-case lists of two hosts with different columns. -/
theorem disj_hostLists {s : ℕ} {h h' : Cell} (hc : h.col om ≠ h'.col om) (x y : Pattern l.m × Routing.Expr F)
    (hx : ∃ K V, x.1 = guardAt l om K V s h ∧ GuardOk l om K V s h)
    (hy : ∃ K V, y.1 = guardAt l om K V s h' ∧ GuardOk l om K V s h') : ItemDisj x y := by
  obtain ⟨K, V, e, g⟩ := hx
  obtain ⟨K', V', e', g'⟩ := hy
  intro v
  rw [e, e']
  exact guardAt_disjoint l om _ _ _ _ _ _ _ _ g g' (Or.inr (Or.inl hc)) v

theorem mem_prevs {w τ' : ℕ} {s : RecSlot}
    (hs : s ∈ [RecField.va, .ad, .ts, .ph, .rgn, .act].flatMap fun f => (List.range (f.width w τ')).map fun j => (f, j)) :
    s.1 ≠ .st ∧ s.2 < s.1.width w τ' := by
  obtain ⟨f, hf, hx⟩ := List.mem_flatMap.mp hs
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
  refine ⟨?_, List.mem_range.mp hj⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem pairwise_of_length_le_one {α : Type} {R : α → α → Prop} (l : List α) (h : l.length ≤ 1) : l.Pairwise R := by
  rcases l with _ | ⟨a, _ | ⟨b, l⟩⟩
  · exact List.Pairwise.nil
  · exact List.pairwise_singleton _ _
  · simp at h

theorem recCell_tag_le (s : RecSlot) : (recCell s).tag ≤ 6 := by
  obtain ⟨f, j⟩ := s; cases f <;> simp [recCell, RecField.tag]

end Hosts

section Blocks8

variable {F : Type} {l : Layout} {om dt K L τ a : ℕ} {M : ACSP.Ram} (c : Ctx l om dt K L τ a M)
include c

theorem Ctx.hw1 : 1 ≤ (dims M τ).w := by have := c.hτw; omega
theorem Ctx.hκ : (dims M τ).κ ≤ 3 * (dims M τ).w := by
  have := c.hτw; show (dims M τ).w + τ + 2 ≤ 3 * (dims M τ).w; omega
theorem Ctx.fin_pos : 0 < 2 * l.k - 1 := by have := c.hk; omega
theorem Ctx.lt_k (x : ℕ) (hx : x < 2 ^ (τ + 1)) : x < 2 ^ l.k := by rw [c.hk]; exact hx

/-- The region predicate of the machine items. -/
abbrev Reg (l : Layout) (om : ℕ) (t : Pattern l.m × Routing.Expr F) (i : ℕ) : Prop :=
  InReg (l := l) (om := om) (2 * l.k - 1) t i

/-- Block 0: the TIME templates (stage `0`, role `2`, `TIME`). -/
theorem blk_te (E : TEq → Routing.Expr F) :
    BlkG (Reg l om) ItemDisj 0 1
      ((timeEqList (dims M τ)).map fun q => (guardAt l om (2 ^ τ) 0 0 ⟨tTag K L q, tBit q, 2, 1⟩, E q)) := by
  have ok := tHost_ok (dims M τ) K L om dt c.hK c.hL c.hw c.hτw (dims_β_le M τ) c.hF
  have g : ∀ q, q.Active (dims M τ) → GuardOk l om (2 ^ τ) 0 0 ⟨tTag K L q, tBit q, 2, 1⟩ := fun q hq =>
    guardOk_of l om dt _ _ _ _ c.hq (c.lt_k _ (rk_time τ)) (c.lt_k _ (rk_zero τ)) (Nat.two_pow_pos _) (ok q hq)
  refine BlkG.of ?_ fun t ht => ?_
  · have hb := (timeEqList_blk (dims M τ) (by rw [c.hL]; exact c.hL1)).1
    rw [c.hK, c.hL] at hb
    refine List.pairwise_map.mpr (hb.imp_of_mem fun {q q'} hq hq' hne => ?_)
    have a1 := mem_timeEqList _ q hq
    have a2 := mem_timeEqList _ q' hq'
    exact disj_host (g q a1) (g q' a2) (col_ne (ok q a1).1 (ok q' a2).1 hne)
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ht
    exact ⟨_, _, _, rfl, g q (mem_timeEqList _ q hq), rfl, rfl⟩

/-- Block 1: Booleanity of the time-row slots (stage `0`, roles `3`/`4`, `TIME`). -/
theorem blk_tb (E : TSlot → Routing.Expr F) :
    BlkG (Reg l om) ItemDisj 1 2
      ((timeSlotList (dims M τ)).map fun s =>
        (guardAt l om (2 ^ τ) 0 0 ⟨(tCell K L s).tag, (tCell K L s).bit, (tCell K L s).role + 3, 1⟩, E s)) := by
  have ok := tCell_ok (dims M τ) K L om dt c.hK c.hL c.hw c.hτw (dims_β_le M τ) c.hF
  have hok : ∀ s, s.Active (dims M τ) →
      (⟨(tCell K L s).tag, (tCell K L s).bit, (tCell K L s).role + 3, 1⟩ : Cell).Ok om dt := fun s hs =>
    ⟨(ok s hs).1, (ok s hs).2.1, by have := (tCell_role K L s).1; show (tCell K L s).role + 3 < 8; omega,
      show (1 : ℕ) < 2 by norm_num⟩
  have g : ∀ s, s.Active (dims M τ) →
      GuardOk l om (2 ^ τ) 0 0 ⟨(tCell K L s).tag, (tCell K L s).bit, (tCell K L s).role + 3, 1⟩ := fun s hs =>
    guardOk_of l om dt _ _ _ _ c.hq (c.lt_k _ (rk_time τ)) (c.lt_k _ (rk_zero τ)) (Nat.two_pow_pos _) (hok s hs)
  refine BlkG.of ?_ fun t ht => ?_
  · refine List.pairwise_map.mpr ((timeSlotList_nodup _).pairwise_of_forall_ne fun s hs s' hs' hne => ?_)
    have a1 := mem_timeSlotList _ s hs
    have a2 := mem_timeSlotList _ s' hs'
    intro v
    by_cases hc : (tCell K L s).tag = (tCell K L s').tag ∧ (tCell K L s).bit = (tCell K L s').bit
    · have hr : (tCell K L s).role ≠ (tCell K L s').role := fun hr =>
        hne (tCell_inj _ K L c.hK c.hL s s' a1 a2 hc.1 hc.2 hr)
      exact guardAt_disjoint l om _ _ _ _ _ _ _ _ (g s a1) (g s' a2)
        (Or.inr (Or.inr (Or.inl (by show (tCell K L s).role + 3 ≠ (tCell K L s').role + 3; omega)))) v
    · have hcol := col_ne (om := om) (c := ⟨(tCell K L s).tag, (tCell K L s).bit, (tCell K L s).role + 3, 1⟩)
        (c' := ⟨(tCell K L s').tag, (tCell K L s').bit, (tCell K L s').role + 3, 1⟩) (hok s a1).1 (hok s' a2).1
        (fun he => hc (by simp only [Prod.mk.injEq] at he; exact he))
      exact guardAt_disjoint l om _ _ _ _ _ _ _ _ (g s a1) (g s' a2) (Or.inr (Or.inl hcol)) v
  · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
    exact ⟨_, _, _, rfl, g s (mem_timeSlotList _ s hs), rfl,
      by have := (tCell_role K L s).1; show (tCell K L s).role + 3 = 3 ∨ (tCell K L s).role + 3 = 4; omega⟩

/-- Block 2: the time copies (B1) at the first lane and (B2) from the previous lane (stage `0`, role `5`). -/
theorem blk_cp (E1 : TCopy → Routing.Expr F) (E2 : TCopy → ℕ → Routing.Expr F) :
    BlkG (Reg l om) ItemDisj 2 3
      ((copyList (dims M τ)).flatMap fun cp =>
        (guardAt l om (2 ^ l.k - 1) 0 0 ⟨(dstCell K L cp).tag, (dstCell K L cp).bit, 5, 1⟩, E1 cp) ::
          (List.range τ).map fun t =>
            (guardAt l om (2 ^ (t + 1) - 1 + 2 ^ τ) (2 ^ t) 0 ⟨(dstCell K L cp).tag, (dstCell K L cp).bit, 5, 1⟩,
              E2 cp t)) := by
  have ok := dstCell_ok (dims M τ) K L om dt c.hK c.hL c.hw c.hτw (dims_β_le M τ) c.hF
  have hok : ∀ cp, cp.Active (dims M τ) →
      (⟨(dstCell K L cp).tag, (dstCell K L cp).bit, 5, 1⟩ : Cell).Ok om dt := fun cp h =>
    ⟨(ok cp h).1, (ok cp h).2.1, show (5 : ℕ) < 8 by norm_num, show (1 : ℕ) < 2 by norm_num⟩
  have hk1 : 2 ^ l.k - 1 < 2 ^ l.k := by rw [c.hk]; exact rk_first τ
  have g0 : ∀ cp, cp.Active (dims M τ) →
      GuardOk l om (2 ^ l.k - 1) 0 0 ⟨(dstCell K L cp).tag, (dstCell K L cp).bit, 5, 1⟩ := fun cp h =>
    guardOk_of l om dt _ _ _ _ c.hq hk1 (c.lt_k _ (rk_zero τ)) (Nat.two_pow_pos _) (hok cp h)
  have gf : ∀ cp, cp.Active (dims M τ) → ∀ t < τ,
      GuardOk l om (2 ^ (t + 1) - 1 + 2 ^ τ) (2 ^ t) 0 ⟨(dstCell K L cp).tag, (dstCell K L cp).bit, 5, 1⟩ :=
    fun cp h t ht => guardOk_of l om dt _ _ _ _ c.hq (c.lt_k _ (rk_lowTime τ t ht))
      (c.lt_k _ (rk_pow τ t ht.le)) (Nat.two_pow_pos _) (hok cp h)
  have hk2 : 2 ^ l.k - 1 = 2 ^ (τ + 1) - 1 := by rw [c.hk]
  refine BlkG.of (List.pairwise_flatMap.mpr ⟨fun cp hcp => ?_, ?_⟩) fun t ht => ?_
  · have a := mem_copyList _ cp hcp
    exact pw_hostList (g0 cp a) (gf cp a) (fun t ht => by rw [hk2]; exact conflict_first_prevT τ t ht)
      (fun t t' h h' => conflict_prevT τ t t' h h')
  · refine (copyList_nodup _).pairwise_of_forall_ne fun cp hcp cp' hcp' hne x hx y hy => ?_
    have a1 := mem_copyList _ cp hcp
    have a2 := mem_copyList _ cp' hcp'
    refine disj_hostLists (s := 0) ?_ x y (mem_hostList (g0 cp a1) (gf cp a1) x hx)
      (mem_hostList (g0 cp' a2) (gf cp' a2) y hy)
    refine col_ne (hok cp a1).1 (hok cp' a2).1 fun he => hne ?_
    simp only [Prod.mk.injEq] at he
    exact dstCell_inj _ K L c.hK c.hL cp cp' a1 a2 he.1 he.2
  · obtain ⟨cp, hcp, hx⟩ := List.mem_flatMap.mp ht
    have a := mem_copyList _ cp hcp
    obtain ⟨K', V', e, g⟩ := mem_hostList (g0 cp a) (gf cp a) t hx
    exact ⟨K', V', _, e, g, rfl, rfl⟩

/-- Block 3: the time halt (B2 `e(Out) = 0` on `EARLY_TIME`, B3 `e(Acc) = 1` on `LAST_TIME`; stage `0`, role `7`,
tag `7`). -/
theorem blk_b3 (E1 : ℕ → Routing.Expr F) (E2 : Routing.Expr F) :
    BlkG (Reg l om) ItemDisj 3 4
      (((List.range τ).map fun b => (guardAt l om (2 ^ τ + (2 ^ (b + 1) - 1)) (2 ^ b - 1) 0 ⟨7, 0, 7, 1⟩, E1 b)) ++
        [(guardAt l om (2 ^ l.k - 1) (2 ^ τ - 1) 0 ⟨7, 0, 7, 1⟩, E2)]) := by
  have hok : (⟨7, 0, 7, 1⟩ : Cell).Ok om dt :=
    ⟨Nat.two_pow_pos _, show 7 < 2 ^ dt by have := c.hF; omega, show (7 : ℕ) < 8 by norm_num,
      show (1 : ℕ) < 2 by norm_num⟩
  have hk1 : 2 ^ l.k - 1 < 2 ^ l.k := by rw [c.hk]; exact rk_first τ
  have gL : GuardOk l om (2 ^ l.k - 1) (2 ^ τ - 1) 0 ⟨7, 0, 7, 1⟩ :=
    guardOk_of l om dt _ _ _ _ c.hq hk1 (c.lt_k _ (rk_last τ)) (Nat.two_pow_pos _) hok
  have gE : ∀ b < τ, GuardOk l om (2 ^ τ + (2 ^ (b + 1) - 1)) (2 ^ b - 1) 0 ⟨7, 0, 7, 1⟩ := fun b hb =>
    guardOk_of l om dt _ _ _ _ c.hq (c.lt_k _ (rk_early τ b hb)) (c.lt_k _ (rk_powSub τ b hb.le))
      (Nat.two_pow_pos _) hok
  have hk2 : 2 ^ l.k - 1 = 2 ^ (τ + 1) - 1 := by rw [c.hk]
  have hcol : (⟨7, 0, 7, 1⟩ : Cell).col om = 2 ^ om * 7 := by simp [Cell.col]
  refine BlkG.of (List.pairwise_append.mpr ⟨List.pairwise_map.mpr
    ((List.Pairwise.and_mem.mp List.pairwise_lt_range).imp fun {b b'} h => ?_),
    List.pairwise_singleton _ _, fun x hx y hy => ?_⟩) fun t ht => ?_
  · obtain ⟨h1, h2, hlt⟩ := h
    exact disj_same_host (gE b (List.mem_range.mp h1)) (gE b' (List.mem_range.mp h2))
      (conflict_early τ b b' hlt (List.mem_range.mp h2))
  · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
    rw [List.mem_singleton.mp hy]
    exact disj_same_host (gE b (List.mem_range.mp hb)) gL
      (by rw [hk2]; exact conflict_early_last τ b (List.mem_range.mp hb))
  · rcases List.mem_append.mp ht with ht | ht
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ht
      exact ⟨_, _, _, rfl, gE b (List.mem_range.mp hb), rfl, rfl, hcol⟩
    · rw [List.mem_singleton.mp ht]
      exact ⟨_, _, _, rfl, gL, rfl, rfl, hcol⟩


/-- Block 4: the SORT templates (final stage, role `2`, every lane). -/
theorem blk_se (E : SEq → Routing.Expr F) :
    BlkG (Reg l om) ItemDisj 4 5
      ((sortEqList (dims M τ)).map fun q => (guardAt l om 0 0 (2 * l.k - 1) ⟨sTag M.w q, sBit M.w q, 2, 1⟩, E q)) := by
  have ok := sHost_ok (dims M τ) K L om dt c.hK c.hL c.hw c.hτw c.hF
  have g : ∀ q, q.Active (dims M τ) → GuardOk l om 0 0 (2 * l.k - 1) ⟨sTag M.w q, sBit M.w q, 2, 1⟩ :=
    fun q hq => guardOk_of l om dt _ _ _ _ c.hq (Nat.two_pow_pos _) (Nat.two_pow_pos _) c.hfin (ok q hq)
  refine BlkG.of ?_ fun t ht => ?_
  · have hb := (sortEqList_blk (dims M τ) c.hw1 c.hκ).1
    refine List.pairwise_map.mpr (hb.imp_of_mem fun {q q'} hq hq' hne => ?_)
    have a1 := mem_sortEqList _ q hq
    have a2 := mem_sortEqList _ q' hq'
    exact disj_host (g q a1) (g q' a2) (col_ne (ok q a1).1 (ok q' a2).1 hne)
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ht
    exact ⟨_, _, _, rfl, g q (mem_sortEqList _ q hq), rfl, rfl⟩

/-- Block 5: Booleanity of the sorted slots (final stage, roles `3`/`4`). -/
theorem blk_sb (E : SSlot → Routing.Expr F) :
    BlkG (Reg l om) ItemDisj 5 6
      ((sortSlotList (dims M τ)).map fun s =>
        (guardAt l om 0 0 (2 * l.k - 1) ⟨(sCell M.w s).tag, (sCell M.w s).bit, (sCell M.w s).role + 3, 1⟩, E s)) := by
  have ok := sCell_ok (dims M τ) K L om dt c.hK c.hL c.hw c.hτw c.hF
  have hok : ∀ s, s.Active (dims M τ) →
      (⟨(sCell M.w s).tag, (sCell M.w s).bit, (sCell M.w s).role + 3, 1⟩ : Cell).Ok om dt := fun s hs =>
    ⟨(ok s hs).1, (ok s hs).2.1, by have := (sCell_role M.w s).1; show (sCell M.w s).role + 3 < 8; omega,
      show (1 : ℕ) < 2 by norm_num⟩
  have g : ∀ s, s.Active (dims M τ) →
      GuardOk l om 0 0 (2 * l.k - 1) ⟨(sCell M.w s).tag, (sCell M.w s).bit, (sCell M.w s).role + 3, 1⟩ :=
    fun s hs => guardOk_of l om dt _ _ _ _ c.hq (Nat.two_pow_pos _) (Nat.two_pow_pos _) c.hfin (hok s hs)
  refine BlkG.of ?_ fun t ht => ?_
  · have hb := (sortSlotList_blk (dims M τ) c.hw1 c.hκ).1
    refine List.pairwise_map.mpr (hb.imp_of_mem fun {s s'} hs hs' hne => ?_)
    have a1 := mem_sortSlotList _ s hs
    have a2 := mem_sortSlotList _ s' hs'
    exact disj_host (g s a1) (g s' a2) (col_ne (hok s a1).1 (hok s' a2).1 hne)
  · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
    exact ⟨_, _, _, rfl, g s (mem_sortSlotList _ s hs), rfl,
      by have := (sCell_role M.w s).1; show (sCell M.w s).role + 3 = 3 ∨ (sCell M.w s).role + 3 = 4; omega⟩

/-- Block 6: the sorted `PREV` copies (B4: sentinel on `FIRST`, predecessor on `PREV_t`; final stage, role `6`). -/
theorem blk_b4 (E1 : RecSlot → Routing.Expr F) (E2 : RecSlot → ℕ → Routing.Expr F) :
    BlkG (Reg l om) ItemDisj 6 7
      (([RecField.va, .ad, .ts, .ph, .rgn, .act].flatMap fun f =>
          (List.range (f.width (dims M τ).w (dims M τ).τ)).map fun j => (f, j)).flatMap fun s =>
        (guardAt l om (2 ^ l.k - 1) 0 (2 * l.k - 1)
          ⟨(sCell M.w (.prev s.1 s.2)).tag, (sCell M.w (.prev s.1 s.2)).bit, 6, 1⟩, E1 s) ::
          (List.range l.k).map fun t =>
            (guardAt l om (2 ^ (t + 1) - 1) (2 ^ t) (2 * l.k - 1)
              ⟨(sCell M.w (.prev s.1 s.2)).tag, (sCell M.w (.prev s.1 s.2)).bit, 6, 1⟩, E2 s t)) := by
  have ok := sCell_ok (dims M τ) K L om dt c.hK c.hL c.hw c.hτw c.hF
  have hok : ∀ s : RecSlot, s.1 ≠ .st → s.2 < s.1.width (dims M τ).w (dims M τ).τ →
      (⟨(sCell M.w (.prev s.1 s.2)).tag, (sCell M.w (.prev s.1 s.2)).bit, 6, 1⟩ : Cell).Ok om dt :=
    fun s h1 h2 => ⟨(ok _ (show (SSlot.prev s.1 s.2).Active (dims M τ) from ⟨h1, h2⟩)).1,
      (ok _ (show (SSlot.prev s.1 s.2).Active (dims M τ) from ⟨h1, h2⟩)).2.1, show (6 : ℕ) < 8 by norm_num,
      show (1 : ℕ) < 2 by norm_num⟩
  have hk1 : 2 ^ l.k - 1 < 2 ^ l.k := Nat.sub_lt (Nat.two_pow_pos _) (by norm_num)
  have hkt : ∀ t < l.k, 2 ^ (t + 1) - 1 < 2 ^ l.k ∧ 2 ^ t < 2 ^ l.k := fun t ht =>
    ⟨by have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show t + 1 ≤ l.k by omega)
        have := Nat.two_pow_pos (t + 1); omega,
      Nat.pow_lt_pow_right (by norm_num) ht⟩
  have g0 : ∀ s : RecSlot, s.1 ≠ .st → s.2 < s.1.width (dims M τ).w (dims M τ).τ →
      GuardOk l om (2 ^ l.k - 1) 0 (2 * l.k - 1)
        ⟨(sCell M.w (.prev s.1 s.2)).tag, (sCell M.w (.prev s.1 s.2)).bit, 6, 1⟩ := fun s h1 h2 =>
    guardOk_of l om dt _ _ _ _ c.hq hk1 (Nat.two_pow_pos _) c.hfin (hok s h1 h2)
  have gf : ∀ s : RecSlot, s.1 ≠ .st → s.2 < s.1.width (dims M τ).w (dims M τ).τ → ∀ t < l.k,
      GuardOk l om (2 ^ (t + 1) - 1) (2 ^ t) (2 * l.k - 1)
        ⟨(sCell M.w (.prev s.1 s.2)).tag, (sCell M.w (.prev s.1 s.2)).bit, 6, 1⟩ := fun s h1 h2 t ht =>
    guardOk_of l om dt _ _ _ _ c.hq (hkt t ht).1 (hkt t ht).2 c.hfin (hok s h1 h2)
  refine BlkG.of (List.pairwise_flatMap.mpr ⟨fun s hs => ?_, ?_⟩) fun t ht => ?_
  · obtain ⟨h1, h2⟩ := mem_prevs hs
    exact pw_hostList (g0 s h1 h2) (gf s h1 h2) (fun t ht => conflict_first_prev4 l.k t ht)
      (fun t t' h _ => conflict_prev4 t t' h)
  · refine (fields6_blk (fun f => f.width (dims M τ).w (dims M τ).τ)).1.imp_of_mem
      fun {s s'} hs hs' hne x hx y hy => ?_
    obtain ⟨h1, h2⟩ := mem_prevs hs
    obtain ⟨h1', h2'⟩ := mem_prevs hs'
    exact disj_hostLists (s := 2 * l.k - 1) (col_ne (hok s h1 h2).1 (hok s' h1' h2').1 hne) x y
      (mem_hostList (g0 s h1 h2) (gf s h1 h2) x hx) (mem_hostList (g0 s' h1' h2') (gf s' h1' h2') y hy)
  · obtain ⟨s, hs, hx⟩ := List.mem_flatMap.mp ht
    obtain ⟨h1, h2⟩ := mem_prevs hs
    obtain ⟨K', V', e, g⟩ := mem_hostList (g0 s h1 h2) (gf s h1 h2) t hx
    exact ⟨K', V', _, e, g, rfl, rfl⟩

/-- Block 7: the input/dummy records (B5: `INPUT` and `DUMMY_b` lane cases; stage `0`, role `7`, record tags). -/
theorem blk_b5 (Es : RecSlot → List (Routing.Expr F)) (hEs : ∀ s, (Es s).length ≤ 1) (Y : RecSlot → Routing.Expr F) :
    BlkG (Reg l om) ItemDisj 7 8
      ((recSlotList (dims M τ)).flatMap fun s =>
        ((Es s).map fun E => (guardAt l om (2 ^ τ + (2 ^ τ - 2 ^ a)) (2 ^ τ) 0
            ⟨(recCell s).tag, (recCell s).bit, 7, 1⟩, E)) ++
          ((List.range (τ - a)).map fun i => (guardAt l om (2 ^ τ + (2 ^ τ - 2 ^ (a + i))) (2 ^ τ + 2 ^ (a + i)) 0
            ⟨(recCell s).tag, (recCell s).bit, 7, 1⟩, Y s))) := by
  have ok := recCell_ok (dims M τ) K L om dt c.hK c.hL c.hw c.hτw (dims_β_le M τ) c.hF
  have hok : ∀ s : RecSlot, s.Active (dims M τ) → (⟨(recCell s).tag, (recCell s).bit, 7, 1⟩ : Cell).Ok om dt :=
    fun s hs => ⟨(ok s hs).1, (ok s hs).2.1, show (7 : ℕ) < 8 by norm_num, show (1 : ℕ) < 2 by norm_num⟩
  have gI : ∀ s : RecSlot, s.Active (dims M τ) →
      GuardOk l om (2 ^ τ + (2 ^ τ - 2 ^ a)) (2 ^ τ) 0 ⟨(recCell s).tag, (recCell s).bit, 7, 1⟩ := fun s hs =>
    guardOk_of l om dt _ _ _ _ c.hq (c.lt_k _ (rk_block τ a)) (c.lt_k _ (rk_time τ)) (Nat.two_pow_pos _) (hok s hs)
  have gD : ∀ s : RecSlot, s.Active (dims M τ) → ∀ i < τ - a,
      GuardOk l om (2 ^ τ + (2 ^ τ - 2 ^ (a + i))) (2 ^ τ + 2 ^ (a + i)) 0
        ⟨(recCell s).tag, (recCell s).bit, 7, 1⟩ := fun s hs i hi =>
    guardOk_of l om dt _ _ _ _ c.hq (c.lt_k _ (rk_block τ (a + i))) (c.lt_k _ (rk_dummyV τ (a + i) (by omega)))
      (Nat.two_pow_pos _) (hok s hs)
  have memI : ∀ s : RecSlot, s.Active (dims M τ) → ∀ x ∈
      ((Es s).map fun E => (guardAt l om (2 ^ τ + (2 ^ τ - 2 ^ a)) (2 ^ τ) 0
            ⟨(recCell s).tag, (recCell s).bit, 7, 1⟩, E)) ++
          ((List.range (τ - a)).map fun i => (guardAt l om (2 ^ τ + (2 ^ τ - 2 ^ (a + i))) (2 ^ τ + 2 ^ (a + i)) 0
            ⟨(recCell s).tag, (recCell s).bit, 7, 1⟩, Y s)),
      ∃ K V, x.1 = guardAt l om K V 0 ⟨(recCell s).tag, (recCell s).bit, 7, 1⟩ ∧
        GuardOk l om K V 0 ⟨(recCell s).tag, (recCell s).bit, 7, 1⟩ := by
    intro s hs x hx
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨E, -, rfl⟩ := List.mem_map.mp hx
      exact ⟨_, _, rfl, gI s hs⟩
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      exact ⟨_, _, rfl, gD s hs i (List.mem_range.mp hi)⟩
  refine BlkG.of (List.pairwise_flatMap.mpr ⟨fun s hs => ?_, ?_⟩) fun t ht => ?_
  · have a0 := mem_recSlotList _ s hs
    refine List.pairwise_append.mpr ⟨pairwise_of_length_le_one _ (by rw [List.length_map]; exact hEs s),
      List.pairwise_map.mpr ((List.Pairwise.and_mem.mp List.pairwise_lt_range).imp fun {i i'} h => ?_),
      fun x hx y hy => ?_⟩
    · obtain ⟨h1, h2, hlt⟩ := h
      have h1 := List.mem_range.mp h1
      have h2 := List.mem_range.mp h2
      exact disj_same_host (gD s a0 i h1) (gD s a0 i' h2) (conflict_dummy τ a i i' hlt (by omega))
    · obtain ⟨E, -, rfl⟩ := List.mem_map.mp hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy
      have hi := List.mem_range.mp hi
      exact disj_same_host (gI s a0) (gD s a0 i hi) (conflict_input_dummy τ a i (by omega))
  · refine (recSlotList_blk (dims M τ)).1.imp_of_mem fun {s s'} hs hs' hne x hx y hy => ?_
    have a1 := mem_recSlotList _ s hs
    have a2 := mem_recSlotList _ s' hs'
    exact disj_hostLists (s := 0) (col_ne (hok s a1).1 (hok s' a2).1 hne) x y (memI s a1 x hx) (memI s' a2 y hy)
  · obtain ⟨s, hs, hx⟩ := List.mem_flatMap.mp ht
    have a0 := mem_recSlotList _ s hs
    obtain ⟨K', V', e, g⟩ := memI s a0 t hx
    refine ⟨K', V', _, e, g, rfl, rfl, ?_⟩
    have hb : (recCell s).bit < 2 ^ om := (hok s a0).1
    have ht6 := recCell_tag_le s
    show (recCell s).bit + 2 ^ om * (recCell s).tag < 2 ^ om * 7
    have : 2 ^ om * ((recCell s).tag + 1) ≤ 2 ^ om * 7 := Nat.mul_le_mul_left _ (by omega)
    rw [Nat.mul_add, mul_one] at this
    omega

end Blocks8


theorem reg_area {F : Type} {l : Layout} {om : ℕ} {fin : ℕ} {t : Pattern l.m × Routing.Expr F} {i : ℕ} (hi8 : i < 8)
    (hi : InReg (l := l) (om := om) fin t i) :
    ∃ K V s h, t.1 = guardAt l om K V s h ∧ GuardOk l om K V s h ∧ h.area = 1 := by
  interval_cases i <;> (obtain ⟨K, V, h, e, g, p⟩ := hi; exact ⟨K, V, _, h, e, g, p.1⟩)

theorem inputEqs_length {F : Type} [Field F] (τ : ℕ) (lam : ℕ → Routing.Expr F) (Y : Routing.Expr F) (s : RecSlot) :
    (inputEqs τ lam Y s).length ≤ 1 := by
  obtain ⟨f, j⟩ := s; cases f <;> simp [inputEqs]

section Machine

variable {F : Type} [Field F] {l : Layout} {om dt K L τ a : ℕ} {M : ACSP.Ram}
  (c : Ctx l om dt K L τ a M)
include c

/-- **The machine items are pairwise disjoint** (`app:affine-embedding` Global noncancellation follows structurally), each in its
region `0..7`. -/
theorem machine_blk (kind : Fin M.ops → AluOp) (lam : ℕ → Routing.Expr F) :
    BlkG (Reg l om) ItemDisj 0 8 (machineItems l om K L M kind τ a lam) := by
  have hR : ∀ x y : Pattern l.m × Routing.Expr F, ∀ i j, Reg l om x i → Reg l om y j → i < j → ItemDisj x y :=
    fun x y i j gi gj h => inReg_disj c.fin_pos gi gj h
  dsimp only [machineItems]
  refine BlkG.app (BlkG.app (BlkG.app (BlkG.app (BlkG.app (BlkG.app (BlkG.app (blk_te c _) (blk_tb c _) hR
    (by omega) (by omega) (by omega)) (blk_cp c _ _) hR (by omega) (by omega) (by omega)) (blk_b3 c _ _) hR
    (by omega) (by omega) (by omega)) (blk_se c _) hR (by omega) (by omega) (by omega)) (blk_sb c _) hR
    (by omega) (by omega) (by omega)) (blk_b4 c _ _) hR (by omega) (by omega) (by omega))
    (blk_b5 c _ ?_ _) hR (by omega) (by omega) (by omega)
  intro s
  exact inputEqs_length _ _ _ _

end Machine

/-- **Routing terms and machine terms never share a point**: routing guards fix area `0`, machine guards area `1`
(`app:affine-embedding` Area separates routing from machine checks). -/
theorem routing_machine_disj {F : Type} {l : Layout} {om : ℕ} (x y : Pattern l.m × Routing.Expr F) (hx : x ∈ routingPairs l)
    (i : ℕ) (hi8 : i < 8) (hy : Reg l om y i) : ItemDisj x y := by
  obtain ⟨K', V', s', h', e, g, harea⟩ := reg_area hi8 hy
  obtain ⟨it, hit, rfl⟩ := List.mem_map.mp hx
  rintro v ⟨h1, h2⟩
  obtain ⟨x0, s0, c0, r0, a0, hin, rfl⟩ := cube_bits_cell l v
  have ha0 := ((Patterns.guard_iff l it ((Catalog.mem_routingItems_iff l it).mp hit) x0 s0 c0 r0 a0 hin).mp
    h1).2.2.1
  rw [e] at h2
  have ha1 := ((guardAt_iff l om K' V' s' h' x0 s0 c0 r0 a0 hin g.known g.value g.stage g.col g.role g.area).mp
    h2).2.2.2.1
  omega


/-- The routing items are pairwise disjoint (`routingTerms_disjoint`). -/
theorem routing_pw {F : Type} [Field F] [CharP F 2] (l : Layout) : (routingPairs (F := F) l).Pairwise ItemDisj := by
  have h := pairwise_of_disjointTerms _ (routingTerms_disjoint (F := F) l)
  unfold routingTerms at h
  unfold routingPairs
  rw [List.pairwise_map] at h ⊢
  exact h

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Adapters.ShortPCP NearCubicGates.Adapters.Joins in
/-- The setting of the instance's machine items (`app:event-trace`/`app:affine-embedding` numbers; `2 ≤ n ≤ t`). -/
theorem ownCtx (V : Verifier) (r : ClockRequest) (hn : 2 ≤ r.1.1) (hnt : r.1.1 ≤ r.2) :
    Ctx (ownLayout V r.2) (wordExp V r.2) (tagExp V) (regCount V) (codeLen V) (tau V r.2) (inRecExp V r)
      (ownRam V r) where
  hk := rfl
  hq := rfl
  hfin := by have := (ownLayout V r.2).stages_fit; have := (ownLayout V r.2).k_pos; omega
  hK := rfl
  hL := mnCode_length V _ _ _ _
  hw := wordW_eq V r.2
  hτw := tau_lt_wordW V r.2 (by omega)
  hF := by have := ftags_le V; unfold ftags at this; exact this
  hL1 := by unfold codeLen; omega
  ha := by have := (inExp_facts V r hn hnt).2.2.2.1; unfold inRecExp; omega

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Adapters.ShortPCP NearCubicGates.Adapters.Joins in
/-- **E2: the emitted terms have pairwise disjoint guards** (`app:affine-embedding` Global noncancellation), for every
coordinate expression `lam`, at every clock request with `2 ≤ n ≤ t`. -/
theorem ownItems_disjoint (V : Verifier) (r : ClockRequest) (hn : 2 ≤ r.1.1) (hnt : r.1.1 ≤ r.2)
    {F : Type} [Field F] [CharP F 2] (lam : ℕ → Routing.Expr F) :
    DisjointTerms (Circuit.termList (ownItems V r lam)) := by
  apply disjointTerms_of_pairwise
  have c := ownCtx V r hn hnt
  have hm := machine_blk c RAMTrace.mnKind lam
  unfold ownItems
  refine List.pairwise_append.mpr ⟨routing_pw _, hm.1, fun x hx y hy => ?_⟩
  obtain ⟨i, -, hi8, gi⟩ := hm.2 y hy
  exact routing_machine_disj x y hx i hi8 gi

end NearCubicGates.Adapters.RAMACSP
