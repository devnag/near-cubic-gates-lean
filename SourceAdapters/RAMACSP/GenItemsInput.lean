import SourceAdapters.RAMACSP.GenItemsLam

/-!
# The input-record block (B5)

Paper: (B5) of `def:event-trace` and "Input subspace" in
`app:affine-embedding`. At role seven on record columns, INPUT selects the
prescribed input-record constants; address bit j is λ_j for j < τ and zero
otherwise. The direct input clause supplies va. DUMMY selects zero for
every semantic bit, including va. Input lanes are `T ≤ x < T+2^a`.

`inP f`: the items of the record bit `(f, j)` (bit index in `vJ`): its input-lane check (none for `va`), then one
dummy-lane check per `i < τ − a` (`vT`). The address check of `ad[j]`, `j < τ`, prints `λ_j` (`GenItemsLam`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

noncomputable section

namespace NearCubicGates.Adapters.RAMACSP.Gen.Items

open NearCubicGates.Adapters NearCubicGates.Adapters.RAMACSP NearCubicGates.Adapters.ACSP
open NearCubicGates.Adapters.ShortPCP NearCubicGates.Adapters.ShortPCP.Machines NearCubicGates.Adapters.ShortPCP.Machines.FL
open NearCubicGates.Adapters.RAMTrace NearCubicGates.Adapters.Joins
open NearCubicWires NearCubicWires.RepairOrdinary

variable {G : Glob}

/-- `min(τ, a)`, `a = m − ω` the input-record exponent (`m` in 29, `ω` in 25, `τ` in 27); the guards and the
dummy count only depend on it. -/
def aE : E := .sub (.v 27) (.sub (.v 27) (.sub (.v 29) (.v 25)))

/-- The input-lane guard mask `2^τ + (2^τ − 2^a)`. -/
def inKnE : E := .add (.v 28) (.sub (.v 28) (pow1E aE))

/-- The dummy-lane guard masks for `i` in `vT`: known `2^τ + (2^τ − 2^(a+i))`, value `2^τ + 2^(a+i)`. -/
def dKnE : E := .add (.v 28) (.sub (.v 28) (pow1E (.add aE (.v vT))))
def dVaE : E := .add (.v 28) (pow1E (.add aE (.v vT)))

/-- The host and the record cell of `(f, j)` (tag `tag`). -/
def h5 (tag : ℕ) : SC := ⟨tag, jE, 7, 1⟩
def c5 (tag : ℕ) : SC := ⟨tag, jE, 0, 0⟩

/-- The input-lane check of a record field. -/
def inBody (tag : ℕ) : RecField → P
  | .va => .nil
  | .act | .rgn => itemP (knE inKnE) (vaE (h5 tag) (.v 28) k0)
      (.seq (readTokP (h5 tag) (c5 tag)) (.seq (tokE 0 (.k 1)) (tokE 2 k0)))
  | .ad => itemP (knE inKnE) (vaE (h5 tag) (.v 28) k0)
      (.ite (.lt jE (.v 27)) (.seq (readTokP (h5 tag) (c5 tag)) (.seq lamP (tokE 2 k0))) (readTokP (h5 tag) (c5 tag)))
  | .ts | .ph | .st => itemP (knE inKnE) (vaE (h5 tag) (.v 28) k0) (readTokP (h5 tag) (c5 tag))

/-- **The items of the record bit `(f, j)`.** -/
def inP (f : RecField) : P :=
  .seq (inBody f.tag f) (.loop vT (.sub (.v 27) aE) (itemP (knE dKnE) (vaE (h5 f.tag) dVaE k0)
    (readTokP (h5 f.tag) (c5 f.tag))))

/-- The read `Y` of the record bit `(f, j)` from its host. -/
def inY {F : Type} (l : Routing.Layout) (om : ℕ) (f : RecField) (j : ℕ) : Routing.Expr F :=
  .read (some (localOffset l om ⟨f.tag, j, 7, 1⟩ ⟨f.tag, j, 0, 0⟩))

/-- The items of the record bit `s` in `machineItems` (layout `l`, `ω`, `τ`, `a`, rows `lam`). -/
def inItems {F : Type} [Field F] [CharP F 2] (l : Routing.Layout) (om τ a : ℕ) (lam : ℕ → Routing.Expr F)
    (s : RecSlot) : List (Routing.Pattern l.m × Routing.Expr F) :=
  let rc := recCell s
  let h : Cell := ⟨rc.tag, rc.bit, 7, 1⟩
  let Y : Routing.Expr F := .read (some (localOffset l om h rc))
  ((inputEqs τ lam Y s).map fun E => (guardAt l om (2 ^ τ + (2 ^ τ - 2 ^ a)) (2 ^ τ) 0 h, E)) ++
    ((List.range (τ - a)).map fun i => (guardAt l om (2 ^ τ + (2 ^ τ - 2 ^ (a + i))) (2 ^ τ + 2 ^ (a + i)) 0 h, Y))

theorem inItems_min {F : Type} [Field F] [CharP F 2] (l : Routing.Layout) (om τ a : ℕ) (lam : ℕ → Routing.Expr F)
    (s : RecSlot) : inItems l om τ a lam s = inItems l om τ (τ - (τ - a)) lam s := by
  simp only [inItems]
  by_cases ha : a ≤ τ
  · rw [show τ - (τ - a) = a by omega]
  · have e1 : 2 ^ τ - 2 ^ a = 2 ^ τ - 2 ^ (τ - (τ - a)) := by
      rw [show τ - (τ - a) = τ by omega, Nat.sub_self]
      have : 2 ^ τ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    rw [e1, show τ - a = 0 by omega]
    simp

/-- The state facts of the input-record block. -/
structure InV (l : Routing.Layout) (om dt τ a : ℕ) (s : FS) : Prop where
  lay : LayV l om dt s
  ht : s.env 27 = τ
  hT : s.env 28 = 2 ^ τ
  hk1 : τ + 1 = l.k
  hkm : l.k < l.m
  haE : evalE G s aE = a
  haτ : a ≤ τ
  cap : 2 ^ l.m + 8 ≤ G.cap
  mN : l.m ≤ G.N
  mK : l.m ≤ G.K

theorem InV.setT {l : Routing.Layout} {om dt τ a : ℕ} {s : FS} (h : InV (G := G) l om dt τ a s) (t : ℕ) :
    InV (G := G) l om dt τ a (s.setv vT t) := by
  have ha : Agree (fun x => x = 25 ∨ x = 27 ∨ x = 29 ∨ layA x) s (s.setv vT t) := ⟨fun x hx => by
    have : x ≠ vT := by rcases hx with e | e | e | e <;> [skip; skip; skip; rcases e with e | e | e | e | e | e | e] <;>
      (subst e; decide)
    simp [Function.update_of_ne this], rfl, rfl⟩
  refine ⟨h.lay.agree (fun x hx => Or.inr (Or.inr (Or.inr hx))) ha, by simp [h.ht, vT], by simp [h.hT, vT], h.hk1,
    h.hkm, ?_, h.haτ, h.cap, h.mN, h.mK⟩
  rw [evalE_agree ha aE ⟨Or.inr (Or.inl rfl), ⟨Or.inr (Or.inl rfl), ⟨Or.inr (Or.inr (Or.inl rfl)), Or.inl rfl⟩⟩⟩]
  exact h.haE

/-- **The items of one record bit.** -/
theorem den_inP {F : Type} [Field F] [CharP F 2] (mk : F → ℕ) (hm0 : mk 0 = 0) (hm1 : mk 1 = 1)
    {l : Routing.Layout} {om dt τ a : ℕ} {s : FS} (hs : InV (G := G) l om dt τ a s) (lam : ℕ → Routing.Expr F)
    (f : RecField) (j : ℕ) (hj : s.env vJ = j) (hc : (recCell (f, j)).Ok om dt)
    (hlam : f = .ad → j < τ → den G s lamP = (Joins.exprToks mk (lam j)).flatMap tokNums) :
    den G s (inP f) = (inItems l om τ a lam (f, j)).flatMap (itemNums mk) := by
  have hcap := hs.cap
  have hpm := Nat.two_pow_pos l.m
  have hp2 : ∀ x, x ≤ l.m → 2 ^ x ≤ G.cap := fun x hx => by
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hx; omega
  have hk1 := hs.hk1
  have hkm := hs.hkm
  have hτk : 2 ^ l.k = 2 * 2 ^ τ := by rw [← hk1, pow_succ]; ring
  have hc' : (⟨f.tag, j, 0, 0⟩ : Cell).Ok om dt := hc
  have hh : (⟨f.tag, j, 7, 1⟩ : Cell).Ok om dt := ⟨hc.1, hc.2.1, by norm_num, by norm_num⟩
  have ehh : ∀ t : FS, t.env vJ = j → SC.ev G t (h5 f.tag) = ⟨f.tag, j, 7, 1⟩ := fun t ht => by
    simp [h5, SC.ev, jE, evalE, ht]
  have ehc : ∀ t : FS, t.env vJ = j → SC.ev G t (c5 f.tag) = ⟨f.tag, j, 0, 0⟩ := fun t ht => by
    simp [c5, SC.ev, jE, evalE, ht]
  have hoff := den_readTokP mk hs.lay (by omega) (h5 f.tag) (c5 f.tag) (by rw [ehh s hj]; exact hh)
    (by rw [ehc s hj]; exact hc')
  rw [ehh s hj, ehc s hj] at hoff
  have hY : (Joins.exprToks mk (inY l om f j : Routing.Expr F)).flatMap tokNums =
      [1, localOffset l om ⟨f.tag, j, 7, 1⟩ ⟨f.tag, j, 0, 0⟩ + 1] := by
    simp [inY, Joins.exprToks, tokNums, Joins.varCode]
  rw [← hY] at hoff
  have hT := hs.hT
  have hpa : 2 ^ a ≤ 2 ^ τ := Nat.pow_le_pow_right (by norm_num) hs.haτ
  have hpa1 := Nat.one_le_two_pow (n := a)
  have hinK : evalE G s inKnE = 2 ^ τ + (2 ^ τ - 2 ^ a) := by
    have e1 : evalE G s (pow1E aE) = 2 ^ a := eval_pow1 hs.haE (by
      have := hp2 τ (by omega); omega)
    show min (s.env 28 + (s.env 28 - evalE G s (pow1E aE))) G.cap = _
    rw [hT, e1]; exact min_cap (by have := hp2 l.k hkm.le; omega)
  have hinr : 2 ^ τ + (2 ^ τ - 2 ^ a) < 2 ^ l.k := by omega
  have hTk : 2 ^ τ < 2 ^ l.k := by have := Nat.two_pow_pos τ; omega
  have rk : RdE notA (knE inKnE) := rd_knE (show vUK ≠ vA by decide) _
    ⟨show (28 : Var) ≠ vA by decide, show (28 : Var) ≠ vA by decide, trivial,
      ⟨show (27 : Var) ≠ vA by decide, show (27 : Var) ≠ vA by decide, show (29 : Var) ≠ vA by decide,
        show (25 : Var) ≠ vA by decide⟩⟩
  have rv : RdE notA (vaE (h5 f.tag) (.v 28) k0) :=
    rd_vaE_notA (h5 f.tag) (show vJ ≠ vA by decide) _ _ (show (28 : Var) ≠ vA by decide) trivial
  have hin : den G s (inBody f.tag f) =
      ((inputEqs τ lam (inY l om f j) (f, j)).map fun E =>
        (guardAt l om (2 ^ τ + (2 ^ τ - 2 ^ a)) (2 ^ τ) 0 ⟨f.tag, j, 7, 1⟩, E)).flatMap (itemNums mk) := by
    have gen := fun (body : P) (e : Routing.Expr F) (hb : den G s body = (Joins.exprToks mk e).flatMap tokNums) =>
      den_itemGen mk hs.lay (by omega) hs.mN (h5 f.tag) body e inKnE (.v 28) k0 _ _ 0 hinK hT (Nat.zero_min _) hinr
        hTk (Nat.two_pow_pos _) (by rw [ehh s hj]; exact hh) rk rv hb
    cases f with
    | va => rfl
    | act =>
      rw [inBody, gen _ (.add (inY l om .act j) (.const 1)) (by
        simp only [den, hoff, tokE, evalE, min_cap (show 0 ≤ G.cap by omega), min_cap (show 1 ≤ G.cap by omega),
          min_cap (show 2 ≤ G.cap by omega), k0, Nat.zero_min]
        simp [Joins.exprToks, tokNums, Joins.varCode, hm1]), ehh s hj]
      simp [inputEqs]
    | rgn =>
      rw [inBody, gen _ (.add (inY l om .rgn j) (.const 1)) (by
        simp only [den, hoff, tokE, evalE, min_cap (show 0 ≤ G.cap by omega), min_cap (show 1 ≤ G.cap by omega),
          min_cap (show 2 ≤ G.cap by omega), k0, Nat.zero_min]
        simp [Joins.exprToks, tokNums, Joins.varCode, hm1]), ehh s hj]
      simp [inputEqs]
    | ts => rw [inBody, gen _ (inY l om .ts j) (by rw [hoff, hY]), ehh s hj]; simp [inputEqs]
    | ph => rw [inBody, gen _ (inY l om .ph j) (by rw [hoff, hY]), ehh s hj]; simp [inputEqs]
    | st => rw [inBody, gen _ (inY l om .st j) (by rw [hoff, hY]), ehh s hj]; simp [inputEqs]
    | ad =>
      by_cases hjt : j < τ
      · rw [inBody, gen _ (.add (inY l om .ad j) (lam j)) (by
          have hl := hlam rfl hjt
          have hc1 : evalE G s (.lt jE (.v 27)) = 1 := by
            have e : evalE G s (.lt jE (.v 27)) = if s.env vJ < s.env 27 then 1 else 0 := rfl
            rw [e, hj, hs.ht, if_pos hjt]
          simp only [den, hc1, one_ne_zero, if_false]
          simp only [den, hoff, hl, tokE, evalE, min_cap (show 2 ≤ G.cap by omega), k0, Nat.zero_min]
          simp [Joins.exprToks, tokNums, Joins.varCode, List.flatMap_append]), ehh s hj]
        simp [inputEqs, hjt]
      · rw [inBody, gen _ (inY l om .ad j) (by
          have hc0 : evalE G s (.lt jE (.v 27)) = 0 := by
            have e : evalE G s (.lt jE (.v 27)) = if s.env vJ < s.env 27 then 1 else 0 := rfl
            rw [e, hj, hs.ht, if_neg hjt]
          simp only [den, hc0, if_true, hoff, hY]), ehh s hj]
        simp [inputEqs, hjt]
  rw [inP, den_seq_eq, hin]
  simp only [inItems, recCell, List.flatMap_append]
  refine congrArg₂ (· ++ ·) rfl ?_
  have hmin : min (evalE G s (.sub (.v 27) aE)) G.N = τ - a := by
    show min (s.env 27 - evalE G s aE) G.N = _; rw [hs.ht, hs.haE]; have := hs.mN; omega
  rw [den_loop s vT _ _ _ hmin (fun i => itemNums mk (guardAt l om (2 ^ τ + (2 ^ τ - 2 ^ (a + i))) (2 ^ τ + 2 ^ (a + i)) 0
    ⟨f.tag, j, 7, 1⟩, .read (some (localOffset l om ⟨f.tag, j, 7, 1⟩ ⟨f.tag, j, 0, 0⟩)))), List.flatMap_map]
  intro i hi
  have hs' := hs.setT i
  have hj' : (s.setv vT i).env vJ = j := by
    rw [FS.setv_env, Function.update_of_ne (show vJ ≠ vT by decide)]; exact hj
  have hT' : (s.setv vT i).env vT = i := by simp
  have hai : a + i < τ := by omega
  have hpai : 2 ^ (a + i) < 2 ^ τ := Nat.pow_lt_pow_right (by norm_num) hai
  have e2 : evalE G (s.setv vT i) (pow1E (.add aE (.v vT))) = 2 ^ (a + i) := by
    have : evalE G (s.setv vT i) (.add aE (.v vT)) = a + i := by
      show min (evalE G (s.setv vT i) aE + (s.setv vT i).env vT) G.cap = _
      rw [hs'.haE, hT']; exact min_cap (by have := hp2 τ (by omega); have := Nat.lt_two_pow_self (n := τ); omega)
    exact eval_pow1 this (by have := hp2 τ (by omega); omega)
  have hdk : evalE G (s.setv vT i) dKnE = 2 ^ τ + (2 ^ τ - 2 ^ (a + i)) := by
    show min ((s.setv vT i).env 28 + ((s.setv vT i).env 28 - evalE G (s.setv vT i) (pow1E (.add aE (.v vT))))) G.cap = _
    rw [hs'.hT, e2]; exact min_cap (by have := hp2 l.k hkm.le; omega)
  have hdv : evalE G (s.setv vT i) dVaE = 2 ^ τ + 2 ^ (a + i) := by
    show min ((s.setv vT i).env 28 + evalE G (s.setv vT i) (pow1E (.add aE (.v vT)))) G.cap = _
    rw [hs'.hT, e2]; exact min_cap (by have := hp2 l.k hkm.le; omega)
  have hoff' := den_readTokP mk hs'.lay (by omega) (h5 f.tag) (c5 f.tag) (by rw [ehh _ hj']; exact hh)
    (by rw [ehc _ hj']; exact hc')
  rw [ehh _ hj', ehc _ hj'] at hoff'
  have rpow : RdE notA (pow1E (.add aE (.v vT))) :=
    ⟨trivial, ⟨⟨show (27 : Var) ≠ vA by decide, show (27 : Var) ≠ vA by decide, show (29 : Var) ≠ vA by decide,
      show (25 : Var) ≠ vA by decide⟩, show vT ≠ vA by decide⟩⟩
  have hpai1 := Nat.one_le_two_pow (n := a + i)
  rw [den_itemGen mk hs'.lay (by omega) hs.mN (h5 f.tag) _ (inY l om f j) dKnE dVaE k0 _ _ 0 hdk hdv
    (Nat.zero_min _) (by omega) (by omega) (Nat.two_pow_pos _) (by rw [ehh _ hj']; exact hh)
    (rd_knE (show vUK ≠ vA by decide) _ ⟨show (28 : Var) ≠ vA by decide, show (28 : Var) ≠ vA by decide, rpow⟩)
    (rd_vaE_notA (h5 f.tag) (show vJ ≠ vA by decide) _ _ ⟨show (28 : Var) ≠ vA by decide, rpow⟩ trivial)
    (by rw [hoff', hY]), ehh _ hj']
  rfl

end NearCubicGates.Adapters.RAMACSP.Gen.Items
