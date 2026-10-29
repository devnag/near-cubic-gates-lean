import SourceAdapters.RAMACSP.GenItemsTime

/-!
# The SORT templates (S1)–(S5) as symbolic trees

Paper: (S1)–(S5) of `def:event-trace` and "Placement" in
`app:affine-embedding`. There are 17 sorted templates. The comparison borrow
chain is partitioned into word-sized segments before printing its equations.

`tmplS q` is the template of the sorted equation `q` with bit index in `vJ`; for (S2) the argument of `borrow` is the
segment `s` and the key bit is `l = s·w + j` (`tmplS_ok`, `tmplS_borrow_ok`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

noncomputable section

namespace NearCubicGates.Adapters.RAMACSP.Gen.Items

open NearCubicGates.Adapters NearCubicGates.Adapters.RAMACSP NearCubicGates.Adapters.ACSP
open NearCubicGates.Adapters.ShortPCP.Machines NearCubicGates.Adapters.ShortPCP.Machines.FL
open NearCubicGates.Adapters.RAMTrace

variable {G : Glob}

/-- A non-routed sorted slot (role `0`) with tag `tag` at bit `b`. -/
def sF (tag : ℕ) (b : E) : SX := .var ⟨tag, b, 0, 1⟩

/-- The predecessor's slot of field `f` (role `1`) at bit `b`. -/
def prevS (f : RecField) (b : E) : SX := .var ⟨f.tag, b, 1, 1⟩

/-- The key bit `l` of the record (`f` = `rS`) or of the predecessor (`f` = `prevS`), by the compile-time selector
(`τ` in 27, `w` in 26). -/
def keyS (f : RecField → E → SX) (lE : E) : SX :=
  .ite (.lt lE (.v 27)) (f .ts lE) (.ite (.eq lE (.v 27)) (f .ph k0)
    (.ite (.lt lE (.add (.add (.v 27) (.k 1)) (.v 26))) (f .ad (.sub (.sub lE (.v 27)) (.k 1))) (f .rgn k0)))

/-- The key bit index of segment `seg`: `l = seg·w + j`. -/
def segE (seg : ℕ) : E := .add (.mul (.k seg) (.v 26)) jE

/-- `ob_l` for `l = seg·w + j`. -/
def obS (seg : ℕ) : SX :=
  if seg = 0 then .ite j0E .zero (sF 8 jm1E) else .ite j0E (sF (8 + seg - 1) wm1E) (sF (8 + seg) jm1E)

/-- `ob_κ` (`κ − 1 = w + τ + 1`). -/
def obKappaS : SX := .ite (.lt (.add (.v 27) (.k 1)) (.v 26)) (sF 9 (.add (.v 27) (.k 1))) (sF 10 k0)

/-- `so_{j+1}`. -/
def soNextS : SX := .ite (.lt (.add jE (.k 1)) (.v 26)) (sF 12 (.add jE (.k 1))) (sF 13 k0)

/-- **The SORT templates** (for `borrow`, the argument is the segment). -/
def tmplS : SEq → SX
  | .act => .mul (complS (prevS .act k0)) (rS .act k0)
  | .both => .add (sF 11 k0) (.mul (rS .act k0) (prevS .act k0))
  | .borrow seg => .add (sF (8 + seg) jE)
      (.add (.mul (complS (keyS prevS (segE seg))) (.add (keyS rS (segE seg)) (obS seg)))
        (.mul (keyS rS (segE seg)) (obS seg)))
  | .strict => .mul (sF 11 k0) (complS obKappaS)
  | .soFirst => .add (sF 12 k0) (.add (prevS .rgn k0) (rS .rgn k0))
  | .soNext _ => .add soNextS (.add (.add (sF 12 jE) (.add (prevS .ad jE) (rS .ad jE)))
      (.mul (sF 12 jE) (.add (prevS .ad jE) (rS .ad jE))))
  | .u => .add (sF 14 k0) (.mul (rS .act k0) (complS (rS .rgn k0)))
  | .g => .add (sF 15 k0) (.mul (sF 14 k0) (complS (rS .st k0)))
  | .ev _ => .add (sF 16 jE) (.mul (complS (sF 13 k0)) (prevS .va jE))
  | .load _ => .mul (sF 15 k0) (.add (rS .va jE) (sF 16 jE))
  | .gA1 => .add (sF 17 k0) (.mul (rS .act k0) (rS .rgn k0))
  | .gA => .add (sF 18 k0) (.mul (sF 17 k0) (rS .ph k0))
  | .same => .mul (sF 18 k0) (sF 13 k0)
  | .phase => .mul (sF 18 k0) (prevS .ph k0)
  | .value _ => .mul (sF 18 k0) (.add (rS .va jE) (prevS .va jE))

/-- The cell of a sorted-vertex variable. -/
def cellS (w : ℕ) : SVar → Cell
  | .inl s => sCell w s
  | .inr s => recCell s

theorem sRead_eq' (l : Routing.Layout) (om w : ℕ) (h : Cell) (v : SVar) :
    sRead l om w h v = localOffset l om h (cellS w v) := by
  cases v <;> rfl

/-- The state facts of a sorted template: bit index `j`, `w` in 26 (`1 ≤ w`), `τ < w` in 27, and room. -/
structure SortV (w τ j : ℕ) (s : FS) : Prop where
  hj : s.env vJ = j
  hw : s.env 26 = w
  ht : s.env 27 = τ
  hjw : j < w
  htw : τ < w
  hcap : 4 * w + 16 ≤ G.cap

theorem SortV.evals {w τ j : ℕ} {s : FS} (h : SortV (G := G) w τ j s) :
    evalE G s jE = j ∧ evalE G s k0 = 0 ∧ evalE G s jm1E = j - 1 ∧ evalE G s wm1E = w - 1 ∧
      evalE G s j0E = (if j = 0 then 1 else 0) ∧ evalE G s (.add jE (.k 1)) = j + 1 ∧
      evalE G s (.add (.v 27) (.k 1)) = τ + 1 ∧ evalE G s (.v 26) = w ∧ evalE G s (.v 27) = τ := by
  have h1 : min 1 G.cap = 1 := min_cap (by have := h.hcap; omega)
  have hjE : evalE G s jE = j := h.hj
  refine ⟨hjE, Nat.zero_min _, ?_, ?_, ?_, ?_, ?_, h.hw, h.ht⟩
  · simp [jm1E, evalE, hjE, h1]
  · simp [wm1E, evalE, h.hw, h1]
  · simp [j0E, evalE, hjE, Nat.zero_min]
  · simp only [evalE, hjE, h1]; have := h.hcap; have := h.hjw; exact min_cap (by omega)
  · simp only [evalE, h.ht, h1]; have := h.hcap; have := h.htw; exact min_cap (by omega)

theorem sortEq_dims (d : RAMTrace.Dims) : d.κ = d.w + d.τ + 2 := rfl

theorem divmod_eq {x w qq r : ℕ} (hw : 0 < w) (h : x = qq * w + r) (hr : r < w) : x / w = qq ∧ x % w = r :=
  (Nat.div_mod_unique hw).mpr ⟨by rw [h]; ring, hr⟩

/-- **The SORT templates evaluate to the catalog cells** (every equation but (S2)). -/
theorem tmplS_ok (d : RAMTrace.Dims) (q : SEq) (hq : q.Active d) (hb : ∀ l, q ≠ .borrow l) {s : FS}
    (hs : SortV (G := G) d.w d.τ (sBit d.w q) s) :
    SX.ev G s (tmplS q) = xmap (cellS d.w) (sortEq d q) := by
  obtain ⟨hjE, hk0, hjm1, hwm1, hj0, hj1, ht1, hw, ht⟩ := hs.evals
  have hw1 : 1 ≤ d.w := by have := hs.hjw; omega
  have hw0 : d.w ≠ 0 := by omega
  have htw := hs.htw
  have hjw := hs.hjw
  have hlt1 : evalE G s (.lt (.add (.v 27) (.k 1)) (.v 26)) = if d.τ + 1 < d.w then 1 else 0 := by
    show (if evalE G s (.add (.v 27) (.k 1)) < evalE G s (.v 26) then 1 else 0) = _
    rw [ht1, hw]
  have hlt2 : evalE G s (.lt (.add jE (.k 1)) (.v 26)) = if sBit d.w q + 1 < d.w then 1 else 0 := by
    show (if evalE G s (.add jE (.k 1)) < evalE G s (.v 26) then 1 else 0) = _
    rw [hj1, hw]
  have hkap : (if d.w ≤ d.τ + 1 then Expr.var (⟨10, 0, 0, 1⟩ : Cell) else Expr.var ⟨9, d.τ + 1, 0, 1⟩) =
      (Expr.var ⟨8 + (d.w + d.τ + 1) / d.w, (d.w + d.τ + 1) % d.w, 0, 1⟩ : Expr Cell) := by
    split_ifs with h
    · have e0 : d.w + d.τ + 1 = 2 * d.w + 0 := by omega
      obtain ⟨e1, e2⟩ := divmod_eq (x := d.w + d.τ + 1) (w := d.w) (qq := 2) (r := 0) (by omega) e0 (by omega)
      rw [e1, e2]
    · have e0 : d.w + d.τ + 1 = 1 * d.w + (d.τ + 1) := by ring
      obtain ⟨e1, e2⟩ := divmod_eq (x := d.w + d.τ + 1) (w := d.w) (qq := 1) (r := d.τ + 1) (by omega) e0 (by omega)
      rw [e1, e2]
  cases q
  case borrow l => exact absurd rfl (hb l)
  all_goals (simp only [sBit] at hjE hjm1 hj0 hj1 hlt2 hjw)
  all_goals
    simp [tmplS, sortEq, SX.ev, SC.ev, xmap, cellS, sCell, recCell, RecField.tag, sF, prevS, rS, hjE, hk0, hjm1, hwm1,
      hj0, hj1, ht1, hw, ht, complS, Expr.compl, soNextS, obKappaS, obE, Dims.κ, hlt1, hlt2, hw0, hjw]
  all_goals (try (split_ifs <;> first | rfl | omega))
  all_goals (try exact hkap)

theorem ev_keyS (d : RAMTrace.Dims) {s : FS} {j : ℕ} (hs : SortV (G := G) d.w d.τ j s) (lE : E) (l : ℕ)
    (hlE : evalE G s lE = l) (hl : l ≤ 3 * d.w) (fS : RecField → E → SX) (fc : RecField → ℕ → Cell)
    (hf : ∀ f b, SX.ev G s (fS f b) = .var (fc f (evalE G s b))) :
    SX.ev G s (keyS fS lE) = .var (fc (keySlot d l).1 (keySlot d l).2) := by
  obtain ⟨hjE, hk0, hjm1, hwm1, hj0, hj1, ht1, hw, ht⟩ := hs.evals
  have hc := hs.hcap
  have h1 : min 1 G.cap = 1 := min_cap (by omega)
  have e1 : evalE G s (.lt lE (.v 27)) = if l < d.τ then 1 else 0 := by
    show (if evalE G s lE < evalE G s (.v 27) then 1 else 0) = _; rw [hlE, ht]
  have e2 : evalE G s (.eq lE (.v 27)) = if l = d.τ then 1 else 0 := by
    show (if evalE G s lE = evalE G s (.v 27) then 1 else 0) = _; rw [hlE, ht]
  have e3 : evalE G s (.lt lE (.add (.add (.v 27) (.k 1)) (.v 26))) = if l < d.τ + 1 + d.w then 1 else 0 := by
    show (if evalE G s lE < evalE G s (.add (.add (.v 27) (.k 1)) (.v 26)) then 1 else 0) = _
    have : evalE G s (.add (.add (.v 27) (.k 1)) (.v 26)) = d.τ + 1 + d.w := by
      show min (evalE G s (.add (.v 27) (.k 1)) + evalE G s (.v 26)) G.cap = _
      rw [ht1, hw]; have := hs.htw; exact min_cap (by omega)
    rw [hlE, this]
  have e4 : evalE G s (.sub (.sub lE (.v 27)) (.k 1)) = l - d.τ - 1 := by
    show evalE G s (.sub lE (.v 27)) - evalE G s (.k 1) = _
    show evalE G s lE - evalE G s (.v 27) - min 1 G.cap = _
    rw [hlE, ht, h1]
  simp only [keyS, SX.ev, e1, e2, e3, keySlot]
  split_ifs <;> simp_all

theorem ev_obS (d : RAMTrace.Dims) {s : FS} {j : ℕ} (hs : SortV (G := G) d.w d.τ j s) (seg : ℕ) :
    SX.ev G s (obS seg) = xmap (cellS d.w) (obE (seg * d.w + j)) := by
  obtain ⟨hjE, hk0, hjm1, hwm1, hj0, hj1, ht1, hw, ht⟩ := hs.evals
  have hjw := hs.hjw
  by_cases hseg : seg = 0
  · subst hseg
    by_cases hj : j = 0
    · simp [obS, SX.ev, hj0, hj, obE]
      rfl
    · have hdm := divmod_eq (x := j - 1) (w := d.w) (qq := 0) (r := j - 1) (by omega) (by ring) (by omega)
      simp [obS, SX.ev, hj0, hj, obE, sF, SC.ev, hjm1, xmap, cellS, sCell, hdm.1, hdm.2]
  · by_cases hj : j = 0
    · subst hj
      obtain ⟨k, rfl⟩ : ∃ k, seg = k + 1 := ⟨seg - 1, by omega⟩
      have hm : (k + 1) * d.w = k * d.w + d.w := by ring
      have hdm := divmod_eq (x := (k + 1) * d.w + 0 - 1) (w := d.w) (qq := k) (r := d.w - 1) (by omega)
        (by omega) (by omega)
      have hl0 : (k + 1) * d.w + 0 ≠ 0 := by omega
      simp only [obS, hseg, if_false, SX.ev, hj0, if_true, obE, hl0, sF, SC.ev, hwm1, xmap, cellS, sCell, hdm.1,
        hdm.2]
      rw [if_neg (by decide)]; congr 2
    · have hdm := divmod_eq (x := seg * d.w + j - 1) (w := d.w) (qq := seg) (r := j - 1) (by omega) (by omega)
        (by omega)
      have hl0 : seg * d.w + j ≠ 0 := by omega
      simp [obS, hseg, SX.ev, hj0, hj, obE, hl0, sF, SC.ev, hjm1, xmap, cellS, sCell, hdm.1, hdm.2]

/-- **The (S2) template of segment `seg`** evaluates to the cells of the borrow equation of key bit `seg·w + j`. -/
theorem tmplS_borrow_ok (d : RAMTrace.Dims) (seg j : ℕ) (hseg : seg ≤ 2) {s : FS}
    (hs : SortV (G := G) d.w d.τ j s) :
    SX.ev G s (tmplS (.borrow seg)) = xmap (cellS d.w) (sortEq d (.borrow (seg * d.w + j))) := by
  obtain ⟨hjE, hk0, hjm1, hwm1, hj0, hj1, ht1, hw, ht⟩ := hs.evals
  have hjw := hs.hjw
  have hc := hs.hcap
  have hl : evalE G s (segE seg) = seg * d.w + j := by
    show min (evalE G s (.mul (.k seg) (.v 26)) + evalE G s jE) G.cap = _
    have : evalE G s (.mul (.k seg) (.v 26)) = seg * d.w := by
      show min (min seg G.cap * evalE G s (.v 26)) G.cap = _
      rw [hw, min_cap (show seg ≤ G.cap by omega)]
      exact min_cap (by nlinarith)
    rw [this, hjE]; exact min_cap (by nlinarith)
  have hl3 : seg * d.w + j ≤ 3 * d.w := by nlinarith
  have hdm := divmod_eq (x := seg * d.w + j) (w := d.w) (qq := seg) (r := j) (by omega) rfl hjw
  have kr := ev_keyS d hs (segE seg) _ hl hl3 rS (fun f b => recCell (f, b)) (fun f b => rfl)
  have kp := ev_keyS d hs (segE seg) _ hl hl3 prevS (fun f b => sCell d.w (.prev f b)) (fun f b => rfl)
  have ho := ev_obS d hs seg
  simp only [tmplS, sortEq, SX.ev, kr, kp, ho, xmap, complS, Expr.compl, keyE, pkeyE, sF, SC.ev, hjE, cellS, sCell,
    hdm.1, hdm.2]

end NearCubicGates.Adapters.RAMACSP.Gen.Items
