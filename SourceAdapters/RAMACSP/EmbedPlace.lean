import SourceAdapters.RAMACSP.EmbedDisjoint
import SourceAdapters.RAMTrace.Catalog
import SourceAdapters.RAMACSP.ConstraintEmit

/-!
# Embedding theorem, part 5 (E3): placement of the event-trace equations in `H`

Paper: `app:affine-embedding`, "Placement" and "Neighbors". Time values lie
in machine area at stage zero, sorted values at the final stage, and routed
records at area zero, role zero. Local reads use host-to-slot translations;
predecessor reads use `Γ_t + η_5 + η_1` or `Γ_t + z + η_6` selected by the
least set lane bit.

A table `A : F → F` on `H` is read as an event-trace assignment `traceOf A` (each slot is the table's value at its
catalog cell). For each kind of emitted machine term, the value of the term at its host point on lane `x` is the
corresponding `ET` expression of `traceOf A` (`place_*`). The local-read lemma `evaluate_place` applies to any read function agreeing with the local offsets.
-/

set_option autoImplicit false

noncomputable section

namespace NearCubicGates.Adapters.RAMACSP

open NearCubicGates.Adapters NearCubicGates.Adapters.RAMTrace Guards Lanes
open Routing

/-! ## Evaluating translated expressions -/

namespace Placement

variable {F : Type} [Field F]

/-- Evaluation commutes with translation of the expression variables. -/
theorem eval_toRouting {ι : Type} (rd : ι → ℕ) (E : RAMTrace.Expr ι) (v : Routing.Vars → F) :
    MvPolynomial.eval v (toRouting rd E).poly = E.eval (fun i => v (some (rd i))) := by
  induction E with
  | zero => simp [toRouting, Routing.Expr.poly, RAMTrace.Expr.eval]
  | one => simp [toRouting, Routing.Expr.poly, RAMTrace.Expr.eval]
  | var i => simp [toRouting, Routing.Expr.poly, RAMTrace.Expr.eval]
  | add a b iha ihb => simp [toRouting, Routing.Expr.poly, RAMTrace.Expr.eval, iha, ihb]
  | mul a b iha ihb => simp [toRouting, Routing.Expr.poly, RAMTrace.Expr.eval, iha, ihb]

/-- Evaluations agree when the assignments agree on every variable read. -/
theorem eval_congr_on_vars {ι : Type} (E : RAMTrace.Expr ι) (v w : ι → F)
    (h : ∀ i ∈ E.vars, v i = w i) : E.eval v = E.eval w := by
  induction E with
  | zero => rfl
  | one => rfl
  | var i => exact h i (by simp [RAMTrace.Expr.vars])
  | add a b iha ihb =>
    exact congrArg₂ (· + ·)
      (iha fun i hi => h i (by simp [RAMTrace.Expr.vars, hi]))
      (ihb fun i hi => h i (by simp [RAMTrace.Expr.vars, hi]))
  | mul a b iha ihb =>
    exact congrArg₂ (· * ·)
      (iha fun i hi => h i (by simp [RAMTrace.Expr.vars, hi]))
      (ihb fun i hi => h i (by simp [RAMTrace.Expr.vars, hi]))

/-- A translated expression reads the corresponding local bank offsets. -/
theorem evaluate_toRouting {ι : Type} (l : Routing.Layout) (e : Fin l.m → F)
    (A : F → F) (z : F) (rd : ι → ℕ) (E : RAMTrace.Expr ι) :
    Routing.evaluate l e A z (toRouting rd E).poly =
      E.eval (fun i => A (z + Routing.maskEval l.m e (rd i))) :=
  eval_toRouting rd E _

theorem evaluate_read (l : Routing.Layout) (e : Fin l.m → F) (A : F → F) (z : F) (b : ℕ) :
    Routing.evaluate l e A z (Routing.Expr.read (some b)).poly = A (z + Routing.maskEval l.m e b) := by
  simp [Routing.evaluate, Routing.Expr.poly]

theorem evaluate_add (l : Routing.Layout) (e : Fin l.m → F) (A : F → F) (z : F) (E E' : Routing.Expr F) :
    Routing.evaluate l e A z (Routing.Expr.add E E').poly =
      Routing.evaluate l e A z E.poly + Routing.evaluate l e A z E'.poly := by
  simp [Routing.evaluate, Routing.Expr.poly]

theorem evaluate_const (l : Routing.Layout) (e : Fin l.m → F) (A : F → F) (z c : F) :
    Routing.evaluate l e A z (Routing.Expr.const c).poly = c := by
  simp [Routing.evaluate, Routing.Expr.poly]

theorem evaluate_bool (l : Routing.Layout) (e : Fin l.m → F) (A : F → F) (z : F) (b : ℕ) :
    Routing.evaluate l e A z (boolExpr b).poly =
      A (z + Routing.maskEval l.m e b) ^ 2 + A (z + Routing.maskEval l.m e b) := by
  simp [Routing.evaluate, Routing.Expr.poly, boolExpr]

end Placement

open Placement

/-! ## Tables as event-trace assignments -/

section Table

variable {F : Type} [Field F] [CharP F 2] {l : Layout} (e : Fin l.m → F) (om : ℕ)

/-- The table's value at catalog cell `c` of lane `x`, stage `s`. -/
def cellAt (A : F → F) (x s : ℕ) (c : Cell) : F := A (label l e x s (c.col om) c.role c.area)

/-- The cell of a time-row variable. -/
def cellT (K L : ℕ) : TVar → Cell
  | .inl s => tCell K L s
  | .inr s => recCell s

/-- The cell of a sorted-vertex variable. -/
def cellS (w : ℕ) : SVar → Cell
  | .inl s => sCell w s
  | .inr s => recCell s

theorem tRead_eq (K L : ℕ) (h : Cell) (v : TVar) : tRead l om K L h v = localOffset l om h (cellT K L v) := by
  cases v <;> rfl

theorem sRead_eq (w : ℕ) (h : Cell) (v : SVar) : sRead l om w h v = localOffset l om h (cellS w v) := by
  cases v <;> rfl

/-- **The event-trace assignment of a table** (`app:event-trace` Realization in `H`): every slot is the table's value at its
catalog cell; routed records at stage `0` (`src`) and the final stage `fin` (`dst`). -/
def traceOf (K L w fin : ℕ) (A : F → F) : Trace F where
  src x f j := cellAt e om A x 0 (recCell (f, j))
  dst x f j := cellAt e om A x fin (recCell (f, j))
  time i s := cellAt e om A i 0 (tCell K L s)
  sort j s := cellAt e om A j fin (sCell w s)

omit [CharP F 2] in
theorem timeRead_traceOf (K L w fin : ℕ) (A : F → F) (i : ℕ) (v : TVar) :
    (traceOf e om K L w fin A).timeRead i v = cellAt e om A i 0 (cellT K L v) := by
  rcases v with s | ⟨f, j⟩ <;> rfl

omit [CharP F 2] in
theorem sortRead_traceOf (K L w fin : ℕ) (A : F → F) (j : ℕ) (v : SVar) :
    (traceOf e om K L w fin A).sortRead j v = cellAt e om A j fin (cellS w v) := by
  rcases v with s | ⟨f, k⟩ <;> rfl

/-- **Local reads land at their cells** (`app:affine-embedding`: for source/check point `(x,s,c,r,a)` and target `(x,s,c',r',a')`, use
`column(c ⊕ c') + role(r ⊕ r') + area(a ⊕ a')`). -/
theorem evaluate_place {ι : Type} (A : F → F) (x s : ℕ) (h : Cell) (rd : ι → ℕ) (cell : ι → Cell)
    (E : RAMTrace.Expr ι) (hh : InRange l x s (h.col om) h.role h.area)
    (hc : ∀ i ∈ E.vars, InRange l x s ((cell i).col om) (cell i).role (cell i).area)
    (hrd : ∀ i, rd i = localOffset l om h (cell i)) :
    Routing.evaluate l e A (label l e x s (h.col om) h.role h.area) (toRouting rd E).poly =
      E.eval (fun i => cellAt e om A x s (cell i)) := by
  rw [evaluate_toRouting]
  apply eval_congr_on_vars
  intro i hi
  rw [hrd]
  exact congrArg A (LayoutFacts.label_local l e x s (h.col om) h.role h.area ((cell i).col om) (cell i).role
    (cell i).area hh (hc i hi))

theorem evaluate_local (A : F → F) (x s : ℕ) (h c : Cell) (hh : InRange l x s (h.col om) h.role h.area)
    (hc : InRange l x s (c.col om) c.role c.area) :
    Routing.evaluate l e A (label l e x s (h.col om) h.role h.area)
      (Routing.Expr.read (some (localOffset l om h c))).poly = cellAt e om A x s c := by
  rw [evaluate_read]
  exact congrArg A (LayoutFacts.label_local l e x s (h.col om) h.role h.area (c.col om) c.role c.area hh hc)

theorem local_landing (x s : ℕ) (h c : Cell) (hh : InRange l x s (h.col om) h.role h.area)
    (hc : InRange l x s (c.col om) c.role c.area) :
    label l e x s (h.col om) h.role h.area + maskEval l.m e (localOffset l om h c) =
      label l e x s (c.col om) c.role c.area :=
  LayoutFacts.label_local l e x s (h.col om) h.role h.area (c.col om) c.role c.area hh hc

theorem evaluate_bool_local (A : F → F) (x s : ℕ) (h c : Cell) (hh : InRange l x s (h.col om) h.role h.area)
    (hc : InRange l x s (c.col om) c.role c.area) :
    Routing.evaluate l e A (label l e x s (h.col om) h.role h.area) (boolExpr (localOffset l om h c)).poly =
      cellAt e om A x s c ^ 2 + cellAt e om A x s c := by
  rw [evaluate_bool, local_landing e om x s h c hh hc]
  rfl

/-- **The time-copy predecessor family** `Γ_t + η_5 + η_1` (`app:affine-embedding` B1/B2 time chain): from a role-`5` host of lane `x`
(`x mod 2^{t+1} = 2^t`) to role `1` of lane `x − 1`, same column, area `1`. -/
theorem evaluate_pred5 (A : F → F) (x s t : ℕ) (col : ℕ) (hh : InRange l x s col 5 1) (ht : t < l.k)
    (hx : x % 2 ^ (t + 1) = 2 ^ t) :
    Routing.evaluate l e A (label l e x s col 5 1)
      (Routing.Expr.read (some (laneCarry t ^^^ eta l 5 ^^^ eta l 1))).poly = A (label l e (x - 1) s col 1 1) := by
  rw [evaluate_read]
  have e1 : eta l 5 ^^^ eta l 1 = eta l (5 ^^^ 1) := by
    have := LayoutFacts.cellMask_xor l 0 0 0 5 0 0 0 0 1 0
      ⟨Nat.two_pow_pos _, Nat.two_pow_pos _, Nat.two_pow_pos _, by decide, by decide⟩
      ⟨Nat.two_pow_pos _, Nat.two_pow_pos _, Nat.two_pow_pos _, by decide, by decide⟩
    simpa [eta] using this
  have e2 : laneCarry t ^^^ eta l 5 ^^^ eta l 1 = laneCarry t ^^^ eta l (5 ^^^ 1) ^^^ cellMask l 0 0 0 0 (1 ^^^ 1) := by
    rw [Nat.xor_assoc, e1]; simp [cellMask]
  rw [e2]
  exact congrArg A (LayoutFacts.label_predecessor l e x s col 5 1 t 1 1 hh (by decide) (by decide) ht hx)

/-- **The sorted-copy predecessor family** `Γ_t + z + η_6` (`app:affine-embedding` B4 sorted chain): from a role-`6` host of lane `x`
to the routed record (role `0`, area `0`) of lane `x − 1`, same column. -/
theorem evaluate_pred6 (A : F → F) (x s t : ℕ) (col : ℕ) (hh : InRange l x s col 6 1) (ht : t < l.k)
    (hx : x % 2 ^ (t + 1) = 2 ^ t) :
    Routing.evaluate l e A (label l e x s col 6 1)
      (Routing.Expr.read (some (laneCarry t ^^^ areaMask l ^^^ eta l 6))).poly = A (label l e (x - 1) s col 0 0) := by
  rw [evaluate_read]
  have e2 : laneCarry t ^^^ areaMask l ^^^ eta l 6 = laneCarry t ^^^ eta l (6 ^^^ 0) ^^^ cellMask l 0 0 0 0 (1 ^^^ 0) := by
    simp only [areaMask, show (6 : ℕ) ^^^ 0 = 6 from rfl, show (1 : ℕ) ^^^ 0 = 1 from rfl]
    rw [Nat.xor_assoc, Nat.xor_assoc, Nat.xor_comm (cellMask l 0 0 0 0 1)]
  rw [e2]
  exact congrArg A (LayoutFacts.label_predecessor l e x s col 6 1 t 0 0 hh (by decide) (by decide) ht hx)

end Table

/-! ## Lowest set bits -/

theorem exists_low_bit (x : ℕ) (hx : 0 < x) : ∃ t, x % 2 ^ (t + 1) = 2 ^ t ∧ 2 ^ t ≤ x := by
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    rcases Nat.even_or_odd x with ⟨y, rfl⟩ | ⟨y, rfl⟩
    · obtain ⟨t, h1, h2⟩ := ih y (by omega) (by omega)
      refine ⟨t + 1, ?_, ?_⟩
      · rw [show y + y = 2 * y by ring, pow_succ, show 2 ^ (t + 1) * 2 = 2 * 2 ^ (t + 1) by ring,
          Nat.mul_mod_mul_left, h1, pow_succ]; ring
      · rw [pow_succ]; omega
    · exact ⟨0, by omega, by simp⟩

theorem low_bit_lt (x n t : ℕ) (hx : x < 2 ^ n) (h : 2 ^ t ≤ x) : t < n := by
  by_contra hc
  have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (not_lt.mp hc)
  omega


/-! ## Small field facts and the coordinate expressions -/

section Field

variable {F : Type} [Field F] [CharP F 2]

theorem eq_of_add_eq_zero_two {x y : F} (h : x + y = 0) : x = y := by
  have := congrArg (· + y) h
  simpa [add_assoc, CharTwo.add_self_eq_zero] using this

theorem isBit_of_sq_add {y : F} (h : y ^ 2 + y = 0) : y = 0 ∨ y = 1 := by
  have h' : y * (y + 1) = 0 := by rw [mul_add, mul_one, ← pow_two]; exact h
  rcases mul_eq_zero.mp h' with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (eq_of_add_eq_zero_two h1)

theorem sq_add_of_isBit {y : F} (h : y = 0 ∨ y = 1) : y ^ 2 + y = 0 := by
  rcases h with rfl | rfl
  · simp
  · simp [CharTwo.add_self_eq_zero]

omit [CharP F 2] in
theorem squares_poly (r : ℕ) : (squares (F := F) r).poly = MvPolynomial.X none ^ (2 ^ r) := by
  induction r with
  | zero => simp [squares, Routing.Expr.poly]
  | succ r ih => rw [squares, Routing.Expr.poly, ih, ← pow_mul, pow_succ]

omit [CharP F 2] in
/-- `λ(X) = Σ_r c_r X^{2^r}` evaluates as the linearized polynomial (`app:affine-embedding` Coordinate and row selectors). -/
theorem evaluate_lamExpr (l : Layout) (e : Fin l.m → F) (A : F → F) (z : F) {m : ℕ} (row : Fin m → F) :
    Routing.evaluate l e A z (lamExpr row).poly = (linearized m row).eval z := by
  have hsq : ∀ r : ℕ, Routing.evaluate l e A z (squares (F := F) r).poly = z ^ (2 ^ r) := fun r => by
    rw [squares_poly]; simp [Routing.evaluate]
  have key : ∀ rs : List (Fin m), Routing.evaluate l e A z
      (rs.foldr (fun r acc => Routing.Expr.add (.mul (.const (row r)) (squares r.val)) acc) (.const 0)).poly =
      (rs.map fun r => row r * z ^ (2 ^ r.val)).sum := by
    intro rs
    induction rs with
    | nil => simp [Routing.evaluate, Routing.Expr.poly]
    | cons r rs ih =>
      rw [List.foldr_cons, evaluate_add, List.map_cons, List.sum_cons, ← ih]
      congr 1
      have := hsq r.val
      simp only [Routing.evaluate, Routing.Expr.poly, map_mul, MvPolynomial.eval_C] at this ⊢
      rw [this]
  unfold lamExpr
  rw [key, linearized, Polynomial.eval_finsetSum, Fin.sum_univ_def]
  simp

end Field

/-! ## Firing an item at a lane -/

/-- **An item's equation at a lane where its guard holds** (`app:affine-embedding` guard library): if every item's equation vanishes
where its guard holds, then a machine item `(guardAt K V s h, E)` gives `E = 0` at the host point of every lane `x`
with `x ∧ K = V ∧ K`. -/
theorem fire {F : Type} [Field F] {l : Layout} (e : Fin l.m → F) (om : ℕ) (A : F → F)
    {items : List (Pattern l.m × Routing.Expr F)}
    (hS : ∀ v, ∀ t ∈ items, patternHolds t.1 v → Routing.evaluate l e A (cubeEval l.m e v) t.2.poly = 0)
    {Kg Vg s : ℕ} {h : Cell} {E : Routing.Expr F} (hmem : (guardAt l om Kg Vg s h, E) ∈ items)
    (g : GuardOk l om Kg Vg s h) (x : ℕ) (hx : x < 2 ^ l.k) (hlane : x &&& Kg = Vg &&& Kg) :
    Routing.evaluate l e A (label l e x s (h.col om) h.role h.area) E.poly = 0 := by
  have hv := (guardAt_iff l om Kg Vg s h x s (h.col om) h.role h.area ⟨hx, g.stage, g.col, g.role, g.area⟩
    g.known g.value g.stage g.col g.role g.area).mpr ⟨rfl, rfl, rfl, rfl, hlane⟩
  exact hS _ _ hmem hv

end NearCubicGates.Adapters.RAMACSP
