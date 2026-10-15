import Proof.Gates.CounterMachine.ReqTab

set_option autoImplicit false

namespace NearCubicGates.Close.CounterMachine

open NearCubicWires NearCubicGates NearCubicGates.Close.Counter NearCubicGates.Close.Tabulator
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats

section Mom
variable (c : Call) (p : Params) (wt : Wit c.n)

/-! ## Forms on the variables from `o` -/

def stO {V : ℕ} (o r s : ℕ) : Formula V := linF o (circ c r).gates.length (wt.coef s r)
def scO {V : ℕ} (o r : ℕ) : Formula V := linF o (circ c r).gates.length (circ c r).coeffs

def digO {V : ℕ} (o : ℕ) : ℕ → ℕ → Formula V
  | r, 0 => stO c wt o r 0
  | r, j + 1 => .sub (stO c wt o r (j + 1)) (.mul (.const (rateOf p j)) (stO c wt o r j))

def phiO {V : ℕ} (o r : ℕ) : Formula V :=
  .sub (.mul (.const (p.M1 : ℤ)) (stO c wt o r (p.J - 1))) (.mul (.const (p.A : ℤ)) (scO c o r))

/-- The moment form of request `digitMoment r j` (`some j`) or `phiMoment r` (`none`). -/
def momF {V : ℕ} (r : ℕ) (j : Option ℕ) : Formula V :=
  match j with
  | some j => .pow (.sub (digO c p wt 0 r j) (digO c p wt (circ c r).gates.length r j)) (2 * p.k)
  | none => .pow (.sub (phiO c p wt 0 r) (phiO c p wt (circ c r).gates.length r)) (2 * p.k)

/-- The moment of request `(r, j)` on the cell `y`. -/
def momVal (r : ℕ) (j : Option ℕ) (y : Cells wt.I) : ℤ :=
  match j with
  | some j => digitMoment c p wt r j y
  | none => phiMoment c p wt r y

theorem momF_degree {V : ℕ} (r : ℕ) (j : Option ℕ) : (momF (V := V) c p wt r j).degree ≤ 2 * p.k := by
  have hst : ∀ o s, (stO (V := V) c wt o r s).degree ≤ 1 := fun _ _ => linF_degree _ _ _
  have hsc : ∀ o, (scO (V := V) c o r).degree ≤ 1 := fun _ => linF_degree _ _ _
  have hdig : ∀ o j, (digO (V := V) c p wt o r j).degree ≤ 1 := by
    intro o j; cases j with
    | zero => exact hst o 0
    | succ j => simp only [digO, Formula.degree, Nat.zero_add]; exact max_le (hst o _) (hst o _)
  have hphi : ∀ o, (phiO (V := V) c p wt o r).degree ≤ 1 := by
    intro o; simp only [phiO, Formula.degree, Nat.zero_add]; exact max_le (hst o _) (hsc o)
  cases j with
  | some j =>
    simp only [momF, Formula.degree]
    have := max_le (hdig 0 j) (hdig (circ c r).gates.length j)
    nlinarith
  | none =>
    simp only [momF, Formula.degree]
    have := max_le (hphi 0) (hphi (circ c r).gates.length)
    nlinarith

/-! ## Evaluation -/

section Eval
variable {V : ℕ} (r : ℕ) (o : ℕ) (z : BitInput c.n) (β : Fin V → ℤ)
  (hV : o + (circ c r).gates.length ≤ V)
  (hβ : ∀ t (ht : t < (circ c r).gates.length), β ⟨o + t, by omega⟩ = if (circ c r).gates[t].eval z then 1 else 0)
include hV hβ

theorem stO_eval (s : ℕ) : (stO c wt o r s).eval β = stageForm c wt r s z := linF_linForm z β _ o _ hV hβ

theorem scO_eval : (scO c o r).eval β = scoreForm c r z := by
  unfold scO scoreForm; rw [score_eq_linForm]; exact linF_linForm z β _ o _ hV hβ

theorem digO_eval (j : ℕ) : (digO c p wt o r j).eval β = digit c p wt r j z := by
  cases j with
  | zero => simp only [digO, digit, CountingCore.proposedDigit]; exact stO_eval c wt r o z β hV hβ 0
  | succ j =>
    simp only [digO, digit, CountingCore.proposedDigit, Formula.eval]
    rw [stO_eval c wt r o z β hV hβ, stO_eval c wt r o z β hV hβ]

theorem phiO_eval : (phiO c p wt o r).eval β = phi c p wt r z := by
  simp only [phiO, phi, Formula.eval]
  rw [stO_eval c wt r o z β hV hβ, scO_eval c r o z β hV hβ]

end Eval

/-! ## The moment request -/

/-- The roles: variable `v < m` is gate `v` at `(y,x)`, variable `m + t` gate `t` at `(y,0^I)`. -/
def momRole (m : ℕ) (v : Fin (2 * m)) : Role m :=
  ⟨⟨v.val % m, Nat.mod_lt _ (by have := v.isLt; omega)⟩, decide (m ≤ v.val)⟩

/-- **Table (b)'s request** for role `r` and the digit `j` (`some j`) or `Φ` (`none`). -/
noncomputable def momReq (hk : wt.I.card = p.k) (r : ℕ) (j : Option ℕ)
    (hB : ∀ t : Fin (circ c r).gates.length, GateBits (Call.B0 c.n) ((circ c r).gates[t]))
    (hc : PrintCondition p.k (c.n - p.k) (momF (V := 2 * (circ c r).gates.length) c p wt r j).degree
      (2 * (circ c r).gates.length) (Tabulator.mT (c.n - p.k) (Call.B0 c.n + Nat.clog 2 (c.n + 1)))) : TabReq where
  n := c.n
  k := p.k
  s := c.n - p.k
  G := (circ c r).gates.length
  V := 2 * (circ c r).gates.length
  gates := fun t => (circ c r).gates[t]
  layout := layoutOf wt.I hk
  H := Finset.univ
  role := momRole (circ c r).gates.length
  F := momF c p wt r j
  B := Call.B0 c.n
  hB := hB
  hc := hc

theorem pointsOf_zero (hk : wt.I.card = p.k) : pointsOf wt.I hk (fun _ => false) = zeroPoint wt.I := rfl

/-- The tabulation of a moment request. -/
noncomputable abbrev momTab (hk : wt.I.card = p.k) (r : ℕ) (j : Option ℕ) :=
  formulaTabulation (fun t : Fin (circ c r).gates.length => (circ c r).gates[t]) (layoutOf wt.I hk) Finset.univ
    (momRole (circ c r).gates.length) (momF (V := 2 * (circ c r).gates.length) c p wt r j)

theorem momTab_value (hk : wt.I.card = p.k) (r : ℕ) (j : Option ℕ) (i : ℕ) (x : Fin p.k → Bool)
    (v : Fin (2 * (circ c r).gates.length)) :
    (momTab c p wt hk r j).value (outerOf (c.n - p.k) i) x v =
      ((circ c r).gates[v.val % (circ c r).gates.length]'(Nat.mod_lt _ (by have := v.isLt; omega))).eval
        (if (circ c r).gates.length ≤ v.val then extend wt.I (cellOf wt.I i) (zeroPoint wt.I)
          else extend wt.I (cellOf wt.I i) (pointsOf wt.I hk x)) := by
  simp only [Tabulation.value, formulaTabulation, momRole, roleInner]
  by_cases h1 : (circ c r).gates.length ≤ v.val
  · simp only [h1, decide_true, if_true]
    rw [← pointsOf_zero c p wt hk, ← joinPoint_layoutOf]; rfl
  · simp only [h1, decide_false, Bool.false_eq_true, if_false]
    rw [← joinPoint_layoutOf]; rfl

theorem momTab_eval (hk : wt.I.card = p.k) (r : ℕ) (j : Option ℕ) (i : ℕ) (x : Fin p.k → Bool) :
    (momF (V := 2 * (circ c r).gates.length) c p wt r j).eval (boolPoint
      ((momTab c p wt hk r j).value (outerOf (c.n - p.k) i) x)) =
      (match j with
        | some j => (digit c p wt r j (extend wt.I (cellOf wt.I i) (pointsOf wt.I hk x)) -
            digit c p wt r j (extend wt.I (cellOf wt.I i) (zeroPoint wt.I))) ^ (2 * p.k)
        | none => (phi c p wt r (extend wt.I (cellOf wt.I i) (pointsOf wt.I hk x)) -
            phi c p wt r (extend wt.I (cellOf wt.I i) (zeroPoint wt.I))) ^ (2 * p.k)) := by
  have hV0 : 0 + (circ c r).gates.length ≤ 2 * (circ c r).gates.length := by omega
  have hVm : (circ c r).gates.length + (circ c r).gates.length ≤ 2 * (circ c r).gates.length := by omega
  have hβ0 : ∀ t (ht : t < (circ c r).gates.length), boolPoint ((momTab c p wt hk r j).value
      (outerOf (c.n - p.k) i) x) ⟨0 + t, by omega⟩ =
      if (circ c r).gates[t].eval (extend wt.I (cellOf wt.I i) (pointsOf wt.I hk x)) then 1 else 0 := by
    intro t ht
    simp only [boolPoint]
    rw [momTab_value]
    simp only [Nat.zero_add, if_neg (show ¬ (circ c r).gates.length ≤ t by omega), Nat.mod_eq_of_lt ht]
  have hβm : ∀ t (ht : t < (circ c r).gates.length), boolPoint ((momTab c p wt hk r j).value
      (outerOf (c.n - p.k) i) x) ⟨(circ c r).gates.length + t, by omega⟩ =
      if (circ c r).gates[t].eval (extend wt.I (cellOf wt.I i) (zeroPoint wt.I)) then 1 else 0 := by
    intro t ht
    simp only [boolPoint]
    rw [momTab_value]
    have e : ((circ c r).gates.length + t) % (circ c r).gates.length = t := by
      rw [Nat.add_mod_left, Nat.mod_eq_of_lt ht]
    simp only [if_pos (show (circ c r).gates.length ≤ (circ c r).gates.length + t by omega), e]
  cases j with
  | some j =>
    simp only [momF, Formula.eval]
    rw [digO_eval c p wt r 0 _ _ hV0 hβ0, digO_eval c p wt r _ _ _ hVm hβm]
  | none =>
    simp only [momF, Formula.eval]
    rw [phiO_eval c p wt r 0 _ _ hV0 hβ0, phiO_eval c p wt r _ _ _ hVm hβm]

/-- **Table (b) through lem:print**: the entry at outer index `i` is the moment on `cellOf I i`. -/
theorem momReq_value (hk : wt.I.card = p.k) (r : ℕ) (j : Option ℕ)
    (hB : ∀ t : Fin (circ c r).gates.length, GateBits (Call.B0 c.n) ((circ c r).gates[t]))
    (hc : PrintCondition p.k (c.n - p.k) (momF (V := 2 * (circ c r).gates.length) c p wt r j).degree
      (2 * (circ c r).gates.length) (Tabulator.mT (c.n - p.k) (Call.B0 c.n + Nat.clog 2 (c.n + 1)))) (i : ℕ) :
    tabTarget (momReq c p wt hk r j hB hc) (outerOf (c.n - p.k) i) = momVal c p wt r j (cellOf wt.I i) := by
  unfold tabTarget
  change ∑ x ∈ (Finset.univ : Finset (Fin p.k → Bool)), (momF (V := 2 * (circ c r).gates.length) c p wt r j).eval
    (boolPoint ((momTab c p wt hk r j).value (outerOf (c.n - p.k) i) x)) = _
  simp only [momTab_eval]
  cases j with
  | some j =>
    simp only [momVal, digitMoment]
    rw [← Equiv.sum_comp (pointsEquiv wt.I hk)]
    simp only [pointsEquiv_apply]
  | none =>
    simp only [momVal, phiMoment]
    rw [← Equiv.sum_comp (pointsEquiv wt.I hk)]
    simp only [pointsEquiv_apply]

end Mom

end NearCubicGates.Close.CounterMachine
