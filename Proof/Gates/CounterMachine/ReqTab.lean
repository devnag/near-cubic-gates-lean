import Proof.Gates.CounterMachine.ReqForm
import Proof.Gates.Counter.Main

set_option autoImplicit false

namespace NearCubicGates.Close.CounterMachine

open NearCubicWires NearCubicGates NearCubicGates.Close.Counter NearCubicGates.Close.Tabulator
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats

section Call
variable (c : Call) (p : Params) (wt : Wit c.n)

/-- The gates of the residue tabulations: `C¹`, then `C²` for a pair call. -/
def resGates : List (NormalizedThresholdGate c.n) :=
  if c.kind = .pair then c.first.gates ++ c.second.gates else c.first.gates

/-- Offset of role `r`'s gates. -/
def offR (r : ℕ) : ℕ := if r = 0 then 0 else c.first.gates.length

def stageF {V : ℕ} (r s : ℕ) : Formula V := linF (offR c r) (circ c r).gates.length (wt.coef s r)

def scoreF {V : ℕ} (r : ℕ) : Formula V := linF (offR c r) (circ c r).gates.length (circ c r).coeffs

def digF {V : ℕ} : ℕ → ℕ → Formula V
  | r, 0 => stageF c wt r 0
  | r, j + 1 => .sub (stageF c wt r (j + 1)) (.mul (.const (rateOf p j)) (stageF c wt r j))

/-- The forms of table (a): the digits `E_j^r` (role-major), then the scores `X^r`. -/
def resForm {V : ℕ} (i : ℕ) : Formula V :=
  if i < roleCount c.kind * p.J then digF c p wt (i / p.J) (i % p.J) else scoreF c (i - roleCount c.kind * p.J)

/-- Their residues. -/
def resRho (κ σ : List ℕ) (i : ℕ) : ℤ :=
  if i < roleCount c.kind * p.J then (κ.getD i 0 : ℤ) else (σ.getD (i - roleCount c.kind * p.J) 0 : ℤ)

theorem stageF_degree {V : ℕ} (r s : ℕ) : (stageF (V := V) c wt r s).degree ≤ 1 := linF_degree _ _ _
theorem scoreF_degree {V : ℕ} (r : ℕ) : (scoreF (V := V) c r).degree ≤ 1 := linF_degree _ _ _

theorem digF_degree {V : ℕ} (r j : ℕ) : (digF (V := V) c p wt r j).degree ≤ 1 := by
  cases j with
  | zero => exact stageF_degree c wt r 0
  | succ j =>
    simp only [digF, Formula.degree, Nat.zero_add]
    exact max_le (stageF_degree c wt r _) (stageF_degree c wt r _)

theorem resForm_degree {V : ℕ} (i : ℕ) : (resForm (V := V) c p wt i).degree ≤ 1 := by
  unfold resForm; split
  · exact digF_degree c p wt _ _
  · exact scoreF_degree c _

/-! ## Gate values -/

/-- Role `r`'s gates sit at `offR r` in `resGates`. -/
theorem resGates_role (r : ℕ) (hr : r < roleCount c.kind) :
    offR c r + (circ c r).gates.length ≤ (resGates c).length ∧
      ∀ t (ht : t < (circ c r).gates.length), ∃ h : offR c r + t < (resGates c).length,
        (resGates c)[offR c r + t] = (circ c r).gates[t] := by
  by_cases h0 : r = 0
  · subst h0
    simp only [offR, if_true, circ, Nat.zero_add, resGates]
    split_ifs
    · refine ⟨by simp, fun t ht => ⟨by simp; omega, ?_⟩⟩
      rw [List.getElem_append_left ht]
    · exact ⟨le_rfl, fun t ht => ⟨ht, rfl⟩⟩
  · have hp : c.kind = .pair := by
      by_contra hne
      have : roleCount c.kind = 1 := by cases hk : c.kind <;> simp_all [roleCount]
      omega
    simp only [offR, h0, if_false, circ, resGates, hp, if_true]
    refine ⟨by simp, fun t ht => ⟨by simp; omega, ?_⟩⟩
    rw [List.getElem_append_right (by omega)]
    congr 1; omega

/-- The gate values at `z` as a Boolean point. -/
def gatePt (z : BitInput c.n) : Fin (resGates c).length → Bool := fun v => ((resGates c)[v]).eval z

theorem stageF_eval (r : ℕ) (hr : r < roleCount c.kind) (s : ℕ) (z : BitInput c.n) :
    (stageF (V := (resGates c).length) c wt r s).eval (boolPoint (gatePt c z)) = stageForm c wt r s z := by
  obtain ⟨hle, hget⟩ := resGates_role c r hr
  unfold stageF stageForm
  refine linF_linForm z _ _ _ _ hle fun t ht => ?_
  obtain ⟨h, e⟩ := hget t ht
  simp only [boolPoint, gatePt, Fin.getElem_fin, e]

theorem scoreF_eval (r : ℕ) (hr : r < roleCount c.kind) (z : BitInput c.n) :
    (scoreF (V := (resGates c).length) c r).eval (boolPoint (gatePt c z)) = scoreForm c r z := by
  obtain ⟨hle, hget⟩ := resGates_role c r hr
  unfold scoreF scoreForm
  rw [score_eq_linForm]
  refine linF_linForm z _ _ _ _ hle fun t ht => ?_
  obtain ⟨h, e⟩ := hget t ht
  simp only [boolPoint, gatePt, Fin.getElem_fin, e]

theorem digF_eval (r : ℕ) (hr : r < roleCount c.kind) (j : ℕ) (z : BitInput c.n) :
    (digF (V := (resGates c).length) c p wt r j).eval (boolPoint (gatePt c z)) = digit c p wt r j z := by
  cases j with
  | zero => simp only [digF, digit, CountingCore.proposedDigit]; exact stageF_eval c wt r hr 0 z
  | succ j =>
    simp only [digF, digit, CountingCore.proposedDigit, Formula.eval]
    rw [stageF_eval c wt r hr, stageF_eval c wt r hr]

/-! ## The residue request -/

/-- The part of a cell as a filter on the inner assignments. -/
noncomputable def partH (hk : wt.I.card = p.k) (part : Option Bool) : Finset (Fin p.k → Bool) :=
  Finset.univ.filter fun x => inPart c wt part (pointsOf wt.I hk x) = true

/-- The residue formula of the request `(q, κ, σ)`. -/
def resFormula (q : ℕ) (κ σ : List ℕ) : Formula (resGates c).length :=
  resF q p.e (fun i : Fin (roleCount c.kind * p.J + roleCount c.kind) => resForm c p wt i.val)
    (fun i => resRho c p κ σ i.val)

/-- **Table (a)'s request** for the part `part`, the prime `q`, the residues `κ`, `σ` (bit bound and printing
condition supplied). -/
noncomputable def resReq (hk : wt.I.card = p.k) (part : Option Bool) (q : ℕ) (κ σ : List ℕ)
    (hB : ∀ i : Fin (resGates c).length, GateBits (Call.B0 c.n) ((resGates c)[i]))
    (hc : PrintCondition p.k (c.n - p.k) (resFormula c p wt q κ σ).degree (resGates c).length
      (Tabulator.mT (c.n - p.k) (Call.B0 c.n + Nat.clog 2 (c.n + 1)))) : TabReq where
  n := c.n
  k := p.k
  s := c.n - p.k
  G := (resGates c).length
  V := (resGates c).length
  gates := fun i => (resGates c)[i]
  layout := layoutOf wt.I hk
  H := partH c p wt hk part
  role := fun v => ⟨v, false⟩
  F := resFormula c p wt q κ σ
  B := Call.B0 c.n
  hB := hB
  hc := hc

/-- The joint residue condition of `jointCount` as the conditions of the forms. -/
theorem resCond_iff (q : ℕ) (κ σ : List ℕ) (z : BitInput c.n) :
    (∀ i : Fin (roleCount c.kind * p.J + roleCount c.kind),
      (resForm (V := (resGates c).length) c p wt i.val).eval (boolPoint (gatePt c z)) ≡ resRho c p κ σ i.val
        [ZMOD (q : ℤ)]) ↔
    ((∀ rj : Role c × Fin p.J, digit c p wt rj.1.val rj.2.val z ≡ (κ.getD (rj.1.val * p.J + rj.2.val) 0 : ℤ)
        [ZMOD (q : ℤ)]) ∧ ∀ r : Role c, scoreForm c r.val z ≡ (σ.getD r.val 0 : ℤ) [ZMOD (q : ℤ)]) := by
  have hJ : ∀ (r : Role c) (j : Fin p.J), r.val * p.J + j.val < roleCount c.kind * p.J := by
    intro r j; have := r.isLt; have := j.isLt; nlinarith
  constructor
  · intro h
    refine ⟨fun rj => ?_, fun r => ?_⟩
    · have hi := h ⟨rj.1.val * p.J + rj.2.val, by have := hJ rj.1 rj.2; omega⟩
      have hlt := hJ rj.1 rj.2
      have hdiv : (rj.1.val * p.J + rj.2.val) / p.J = rj.1.val := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by have := rj.2.isLt; omega), Nat.div_eq_of_lt rj.2.isLt]
        simp
      have hmod : (rj.1.val * p.J + rj.2.val) % p.J = rj.2.val := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt rj.2.isLt]
      simp only [resForm, resRho, if_pos hlt, hdiv, hmod] at hi
      rwa [digF_eval c p wt _ rj.1.isLt] at hi
    · have hi := h ⟨roleCount c.kind * p.J + r.val, by have := r.isLt; omega⟩
      simp only [resForm, resRho, show ¬ (roleCount c.kind * p.J + r.val < roleCount c.kind * p.J) by omega,
        if_false, Nat.add_sub_cancel_left] at hi
      rwa [scoreF_eval c _ r.isLt] at hi
  · rintro ⟨h1, h2⟩ i
    by_cases hi : i.val < roleCount c.kind * p.J
    · have hJp : 0 < p.J := by
        rcases Nat.eq_zero_or_pos p.J with h0 | h0
        · have : roleCount c.kind * p.J = 0 := by rw [h0, Nat.mul_zero]
          omega
        · exact h0
      have hr : i.val / p.J < roleCount c.kind := by rw [Nat.div_lt_iff_lt_mul hJp]; exact hi
      have := h1 (⟨i.val / p.J, hr⟩, ⟨i.val % p.J, Nat.mod_lt _ hJp⟩)
      simp only [resForm, resRho, if_pos hi]
      rw [digF_eval c p wt _ hr]
      have e : i.val / p.J * p.J + i.val % p.J = i.val := Nat.div_add_mod' _ _
      simpa [e] using this
    · have hr : i.val - roleCount c.kind * p.J < roleCount c.kind := by have := i.isLt; omega
      have := h2 ⟨i.val - roleCount c.kind * p.J, hr⟩
      simp only [resForm, resRho, if_neg hi]
      rw [scoreF_eval c _ hr]
      exact this

/-- **Table (a) through lem:print**: the entry at outer index `i`, reduced modulo `q^e`, is the joint count. -/
theorem resReq_value (hk : wt.I.card = p.k) (part : Option Bool) (q : ℕ) (κ σ : List ℕ)
    (hB : ∀ i : Fin (resGates c).length, GateBits (Call.B0 c.n) ((resGates c)[i]))
    (hc : PrintCondition p.k (c.n - p.k) (resFormula c p wt q κ σ).degree (resGates c).length
      (Tabulator.mT (c.n - p.k) (Call.B0 c.n + Nat.clog 2 (c.n + 1))))
    (hq : Nat.Prime q) (he : 1 ≤ p.e) (hlift : 2 ^ p.k < q ^ p.e) (i : ℕ) :
    (tabTarget (resReq c p wt hk part q κ σ hB hc) (outerOf (c.n - p.k) i)) % ((q : ℤ) ^ p.e) =
      (jointCount c p wt q part (cellOf wt.I i) (fun rj => (κ.getD (rj.1.val * p.J + rj.2.val) 0 : ℤ))
        (fun r => (σ.getD r.val 0 : ℤ)) : ℤ) := by
  classical
  have hH : (partH c p wt hk part).card < q ^ p.e := by
    refine lt_of_le_of_lt ?_ hlift
    calc (partH c p wt hk part).card ≤ (Finset.univ : Finset (Fin p.k → Bool)).card := Finset.card_le_univ _
      _ = 2 ^ p.k := by simp
  have hcount := resF_count q hq p.e he (fun i : Fin (roleCount c.kind * p.J + roleCount c.kind) =>
      resForm (V := (resGates c).length) c p wt i.val) (fun i => resRho c p κ σ i.val) (partH c p wt hk part)
    (fun x => (formulaTabulation (fun i : Fin (resGates c).length => (resGates c)[i]) (layoutOf wt.I hk)
      (partH c p wt hk part) (fun v => (⟨v, false⟩ : Role (resGates c).length)) (resFormula c p wt q κ σ)).value
        (outerOf (c.n - p.k) i) x) hH
  have hval : ∀ x : Fin p.k → Bool, (formulaTabulation (fun i : Fin (resGates c).length => (resGates c)[i])
      (layoutOf wt.I hk) (partH c p wt hk part) (fun v => (⟨v, false⟩ : Role (resGates c).length))
      (resFormula c p wt q κ σ)).value (outerOf (c.n - p.k) i) x =
      gatePt c (extend wt.I (cellOf wt.I i) (pointsOf wt.I hk x)) := by
    intro x; funext v
    simp only [Tabulation.value, formulaTabulation, roleInner, Bool.false_eq_true, if_false, gatePt]
    rw [joinPoint_layoutOf]
  simp only [hval] at hcount
  unfold tabTarget
  change (∑ x ∈ partH c p wt hk part, (resFormula c p wt q κ σ).eval (boolPoint ((formulaTabulation
    (fun i : Fin (resGates c).length => (resGates c)[i]) (layoutOf wt.I hk) (partH c p wt hk part)
    (fun v => (⟨v, false⟩ : Role (resGates c).length)) (resFormula c p wt q κ σ)).value (outerOf (c.n - p.k) i) x)))
    % ((q : ℤ) ^ p.e) = _
  simp only [hval]
  unfold resFormula
  rw [hcount]
  congr 1
  unfold jointCount
  simp only [resCond_iff]
  -- the bijection between inner assignments and points
  apply Finset.card_bij (fun x _ => pointsOf wt.I hk x)
  · intro x hx
    simp only [partH, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact ⟨hx.1, hx.2⟩
  · intro x1 _ x2 _ h
    apply (pointsEquiv wt.I hk).injective
    rw [pointsEquiv_apply, pointsEquiv_apply]; exact h
  · intro y hy
    refine ⟨(pointsEquiv wt.I hk).symm y, ?_, ?_⟩
    · have e : pointsOf wt.I hk ((pointsEquiv wt.I hk).symm y) = y := by
        rw [← pointsEquiv_apply]; simp
      simp only [partH, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      rw [e]; exact hy
    · rw [← pointsEquiv_apply]; simp

end Call

end NearCubicGates.Close.CounterMachine
