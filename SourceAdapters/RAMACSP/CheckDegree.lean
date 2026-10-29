import SourceAdapters.RAMACSP.ConstraintEmit
import SourceAdapters.RAMACSP.CheckFrame
import SourceAdapters.Routing.CircuitExpr
import SourceAdapters.Routing.CircuitFinal
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.Algebra.MvPolynomial.Rename

/-!
# the formal weighted degree of the emitted constraint (`lem:acsp-degree`)

Paper: `lem:acsp-degree`. A normalized pattern has X-degree at most
`mH·2^(mH-1)`. Every machine equation has assignment degree at most two;
its position coordinate has X-degree at most `2^(mH-1)`. Expanding each
selector-times-equation term gives weighted degree at most
`mH·h/2 + 2(h-1) ≤ (mH+4)·h`, where `h = 2^mH`.
A sum has no monomial outside the union of its summands' monomials.

`WDeg` supplies the weighted-degree rules for sums, products, powers, constants, variables and renamings.
-/

set_option autoImplicit false

noncomputable section

namespace NearCubicGates.Adapters.RAMACSP.WDeg
open MvPolynomial

variable {σ R : Type} [CommSemiring R] (w : σ → ℕ)

theorem le_iff {p : MvPolynomial σ R} {n : ℕ} :
    weightedTotalDegree w p ≤ n ↔ ∀ d ∈ p.support, Finsupp.weight w d ≤ n := Finset.sup_le_iff

theorem add_le (p q : MvPolynomial σ R) :
    weightedTotalDegree w (p + q) ≤ max (weightedTotalDegree w p) (weightedTotalDegree w q) := by
  classical
  rw [le_iff]
  intro d hd
  rcases Finset.mem_union.mp (MvPolynomial.support_add hd) with h | h
  · exact (le_weightedTotalDegree w h).trans (le_max_left _ _)
  · exact (le_weightedTotalDegree w h).trans (le_max_right _ _)

theorem mul_le (p q : MvPolynomial σ R) :
    weightedTotalDegree w (p * q) ≤ weightedTotalDegree w p + weightedTotalDegree w q := by
  classical
  rw [le_iff]
  intro d hd
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul p q hd)
  rw [map_add]
  exact Nat.add_le_add (le_weightedTotalDegree w ha) (le_weightedTotalDegree w hb)

theorem C_le (c : R) : weightedTotalDegree w (C c : MvPolynomial σ R) ≤ 0 := by
  rw [le_iff]
  intro d hd
  rw [← MvPolynomial.monomial_zero'] at hd
  have := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hd)
  subst this; simp

theorem X_le (v : σ) : weightedTotalDegree w (X v : MvPolynomial σ R) ≤ w v := by
  rw [le_iff]
  intro d hd
  rw [MvPolynomial.X] at hd
  have := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hd)
  subst this; simp [Finsupp.weight_apply, Finsupp.sum_single_index]

theorem pow_le (p : MvPolynomial σ R) (n : ℕ) : weightedTotalDegree w (p ^ n) ≤ n * weightedTotalDegree w p := by
  induction n with
  | zero => simpa using C_le w (1 : R)
  | succ n ih =>
    rw [pow_succ]
    refine (mul_le w _ _).trans ?_
    rw [Nat.succ_mul]; omega

theorem list_sum_le (l : List (MvPolynomial σ R)) (n : ℕ) (h : ∀ p ∈ l, weightedTotalDegree w p ≤ n) :
    weightedTotalDegree w l.sum ≤ n := by
  induction l with
  | nil => simpa using (C_le w (0 : R)).trans (Nat.zero_le n)
  | cons p l ih =>
    rw [List.sum_cons]
    refine (add_le w _ _).trans (max_le (h p (by simp)) (ih fun q hq => h q (by simp [hq])))

theorem finset_prod_le {ι : Type} (s : Finset ι) (f : ι → MvPolynomial σ R) (n : ℕ)
    (h : ∀ i ∈ s, weightedTotalDegree w (f i) ≤ n) :
    weightedTotalDegree w (∏ i ∈ s, f i) ≤ s.card * n := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using C_le w (1 : R)
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    refine (mul_le w _ _).trans ?_
    have h1 := h a (by simp)
    have h2 := ih fun i hi => h i (by simp [hi])
    rw [Nat.succ_mul]; omega

theorem finset_sum_le {ι : Type} (s : Finset ι) (f : ι → MvPolynomial σ R) (n : ℕ)
    (h : ∀ i ∈ s, weightedTotalDegree w (f i) ≤ n) :
    weightedTotalDegree w (∑ i ∈ s, f i) ≤ n := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (C_le w (0 : R)).trans (Nat.zero_le n)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (add_le w _ _).trans (max_le (h a (by simp)) (ih fun i hi => h i (by simp [hi])))

theorem rename_le {τ : Type} (f : σ → τ) (w' : τ → ℕ) (hw : ∀ v, w' (f v) ≤ w v) (p : MvPolynomial σ R) :
    weightedTotalDegree w' (rename f p) ≤ weightedTotalDegree w p := by
  classical
  rw [le_iff]
  intro d hd
  by_contra hlt
  apply (MvPolynomial.mem_support_iff.mp hd)
  apply MvPolynomial.coeff_rename_eq_zero
  intro u hud
  by_contra hne
  have hu : u ∈ p.support := MvPolynomial.mem_support_iff.mpr hne
  apply hlt
  subst hud
  refine le_trans ?_ (le_weightedTotalDegree w hu)
  rw [Finsupp.weight_apply, Finsupp.weight_apply,
    Finsupp.sum_mapDomain_index (by simp) (by intros; simp [add_mul])]
  simp only [Finsupp.sum]
  exact Finset.sum_le_sum fun v _ => by simp only [smul_eq_mul]; exact Nat.mul_le_mul_left _ (hw v)

theorem mono_weight (w' : σ → ℕ) (hw : ∀ v, w v ≤ w' v) (p : MvPolynomial σ R) :
    weightedTotalDegree w p ≤ weightedTotalDegree w' p := by
  rw [le_iff]
  intro d hd
  refine le_trans ?_ (le_weightedTotalDegree w' hd)
  rw [Finsupp.weight_apply, Finsupp.weight_apply]
  simp only [Finsupp.sum]
  exact Finset.sum_le_sum fun v _ => by simp only [smul_eq_mul]; exact Nat.mul_le_mul_left _ (hw v)

end NearCubicGates.Adapters.RAMACSP.WDeg

/-! ## The degree table of `lem:acsp-degree`: every equation has assignment degree `≤ 2` -/

namespace NearCubicGates.Adapters.RAMACSP.EqDeg
open NearCubicGates.Adapters.ACSP NearCubicGates.Adapters.RAMTrace NearCubicGates.Adapters.RAMTrace.Expr

variable {ι : Type}

theorem var_le (x : ι) (k : ℕ) (hk : 1 ≤ k) : (Expr.var x).deg ≤ k := hk
theorem zero_le' (k : ℕ) : (Expr.zero : Expr ι).deg ≤ k := Nat.zero_le _
theorem one_le' (k : ℕ) : (Expr.one : Expr ι).deg ≤ k := Nat.zero_le _
theorem bit_le (b : Bool) (k : ℕ) : (Expr.bit b : Expr ι).deg ≤ k := by unfold Expr.bit; split <;> exact Nat.zero_le _
theorem add_le {a b : Expr ι} {k : ℕ} (ha : a.deg ≤ k) (hb : b.deg ≤ k) : (Expr.add a b).deg ≤ k := max_le ha hb
theorem mul11 {a b : Expr ι} (ha : a.deg ≤ 1) (hb : b.deg ≤ 1) : (Expr.mul a b).deg ≤ 2 := Nat.add_le_add ha hb
theorem mul02 {a b : Expr ι} {k : ℕ} (ha : a.deg ≤ 0) (hb : b.deg ≤ k) : (Expr.mul a b).deg ≤ k := by
  show a.deg + b.deg ≤ k; omega
theorem mul20 {a b : Expr ι} {k : ℕ} (ha : a.deg ≤ k) (hb : b.deg ≤ 0) : (Expr.mul a b).deg ≤ k := by
  show a.deg + b.deg ≤ k; omega
theorem compl_le {a : Expr ι} {k : ℕ} (ha : a.deg ≤ k) : (Expr.compl a).deg ≤ k := max_le (Nat.zero_le _) ha
theorem ite_le {c : Prop} [Decidable c] {a b : Expr ι} {k : ℕ} (ha : a.deg ≤ k) (hb : b.deg ≤ k) :
    (if c then a else b).deg ≤ k := by split <;> assumption
theorem sumCode_le {α : Type} (f : ℕ → α → Expr ι) (k : ℕ) (h : ∀ p I, (f p I).deg ≤ k) :
    ∀ (p : ℕ) (l : List α), (Expr.sumCode f p l).deg ≤ k
  | _, [] => Nat.zero_le _
  | p, I :: l => max_le (h p I) (sumCode_le f k h (p + 1) l)
theorem sum_le (k : ℕ) : ∀ (l : List (Expr ι)), (∀ e ∈ l, e.deg ≤ k) → (Expr.sum l).deg ≤ k
  | [], _ => Nat.zero_le _
  | a :: l, h => max_le (h a (by simp)) (sum_le k l fun e he => h e (by simp [he]))

variable (M : Ram) (kind : Fin M.ops → AluOp) (τ : ℕ)

theorem eSet_le (Q : Instr M.w M.k M.ops → Bool) (k : ℕ) (hk : 1 ≤ k) : (eSet M Q).deg ≤ k :=
  sumCode_le _ k (fun _ _ => ite_le (var_le _ k hk) (zero_le' k)) 0 M.code
theorem opnd_le (x : Operand M.w M.k) (j : ℕ) : (opnd M x j).deg ≤ 1 := by
  cases x <;> simp only [opnd] <;> first | exact var_le _ 1 le_rfl | exact bit_le _ 1
theorem srcX_le (I : Instr M.w M.k M.ops) (j : ℕ) : (srcX M I j).deg ≤ 1 := by
  cases I <;> simp only [srcX] <;> first | exact opnd_le M _ j | exact var_le _ 1 le_rfl | exact zero_le' 1
theorem srcY_le (I : Instr M.w M.k M.ops) (j : ℕ) : (srcY M I j).deg ≤ 1 := by
  cases I <;> simp only [srcY] <;> first | exact opnd_le M _ j | exact var_le _ 1 le_rfl | exact zero_le' 1
theorem srcXF_le (I : Instr M.w M.k M.ops) : (srcXF M I).deg ≤ 1 := by
  cases I <;> simp only [srcXF] <;> first | exact var_le _ 1 le_rfl | exact zero_le' 1
theorem eDot_le (s : Instr M.w M.k M.ops → Expr TVar) (hs : ∀ I, (s I).deg ≤ 1) : (eDot M s).deg ≤ 2 :=
  sumCode_le _ 2 (fun _ I => mul11 (var_le _ 1 le_rfl) (hs I)) 0 M.code
theorem pcTerm_le (p : ℕ) (I : Instr M.w M.k M.ops) (j : ℕ) : (pcTerm M p I j).deg ≤ 2 := by
  cases I <;> simp only [pcTerm] <;>
    first
    | exact mul20 (var_le _ 2 (by norm_num)) (bit_le _ 0)
    | exact add_le (mul20 (mul11 (var_le _ 1 le_rfl) (var_le _ 1 le_rfl)) (bit_le _ 0))
        (mul20 (add_le (var_le _ 2 (by norm_num)) (mul11 (var_le _ 1 le_rfl) (var_le _ 1 le_rfl))) (bit_le _ 0))

theorem timeEq_le (q : TEq) : (timeEq M kind τ q).deg ≤ 2 := by
  have v1 : ∀ x : TVar, (Expr.var x).deg ≤ 1 := fun x => var_le x 1 le_rfl
  have v2 : ∀ x : TVar, (Expr.var x).deg ≤ 2 := fun x => var_le x 2 (by norm_num)
  have e1 : ∀ Q, (eSet M Q).deg ≤ 1 := fun Q => eSet_le M Q 1 le_rfl
  have e2 : ∀ Q, (eSet M Q).deg ≤ 2 := fun Q => eSet_le M Q 2 (by norm_num)
  have ca : ∀ j, (caE j).deg ≤ 1 := fun j => ite_le (zero_le' 1) (v1 _)
  have bo : ∀ j, (boE j).deg ≤ 1 := fun j => ite_le (zero_le' 1) (v1 _)
  have tc : ∀ j, (tcE j).deg ≤ 1 := fun j => ite_le (one_le' 1) (v1 _)
  have ac : ∀ j, (acE j).deg ≤ 1 := fun j => ite_le (v1 _) (v1 _)
  have bc : ∀ j, (bcE j).deg ≤ 1 := fun j => ite_le (v1 _) (v1 _)
  have cm : ∀ j, (cmpE M j).deg ≤ 1 := fun j => ite_le (add_le (v1 _) (v1 _)) (v1 _)
  have w12 : ∀ e : Expr TVar, e.deg ≤ 1 → e.deg ≤ 2 := fun e h => h.trans (by norm_num)
  cases q with
  | flag r j => exact mul11 (v1 _) (v1 _)
  | decFirst => exact add_le (v2 _) (v2 _)
  | decRec p => exact add_le (add_le (v2 _) (v2 _)) (v2 _)
  | decExcl p => exact mul11 (v1 _) (v1 _)
  | decLast => exact add_le (v2 _) (one_le' 2)
  | decPc j => exact add_le (v2 _) (sumCode_le _ 2 (fun _ _ => ite_le (v2 _) (zero_le' 2)) 0 M.code)
  | opX j => exact add_le (v2 _) (eDot_le M _ fun I => srcX_le M I j)
  | opY j => exact add_le (v2 _) (eDot_le M _ fun I => srcY_le M I j)
  | opXF => exact add_le (v2 _) (eDot_le M _ fun I => srcXF_le M I)
  | sumAD j => exact add_le (add_le (add_le (v2 _) (v2 _)) (v2 _)) (w12 _ (ca j))
  | carry j => exact add_le (v2 _) (add_le (add_le (mul11 (v1 _) (v1 _)) (mul11 (v1 _) (ca j))) (mul11 (v1 _) (ca j)))
  | sumSB j => exact add_le (add_le (add_le (v2 _) (v2 _)) (v2 _)) (w12 _ (bo j))
  | borrow j => exact add_le (v2 _) (add_le (mul11 (compl_le (v1 _)) (add_le (v1 _) (bo j))) (mul11 (v1 _) (bo j)))
  | andAN j => exact add_le (v2 _) (mul11 (v1 _) (v1 _))
  | ozFirst => exact add_le (v2 _) (v2 _)
  | ozRec j => exact add_le (v2 _) (add_le (add_le (v2 _) (v2 _)) (mul11 (v1 _) (v1 _)))
  | gt => exact add_le (v2 _) (mul11 (compl_le (v1 _)) (v1 _))
  | rfFlag j => exact mul11 (v1 _) (v1 _)
  | store j => exact mul11 (e1 _) (add_le (v1 _) (v1 _))
  | res j =>
    refine add_le (v2 _) (sum_le 2 _ ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro e (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · exact mul11 (e1 _) (v1 _)
    · exact mul11 (e1 _) (v1 _)
    · exact mul11 (e1 _) (v1 _)
    · exact mul11 (e1 _) (cm j)
    · exact mul11 (e1 _) (v1 _)
    · exact mul11 (e1 _) (v1 _)
    · exact ite_le (mul11 (e1 _) (v1 _)) (zero_le' 2)
  | resF => exact add_le (v2 _) (mul11 (e1 _) (v1 _))
  | reg r j => exact add_le (v2 _) (add_le (mul11 (e1 _) (v1 _)) (mul11 (compl_le (e1 _)) (v1 _)))
  | regF r => exact add_le (v2 _) (add_le (mul11 (e1 _) (v1 _)) (mul11 (compl_le (e1 _)) (v1 _)))
  | pcNext j => exact add_le (v2 _) (sumCode_le _ 2 (fun p I => pcTerm_le M p I j) 0 M.code)
  | recAct => exact add_le (v2 _) (add_le (add_le (e2 _) (e2 _)) (v2 _))
  | recRgn => exact add_le (v2 _) (v2 _)
  | recAd j => exact add_le (v2 _) (add_le (mul11 (add_le (e1 _) (e1 _)) (v1 _)) (ite_le (mul11 (v1 _) (v1 _)) (zero_le' 2)))
  | recPh => exact add_le (v2 _) (one_le' 2)
  | recVa j => exact add_le (v2 _) (add_le (mul11 (add_le (e1 _) (e1 _)) (v1 _)) (mul11 (v1 _) (v1 _)))
  | recSt => exact add_le (v2 _) (e2 _)
  | tsn j => exact add_le (add_le (v2 _) (v2 _)) (w12 _ (tc j))
  | tc j => exact add_le (v2 _) (mul11 (v1 _) (tc j))
  | aA => exact add_le (v2 _) (mul11 (e1 _) (compl_le (v1 _)))
  | can j => exact add_le (add_le (v2 _) (v2 _)) (w12 _ (ac j))
  | ac j => exact add_le (v2 _) (mul11 (v1 _) (ac j))
  | aB => exact add_le (v2 _) (mul11 (e1 _) (compl_le (v1 _)))
  | cbn j => exact add_le (add_le (v2 _) (v2 _)) (w12 _ (bc j))
  | bc j => exact add_le (v2 _) (mul11 (v1 _) (bc j))
  | bound => exact mul11 (v1 _) (v1 _)

theorem outE_le : (outE M).deg ≤ 1 := eSet_le M _ 1 le_rfl

theorem accE_le : (accE M).deg ≤ 1 := add_le (eSet_le M _ 1 le_rfl) (one_le' 1)

theorem sortEq_le (d : Dims) (q : SEq) : (sortEq d q).deg ≤ 2 := by
  have v1 : ∀ x : SVar, (Expr.var x).deg ≤ 1 := fun x => var_le x 1 le_rfl
  have v2 : ∀ x : SVar, (Expr.var x).deg ≤ 2 := fun x => var_le x 2 (by norm_num)
  have ke : ∀ l, (keyE d l).deg ≤ 1 := fun l => v1 _
  have pk : ∀ l, (pkeyE d l).deg ≤ 1 := fun l => v1 _
  have ob : ∀ l, (obE l).deg ≤ 1 := fun l => ite_le (zero_le' 1) (v1 _)
  cases q with
  | act => exact mul11 (compl_le (v1 _)) (v1 _)
  | both => exact add_le (v2 _) (mul11 (v1 _) (v1 _))
  | borrow l => exact add_le (v2 _) (add_le (mul11 (compl_le (pk l)) (add_le (ke l) (ob l))) (mul11 (ke l) (ob l)))
  | strict => exact mul11 (v1 _) (compl_le (ob _))
  | soFirst => exact add_le (v2 _) (add_le (v2 _) (v2 _))
  | soNext j => exact add_le (v2 _) (add_le (add_le (v2 _) (add_le (v2 _) (v2 _))) (mul11 (v1 _) (add_le (v1 _) (v1 _))))
  | u => exact add_le (v2 _) (mul11 (v1 _) (compl_le (v1 _)))
  | g => exact add_le (v2 _) (mul11 (v1 _) (compl_le (v1 _)))
  | ev j => exact add_le (v2 _) (mul11 (compl_le (v1 _)) (v1 _))
  | load j => exact mul11 (v1 _) (add_le (v1 _) (v1 _))
  | gA1 => exact add_le (v2 _) (mul11 (v1 _) (v1 _))
  | gA => exact add_le (v2 _) (mul11 (v1 _) (v1 _))
  | same => exact mul11 (v1 _) (v1 _)
  | phase => exact mul11 (v1 _) (v1 _)
  | value j => exact mul11 (v1 _) (add_le (v1 _) (v1 _))

end NearCubicGates.Adapters.RAMACSP.EqDeg

namespace NearCubicGates.Adapters.RAMACSP

open NearCubicGates.Adapters NearCubicGates.Adapters.ACSP MvPolynomial

section Weights

variable {F : Type} [Field F] [CharP F 2]

/-- The gate-wise weight of an expression (the degree argument of `lem:acsp-degree`: `X` weight `1`, an assignment read weight `D`,
constants `0`, `add ↦ max`, `mul ↦ +`). -/
def exprWeight (D : ℕ) : Routing.Expr F → ℕ
  | .const _ => 0
  | .read none => 1
  | .read (some _) => D
  | .add a b => max (exprWeight D a) (exprWeight D b)
  | .mul a b => exprWeight D a + exprWeight D b
  | .square a => 2 * exprWeight D a

omit [CharP F 2] in
/-- **the degree argument of `lem:acsp-degree` for one expression.** -/
theorem expr_wdeg_le (m : ℕ) (E : Routing.Expr F) :
    weightedTotalDegree (Routing.weight m) E.poly ≤ exprWeight (2 ^ m - 1) E := by
  induction E with
  | const c => exact (WDeg.C_le _ c).trans (Nat.zero_le _)
  | read v =>
    cases v with
    | none => exact WDeg.X_le _ none
    | some b => exact WDeg.X_le _ (some b)
  | add a b iha ihb =>
    exact (WDeg.add_le _ _ _).trans (max_le_max iha ihb)
  | mul a b iha ihb =>
    exact (WDeg.mul_le _ _ _).trans (Nat.add_le_add iha ihb)
  | square a iha =>
    exact (WDeg.pow_le _ _ 2).trans (Nat.mul_le_mul_left 2 iha)

omit [CharP F 2] in
/-- `liftX q` has weighted degree at most `deg q` (weight `1` on `X`). -/
theorem liftX_wdeg_le (m : ℕ) (q : Polynomial F) :
    weightedTotalDegree (Routing.weight m) (Routing.liftX q) ≤ q.natDegree := by
  unfold Routing.liftX
  rw [Polynomial.eval₂_eq_sum_range]
  refine WDeg.finset_sum_le _ _ _ _ fun i hi => ?_
  have hi' : i ≤ q.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  refine (WDeg.mul_le _ _ _).trans ?_
  have h1 := WDeg.C_le (Routing.weight m) (q.coeff i)
  have h2 := (WDeg.pow_le (Routing.weight m) (MvPolynomial.X none : Routing.MP F) i).trans
    (Nat.mul_le_mul_left i (WDeg.X_le (Routing.weight m) none))
  simp only [Routing.weight, mul_one] at h2
  omega

omit [CharP F 2] in
/-- **Normalized selectors** (`lem:acsp-degree`): a pattern on `m` coordinates has weighted degree `≤ m·2^{m−1}`. -/
theorem selector_wdeg_le {m : ℕ} {e : Fin m → F} (coords : Routing.Coordinates m e) (p : Routing.Pattern m) :
    weightedTotalDegree (Routing.weight m) (Routing.selector coords p) ≤ m * 2 ^ (m - 1) := by
  unfold Routing.selector
  refine le_trans (WDeg.finset_prod_le _ Finset.univ _ (2 ^ (m - 1)) fun a _ => ?_) ?_
  · have hl := (liftX_wdeg_le m (Routing.linearized m (coords.coeff a))).trans (coords.degree_le a)
    have h1 : weightedTotalDegree (Routing.weight m) (1 : Routing.MP F) ≤ 0 := by
      simpa using WDeg.C_le (Routing.weight m) (1 : F)
    split
    · exact h1.trans (Nat.zero_le _)
    · exact hl
    · exact (WDeg.add_le _ _ _).trans (max_le (h1.trans (Nat.zero_le _)) hl)
  · simp

omit [CharP F 2] in
/-- **`lem:acsp-degree` for the emitted sum**: if every equation has weighted degree `≤ B`, the emitted polynomial has
weighted degree `≤ m·2^{m−1} + B`. -/
theorem emit_wdeg_le {m : ℕ} {e : Fin m → F} (coords : Routing.Coordinates m e) (ts : List (Routing.Term m F))
    (B : ℕ) (h : ∀ t ∈ ts, weightedTotalDegree (Routing.weight m) t.equation ≤ B) :
    weightedTotalDegree (Routing.weight m) (Routing.emit coords ts) ≤ m * 2 ^ (m - 1) + B := by
  unfold Routing.emit
  refine WDeg.list_sum_le _ _ _ fun q hq => ?_
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hq
  exact (WDeg.mul_le _ _ _).trans (Nat.add_le_add (selector_wdeg_le coords t.guard) (h t ht))

end Weights


/-! ## Serialization: the reduced-mask circuit has the field circuit's polynomial

(`mapGate`, `mapCircuit`, `poly_mapCircuit` copied from the old-route `ShortPCP/SuccinctCode.lean`, not imported.) -/

/-- A gate with its constant mapped by `φ`. -/
def mapGate {R S : Type} (φ : R → S) : ArithGate R → ArithGate S
  | .input i => .input i
  | .const v => .const (φ v)
  | .add a b => .add a b
  | .mul a b => .mul a b

/-- A circuit with its constants mapped by `φ`. -/
def mapCircuit {R S : Type} (φ : R → S) (c : ArithCircuit R) : ArithCircuit S := ⟨c.gates.map (mapGate φ)⟩

theorem mapCircuit_comp {R S U : Type} (φ : R → S) (ψ : S → U) (c : ArithCircuit R) :
    mapCircuit ψ (mapCircuit φ c) = mapCircuit (ψ ∘ φ) c := by
  simp only [mapCircuit, List.map_map, ArithCircuit.mk.injEq]
  apply List.map_congr_left
  intro g _
  cases g <;> rfl

theorem mapCircuit_congr {R S : Type} (φ ψ : R → S) (h : ∀ v, φ v = ψ v) (c : ArithCircuit R) :
    mapCircuit φ c = mapCircuit ψ c := by
  rw [show φ = ψ from funext h]

section RingHom

variable {R S : Type} [CommSemiring R] [CommSemiring S] (ψ : R →+* S) (m : ℕ)

theorem getD_map_zero (prior : List (MvPolynomial (Fin m) R)) (i : ℕ) :
    (prior.map (MvPolynomial.map ψ)).getD i 0 = MvPolynomial.map ψ (prior.getD i 0) := by
  rw [← map_zero (MvPolynomial.map ψ), List.getD_map]

theorem gate_poly_map (prior : List (MvPolynomial (Fin m) R)) (g : ArithGate R) :
    (mapGate ψ g).poly m (prior.map (MvPolynomial.map ψ)) = MvPolynomial.map ψ (g.poly m prior) := by
  cases g with
  | input i =>
    simp only [mapGate, ArithGate.poly]
    split_ifs <;> simp
  | const v => simp [mapGate, ArithGate.poly]
  | add a b => simp only [mapGate, ArithGate.poly, getD_map_zero, map_add]
  | mul a b => simp only [mapGate, ArithGate.poly, getD_map_zero, map_mul]

theorem foldl_map_poly : ∀ (gs : List (ArithGate R)) (prior : List (MvPolynomial (Fin m) R)),
    (gs.map (mapGate ψ)).foldl (fun prior g => prior ++ [g.poly m prior]) (prior.map (MvPolynomial.map ψ)) =
      (gs.foldl (fun prior g => prior ++ [g.poly m prior]) prior).map (MvPolynomial.map ψ)
  | [], _ => rfl
  | g :: gs, prior => by
    simp only [List.map_cons, List.foldl_cons]
    rw [gate_poly_map, show prior.map (MvPolynomial.map ψ) ++ [MvPolynomial.map ψ (g.poly m prior)] =
      (prior ++ [g.poly m prior]).map (MvPolynomial.map ψ) by simp]
    exact foldl_map_poly gs _

/-- The polynomial of a circuit commutes with a ring homomorphism applied to its constants. -/
theorem poly_mapCircuit (c : ArithCircuit R) :
    (mapCircuit ψ c).poly m = MvPolynomial.map ψ (c.poly m) := by
  unfold ArithCircuit.poly mapCircuit
  have h := foldl_map_poly ψ m c.gates []
  simp only [List.map_nil] at h
  simp only
  rw [h, ← map_zero (MvPolynomial.map ψ), List.getLastD_map]

end RingHom

theorem mapCircuit_id {R : Type} (c : ArithCircuit R) : mapCircuit id c = c := by
  cases c with
  | mk gs =>
    simp only [mapCircuit, ArithCircuit.mk.injEq]
    conv_rhs => rw [← List.map_id gs]
    apply List.map_congr_left
    intro g _
    cases g <;> rfl

theorem codeCircuit_gateMask (irr : Polynomial (ZMod 2)) (hm : irr.Monic) (f : ℕ)
    (gs : List (ArithGate (AdjoinRoot irr))) :
    Joins.codeCircuit (gs.map (gateMask irr hm f)) =
      mapCircuit (fun c => NearCubicWires.WireExponent3_5.GF.toPoly
        (NearCubicWires.WireExponent3_5.GF.ofPoly (AdjoinRoot.modByMonicHom hm c) f)) ⟨gs⟩ := by
  simp only [Joins.codeCircuit, mapCircuit, List.map_map, ArithCircuit.mk.injEq]
  apply List.map_congr_left
  intro g _
  cases g <;> rfl

/-- The serialized circuit read over `F₂[x]/(irr)` is the field circuit (`f = deg irr`). -/
theorem fieldPoly_gateMask (irr : Polynomial (ZMod 2)) (hm : irr.Monic) (f : ℕ) (hf : irr.natDegree = f)
    (gs : List (ArithGate (AdjoinRoot irr))) (n : ℕ) :
    fieldPoly irr (Joins.codeCircuit (gs.map (gateMask irr hm f))) n = (⟨gs⟩ : ArithCircuit (AdjoinRoot irr)).poly n := by
  unfold fieldPoly
  rw [codeCircuit_gateMask, ← poly_mapCircuit (AdjoinRoot.mk irr), mapCircuit_comp]
  have h : ∀ c : AdjoinRoot irr, (⇑(AdjoinRoot.mk irr) ∘ fun c => NearCubicWires.WireExponent3_5.GF.toPoly
      (NearCubicWires.WireExponent3_5.GF.ofPoly (AdjoinRoot.modByMonicHom hm c) f)) c = id c := by
    intro c
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective c
    simp only [Function.comp_apply, id]
    rw [AdjoinRoot.modByMonicHom_mk, NearCubicWires.WireExponent3_5.GF.toPoly_ofPoly]
    · have := AdjoinRoot.mk_leftInverse hm (AdjoinRoot.mk irr p)
      rwa [AdjoinRoot.modByMonicHom_mk] at this
    · have := Polynomial.degree_modByMonic_lt p hm
      rwa [Polynomial.degree_eq_natDegree hm.ne_zero, hf] at this
  rw [mapCircuit_congr _ _ h, mapCircuit_id]

/-! ## The weights of the items -/

section Items

variable {F : Type} [Field F] [CharP F 2]

omit [CharP F 2] in
theorem toRouting_weight {ι : Type} (D : ℕ) (rd : ι → ℕ) (E : RAMTrace.Expr ι) :
    exprWeight D (toRouting (F := F) rd E) ≤ D * E.deg := by
  induction E with
  | zero => exact Nat.zero_le _
  | one => exact Nat.zero_le _
  | var i => simp [toRouting, exprWeight, RAMTrace.Expr.deg]
  | add a b iha ihb =>
    simp only [toRouting, exprWeight, RAMTrace.Expr.deg]
    exact max_le (iha.trans (Nat.mul_le_mul_left _ (le_max_left _ _)))
      (ihb.trans (Nat.mul_le_mul_left _ (le_max_right _ _)))
  | mul a b iha ihb =>
    simp only [toRouting, exprWeight, RAMTrace.Expr.deg]
    rw [Nat.mul_add]; exact Nat.add_le_add iha ihb

omit [Field F] [CharP F 2] in
theorem squares_weight (D r : ℕ) : exprWeight D (squares (F := F) r) = 2 ^ r := by
  induction r with
  | zero => rfl
  | succ r ih => simp only [squares, exprWeight, ih, pow_succ]; ring

omit [CharP F 2] in
theorem lamExpr_weight (D : ℕ) {m : ℕ} (row : Fin m → F) : exprWeight D (lamExpr row) ≤ 2 ^ (m - 1) := by
  unfold lamExpr
  suffices h : ∀ (rs : List (Fin m)), exprWeight D
      (rs.foldr (fun r acc => Routing.Expr.add (.mul (.const (row r)) (squares r.val)) acc) (.const 0)) ≤
        2 ^ (m - 1) from h _
  intro rs
  induction rs with
  | nil => exact Nat.zero_le _
  | cons r rs ih =>
    simp only [List.foldr_cons, exprWeight, squares_weight, Nat.zero_add]
    exact max_le (Nat.pow_le_pow_right (by norm_num) (by have := r.isLt; omega)) ih

omit [Field F] [CharP F 2] in
theorem routingItem_weight (l : Routing.Layout) (D : ℕ) (it : Routing.RoutingItem) :
    exprWeight D (it.expr (F := F) l) ≤ 2 * D := by
  cases it <;> simp only [Routing.RoutingItem.expr, exprWeight] <;> omega

omit [CharP F 2] in
theorem inputEqs_weight (D τ : ℕ) (lam : ℕ → Routing.Expr F) (hlam : ∀ j, exprWeight D (lam j) ≤ D)
    (Y : Routing.Expr F) (hY : exprWeight D Y ≤ D) (s : RAMTrace.RecSlot) :
    ∀ E ∈ inputEqs τ lam Y s, exprWeight D E ≤ 2 * D := by
  intro E hE
  obtain ⟨f, j⟩ := s
  cases f with
  | va => simp [inputEqs] at hE
  | ad =>
    simp only [inputEqs, List.mem_cons, List.not_mem_nil, or_false] at hE
    subst hE
    split
    · simp only [exprWeight]; have := hlam j; omega
    · omega
  | ts | ph | st =>
    simp only [inputEqs, List.mem_cons, List.not_mem_nil, or_false] at hE
    subst hE; omega
  | act | rgn =>
    simp only [inputEqs, List.mem_cons, List.not_mem_nil, or_false] at hE
    subst hE; simp only [exprWeight]; omega

omit [CharP F 2] in
/-- Every machine item's equation has weight `≤ 2D` (`lem:acsp-degree` degree table; the position term `λ_j` has weight
`≤ D`). -/
theorem machineItems_weight (l : Routing.Layout) (om K L : ℕ) (M : ACSP.Ram) (kind : Fin M.ops → RAMTrace.AluOp)
    (τ a D : ℕ) (lam : ℕ → Routing.Expr F) (hD : 1 ≤ D) (hlam : ∀ j, exprWeight D (lam j) ≤ D) :
    ∀ t ∈ machineItems l om K L M kind τ a lam, exprWeight D t.2 ≤ 2 * D := by
  have hT : ∀ (rd : RAMTrace.TVar → ℕ) q,
      exprWeight D (toRouting (F := F) rd (RAMTrace.timeEq M kind τ q)) ≤ 2 * D := by
    intro rd q
    have h1 := toRouting_weight (F := F) D rd (RAMTrace.timeEq M kind τ q)
    have h3 : D * (RAMTrace.timeEq M kind τ q).deg ≤ D * 2 := Nat.mul_le_mul_left D (EqDeg.timeEq_le M kind τ q)
    omega
  have hS : ∀ (rd : RAMTrace.SVar → ℕ) d q,
      exprWeight D (toRouting (F := F) rd (RAMTrace.sortEq d q)) ≤ 2 * D := by
    intro rd d q
    have h1 := toRouting_weight (F := F) D rd (RAMTrace.sortEq d q)
    have h3 : D * (RAMTrace.sortEq d q).deg ≤ D * 2 := Nat.mul_le_mul_left D (EqDeg.sortEq_le d q)
    omega
  have hO : ∀ (rd : RAMTrace.TVar → ℕ), exprWeight D (toRouting (F := F) rd (RAMTrace.outE M)) ≤ 2 * D := by
    intro rd
    have h1 := toRouting_weight (F := F) D rd (RAMTrace.outE M)
    have h3 : D * (RAMTrace.outE M).deg ≤ D * 1 := Nat.mul_le_mul_left D (EqDeg.outE_le M)
    omega
  have hA : ∀ (rd : RAMTrace.TVar → ℕ), exprWeight D (toRouting (F := F) rd (RAMTrace.accE M)) ≤ 2 * D := by
    intro rd
    have h1 := toRouting_weight (F := F) D rd (RAMTrace.accE M)
    have h3 : D * (RAMTrace.accE M).deg ≤ D * 1 := Nat.mul_le_mul_left D (EqDeg.accE_le M)
    omega
  intro t ht
  simp only [machineItems, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_cons,
    List.mem_range, List.not_mem_nil, or_false] at ht
  rcases ht with ((((((h | h) | h) | h) | h) | h) | h) | h
  · obtain ⟨q, -, rfl⟩ := h; exact hT _ q
  · obtain ⟨s, -, rfl⟩ := h; simp only [boolExpr, exprWeight]; omega
  · obtain ⟨cp, -, h⟩ := h
    rcases h with rfl | ⟨u, -, rfl⟩ <;> simp only [exprWeight] <;> omega
  · rcases h with ⟨b, -, rfl⟩ | rfl
    · exact hO _
    · exact hA _
  · obtain ⟨q, -, rfl⟩ := h; exact hS _ _ q
  · obtain ⟨s, -, rfl⟩ := h; simp only [boolExpr, exprWeight]; omega
  · obtain ⟨s, -, h⟩ := h
    rcases h with rfl | ⟨u, -, rfl⟩ <;> simp only [exprWeight] <;> omega
  · obtain ⟨s, -, ht⟩ := h
    rcases ht with ⟨E, hE, rfl⟩ | ⟨u, -, rfl⟩
    · exact inputEqs_weight D τ lam hlam _ (by simp only [exprWeight]; omega) s E hE
    · simp only [exprWeight]; omega

end Items

/-! ## D: the degree constraint of the instance -/

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Adapters.Joins NearCubicGates.Adapters.ShortPCP
open scoped Polynomial

/-- **Every read of an item is a bank offset** (`app:affine-embedding` access census: local bank, the two predecessor families, the
routing bank), at every clock request with `2 ≤ n ≤ t`. -/
def ItemsReadInBank (V : Verifier) : Prop :=
  ∀ (F : Type) [Field F] [CharP F 2] (r : ClockRequest), 2 ≤ r.1.1 → r.1.1 ≤ r.2 →
    ∀ lam : ℕ → Routing.Expr F, (∀ j, Routing.Circuit.ReadsIn (Routing.globalBank (ownLayout V r.2)) (lam j)) →
      ∀ t ∈ ownItems V r lam, Routing.Circuit.ReadsIn (Routing.globalBank (ownLayout V r.2)) t.2

/-- The uniform weights `1` on `X`, `2^{mH} − 1` on every neighbor variable. -/
def uniW (n mH : ℕ) : Fin (n + 1) → ℕ := fun j => if j.val = 0 then 1 else 2 ^ mH - 1

variable (V : Verifier) (irrPoly : ℕ → (ZMod 2)[X])

theorem lamExpr_reads {F : Type} [Field F] {m : ℕ} (bank : List ℕ) (row : Fin m → F) :
    Routing.Circuit.ReadsIn bank (lamExpr row) := by
  unfold lamExpr
  suffices h : ∀ rs : List (Fin m), Routing.Circuit.ReadsIn bank
      (rs.foldr (fun r acc => Routing.Expr.add (.mul (.const (row r)) (squares r.val)) acc) (.const 0)) from h _
  have hsq : ∀ r, Routing.Circuit.ReadsIn bank (squares (F := F) r) := by
    intro r; induction r with
    | zero => trivial
    | succ r ih => exact ih
  intro rs
  induction rs with
  | nil => trivial
  | cons r rs ih => exact ⟨⟨trivial, hsq _⟩, ih⟩

theorem baseIrr_eq (r : ClockRequest) (hdeg : (irrPoly (fieldExp V r.2)).natDegree = fieldExp V r.2) :
    baseIrr V irrPoly r = irrPoly (fieldExp V r.2) := by
  unfold baseIrr
  unfold ACSP.Affine.Instance.irrPoly
  rw [ownInst_irr]
  unfold modMask
  apply NearCubicWires.WireExponent3_5.GF.toPoly_ofPoly
  exact lt_of_le_of_lt Polynomial.degree_le_natDegree (by rw [hdeg]; exact_mod_cast Nat.lt_succ_self _)

theorem modulusGood (hI : Published.Shoup.IrreducibleChoice irrPoly) (r : ClockRequest) : ModulusGood V irrPoly r := by
  have hf : 1 ≤ fieldExp V r.2 := by have := domExp_add_two_le_fieldExp V r.2; omega
  obtain ⟨h1, h2⟩ := hI _ hf
  unfold ModulusGood
  rw [baseIrr_eq V irrPoly r h2]
  exact ⟨h1, h2⟩

/-- The weighted degree of the field circuit, at the bank arity (`lem:acsp-degree`, via the circuit correctness theorem). -/
theorem ownCircuit_wdeg (hRI : ItemsReadInBank V) (r : ClockRequest)
    (hn : 2 ≤ r.1.1) (hnt : r.1.1 ≤ r.2) (h : ModulusGood V irrPoly r) (n : ℕ)
    (hlen : n = (Routing.globalBank (ownLayout V r.2)).length) :
    MvPolynomial.weightedTotalDegree (uniW n (ownLayout V r.2).m) ((ownCircuit V irrPoly r h).poly (n + 1)) ≤
      (ownLayout V r.2).m * 2 ^ ((ownLayout V r.2).m - 1) + 2 * (2 ^ (ownLayout V r.2).m - 1) := by
  subst hlen
  haveI : Fact (Irreducible (baseIrr V irrPoly r)) := ⟨h.1⟩
  unfold ownCircuit
  simp only
  rw [(Routing.Circuit.compileTerms_correct _ _ _ (hRI _ r hn hnt _ (fun j => by
    split
    · exact lamExpr_reads _ _
    · trivial))).2.2.1]
  have hD : 1 ≤ 2 ^ (ownLayout V r.2).m - 1 := by
    have : 2 ≤ 2 ^ (ownLayout V r.2).m := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ (ownLayout V r.2).m := Nat.pow_le_pow_right (by norm_num) (by simp [ownLayout, Routing.Layout.m])
    omega
  refine (WDeg.rename_le (Routing.weight (ownLayout V r.2).m) _ _ ?_ _).trans ?_
  · intro v
    cases v with
    | none =>
      simp only [uniW, Routing.encodeVar, Routing.readIndex, Routing.weight]
      simp
    | some b =>
      simp only [uniW, Routing.weight]
      split <;> omega
  · refine emit_wdeg_le _ _ _ fun t ht => ?_
    obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht
    refine (expr_wdeg_le _ t0.2).trans ?_
    rcases List.mem_append.mp ht0 with hr | hm
    · obtain ⟨it, -, rfl⟩ := List.mem_map.mp hr
      exact routingItem_weight _ _ it
    · refine machineItems_weight _ _ _ _ _ _ _ _ _ _ hD (fun j => ?_) t0 hm
      split
      · refine (lamExpr_weight _ _).trans ?_
        have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (Nat.sub_le (ownLayout V r.2).m 1)
        have h2 : 2 ^ ((ownLayout V r.2).m - 1) * 2 = 2 ^ (ownLayout V r.2).m := by
          rw [← pow_succ]; congr 1
        omega
      · exact Nat.zero_le _

theorem instance_consPoly (c : ACSP.Affine.Instance) :
    c.consPoly = fieldPoly c.irrPoly (codeCircuit c.cons) (c.cN + 1) := rfl

theorem arithCircuit_mk_gates {R : Type} (c : ArithCircuit R) : (⟨c.gates⟩ : ArithCircuit R) = c := by
  cases c; rfl

/-- Serializing and reading the reduced constant masks preserves the actual
constraint polynomial, at the unchanged neighbor arity. -/
theorem ownConsPoly_eq_circuit (r : ClockRequest) (hG : ModulusGood V irrPoly r) :
    (ownInst V irrPoly (ownCons V irrPoly) r).consPoly =
      (ownCircuit V irrPoly r hG).poly ((ownInst V irrPoly (ownCons V irrPoly) r).cN + 1) := by
  have e1 : (ownInst V irrPoly (ownCons V irrPoly) r).cons = ownConsOf V irrPoly r hG := by
    rw [ownInst_cons]; unfold ownCons; exact dif_pos hG
  have e2 := fieldPoly_gateMask (baseIrr V irrPoly r) (modulus_monic hG.1) (fieldExp V r.2) hG.2
    (ownCircuit V irrPoly r hG).gates ((ownInst V irrPoly (ownCons V irrPoly) r).cN + 1)
  rw [arithCircuit_mk_gates] at e2
  refine Eq.trans ?_ e2
  rw [instance_consPoly, e1]
  rfl

/-- Polynomial and weight equalities transport a weighted-degree certificate
to the literal support condition of the affine instance. -/
theorem hasDegreeBound_of_polynomial (c : ACSP.Affine.Instance)
    (p : MvPolynomial (Fin (c.cN + 1)) c.Fld) (w : Fin (c.cN + 1) → ℕ) (d : ℕ)
    (hP : c.consPoly = p) (hW : c.weight = w)
    (hB : MvPolynomial.weightedTotalDegree w p ≤ d) : c.HasDegreeBound d := by
  apply (WDeg.le_iff c.weight).mp
  rw [hP, hW]
  exact hB

/-- The actual emitted constraint satisfies the support-weight certificate of
`def:acsp`, with the explicit degree budget. -/
theorem degreeBound (hRI : ItemsReadInBank V)
    (hI : Published.Shoup.IrreducibleChoice irrPoly) : DegreeBound V irrPoly (ownCons V irrPoly) := by
  intro r hn hnt
  have hG := modulusGood V irrPoly hI r
  have hPoly := ownConsPoly_eq_circuit V irrPoly r hG
  have hW : (ownInst V irrPoly (ownCons V irrPoly) r).weight =
      uniW (ownInst V irrPoly (ownCons V irrPoly) r).cN (ownLayout V r.2).m := by
    funext j
    simp only [ACSP.Affine.Instance.weight, uniW, ownInst_mH]
  have hc := ownCircuit_wdeg V irrPoly hRI r hn hnt hG
    (ownInst V irrPoly (ownCons V irrPoly) r).cN (ownInst_cN V irrPoly (ownCons V irrPoly) r)
  have hB : (ownLayout V r.2).m * 2 ^ ((ownLayout V r.2).m - 1) + 2 * (2 ^ (ownLayout V r.2).m - 1) ≤
      degreeBudget V r.2 := by
    rw [ownLayout_m]
    unfold degreeBudget
    have h1 : domExp V r.2 * 2 ^ (domExp V r.2 - 1) ≤ domExp V r.2 * 2 ^ domExp V r.2 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _))
    have he : (domExp V r.2 + 4) * 2 ^ domExp V r.2 = domExp V r.2 * 2 ^ domExp V r.2 + 4 * 2 ^ domExp V r.2 := by
      ring
    omega
  exact ⟨degreeBudget V r.2,
    hasDegreeBound_of_polynomial (ownInst V irrPoly (ownCons V irrPoly) r)
      ((ownCircuit V irrPoly r hG).poly ((ownInst V irrPoly (ownCons V irrPoly) r).cN + 1))
      (uniW (ownInst V irrPoly (ownCons V irrPoly) r).cN (ownLayout V r.2).m)
      (degreeBudget V r.2) hPoly hW (hc.trans hB),
    four_degreeBudget_le V r.2⟩

end NearCubicGates.Adapters.RAMACSP
