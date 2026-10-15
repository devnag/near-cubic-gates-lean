import Proof.Gates.CounterMachine.ReqLayout
import Proof.Gates.ResidueCounts

set_option autoImplicit false

namespace NearCubicGates.Close.CounterMachine

open NearCubicWires NearCubicGates NearCubicGates.Close.Counter NearCubicGates.Close.Tabulator
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats

/-! ## Residue polynomials with formula-valued forms -/

section Res
variable {V r : ℕ}

/-- `Amp_e(∏_i (1 − (f_i − ρ_i)^{p−1}))` (lem:residue-count, line 1511) with formula-valued forms. -/
def resF (p e : ℕ) (f : Fin r → Formula V) (ρ : Fin r → ℤ) : Formula V :=
  Formula.amp e (Formula.prodList ((List.finRange r).map fun i =>
    .sub (.const 1) (.pow (.sub (f i) (.const (ρ i))) (p - 1))))

theorem resF_eval (p e : ℕ) (f : Fin r → Formula V) (ρ : Fin r → ℤ) (β : Fin V → ℤ) :
    (resF p e f ρ).eval β = ResidueCounts.liftedIndicator p e (fun i => (f i).eval β) ρ := by
  simp only [resF, Formula.eval_amp, ResidueCounts.liftedIndicator, Formula.eval_prodList, List.map_map,
    Function.comp_def, Formula.eval, ResidueCounts.fermatProduct]
  rw [Fin.prod_univ_def]

theorem resF_degree_le (p e : ℕ) (f : Fin r → Formula V) (ρ : Fin r → ℤ) (hf : ∀ i, (f i).degree ≤ 1) :
    (resF p e f ρ).degree ≤ (2 * e - 1) * r * (p - 1) := by
  refine (Formula.degree_amp_le e _).trans ?_
  rw [mul_assoc]
  refine Nat.mul_le_mul_left _ ((Formula.degree_prodList_le _).trans ?_)
  rw [List.map_map]
  have hle : ∀ (l : List (Fin r)), (l.map ((Formula.degree) ∘ fun i =>
      Formula.sub (.const 1) (.pow (.sub (f i) (.const (ρ i))) (p - 1)))).sum ≤ l.length * (p - 1) := by
    intro l
    induction l with
    | nil => simp
    | cons i l ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, Function.comp_apply]
      have h1 : (Formula.sub (.const 1) (.pow (.sub (f i) (.const (ρ i))) (p - 1)) : Formula V).degree ≤ p - 1 := by
        simp only [Formula.degree, Nat.zero_max, max_zero]
        have := hf i
        calc (p - 1) * (f i).degree ≤ (p - 1) * 1 := Nat.mul_le_mul_left _ this
          _ = p - 1 := by ring
      nlinarith
  simpa using hle (List.finRange r)

/-- lem:residue-count for formula-valued forms. -/
theorem resF_count {k : ℕ} (p : ℕ) (hp : Nat.Prime p) (e : ℕ) (he : 1 ≤ e) (f : Fin r → Formula V)
    (ρ : Fin r → ℤ) (H : Finset (Fin k → Bool)) (point : (Fin k → Bool) → Fin V → Bool) (hH : H.card < p ^ e) :
    (∑ x ∈ H, (resF p e f ρ).eval (boolPoint (point x))) % ((p : ℤ) ^ e) =
      ((H.filter fun x => ∀ i, (f i).eval (boolPoint (point x)) ≡ ρ i [ZMOD (p : ℤ)]).card : ℤ) := by
  classical
  have hmod : (∑ x ∈ H, (resF p e f ρ).eval (boolPoint (point x))) ≡
      ∑ x ∈ H, (if ∀ i, (f i).eval (boolPoint (point x)) ≡ ρ i [ZMOD (p : ℤ)] then (1 : ℤ) else 0)
        [ZMOD (p : ℤ) ^ e] := by
    apply Int.ModEq.sum
    intro x _
    rw [resF_eval]
    convert ResidueCounts.liftedIndicator_modEq p hp e he (fun i => (f i).eval (boolPoint (point x))) ρ using 2
  rw [Finset.sum_boole] at hmod
  have hcard : (H.filter fun x => ∀ i, (f i).eval (boolPoint (point x)) ≡ ρ i [ZMOD (p : ℤ)]).card < p ^ e :=
    (Finset.card_filter_le _ _).trans_lt hH
  have hlt : (((H.filter fun x => ∀ i, (f i).eval (boolPoint (point x)) ≡ ρ i [ZMOD (p : ℤ)]).card : ℕ) : ℤ)
      < (p : ℤ) ^ e := by exact_mod_cast hcard
  exact hmod.eq.trans (Int.emod_eq_of_lt (by positivity) hlt)

end Res

/-! ## Linear forms over the gate variables -/

section Lin
variable {V : ℕ}

/-- The variable with index `i` (the constant `0` past the end). -/
def varN (i : ℕ) : Formula V := if h : i < V then .var ⟨i, h⟩ else .const 0

/-- `Σ_{t < m} a_t · x_{off+t}`. -/
def linF (off m : ℕ) (a : List ℤ) : Formula V :=
  Formula.sumList ((List.range m).map fun t => .mul (.const (a.getD t 0)) (varN (off + t)))

theorem varN_degree (i : ℕ) : (varN (V := V) i).degree ≤ 1 := by
  unfold varN; split <;> simp [Formula.degree]

theorem linF_degree (off m : ℕ) (a : List ℤ) : (linF (V := V) off m a).degree ≤ 1 := by
  apply Formula.degree_sumList_le
  intro f hf
  simp only [List.mem_map, List.mem_range] at hf
  obtain ⟨t, _, rfl⟩ := hf
  simp only [Formula.degree, Nat.zero_add]
  exact varN_degree _

theorem varN_eval (i : ℕ) (hi : i < V) (β : Fin V → ℤ) : (varN (V := V) i).eval β = β ⟨i, hi⟩ := by
  simp [varN, hi, Formula.eval]

theorem linF_eval (off m : ℕ) (a : List ℤ) (β : Fin V → ℤ) (hV : off + m ≤ V) :
    (linF (V := V) off m a).eval β =
      ((List.range m).map fun t => a.getD t 0 * if h : off + t < V then β ⟨off + t, h⟩ else 0).sum := by
  unfold linF
  rw [Formula.eval_sumList, List.map_map]
  congr 1
  apply List.map_congr_left
  intro t ht
  simp only [List.mem_range] at ht
  simp only [Function.comp_apply, Formula.eval]
  rw [varN_eval _ (by omega), dif_pos (by omega)]

/-- **`linF` computes `linForm`** when the variables `off, …, off + m − 1` hold the gate values. -/
theorem linF_linForm {n : ℕ} (z : BitInput n) (β : Fin V → ℤ) :
    ∀ (gs : List (NormalizedThresholdGate n)) (off : ℕ) (a : List ℤ) (hV : off + gs.length ≤ V),
      (∀ t (ht : t < gs.length), β ⟨off + t, by omega⟩ = if gs[t].eval z then 1 else 0) →
      (linF (V := V) off gs.length a).eval β = linForm gs a z
  | [], off, a, _, _ => by simp [linF, Formula.sumList, Formula.eval, linForm]
  | g :: gs, off, a, hV, hβ => by
    have ih := linF_linForm z β gs (off + 1) a.tail (by simp only [List.length_cons] at hV; omega)
      (fun t ht => by
        have := hβ (t + 1) (by simp; omega)
        simp only [List.getElem_cons_succ] at this
        have e : (⟨off + 1 + t, by simp only [List.length_cons] at hV; omega⟩ : Fin V) =
            ⟨off + (t + 1), by simp only [List.length_cons] at hV; omega⟩ := Fin.ext (by show off + 1 + t = off + (t + 1); omega)
        rw [e]; exact this)
    have e1 : (linF (V := V) off (g :: gs).length a).eval β =
        a.getD 0 0 * β ⟨off, by simp only [List.length_cons] at hV; omega⟩ + (linF (V := V) (off + 1) gs.length a.tail).eval β := by
      unfold linF
      rw [List.length_cons, List.range_succ_eq_map, List.map_cons, Formula.sumList, Formula.eval, List.map_map]
      congr 1
      · simp only [Formula.eval, Nat.add_zero]
        rw [varN_eval _ (by simp only [List.length_cons] at hV; omega)]
      · congr 2
        apply List.map_congr_left
        intro t _
        simp only [Function.comp_apply]
        have h1 : a.getD (t + 1) 0 = a.tail.getD t 0 := by cases a <;> simp
        have h2 : off + (t + 1) = off + 1 + t := by omega
        rw [h1, h2]
    rw [e1, ih]
    have h0 := hβ 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at h0
    rw [h0]
    cases a with
    | nil => simp [linForm]
    | cons a0 as => simp [linForm, List.zip_cons_cons]

end Lin

end NearCubicGates.Close.CounterMachine
