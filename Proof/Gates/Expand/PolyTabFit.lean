import Proof.Gates.Expand.PolyTabOK3

set_option autoImplicit false

namespace NearCubicGates.Close.Expand.PolyTab

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Tabulator NearCubicGates.Close.TabMachine
open NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Expand

variable (E : ExpandMachine)

theorem lt_two_pow_nbl' (x : ℕ) : x < 2 ^ natBitLength x := Nat.lt_pow_succ_log_self (by norm_num) x

theorem coef_lt_Cm (r : TabReq) (t : Finset (Fin r.V) × ℤ) (ht : t ∈ (tabT E r).Q) : t.2.natAbs < 2 ^ Cm E r :=
  lt_of_lt_of_le (lt_two_pow_nbl' _) (Nat.pow_le_pow_right (by norm_num)
    (le_foldr_max _ _ (List.mem_map_of_mem (f := fun t : Finset (Fin r.V) × ℤ => natBitLength t.2.natAbs) ht)))

/-- The bounds with the degree bound `V` and the coefficient bound `Cm`. -/
theorem tabT_boundsV (r : TabReq) : (tabT E r).Bounds r.B r.V (Cm E r) where
  gates := r.hB
  nodup := (E.ok ⟨r.V, r.F⟩).nodup
  degree := fun S _ => (Finset.card_le_univ _).trans (by simp)
  coeff := coef_lt_Cm E r

theorem fits_mono {p q : ℕ} (h : p ≤ q) {c : MatrixScoreBatch.Cut} (hc : EquationRow.Fits p c) : EquationRow.Fits q c := by
  have hp : 2 ^ p ≤ 2 ^ q := Nat.pow_le_pow_right (by norm_num) h
  exact ⟨fun w hw => lt_of_lt_of_le (hc.1 w hw) hp, lt_of_lt_of_le hc.2.1 hp, lt_of_lt_of_le hc.2.2 hp⟩

theorem Wk_le_Wdk (r : TabReq) : Wk E r ≤ Wdk E r := by have := Wdk_succ E r; nlinarith

theorem fieldBits_le (r : TabReq) : fieldBits r.n r.s r.V r.B (Cm E r) ≤ Wdk E r := by
  unfold fieldBits
  refine max_le ?_ (le_trans (by unfold Wk; omega) (Wk_le_Wdk E r))
  set a := r.V * (r.s + 1) with ha
  set b := 2 * r.B + 2 * r.n + 4 * r.s + 10 with hb
  have hCB : CB r < 2 ^ b := CB_lt r
  have h1 : r.V * ((r.s + 1) * CB r) + 1 ≤ 2 ^ (a + b) := by
    have := mul_succ_le_two_pow (r.V * (r.s + 1)) (CB r) a b Nat.lt_two_pow_self hCB
    rw [mul_assoc] at this; exact this
  have h2 : r.V * ((r.s + 1) * CB r) + 1 + 1 ≤ 2 ^ (a + b + 1) := by
    have : 1 ≤ 2 ^ (a + b) := Nat.one_le_two_pow
    rw [pow_succ]; omega
  have h3 : fieldBound r.n r.s r.V r.B < 2 ^ (b + (a + b + 1) * r.V) := by
    unfold fieldBound
    rw [pow_add, pow_mul]
    exact Nat.mul_lt_mul_of_lt_of_le hCB (Nat.pow_le_pow_left h2 _) (by positivity)
  have h4 : Nat.size (fieldBound r.n r.s r.V r.B) ≤ b + (a + b + 1) * r.V := Nat.size_le.mpr h3
  refine le_trans h4 (le_trans ?_ (Wk_le_Wdk E r))
  refine le_trans ?_ (Wk_dm E r)
  unfold Dm
  have : b + (a + b + 1) * r.V ≤ (r.V + 2) * (a + b + 1) := by nlinarith
  refine le_trans this (Nat.mul_le_mul_left _ ?_)
  omega

theorem fits_Wd (r : TabReq) : ∀ c ∈ (tabT E r).exactCuts, EquationRow.Fits (Wdk E r) c := fun c hc =>
  fits_mono (fieldBits_le E r) ((tabT E r).fits_of_bounds r.B r.V (Cm E r) (tabT_boundsV E r) c hc)

theorem capT (r : TabReq) : (tabT E r).exactCuts.length ^ 100 ≤ 2 ^ r.s :=
  (tabT E r).capacity_of_condition r.B r.F.degree (r.F.weight + 1) (tabT_bounds E r) r.hc

theorem s67 (r : TabReq) : 67 ≤ r.s := printCondition_s _ _ _ _ _ r.hc

/-- The printer's input. -/
noncomputable def inp (r : TabReq) : EquationRow.Input := (tabT E r).input (Wdk E r) (fits_Wd E r) (s67 r) (capT E r)

theorem inp_d (r : TabReq) : (inp E r).d = (r.s + 1) / 2 := rfl
theorem inp_p (r : TabReq) : (inp E r).p = Wdk E r := rfl
theorem inp_odd (r : TabReq) : (inp E r).odd = decide (r.s % 2 = 1) := rfl
theorem inp_cuts (r : TabReq) : (inp E r).cuts = (tabT E r).exactCuts := rfl

theorem pow100_le {x m : ℕ} (h : x ^ 100 ≤ 2 ^ m) : x ≤ 2 ^ (m / 100 + 1) := by
  by_contra hc
  have h2 : (2 ^ (m / 100 + 1)) ^ 100 < x ^ 100 := Nat.pow_lt_pow_left (by omega) (by norm_num)
  rw [← pow_mul] at h2
  have h3 : 2 ^ m < 2 ^ ((m / 100 + 1) * 100) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega

/-- `back_spec`'s gate bound. -/
theorem inp_hg (r : TabReq) : (inp E r).cuts.length ≤ 2 ^ (inp E r).d := by
  rw [inp_cuts, inp_d]
  have := s67 r
  exact le_trans (pow100_le (capT E r)) (Nat.pow_le_pow_right (by norm_num) (by omega))

/-! ## The width of the printed records -/

theorem monomialValue_abs {V : ℕ} (b : Fin V → Bool) (S : Finset (Fin V)) : (monomialValue b S).natAbs ≤ 1 := by
  unfold monomialValue; split_ifs <;> simp

theorem eval_abs {V : ℕ} (b : Fin V → Bool) (P : Terms V) : (Terms.eval b P).natAbs ≤ Terms.absSum P := by
  induction P with
  | nil => simp [Terms.eval]
  | cons t P ih =>
    have e : Terms.eval b (t :: P) = t.2 * monomialValue b t.1 + Terms.eval b P := by simp [Terms.eval]
    rw [e, Terms.absSum_cons]
    have h1 := Int.natAbs_add_le (t.2 * monomialValue b t.1) (Terms.eval b P)
    have h2 : (t.2 * monomialValue b t.1).natAbs ≤ t.2.natAbs := by
      rw [Int.natAbs_mul]
      calc t.2.natAbs * (monomialValue b t.1).natAbs ≤ t.2.natAbs * 1 :=
          Nat.mul_le_mul_left _ (monomialValue_abs b t.1)
        _ = t.2.natAbs := by ring
    omega

theorem absSum_le_card (r : TabReq) : Terms.absSum (tabT E r).Q ≤ (tabT E r).Q.length * 2 ^ Cm E r := by
  unfold Terms.absSum
  have := List.sum_le_card_nsmul ((tabT E r).Q.map fun t => t.2.natAbs) (2 ^ Cm E r) (by
    intro x hx; obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx; exact (coef_lt_Cm E r t ht).le)
  simpa using this

theorem Q_length (r : TabReq) : (tabT E r).Q.length ≤ 2 ^ r.V := by
  have hnd : (Terms.keys (tabT E r).Q).Nodup := (E.ok ⟨r.V, r.F⟩).nodup
  have := hnd.length_le_card
  simp only [Terms.keys, List.length_map, Fintype.card_finset, Fintype.card_fin] at this
  exact this

theorem target_abs (r : TabReq) (y : Fin r.s → Bool) :
    ((tabT E r).target y).natAbs ≤ 2 ^ r.k * (2 ^ r.V * 2 ^ Cm E r) := by
  unfold Tabulation.target
  have h1 : ∀ x ∈ (tabT E r).H, (Terms.eval ((tabT E r).value y x) (tabT E r).Q).natAbs ≤ 2 ^ r.V * 2 ^ Cm E r :=
    fun x _ => (eval_abs _ _).trans ((absSum_le_card E r).trans (Nat.mul_le_mul_right _ (Q_length E r)))
  have h2 := Finset.abs_sum_le_sum_abs (fun x => Terms.eval ((tabT E r).value y x) (tabT E r).Q) (tabT E r).H
  have h3 : ((tabT E r).H.card : ℕ) ≤ 2 ^ r.k := by
    have := Finset.card_le_univ (tabT E r).H
    simpa using this
  have h4 : (∑ x ∈ (tabT E r).H, (Terms.eval ((tabT E r).value y x) (tabT E r).Q).natAbs) ≤
      (tabT E r).H.card * (2 ^ r.V * 2 ^ Cm E r) := by
    have := Finset.sum_le_card_nsmul (tabT E r).H _ _ h1
    simpa using this
  have h6 : (∑ x ∈ (tabT E r).H, Terms.eval ((tabT E r).value y x) (tabT E r).Q).natAbs ≤
      ∑ x ∈ (tabT E r).H, (Terms.eval ((tabT E r).value y x) (tabT E r).Q).natAbs := by
    have := h2; simp only [Int.abs_eq_natAbs] at this; exact_mod_cast this
  exact h6.trans (h4.trans (Nat.mul_le_mul_right _ h3))

/-- The record width of the printed table. -/
noncomputable def width (r : TabReq) : ℕ := qOf (inp E r) + 1

theorem width_fits (r : TabReq) (y : Fin r.s → Bool) : WordPrograms.SInt.encS (tabTarget r y) < 2 ^ width E r := by
  rw [← tabT_target E r y]
  have h1 := target_abs E r y
  set z := (tabT E r).target y
  have h2 : WordPrograms.SInt.encS z ≤ 2 * z.natAbs + 1 := by unfold WordPrograms.SInt.encS; split_ifs <;> omega
  have h3 : 2 ^ r.k * (2 ^ r.V * 2 ^ Cm E r) = 2 ^ (r.k + r.V + Cm E r) := by rw [pow_add, pow_add]; ring
  have h4 : r.k + r.V + Cm E r + 1 < width E r := by
    have := Wk_le_Wdk E r
    have := Wk_ge0 E r
    have : Cm E r ≤ Wk E r := by unfold Wk; omega
    have : r.V ≤ r.V * (r.s + 1) := Nat.le_mul_of_pos_right _ (by omega)
    unfold width qOf; rw [inp_p]; unfold Dm at *; omega
  have h5 : 2 * 2 ^ (r.k + r.V + Cm E r) + 1 < 2 ^ width E r := by
    have : 2 ^ (r.k + r.V + Cm E r + 2) ≤ 2 ^ width E r := Nat.pow_le_pow_right (by norm_num) (by omega)
    have e : 2 ^ (r.k + r.V + Cm E r + 2) = 4 * 2 ^ (r.k + r.V + Cm E r) := by rw [pow_add]; ring
    have : 1 ≤ 2 ^ (r.k + r.V + Cm E r) := Nat.one_le_two_pow
    omega
  omega

/-! ## The printer's order is a permutation -/

theorem printerOrder_mem (s x : ℕ) : x ∈ CounterMachine.printerOrder s ↔ x < 2 ^ s := by
  unfold CounterMachine.printerOrder
  simp only [List.mem_flatMap, List.mem_range, List.mem_map]
  have hs : 2 ^ s = 2 ^ ((s + 1) / 2) * 2 ^ (s / 2) := by rw [← pow_add]; congr 1; omega
  constructor
  · rintro ⟨i, hi, j, hj, rfl⟩
    rw [hs]
    have : 2 ^ ((s + 1) / 2) * j + 2 ^ ((s + 1) / 2) ≤ 2 ^ ((s + 1) / 2) * 2 ^ (s / 2) := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hj
    omega
  · intro hx
    have hp : 0 < 2 ^ ((s + 1) / 2) := Nat.two_pow_pos _
    refine ⟨x % 2 ^ ((s + 1) / 2), Nat.mod_lt _ hp, x / 2 ^ ((s + 1) / 2), ?_, ?_⟩
    · rw [hs] at hx; exact Nat.div_lt_of_lt_mul hx
    · exact Nat.mod_add_div x _

theorem printerOrder_nodup (s : ℕ) : (CounterMachine.printerOrder s).Nodup := by
  unfold CounterMachine.printerOrder
  have hp : 0 < 2 ^ ((s + 1) / 2) := Nat.two_pow_pos _
  rw [List.nodup_flatMap]
  refine ⟨fun i hi => ?_, ?_⟩
  · refine (List.nodup_range).map_on fun a _ b _ h => ?_
    have : 2 ^ ((s + 1) / 2) * a = 2 ^ ((s + 1) / 2) * b := by omega
    exact Nat.eq_of_mul_eq_mul_left hp this
  · refine List.nodup_range.pairwise_of_forall_ne fun i hi i' hi' hne => ?_
    simp only [List.mem_range] at hi hi'
    intro x hx hx'
    simp only [List.mem_map, List.mem_range] at hx hx'
    obtain ⟨j, _, rfl⟩ := hx
    obtain ⟨j', _, e⟩ := hx'
    have h1 := congrArg (· % 2 ^ ((s + 1) / 2)) e
    simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hi'] at h1
    exact hne h1.symm

theorem printerOrder_perm (s : ℕ) : (CounterMachine.printerOrder s).Perm (List.range (2 ^ s)) :=
  (List.perm_ext_iff_of_nodup (printerOrder_nodup s) List.nodup_range).mpr fun x => by
    rw [printerOrder_mem, List.mem_range]

end NearCubicGates.Close.Expand.PolyTab
