import Proof.Wire_3_5.RowsThr

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Rows
open NearCubicWires.WireExponent3_5.Shared ZMod Finset Matrix
open scoped Matrix.Norms.L2Operator

section Means
variable {N Q : ℕ}

/-- The live-pair average `E_{u,v∈[N]} f(u,v)`. -/
noncomputable def liveMean (f : Fin N → Fin N → ℝ) : ℝ := (∑ u, ∑ v, f u v) / (N : ℝ) ^ 2

/-- The sample average `(1/Q)Σ_ℓ f(U_ℓ,V_ℓ)`. -/
noncomputable def sampleMean (S : Fin Q → Fin N × Fin N) (f : Fin N → Fin N → ℝ) : ℝ :=
  (∑ l, f (S l).1 (S l).2) / Q

theorem bitR_cast (b : Bool) : ((bitR b : ℝ) : ℂ) = bitC b := by cases b <;> simp [bitR, bitC]

/-- A real row with a separable complex expansion obeys the separable sample bound. -/
theorem real_sample_error {T Λ : Type} [Fintype T] [Fintype Λ] (hN : 0 < N) (hQ : 0 < Q) (f : Fin N → Fin N → ℝ)
    (G : Fin N → Fin N → ℂ) (H : T → Fin N → Fin N → ℂ) (c : T → Λ → ℂ) (a b : Λ → Fin N → ℂ)
    (ha : ∀ lam i, ‖a lam i‖ ≤ 1) (hb : ∀ lam i, ‖b lam i‖ ≤ 1) (S : Fin Q → Fin N × Fin N) (η : ℝ)
    (hη : ∀ t, ‖sampleError (stateMatrix G H t) S‖ / (Q * N) ≤ η)
    (hf : ∀ u v, (f u v : ℂ) = separableRow G H c a b u v) :
    |liveMean f - sampleMean S f| ≤ (∑ t, ∑ lam, ‖c t lam‖) * η := by
  have h := separable_sample_error hN hQ G H c a b ha hb S η hη
  have hcast : ((liveMean f - sampleMean S f : ℝ) : ℂ) =
      (∑ u, ∑ v, separableRow G H c a b u v) / (N : ℂ) ^ 2 -
        (∑ j, separableRow G H c a b (S j).1 (S j).2) / (Q : ℂ) := by
    simp only [liveMean, sampleMean, ← hf]
    push_cast
    rfl
  rw [← hcast, Complex.norm_real, Real.norm_eq_abs] at h
  exact h

theorem liveMean_sum {ι : Type} [Fintype ι] (w : ι → ℝ) (f : ι → Fin N → Fin N → ℝ) :
    liveMean (fun u v => ∑ i, w i * f i u v) = ∑ i, w i * liveMean (f i) := by
  unfold liveMean
  rw [show (∑ i, w i * ((∑ u, ∑ v, f i u v) / (N : ℝ) ^ 2)) = (∑ i, w i * ∑ u, ∑ v, f i u v) / (N : ℝ) ^ 2 by
    rw [Finset.sum_div]; exact Finset.sum_congr rfl fun i _ => by ring]
  congr 1
  simp only [Finset.mul_sum]
  calc ∑ u, ∑ v, ∑ i, w i * f i u v = ∑ u, ∑ i, ∑ v, w i * f i u v :=
        Finset.sum_congr rfl fun u _ => Finset.sum_comm
    _ = ∑ i, ∑ u, ∑ v, w i * f i u v := Finset.sum_comm

theorem sampleMean_sum {ι : Type} [Fintype ι] (S : Fin Q → Fin N × Fin N) (w : ι → ℝ)
    (f : ι → Fin N → Fin N → ℝ) :
    sampleMean S (fun u v => ∑ i, w i * f i u v) = ∑ i, w i * sampleMean S (f i) := by
  unfold sampleMean
  rw [Finset.sum_comm]
  simp only [Finset.sum_div, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring

end Means

section Sym
variable {N Q a : ℕ}

abbrev SymState (m : Fin a → ℕ) : Type := (j : Fin a) → Fin (m j + 1) × Fin (m j + 1)

theorem card_symState (m : Fin a → ℕ) : Fintype.card (SymState m) = ∏ j, (m j + 1) ^ 2 := by
  simp [SymState, Fintype.card_pi, Fintype.card_prod, sq]

/-- The signed state shift `t_j^+ − t_j^−`. -/
def symShift (m : Fin a → ℕ) (τ : SymState m) (j : Fin a) : ℤ := ((τ j).1 : ℤ) - (τ j).2

noncomputable def symRow (m : Fin a → ℕ) (g : Fin a → ℤ → Bool) (G : Fin N → Fin N → Bool)
    (H : SymState m → Fin N → Fin N → Bool) (A B : Fin a → Fin N → ℤ) (u v : Fin N) : ℝ :=
  bitR (G u v) * ∑ τ, bitR (H τ u v) * ∏ j, bitR (g j (A j u + B j v + symShift m τ j))

/-- The SYM state matrices `D_{e,τ} = G_e·H_{e,τ}` (row:matrix) as complex matrices. -/
noncomputable def symStateMatrix (m : Fin a → ℕ) (G : Fin N → Fin N → Bool) (H : SymState m → Fin N → Fin N → Bool)
    (τ : SymState m) : Fin N → Fin N → ℂ :=
  stateMatrix (fun u v => bitC (G u v)) (fun τ u v => bitC (H τ u v)) τ

theorem sym_sampler_interface (hN : 0 < N) (hQ : 0 < Q) (m : Fin a → ℕ) (g : Fin a → ℤ → Bool)
    (G : Fin N → Fin N → Bool) (H : SymState m → Fin N → Fin N → Bool) (A B : Fin a → Fin N → ℤ)
    (hA : ∀ j u, -(m j : ℤ) ≤ A j u ∧ A j u ≤ m j) (hB : ∀ j v, 0 ≤ B j v ∧ B j v ≤ m j)
    (S : Fin Q → Fin N × Fin N) (η : ℝ) (hη0 : 0 ≤ η)
    (hη : ∀ τ, ‖sampleError (symStateMatrix m G H τ) S‖ / (Q * N) ≤ η) :
    |liveMean (symRow m g G H A B) - sampleMean S (symRow m g G H A B)| ≤
      ((∏ j, ((m j + 1) ^ 2 : ℕ) : ℝ) * ∏ j, (symModulus (m j) : ℝ)) * η := by
  have hsep := real_sample_error hN hQ (symRow m g G H A B) (fun u v => bitC (G u v)) (fun τ u v => bitC (H τ u v))
    (fun τ ℓ => symCoeff m g (symShift m τ) ℓ) (fun ℓ u => symLeft m (fun j => A j u) ℓ)
    (fun ℓ v => symRight m (fun j => B j v) ℓ) (fun ℓ u => (norm_symLeft m _ ℓ).le)
    (fun ℓ v => (norm_symRight m _ ℓ).le) S η hη ?_
  · refine hsep.trans (mul_le_mul_of_nonneg_right ?_ hη0)
    calc ∑ τ : SymState m, ∑ ℓ, ‖symCoeff m g (symShift m τ) ℓ‖ ≤ ∑ _τ : SymState m, ∏ j, (symModulus (m j) : ℝ) :=
          Finset.sum_le_sum fun τ _ => symCoeff_mass_le m g _
      _ = _ := by
          rw [Finset.sum_const, Finset.card_univ, card_symState, nsmul_eq_mul, Nat.cast_prod]
  · intro u v
    simp only [symRow, separableRow]
    push_cast
    rw [bitR_cast]
    congr 1
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [bitR_cast]
    congr 1
    have hlook := symLookup_eq_separable m g (fun j => A j u) (fun j => B j v) (symShift m τ) (fun j => by
      have h1 := (τ j).1.isLt
      have h2 := (τ j).2.isLt
      have hA' := hA j u
      have hB' := hB j v
      simp only [symShift]
      constructor <;> omega)
    rw [← hlook]
    simp only [symLookup]
    exact Finset.prod_congr rfl fun j _ => bitR_cast _

end Sym

section Thr
variable {N Q : ℕ} {Gq Pr : Type} [Fintype Gq] [Fintype Pr] (prime : Pr → ℕ) [∀ pr, NeZero (prime pr)]

noncomputable def thrRow (H : Gq → (pr : Pr) → ZMod (prime pr) → Fin N → Fin N → Bool) (A B : Gq → Pr → Fin N → ℤ)
    (g : Gq) (pr : Pr) (u v : Fin N) : ℝ :=
  ∑ s : ZMod (prime pr), bitR (H g pr s u v) * bitR (thrReported (A g pr u) (B g pr v) s)

noncomputable def thrObservable (G : Fin N → Fin N → Bool) (H : Gq → (pr : Pr) → ZMod (prime pr) → Fin N → Fin N → Bool)
    (A B : Gq → Pr → Fin N → ℤ) (u v : Fin N) : ℝ :=
  ∑ gp : Gq × Pr, (1 / (Fintype.card Pr : ℝ)) * (bitR (G u v) * thrRow prime H A B gp.1 gp.2 u v)

/-- The THR state matrices `D_{(g,p),s} = G·H_{g,p,s}` (row:matrix). -/
noncomputable def thrStateMatrix (G : Fin N → Fin N → Bool)
    (H : Gq → (pr : Pr) → ZMod (prime pr) → Fin N → Fin N → Bool) (g : Gq) (pr : Pr) (s : ZMod (prime pr)) :
    Fin N → Fin N → ℂ :=
  stateMatrix (fun u v => bitC (G u v)) (fun s u v => bitC (H g pr s u v)) s

omit [Fintype Gq] [Fintype Pr] in

theorem thrRow_sample_error (hN : 0 < N) (hQ : 0 < Q) (G : Fin N → Fin N → Bool)
    (H : Gq → (pr : Pr) → ZMod (prime pr) → Fin N → Fin N → Bool) (A B : Gq → Pr → Fin N → ℤ) (g : Gq) (pr : Pr)
    (S : Fin Q → Fin N × Fin N) (η : ℝ)
    (hη : ∀ s, ‖sampleError (thrStateMatrix prime G H g pr s) S‖ / (Q * N) ≤ η) :
    |liveMean (fun u v => bitR (G u v) * thrRow prime H A B g pr u v) -
        sampleMean S (fun u v => bitR (G u v) * thrRow prime H A B g pr u v)| ≤ prime pr * η := by
  have hsep := real_sample_error hN hQ (fun u v => bitR (G u v) * thrRow prime H A B g pr u v)
    (fun u v => bitC (G u v)) (fun s u v => bitC (H g pr s u v))
    (fun (s ℓ : ZMod (prime pr)) => ((prime pr : ℂ)⁻¹ * chi (ℓ * s)))
    (fun ℓ u => chi (ℓ * (A g pr u : ZMod (prime pr)))) (fun ℓ v => chi (ℓ * (B g pr v : ZMod (prime pr))))
    (fun ℓ u => (norm_chi _).le) (fun ℓ v => (norm_chi _).le) S η hη ?_
  · refine hsep.trans (le_of_eq ?_)
    simp only [thrCoeff_mass, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one]
  · intro u v
    simp only [thrRow, separableRow]
    push_cast
    rw [bitR_cast]
    congr 1
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [bitR_cast, bitR_cast, thrReported_separable]

theorem thr_sampler_interface (hN : 0 < N) (hQ : 0 < Q) (G : Fin N → Fin N → Bool)
    (H : Gq → (pr : Pr) → ZMod (prime pr) → Fin N → Fin N → Bool) (A B : Gq → Pr → Fin N → ℤ)
    (S : Fin Q → Fin N × Fin N) (η pmax : ℝ) (hη0 : 0 ≤ η) (hpmax0 : 0 ≤ pmax) (hpmax : ∀ pr, (prime pr : ℝ) ≤ pmax)
    (hη : ∀ g pr s, ‖sampleError (thrStateMatrix prime G H g pr s) S‖ / (Q * N) ≤ η) :
    |liveMean (thrObservable prime G H A B) - sampleMean S (thrObservable prime G H A B)| ≤
      Fintype.card Gq * pmax * η := by
  have hL := liveMean_sum (fun _ : Gq × Pr => 1 / (Fintype.card Pr : ℝ))
    (fun gp u v => bitR (G u v) * thrRow prime H A B gp.1 gp.2 u v)
  have hS := sampleMean_sum S (fun _ : Gq × Pr => 1 / (Fintype.card Pr : ℝ))
    (fun gp u v => bitR (G u v) * thrRow prime H A B gp.1 gp.2 u v)
  have hL' : liveMean (thrObservable prime G H A B) = _ := hL
  have hS' : sampleMean S (thrObservable prime G H A B) = _ := hS
  rw [hL', hS', ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hPr0 : (0 : ℝ) ≤ 1 / (Fintype.card Pr : ℝ) := by positivity
  calc ∑ gp : Gq × Pr, |1 / (Fintype.card Pr : ℝ) *
          liveMean (fun u v => bitR (G u v) * thrRow prime H A B gp.1 gp.2 u v) -
        1 / (Fintype.card Pr : ℝ) * sampleMean S (fun u v => bitR (G u v) * thrRow prime H A B gp.1 gp.2 u v)|
      ≤ ∑ gp : Gq × Pr, 1 / (Fintype.card Pr : ℝ) * (pmax * η) := by
        refine Finset.sum_le_sum fun gp _ => ?_
        rw [← mul_sub, abs_mul, abs_of_nonneg hPr0]
        refine mul_le_mul_of_nonneg_left ?_ hPr0
        exact (thrRow_sample_error prime hN hQ G H A B gp.1 gp.2 S η (hη gp.1 gp.2)).trans
          (mul_le_mul_of_nonneg_right (hpmax gp.2) hη0)
    _ = Fintype.card Gq * (Fintype.card Pr * (1 / (Fintype.card Pr : ℝ))) * (pmax * η) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, nsmul_eq_mul]
        push_cast
        ring
    _ ≤ Fintype.card Gq * 1 * (pmax * η) := by
        have hle : (Fintype.card Pr : ℝ) * (1 / (Fintype.card Pr : ℝ)) ≤ 1 := by
          rcases eq_or_ne (Fintype.card Pr : ℝ) 0 with h | h
          · rw [h, zero_mul]; exact zero_le_one
          · rw [mul_one_div_cancel h]
        have hpe : 0 ≤ pmax * η := mul_nonneg hpmax0 hη0
        gcongr
    _ = Fintype.card Gq * pmax * η := by ring

end Thr

theorem averaged_sample_error {Zc Es : Type} [Fintype Zc] [Fintype Es] [Nonempty Es] (live samp : Zc → Es → ℝ)
    (Mf : ℝ) (ηz : Zc → ℝ) (η : ℝ) (hM : 0 ≤ Mf) (hpt : ∀ z e, |live z e - samp z e| ≤ Mf * ηz z)
    (hη : uMean ηz ≤ η) :
    |uMean (fun z => uMean (fun e => live z e)) - uMean (fun z => uMean (fun e => samp z e))| ≤ Mf * η := by
  rw [← uMean_sub']
  refine (abs_uMean_le _).trans ?_
  calc uMean (fun z => |uMean (fun e => live z e) - uMean (fun e => samp z e)|)
      ≤ uMean (fun z => Mf * ηz z) := by
        refine uMean_mono fun z => ?_
        rw [← uMean_sub']
        refine (abs_uMean_le _).trans (uMean_le_const _ _ ?_ fun e => hpt z e)
        exact (abs_nonneg _).trans (hpt z (Classical.arbitrary Es))
    _ = Mf * uMean ηz := uMean_const_mul Mf ηz
    _ ≤ Mf * η := mul_le_mul_of_nonneg_left hη hM

end NearCubicWires.WireExponent3_5.Rows
