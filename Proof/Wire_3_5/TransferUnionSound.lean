import Proof.Wire_3_5.TransferUnion

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer
open Filter Topology
open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.RepairSource NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.Shared (uMean bitR)
open NearCubicWires.ComponentwiseBranchExtraction (systematicConstraint)

/-- `tr:soundness` with real estimates (the machine's estimates are exact rationals; their real values are what the
accuracy bounds speak about): estimates within `ε₀` of the tests of any guess and any masks cannot pass
`tr:thresholds` on a PCPP that is pointwise sound and whose circuit the outer verifier accepts on at most `η` of the
random inputs. -/
theorem masked_soundness_real {q : ℕ} {H : BooleanCircuit q} (pcpp : PointwisePCPP H) {cp sp : ℝ}
    (params : MaskedSoundnessParameters cp sp) {Seed : Type} [Fintype Seed] [Nonempty Seed]
    (hsound : ∀ x, ¬ H.eval x → ∀ aux, pcpp.satisfiedFraction x aux ≤ sp)
    (houter : uMean (fun x : BitInput q => bitR (H.eval x)) ≤ params.outerError)
    (S : PcppVar pcpp → BitInput q → ℝ) (G : PcppVar pcpp → Seed → BitInput q → Bool) (Vh Qh μh : ℝ)
    (hV : |Vh - testV pcpp S G| ≤ params.eps0) (hQ : |Qh - testQ pcpp S G| ≤ params.eps0)
    (hμ : |μh - testMu pcpp S G| ≤ params.eps0) (hVp : Vh ≤ 2 * (params.v0 : ℝ)) (hQp : Qh ≤ 1 + (params.v0 : ℝ))
    (hμp : (params.threshold : ℝ) ≤ μh) : False := by
  have hv0 : (0 : ℝ) < params.v0 := by exact_mod_cast params.v0_pos
  have hv24 : (params.v0 : ℝ) ≤ 1 / 24 :=
    calc (params.v0 : ℝ) ≤ ((1 / 24 : ℚ) : ℝ) := Rat.cast_le.mpr params.v0_le
      _ = 1 / 24 := by norm_num
  have hεv : (params.eps0 : ℝ) ≤ params.v0 := by exact_mod_cast params.eps0_le_v0
  have hV' : testV pcpp S G ≤ 3 * (params.v0 : ℝ) := by linarith [(abs_le.mp hV).1]
  have hQ' : testQ pcpp S G ≤ 1 + 2 * (params.v0 : ℝ) := by linarith [(abs_le.mp hQ).1]
  have h1 := testMu_le_rounded pcpp S G params.v0 hv0 hv24 hV' hQ'
  have h2 := maskedRoundedScore_le pcpp S G
  have h3 := roundedScore_le_soundness pcpp params.sp_nonneg hsound S
  have h4 := (abs_le.mp hμ).2
  have hmid := params.thresholdAboveMidpoint
  have hres := params.roundingReserve
  have hout := params.outerReserve
  linarith

section Union
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B}

namespace UnionGuess
variable {S : UnionSetup I} {N : ℕ} {z : BitInput N} (g : UnionGuess S z)

/-- The atoms' functions. -/
abbrev atoms : g.AtomIx → BitInput g.q → Bool := fun a x => g.mode.eval (g.circ a) x

theorem linForm_wOne (x : BitInput g.q) : linForm g.atoms g.wOne x = 1 := by
  unfold linForm
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  have h1 : ∑ u : Unit, g.wOne (Sum.inl u) * bitR (g.atoms (Sum.inl u) x) = 1 := by
    rw [Fintype.sum_unique]
    show 1 * bitR (g.mode.eval (S.constAtom g.mode g.q) x) = 1
    rw [S.constAtom_eval]; simp [bitR]
  have h2 : ∑ p : PcppVar g.pcpp × Fin g.s, g.wOne (Sum.inr (Sum.inl p)) * bitR (g.atoms (Sum.inr (Sum.inl p)) x) =
      0 := Finset.sum_eq_zero fun p _ => by simp [wOne]
  have h3 : ∑ Y : PcppVar g.pcpp, g.wOne (Sum.inr (Sum.inr Y)) * bitR (g.atoms (Sum.inr (Sum.inr Y)) x) = 0 :=
    Finset.sum_eq_zero fun Y _ => by simp [wOne]
  rw [h1, h2, h3]; ring

theorem linForm_wE (X : PcppVar g.pcpp) (x : BitInput g.q) :
    linForm g.atoms (g.wE X) x = bitR (parityOn (g.support X) x) := by
  unfold linForm
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  have h1 : ∑ u : Unit, g.wE X (Sum.inl u) * bitR (g.atoms (Sum.inl u) x) = 0 :=
    Finset.sum_eq_zero fun u _ => by simp [wE]
  have h2 : ∑ p : PcppVar g.pcpp × Fin g.s, g.wE X (Sum.inr (Sum.inl p)) * bitR (g.atoms (Sum.inr (Sum.inl p)) x) =
      0 := Finset.sum_eq_zero fun p _ => by simp [wE]
  have h3 : ∑ Y : PcppVar g.pcpp, g.wE X (Sum.inr (Sum.inr Y)) * bitR (g.atoms (Sum.inr (Sum.inr Y)) x) =
      bitR (g.atoms (Sum.inr (Sum.inr X)) x) := by
    rw [Finset.sum_eq_single X]
    · simp [wE]
    · intro Y _ hY; simp [wE, hY]
    · simp
  rw [h1, h2, h3, zero_add, zero_add]
  show bitR (g.mode.eval (S.parityAtom g.mode g.q (g.support X)) x) = _
  rw [S.parityAtom_eval]

theorem constraint_eq (X : PcppVar g.pcpp) (x : BitInput g.q) :
    systematicConstraint g.pcpp x X = if g.sysBit X then some (parityOn (g.support X) x) else none := by
  refine Fin.addCases (fun i => ?_) (fun j => ?_) X
  · simp [systematicConstraint, sysBit, support, i.isLt]
  · simp [systematicConstraint, sysBit]

theorem linMass_wS (hsign : ∀ X a, g.sign X a ∈ ({-1, 0, 1} : Finset ℤ)) (X : PcppVar g.pcpp) :
    linMass (g.wS X) ≤ S.gridMass g.q := by
  have hL : (0 : ℝ) ≤ (S.gridMass g.q : ℝ) := by exact_mod_cast S.gridMass_nonneg _
  have hc : (0 : ℝ) ≤ (S.gridMass g.q : ℝ) / g.s := div_nonneg hL (Nat.cast_nonneg _)
  have hsum : linMass (g.wS X) = ∑ a : Fin g.s, |(S.gridMass g.q : ℝ) / g.s * (g.sign X a : ℝ)| := by
    unfold linMass
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_prod_type]
    have h1 : ∑ u : Unit, |g.wS X (Sum.inl u)| = 0 := Finset.sum_eq_zero fun u _ => by simp [wS]
    have h3 : ∑ Y : PcppVar g.pcpp, |g.wS X (Sum.inr (Sum.inr Y))| = 0 :=
      Finset.sum_eq_zero fun Y _ => by simp [wS]
    have h2 : ∑ Y : PcppVar g.pcpp, ∑ a : Fin g.s, |g.wS X (Sum.inr (Sum.inl (Y, a)))| =
        ∑ a : Fin g.s, |(S.gridMass g.q : ℝ) / g.s * (g.sign X a : ℝ)| := by
      rw [Finset.sum_eq_single X]
      · exact Finset.sum_congr rfl fun a _ => by simp [wS]
      · intro Y _ hY; exact Finset.sum_eq_zero fun a _ => by simp [wS, hY]
      · simp
    rw [h1, h2, h3, zero_add, add_zero]
  have habs : ∀ a, |(S.gridMass g.q : ℝ) / g.s * (g.sign X a : ℝ)| ≤ (S.gridMass g.q : ℝ) / g.s := by
    intro a
    rw [abs_mul, abs_of_nonneg hc]
    have h := hsign X a
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    have : |(g.sign X a : ℝ)| ≤ 1 := by rcases h with h | h | h <;> simp [h]
    exact mul_le_of_le_one_right hc this
  rw [hsum]
  calc ∑ a : Fin g.s, |(S.gridMass g.q : ℝ) / g.s * (g.sign X a : ℝ)| ≤ ∑ _a : Fin g.s, (S.gridMass g.q : ℝ) / g.s :=
        Finset.sum_le_sum fun a _ => habs a
    _ ≤ (S.gridMass g.q : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rcases Nat.eq_zero_or_pos g.s with h0 | hpos
        · rw [h0]; simpa using hL
        · rw [mul_div_cancel₀ _ (by exact_mod_cast hpos.ne')]

theorem linMass_wOne : linMass g.wOne ≤ 1 := by
  unfold linMass
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp [wOne]

theorem linMass_wE (X : PcppVar g.pcpp) : linMass (g.wE X) ≤ 1 := by
  unfold linMass
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  have h1 : ∑ u : Unit, |g.wE X (Sum.inl u)| = 0 := Finset.sum_eq_zero fun u _ => by simp [wE]
  have h2 : ∑ p : PcppVar g.pcpp × Fin g.s, |g.wE X (Sum.inr (Sum.inl p))| = 0 :=
    Finset.sum_eq_zero fun p _ => by simp [wE]
  have h3 : ∑ Y : PcppVar g.pcpp, |g.wE X (Sum.inr (Sum.inr Y))| = 1 := by
    rw [Finset.sum_eq_single X]
    · simp [wE]
    · intro Y _ hY; simp [wE, hY]
    · simp
  rw [h1, h2, h3]; norm_num

noncomputable def forms (hsign : ∀ X a, g.sign X a ∈ ({-1, 0, 1} : Finset ℤ)) :
    AtomForms g.pcpp g.atoms (S.gridMass g.q) where
  wS := g.wS
  wOne := g.wOne
  wE := g.wE
  sys := g.sysBit
  parity := fun X x => parityOn (g.support X) x
  one_eq := g.linForm_wOne
  E_eq := g.linForm_wE
  constraint_eq := g.constraint_eq
  S_mass := g.linMass_wS hsign
  one_mass := g.linMass_wOne
  E_mass := g.linMass_wE

theorem not_unionAccepts (P : FusedPrimitive I) (hN : 1 ≤ N) (hno : S.machine.accepts N z = false)
    (hout : 1 / (N : ℝ) ^ 10 ≤ (S.params.outerError : ℝ))
    (hD : (1 + (S.gridMass g.q : ℝ)) ^ 4 * (g.q : ℝ) ^ (-(I.D : ℝ)) ≤ (S.params.eps0 : ℝ)) :
    ¬ UnionAccepts S P z g := by
  rintro ⟨-, hsign, -, hVcall, hQcall, hμcall, hVp, hQp, hμp⟩
  have hL : (0 : ℝ) ≤ (S.gridMass g.q : ℝ) := by exact_mod_cast S.gridMass_nonneg _
  have hVacc := seed_propagated_V I P hL (g.forms hsign) g.carrier g.translation hVcall
  have hQacc := seed_propagated_Q I P hL (g.forms hsign) g.carrier g.translation hQcall
  have hμacc := seed_propagated_Mu I P hL (g.forms hsign) g.carrier g.translation hμcall
  have hsound : ∀ x, ¬ (S.request z g.oracle).circuit.eval x → ∀ aux,
      g.pcpp.satisfiedFraction x aux ≤ S.pcppAlg.soundness := by
    intro x hx aux
    exact S.pcppAlg.sound (S.request z g.oracle) x (by simpa using hx) aux
  have houter : uMean (fun x : BitInput g.q => bitR ((S.request z g.oracle).circuit.eval x)) ≤
      (S.params.outerError : ℝ) :=
    (S.outerSound N hN z hno g.oracle).trans hout
  exact masked_soundness_real g.pcpp S.params hsound houter (g.forms hsign).guess
    (carrierFilter I g.mode g.pcpp g.carrier g.translation) (g.Vhat P) (g.Qhat P) (g.μhat P)
    (hVacc.trans hD) (hQacc.trans hD) (hμacc.trans hD) hVp hQp hμp

end UnionGuess

/-- The PCPP arity is at least the native width. -/
theorem nativeWidth_le_q (S : UnionSetup I) {N : ℕ} {z : BitInput N} (g : UnionGuess S z) :
    S.pcp.nativeWidth N ≤ g.q :=
  le_max_left _ _

theorem oneSided_of_soundFor (S : UnionSetup I) (P : FusedPrimitive I) (M : OrdinaryWeakMachine)
    (hS : SoundFor S P M) (hη : 0 < (S.params.outerError : ℝ))
    (hw : Tendsto (fun N => S.pcp.nativeWidth N) atTop atTop)
    (hD : ∀ᶠ q : ℕ in atTop, (1 + (S.gridMass q : ℝ)) ^ 4 * (q : ℝ) ^ (-(I.D : ℝ)) ≤ (S.params.eps0 : ℝ)) :
    OneSided M S.language := by
  have h1 : ∀ᶠ N : ℕ in atTop, 1 ≤ N ∧ 1 / (N : ℝ) ^ 10 ≤ (S.params.outerError : ℝ) := by
    have ht : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) := tendsto_one_div_atTop_nhds_zero_nat
    filter_upwards [ht.eventually_le_const hη, eventually_ge_atTop 1] with N hN hN1
    refine ⟨hN1, ?_⟩
    have hN1' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
    have : 1 / (N : ℝ) ^ 10 ≤ 1 / (N : ℝ) := by
      apply one_div_le_one_div_of_le (by positivity)
      calc (N : ℝ) = (N : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ (N : ℝ) ^ 10 := pow_le_pow_right₀ hN1' (by norm_num)
    exact this.trans hN
  obtain ⟨Q₀, hQ⟩ := eventually_atTop.mp hD
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp (h1.and (hw.eventually_ge_atTop Q₀))
  refine ⟨n₀, fun n hn x hacc => ?_⟩
  obtain ⟨g, hg⟩ := hS n x hacc
  by_contra hL
  have hno : S.machine.accepts n x = false := by
    rw [← S.decides]; simpa using hL
  exact g.not_unionAccepts P (hn₀ n hn).1.1 hno (hn₀ n hn).1.2 (hQ _ ((hn₀ n hn).2.trans (nativeWidth_le_q S g))) hg

end Union

end NearCubicWires.WireExponent3_5.Transfer
