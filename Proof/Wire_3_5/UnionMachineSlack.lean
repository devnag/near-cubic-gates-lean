import Proof.Wire_3_5.UnionMachineWeak

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine
open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairSource
open NearCubicWires.WireExponent3_5.Transfer NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.WireExponent3_5.Shared (uMean bitR)
open NearCubicWires.RecoveryScheduleEnvelope (oracleSizeBound)
open Filter Topology

/-! ## Rounding -/

/-- **The rounded answer** `⌊2^p v⌋/2^p`. -/
def roundQ (p : ℕ) (v : ℚ) : ℚ := (⌊v * 2 ^ p⌋ : ℚ) / 2 ^ p

theorem roundQ_close_rat (p : ℕ) (v : ℚ) : |roundQ p v - v| ≤ 1 / 2 ^ p := by
  have hp : (0 : ℚ) < 2 ^ p := by positivity
  have h1 : (⌊v * 2 ^ p⌋ : ℚ) ≤ v * 2 ^ p := Int.floor_le _
  have h2 : v * 2 ^ p < (⌊v * 2 ^ p⌋ : ℚ) + 1 := Int.lt_floor_add_one _
  have e : roundQ p v - v = ((⌊v * 2 ^ p⌋ : ℚ) - v * 2 ^ p) / 2 ^ p := by
    rw [sub_div, mul_div_cancel_right₀ _ hp.ne']; rfl
  rw [e, abs_div, abs_of_pos hp]
  apply div_le_div_of_nonneg_right _ hp.le
  rw [abs_le]; constructor <;> linarith

theorem roundQ_close (p : ℕ) (v : ℚ) : |(roundQ p v : ℝ) - v| ≤ 1 / 2 ^ p := by
  have h : ((|roundQ p v - v| : ℚ) : ℝ) ≤ ((1 / 2 ^ p : ℚ) : ℝ) := Rat.cast_le.mpr (roundQ_close_rat p v)
  push_cast at h
  exact h

/-- **The slack** of the rounding at grid mass `Λ̄`: `(1+Λ̄)⁴·2^{−p}`. -/
def slackOf (mass : ℚ) (p : ℕ) : ℚ := (1 + mass) ^ 4 / 2 ^ p

theorem slackOf_cast (mass : ℚ) (p : ℕ) : (slackOf mass p : ℝ) = (1 + (mass : ℝ)) ^ 4 * (1 / 2 ^ p) := by
  unfold slackOf; push_cast; ring

/-- **The slack check** of a parsed guess: T's `check` with the thresholds relaxed by `δ`. -/
def slackCheck (D : UnionCheckData) (val : PrimRequest → ℚ) (v0 τ δ : ℚ) (callOk : PrimRequest → Bool) : Bool :=
  D.signsOk && D.schedule.all callOk && decide (D.VhatQ val ≤ 2 * v0 + δ) && decide (D.QhatQ val ≤ 1 + v0 + δ) &&
    decide (τ - δ ≤ D.μhatQ val)

/-- At zero slack the slack check is T's exact check. -/
theorem slackCheck_zero (D : UnionCheckData) (val : PrimRequest → ℚ) (v0 τ : ℚ) (callOk : PrimRequest → Bool) :
    slackCheck D val v0 τ 0 callOk = D.check val v0 τ callOk := by
  simp only [slackCheck, UnionCheckData.check, add_zero, sub_zero]

section Slack
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B}

namespace UnionGuessSlack
variable {S : UnionSetup I} {N : ℕ} {z : BitInput N} (g : UnionGuess S z)

/-! ## The estimates at any answers -/

/-- `V̂` at the answers `val`. -/
noncomputable def VhatV (val : PrimRequest → ℚ) : ℝ :=
  uMean fun pos : Fin (2 ^ g.pcpp.clauseBits) × Fin 2 => (g.polyVAt pos).estimate (fun _ t => (val (g.vCall pos t) : ℝ))

/-- `Q̂` at the answers `val`. -/
noncomputable def QhatV (val : PrimRequest → ℚ) : ℝ :=
  uMean fun pos : Fin (2 ^ g.pcpp.clauseBits) × Fin 2 => (g.polyQAt pos).estimate (fun _ t => (val (g.vCall pos t) : ℝ))

/-- `μ̂` at the answers `val`. -/
noncomputable def μhatV (val : PrimRequest → ℚ) : ℝ :=
  uMean fun i : Fin (2 ^ g.pcpp.clauseBits) => (g.polyMuAt i).estimate (fun _ t => (val (g.muCall i t) : ℝ))

theorem VhatV_eq (val : PrimRequest → ℚ) : VhatV g val = ((g.checkData g.translation).VhatQ val : ℝ) := by
  have hc : ((Fintype.card (Fin (2 ^ g.pcpp.clauseBits) × Fin 2) : ℕ) : ℝ) =
      (2 : ℝ) ^ (g.checkData g.translation).pcpp.clauseBits * 2 := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]; push_cast; rfl
  unfold VhatV uMean Poly4.estimate
  rw [UnionCheckData.VhatQ, UnionCheckData.combine_termsV, hc]
  push_cast
  rw [div_left_inj' (by positivity)]
  refine Finset.sum_congr rfl fun pos _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun t _ => ?_
  rw [g.coeffV_eq g.translation pos j t, g.checkData_vCall pos t]

theorem QhatV_eq (val : PrimRequest → ℚ) : QhatV g val = ((g.checkData g.translation).QhatQ val : ℝ) := by
  have hc : ((Fintype.card (Fin (2 ^ g.pcpp.clauseBits) × Fin 2) : ℕ) : ℝ) =
      (2 : ℝ) ^ (g.checkData g.translation).pcpp.clauseBits * 2 := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]; push_cast; rfl
  unfold QhatV uMean Poly4.estimate
  rw [UnionCheckData.QhatQ, UnionCheckData.combine_termsQ, hc]
  push_cast
  rw [div_left_inj' (by positivity)]
  refine Finset.sum_congr rfl fun pos _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun t _ => ?_
  rw [g.coeffQ_eq g.translation pos j t, g.checkData_vCall pos t]

theorem μhatV_eq (val : PrimRequest → ℚ) : μhatV g val = ((g.checkData g.translation).μhatQ val : ℝ) := by
  have hc : ((Fintype.card (Fin (2 ^ g.pcpp.clauseBits)) : ℕ) : ℝ) =
      (2 : ℝ) ^ (g.checkData g.translation).pcpp.clauseBits := by
    rw [Fintype.card_fin]; push_cast; rfl
  unfold μhatV uMean Poly4.estimate
  rw [UnionCheckData.μhatQ, UnionCheckData.combine_termsMu, hc]
  push_cast
  rw [div_left_inj' (by positivity)]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun t _ => ?_
  rw [g.coeffMu_eq g.translation i j t, g.checkData_muCall i t]

/-- The exact estimates are the estimates at the primitive's values. -/
theorem VhatV_value (P : FusedPrimitive I) : VhatV g P.value = g.Vhat P := rfl
theorem QhatV_value (P : FusedPrimitive I) : QhatV g P.value = g.Qhat P := rfl
theorem μhatV_value (P : FusedPrimitive I) : μhatV g P.value = g.μhat P := rfl

/-! ## Close answers give close estimates -/

theorem VhatV_sub (hsign : ∀ X a, g.sign X a ∈ ({-1, 0, 1} : Finset ℤ)) (val val' : PrimRequest → ℚ) (η : ℝ)
    (hη0 : 0 ≤ η) (hη : ∀ r, |(val r : ℝ) - val' r| ≤ η) :
    |VhatV g val - VhatV g val'| ≤ (1 + (S.gridMass g.q : ℝ)) ^ 4 * η := by
  have hL : (0 : ℝ) ≤ (S.gridMass g.q : ℝ) := by exact_mod_cast S.gridMass_nonneg _
  unfold VhatV
  refine (abs_uMean_sub_le _ _).trans (uMean_le_const' _ _ (by positivity) fun pos => ?_)
  have h : |(g.polyVAt pos).estimate (fun _ t => (val (g.vCall pos t) : ℝ)) -
      (g.polyVAt pos).estimate (fun _ t => (val' (g.vCall pos t) : ℝ))| ≤ (g.polyVAt pos).mass * η :=
    Poly4.estimate_error _ _ _ η (fun j t _ => hη _)
  have hm : (g.polyVAt pos).mass ≤ (1 + (S.gridMass g.q : ℝ)) ^ 4 :=
    polyV_mass_le (g.sysBit (posVar g.pcpp pos.1 pos.2)) (g.wS (posVar g.pcpp pos.1 pos.2)) g.wOne
      (g.wE (posVar g.pcpp pos.1 pos.2)) _ hL (g.linMass_wS hsign _) g.linMass_wOne (g.linMass_wE _)
  exact h.trans (mul_le_mul_of_nonneg_right hm hη0)

theorem QhatV_sub (hsign : ∀ X a, g.sign X a ∈ ({-1, 0, 1} : Finset ℤ)) (val val' : PrimRequest → ℚ) (η : ℝ)
    (hη0 : 0 ≤ η) (hη : ∀ r, |(val r : ℝ) - val' r| ≤ η) :
    |QhatV g val - QhatV g val'| ≤ (1 + (S.gridMass g.q : ℝ)) ^ 4 * η := by
  have hL : (0 : ℝ) ≤ (S.gridMass g.q : ℝ) := by exact_mod_cast S.gridMass_nonneg _
  unfold QhatV
  refine (abs_uMean_sub_le _ _).trans (uMean_le_const' _ _ (by positivity) fun pos => ?_)
  have h : |(g.polyQAt pos).estimate (fun _ t => (val (g.vCall pos t) : ℝ)) -
      (g.polyQAt pos).estimate (fun _ t => (val' (g.vCall pos t) : ℝ))| ≤ (g.polyQAt pos).mass * η :=
    Poly4.estimate_error _ _ _ η (fun j t _ => hη _)
  have hm : (g.polyQAt pos).mass ≤ (1 + (S.gridMass g.q : ℝ)) ^ 4 :=
    polyQ_mass_le (g.wS (posVar g.pcpp pos.1 pos.2)) g.wOne _ hL (g.linMass_wS hsign _) g.linMass_wOne
  exact h.trans (mul_le_mul_of_nonneg_right hm hη0)

theorem μhatV_sub (hsign : ∀ X a, g.sign X a ∈ ({-1, 0, 1} : Finset ℤ)) (val val' : PrimRequest → ℚ) (η : ℝ)
    (hη0 : 0 ≤ η) (hη : ∀ r, |(val r : ℝ) - val' r| ≤ η) :
    |μhatV g val - μhatV g val'| ≤ (1 + (S.gridMass g.q : ℝ)) ^ 4 * η := by
  have hL : (0 : ℝ) ≤ (S.gridMass g.q : ℝ) := by exact_mod_cast S.gridMass_nonneg _
  unfold μhatV
  refine (abs_uMean_sub_le _ _).trans (uMean_le_const' _ _ (by positivity) fun i => ?_)
  have h : |(g.polyMuAt i).estimate (fun _ t => (val (g.muCall i t) : ℝ)) -
      (g.polyMuAt i).estimate (fun _ t => (val' (g.muCall i t) : ℝ))| ≤ (g.polyMuAt i).mass * η :=
    Poly4.estimate_error _ _ _ η (fun j t _ => hη _)
  have hm : (g.polyMuAt i).mass ≤ (1 + (S.gridMass g.q : ℝ)) ^ 4 :=
    polyMu_mass_le (posNeg g.pcpp i 0) (posNeg g.pcpp i 1) (g.wS (posVar g.pcpp i 0))
      (g.wS (posVar g.pcpp i 1)) g.wOne _ hL (g.linMass_wS hsign _) (g.linMass_wS hsign _) g.linMass_wOne
  exact h.trans (mul_le_mul_of_nonneg_right hm hη0)

/-! ## The calls' errors -/

theorem vCall_error (P : FusedPrimitive I) (pos : Fin (2 ^ g.pcpp.clauseBits) × Fin 2) (t : Fin 4 → g.AtomIx)
    (h : I.Call (g.vCall pos t)) :
    |(P.value (g.vCall pos t) : ℝ) - tupleTruth g.atoms
      (carrierFilter I g.mode g.pcpp g.carrier g.translation (posVar g.pcpp pos.1 pos.2)) t| ≤
      (g.q : ℝ) ^ (-(I.D : ℝ)) := by
  have h1 : |(P.value (g.vCall pos t) : ℝ) - I.truth (g.vCall pos t)| ≤ (g.q : ℝ) ^ (-(I.D : ℝ)) := P.error _ h
  have e : I.truth (g.vCall pos t) = tupleTruth g.atoms
      (carrierFilter I g.mode g.pcpp g.carrier g.translation (posVar g.pcpp pos.1 pos.2)) t :=
    tupleTruth_single I g.mode g.pcpp g.carrier g.translation g.circ _ t
  rw [e] at h1
  exact h1

theorem muCall_error (P : FusedPrimitive I) (i : Fin (2 ^ g.pcpp.clauseBits)) (t : Fin 4 → g.AtomIx)
    (h : I.Call (g.muCall i t)) :
    |(P.value (g.muCall i t) : ℝ) - tupleTruth g.atoms
      (clauseMask g.pcpp (carrierFilter I g.mode g.pcpp g.carrier g.translation) i) t| ≤
      (g.q : ℝ) ^ (-(I.D : ℝ)) := by
  have h1 : |(P.value (g.muCall i t) : ℝ) - I.truth (g.muCall i t)| ≤ (g.q : ℝ) ^ (-(I.D : ℝ)) := P.error _ h
  have e : I.truth (g.muCall i t) = tupleTruth g.atoms
      (clauseMask g.pcpp (carrierFilter I g.mode g.pcpp g.carrier g.translation) i) t :=
    tupleTruth_pair I g.mode g.pcpp g.carrier g.translation g.circ i t
  rw [e] at h1
  exact h1

/-! ## The slack acceptance and its soundness -/

variable (P : FusedPrimitive I) (p : ℕ → ℕ)

/-- The machine's answers: the primitive's values rounded to `p(q)` bits. -/
def roundedVal (q : ℕ) : PrimRequest → ℚ := fun r => roundQ (p q) (P.value r)

theorem roundedVal_close (q : ℕ) (r : PrimRequest) : |((roundedVal P p q r : ℚ) : ℝ) - P.value r| ≤ 1 / 2 ^ p q :=
  roundQ_close _ _

/-- **Slack acceptance**: grid signs, admissible calls, and `tr:thresholds` relaxed by the slack at the rounded
answers. -/
def SlackAccepts : Prop :=
  (∀ X a, g.sign X a ∈ ({-1, 0, 1} : Finset ℤ)) ∧
  (∀ pos j t, (g.polyVAt pos).coeff j t ≠ 0 → I.Call (g.vCall pos t)) ∧
  (∀ pos j t, (g.polyQAt pos).coeff j t ≠ 0 → I.Call (g.vCall pos t)) ∧
  (∀ i j t, (g.polyMuAt i).coeff j t ≠ 0 → I.Call (g.muCall i t)) ∧
  VhatV g (roundedVal P p g.q) ≤ 2 * (S.params.v0 : ℝ) + (slackOf (S.gridMass g.q) (p g.q) : ℝ) ∧
  QhatV g (roundedVal P p g.q) ≤ 1 + (S.params.v0 : ℝ) + (slackOf (S.gridMass g.q) (p g.q) : ℝ) ∧
  (S.params.threshold : ℝ) - (slackOf (S.gridMass g.q) (p g.q) : ℝ) ≤ μhatV g (roundedVal P p g.q)

/-- **Exact acceptance passes the slack thresholds.** -/
theorem slack_of_accepts (hg : UnionAccepts S P z g) :
    VhatV g (roundedVal P p g.q) ≤ 2 * (S.params.v0 : ℝ) + (slackOf (S.gridMass g.q) (p g.q) : ℝ) ∧
    QhatV g (roundedVal P p g.q) ≤ 1 + (S.params.v0 : ℝ) + (slackOf (S.gridMass g.q) (p g.q) : ℝ) ∧
    (S.params.threshold : ℝ) - (slackOf (S.gridMass g.q) (p g.q) : ℝ) ≤ μhatV g (roundedVal P p g.q) := by
  obtain ⟨-, hsign, -, -, -, -, hV, hQ, hμ⟩ := hg
  have hη : ∀ r, |((roundedVal P p g.q r : ℚ) : ℝ) - P.value r| ≤ 1 / 2 ^ p g.q := roundedVal_close P p g.q
  have h1 := VhatV_sub g hsign (roundedVal P p g.q) P.value _ (by positivity) hη
  have h2 := QhatV_sub g hsign (roundedVal P p g.q) P.value _ (by positivity) hη
  have h3 := μhatV_sub g hsign (roundedVal P p g.q) P.value _ (by positivity) hη
  rw [VhatV_value] at h1
  rw [QhatV_value] at h2
  rw [μhatV_value] at h3
  rw [slackOf_cast]
  obtain ⟨-, h1⟩ := abs_le.mp h1
  obtain ⟨-, h2⟩ := abs_le.mp h2
  obtain ⟨h3, -⟩ := abs_le.mp h3
  refine ⟨?_, ?_, ?_⟩ <;> linarith

theorem vCall_round_error (pos : Fin (2 ^ g.pcpp.clauseBits) × Fin 2) (t : Fin 4 → g.AtomIx)
    (h : I.Call (g.vCall pos t)) :
    |((roundedVal P p g.q (g.vCall pos t) : ℚ) : ℝ) - tupleTruth g.atoms
      (carrierFilter I g.mode g.pcpp g.carrier g.translation (posVar g.pcpp pos.1 pos.2)) t| ≤
      (g.q : ℝ) ^ (-(I.D : ℝ)) + 1 / 2 ^ p g.q := by
  have h1 := vCall_error g P pos t h
  have h2 := roundedVal_close P p g.q (g.vCall pos t)
  have h3 := abs_sub_le ((roundedVal P p g.q (g.vCall pos t) : ℚ) : ℝ) (P.value (g.vCall pos t) : ℝ)
    (tupleTruth g.atoms (carrierFilter I g.mode g.pcpp g.carrier g.translation (posVar g.pcpp pos.1 pos.2)) t)
  linarith

theorem muCall_round_error (i : Fin (2 ^ g.pcpp.clauseBits)) (t : Fin 4 → g.AtomIx) (h : I.Call (g.muCall i t)) :
    |((roundedVal P p g.q (g.muCall i t) : ℚ) : ℝ) - tupleTruth g.atoms
      (clauseMask g.pcpp (carrierFilter I g.mode g.pcpp g.carrier g.translation) i) t| ≤
      (g.q : ℝ) ^ (-(I.D : ℝ)) + 1 / 2 ^ p g.q := by
  have h1 := muCall_error g P i t h
  have h2 := roundedVal_close P p g.q (g.muCall i t)
  have h3 := abs_sub_le ((roundedVal P p g.q (g.muCall i t) : ℚ) : ℝ) (P.value (g.muCall i t) : ℝ)
    (tupleTruth g.atoms (clauseMask g.pcpp (carrierFilter I g.mode g.pcpp g.carrier g.translation) i) t)
  linarith

/-- **No slack acceptance on a no-instance**: past the onsets where the outer error `N^{−10}` is at most `η` and the
propagated error of the rounded answers plus the slack is at most `ε₀`. -/
theorem not_slackAccepts (hN : 1 ≤ N) (hno : S.machine.accepts N z = false)
    (hout : 1 / (N : ℝ) ^ 10 ≤ (S.params.outerError : ℝ))
    (hD : (1 + (S.gridMass g.q : ℝ)) ^ 4 * ((g.q : ℝ) ^ (-(I.D : ℝ)) + 1 / 2 ^ p g.q) +
      (slackOf (S.gridMass g.q) (p g.q) : ℝ) ≤ (S.params.eps0 : ℝ)) :
    ¬ SlackAccepts g P p := by
  rintro ⟨hsign, hVcall, hQcall, hμcall, hVp, hQp, hμp⟩
  have hL : (0 : ℝ) ≤ (S.gridMass g.q : ℝ) := by exact_mod_cast S.gridMass_nonneg _
  have herr : (0 : ℝ) ≤ (g.q : ℝ) ^ (-(I.D : ℝ)) + 1 / 2 ^ p g.q := by positivity
  have hδ0 : (0 : ℝ) ≤ (slackOf (S.gridMass g.q) (p g.q) : ℝ) := by rw [slackOf_cast]; positivity
  have hV : |VhatV g (roundedVal P p g.q) - testV g.pcpp (g.forms hsign).guess
      (carrierFilter I g.mode g.pcpp g.carrier g.translation)| ≤
      (1 + (S.gridMass g.q : ℝ)) ^ 4 * ((g.q : ℝ) ^ (-(I.D : ℝ)) + 1 / 2 ^ p g.q) :=
    propagated_V hL (g.forms hsign) (carrierFilter I g.mode g.pcpp g.carrier g.translation)
      (fun pos _ t => ((roundedVal P p g.q (g.vCall pos t) : ℚ) : ℝ)) _ herr
      (fun pos j t hc => vCall_round_error g P p pos t (hVcall pos j t hc))
  have hQ : |QhatV g (roundedVal P p g.q) - testQ g.pcpp (g.forms hsign).guess
      (carrierFilter I g.mode g.pcpp g.carrier g.translation)| ≤
      (1 + (S.gridMass g.q : ℝ)) ^ 4 * ((g.q : ℝ) ^ (-(I.D : ℝ)) + 1 / 2 ^ p g.q) :=
    propagated_Q hL (g.forms hsign) (carrierFilter I g.mode g.pcpp g.carrier g.translation)
      (fun pos _ t => ((roundedVal P p g.q (g.vCall pos t) : ℚ) : ℝ)) _ herr
      (fun pos j t hc => vCall_round_error g P p pos t (hQcall pos j t hc))
  have hμ : |μhatV g (roundedVal P p g.q) - testMu g.pcpp (g.forms hsign).guess
      (carrierFilter I g.mode g.pcpp g.carrier g.translation)| ≤
      (1 + (S.gridMass g.q : ℝ)) ^ 4 * ((g.q : ℝ) ^ (-(I.D : ℝ)) + 1 / 2 ^ p g.q) :=
    propagated_Mu hL (g.forms hsign) (carrierFilter I g.mode g.pcpp g.carrier g.translation)
      (fun i _ t => ((roundedVal P p g.q (g.muCall i t) : ℚ) : ℝ)) _ herr
      (fun i j t hc => muCall_round_error g P p i t (hμcall i j t hc))
  have hsound : ∀ x, ¬ (S.request z g.oracle).circuit.eval x → ∀ aux,
      g.pcpp.satisfiedFraction x aux ≤ S.pcppAlg.soundness := by
    intro x hx aux
    exact S.pcppAlg.sound (S.request z g.oracle) x (by simpa using hx) aux
  have houter : uMean (fun x : BitInput g.q => bitR ((S.request z g.oracle).circuit.eval x)) ≤
      (S.params.outerError : ℝ) :=
    (S.outerSound N hN z hno g.oracle).trans hout
  obtain ⟨hV1, hV2⟩ := abs_le.mp hV
  obtain ⟨hQ1, hQ2⟩ := abs_le.mp hQ
  obtain ⟨hμ1, hμ2⟩ := abs_le.mp hμ
  exact masked_soundness_real g.pcpp S.params hsound houter (g.forms hsign).guess
    (carrierFilter I g.mode g.pcpp g.carrier g.translation)
    (VhatV g (roundedVal P p g.q) - (slackOf (S.gridMass g.q) (p g.q) : ℝ))
    (QhatV g (roundedVal P p g.q) - (slackOf (S.gridMass g.q) (p g.q) : ℝ))
    (μhatV g (roundedVal P p g.q) + (slackOf (S.gridMass g.q) (p g.q) : ℝ))
    (abs_le.mpr ⟨by linarith, by linarith⟩) (abs_le.mpr ⟨by linarith, by linarith⟩)
    (abs_le.mpr ⟨by linarith, by linarith⟩) (by linarith) (by linarith) (by linarith)

end UnionGuessSlack

open UnionGuessSlack

/-! ## The slack check, the run, soundness and completeness -/

variable {S : UnionSetup I} {N : ℕ} {z : BitInput N}

/-- **The union machine's slack check on a parsed guess**: oracle size, the word bound, then the slack check at the
answers `val` with the slack of `p(q)`-bit rounding. -/
def unionSlackCheck (S : UnionSetup I) {N : ℕ} (z : BitInput N) (g : UnionGuess S z) (tr : List ℕ)
    (callOk : PrimRequest → Bool) (val : PrimRequest → ℚ) (p : ℕ → ℕ) : Bool :=
  decide (g.oracle.size ≤ oracleSizeBound S.G (S.pcp.nativeWidth N)) && decide (g.word.length ≤ N / 16) &&
    slackCheck (g.checkData tr) val S.params.v0 S.params.threshold (slackOf (S.gridMass g.q) (p g.q)) callOk

theorem schedule_calls_iff (g : UnionGuess S z) (callOk : PrimRequest → Bool)
    (hok : ∀ r ∈ (g.checkData g.translation).schedule, callOk r = true ↔ I.Call r) :
    (g.checkData g.translation).schedule.all callOk = true ↔
      ((∀ pos j t, (g.polyVAt pos).coeff j t ≠ 0 → I.Call (g.vCall pos t)) ∧
        (∀ pos j t, (g.polyQAt pos).coeff j t ≠ 0 → I.Call (g.vCall pos t)) ∧
        (∀ i j t, (g.polyMuAt i).coeff j t ≠ 0 → I.Call (g.muCall i t))) := by
  have hV : (∀ pos j t, ((g.checkData g.translation).polyVAt pos).coeff j t ≠ 0 →
      I.Call ((g.checkData g.translation).vCall pos t)) ↔
      ∀ pos j t, (g.polyVAt pos).coeff j t ≠ 0 → I.Call (g.vCall pos t) := by
    constructor
    · intro h pos j t hc
      exact g.checkData_vCall pos t ▸ h pos j t ((g.coeffV_ne_zero _ pos j t).1 hc)
    · intro h pos j t hc
      exact (g.checkData_vCall pos t).symm ▸ h pos j t ((g.coeffV_ne_zero _ pos j t).2 hc)
  have hQ : (∀ pos j t, ((g.checkData g.translation).polyQAt pos).coeff j t ≠ 0 →
      I.Call ((g.checkData g.translation).vCall pos t)) ↔
      ∀ pos j t, (g.polyQAt pos).coeff j t ≠ 0 → I.Call (g.vCall pos t) := by
    constructor
    · intro h pos j t hc
      exact g.checkData_vCall pos t ▸ h pos j t ((g.coeffQ_ne_zero _ pos j t).1 hc)
    · intro h pos j t hc
      exact (g.checkData_vCall pos t).symm ▸ h pos j t ((g.coeffQ_ne_zero _ pos j t).2 hc)
  have hM : (∀ i j t, ((g.checkData g.translation).polyMuAt i).coeff j t ≠ 0 →
      I.Call ((g.checkData g.translation).muCall i t)) ↔
      ∀ i j t, (g.polyMuAt i).coeff j t ≠ 0 → I.Call (g.muCall i t) := by
    constructor
    · intro h i j t hc
      exact g.checkData_muCall i t ▸ h i j t ((g.coeffMu_ne_zero _ i j t).1 hc)
    · intro h i j t hc
      exact (g.checkData_muCall i t).symm ▸ h i j t ((g.coeffMu_ne_zero _ i j t).2 hc)
  rw [List.all_eq_true, ← hV, ← hQ, ← hM, ← UnionCheckData.forall_schedule_iff]
  exact forall₂_congr fun r hr => hok r hr

/-- **Completeness**: an exactly accepting guess passes the slack check at the rounded answers. -/
theorem unionSlackCheck_of_accepts (P : FusedPrimitive I) (p : ℕ → ℕ) (g : UnionGuess S z)
    (callOk : PrimRequest → Bool) (hok : ∀ r ∈ (g.checkData g.translation).schedule, callOk r = true ↔ I.Call r)
    (hg : UnionAccepts S P z g) :
    unionSlackCheck S z g g.translation callOk (roundedVal P p g.q) p = true := by
  obtain ⟨sV, sQ, sμ⟩ := slack_of_accepts g P p hg
  obtain ⟨hsize, hsign, hword, hV, hQ, hM, -, -, -⟩ := hg
  rw [VhatV_eq] at sV
  rw [QhatV_eq] at sQ
  rw [μhatV_eq] at sμ
  unfold unionSlackCheck slackCheck
  simp only [Bool.and_eq_true, decide_eq_true_iff]
  refine ⟨⟨hsize, hword⟩, ⟨⟨⟨⟨?_, (schedule_calls_iff g callOk hok).2 ⟨hV, hQ, hM⟩⟩, ?_⟩, ?_⟩, ?_⟩⟩
  · unfold UnionCheckData.signsOk; exact decide_eq_true_iff.mpr hsign
  · exact_mod_cast sV
  · exact_mod_cast sQ
  · exact_mod_cast sμ

/-- **Soundness direction**: a passing slack check at the rounded answers gives slack acceptance. -/
theorem slackAccepts_of_check (P : FusedPrimitive I) (p : ℕ → ℕ) (g : UnionGuess S z)
    (callOk : PrimRequest → Bool) (hok : ∀ r ∈ (g.checkData g.translation).schedule, callOk r = true ↔ I.Call r)
    (h : unionSlackCheck S z g g.translation callOk (roundedVal P p g.q) p = true) : SlackAccepts g P p := by
  unfold unionSlackCheck slackCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_iff] at h
  obtain ⟨-, ⟨⟨⟨⟨hs, hc⟩, hV⟩, hQ⟩, hμ⟩⟩ := h
  obtain ⟨hcV, hcQ, hcM⟩ := (schedule_calls_iff g callOk hok).1 hc
  have hs' : ∀ X a, g.sign X a ∈ ({-1, 0, 1} : Finset ℤ) := by
    unfold UnionCheckData.signsOk at hs; exact decide_eq_true_iff.mp hs
  refine ⟨hs', hcV, hcQ, hcM, ?_, ?_, ?_⟩
  · rw [VhatV_eq]; exact_mod_cast hV
  · rw [QhatV_eq]; exact_mod_cast hQ
  · rw [μhatV_eq]; exact_mod_cast hμ

/-- **The union machine's run on a witness**: decode it, then the slack check at the rounded answers
(the translation `tr` a parameter, as in T's `unionRun`, so the run stays executable). -/
def unionSlackRun (S : UnionSetup I) {N : ℕ} (z : BitInput N) (tr : UnionGuess S z → List ℕ)
    (callOk : PrimRequest → Bool) (P : FusedPrimitive I) (p : ℕ → ℕ) (w : List Bool) : Bool :=
  match decodeGuess S z w with
  | none => false
  | some g => unionSlackCheck S z g (tr g) callOk (roundedVal P p g.q) p

theorem unionSlackRun_sound (P : FusedPrimitive I) (p : ℕ → ℕ) (callOk : PrimRequest → Bool)
    (hok : ∀ g : UnionGuess S z, ∀ r ∈ (g.checkData g.translation).schedule, callOk r = true ↔ I.Call r)
    (w : List Bool) (h : unionSlackRun S z UnionGuess.translation callOk P p w = true) : ∃ g : UnionGuess S z, SlackAccepts g P p := by
  unfold unionSlackRun at h
  split at h
  · exact absurd h Bool.false_ne_true
  · exact ⟨_, slackAccepts_of_check P p _ callOk (hok _) h⟩

theorem unionSlackRun_complete (P : FusedPrimitive I) (p : ℕ → ℕ) (callOk : PrimRequest → Bool) (g : UnionGuess S z)
    (hok : ∀ r ∈ (g.checkData g.translation).schedule, callOk r = true ↔ I.Call r) (hg : UnionAccepts S P z g)
    (W : ℕ) (hW : N / 16 ≤ W) :
    ∃ w : List Bool, w.length = W ∧ unionSlackRun S z UnionGuess.translation callOk P p w = true := by
  have hlen : g.word.length ≤ W := hg.2.2.1.trans hW
  refine ⟨encodeGuess g ++ List.replicate (W - g.word.length) false, ?_, ?_⟩
  · simp only [List.length_append, List.length_replicate, encodeGuess]
    omega
  · unfold unionSlackRun
    rw [decodeGuess_encodeGuess]
    exact unionSlackCheck_of_accepts P p g callOk hok hg

/-- **Slack soundness of a machine**: it accepts only through slack-accepting guesses. -/
def SoundForSlack (S : UnionSetup I) (P : FusedPrimitive I) (p : ℕ → ℕ) (M : OrdinaryWeakMachine) : Prop :=
  ∀ N (z : BitInput N), M.accepts N z → ∃ g : UnionGuess S z, SlackAccepts g P p

/-- **`OneSided` from slack soundness**: once the outer error is positive, the native width grows, and the rounded
answers' propagated error plus the slack eventually fits `ε₀`. -/
theorem oneSided_of_soundForSlack (S : UnionSetup I) (P : FusedPrimitive I) (p : ℕ → ℕ) (M : OrdinaryWeakMachine)
    (hS : SoundForSlack S P p M) (hη : 0 < (S.params.outerError : ℝ))
    (hw : Tendsto (fun N => S.pcp.nativeWidth N) atTop atTop)
    (hD : ∀ᶠ q : ℕ in atTop, (1 + (S.gridMass q : ℝ)) ^ 4 * ((q : ℝ) ^ (-(I.D : ℝ)) + 1 / 2 ^ p q) +
      (slackOf (S.gridMass q) (p q) : ℝ) ≤ (S.params.eps0 : ℝ)) :
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
  exact not_slackAccepts g P p (hn₀ n hn).1.1 hno (hn₀ n hn).1.2
    (hQ _ ((hn₀ n hn).2.trans (nativeWidth_le_q S g))) hg

end Slack

end NearCubicWires.WireExponent3_5.UnionMachine
