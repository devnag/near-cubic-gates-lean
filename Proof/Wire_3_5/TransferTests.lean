import Proof.Circuits.ComponentwiseBranchExtraction
import Proof.Wire_3_5.Rounding

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires NearCubicWires.SourceInterfaces
open NearCubicWires.WireExponent3_5.Shared (uMean bitR maskedMean uMean_mono uMean_add bitR_nonneg bitR_le_one
  maskedMean_le_of_nonneg maskedRounding_holds)
open NearCubicWires.ComponentwiseValidity (validityPenalty validityRound clauseValue)
open NearCubicWires.ComponentwiseBranchExtraction (literalIndex literalNegated systematicConstraint roundedProof
  roundedAuxiliary clauseRealValue roundedProof_eq_assignment clauseRealValue_bitAsReal)

/-! ## Uniform means: two helpers -/

theorem uMean_sub {Ω : Type} [Fintype Ω] (f g : Ω → ℝ) : uMean (fun ω => f ω - g ω) = uMean f - uMean g := by
  unfold uMean; rw [Finset.sum_sub_distrib, sub_div]

theorem uMean_const {Ω : Type} [Fintype Ω] [Nonempty Ω] (c : ℝ) : uMean (fun _ : Ω => c) = c := by
  unfold uMean
  have h : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

theorem uMean_clause_seed_input {C Seed In : Type} [Fintype C] [Fintype Seed] [Fintype In] [Nonempty C]
    [Nonempty Seed] [Nonempty In] (g : C → In → ℝ) :
    uMean (fun p : C × (Seed × In) => g p.1 p.2.2) = uMean (fun x : In => uMean (fun i : C => g i x)) := by
  unfold uMean
  have hC : (0 : ℝ) < Fintype.card C := by exact_mod_cast Fintype.card_pos
  have hS : (0 : ℝ) < Fintype.card Seed := by exact_mod_cast Fintype.card_pos
  have hI : (0 : ℝ) < Fintype.card In := by exact_mod_cast Fintype.card_pos
  simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_prod,
    Nat.cast_mul]
  rw [← Finset.sum_div, Finset.sum_comm, ← Finset.mul_sum]
  field_simp

/-! ## Clause positions of the PCPP -/

section Positions
variable {q : ℕ} {H : BooleanCircuit q} (pcpp : PointwisePCPP H)

abbrev PcppVar : Type := Fin (pcpp.systematicBits + pcpp.auxiliaryBits)

/-- The literal at position `j ∈ {0,1}` of clause `i`. -/
def posLiteral (i : Fin (2 ^ pcpp.clauseBits)) (j : Fin 2) :
    Literal (pcpp.systematicBits + pcpp.auxiliaryBits) :=
  ![(pcpp.clauses i).left, (pcpp.clauses i).right] j

def posVar (i : Fin (2 ^ pcpp.clauseBits)) (j : Fin 2) : PcppVar pcpp := literalIndex (posLiteral pcpp i j)

def posNeg (i : Fin (2 ^ pcpp.clauseBits)) (j : Fin 2) : Bool := literalNegated (posLiteral pcpp i j)

@[simp] theorem posVar_zero (i : Fin (2 ^ pcpp.clauseBits)) :
    posVar pcpp i 0 = literalIndex (pcpp.clauses i).left := by simp [posVar, posLiteral]
@[simp] theorem posVar_one (i : Fin (2 ^ pcpp.clauseBits)) :
    posVar pcpp i 1 = literalIndex (pcpp.clauses i).right := by simp [posVar, posLiteral]
@[simp] theorem posNeg_zero (i : Fin (2 ^ pcpp.clauseBits)) :
    posNeg pcpp i 0 = literalNegated (pcpp.clauses i).left := by simp [posNeg, posLiteral]
@[simp] theorem posNeg_one (i : Fin (2 ^ pcpp.clauseBits)) :
    posNeg pcpp i 1 = literalNegated (pcpp.clauses i).right := by simp [posNeg, posLiteral]

end Positions

section Tests
variable {q : ℕ} {H : BooleanCircuit q} (pcpp : PointwisePCPP H) {Seed : Type} [Fintype Seed]

/-- `V = E_{pos,e,x} G_X P_X`: the masked validity penalty, `P_X = S_X²(1−S_X)²` on auxiliary variables and
`(S_X − E_X(x))²` on systematic ones (`validityPenalty` at the prescribed constraint). -/
noncomputable def testV (S : PcppVar pcpp → BitInput q → ℝ) (G : PcppVar pcpp → Seed → BitInput q → Bool) : ℝ :=
  uMean fun p : Fin (2 ^ pcpp.clauseBits) × Fin 2 × (Seed × BitInput q) =>
    bitR (G (posVar pcpp p.1 p.2.1) p.2.2.1 p.2.2.2) *
      validityPenalty (systematicConstraint pcpp p.2.2.2 (posVar pcpp p.1 p.2.1)) (S (posVar pcpp p.1 p.2.1) p.2.2.2)

/-- `Q = E_{pos,e,x} G_X S_X²`: the masked second moment (kept). -/
noncomputable def testQ (S : PcppVar pcpp → BitInput q → ℝ) (G : PcppVar pcpp → Seed → BitInput q → Bool) : ℝ :=
  uMean fun p : Fin (2 ^ pcpp.clauseBits) × Fin 2 × (Seed × BitInput q) =>
    bitR (G (posVar pcpp p.1 p.2.1) p.2.2.1 p.2.2.2) * S (posVar pcpp p.1 p.2.1) p.2.2.2 ^ 2

def clauseMask (G : PcppVar pcpp → Seed → BitInput q → Bool) (i : Fin (2 ^ pcpp.clauseBits)) (e : Seed)
    (x : BitInput q) : Bool :=
  G (posVar pcpp i 0) e x && G (posVar pcpp i 1) e x

/-- `μ = E_{i,e,x} M_i Cons_i(S_{X(i,1)}, S_{X(i,2)})`, with `Cons_i` the degree-two arithmetization of the
two-literal OR with its prescribed signs (`clauseRealValue`, Theorem 2.5's `clauseValue`). -/
noncomputable def testMu (S : PcppVar pcpp → BitInput q → ℝ) (G : PcppVar pcpp → Seed → BitInput q → Bool) : ℝ :=
  uMean fun p : Fin (2 ^ pcpp.clauseBits) × (Seed × BitInput q) =>
    bitR (clauseMask pcpp G p.1 p.2.1 p.2.2) * clauseRealValue (pcpp.clauses p.1) (fun X => S X p.2.2)

end Tests

structure MaskedSoundnessParameters (cp sp : ℝ) where
  v0 : ℚ
  eps0 : ℚ
  outerError : ℚ
  threshold : ℚ
  v0_pos : 0 < v0
  v0_le : v0 ≤ 1 / 24
  eps0_nonneg : 0 ≤ eps0
  eps0_le_v0 : eps0 ≤ v0
  sp_nonneg : 0 ≤ sp
  thresholdAboveMidpoint : (cp + sp) / 2 ≤ (threshold : ℝ)
  roundingReserve : 5 * Real.sqrt (24 * (v0 : ℝ)) + (eps0 : ℝ) < (cp - sp) / 3
  outerReserve : (outerError : ℝ) ≤ (cp - sp) / 6

def MaskedAccepts {cp sp : ℝ} (params : MaskedSoundnessParameters cp sp) (Vhat Qhat μhat : ℚ) : Prop :=
  Vhat ≤ 2 * params.v0 ∧ Qhat ≤ 1 + params.v0 ∧ params.threshold ≤ μhat

instance {cp sp : ℝ} (params : MaskedSoundnessParameters cp sp) (Vhat Qhat μhat : ℚ) :
    Decidable (MaskedAccepts params Vhat Qhat μhat) := by
  unfold MaskedAccepts; infer_instance

structure MaskedVerifierTrace {q : ℕ} {H : BooleanCircuit q} (pcpp : PointwisePCPP H) {cp sp : ℝ}
    (params : MaskedSoundnessParameters cp sp) (Seed : Type) [Fintype Seed] where
  guess : PcppVar pcpp → BitInput q → ℝ
  filter : PcppVar pcpp → Seed → BitInput q → Bool
  Vhat : ℚ
  Qhat : ℚ
  μhat : ℚ
  V_accurate : |(Vhat : ℝ) - testV pcpp guess filter| ≤ params.eps0
  Q_accurate : |(Qhat : ℝ) - testQ pcpp guess filter| ≤ params.eps0
  μ_accurate : |(μhat : ℝ) - testMu pcpp guess filter| ≤ params.eps0
  accepted : MaskedAccepts params Vhat Qhat μhat

section Soundness
variable {q : ℕ} {H : BooleanCircuit q} (pcpp : PointwisePCPP H) {Seed : Type} [Fintype Seed]

noncomputable def roundedClause (S : PcppVar pcpp → BitInput q → ℝ) (i : Fin (2 ^ pcpp.clauseBits))
    (x : BitInput q) : ℝ :=
  clauseRealValue (pcpp.clauses i) (fun X => bitAsReal (roundedProof pcpp x (fun X => S X x) X))

/-- The rounded proof is a genuine PCPP assignment, so its clause value is the Boolean clause value. -/
theorem roundedClause_eq (S : PcppVar pcpp → BitInput q → ℝ) (i : Fin (2 ^ pcpp.clauseBits)) (x : BitInput q) :
    roundedClause pcpp S i x =
      bitAsReal ((pcpp.clauses i).eval (pcpp.assignment x (roundedAuxiliary pcpp (fun X => S X x)))) := by
  unfold roundedClause
  rw [clauseRealValue_bitAsReal, roundedProof_eq_assignment]

theorem roundedClause_nonneg (S : PcppVar pcpp → BitInput q → ℝ) (i : Fin (2 ^ pcpp.clauseBits))
    (x : BitInput q) : 0 ≤ roundedClause pcpp S i x := by
  rw [roundedClause_eq]; cases (pcpp.clauses i).eval _ <;> simp [bitAsReal]

/-- The masked rounded score `E_{i,e,x} M_i Cons_i(B)`. -/
noncomputable def maskedRoundedScore (S : PcppVar pcpp → BitInput q → ℝ)
    (G : PcppVar pcpp → Seed → BitInput q → Bool) : ℝ :=
  uMean fun p : Fin (2 ^ pcpp.clauseBits) × (Seed × BitInput q) =>
    bitR (clauseMask pcpp G p.1 p.2.1 p.2.2) * roundedClause pcpp S p.1 p.2.2

theorem testMu_le_rounded (S : PcppVar pcpp → BitInput q → ℝ) (G : PcppVar pcpp → Seed → BitInput q → Bool)
    (v₀ : ℝ) (hv : 0 < v₀) (hv24 : v₀ ≤ 1 / 24) (hV : testV pcpp S G ≤ 3 * v₀)
    (hQ : testQ pcpp S G ≤ 1 + 2 * v₀) :
    testMu pcpp S G ≤ maskedRoundedScore pcpp S G + 5 * Real.sqrt (24 * v₀) := by
  have h := maskedRounding_holds (Clause := Fin (2 ^ pcpp.clauseBits)) (Ω := Seed × BitInput q)
    (fun i j ω => S (posVar pcpp i j) ω.2) (fun i j ω => systematicConstraint pcpp ω.2 (posVar pcpp i j))
    (fun i j => posNeg pcpp i j) (fun i j ω => G (posVar pcpp i j) ω.1 ω.2) v₀ hv hv24 hV hQ
  have hsplit : uMean (fun p : Fin (2 ^ pcpp.clauseBits) × (Seed × BitInput q) =>
      bitR (G (posVar pcpp p.1 0) p.2.1 p.2.2 && G (posVar pcpp p.1 1) p.2.1 p.2.2) *
        (clauseValue (posNeg pcpp p.1 0) (posNeg pcpp p.1 1) (S (posVar pcpp p.1 0) p.2.2)
            (S (posVar pcpp p.1 1) p.2.2) -
          clauseValue (posNeg pcpp p.1 0) (posNeg pcpp p.1 1)
            (bitAsReal (validityRound (systematicConstraint pcpp p.2.2 (posVar pcpp p.1 0))
              (S (posVar pcpp p.1 0) p.2.2)))
            (bitAsReal (validityRound (systematicConstraint pcpp p.2.2 (posVar pcpp p.1 1))
              (S (posVar pcpp p.1 1) p.2.2))))) =
      testMu pcpp S G - maskedRoundedScore pcpp S G := by
    unfold testMu maskedRoundedScore
    rw [← uMean_sub]
    refine congrArg uMean (funext fun p => ?_)
    simp only [mul_sub, posVar_zero, posVar_one, posNeg_zero, posNeg_one, clauseMask, roundedClause,
      clauseRealValue, roundedProof]
  rw [hsplit] at h
  linarith [(abs_le.mp h).2]

theorem maskedRoundedScore_le [Nonempty Seed] (S : PcppVar pcpp → BitInput q → ℝ)
    (G : PcppVar pcpp → Seed → BitInput q → Bool) :
    maskedRoundedScore pcpp S G ≤ uMean (fun x : BitInput q => uMean (fun i => roundedClause pcpp S i x)) := by
  have h0 := maskedMean_le_of_nonneg
    (fun p : Fin (2 ^ pcpp.clauseBits) × (Seed × BitInput q) => clauseMask pcpp G p.1 p.2.1 p.2.2)
    (f := fun p => roundedClause pcpp S p.1 p.2.2) (fun p => roundedClause_nonneg pcpp S p.1 p.2.2)
  have e : maskedRoundedScore pcpp S G =
      maskedMean (fun p : Fin (2 ^ pcpp.clauseBits) × (Seed × BitInput q) => clauseMask pcpp G p.1 p.2.1 p.2.2)
        (fun p => roundedClause pcpp S p.1 p.2.2) := by
    unfold maskedRoundedScore maskedMean; rfl
  have h1 : maskedRoundedScore pcpp S G ≤
      uMean (fun p : Fin (2 ^ pcpp.clauseBits) × (Seed × BitInput q) => roundedClause pcpp S p.1 p.2.2) :=
    e ▸ h0
  haveI : Nonempty (Fin (2 ^ pcpp.clauseBits)) := ⟨⟨0, by positivity⟩⟩
  rwa [uMean_clause_seed_input (fun i x => roundedClause pcpp S i x)] at h1

/-- The clause mean of the rounded proof at `x` is the PCPP satisfied fraction of that assignment. -/
theorem uMean_roundedClause (S : PcppVar pcpp → BitInput q → ℝ) (x : BitInput q) :
    uMean (fun i => roundedClause pcpp S i x) =
      pcpp.satisfiedFraction x (roundedAuxiliary pcpp (fun X => S X x)) := by
  rw [← ComponentwiseBranchExtraction.expect_bitAsReal_eq_satisfiedFraction, Finset.expect_eq_sum_div_card,
    Finset.card_univ]
  unfold uMean
  congr 1
  exact Finset.sum_congr rfl fun i _ => roundedClause_eq pcpp S i x

theorem roundedScore_le_soundness {sp : ℝ} (hsp : 0 ≤ sp)
    (hsound : ∀ x, ¬ H.eval x → ∀ aux, pcpp.satisfiedFraction x aux ≤ sp) (S : PcppVar pcpp → BitInput q → ℝ) :
    uMean (fun x : BitInput q => uMean (fun i => roundedClause pcpp S i x)) ≤
      sp + uMean (fun x : BitInput q => bitR (H.eval x)) := by
  have hpt : ∀ x : BitInput q, uMean (fun i => roundedClause pcpp S i x) ≤ sp + bitR (H.eval x) := by
    intro x
    rw [uMean_roundedClause]
    by_cases hx : H.eval x
    · have := ComponentwiseVerifierParameters.pointwiseSatisfiedFraction_le_one pcpp x
        (roundedAuxiliary pcpp (fun X => S X x))
      simp only [hx, bitR, if_true]; linarith
    · have := hsound x hx (roundedAuxiliary pcpp (fun X => S X x))
      simp only [hx, bitR, Bool.false_eq_true, if_false]; linarith
  calc uMean (fun x : BitInput q => uMean (fun i => roundedClause pcpp S i x))
      ≤ uMean (fun x : BitInput q => sp + bitR (H.eval x)) := uMean_mono hpt
    _ = sp + uMean (fun x : BitInput q => bitR (H.eval x)) := by rw [uMean_add, uMean_const]

theorem maskedVerifierTrace_empty {cp sp : ℝ} (params : MaskedSoundnessParameters cp sp) [Nonempty Seed]
    (hsound : ∀ x, ¬ H.eval x → ∀ aux, pcpp.satisfiedFraction x aux ≤ sp)
    (houter : uMean (fun x : BitInput q => bitR (H.eval x)) ≤ params.outerError) :
    IsEmpty (MaskedVerifierTrace pcpp params Seed) := by
  refine ⟨fun trace => ?_⟩
  obtain ⟨hVp, hQp, hμp⟩ := trace.accepted
  have hv0 : (0 : ℝ) < params.v0 := by exact_mod_cast params.v0_pos
  have hv24 : (params.v0 : ℝ) ≤ 1 / 24 :=
    calc (params.v0 : ℝ) ≤ ((1 / 24 : ℚ) : ℝ) := Rat.cast_le.mpr params.v0_le
      _ = 1 / 24 := by norm_num
  have hεv : (params.eps0 : ℝ) ≤ params.v0 := by exact_mod_cast params.eps0_le_v0
  have hVp' : (trace.Vhat : ℝ) ≤ 2 * params.v0 := by exact_mod_cast hVp
  have hQp' : (trace.Qhat : ℝ) ≤ 1 + params.v0 := by exact_mod_cast hQp
  have hμp' : (params.threshold : ℝ) ≤ trace.μhat := by exact_mod_cast hμp
  have hV : testV pcpp trace.guess trace.filter ≤ 3 * (params.v0 : ℝ) := by
    linarith [(abs_le.mp trace.V_accurate).1]
  have hQ : testQ pcpp trace.guess trace.filter ≤ 1 + 2 * (params.v0 : ℝ) := by
    linarith [(abs_le.mp trace.Q_accurate).1]
  have h1 := testMu_le_rounded pcpp trace.guess trace.filter params.v0 hv0 hv24 hV hQ
  have h2 := maskedRoundedScore_le pcpp trace.guess trace.filter
  have h3 := roundedScore_le_soundness pcpp params.sp_nonneg hsound trace.guess
  have h4 := (abs_le.mp trace.μ_accurate).2
  have hmid := params.thresholdAboveMidpoint
  have hres := params.roundingReserve
  have hout := params.outerReserve
  linarith

end Soundness

/-! ## The paper's parameter choice is satisfiable, and the trace is not vacuous -/

noncomputable def satMaskedSoundnessParameters : MaskedSoundnessParameters (3 / 4) (1 / 4) where
  v0 := 1 / 100000
  eps0 := 1 / 100000
  outerError := 1 / 100
  threshold := 1 / 2
  v0_pos := by norm_num
  v0_le := by norm_num
  eps0_nonneg := by norm_num
  eps0_le_v0 := le_rfl
  sp_nonneg := by norm_num
  thresholdAboveMidpoint := by norm_num
  roundingReserve := by
    have hs : Real.sqrt (24 * ((1 / 100000 : ℚ) : ℝ)) ≤ 1 / 50 := by
      rw [Real.sqrt_le_left (by norm_num)]
      norm_num
    push_cast at hs ⊢
    linarith
  outerReserve := by norm_num

/-- A one-clause PCPP (`y ∨ y` on one auxiliary variable) for the constant-true circuit, used only to show that the
trace is satisfiable on its own. -/
def regressionMaskedPCPP : PointwisePCPP (ComponentwiseVerifierParameters.constantBooleanCircuit true) where
  systematicBits := 0
  auxiliaryBits := 1
  clauseBits := 0
  systematicSupport := fun i => i.elim0
  systematicSupportBound := fun i => i.elim0
  clauses := fun _ => ⟨.positive ⟨0, by omega⟩, .positive ⟨0, by omega⟩⟩
  honestAuxiliary := fun _ _ => true
  constructionSteps := 0
  honestSteps := fun _ => 0

/-- Non-vacuity: on a yes-instance (the constant-true circuit) the trace exists — guess `S ≡ 1`, all masks on,
exact estimates `V̂ = 0`, `Q̂ = 1`, `μ̂ = 1` — so `maskedVerifierTrace_empty` draws its contradiction from the PCPP
soundness and outer-error hypotheses, not from an unsatisfiable field. -/
theorem maskedVerifierTrace_nonvacuous :
    Nonempty (MaskedVerifierTrace regressionMaskedPCPP satMaskedSoundnessParameters Unit) := by
  have hV : testV regressionMaskedPCPP (Seed := Unit) (fun _ _ => 1) (fun _ _ _ => true) = 0 := by
    unfold testV uMean
    simp [bitR, systematicConstraint, validityPenalty, ComponentwiseValidity.booleanityPenalty, Fin.addCases,
      posVar, posLiteral, regressionMaskedPCPP, literalIndex]
  have hQ : testQ regressionMaskedPCPP (Seed := Unit) (fun _ _ => 1) (fun _ _ _ => true) = 1 := by
    unfold testQ uMean
    simp [bitR]
  have hμ : testMu regressionMaskedPCPP (Seed := Unit) (fun _ _ => 1) (fun _ _ _ => true) = 1 := by
    have h2 : Fintype.card (Fin (2 ^ regressionMaskedPCPP.clauseBits) × (Unit × BitInput 1)) = 2 := by
      simp [BitInput, Fintype.card_prod, Fintype.card_pi, regressionMaskedPCPP]
    unfold testMu uMean
    rw [Finset.sum_congr rfl (g := fun _ => (1 : ℝ)) (fun p _ => by
      simp [bitR, clauseMask, clauseRealValue, clauseValue, ComponentwiseValidity.literalValue, literalNegated,
        regressionMaskedPCPP])]
    rw [Finset.sum_const, Finset.card_univ, h2]
    norm_num
  have hε : (0 : ℝ) ≤ (satMaskedSoundnessParameters.eps0 : ℝ) := by
    exact_mod_cast satMaskedSoundnessParameters.eps0_nonneg
  refine ⟨⟨fun _ _ => 1, fun _ _ _ => true, 0, 1, 1, ?_, ?_, ?_, ?_⟩⟩
  · rw [hV]; simpa using hε
  · rw [hQ]; simpa using hε
  · rw [hμ]; simpa using hε
  · refine ⟨by simp [satMaskedSoundnessParameters], by simp [satMaskedSoundnessParameters],
      by simp [satMaskedSoundnessParameters]; norm_num⟩

end NearCubicWires.WireExponent3_5.Transfer
