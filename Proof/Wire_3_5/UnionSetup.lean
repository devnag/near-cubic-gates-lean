import Proof.Wire_3_5.UnionAtoms
import Proof.Wire_3_5.UnionParams
import Proof.Wire_3_5.GateUnion
import Proof.Wire_3_5.Split
import Proof.Hierarchy.CompetitorSourceAverage
import Proof.Foundations.ProjectionPCPPadding

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.ProjectionPCPPadding (padProjectionPCP padProjectionPCP_sound)
open NearCubicWires.RepairOrdinary.CompetitorSourceAverage (acceptanceMean request_acceptance outer_acceptance
  oracleProof)
open NearCubicWires.WireExponent3_5.Shared (uMean bitR)
open NearCubicWires.Bindings.CLW20Theorem113 (InNTIME)

/-! ## Outer soundness of a padded hierarchy PCP -/

theorem uMean_bitR_eq_acceptanceMean {n : ℕ} (c : BooleanCircuit n) :
    uMean (fun x : BitInput n => bitR (c.eval x)) = acceptanceMean c := by
  unfold uMean acceptanceMean bitR
  rw [Finset.expect_eq_sum_div_card, Finset.card_univ]

theorem padded_outerSound {T : ℕ → ℕ} {H : OrdinaryHierarchy T} {degrees : PCPDegrees}
    (P : OrdinaryPCPResult H degrees) (w : ℕ → ℕ) (hw : ∀ n, P.pcp.nativeWidth n ≤ w n) (a : PointwisePCPPAlgorithm)
    (N : ℕ) (hN : 1 ≤ N) (z : BitInput N) (hno : H.timedView.accepts N z = false)
    (oracle : BooleanCircuit ((padProjectionPCP P.pcp w hw).nativeWidth N)) :
    uMean (fun x : BitInput (unionRequest (padProjectionPCP P.pcp w hw) a z oracle).arity =>
      bitR ((unionRequest (padProjectionPCP P.pcp w hw) a z oracle).circuit.eval x)) ≤ 1 / (N : ℝ) ^ 10 := by
  rw [uMean_bitR_eq_acceptanceMean]
  have hind : ∀ u v, (padProjectionPCP P.pcp w hw).decision z u = (padProjectionPCP P.pcp w hw).decision z v :=
    fun u v => P.decisionIndependent N z _ _
  have hacc := (request_acceptance a _).trans (outer_acceptance (padProjectionPCP P.pcp w hw) z oracle hind)
  unfold unionRequest
  rw [show PCPPSubstitution.sourceRequest a oracle ((padProjectionPCP P.pcp w hw).queryAddressBits z)
      ((padProjectionPCP P.pcp w hw).decision z fun _ => false) =
      PCPPRequestBoundary.request a (PCPPSubstitution.compactSubstituted oracle
        ((padProjectionPCP P.pcp w hw).queryAddressBits z) ((padProjectionPCP P.pcp w hw).decision z fun _ => false))
      from rfl, hacc]
  exact padProjectionPCP_sound P.pcp w hw z _ (P.sound N hN z hno) (oracleProof oracle)

/-! ## A setup from a hierarchy PCP result -/

section Setup
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E}

/-- The union setup from a hierarchy `H` deciding `L`, its PCP result `P`, a padded width, a PCPP algorithm, the oracle
degree, the masked verifier's constants and the grid. -/
noncomputable def setupOfResult (I : PrimitiveInputs B) (L : Language) {T : ℕ → ℕ} (H : OrdinaryHierarchy T)
    (hL : ∀ n (x : BitInput n), L n x = true ↔ H.verifier.language H.time n x) {degrees : PCPDegrees}
    (P : OrdinaryPCPResult H degrees) (w : ℕ → ℕ) (hw : ∀ n, P.pcp.nativeWidth n ≤ w n) (a : PointwisePCPPAlgorithm)
    (G : ℕ) (params : MaskedSoundnessParameters a.completeness a.soundness) (gridMass : ℕ → ℚ)
    (hmass : ∀ q, 0 ≤ gridMass q) (gridSize : ℕ → ℕ) : UnionSetup I where
  language := L
  machine := H.timedView
  clock := H.time
  decides := fun N z => Bool.eq_iff_iff.2 ((hL N z).trans (hierarchy_language_exact H N z).symm)
  pcp := padProjectionPCP P.pcp w hw
  pcppAlg := a
  outerSound := fun N hN z hno oracle => padded_outerSound P w hw a N hN z hno oracle
  G := G
  params := params
  gridMass := gridMass
  gridMass_nonneg := hmass
  gridSize := gridSize
  constAtom := unionConstAtom
  constAtom_eval := unionConstAtom_eval
  constAtom_gates := unionConstAtom_gates
  parityAtom := unionParityAtom
  parityAtom_eval := unionParityAtom_eval

end Setup

/-! ## The gate's setup `S₀` -/

/-- The masked verifier's soundness constants at the literal's PCPP gap. -/
noncomputable def gateParams (l : Literals) : MaskedSoundnessParameters (gatePCPP l).completeness (gatePCPP l).soundness :=
  Classical.choose (exists_unionParams (gatePCPP l).soundnessPositive.le (gatePCPP l).gap)

/-- The matching completeness constants. -/
noncomputable def gateCParams (l : Literals) : MaskedCompletenessParameters (gateParams l) :=
  Classical.choice (Classical.choose_spec (exists_unionParams (gatePCPP l).soundnessPositive.le (gatePCPP l).gap))

/-- `C_δ = ⌈5/δ²⌉`: the grid's size-to-mass ratio `s = C_δ Λ̄²` with `19 ≤ C_δ²δ⁴`. -/
noncomputable def gateCδ (l : Literals) : ℕ := ⌈(5 : ℚ) / (gateCParams l).δ ^ 2⌉₊

/-- `Λ̄(q) = ⌊√(s(q)/C_δ)⌋`: the largest mass the gate's grid size supports. -/
def gridMassOf (Cδ : ℕ) (sp : ℕ → ℕ) (q : ℕ) : ℚ := (Nat.sqrt (sp q / Cδ) : ℕ)

/-- **`19Λ̄⁴ ≤ s²δ⁴`** at every `q` (`hsδ` of `exists_unionAccepts`), whenever `5 ≤ C_δ δ²`. -/
theorem gridMass_hsδ (Cδ : ℕ) (sp : ℕ → ℕ) (δ : ℚ) (hδ : 0 ≤ δ) (hC : 5 ≤ (Cδ : ℚ) * δ ^ 2) (q : ℕ) :
    19 * ((gridMassOf Cδ sp q : ℚ) : ℝ) ^ 4 ≤ ((sp q : ℕ) : ℝ) ^ 2 * (δ : ℝ) ^ 4 := by
  unfold gridMassOf
  set m := Nat.sqrt (sp q / Cδ) with hm
  have h1 : m * m ≤ sp q / Cδ := Nat.sqrt_le _
  have h2 : sp q / Cδ * Cδ ≤ sp q := Nat.div_mul_le_self _ _
  have h3 : Cδ * (m * m) ≤ sp q := by nlinarith
  have h3' : (Cδ : ℝ) * ((m : ℝ) * m) ≤ (sp q : ℝ) := by exact_mod_cast h3
  have hC' : (5 : ℝ) ≤ (Cδ : ℝ) * (δ : ℝ) ^ 2 := by exact_mod_cast hC
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hδ0 : (0 : ℝ) ≤ δ := by exact_mod_cast hδ
  push_cast
  have hsq : ((Cδ : ℝ) * ((m : ℝ) * m)) ^ 2 ≤ (sp q : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) h3' 2
  have h25 : (25 : ℝ) * (m : ℝ) ^ 4 ≤ ((Cδ : ℝ) * (δ : ℝ) ^ 2) ^ 2 * (m : ℝ) ^ 4 := by
    have : (25 : ℝ) ≤ ((Cδ : ℝ) * (δ : ℝ) ^ 2) ^ 2 := by nlinarith
    nlinarith [pow_nonneg hm0 4]
  nlinarith [pow_nonneg hm0 4, pow_nonneg hδ0 4]

theorem gateCδ_spec (l : Literals) : 5 ≤ ((gateCδ l : ℕ) : ℚ) * (gateCParams l).δ ^ 2 ∨ (gateCParams l).δ = 0 := by
  by_cases hδ : (gateCParams l).δ = 0
  · exact Or.inr hδ
  · left
    have hpos : 0 < (gateCParams l).δ ^ 2 := by positivity
    have hc : (5 : ℚ) / (gateCParams l).δ ^ 2 ≤ (gateCδ l : ℚ) := Nat.le_ceil _
    calc (5 : ℚ) = 5 / (gateCParams l).δ ^ 2 * (gateCParams l).δ ^ 2 := by field_simp
      _ ≤ (gateCδ l : ℚ) * (gateCParams l).δ ^ 2 := by gcongr

variable (l : Literals) (G : Split.Gate) (oracleDeg : ℕ)

/-- The hierarchy of `L` (chosen from `L ∈ NTIME(T)`). -/
noncomputable def hierarchyOf {kclk : ℕ} {L : Language} (hL : InNTIME (fun n => n ^ (kclk + 2)) L) :
    OrdinaryHierarchy (fun n => n ^ (kclk + 2)) :=
  Classical.choose hL

/-- The padding exponent of the hierarchy PCP (`k + 3 ≤ C_pad`, `H.coefficient ≤ C_pad`). -/
noncomputable def cpadOf {kclk : ℕ} (H : OrdinaryHierarchy (fun n => n ^ (kclk + 2))) : ℕ := max H.coefficient (kclk + 3)

/-- The universal-source hierarchy PCP of `H` (base `HierarchyNormalized.separated`). -/
noncomputable def hierarchyPCP {kclk : ℕ} (H : OrdinaryHierarchy (fun n => n ^ (kclk + 2))) :
    SeparatedPCPResult H (ProjectionNormalization.HierarchyNormalizedBounds.inputExponent (gateSource l)) :=
  ProjectionNormalization.HierarchyNormalized.separated (gateSource l) H (cpadOf H) (le_max_left _ _)
    (le_max_right _ _)

/-- The padded width `max(R(N), q(N))`. -/
noncomputable def paddedWidth {kclk : ℕ} (H : OrdinaryHierarchy (fun n => n ^ (kclk + 2))) (N : ℕ) : ℕ :=
  max ((hierarchyPCP l H).data.pcp.nativeWidth N) (Ledger.nativeWidth kclk G.Apad N)

/-- **The pinned union setup `S₀`** at every gate: for every ledger and every `L ∈ NTIME(N^{kclk+2})`, the padded
universal-source PCP of `L`'s hierarchy, the `clw311` PCPP, the gate's grid, and the atoms. -/
noncomputable def unionSetupS0 : G.Setup := fun kclk coef A a ha L hL =>
  setupOfResult (G.inputs kclk coef A a ha) L (hierarchyOf hL) (Classical.choose_spec hL)
    (hierarchyPCP l (hierarchyOf hL)).data (paddedWidth l G (hierarchyOf hL)) (fun _ => le_max_left _ _) (gatePCPP l)
    oracleDeg (gateParams l) (gridMassOf (gateCδ l) G.row.sp) (fun _ => by unfold gridMassOf; positivity) G.row.sp

theorem unionSetupS0_language (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (L : Language)
    (hL : InNTIME (fun n => n ^ (kclk + 2)) L) : (unionSetupS0 l G oracleDeg kclk coef A a ha L hL).language = L := rfl

theorem unionSetupS0_gridSize (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (L : Language)
    (hL : InNTIME (fun n => n ^ (kclk + 2)) L) : (unionSetupS0 l G oracleDeg kclk coef A a ha L hL).gridSize = G.row.sp :=
  rfl

/-- The padded width is the ledger's `q(N)` eventually. -/
theorem unionSetupS0_width (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (L : Language)
    (hL : InNTIME (fun n => n ^ (kclk + 2)) L) (hApad : (gateSource l).degrees.proofLog + 6 ≤ G.Apad) :
    ∃ N₀, ∀ N, N₀ ≤ N →
      (unionSetupS0 l G oracleDeg kclk coef A a ha L hL).pcp.nativeWidth N = Ledger.nativeWidth kclk G.Apad N := by
  obtain ⟨N₀, hN₀⟩ := width_le_nativeWidth kclk (5 + (gateSource l).degrees.proofLog)
    (hierarchyPCP l (hierarchyOf hL)).data.coefficient (hierarchyOf hL).coefficient
    (fun N => (hierarchyPCP l (hierarchyOf hL)).data.pcp.nativeWidth N)
    (fun n hn => (hierarchyPCP l (hierarchyOf hL)).data.proofBound n hn)
  refine ⟨N₀, fun N hN => ?_⟩
  have h1 := hN₀ N hN
  have hmono : Ledger.nativeWidth kclk (5 + (gateSource l).degrees.proofLog + 1) N ≤
      Ledger.nativeWidth kclk G.Apad N := by
    unfold Ledger.nativeWidth
    have : 5 + (gateSource l).degrees.proofLog + 1 ≤ G.Apad := by omega
    have := Nat.mul_le_mul_right (Nat.clog 2 (Nat.clog 2 (N ^ (kclk + 2)) + 2)) this
    omega
  show max _ _ = _
  exact max_eq_right (h1.trans hmono)

end NearCubicWires.WireExponent3_5.Transfer
