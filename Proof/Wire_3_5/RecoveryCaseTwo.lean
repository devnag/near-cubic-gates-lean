import Proof.Wire_3_5.RecoveryFamily
import Proof.Wire_3_5.UnionEventual

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.RepairSource NearCubicWires.RepairRepresentation NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.CloseoutWitness
open NearCubicWires.WireExponent3_5.Shared (uMean bitR)

section CaseTwo
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B}
variable (S : UnionSetup I) {N : ℕ} (z : BitInput N) (oracle : BooleanCircuit (S.pcp.nativeWidth N)) (m : Mode)

/-- The ledger's conditions at the request's width `q` that `exists_unionAccepts` reads, for atoms within the wire
cap `W` and the description cap `Ldesc` (the Case-2 family's limits), at mass bound `A`. -/
structure CaseTwoLedger (P : FusedPrimitive I) (cparams : MaskedCompletenessParameters S.params) (A : ℚ)
    (W Ldesc : ℕ) where
  hA : (A : ℝ) ≤ (S.gridMass (S.request z oracle).arity : ℝ)
  hΛ : 1 ≤ (S.gridMass (S.request z oracle).arity : ℝ)
  hs : 1 ≤ S.gridSize (S.request z oracle).arity
  hsδ : 19 * (S.gridMass (S.request z oracle).arity : ℝ) ^ 4 ≤
    (S.gridSize (S.request z oracle).arity : ℝ) ^ 2 * (cparams.δ : ℝ) ^ 4
  hStar : I.StarAt (S.request z oracle).arity
  hFit : B.FitsAt (S.request z oracle).arity
  hname : 2 ≤ I.nameCount
  hdesc : Ldesc ≤ ((S.request z oracle).arity + 1) ^ I.descDeg
  hdescK : m.descriptionBits (S.constAtom m (S.request z oracle).arity) ≤ ((S.request z oracle).arity + 1) ^ I.descDeg
  hdescP : ∀ Sp, m.descriptionBits (S.parityAtom m (S.request z oracle).arity Sp) ≤
    ((S.request z oracle).arity + 1) ^ I.descDeg
  hKP : ∀ Sp, (m.gates (S.parityAtom m (S.request z oracle).arity Sp)).length ≤ W
  hlen : (S.gridSize (S.request z oracle).arity + 1) * W ≤ ((S.request z oracle).arity + 1) ^ I.carrierDeg
  hbC : Ldesc ≤ ((S.request z oracle).arity + 1) ^ I.carrierDeg
  hbP : ∀ Sp, ∀ gt ∈ m.gates (S.parityAtom m (S.request z oracle).arity Sp),
    gt.encodingBits ≤ ((S.request z oracle).arity + 1) ^ I.carrierDeg
  Cpar : ℝ
  hCpar : 0 ≤ Cpar
  hwP : ∀ Sp, ((m.gates (S.parityAtom m (S.request z oracle).arity Sp)).wires : ℝ) ≤
    Cpar * ((S.request z oracle).arity : ℝ) ^ 2
  hcap : (I.starParams (S.request z oracle).arity hStar).popRate *
      ((S.gridSize (S.request z oracle).arity : ℝ) * W + Cpar * ((S.request z oracle).arity : ℝ) ^ 2) ≤
    (cparams.β : ℝ) * (B.capOf m (S.request z oracle).arity : ℝ)
  hξ : 1 / (2 : ℝ) ^ (I.filterParams m (S.request z oracle).arity).errExp ≤ (cparams.ξ : ℝ)
  hD : (1 + (S.gridMass (S.request z oracle).arity : ℝ)) ^ 4 *
      ((S.request z oracle).arity : ℝ) ^ (-(I.D : ℝ)) ≤ (S.params.eps0 : ℝ)
  Ko : ℕ
  Ks : ℕ
  Kc : ℕ
  hO : (natWord (ExecutableInterfaces.encodeBooleanCircuit oracle)).length ≤ Ko
  hKs : ∀ σ ∈ ({-1, 0, 1} : Finset ℤ), (intWord σ).length ≤ Ks
  hcodeC : ∀ C : m.Circuit (S.request z oracle).arity, m.descriptionBits C ≤ Ldesc → (natWord (m.code C)).length ≤ Kc
  hcodeK : (natWord (m.code (S.constAtom m (S.request z oracle).arity))).length ≤ Kc
  hbudget : 1 + Ko + ((S.pcppOf z oracle).systematicBits + (S.pcppOf z oracle).auxiliaryBits) *
    (S.gridSize (S.request z oracle).arity * (Ks + Kc)) ≤ N / 16

/-- **An accepting guess from the averaged approximate sum** (D1.1 + `exists_unionAccepts`): an occurrence-averaged
family (`[0,1]`-valued, honest error `≤ ζ`, mass `≤ A`, wires `≤ W`, descriptions `≤ Ldesc`) at a tautological
substituted circuit, under the ledger's conditions at `q`, gives a guess the union machine accepts. -/
theorem exists_unionAccepts_of_family (P : FusedPrimitive I) (cparams : MaskedCompletenessParameters S.params)
    (hsize : oracle.size ≤ RecoveryScheduleEnvelope.oracleSizeBound S.G (S.pcp.nativeWidth N))
    (htaut : ∀ x, (S.request z oracle).circuit.eval x = true) (spectrum : ExpanderSpectrumContract)
    {Jc Bc Dc W Ldesc : ℕ} {A : ℚ}
    (family : SumFamily m.Circuit (fun C => modeWireCount m C) (fun C => m.descriptionBits C)
      (Average.limits (S.request z oracle).arity Jc Bc Dc A W Ldesc)
      ((S.pcppOf z oracle).systematicBits + (S.pcppOf z oracle).auxiliaryBits))
    (hu : ∀ u X, 0 ≤ family.value (fun C x => m.eval C x) u X ∧ family.value (fun C x => m.eval C x) u X ≤ 1)
    (herr : CompetitorSourceAverage.honestError S.pcppAlg (S.request z oracle)
      (family.value (fun C x => m.eval C x)) ≤ (cparams.ζ : ℝ))
    (led : CaseTwoLedger S z oracle m P cparams A W Ldesc) :
    ∃ g : UnionGuess S z, UnionAccepts S P z g := by
  have happrox := (approx_eq_honestError S.pcppAlg (S.request z oracle)
    (family.value (fun C x => m.eval C x))).trans_le herr
  simp only [famValue_eq] at happrox
  exact exists_unionAccepts S z oracle m P cparams hsize htaut (J := fun X => Fin (famTerms family X).length)
    (famAtom family) (famCoeff family) (famT_mem family hu) happrox
    (fun X => (famMass_le family X).trans led.hA) led.hΛ led.hs led.hsδ led.hStar led.hFit led.hname
    (fun X j => (famAtom_descriptionBits_le family X j).trans led.hdesc) led.hdescK led.hdescP W
    (famAtom_gates_length_le family) led.hKP led.hlen
    (fun X j gt hgt => (famAtom_gate_encodingBits_le family X j gt hgt).trans led.hbC) led.hbP
    (W : ℝ) led.Cpar (Nat.cast_nonneg W) led.hCpar
    (fun X j => by
      have h1 := wires_le_wireCount m (famAtom family X j)
      have h2 := famAtom_wireCount_le family X j
      exact_mod_cast h1.trans h2) led.hwP led.hcap spectrum led.hξ led.hD led.Ko led.Ks led.Kc led.hO led.hKs
    (fun X j => led.hcodeC _ (famAtom_descriptionBits_le family X j)) led.hcodeK led.hbudget

open NearCubicWires.RepairSource.CloseoutSampledWitness (symmetric_family threshold_family massCap symmetricLimits
  thresholdLimits)
open NearCubicWires.ComponentwiseCircuitRestriction (restrictedSymmetricDescriptionCap
  restrictedThresholdDescriptionCap)
open NearCubicWires.RecoveryWitnessPolicy (symmetricDescriptionCap thresholdDescriptionCap)
open NearCubicWires.CircuitRestriction (symmetricWireFamily thresholdWireFamily)

/-- **Case 2, `SYM∘THR`**: at an input the machine rejects although every accepting guess would make it accept, the
padded honest table has no `SYM∘THR` approximate sum (`SampledXorSum symmetricWireFamily`). -/
theorem no_sampled_sym (normalization : ThresholdNormalizationContract) (spectrum : ExpanderSpectrumContract)
    (P : FusedPrimitive I) (cparams : MaskedCompletenessParameters S.params) (M : OrdinaryWeakMachine)
    (hacc : ∀ g : UnionGuess S z, UnionAccepts S P z g → M.accepts N z) (hrej : ¬ M.accepts N z)
    (hsize : oracle.size ≤ RecoveryScheduleEnvelope.oracleSizeBound S.G (S.pcp.nativeWidth N))
    (htaut : ∀ x, (S.request z oracle).circuit.eval x = true)
    (r copies W : ℕ) (hr : (S.pcppOf z oracle).clauseBits ≤ r) (δ : ℚ) (hd : 0 < δ) (hh : δ < 1 / 2)
    (hδζ : (δ : ℝ) ≤ cparams.ζ)
    (led : CaseTwoLedger S z oracle .sym P cparams (massCap δ copies) W
      (restrictedSymmetricDescriptionCap (S.request z oracle).arity ((S.request z oracle).arity + r + 1)
        (2 ^ symmetricDescriptionCap ((S.request z oracle).arity + r + 1) W) W)) :
    SampledXorSum symmetricWireFamily δ ((S.request z oracle).arity + r + 1) copies W
      (CloseoutLanguage.paddedUnsigned (S.pcppOf z oracle) hr) → False := by
  intro sample
  obtain ⟨family, herr, hu⟩ := symmetric_family normalization S.pcppAlg (S.request z oracle) r copies W hr δ hd hh
    sample
  obtain ⟨g, hg⟩ := exists_unionAccepts_of_family S z oracle .sym P cparams hsize htaut spectrum family hu
    (herr.trans hδζ) led
  exact hrej (hacc g hg)

/-- **Case 2, `THR∘THR`**: the same for `thresholdWireFamily`. -/
theorem no_sampled_thr (normalization : ThresholdNormalizationContract) (spectrum : ExpanderSpectrumContract)
    (P : FusedPrimitive I) (cparams : MaskedCompletenessParameters S.params) (M : OrdinaryWeakMachine)
    (hacc : ∀ g : UnionGuess S z, UnionAccepts S P z g → M.accepts N z) (hrej : ¬ M.accepts N z)
    (hsize : oracle.size ≤ RecoveryScheduleEnvelope.oracleSizeBound S.G (S.pcp.nativeWidth N))
    (htaut : ∀ x, (S.request z oracle).circuit.eval x = true)
    (r copies W : ℕ) (hr : (S.pcppOf z oracle).clauseBits ≤ r) (δ : ℚ) (hd : 0 < δ) (hh : δ < 1 / 2)
    (hδζ : (δ : ℝ) ≤ cparams.ζ)
    (led : CaseTwoLedger S z oracle .thr P cparams (massCap δ copies) W
      (restrictedThresholdDescriptionCap (S.request z oracle).arity ((S.request z oracle).arity + r + 1)
        (2 ^ thresholdDescriptionCap ((S.request z oracle).arity + r + 1) W)
        (thresholdDescriptionCap ((S.request z oracle).arity + r + 1) W))) :
    SampledXorSum thresholdWireFamily δ ((S.request z oracle).arity + r + 1) copies W
      (CloseoutLanguage.paddedUnsigned (S.pcppOf z oracle) hr) → False := by
  intro sample
  obtain ⟨family, herr, hu⟩ := threshold_family normalization S.pcppAlg (S.request z oracle) r copies W hr δ hd hh
    sample
  obtain ⟨g, hg⟩ := exists_unionAccepts_of_family S z oracle .thr P cparams hsize htaut spectrum family hu
    (herr.trans hδζ) led
  exact hrej (hacc g hg)

end CaseTwo

end NearCubicWires.WireExponent3_5.Transfer
