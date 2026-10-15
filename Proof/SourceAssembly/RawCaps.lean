import Proof.CaseAnalysis.FiveLiveSetCaps
import Proof.CaseAnalysis.RawRowsModeBounds

/-! Admitted-request numeric feasibility, step 1: the decoded per-atom wire cap.

`paper.tex:1320-1324` imposes the wire cap COMPONENTWISE on each atom and
forbids charging a sum of atom wires to a call, so the decoded cap enters here
as a per-circuit bound and the independently compiled parity atom enters
through a `max`, never through a sum.  The decoded cap is the natural-number
floor `copies*⌊wireScale (1/den) e q⌋₊`; the paper's coefficient `paperCap A κ`
is chosen AFTER the shape constants, which is why `den` is free. -/
namespace NearCubicWires.Admission.Raw
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutRawRows
open CanonicalFourfoldRowProgram SupplierPipeline SupplierEstimator SupplierCapacity
open SupplierListPolynomial SupplierListSchedule SupplierWalkBridge SupplierTouching
open RepairOrdinary.CloseoutRowsRawLogShape
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

/-- Converse of `wireScale_cap`: the cap in product form implies the quotient form. -/
theorem wireScale_of_cap (q e : ℕ) (a : ℝ) (w : ℕ)
    (h : (w : ℝ)*(logScale q : ℝ)^e ≤ a*(q : ℝ)^3) :
    (w : ℝ) ≤ wireScale a e q := by
  have hl : (0 : ℝ) < logScale q := by exact_mod_cast logScale_pos q
  unfold wireScale
  exact (le_div_iff₀ (pow_pos hl e)).mpr h

/-- The decoded natural cap `copies*⌊wireScale (1/den) e q⌋₊` is at most the real
cap at coefficient `copies/den`. -/
theorem cap_of_floor (q e copies den w : ℕ) (hden : 0 < den)
    (hw : w ≤ copies*⌊wireScale (1/(den : ℝ)) e q⌋₊) :
    (w : ℝ) ≤ wireScale ((copies : ℝ)/(den : ℝ)) e q := by
  have hdR : (0 : ℝ) < den := by exact_mod_cast hden
  have hl : (0 : ℝ) < logScale q := by exact_mod_cast logScale_pos q
  have hpos : (0 : ℝ) ≤ wireScale (1/(den : ℝ)) e q := by
    unfold wireScale
    positivity
  have hfloor : (⌊wireScale (1/(den : ℝ)) e q⌋₊ : ℝ) ≤ wireScale (1/(den : ℝ)) e q :=
    Nat.floor_le hpos
  have hwR : (w : ℝ) ≤ (copies : ℝ)*(⌊wireScale (1/(den : ℝ)) e q⌋₊ : ℝ) := by
    exact_mod_cast hw
  have hmul : (copies : ℝ)*(⌊wireScale (1/(den : ℝ)) e q⌋₊ : ℝ) ≤
      (copies : ℝ)*wireScale (1/(den : ℝ)) e q :=
    mul_le_mul_of_nonneg_left hfloor (Nat.cast_nonneg copies)
  have hid : (copies : ℝ)*wireScale (1/(den : ℝ)) e q =
      wireScale ((copies : ℝ)/(den : ℝ)) e q := by
    unfold wireScale
    field_simp
  linarith [hwR.trans hmul, hid.le, hid.ge]

/-- The wire denominator is chosen after the shape constants: any `den` beyond
`copies*capDenominator A κ` puts the decoded cap under the paper coefficient. -/
theorem cap_le_paperCap (q e copies den A kappa w : ℕ) (hcopies : 0 < copies)
    (hden : copies*capDenominator A kappa ≤ den)
    (hw : w ≤ copies*⌊wireScale (1/(den : ℝ)) e q⌋₊) :
    (w : ℝ) ≤ wireScale (paperCap A kappa) e q := by
  have hcap : 0 < capDenominator A kappa := by unfold capDenominator; positivity
  have hden0 : 0 < den := lt_of_lt_of_le (Nat.mul_pos hcopies hcap) hden
  have hdR : (0 : ℝ) < den := by exact_mod_cast hden0
  have hcapR : (0 : ℝ) < capDenominator A kappa := by exact_mod_cast hcap
  have hcoef : (copies : ℝ)/(den : ℝ) ≤ paperCap A kappa := by
    unfold paperCap
    rw [div_le_div_iff₀ hdR hcapR, one_mul]
    have := (Nat.cast_le (α := ℝ)).mpr hden
    push_cast at this
    linarith
  exact (cap_of_floor q e copies den w hden0 hw).trans
    (wireScale_mono_coefficient hcoef e q)

/-- The independently compiled parity atom carries `q*(q+1)` wires; it fits under
the paper coefficient from one arity onset, with no sum of atom caps. -/
theorem parity_wire_eventual (e c : ℕ) (hc : 0 < c) :
    ∃ onset, ∀ q, onset ≤ q → ((q*(q+1) : ℕ) : ℝ) ≤ wireScale (1/(c : ℝ)) e q := by
  obtain ⟨n₀,h₀⟩ := coefficient_mul_logScale_pow_eventually_le (2*c) e
  refine ⟨max 1 n₀,?_⟩
  intro q hq
  have h1 : 1 ≤ q := le_trans (Nat.le_max_left _ _) hq
  have h2 : 2*c*(logScale q)^e ≤ q := h₀ q (le_trans (Nat.le_max_right _ _) hq)
  have hstep : q+1 ≤ 2*q := by omega
  have hnat : c*(q*(q+1))*(logScale q)^e ≤ q^3 := by
    calc c*(q*(q+1))*(logScale q)^e ≤ c*(q*(2*q))*(logScale q)^e :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left c (Nat.mul_le_mul_left q hstep))
      _ = (q*q)*(2*c*(logScale q)^e) := by ring
      _ ≤ (q*q)*q := Nat.mul_le_mul_left _ h2
      _ = q^3 := by ring
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hnatR : (c : ℝ)*((q : ℝ)*((q : ℝ)+1))*(logScale q : ℝ)^e ≤ (q : ℝ)^3 := by
    exact_mod_cast hnat
  apply wireScale_of_cap
  have hrw : (1/(c : ℝ))*(q : ℝ)^3 = (q : ℝ)^3/(c : ℝ) := by ring
  rw [hrw, le_div_iff₀ hcR]
  push_cast
  nlinarith only [hnatR]

/-- The full admitted per-atom cap: the decoded floor cap on carried atoms, the
parity atom's own wire count on the systematic ones, combined by `max`. -/
theorem admitted_wire_cap (q e copies den A kappa w : ℕ) (hcopies : 0 < copies)
    (hden : copies*capDenominator A kappa ≤ den)
    (hpar : ((q*(q+1) : ℕ) : ℝ) ≤ wireScale (paperCap A kappa) e q)
    (hw : w ≤ max (q*(q+1)) (copies*⌊wireScale (1/(den : ℝ)) e q⌋₊)) :
    (w : ℝ) ≤ wireScale (paperCap A kappa) e q := by
  rcases Nat.le_total w (q*(q+1)) with h | h
  · exact le_trans (by exact_mod_cast h) hpar
  · rcases le_max_iff.mp hw with h' | h'
    · exact le_trans (by exact_mod_cast h') hpar
    · exact cap_le_paperCap q e copies den A kappa w hcopies hden h'

end
end NearCubicWires.Admission.Raw
