import Proof.SourceAssembly.RawLayout
import Proof.Assembly.RowAdapter

/-! Admitted-request numeric feasibility, step 9: an actual `Packets.Layout` for
the admitted SYM family.

`layoutOf` (`Proof/CaseAnalysis/FiveNativeResources.lean`) is restated here as
`layoutOfNumeric` because that module is not on this seed; the construction is
the accepted one, `C` dropped because `Layout.C` is unconstrained.  Every
numeric premise is discharged from `admitted_layout_sym`, `Geometry.touch` and
`Geometry.card`. -/
namespace NearCubicWires.Admission.Raw
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutRawRows
open CanonicalFourfoldRowProgram SupplierPipeline SupplierEstimator SupplierCapacity
open SupplierListPolynomial SupplierListSchedule SupplierWalkBridge SupplierTouching
open RepairOrdinary.CloseoutRowsRawLogShape RepairRepresentation
open FixedLivePackets
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem normalizedLiveCount_le_liveScale (q kappa : ℕ) :
    normalizedLiveCount q kappa ≤ kappa*logScale q := Nat.min_le_right _ _

/-- The accepted numeric Layout constructor. -/
def layoutOfNumeric {q L : ℕ} (a : DecompositionAlgorithm) (F : Packets.Family q L)
    (g : Packets.Geometry F) (ell w D C : ℕ)
    (ha : Packets.alphabet a F ≤ 2^ell) (hd : ∀ row ∈ F.rows, row.degree ≤ D)
    (hw : D*ell < w) (hs : 67 ≤ Packets.residual F)
    (hl : 200*(normalizedLiveCount q L+w*(normalizedLiveCount q L+2)) ≤ Packets.residual F) :
    Packets.Layout a F g where
  w := w
  degree := D
  C := C
  residualLarge := hs
  positiveWidth := by omega
  degreeBound := hd
  widthFromTouch := by
    intro _ row hrow
    calc
      (Packets.alphabet a F)^row.degree ≤ (2^ell)^row.degree := Nat.pow_le_pow_left ha _
      _ = 2^(ell*row.degree) := by rw [pow_mul]
      _ ≤ 2^(D*ell) := Nat.pow_le_pow_right (by decide) (by nlinarith [hd row hrow])
      _ < 2^w := Nat.pow_lt_pow_right (by decide) hw
  load := hl

/-- Every printed SYM row carries the same degree: `circuits.length` copies of
the accepted `Packets.coordinateDegree`. -/
theorem symFamily_row_degree (r : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (L target : ℕ) (row : Packets.Row (Packets.symFamily r L target).occurrences L)
    (hrow : row ∈ (Packets.symFamily r L target).rows) :
    row.degree = r.circuits.length *
      Packets.coordinateDegree (symmetricFourfoldOccurrences r)
        (Packets.live (Packets.symFamily r L target))
        (symmetricListDenominator r target) := by
  obtain ⟨e,_,hmem⟩ := List.mem_flatMap.mp hrow
  obtain ⟨off,_,heq⟩ := List.mem_map.mp hmem
  rw [← heq]
  rfl

theorem admitted_symLayout (target ce kappa copies : ℕ) (hcopies : 0 < copies) :
    ∃ den0 onset : ℕ, ∀ den : ℕ, den0 ≤ den →
      ∀ (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedSymmetricThresholdCircuit)
        (ell C : ℕ) (g : Packets.Geometry (Packets.symFamily r kappa target)),
      onset ≤ r.q →
      r.circuits.length ≤ 4 →
      Packets.alphabet a (Packets.symFamily r kappa target) ≤ 2^ell →
      ell+1 ≤ (ce+1)*logScale r.q →
      (∀ c∈r.circuits, c.wireCount ≤
        max (r.q*(r.q+1)) (copies*⌊wireScale (1/(den : ℝ)) 5 r.q⌋₊)) →
      ∃ layout : Packets.Layout a (Packets.symFamily r kappa target) g, layout.C = C ∧
        layout.w = rowWidth r.circuits.length (canonicalWalkLength (symmetricListDenominator r target))
          (windowSumAt (symmetricFourfoldOccurrences r) (Packets.live (Packets.symFamily r kappa target)))
          (rowDepthAt (symmetricFourfoldOccurrences r) (Packets.live (Packets.symFamily r kappa target)))
          ell ell := by
  obtain ⟨den0,onset,h⟩ :=
    admitted_layout_sym (canonicalWalkLength (4*(target+1))) ce kappa copies hcopies
  refine ⟨den0,onset,?_⟩
  intro den hden a r ell C g hq hfour ha he hw
  obtain ⟨_,hlt,hres,hload⟩ := h den hden r (Packets.live (Packets.symFamily r kappa target))
    (symmetricListDenominator r target) ell (normalizedLiveCount r.q kappa) hq hfour
    (symmetric_walk_constant target r hfour) he
    (normalizedLiveCount_le_liveScale r.q kappa) g.touch hw
  exact ⟨layoutOfNumeric a (Packets.symFamily r kappa target) g ell _
    (r.circuits.length * Packets.coordinateDegree (symmetricFourfoldOccurrences r)
      (Packets.live (Packets.symFamily r kappa target)) (symmetricListDenominator r target)) C
    ha (fun row hrow => le_of_eq (symFamily_row_degree r kappa target row hrow)) hlt hres hload,
    rfl,rfl⟩

/-- Every printed THR row's degree is under `modulusDigitCount cutoff` copies of
the accepted `Packets.coordinateDegree`: the printed modulus is a prime at most
the cutoff, and `modulusDigitCount` is monotone. -/
theorem thrFamily_row_degree (a : DecompositionAlgorithm)
    (r : FourfoldRequest NormalizedThresholdThresholdCircuit) (L target : ℕ)
    (row : Packets.Row (Packets.thrFamily a r L target).occurrences L)
    (hrow : row ∈ (Packets.thrFamily a r L target).rows) :
    row.degree ≤
      modulusDigitCount (RepairOrdinary.CloseoutFinalC10ThresholdRows.primeCutoff a r target) *
        Packets.coordinateDegree (thresholdFourfoldOccurrences r)
          (Packets.live (Packets.thrFamily a r L target))
          (RepairOrdinary.CloseoutFinalC10ThresholdRows.listDenominator a r target) := by
  obtain ⟨sel,_,h1⟩ := List.mem_flatMap.mp hrow
  obtain ⟨prime,_,h2⟩ := List.mem_flatMap.mp h1
  obtain ⟨e,_,h3⟩ := List.mem_flatMap.mp h2
  obtain ⟨off,_,heq⟩ := List.mem_map.mp h3
  rw [← heq]
  exact Nat.mul_le_mul_right _
    (Nat.succ_le_succ (Nat.log_mono_right (SupplierPrime.mem_primesUpTo.mp prime.property).2))

theorem admitted_thrLayout (cz ct ce kappa copies : ℕ) (hcopies : 0 < copies) :
    ∃ den0 onset : ℕ, ∀ den : ℕ, den0 ≤ den →
      ∀ (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
        (target ell C : ℕ) (g : Packets.Geometry (Packets.thrFamily a r kappa target)),
      onset ≤ r.q →
      r.circuits.length ≤ 4 →
      modulusDigitCount (RepairOrdinary.CloseoutFinalC10ThresholdRows.primeCutoff a r target)+1 ≤
        (cz+1)*logScale r.q →
      canonicalWalkLength
        (RepairOrdinary.CloseoutFinalC10ThresholdRows.listDenominator a r target)+1 ≤
        (ct+1)*logScale r.q →
      Packets.alphabet a (Packets.thrFamily a r kappa target) ≤ 2^ell →
      ell+1 ≤ (ce+1)*logScale r.q →
      (∀ c∈r.circuits, c.wireCount ≤
        max (r.q*(r.q+1)) (copies*⌊wireScale (1/(den : ℝ)) 9 r.q⌋₊)) →
      ∃ layout : Packets.Layout a (Packets.thrFamily a r kappa target) g, layout.C = C ∧
        layout.w = rowWidth
          (modulusDigitCount (RepairOrdinary.CloseoutFinalC10ThresholdRows.primeCutoff a r target))
          (canonicalWalkLength (RepairOrdinary.CloseoutFinalC10ThresholdRows.listDenominator a r target))
          (windowSumAt (thresholdFourfoldOccurrences r) (Packets.live (Packets.thrFamily a r kappa target)))
          (rowDepthAt (thresholdFourfoldOccurrences r) (Packets.live (Packets.thrFamily a r kappa target)))
          ell ell := by
  obtain ⟨den0,onset,h⟩ := admitted_layout_thr cz ct ce kappa copies hcopies
  refine ⟨den0,onset,?_⟩
  intro den hden a r target ell C g hq hfour hz ht ha he hw
  obtain ⟨_,hlt,hres,hload⟩ := h den hden r (Packets.live (Packets.thrFamily a r kappa target))
    (RepairOrdinary.CloseoutFinalC10ThresholdRows.listDenominator a r target)
    (modulusDigitCount (RepairOrdinary.CloseoutFinalC10ThresholdRows.primeCutoff a r target))
    ell (normalizedLiveCount r.q kappa) hq hfour hz ht he
    (normalizedLiveCount_le_liveScale r.q kappa) g.touch hw
  exact ⟨layoutOfNumeric a (Packets.thrFamily a r kappa target) g ell _
    (modulusDigitCount (RepairOrdinary.CloseoutFinalC10ThresholdRows.primeCutoff a r target) *
      Packets.coordinateDegree (thresholdFourfoldOccurrences r)
        (Packets.live (Packets.thrFamily a r kappa target))
        (RepairOrdinary.CloseoutFinalC10ThresholdRows.listDenominator a r target)) C
    ha (fun row hrow => thrFamily_row_degree a r kappa target row hrow) hlt hres hload,
    rfl,rfl⟩

end
end NearCubicWires.Admission.Raw
