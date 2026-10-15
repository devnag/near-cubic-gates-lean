import Proof.SourceAssembly.RawCaps

/-! Admitted-request numeric feasibility, steps 1-2: the occurrence population
and the active-set cap at the actual decoded wire cap.

`thm:supplier-fixed` (`paper.tex:721-733`) gives a call at most four normalized
`q`-input SYMTHR circuits subject to `W(C_i) ≤ a^fix q^3/L_q^5`; the THR branch
is the same statement at `L_q^9`.  Both caps here are the decoded ones, taken
componentwise (`paper.tex:1320-1324`) with the parity atom's own wire count
folded in by `max`.  The SYM parity atom carries `2*|support| ≤ q*(q+1)` wires
and the THR parity atom `|support|*(|support|+1) ≤ q*(q+1)`, so one `max` term
serves both modes. -/
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

/-- One arity onset makes every admitted atom — carried or parity — satisfy the
paper cap at the coefficient `paperCap A κ` that the margin will consume. -/
theorem admitted_caps_eventual (e A kappa copies den : ℕ) (hcopies : 0 < copies)
    (hden : copies*capDenominator A kappa ≤ den) :
    ∃ onset, ∀ q, onset ≤ q → ∀ w : ℕ,
      w ≤ max (q*(q+1)) (copies*⌊wireScale (1/(den : ℝ)) e q⌋₊) →
      (w : ℝ) ≤ wireScale (paperCap A kappa) e q := by
  have hcap : 0 < capDenominator A kappa := by unfold capDenominator; positivity
  obtain ⟨n₀,h₀⟩ := parity_wire_eventual e (capDenominator A kappa) hcap
  refine ⟨n₀,?_⟩
  intro q hq w hw
  exact admitted_wire_cap q e copies den A kappa w hcopies hden (h₀ q hq) hw

theorem admitted_population_sym (r : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (A kappa copies den : ℕ) (hcopies : 0 < copies)
    (hden : copies*capDenominator A kappa ≤ den)
    (hfour : r.circuits.length ≤ 4)
    (hpar : ((r.q*(r.q+1) : ℕ) : ℝ) ≤ wireScale (paperCap A kappa) 5 r.q)
    (hw : ∀ c∈r.circuits, c.wireCount ≤
      max (r.q*(r.q+1)) (copies*⌊wireScale (1/(den : ℝ)) 5 r.q⌋₊)) :
    (symmetricFourfoldOccurrences r).length ≤ 4*r.q^3 :=
  symmetric_population r 5 (paperCap A kappa) (paperCap_le_one A kappa) hfour
    (fun c hc => admitted_wire_cap r.q 5 copies den A kappa c.wireCount hcopies hden hpar (hw c hc))

theorem admitted_population_thr (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (A kappa copies den : ℕ) (hcopies : 0 < copies)
    (hden : copies*capDenominator A kappa ≤ den)
    (hfour : r.circuits.length ≤ 4)
    (hpar : ((r.q*(r.q+1) : ℕ) : ℝ) ≤ wireScale (paperCap A kappa) 9 r.q)
    (hw : ∀ c∈r.circuits, c.wireCount ≤
      max (r.q*(r.q+1)) (copies*⌊wireScale (1/(den : ℝ)) 9 r.q⌋₊)) :
    (thresholdFourfoldOccurrences r).length ≤ 4*r.q^3 :=
  threshold_population r 9 (paperCap A kappa) (paperCap_le_one A kappa) hfour
    (fun c hc => admitted_wire_cap r.q 9 copies den A kappa c.wireCount hcopies hden hpar (hw c hc))

theorem admitted_active_sym (r : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (I : Finset (Fin r.q)) (A kappa copies den : ℕ) (hcopies : 0 < copies)
    (hden : copies*capDenominator A kappa ≤ den) (hq : 0 < r.q)
    (hfour : r.circuits.length ≤ 4)
    (hpar : ((r.q*(r.q+1) : ℕ) : ℝ) ≤ wireScale (paperCap A kappa) 5 r.q)
    (htouch : r.q * touchingCost (occurrenceSupport (symmetricFourfoldOccurrences r)) I ≤
      normalizedLiveCount r.q kappa *
        supportIncidenceMass (occurrenceSupport (symmetricFourfoldOccurrences r)))
    (hw : ∀ c∈r.circuits, c.wireCount ≤
      max (r.q*(r.q+1)) (copies*⌊wireScale (1/(den : ℝ)) 5 r.q⌋₊)) :
    (touchingCost (occurrenceSupport (symmetricFourfoldOccurrences r)) I : ℝ)*
        (logScale r.q : ℝ)^4 ≤ 4*kappa*paperCap A kappa*(r.q : ℝ)^2 :=
  symmetric_active_cap_of_touch r I kappa (paperCap A kappa)
    (le_of_lt (paperCap_positive A kappa)) hq hfour htouch
    (fun c hc => admitted_wire_cap r.q 5 copies den A kappa c.wireCount hcopies hden hpar (hw c hc))

theorem admitted_active_thr (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (I : Finset (Fin r.q)) (A kappa copies den : ℕ) (hcopies : 0 < copies)
    (hden : copies*capDenominator A kappa ≤ den) (hq : 0 < r.q)
    (hfour : r.circuits.length ≤ 4)
    (hpar : ((r.q*(r.q+1) : ℕ) : ℝ) ≤ wireScale (paperCap A kappa) 9 r.q)
    (htouch : r.q * touchingCost (occurrenceSupport (thresholdFourfoldOccurrences r)) I ≤
      normalizedLiveCount r.q kappa *
        supportIncidenceMass (occurrenceSupport (thresholdFourfoldOccurrences r)))
    (hw : ∀ c∈r.circuits, c.wireCount ≤
      max (r.q*(r.q+1)) (copies*⌊wireScale (1/(den : ℝ)) 9 r.q⌋₊)) :
    (touchingCost (occurrenceSupport (thresholdFourfoldOccurrences r)) I : ℝ)*
        (logScale r.q : ℝ)^8 ≤ 4*kappa*paperCap A kappa*(r.q : ℝ)^2 :=
  threshold_active_cap_of_touch r I kappa (paperCap A kappa)
    (le_of_lt (paperCap_positive A kappa)) hq hfour htouch
    (fun c hc => admitted_wire_cap r.q 9 copies den A kappa c.wireCount hcopies hden hpar (hw c hc))

end
end NearCubicWires.Admission.Raw
