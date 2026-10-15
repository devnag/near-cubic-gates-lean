import Proof.Wire_3_5.Contracts
import Proof.Wire_3_5.StarSelectionChoice

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.SelectionMachine
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Stars
open NearCubicWires.WireExponent3_5.Machine NearCubicWires.WireExponent3_5.Machine.S0Defs
open NearCubicWires.WireExponent3_5.Cost

def ParamsOk (R : SelectionReq) : Prop := R.r % 2 = 0 ∧ 2 ≤ R.r ∧ 4 * R.r ≤ R.n

instance (R : SelectionReq) : Decidable (ParamsOk R) := by unfold ParamsOk; infer_instance

/-- The star parameters of an admissible request. -/
def starParamsOf (R : SelectionReq) (h : ParamsOk R) : StarParams :=
  ⟨R.n, R.r, Nat.even_iff.mpr h.1, h.2.1, h.2.2⟩

/-- A seed gate as a normalized threshold gate (the same weights and threshold). -/
def gateOf {n : ℕ} (g : IntGate n) : NormalizedThresholdGate n := ⟨g.weights, g.threshold⟩

def popsOf (R : SelectionReq) : List (ℚ × Carrier R.n) :=
  R.pops.map fun X => (X.2, X.1.map fun i => gateOf (R.gates.getD i ⟨fun _ => 0, 0⟩))

/-- The objective of a coset (its codes): `starObjectiveRef` at the translation of the codes. -/
def selObjective (R : SelectionReq) (c : Coset) : ℚ :=
  if h : ParamsOk R then
    (starParamsOf R h).starObjectiveRef ((starParamsOf R h).translationOfCodes c) (popsOf R)
  else 0

/-- The selected coset: `selectCodes`. -/
def selArgmin (R : SelectionReq) : Coset :=
  if h : ParamsOk R then (starParamsOf R h).selectCodes (popsOf R) else []

/-- **The C1 contract at the verified references.** -/
def c1inst (E : Envelope) (encodeCoset : Coset → List Bool) (inputWord : SelectionReq → List Bool)
    (psi : SelectionReq → ℕ) (coef : ℕ) : MachineContract E :=
  c1 E selObjective selArgmin encodeCoset inputWord psi coef

/-- **The error field holds for the reference** on every admissible request (the `Certified.err` field of C1). -/
theorem c1inst_err (E : Envelope) (encodeCoset : Coset → List Bool) (inputWord : SelectionReq → List Bool)
    (psi : SelectionReq → ℕ) (coef : ℕ) :
    ∀ R, (c1inst E encodeCoset inputWord psi coef).pre R →
      (c1inst E encodeCoset inputWord psi coef).errSpec R ((c1inst E encodeCoset inputWord psi coef).ref R) := by
  rintro R ⟨hr, h2, h4, _, _⟩
  have h : ParamsOk R := ⟨hr, h2, h4⟩
  show (selArgmin R).length = R.r ∧ ∀ c' : Coset, c'.length = R.r → (∀ σ ∈ c', σ < 2 ^ R.s) →
    selObjective R (selArgmin R) ≤ selObjective R c'
  unfold selArgmin selObjective
  simp only [dif_pos h]
  refine ⟨(starParamsOf R h).selectCodes_length (popsOf R), fun c' _ _ => ?_⟩
  exact (starParamsOf R h).selectCodes_min (popsOf R) _

end NearCubicWires.WireExponent3_5.SelectionMachine
