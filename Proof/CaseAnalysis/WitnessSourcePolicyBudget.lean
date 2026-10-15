import Proof.CaseAnalysis.WitnessNativeCacheBudget
import Proof.PCP.PCPPNativeNodeReadBounds
import Proof.CaseAnalysis.ScheduleWidthBudget

/-! The real metadata and coefficient policy costs allow a fixed envelope
over their short input fields. The finite maximum is only a runtime bound. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.SourcePolicy
open PaddedRunnerBudgetClosure BudgetTools RepairSource ProjectionNormalization CloseoutSchedule
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem counts_polynomial {a b cb : ℕ→ℕ} (ha:SourcePoly a) (hb:SourcePoly b) (hc:SourcePoly cb) :
    SourcePoly (fun n=>SourceCounts.budget (a n) (b n) (cb n)) := by
  have upper:SourcePoly (fun n=>256*(a n+b n+cb n+1)^2):=by fast_budget_poly
  have nodes:SourcePoly (fun n=>PCPPNativeNodeRead.budget (a n) (b n) (cb n)):=
    upper.mono (fun n=>PCPPNativeNodeRead.budget_bound (a n) (b n) (cb n))
  dsimp only [SourceCounts.budget,SourceFields.budget,SourceFields.rawBudget]
  fast_budget_poly

theorem core_polynomial {R cb : ℕ→ℕ} (hr:SourcePoly R) (hc:SourcePoly cb)
    (D copies : ℕ) (delta : ℚ) (hD:1≤D) :
    SourcePoly (fun n=>CorePolicy.budget D copies (R n) (cb n) delta) := by
  have q:SourcePoly (fun n=>CorePolicy.q0 D (R n)):=
    ((hr.add (polyDominated_const 1)).const_mul (D+1)).mono
      (fun n=>FamilyResources.core_bound D (R n) (R n) le_rfl)
  have w:SourcePoly (fun n=>Width.budget D 1 (R n)):=by
    have upper:SourcePoly (fun n=>(DimensionPolynomial.coefficient D 1+64*1+900)*(R n+3)^(2*D+2)):=by
      fast_budget_poly
    exact upper.mono (fun n=>Width.budget_bound D 1 (R n) hD)
  have p:=polynomial_cost q (CoefficientBits.factor delta copies) 1
  dsimp only [CorePolicy.budget,CoefficientBits.budget,CoefficientBits.width,DimensionPolynomial.value]
  fast_budget_poly

theorem polynomial {R a b cb : ℕ→ℕ} (hr:SourcePoly R) (ha:SourcePoly a) (hb:SourcePoly b)
    (hc:SourcePoly cb) (D copies : ℕ) (delta : ℚ) (hD:1≤D) :
    SourcePoly (fun n=>budget D copies (R n) (a n) (b n) (cb n) delta) :=
  ((counts_polynomial ha hb hc).add (polyDominated_const 1)).add (core_polynomial hr hc D copies delta hD)

def cost (D copies : ℕ) (delta : ℚ) (p : LegalBudget.Parameters):=
  budget D copies p.1 p.2.1 p.2.2.2 p.2.2.1 delta
def envelope (D copies : ℕ) (delta : ℚ) (S : ℕ):=(LegalBudget.box S).sup (cost D copies delta)

theorem budget_le (D copies R a b cb S : ℕ) (delta : ℚ)
    (hr:R≤S) (ha:a≤S) (hb:b≤S) (hc:cb≤S) (hpow:2^cb≤S) :
    budget D copies R a b cb delta≤envelope D copies delta S := by
  apply Finset.le_sup (f:=cost D copies delta) (b:=(R,a,cb,b))
  simp only [LegalBudget.box,Finset.mem_filter,Finset.product_eq_sprod,Finset.mem_product,Finset.mem_range]
  omega

theorem envelope_polynomial (D copies : ℕ) (delta : ℚ) (hD:1≤D)
    {S : ℕ→ℕ} (hs:SourcePoly S) : SourcePoly (fun n=>envelope D copies delta (S n)) := by
  let pick (n : ℕ):LegalBudget.Parameters:=
    (Finset.exists_mem_eq_sup (LegalBudget.box (S n)) (LegalBudget.box_nonempty (S n)) (cost D copies delta)).choose
  have chosen (n : ℕ):pick n∈LegalBudget.box (S n) ∧ envelope D copies delta (S n)=cost D copies delta (pick n):=
    (Finset.exists_mem_eq_sup (LegalBudget.box (S n)) (LegalBudget.box_nonempty (S n)) (cost D copies delta)).choose_spec
  have hmax:=hs.add (polyDominated_const 1)
  have hr:SourcePoly (fun n=>(pick n).1):=hmax.mono (fun n=>(LegalBudget.box_bounds (chosen n).1).1)
  have ha:SourcePoly (fun n=>(pick n).2.1):=hmax.mono (fun n=>(LegalBudget.box_bounds (chosen n).1).2.1)
  have hc:SourcePoly (fun n=>(pick n).2.2.1):=hmax.mono (fun n=>(LegalBudget.box_bounds (chosen n).1).2.2.1)
  have hb:SourcePoly (fun n=>(pick n).2.2.2):=hmax.mono (fun n=>(LegalBudget.box_bounds (chosen n).1).2.2.2.1)
  exact (polynomial hr ha hb hc D copies delta hD).mono (fun n=>(chosen n).2.le)

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.SourcePolicy
