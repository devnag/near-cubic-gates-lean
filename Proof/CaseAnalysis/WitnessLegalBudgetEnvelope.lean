import Proof.CaseAnalysis.WitnessLegalBudgetPolynomial

/-! One finite maximum of actual legal-policy costs is fixed before k.
Its maximizing short parameters satisfy the same polynomial bounds, so the
literal budget theorem proves this uniform envelope polynomial. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.LegalBudget
open PaddedRunnerBudgetClosure BudgetTools
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

abbrev Parameters:=ℕ×ℕ×ℕ×ℕ
def box (S : ℕ) : Finset Parameters :=
  ((Finset.range (S+2)).product ((Finset.range (S+2)).product
    ((Finset.range (S+2)).product (Finset.range (S+2))))).filter (fun p=>2^p.2.2.1≤S+1)
def cost (e den copies : ℕ) (delta : ℚ) (sym : Bool) (p : Parameters) :=
  LegalTemplate.budget e den delta copies sym p.1 p.2.1 p.2.2.1 p.2.2.2
def envelope (e den copies : ℕ) (delta : ℚ) (sym : Bool) (S : ℕ) :=
  (box S).sup (cost e den copies delta sym)

theorem box_nonempty (S : ℕ) : (box S).Nonempty := by
  refine ⟨(0,0,0,0),?_⟩
  simp [box]

theorem box_bounds {S : ℕ} {p : Parameters} (hp:p∈box S) :
    p.1≤S+1 ∧ p.2.1≤S+1 ∧ p.2.2.1≤S+1 ∧ p.2.2.2≤S+1 ∧ 2^p.2.2.1≤S+1 := by
  simp only [box,Finset.mem_filter,Finset.product_eq_sprod,Finset.mem_product,Finset.mem_range] at hp
  omega

theorem budget_le (e den copies : ℕ) (delta : ℚ) (sym : Bool) (S R q cb b : ℕ)
    (hr:R≤S) (hq:q≤S) (hcb:cb≤S) (hb:b≤S) (hc:2^cb≤S) :
    LegalTemplate.budget e den delta copies sym R q cb b≤envelope e den copies delta sym S := by
  apply Finset.le_sup (f:=cost e den copies delta sym) (b:=(R,q,cb,b))
  simp only [box,Finset.mem_filter,Finset.product_eq_sprod,Finset.mem_product,Finset.mem_range]
  omega

theorem envelope_polynomial (e den copies : ℕ) (delta : ℚ) (sym : Bool)
    {S : ℕ→ℕ} (hs:SourcePoly S) : SourcePoly (fun n=>envelope e den copies delta sym (S n)) := by
  let pick (n : ℕ):Parameters:=
    (Finset.exists_mem_eq_sup (box (S n)) (box_nonempty (S n)) (cost e den copies delta sym)).choose
  have chosen (n : ℕ):pick n∈box (S n) ∧ envelope e den copies delta sym (S n)=cost e den copies delta sym (pick n):=
    (Finset.exists_mem_eq_sup (box (S n)) (box_nonempty (S n)) (cost e den copies delta sym)).choose_spec
  have hmax:=hs.add (polyDominated_const 1)
  have hr:SourcePoly (fun n=>(pick n).1):=hmax.mono (fun n=>(box_bounds (chosen n).1).1)
  have hq:SourcePoly (fun n=>(pick n).2.1):=hmax.mono (fun n=>(box_bounds (chosen n).1).2.1)
  have hcb:SourcePoly (fun n=>(pick n).2.2.1):=hmax.mono (fun n=>(box_bounds (chosen n).1).2.2.1)
  have hb:SourcePoly (fun n=>(pick n).2.2.2):=hmax.mono (fun n=>(box_bounds (chosen n).1).2.2.2.1)
  have hc:SourcePoly (fun n=>2^(pick n).2.2.1):=hmax.mono (fun n=>(box_bounds (chosen n).1).2.2.2.2)
  exact (legal hr hq hcb hb hc e den copies delta sym).mono (fun n=>(chosen n).2.le)

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.LegalBudget
