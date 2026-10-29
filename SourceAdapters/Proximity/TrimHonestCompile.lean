import SourceAdapters.Proximity.TrimHonestRun

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": compile the complete initialized honest producer with
one allocation obtained from the physically read input-length prefix. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.TrimHonest
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells
open NearCubicGates.Published.CW19Proximity NearCubicGates.Adapters.Joins

variable {q : ℕ} (V : (S : SourceCircuit) → NonadaptiveVerifier S.arity q)
    (proofSize : SourceCircuit → ℕ)
    (honest : (p : AcceptedSourceInput) → BitInput (proofSize p.1)) (K e a : ℕ)
    (P : WordFunction (ProofCall V) (proofCallInput V) (normalizedProofOutput V proofSize honest)
      (fun r => K * ((proofCallInput V r).length + 1) ^ e))

noncomputable def allocatedWordFunction (A D : ℕ) (hA : 1 ≤ A)
    (H : ∀ p, HonestFullAllocation.AllBounds V proofSize honest K e a p
      (HonestAllocation.allocation (preparedHonestInput V) A D p)
      (HonestAllocation.allocation (preparedHonestInput V) A D p)
      (HonestAllocation.allocation (preparedHonestInput V) A D p)) :
    WordFunction AcceptedSourceInput (fun p => LengthPrefix.wrapped (preparedHonestInput V p))
      (preparedHonestOutput V proofSize honest)
      (fun p => langBudget (SourceCallee.callee V proofSize honest _ P) (SourceCallee.uniformSize A D) VV MM
        (LengthPrefix.wrapped (preparedHonestInput V p))
        (HonestFullAllocation.cost V proofSize K e a p
          (HonestAllocation.allocation (preparedHonestInput V) A D p)
          (HonestAllocation.allocation (preparedHonestInput V) A D p))) :=
  wordFunction_of_lang (Req := AcceptedSourceInput) (V := VV) (M := MM)
    (fun p => LengthPrefix.wrapped (preparedHonestInput V p)) (preparedHonestOutput V proofSize honest)
    (SourceCallee.callee V proofSize honest _ P) (SourceCallee.uniformSize A D) (fullProgram q)
    (fun p => HonestFullAllocation.cost V proofSize K e a p
      (HonestAllocation.allocation (preparedHonestInput V) A D p)
      (HonestAllocation.allocation (preparedHonestInput V) A D p))
    (fun p => by
      obtain ⟨b, cost, he, hcost, hout⟩ := full_run V proofSize honest K e a P p
        (HonestAllocation.allocation (preparedHonestInput V) A D p)
        (HonestAllocation.allocation (preparedHonestInput V) A D p)
        (HonestAllocation.allocation (preparedHonestInput V) A D p) (H p)
      refine ⟨b, cost, ?_, hout, hcost⟩
      simpa only [ctxOf, SourceCallee.uniformSize, Sz.W, Sz.Lk, Sz.Bk,
        HonestAllocation.allocation, SourceCallee.context] using he)
    (fun p => by
      simpa only [ctxOf, SourceCallee.uniformSize, Sz.W, HonestAllocation.allocation] using
        HonestAllocation.positive (preparedHonestInput V) A D hA p)

end NearCubicGates.Adapters.Proximity.TrimHonest
