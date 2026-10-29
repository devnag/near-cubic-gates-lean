import SourceAdapters.Proximity.AllocationGrowth

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": extract an actual ordinary constructor from the
proved initialized run with a fixed polynomial Cells allocation. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.SourceCallee

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells
open NearCubicGates.Published.CW19Proximity

variable {q : ℕ} (V : (S : SourceCircuit) → NonadaptiveVerifier S.arity q)
    (proofLength : SourceCircuit → ℕ) (honest : (p : AcceptedSourceInput) → BitInput (proofLength p.1))
    (K e : ℕ)
    (P : WordFunction (ProofCall V) (proofCallInput V) (normalizedProofOutput V proofLength honest)
      (fun p => K * ((proofCallInput V p).length + 1) ^ e))

noncomputable def allocatedConstructorWordFunction (a A D : ℕ) (hA : 1 ≤ A)
    (hr : ∀ S, (V S).randomBits ≤ a * Nat.clog 2 (sourceMeasure S + 2))
    (hw : ∀ S, widthDemand q (sourceMeasure S) (V S).randomBits
      (callBudgetCap q a K e (sourceMeasure S)) ≤ allocation A D S)
    (hl : ∀ S, requestCap q a (sourceMeasure S) ≤ allocation A D S)
    (hb : ∀ S, callBudgetCap q a K e (sourceMeasure S) ≤ allocation A D S) :
    WordFunction SourceCircuit (fun S => LengthPrefix.wrapped (sourceCircuitWord S))
      (fun S => Joins.trimRequestWord ⟨S.arity, clauseVerifier (V S)⟩)
      (fun S => langBudget (callee V proofLength honest _ P) (uniformSize A D) VV MM
        (LengthPrefix.wrapped (sourceCircuitWord S))
        (constructorCost V S (allocation A D S) (allocation A D S)
          (widthMeasure q (V S).randomBits (callBudgetCap q a K e (sourceMeasure S))))) :=
  wordFunction_of_lang (V := VV) (M := MM)
    (fun S => LengthPrefix.wrapped (sourceCircuitWord S))
    (fun S => Joins.trimRequestWord ⟨S.arity, clauseVerifier (V S)⟩)
    (callee V proofLength honest _ P) (uniformSize A D) (constructorProgram q 1 2)
    (fun S => constructorCost V S (allocation A D S) (allocation A D S)
      (widthMeasure q (V S).randomBits (callBudgetCap q a K e (sourceMeasure S))))
    (fun S => by
      have H := numerical_constructor V proofLength honest _ P S a
        (callBudgetCap q a K e (sourceMeasure S)) (allocation A D S) (allocation A D S) (allocation A D S)
        (random_linear V a hr S) (fun p hp => budget_below_cap V a K e (sourceMeasure S) p hp)
        (hl S) (hb S) (hw S)
      obtain ⟨b, cost, he, hcost, hout⟩ := constructor_run V proofLength honest _ P S
        (allocation A D S) (allocation A D S) (allocation A D S)
        (widthMeasure q (V S).randomBits (callBudgetCap q a K e (sourceMeasure S))) 1 2 (by decide) H
      refine ⟨b, cost, ?_, hout, hcost⟩
      simpa only [ctxOf, uniformSize, Sz.W, Sz.Lk, Sz.Bk, allocation, context,
        LengthPrefix.wrapped, List.append_nil] using he)
    (fun S => by
      simpa only [ctxOf, uniformSize, Sz.W, allocation] using allocation_positive A D hA S)

end NearCubicGates.Adapters.Proximity.SourceCallee
