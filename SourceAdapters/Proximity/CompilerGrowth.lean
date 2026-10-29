import SourceAdapters.Proximity.ConstructorGrowth
import Proof.Gates.CellsPack.Lang

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": polynomial cost for the actual physical Cells
compiler, including allocated source calls and the paid input length prefix. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.SourceCallee

open NearCubicWires NearCubicGates.Close.Cells NearCubicGates.Published.CW19Proximity Growth

theorem compiler_budget_bounded (K : Callee) (A D : ℕ) (N : SourceCircuit → ℕ)
    (hN : Bounded sourceMeasure N) :
    Bounded sourceMeasure (fun S => langBudget K (uniformSize A D) VV MM
      (LengthPrefix.wrapped (sourceCircuitWord S)) (N S)) := by
  have halloc := allocation_bounded A D
  have hlead : Bounded sourceMeasure (fun S => leadOnes (LengthPrefix.wrapped (sourceCircuitWord S))) := by
    simpa only [LengthPrefix.wrapped_leadOnes, sourceMeasure] using
      (bounded_size (size := sourceMeasure)).bitLength
  have hG : Bounded sourceMeasure (fun S => NearCubicGates.Close.CellsPack.Gof K (uniformSize A D)
      (leadOnes (LengthPrefix.wrapped (sourceCircuitWord S)))) := by
    exact (((((((((((halloc).add (halloc)).add (halloc)).add (hlead)).add (bounded_const A)).add (bounded_const A)).add (bounded_const A)).add (bounded_const D)).add (bounded_const D)).add (bounded_const D)).add (bounded_const (TSK K))).add (bounded_const 1)
  have hinput : Bounded sourceMeasure (fun S => (LengthPrefix.wrapped (sourceCircuitWord S)).length) :=
    ((bounded_const 3).mul (bounded_size.add (bounded_const 1))).mono
      (fun S => LengthPrefix.wrapped_length_bound (sourceCircuitWord S))
  have hbound := ((bounded_const (10 ^ 6)).mul ((hN.add (bounded_const 1)).mul (hG.pow 2))).add
    ((bounded_const 10).mul hinput)
  exact hbound.mono (fun S => NearCubicGates.Close.CellsPack.lang_le2 K (uniformSize A D)
    (LengthPrefix.wrapped (sourceCircuitWord S)) (N S))

end NearCubicGates.Adapters.Proximity.SourceCallee
