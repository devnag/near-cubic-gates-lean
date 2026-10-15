import Proof.Wire_3_5.UnionMachineFiltSetupIface5

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.BudgetIface
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Filters

/-- **The FILTER pipeline's cost bound, v2** (C6b): polynomial in every parameter, times `(L+2)^{D_f(e+1)}` in the
slice length `L` only, uniformly in the seed. -/
def FiltPipeLe2 : Prop :=
  ∃ Kf Df : ℕ, ∀ (P : GapParams) (e : GapSeed P) (L r4 G off : ℕ), 1 ≤ P.cap →
    FiltPipe.filtPipeBound P e L r4 G off (FiltSetup.rulerW P) (FiltSetup.rulerW P) ≤
      Kf * (P.len + P.cap + P.errExp + L + r4 + G + off + 2) ^ Df * (L + 2) ^ (Df * (P.errExp + 1))

end NearCubicWires.WireExponent3_5.PrimAsm.BudgetIface
