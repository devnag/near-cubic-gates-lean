import Proof.Wire_3_5.UnionMachineFiltSetupIface5
import Proof.Wire_3_5.PrimAsmThrDataIface3
import Proof.Wire_3_5.PrimAsmPlan

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.BudgetIface
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan

/-- **The FILTER pipeline's cost bound** (C6b): at the setup's rulers, `filtPipeBound` is at most
`K_f·(len + cap + e + L + r4 + G + off + 2)^{D_f·(e+1)}`, uniformly in the seed. -/
def FiltPipeLe : Prop :=
  ∃ Kf Df : ℕ, ∀ (P : GapParams) (e : GapSeed P) (L r4 G off : ℕ), 1 ≤ P.cap →
    FiltPipe.filtPipeBound P e L r4 G off (FiltSetup.rulerW P) (FiltSetup.rulerW P) ≤
      Kf * (P.len + P.cap + P.errExp + L + r4 + G + off + 2) ^ (Df * (P.errExp + 1))

/-- **The THR numbers are polynomial at the caller's calls** (specialized at `callInputs`): for
every THR filter-cap exponent `D_c`, an exponent `D_t` (depending on `l`, `D_c` only: `|𝒢| ≤ (n+2)^{4·algX l}`,
`CallIndex.thrEq_le`), and for every coefficient `C_c` and gate `F` a coefficient `K_t`, bounding every entry of
`hashNums` at every THR call shape (StageU's order: the exponent before `F`). -/
def ThrNumsPoly (l : Literals) : Prop :=
  ∀ Dc : ℕ, ∃ Dt : ℕ, ∀ (Cc : ℕ) (F : GateFree l), ∃ Kt : ℕ, ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (n : ℕ)
    (hs : (callInputs l F kclk coef A a ha).StarAt n) {a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit n)
    (carriers : List (Stars.Carrier n)) (capT : ℕ), a' ≤ 4 → carriers.length ≤ 2 →
    (∀ i, (Cs i).descriptionBits ≤ (n + 1) ^ 26) → capT ≤ Cc * (n + 1) ^ Dc →
    ∀ v ∈ ThrData.hashNums ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers (gate0 l F).alg
      (callInputs l F kclk coef A a ha).D capT, v ≤ Kt * (n + 1) ^ Dt

end NearCubicWires.WireExponent3_5.PrimAsm.BudgetIface
