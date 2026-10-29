import Proof.Gates.Interfaces.Transfer
import Proof.MachineModel.OrdinaryOracleComposeReady

/-!
# The recovery after the refuter: one SAT-oracle program from `(z, point)` to the gate core's bit

`sec:all-lengths`: "The choices of sec:gadget-transfer are recovered in three stages, by prefix self-reduction on SAT
formulas of size 2^{O(q)}. First, a formula over the description of B_src with the N constraints eq:source-check …
finds the first source circuit B*_src, or shows that there is none, in which case the table is X_z. Second, the
algorithm of imp:short-pcp is run deterministically on ⟨B*_src⟩_ν …; a formula with one variable per oracle address …
finds the first oracle O*. Third, a formula over the description of B_pf with the 2^{ℓ_out} constraints
B_pf(a0^{q−ℓ_out}) = O*(a) … finds the first B*_pf, or shows that there is none, in which case the table is Ô*. …
Run the general amplifier on X_z or Ô*. If no oracle O* exists at an exceptional initial source length, the second
stage detects that case and the slice is set to zero. In the small-oracle branch, the honest PCPP proof and each AND
helper are computable in polynomial time once the pair is known."

`AfterRun s P g` is that computation as one ordinary SAT-oracle program, started after the refuter: its port `zPort`
holds the refuter's source input `z ∈ {0,1}^{2^ν}` (framed, followed by any word `post`), its port `pointPort` the final
address `point ∈ {0,1}^n`, every other tape (the query tape included) is blank; it halts with heads at zero and its
output tape holds the gate core's value `gateCore … ν z … n point` (`Transfer.GateParams.gateCore`: Case 2's padded hard
table, Case 1's amplified `X_z` or `Ô*`, or `false` without an honest oracle), within `C (2^n + 1)^E` steps, whenever
`ν` is a live source index for `n` (`1 ≤ ν`, `cutoff ≤ 2^ν`, `m(q(N_ν)) ≤ n/2`). The common program
(Recovery/Common*) runs the refuter prefix and then this program; `cutoff` is absorbed by raising the source onset
(`Transfer.RecoverySupply` allows it).
-/

set_option autoImplicit false

namespace NearCubicGates.Close.Recovery

open NearCubicWires NearCubicWires.RepairSource NearCubicWires.RepairOrdinary NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairSource.CloseoutLanguage NearCubicGates.Close.Transfer NearCubicGates.Close.Gadget

/-- The input bank of the after-prefix program: `frame z ++ post` on `zPort`, `frame point` on `pointPort`, every other
tape blank. -/
def afterBank {t : ℕ} (zPort pointPort : Fin t) (zWord pointWord : List Bool) : Fin t → List Bool :=
  fun i => if i = zPort then zWord else if i = pointPort then pointWord else []

/-- **The recovery after the refuter** (`sec:all-lengths`, the three stages and the two branches). -/
structure AfterRun (s : GateSources) (P : ThreeQueryPCPP) (g : GateParams) where
  prog : OrdinaryOracleProgram
  zPort : Fin prog.base.tapeCount
  pointPort : Fin prog.base.tapeCount
  zPoint : zPort ≠ pointPort
  zQuery : zPort ≠ prog.queryTape
  pointQuery : pointPort ≠ prog.queryTape
  zOutput : zPort ≠ prog.base.outputTape
  pointOutput : pointPort ≠ prog.base.outputTape
  queryOutput : prog.queryTape ≠ prog.base.outputTape
  cutoff : ℕ
  C : ℕ
  E : ℕ
  run : ∀ (n : ℕ) (point : BitInput n) (ν : ℕ) (z : BitInput (2 ^ ν)) (post : List Bool),
    1 ≤ ν → cutoff ≤ 2 ^ ν → g.coreArity s ν ≤ n / 2 →
    ∃ cost, cost ≤ C * (2 ^ n + 1) ^ E ∧ ∃ out : Fin prog.base.tapeCount → List Bool,
      OrdinaryOracleCompose.Ready RecoveryOracle.correctedSat prog cost
        (afterBank zPort pointPort (RepairOrdinary.frame (List.ofFn z) ++ post) (RepairOrdinary.frame (List.ofFn point))) out ∧
      out prog.base.outputTape =
        RepairOrdinary.frame (g.gateCore s P (selectedAmplifier s.amplification g.degree) ν z
          (clauseWidth g.clauseDegree (g.width s ν)) g.positionLog n point).toNat.bits

/-- The parameter facts the after-prefix program may use (fields of `Transfer.GateParamsReady`): `K_amp ≥ 1`,
`K_amp ≥ a_G`, `log₂ P ≥ 1`, `d_G ≥ 1`. -/
structure AfterReady (s : GateSources) (g : GateParams) : Prop where
  ampPos : 1 ≤ g.ampFactor
  ampLarge : (selectedAmplifier s.amplification g.degree).arityCoefficient ≤ g.ampFactor
  positionPos : 1 ≤ g.positionLog
  clausePos : 1 ≤ g.clauseDegree

theorem afterReady_of {s : GateSources} {P : ThreeQueryPCPP} {ε : ℝ} {g : GateParams} {budget : ℕ → ℕ}
    (h : GateParamsReady s P ε g budget) : AfterReady s g :=
  ⟨h.ampPos, h.ampLarge, h.positionPos, h.clausePos⟩

/-- The deliverable: the after-prefix program for every source bundle, PCPP and ready parameter choice. -/
def AfterSupply : Prop :=
  ∀ (s : GateSources) (P : ThreeQueryPCPP) (g : GateParams), AfterReady s g → Nonempty (AfterRun s P g)

end NearCubicGates.Close.Recovery
