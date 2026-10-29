import SourceAdapters.Proximity.HeaderParameters
import SourceAdapters.Proximity.HonestPreparedRun

/-! Q04, `app:sources`, "Uniform three-query PCPP and code interfaces": obtain the source randomness count by its actual
source algorithm and compute the coin-loop bound by paid binary arithmetic. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.HonestCoinSetup

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicGates.Close.Cells
open NearCubicGates.Published.CW19Proximity
open SourceRequests (State Script lengthReg)
open SourceCallee (randomReg coinLimitReg)

def script (q : ℕ) : Script := .seq SourceCallee.randomProgram (SourceHeader.parameters q)
def scratch : List (Fin VV) := (randomReg :: SourceResults.scratch) ++ SourceHeader.parameterScratch

def cost (q r sourceLength Lk Bk : ℕ) : ℕ :=
  15 * sourceLength + Lk + Bk + 10 * r.bits.length + 5 * r + 2 * predicateBlockBits q + 47

structure Ready {q : ℕ} (V : (S : SourceCircuit) → NonadaptiveVerifier S.arity q)
    (S : SourceCircuit) (a b : State) : Prop where
  constants : Cst b
  random : b.env randomReg = (V S).randomBits
  coins : b.env coinLimitReg = 2 ^ (V S).randomBits
  total_random : b.env SourceHeader.totalRandomReg = (V S).randomBits + predicateBlockBits q
  cursor : b.ip = a.ip
  out : b.out = a.out
  ram : b.ram = a.ram
  rc : b.rc = a.rc
  kin : b.kin = []
  vars : Fr a b scratch

variable {q : ℕ} (V : (S : SourceCircuit) → NonadaptiveVerifier S.arity q)
    (proofSize : SourceCircuit → ℕ)
    (honest : (p : AcceptedSourceInput) → BitInput (proofSize p.1))
    (budget : ProofCall V → ℕ)
    (P : WordFunction (ProofCall V) (proofCallInput V) (normalizedProofOutput V proofSize honest) budget)

theorem run (S : SourceCircuit) (Wd Lk Bk : ℕ) (pre tail : List Bool)
    (a : State) (hc : Cst a) (hW : 4 ≤ 2 ^ Wd)
    (hl : a.env lengthReg = (sourceCircuitWord S).length)
    (hip : a.ip = pre.length) (hkin : a.kin = [])
    (hroom : (proofCallInput V (SourceCallee.randomRequest V S)).length ≤ Lk)
    (hbudget : budget (SourceCallee.randomRequest V S) ≤ Bk)
    (hwidth : (V S).randomBits.bits.length + 1 ≤ Wd)
    (hpow : (V S).randomBits < Wd)
    (hcombined : (V S).randomBits + predicateBlockBits q < 2 ^ Wd) :
    let C := SourceCallee.context V proofSize honest budget P Wd (pre ++ sourceCircuitWord S ++ tail) Lk Bk
    Hs C (script q) a (cost q (V S).randomBits (sourceCircuitWord S).length Lk Bk)
      (Ready V S a) := by
  dsimp only
  let C := SourceCallee.context V proofSize honest budget P Wd (pre ++ sourceCircuitWord S ++ tail) Lk Bk
  obtain ⟨b, nb, eb, hb, rb⟩ := SourceCallee.source_random V proofSize honest budget P S Wd Lk Bk
    pre tail a hc hW hl hip hkin hroom hbudget hwidth
  have cb := Cst.of_fr hc rb.vars (by decide)
  obtain ⟨c, nc, ec, hcc, cp, ct, cs, cf⟩ := SourceHeader.parameters_run C q (V S).randomBits b cb
    rb.value_eq hpow hcombined
  have rest := rb.rest_eq
  simp only [SourceResults.rest, Prod.mk.injEq] at rest
  refine ⟨c, _, Ex.seq eb ec, ?_, ?_⟩
  · unfold cost
    omega
  exact ⟨Cst.of_fr cb cf (by decide), (cf randomReg (by decide)).trans rb.value_eq,
    cp, ct, cs.ip.trans rest.1, cs.out.trans rest.2.1, cs.ram.trans rest.2.2.1,
    cs.rc.trans rest.2.2.2, cs.kin.trans rb.kin_nil,
    (rb.vars.weaken (by decide)).trans (cf.weaken (by decide))⟩

end NearCubicGates.Adapters.Proximity.HonestCoinSetup
