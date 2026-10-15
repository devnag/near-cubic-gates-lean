import Proof.Gates.Dispatch.ParamsH
import Proof.Gates.Interfaces.CounterFormats

set_option autoImplicit false
set_option maxRecDepth 4000

namespace NearCubicGates.Close.Dispatch

open NearCubicGates NearCubicGates.Close.Counter NearCubicWires NearCubicWires.RepairRepresentation
  NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats

/-- The witness flag. -/
def vWF : Fin VV := ⟨61, by decide⟩

/-- The variables fragment (W) may change (below the expression stack). -/
def WitVar (y : Fin VV) : Prop := (3 ≤ y.val ∧ y.val < 15) ∨ (61 ≤ y.val ∧ y.val < 131)

instance (y : Fin VV) : Decidable (WitVar y) := by unfold WitVar; infer_instance

/-- Its frame: every other variable below `200` is kept. -/
def FrW (a b : DS VV) : Prop := ∀ y : Fin VV, y.val < 200 → ¬ WitVar y → b.env y = a.env y

/-- What both programs may assume about the call and the parameters. -/
structure WitPre (C : Ctx) (c : Call) (p : Params) (a : DS VV) : Prop where
  cst : Cst a
  parse : ParseOut c a
  k : a.env pK = p.k
  lam : a.env pLAM = Target.lambda c.n
  J : a.env pJ = p.J
  cw : C.cw = callWord c
  nL : c.n ≤ C.cw.length
  kn : p.k ≤ c.n
  Jn : p.J ≤ c.n + 1
  wd : 4000 * (C.cw.length + 4) ^ 2 ≤ C.Wd

/-- **Fragment (W)**: the bounded witness decoder and printer. -/
structure WitFrag where
  check : St VV
  print : St VV
  cost : ℕ → ℕ
  cost_poly : ∃ K e : ℕ, ∀ L, cost L ≤ K * (L + 1) ^ e
  spec : ∀ (C : Ctx) (c : Call) (p : Params) (a : DS VV), WitPre C c p a → a.wq = 0 →
    Hs C check a (cost C.cw.length) (fun b => b.env vWF = bnat ((decodeWitness c p C.wit).isSome = true) ∧
      b.out = a.out ∧ Cst b ∧ FrW a b ∧
      ∀ wt, decodeWitness c p C.wit = some wt → ∀ b' : DS VV, WitPre C c p b' →
        (∀ y : Fin VV, 61 ≤ y.val → y.val < 98 → b'.env y = b.env y) →
        Hs C print b' (cost C.cw.length) (fun d => d.out = b'.out ++ witWord c p wt ∧ Cst d ∧ FrW b' d))

end NearCubicGates.Close.Dispatch
