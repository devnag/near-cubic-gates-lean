import Proof.Gates.Worker.Complete
import Proof.Gates.Counter.Den
import Proof.Gates.Counter.OutOK
import Proof.Gates.Closure.Budget
import Proof.Gates.Worker.Decide
import Proof.CaseAnalysis.FinalSupplierTotality

set_option autoImplicit false

namespace NearCubicGates.Close.Closure

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.CloseoutWitness
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Gadget NearCubicGates.Close.Transfer NearCubicGates.Close.Worker

/-! The field types unfold through the test, the guards and the outer PCP; the structure elaborator would `whnf`
through them. They are used, never unfolded, here (as the shared `FinalClose` does). -/
attribute [local irreducible] Guess.Certified Guess.Guards Guess.SizeOK Weak.Total Weak.decides width

def CounterSupply : Prop :=
  ∀ _s : GateSources, ∃ B1 B2 : ℕ, 1 ≤ B1 ∧ 1 ≤ B2 ∧ ∃ ctr : Counter B1 B2, Counter.DenOK ctr ∧ Counter.OutOK ctr

structure WorkerMachine (s : GateSources) (P : ThreeQueryPCPP) (g : GateParams) {B1 B2 : ℕ} (ctr : Counter B1 B2)
    (budget : ℕ → ℕ) (εT ω : ℚ) where
  tapes : ℕ
  states : ℕ
  worker : LocalBitMultitape.Machine tapes states
  htapes : 2 ≤ tapes
  result : Fin tapes
  fuel : ℕ → ℕ
  /-- The machine halts within `fuel N` on every input and every witness word. -/
  total : Weak.Total worker htapes result fuel
  /-- An accepted witness word carries a guess passing the test (v2 lines 2344–2378). -/
  sound : ∀ (N : ℕ) (x : BitInput N) (bits : List Bool), Weak.decides worker htapes result fuel N x bits →
    ∃ G : Guess (width s g N), G.Certified P x ctr budget (εT : ℝ) ω
  /-- Every guess within the size limits that passes the test has an accepted witness word of `⌊N/16⌋` bits. -/
  complete : ∃ onset : ℕ, ∀ N, onset ≤ N → ∀ (x : BitInput N) (G : Guess (width s g N)),
    G.SizeOK P x ctr budget → G.Certified P x ctr budget (εT : ℝ) ω →
      ∃ w : BitInput (N / 16), Weak.decides worker htapes result fuel N x (List.ofFn w)
  A : ℕ
  B : ℕ
  a : ℕ
  sigma : ℕ
  hot : ℕ → ℕ
  ha : a ≤ g.k + 1
  /-- `σ > A_pad`: `2^q ≤ C N^{k+2} q^{A_pad}` (`Outer.widthOf_table`, paper v2 §11.4 "`2^q/T_clk(N) = q^{O(1)}`"). -/
  hsigma : Outer.apad s.mw (g.sv s) + 1 ≤ sigma
  /-- The runtime split: polynomial preprocessing plus a hot part `o(2^q)` per `q^σ`. -/
  split : ∃ onset : ℕ, ∀ N, onset ≤ N →
    fuel N + 2 ≤ A * (N + 1) ^ a + hot N ∧
      hot N * (width s g N) ^ sigma ≤ B * 2 ^ (width s g N)

/-- The worker exists at every parameter choice whose clock exponent covers the preprocessing exponent `d₀`, with the
computable budget `budgetOf η` (the machine checks `topWeight ≤ b(q)`, so `b` must be computable). `d₀` may depend on
everything the consumer fixes before the clock (paper: "independent of the clock"). -/
def WorkerSupply : Prop :=
  ∀ (s : GateSources) (P : ThreeQueryPCPP) (B1 B2 : ℕ) (ctr : Counter B1 B2) (η εT ω : ℚ), Counter.DenOK ctr →
    Counter.OutOK ctr → 0 < η → 0 < ω →
    ∃ d0 : ℕ, ∀ g : GateParams, d0 ≤ g.k + 1 → Nonempty (WorkerMachine s P g ctr (budgetOf η) εT ω)

end NearCubicGates.Close.Closure
