import Proof.Gates.CounterMachine.CellTablesLoop5

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.CounterMachine.CellTablesProg

open NearCubicWires NearCubicGates NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Counter NearCubicGates.Close.CounterMachine
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Cells.PrefixLoader (sN gKd gJ gRC gN gS gJR loadP loadCost LS)
open NearCubicGates.Close.CounterMachine.CellTables (vS vH1 vH0 vSH vKY vQE vRS vRW sREC sTMP convP Frame)

def cstInit : St VV MM := .seq (.op (.inc v1)) (.seq (.op (.inc v2)) (.op (.inc v2)))

def startP : St VV MM := .seq cstInit (.seq loadP (.seq walkP cstP))

variable {B1 B2 cT : ℕ} {PolyTab : TabMachine}

def wdNeed (r : CellReq B1 B2 cT) : ℕ :=
  10 * (cellInput r).length + lamW r.c r.p + r.p.P + r.p.J + dOf r.c r.p + Nat.size (deltaBound r.c r.p) + 20

def startCost (r : CellReq B1 B2 cT) : ℕ :=
  5 + loadCost (callN r.c).length (paramsN r.p).length (witN r.c r.p r.wt).length (srList r.c r.p).length
    (cellInput r).length + (21 * (cellN r.c r.p r.wt).length + 300) + cstCost r.c r.p + 3

/-- The state after the start. -/
structure Started (C : Ctx) (r : CellReq B1 B2 cT) (e : DS VV MM) : Prop where
  pre : Pre C r e
  ramQ : e.ram sQ = r.p.primes.sort (· ≤ ·)
  rcQ : e.rc sQ = (r.p.primes.sort (· ≤ ·)).length
  np : e.env wNP = (r.p.primes.sort (· ≤ ·)).length
  ee : e.env wE = r.p.e
  kd : e.env gKd = kindTag r.c.kind
  j : e.env gJ = r.p.J
  rc : e.env gRC = roleCount r.c.kind
  rw : e.env vRW = r.c.n - r.p.k + keyBits r.p * keyLen r.c r.p + valueWidth r.c r.p
  out : e.out = []
  recs : e.ram sREC = []

theorem factors_sum_lt (r : CellReq B1 B2 cT) : r.p.factors.sum < 2 ^ (2 * (cellInput r).length) := by
  set X := (cellInput r).length
  have hmem : ∀ f ∈ r.p.factors, f < 2 ^ X := by
    intro f hf
    have h1 : f ∈ cellN r.c r.p r.wt := by
      unfold cellN paramsN; simp only [List.mem_append]; left; right; simp [hf]
    exact lt_of_lt_of_le (Cells.lt_natBitLength f) (Nat.pow_le_pow_right (by norm_num) (nbl_le_cellInput r f h1))
  have hlen : r.p.factors.length ≤ X := by
    have h1 : r.p.factors.length ≤ (paramsN r.p).length := by unfold paramsN; simp; omega
    have h2 : (paramsN r.p).length ≤ (cellN r.c r.p r.wt).length := by unfold cellN; simp; omega
    exact h1.trans (h2.trans (cellN_len_le r))
  have hs : r.p.factors.sum ≤ r.p.factors.length * 2 ^ X := by
    have := List.sum_le_card_nsmul r.p.factors (2 ^ X) (fun f hf => (hmem f hf).le)
    simpa using this
  have hX : X < 2 ^ X := Nat.lt_two_pow_self
  calc r.p.factors.sum ≤ r.p.factors.length * 2 ^ X := hs
    _ < 2 ^ X * 2 ^ X := Nat.mul_lt_mul_of_pos_right (lt_of_le_of_lt hlen hX) (Nat.two_pow_pos _)
    _ = 2 ^ (2 * X) := by rw [← pow_add]; ring_nf

end NearCubicGates.Close.CounterMachine.CellTablesProg
