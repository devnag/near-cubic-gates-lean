import Proof.Gates.CounterMachine.FormulaLink

set_option autoImplicit false

namespace NearCubicGates.Close.CounterMachine

open NearCubicWires NearCubicGates NearCubicGates.Close.Counter NearCubicGates.Close.Tabulator
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.RepairOrdinary (WordFunction)

def printerOrder (s : ℕ) : List ℕ :=
  (List.range (2 ^ ((s + 1) / 2))).flatMap fun i => (List.range (2 ^ (s / 2))).map fun j => i + 2 ^ ((s + 1) / 2) * j

/-- A request word up to and including `natWord V`. -/
def prefixWord {n : ℕ} (k s B : ℕ) (gates : List (NormalizedThresholdGate n)) (inner outer : List ℕ)
    (hbits : List Bool) (roles : List (ℕ × Bool)) (V : ℕ) : List Bool :=
  natWord n ++ natWord k ++ natWord s ++ natWord B ++ listWord gateWord gates ++ listWord natWord inner ++
    listWord natWord outer ++ listWord bitWord hbits ++
    listWord (fun ρ : ℕ × Bool => natWord ρ.1 ++ bitWord ρ.2) roles ++ natWord V

/-- The inner index `x` as a point of `I`: the `t`-th coordinate of `I` (increasing) is bit `t` of `x`. -/
def innerPt {n : ℕ} (I : Finset (Fin n)) (x : ℕ) : Points I := fun i => x.testBit ((coordsOf I).idxOf i.1.val)

section Pre
variable (c : Call) (p : Params) (wt : Wit c.n)

/-- The indicator of the part over the inner indices `x < 2^k`. -/
def resHbits (part : Option Bool) : List Bool :=
  (List.range (2 ^ p.k)).map fun x => inPart c wt part (innerPt wt.I x)

/-- The prefix of every table-(a) request on `part`. -/
def resPrefix (part : Option Bool) : List Bool :=
  prefixWord p.k (c.n - p.k) (Call.B0 c.n) (resGates c) (coordsOf wt.I) ((outerCoords wt.I).map Fin.val)
    (resHbits c p wt part) ((List.range (resGates c).length).map fun v => (v, false)) (resGates c).length

/-- The prefix of every table-(b) request of role `r`. -/
def momPrefix (r : ℕ) : List Bool :=
  prefixWord p.k (c.n - p.k) (Call.B0 c.n) (circ c r).gates (coordsOf wt.I) ((outerCoords wt.I).map Fin.val)
    (List.replicate (2 ^ p.k) true)
    (((List.range (circ c r).gates.length).map fun v => (v, false)) ++
      ((List.range (circ c r).gates.length).map fun v => (v, true)))
    (2 * (circ c r).gates.length)

end Pre

/-- All prefixes of a call, framed: the residue prefixes of the parts, then the moment prefixes of the roles. -/
def prefixesWord {B1 B2 cT : ℕ} (r : CellReq B1 B2 cT) : List Bool :=
  (parts r.c).flatMap (fun part => RepairOrdinary.frame (resPrefix r.c r.p r.wt part)) ++
    (List.range (roleCount r.c.kind)).flatMap fun ro => RepairOrdinary.frame (momPrefix r.c r.p r.wt ro)

structure PrefixMachine (B1 B2 cT : ℕ) where
  budget : CellReq B1 B2 cT → ℕ
  wf : WordFunction (CellReq B1 B2 cT) cellInput prefixesWord budget
  cls : ∃ C e : ℕ, ∀ r : CellReq B1 B2 cT, budget r ≤ C * 2 ^ r.p.k * ((cellInput r).length + 1) ^ e

end NearCubicGates.Close.CounterMachine
