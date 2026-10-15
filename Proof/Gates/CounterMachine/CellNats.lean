import Proof.Gates.CounterMachine.ReqCond

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.CounterMachine

open NearCubicWires NearCubicGates NearCubicGates.Close.Counter NearCubicGates.Close.Tabulator
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats
open NearCubicWires.RepairRepresentation (natWord)

/-! ## The naturals of each word -/

def intN (z : ℤ) : List ℕ := [if z < 0 then 1 else 0, z.natAbs]
def ratN (q : ℚ) : List ℕ := intN q.num ++ [q.den]
def bitN (b : Bool) : ℕ := if b then 1 else 0

def gateN {n : ℕ} (g : NormalizedThresholdGate n) : List ℕ :=
  [n] ++ (List.ofFn g.weight).flatMap intN ++ intN g.threshold

def circN {n : ℕ} (C : NCircuit n) : List ℕ :=
  [C.gates.length] ++ C.gates.flatMap gateN ++ [C.coeffs.length] ++ C.coeffs.flatMap intN ++ [C.table.length] ++
    C.table.map bitN

def callN (c : Call) : List ℕ :=
  [c.n, kindTag c.kind] ++ circN c.first ++ circN c.second ++ [c.parity.length] ++ c.parity ++ ratN c.radius

def paramsN (p : Params) : List ℕ :=
  [p.n, bitN p.pair, p.W] ++ ratN p.beta ++ [p.k, p.T, p.m, p.Dmax, p.P, p.e, (p.primes.sort (· ≤ ·)).length] ++
    p.primes.sort (· ≤ ·) ++ [p.window, p.L2, p.Lw, p.hE, p.h, p.R0] ++ ratN p.ell0 ++
    [p.M1, p.J, p.factors.length] ++ p.factors ++ [p.A, p.Lambda]

/-- The stage-role pairs of the witness, stage-major. -/
def srList (c : Call) (p : Params) : List (ℕ × ℕ) :=
  (List.range p.J).flatMap fun s => (List.range (roleCount c.kind)).map fun r => (s, r)

def witN (c : Call) (p : Params) (wt : Wit c.n) : List ℕ :=
  [(coordsOf wt.I).length] ++ coordsOf wt.I ++
    (srList c p).flatMap fun sr => [(wt.coef sr.1 sr.2).length] ++ (wt.coef sr.1 sr.2).flatMap intN

def cellN (c : Call) (p : Params) (wt : Wit c.n) : List ℕ := callN c ++ paramsN p ++ witN c p wt

/-! ## The words -/

theorem intN_word (z : ℤ) : (intN z).flatMap natWord = Interfaces.intWord z := by
  simp [intN, Interfaces.intWord]

theorem ratN_word (q : ℚ) : (ratN q).flatMap natWord = ratWord q := by
  simp only [ratN, ratWord, List.flatMap_append, intN_word]; simp

theorem list_word {α : Type} (f : α → List ℕ) (xs : List α) :
    ([xs.length] ++ xs.flatMap f).flatMap natWord = listWord (fun x => (f x).flatMap natWord) xs := by
  simp [listWord, List.flatMap_append, List.flatMap_assoc]

theorem gateN_word {n : ℕ} (g : NormalizedThresholdGate n) : (gateN g).flatMap natWord = gateWord g := by
  unfold gateN gateWord
  rw [List.flatMap_append, List.flatMap_append, intN_word, List.flatMap_assoc]
  congr 1
  simp only [listWord, List.length_ofFn, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  congr 1
  apply List.flatMap_congr
  intro z _; exact intN_word z

theorem circN_word {n : ℕ} (C : NCircuit n) : (circN C).flatMap natWord = circuitWord C := by
  unfold circN circuitWord
  simp only [List.flatMap_append, List.flatMap_assoc, List.flatMap_map]
  simp [listWord, gateN_word, intN_word, bitWord, bitN, List.append_assoc]
  apply List.flatMap_congr; intro b _; rfl

theorem callN_word (c : Call) : (callN c).flatMap natWord = callWord c := by
  unfold callN callWord
  simp only [List.flatMap_append, circN_word, ratN_word]
  simp [listWord, List.append_assoc]

theorem paramsN_word (p : Params) : (paramsN p).flatMap natWord = paramsWord p := by
  unfold paramsN paramsWord
  simp only [List.flatMap_append, ratN_word]
  simp [listWord, bitWord, List.append_assoc]
  rfl

theorem witN_word (c : Call) (p : Params) (wt : Wit c.n) : (witN c p wt).flatMap natWord = witWord c p wt := by
  unfold witN witWord srList
  simp only [List.flatMap_append, List.flatMap_assoc]
  simp [listWord, intN_word, List.append_assoc]

/-- **The cell input is the naturals' words.** -/
theorem cellN_word (c : Call) (p : Params) (wt : Wit c.n) :
    (cellN c p wt).flatMap natWord = callWord c ++ paramsWord p ++ witWord c p wt := by
  unfold cellN; simp only [List.flatMap_append, callN_word, paramsN_word, witN_word]

end NearCubicGates.Close.CounterMachine
