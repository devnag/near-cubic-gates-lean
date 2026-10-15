import Proof.Gates.Cells.Inv

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace NearCubicGates.Close.Cells

open NearCubicWires NearCubicGates
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter
open NearCubicGates.Close.CounterMachine

/-- The number of cells `2^{|outer coordinates|}`. -/
def gNC : Fin VV := ⟨126, by decide⟩

def ifaceList : List (Fin VV) := [vZ, v1, v2, gN, gKd, gJ, gRC, vHE, vM1, vA, vLam, vBN, vNP, vIPr, vTS0, vTS1,
  vTW0, vTW1, p2VW, p2K, p2KF, pTH, pTL, pR, vKB, gB1, gWS, gFS, gPar, gPL, gNC, vNL]

/-- **The interface variables** (set once by the prelude). -/
structure Iface (c : Call) (p : Params) (wt : Wit c.n) (a : DS VV MM) : Prop where
  cst : Cst a
  n : a.env gN = c.n
  kind : a.env gKd = kindTag c.kind
  J : a.env gJ = p.J
  rc : a.env gRC = roleCount c.kind
  hE : a.env vHE = p.hE
  M1 : a.env vM1 = p.M1
  A : a.env vA = p.A
  Lam : a.env vLam = p.Lambda
  BN : a.env vBN = (wWin p) ^ (nDig c p)
  NP : a.env vNP = (p.primes.sort (· ≤ ·)).length
  IPr : (cellN c p wt).drop (a.env vIPr) = p.primes.sort (· ≤ ·) ++
    (cellN c p wt).drop (a.env vIPr + (p.primes.sort (· ≤ ·)).length)
  TS0 : (cellN c p wt).drop (a.env vTS0) = (circ c 0).table.map bitN ++
    (cellN c p wt).drop (a.env vTS0 + (circ c 0).table.length)
  TS1 : (cellN c p wt).drop (a.env vTS1) = (circ c 1).table.map bitN ++
    (cellN c p wt).drop (a.env vTS1 + (circ c 1).table.length)
  TW0 : a.env vTW0 = (circ c 0).topWeight
  TW1 : a.env vTW1 = (circ c 1).topWeight
  VW : a.env p2VW = 2 ^ valueWidth c p
  KW : a.env p2K = 2 ^ keyW c p
  KF : a.env p2KF = 2 ^ (keyW c p - keyBits p)
  TH : a.env pTH = min (p.hE ^ (2 * p.k)) (2 ^ valueWidth c p)
  TL : a.env pTL = min (p.Lambda ^ (2 * p.k)) (2 ^ valueWidth c p)
  R : a.env pR = (reqIds c p).length
  KB : a.env vKB = 2 ^ keyBits p
  B1 : a.env gB1 = iG2 (cellN c p wt)
  WS : a.env gWS = iOm (cellN c p wt) + 1 + fld (cellN c p wt) (iOm (cellN c p wt))
  FS : a.env gFS = iPsi (cellN c p wt) + 24 + nPr (cellN c p wt)
  Par : a.env gPar = iPar (cellN c p wt) + 1
  PL : a.env gPL = c.parity.length
  NC : a.env gNC = 2 ^ cellBits wt.I
  NL : a.env vNL = (cellN c p wt).length

theorem Iface.of_eq {c : Call} {p : Params} {wt : Wit c.n} {a b : DS VV MM} (h : Iface c p wt a)
    (hf : ∀ x ∈ ifaceList, b.env x = a.env x) : Iface c p wt b := by
  have e : ∀ x, x ∈ ifaceList → b.env x = a.env x := hf
  exact ⟨⟨by rw [e vZ (by decide)]; exact h.cst.z, by rw [e v1 (by decide)]; exact h.cst.one,
      by rw [e v2 (by decide)]; exact h.cst.two⟩,
    by rw [e gN (by decide)]; exact h.n, by rw [e gKd (by decide)]; exact h.kind,
    by rw [e gJ (by decide)]; exact h.J, by rw [e gRC (by decide)]; exact h.rc,
    by rw [e vHE (by decide)]; exact h.hE, by rw [e vM1 (by decide)]; exact h.M1,
    by rw [e vA (by decide)]; exact h.A, by rw [e vLam (by decide)]; exact h.Lam,
    by rw [e vBN (by decide)]; exact h.BN, by rw [e vNP (by decide)]; exact h.NP,
    by rw [e vIPr (by decide)]; exact h.IPr, by rw [e vTS0 (by decide)]; exact h.TS0,
    by rw [e vTS1 (by decide)]; exact h.TS1, by rw [e vTW0 (by decide)]; exact h.TW0,
    by rw [e vTW1 (by decide)]; exact h.TW1, by rw [e p2VW (by decide)]; exact h.VW,
    by rw [e p2K (by decide)]; exact h.KW, by rw [e p2KF (by decide)]; exact h.KF,
    by rw [e pTH (by decide)]; exact h.TH, by rw [e pTL (by decide)]; exact h.TL,
    by rw [e pR (by decide)]; exact h.R, by rw [e vKB (by decide)]; exact h.KB,
    by rw [e gB1 (by decide)]; exact h.B1, by rw [e gWS (by decide)]; exact h.WS,
    by rw [e gFS (by decide)]; exact h.FS, by rw [e gPar (by decide)]; exact h.Par,
    by rw [e gPL (by decide)]; exact h.PL, by rw [e gNC (by decide)]; exact h.NC,
    by rw [e vNL (by decide)]; exact h.NL⟩

/-- A frame list disjoint from the interface keeps it. -/
theorem Iface.of_fr {c : Call} {p : Params} {wt : Wit c.n} {a b : DS VV MM} {T : List (Fin VV)}
    (h : Iface c p wt a) (hf : Fr a b T) (hT : ∀ x ∈ ifaceList, x ∉ T) : Iface c p wt b :=
  h.of_eq (fun x hx => hf x (hT x hx))

/-! ## Lengths that do not depend on the cell -/

theorem ctrL_len (c : Call) (p : Params) (wt : Wit c.n) (y y' : Cells wt.I) :
    (ctrL c p wt y).length = (ctrL c p wt y').length := by
  simp [ctrL, pairOf, List.length_flatMap]

theorem kxL_len (c : Call) (p : Params) (wt : Wit c.n) (y y' : Cells wt.I) :
    (kxL c p wt y).length = (kxL c p wt y').length := by
  simp [kxL, pairOf, List.length_flatMap]

theorem rowVals_len (c : Call) (p : Params) (wt : Wit c.n) (y y' : Cells wt.I) :
    (rowVals c p wt y).length = (rowVals c p wt y').length := by
  simp [rowVals, List.length_flatMap]

theorem gWork_eq (c : Call) (p : Params) (wt : Wit c.n) (y y' : Cells wt.I) :
    gWork c p wt y = gWork c p wt y' := by
  unfold gWork; rw [rowVals_len c p wt y y']

/-- **The stores of the loop.** -/
structure Sto (c : Call) (p : Params) (wt : Wit c.n) (a : DS VV MM) : Prop where
  sN : a.ram sN = cellN c p wt
  sP : a.ram sP = tailL p
  sR : a.ram sR = membL wt.I
  lCT : (a.ram sCT).length ≤ (reqIds c p).length
  lZb : (a.ram sZb).length ≤ c.n
  lE : ∀ y : Cells wt.I, (a.ram sE).length ≤ (ctrL c p wt y).length
  lX : ∀ y : Cells wt.I, (a.ram sX).length ≤ (kxL c p wt y).length
  lG : ∀ y : Cells wt.I, (a.ram sG).length ≤ gWork c p wt y
  lB : ∀ y : Cells wt.I, (a.ram sB).length ≤ gWork c p wt y
  lA : ∀ y : Cells wt.I, (a.ram sA).length ≤ (rowVals c p wt y).length
  rcur : ∀ m, a.rc m ≤ (a.ram m).length
  out : a.out = []
  kin : a.kin = []
  kc : a.kc ≤ a.kout.length

end NearCubicGates.Close.Cells
