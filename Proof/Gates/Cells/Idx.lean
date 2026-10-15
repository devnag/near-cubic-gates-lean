import Proof.Gates.Cells.Load3
import Proof.Gates.CounterMachine.CellIdx

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

namespace NearCubicGates.Close.Cells

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Interfaces
open NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter
open NearCubicGates.Close.CounterMachine (cellN callN paramsN witN circN gateN intN ratN bitN srList
  flatMap_gateN_length flatMap_intN_length ratN_length)

/-! ## Index functions on the list -/

section IdxFun
variable (L : List ℕ)

def fld (i : ℕ) : ℕ := L.getD i 0
def iC1 : ℕ := 3 + fld L 2 * (2 * fld L 0 + 3)
def iT1 : ℕ := iC1 L + 1 + 2 * fld L (iC1 L)
def iG2 : ℕ := iT1 L + 1 + fld L (iT1 L)
def iC2 : ℕ := iG2 L + 1 + fld L (iG2 L) * (2 * fld L 0 + 3)
def iT2 : ℕ := iC2 L + 1 + 2 * fld L (iC2 L)
def iPar : ℕ := iT2 L + 1 + fld L (iT2 L)
def iPsi : ℕ := iPar L + 4 + fld L (iPar L)
def nPr : ℕ := fld L (iPsi L + 12)
def nFa : ℕ := fld L (iPsi L + 24 + nPr L)
def iOm : ℕ := iPsi L + 27 + nPr L + nFa L

end IdxFun

theorem drop_app (A B : List ℕ) (i : ℕ) (h : i = A.length) : (A ++ B).drop i = B := by
  subst h; exact List.drop_left

theorem fld_of_drop {L B : List ℕ} {i x : ℕ} (h : L.drop i = x :: B) : fld L i = x := by
  unfold fld
  have : L.getD i 0 = (L.drop i).getD 0 0 := by simp [List.getD_eq_getElem?_getD]
  rw [this, h]; rfl

/-! ## The call -/

section Call
variable (c : Call) (p : Params) (wt : Wit c.n)

theorem cellN_split : cellN c p wt = ([c.n, kindTag c.kind] ++ circN c.first ++ circN c.second ++
    [c.parity.length] ++ c.parity ++ ratN c.radius) ++ (paramsN p ++ witN c p wt) := by
  simp [cellN, callN, List.append_assoc]

theorem idx_n : fld (cellN c p wt) 0 = c.n := by
  apply fld_of_drop (B := (kindTag c.kind :: (circN c.first ++ circN c.second ++ [c.parity.length] ++ c.parity ++
    ratN c.radius ++ (paramsN p ++ witN c p wt))))
  rw [cellN_split]; simp [List.append_assoc]

theorem idx_kind : fld (cellN c p wt) 1 = kindTag c.kind := by
  apply fld_of_drop (B := (circN c.first ++ circN c.second ++ [c.parity.length] ++ c.parity ++
    ratN c.radius ++ (paramsN p ++ witN c p wt)))
  rw [cellN_split]; simp [List.append_assoc]

/-- The first circuit from index `2`. -/
theorem idx_circ1 : (cellN c p wt).drop 2 = circN c.first ++ (circN c.second ++ [c.parity.length] ++ c.parity ++
    ratN c.radius ++ (paramsN p ++ witN c p wt)) := by
  rw [cellN_split]
  have : ([c.n, kindTag c.kind] ++ circN c.first ++ circN c.second ++ [c.parity.length] ++ c.parity ++ ratN c.radius) ++
      (paramsN p ++ witN c p wt) = [c.n, kindTag c.kind] ++ (circN c.first ++ (circN c.second ++ [c.parity.length] ++
      c.parity ++ ratN c.radius ++ (paramsN p ++ witN c p wt))) := by simp [List.append_assoc]
  rw [this, drop_app _ _ 2 rfl]

theorem drop_split {L X Y : List ℕ} {b : ℕ} (h : L.drop b = X ++ Y) : L.drop (b + X.length) = Y := by
  rw [← List.drop_drop, h, List.drop_left]

theorem drop_split' {L X Y : List ℕ} {b : ℕ} (h : L.drop b = X ++ Y) (k : ℕ) (hk : X.length = k) :
    L.drop (b + k) = Y := by
  rw [← hk]; exact drop_split h

/-- The parts of a circuit at a base index. -/
theorem circ_fields {n : ℕ} (Cc : NCircuit n) (L R : List ℕ) (b : ℕ) (hb : L.drop b = circN Cc ++ R) :
    fld L b = Cc.gates.length ∧ L.drop (b + 1) = Cc.gates.flatMap gateN ++ ([Cc.coeffs.length] ++
      (Cc.coeffs.flatMap intN ++ ([Cc.table.length] ++ (Cc.table.map bitN ++ R)))) ∧
    fld L (b + 1 + Cc.gates.length * (2 * n + 3)) = Cc.coeffs.length ∧
    L.drop (b + 1 + Cc.gates.length * (2 * n + 3) + 1) = Cc.coeffs.flatMap intN ++ ([Cc.table.length] ++
      (Cc.table.map bitN ++ R)) ∧
    fld L (b + 1 + Cc.gates.length * (2 * n + 3) + 1 + 2 * Cc.coeffs.length) = Cc.table.length ∧
    L.drop (b + 1 + Cc.gates.length * (2 * n + 3) + 1 + 2 * Cc.coeffs.length + 1) = Cc.table.map bitN ++ R ∧
    L.drop (b + 1 + Cc.gates.length * (2 * n + 3) + 1 + 2 * Cc.coeffs.length + 1 + Cc.table.length) = R := by
  have h1 : L.drop b = [Cc.gates.length] ++ (Cc.gates.flatMap gateN ++ ([Cc.coeffs.length] ++
      (Cc.coeffs.flatMap intN ++ ([Cc.table.length] ++ (Cc.table.map bitN ++ R))))) := by
    rw [hb]; simp [circN, List.append_assoc]
  have h2 := drop_split h1
  have h3 := drop_split h2
  have h4 := drop_split h3
  have h5 := drop_split h4
  have h6 := drop_split h5
  have h7 := drop_split h6
  simp only [List.length_singleton, flatMap_gateN_length, flatMap_intN_length, List.length_map] at h2 h3 h4 h5 h6 h7
  refine ⟨fld_of_drop (B := _) (by simpa using h1), h2, fld_of_drop (B := _) (by simpa using h3), h4,
    fld_of_drop (B := _) (by simpa using h5), h6, h7⟩

/-- **The layout of the cell input.** -/
structure Lay (c : Call) (p : Params) (wt : Wit c.n) (L : List ℕ) : Prop where
  n : fld L 0 = c.n
  kind : fld L 1 = kindTag c.kind
  g1 : fld L 2 = c.first.gates.length
  gates1 : ∃ R, L.drop 3 = c.first.gates.flatMap gateN ++ R
  c1 : fld L (iC1 L) = c.first.coeffs.length
  coeffs1 : ∃ R, L.drop (iC1 L + 1) = c.first.coeffs.flatMap intN ++ R
  t1 : fld L (iT1 L) = c.first.table.length
  table1 : ∃ R, L.drop (iT1 L + 1) = c.first.table.map bitN ++ R
  g2 : fld L (iG2 L) = c.second.gates.length
  gates2 : ∃ R, L.drop (iG2 L + 1) = c.second.gates.flatMap gateN ++ R
  c2 : fld L (iC2 L) = c.second.coeffs.length
  coeffs2 : ∃ R, L.drop (iC2 L + 1) = c.second.coeffs.flatMap intN ++ R
  t2 : fld L (iT2 L) = c.second.table.length
  table2 : ∃ R, L.drop (iT2 L + 1) = c.second.table.map bitN ++ R
  par : fld L (iPar L) = c.parity.length
  parl : ∃ R, L.drop (iPar L + 1) = c.parity ++ R
  params : L.drop (iPsi L) = paramsN p ++ witN c p wt
  np : nPr L = (p.primes.sort (· ≤ ·)).length
  nf : nFa L = p.factors.length
  wit : L.drop (iOm L) = witN c p wt

theorem lay : Lay c p wt (cellN c p wt) := by
  set L := cellN c p wt with hL
  have hn := idx_n c p wt
  have hk := idx_kind c p wt
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := circ_fields c.first L _ 2 (idx_circ1 c p wt)
  have e1 : iC1 L = 2 + 1 + c.first.gates.length * (2 * c.n + 3) := by
    unfold iC1; rw [hn, a1]
  have e2 : iT1 L = 2 + 1 + c.first.gates.length * (2 * c.n + 3) + 1 + 2 * c.first.coeffs.length := by
    unfold iT1; rw [e1, a3]
  have e3 : iG2 L = 2 + 1 + c.first.gates.length * (2 * c.n + 3) + 1 + 2 * c.first.coeffs.length + 1 +
      c.first.table.length := by
    unfold iG2; rw [e2, a5]
  rw [← e3] at a7
  have a7' : L.drop (iG2 L) = circN c.second ++ ([c.parity.length] ++ c.parity ++ ratN c.radius ++
      (paramsN p ++ witN c p wt)) := by rw [a7]; simp [List.append_assoc]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := circ_fields c.second L _ (iG2 L) a7'
  have f1 : iC2 L = iG2 L + 1 + c.second.gates.length * (2 * c.n + 3) := by
    unfold iC2; rw [hn, b1]
  have f2 : iT2 L = iG2 L + 1 + c.second.gates.length * (2 * c.n + 3) + 1 + 2 * c.second.coeffs.length := by
    unfold iT2; rw [f1, b3]
  have f3 : iPar L = iG2 L + 1 + c.second.gates.length * (2 * c.n + 3) + 1 + 2 * c.second.coeffs.length + 1 +
      c.second.table.length := by
    unfold iPar; rw [f2, b5]
  rw [← f3] at b7
  have hp1 : L.drop (iPar L) = [c.parity.length] ++ (c.parity ++ (ratN c.radius ++ (paramsN p ++ witN c p wt))) := by
    rw [b7]; simp [List.append_assoc]
  have hpar : fld L (iPar L) = c.parity.length := fld_of_drop (B := _) (by simpa using hp1)
  have hp2 := drop_split hp1
  have hp3 := drop_split hp2
  have hp4 := drop_split hp3
  simp only [List.length_singleton, ratN_length] at hp2 hp3 hp4
  have hpsi : iPsi L = iPar L + 1 + c.parity.length + 3 := by unfold iPsi; rw [hpar]; ring
  rw [← hpsi] at hp4
  -- the parameters
  set F9 := [p.n, bitN p.pair, p.W] ++ ratN p.beta ++ [p.k, p.T, p.m, p.Dmax, p.P, p.e]
  set Pr := p.primes.sort (· ≤ ·)
  set F11 := [p.window, p.L2, p.Lw, p.hE, p.h, p.R0] ++ ratN p.ell0 ++ [p.M1, p.J]
  have hq : paramsN p ++ witN c p wt = F9 ++ ([Pr.length] ++ (Pr ++ (F11 ++ ([p.factors.length] ++
      (p.factors ++ ([p.A, p.Lambda] ++ witN c p wt)))))) := by
    simp [CounterMachine.paramsN, F9, Pr, F11, List.append_assoc]
  have q1 := drop_split' (hp4.trans hq) 12 (by simp [F9, ratN_length])
  have hnp : nPr L = Pr.length := fld_of_drop (B := _) (by simpa using q1)
  have q2 := drop_split' q1 1 rfl
  have q3 := drop_split' q2 Pr.length rfl
  have q4 := drop_split' q3 11 (by simp [F11, ratN_length])
  have hnf : nFa L = p.factors.length := by
    unfold nFa; rw [hnp]
    have e : iPsi L + 24 + Pr.length = iPsi L + 12 + 1 + Pr.length + 11 := by ring
    rw [e]
    exact fld_of_drop (B := _) (by simpa using q4)
  have q5 := drop_split' q4 1 rfl
  have q6 := drop_split' q5 p.factors.length rfl
  have q7 := drop_split' q6 2 rfl
  refine ⟨hn, hk, a1, ⟨_, a2⟩, by rw [e1]; exact a3, ⟨_, by rw [e1]; exact a4⟩, by rw [e2]; exact a5,
    ⟨_, by rw [e2]; exact a6⟩, b1, ⟨_, b2⟩, by rw [f1]; exact b3, ⟨_, by rw [f1]; exact b4⟩, by rw [f2]; exact b5,
    ⟨_, by rw [f2]; exact b6⟩, hpar, ⟨_, by simpa using hp2⟩, ?_, hnp, hnf, ?_⟩
  · rw [hp4]
  · unfold iOm; rw [hnp, hnf]
    rw [show iPsi L + 27 + Pr.length + p.factors.length =
      iPsi L + 12 + 1 + Pr.length + 11 + 1 + p.factors.length + 2 by ring]
    exact q7

end Call

end NearCubicGates.Close.Cells
