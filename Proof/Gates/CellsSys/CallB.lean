import Proof.Gates.CellsSys.CallA

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000

namespace NearCubicGates.Close.Cells.SystemsPhase

open NearCubicGates.Close.Cells
open NearCubicWires NearCubicGates NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter

variable {C : Ctx}

/-- The numeric data the reader uses. -/
structure CallN (e : DS VV MM) (K OP PI X0 Y0 X1 Y1 N0 N1 T0 W0 T1 W1 Mx Bw : ℕ) (md : ℕ → ℕ → ℕ) (C : Ctx) :
    Prop where
  hK : e.env vKd = K
  hOP : e.env vOP = OP
  hPI : e.env pI = PI
  hx0 : e.env l0P = X0
  hy0 : e.env l0N = Y0
  hx1 : e.env l1P = X1
  hy1 : e.env l1N = Y1
  hn0 : e.env n0 = N0
  hn1 : e.env n1 = N1
  hT0 : e.env vTS0 = T0
  hW0 : e.env vTW0 = W0
  hT1 : e.env vTS1 = T1
  hW1 : e.env vTW1 = W1
  small : OP ≤ 1 ∧ PI ≤ 1
  i0 : ∀ a < N0, Y0 ≤ T0 + W0 + X0 + a ∧ T0 + W0 + X0 + a - Y0 < (e.ram sN).length ∧
    (e.ram sN).getD (T0 + W0 + X0 + a - Y0) 0 ≤ 1
  i1 : K = 1 → ∀ b < N1, Y1 ≤ T1 + W1 + X1 + b ∧ T1 + W1 + X1 + b - Y1 < (e.ram sN).length ∧
    (e.ram sN).getD (T1 + W1 + X1 + b - Y1) 0 ≤ 1
  w0 : 0 < N0 → T0 + W0 + X0 + N0 < 2 ^ C.Wd
  w1 : K = 1 → 0 < N1 → T1 + W1 + X1 + N1 < 2 ^ C.Wd
  wn0 : N0 < 2 ^ C.Wd
  wn1 : N1 < 2 ^ C.Wd
  mx : ∀ a < N0, ∀ b < N1, md a b ≤ Mx
  bm : ∀ a < N0, ∀ b < N1, natBitLength (md a b) ≤ Bw
  B1 : 1 ≤ Bw
  BW : Bw + 2 ≤ C.Wd
  room : e.env vCnt + N0 * N1 * Mx < 2 ^ C.Wd
  len : (e.ram sN).length < 2 ^ C.Wd

/-- The bits of a point and the predicate. -/
def b0f (L : List ℕ) (T0 W0 X0 Y0 a : ℕ) : ℕ := L.getD (T0 + W0 + X0 + a - Y0) 0
def pbf (L : List ℕ) (K OP PI X0 Y0 X1 Y1 T0 W0 T1 W1 a b : ℕ) : ℕ :=
  (b0f L T0 W0 X0 Y0 a + (if K = 1 then b0f L T1 W1 X1 Y1 b else 0) + (if K = 2 then OP + PI else 0)) % 2
/-- The contribution of a point. -/
def cfn (L : List ℕ) (K OP PI X0 Y0 X1 Y1 T0 W0 T1 W1 : ℕ) (md : ℕ → ℕ → ℕ) (a b : ℕ) : ℕ :=
  if pbf L K OP PI X0 Y0 X1 Y1 T0 W0 T1 W1 a b = 1 then md a b else 0

def rdW (md : ℕ → ℕ → ℕ) (a b : ℕ) : List Bool := natWord 0 ++ natWord (md a b) ++ natWord 1

def idxP (ts tw lp ai ln : Fin VV) : St VV MM :=
  .seq (.op (.copy prd ts)) (.seq (.op (.add prd tw)) (.seq (.op (.add prd lp)) (.seq (.op (.add prd ai))
    (.op (.sub prd ln)))))

theorem idxP_spec (ts tw lp ai ln : Fin VV) (h1 : prd ≠ ts) (h2 : prd ≠ tw) (h3 : prd ≠ lp) (h4 : prd ≠ ai)
    (h5 : prd ≠ ln) (s : DS VV MM) (T Wt X A Y : ℕ) (ht : s.env ts = T) (hw : s.env tw = Wt) (hl : s.env lp = X)
    (ha : s.env ai = A) (hy : s.env ln = Y) (hY : Y ≤ T + Wt + X + A) (hW : T + Wt + X + A < 2 ^ C.Wd) :
    Hs C (idxP ts tw lp ai ln) s 9 (fun s' => s'.env prd = T + Wt + X + A - Y ∧ Fr s s' [prd] ∧ Same s s') := by
  have ev : ∀ {u v : DS VV MM}, Fr u v [prd] → ∀ x, x ≠ prd → v.env x = u.env x :=
    fun hf x hx => hf x (by simp [hx])
  refine Hx.hs (Hs.then (o_copy prd ts s h1) (fun s1 ⟨p1, p2, p3⟩ k1 hk1 => ?_))
  refine Hs.then (o_add prd tw s1 h2 (by rw [p1, ev p2 tw (Ne.symm h2), ht, hw]; omega)) (fun s2 ⟨q1, q2, q3⟩ k2 hk2 => ?_)
  rw [p1, ev p2 tw (Ne.symm h2), ht, hw] at q1
  have F2 : Fr s s2 [prd] := Fr.trans p2 q2
  refine Hs.then (o_add prd lp s2 h3 (by rw [q1, F2 lp (by simp [Ne.symm h3]), hl]; omega))
    (fun s3 ⟨r1, r2, r3⟩ k3 hk3 => ?_)
  rw [q1, F2 lp (by simp [Ne.symm h3]), hl] at r1
  have F3 : Fr s s3 [prd] := Fr.trans F2 r2
  refine Hs.then (o_add prd ai s3 h4 (by rw [r1, F3 ai (by simp [Ne.symm h4]), ha]; omega))
    (fun s4 ⟨u1, u2, u3⟩ k4 hk4 => ?_)
  rw [r1, F3 ai (by simp [Ne.symm h4]), ha] at u1
  have F4 : Fr s s4 [prd] := Fr.trans F3 u2
  refine Hs.last (o_sub prd ln s4 h5 (by rw [u1, F4 ln (by simp [Ne.symm h5]), hy]; omega))
    (fun s5 ⟨v1, v2, v3⟩ k5 hk5 => ⟨⟨by rw [v1, u1, F4 ln (by simp [Ne.symm h5]), hy], Fr.trans F4 v2,
      Same.trans p3 (Same.trans q3 (Same.trans r3 (Same.trans u3 v3)))⟩, by omega⟩)

end NearCubicGates.Close.Cells.SystemsPhase
