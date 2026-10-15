import Proof.Gates.CellsSys.Kit

set_option autoImplicit false
set_option maxRecDepth 4000

namespace NearCubicGates.Close.Cells.SystemsPhase

open NearCubicGates.Close.Cells
open NearCubicWires NearCubicGates NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter

variable {C : Ctx}

/-! ## The phase's variables (50 … 99) -/

def pI : Fin VV := ⟨50, by decide⟩
def nPa : Fin VV := ⟨51, by decide⟩
def tI : Fin VV := ⟨52, by decide⟩
def rI : Fin VV := ⟨53, by decide⟩
def jI : Fin VV := ⟨54, by decide⟩
def iI : Fin VV := ⟨55, by decide⟩
def dV : Fin VV := ⟨56, by decide⟩
def pw : Fin VV := ⟨57, by decide⟩
def wW : Fin VV := ⟨58, by decide⟩
def accP : Fin VV := ⟨59, by decide⟩
def accN : Fin VV := ⟨60, by decide⟩
def f1 : Fin VV := ⟨61, by decide⟩
def f2 : Fin VV := ⟨62, by decide⟩
def f3 : Fin VV := ⟨63, by decide⟩
def ix : Fin VV := ⟨64, by decide⟩
def Cp : Fin VV := ⟨65, by decide⟩
def Cn : Fin VV := ⟨66, by decide⟩
def kP : Fin VV := ⟨67, by decide⟩
def kN : Fin VV := ⟨68, by decide⟩
def xP : Fin VV := ⟨69, by decide⟩
def xN : Fin VV := ⟨70, by decide⟩
def Wv : Fin VV := ⟨71, by decide⟩
def q1 : Fin VV := ⟨72, by decide⟩
def q2 : Fin VV := ⟨73, by decide⟩
def q3 : Fin VV := ⟨74, by decide⟩
def q4 : Fin VV := ⟨75, by decide⟩
def lP : Fin VV := ⟨76, by decide⟩
def lN : Fin VV := ⟨77, by decide⟩
def hP : Fin VV := ⟨78, by decide⟩
def hN : Fin VV := ⟨79, by decide⟩
def nL : Fin VV := ⟨80, by decide⟩
def l0P : Fin VV := ⟨81, by decide⟩
def l0N : Fin VV := ⟨82, by decide⟩
def n0 : Fin VV := ⟨83, by decide⟩
def l1P : Fin VV := ⟨84, by decide⟩
def l1N : Fin VV := ⟨85, by decide⟩
def n1 : Fin VV := ⟨86, by decide⟩
def a0I : Fin VV := ⟨87, by decide⟩
def a1I : Fin VV := ⟨88, by decide⟩
def cnt : Fin VV := ⟨89, by decide⟩
def qI : Fin VV := ⟨90, by decide⟩
def qV : Fin VV := ⟨91, by decide⟩
def s0I : Fin VV := ⟨92, by decide⟩
def s1I : Fin VV := ⟨93, by decide⟩
def qB : Fin VV := ⟨94, by decide⟩
def mV : Fin VV := ⟨95, by decide⟩
def prd : Fin VV := ⟨96, by decide⟩
def b0 : Fin VV := ⟨97, by decide⟩
def b1 : Fin VV := ⟨98, by decide⟩
def nDg : Fin VV := ⟨99, by decide⟩

/-! ## `pw := w^e` (`e` in `q3`) -/

def powL : St VV MM :=
  .seq (.op (.zero pw)) (.seq (.op (.inc pw)) (forS c1 q3 (.seq (.op (.mul pw wW f1)) (.op (.copy pw f1)))))

theorem powL_spec (a : DS VV MM) (w e : ℕ) (hw : a.env wW = w) (he : a.env q3 = e) (hw1 : 1 ≤ w)
    (hpw : w ^ e * (w + 1) < 2 ^ C.Wd) (heW : e < 2 ^ C.Wd) :
    Hs C powL a (e * 7 + 10) (fun b => b.env pw = w ^ e ∧ Fr a b [pw, f1, c1] ∧ Same a b) := by
  have hpos : 1 ≤ w ^ e := Nat.one_le_pow _ _ hw1
  have h1W : 1 < 2 ^ C.Wd := by
    have : 1 ≤ w ^ e * (w + 1) := Nat.one_le_iff_ne_zero.2 (by positivity)
    omega
  refine Hx.hs (Hs.then (o_zero pw a) (fun b1 ⟨p1, p2, p3⟩ k1 hk1 => ?_))
  refine Hs.then (o_inc pw b1 (by rw [p1]; omega)) (fun b2 ⟨r1, r2, r3⟩ k2 hk2 => ?_)
  rw [p1] at r1
  have b2w : b2.env wW = w := by simp (disch := decide) only [r2.ev, p2.ev]; exact hw
  have b2e : b2.env q3 = e := by simp (disch := decide) only [r2.ev, p2.ev]; exact he
  have hpe : ∀ k ≤ e, w ^ k * w < 2 ^ C.Wd := fun k hk =>
    lt_of_le_of_lt (Nat.mul_le_mul (Nat.pow_le_pow_right hw1 hk) (by omega)) hpw
  let I : ℕ → DS VV MM → Prop := fun k d => d.env pw = w ^ k ∧ d.env wW = w ∧ Fr b2 d [pw, f1, c1] ∧ Same b2 d
  have hl := forS_spec' (C := C) c1 q3 (by decide) (.seq (.op (.mul pw wW f1)) (.op (.copy pw f1))) b2 e heW I 3
    (fun k d v ⟨i1, i2, i3, i4⟩ => ⟨by rw [DS.set_env_ne _ _ (by decide)]; exact i1,
      by rw [DS.set_env_ne _ _ (by decide)]; exact i2, Fr.trans i3 (Fr.set d v (by decide)),
      Same.trans i4 (Same.set d c1 v)⟩)
    ⟨by rw [r1]; simp, b2w, Fr.refl _ _, Same.refl _⟩ b2e (fun k hk d ⟨i1, i2, i3, i4⟩ hdk hde => by
      refine Hs.mono (Hs.seq (t1 := 1) (t2 := 1) (o_mul pw wW f1 d (by decide) (by decide) (by decide)
        (by rw [i1, i2]; exact hpe k hk.le)) (fun g ⟨g1, g2, g3⟩ => ?_)) (by norm_num) (fun _ h => h)
      refine Hs.mono (o_copy pw f1 g (by decide)) le_rfl ?_
      rintro h ⟨h1, h2, h3⟩
      have hg2 : g.env wW = w := by simp (disch := decide) only [g2.ev]; exact i2
      refine ⟨⟨by rw [h1, g1, i1, i2, pow_succ], by simp (disch := decide) only [h2.ev]; exact hg2,
        Fr.trans i3 (Fr.trans (g2.weaken (by decide)) (h2.weaken (by decide))), Same.trans i4 (Same.trans g3 h3)⟩,
        by simp (disch := decide) only [h2.ev, g2.ev]; exact hdk, by simp (disch := decide) only [h2.ev, g2.ev]; exact hde⟩)
  refine Hs.last hl (fun g ⟨⟨g1, _, g3, g4⟩, _, _⟩ k3 hk3 => ⟨⟨g1, Fr.trans (p2.weaken (by decide))
    (Fr.trans (r2.weaken (by decide)) g3), Same.trans p3 (Same.trans r3 g4)⟩, by omega⟩)

/-! ## One digit term -/

/-- The `i`-th digit (most significant first) of the counter `t` (radix `w`, `nD` digits). -/
def dig (w nD t i : ℕ) : ℕ := t / w ^ (nD - 1 - i) % w

def accPf (PL EL : List ℕ) (r J nD w t k : ℕ) : ℕ :=
  ∑ j ∈ Finset.range k, PL.getD j 0 * (EL.getD (2 * (r * J + j)) 0 + 1 + dig w nD t (r * J + j))

def accNf (PL EL : List ℕ) (r J hE k : ℕ) : ℕ :=
  ∑ j ∈ Finset.range k, PL.getD j 0 * (EL.getD (2 * (r * J + j) + 1) 0 + hE)

def digB : St VV MM :=
  .seq (.op (.mul rI vJ' iI)) (.seq (.op (.add iI jI)) (.seq (.op (.copy q3 nDg)) (.seq (.op (.sub q3 v1)) (.seq (.op (.sub q3 iI)) (.seq powL (.seq (.op (.dm tI pw f1 f2)) (.seq (.op (.dm f1 wW f2 dV)) (.seq (fetch sP jI f1) (.seq (.op (.copy ix iI)) (.seq (.op (.shl ix)) (.seq (fetch sE ix f2) (.seq (.op (.inc ix)) (.seq (fetch sE ix f3) (.seq (.op (.copy q1 f2)) (.seq (.op (.inc q1)) (.seq (.op (.add q1 dV)) (.seq (.op (.mul f1 q1 q2)) (.seq (.op (.add accP q2)) (.seq (.op (.copy q1 f3)) (.seq (.op (.add q1 vHE)) (.seq (.op (.mul f1 q1 q2)) (.op (.add accN q2)))))))))))))))))))))))

def digT : List (Fin VV) := [iI, q3, pw, f1, c1, f2, dV, ix, f3, q1, q2, accP, accN, c0, vJ]

def digCost (nD lP lE : ℕ) : ℕ := 7 * nD + 6 * lP + 12 * lE + 120

/-- What the digit loop keeps and needs. -/
structure DigI (PL EL : List ℕ) (r t J hE w nD : ℕ) (d : DS VV MM) : Prop where
  r : d.env rI = r
  t : d.env tI = t
  J : d.env vJ' = J
  hE : d.env vHE = hE
  w : d.env wW = w
  nD : d.env nDg = nD
  P : d.ram sP = PL
  E : d.ram sE = EL
  rc : RcOK d
  cst : Cst d

theorem digB_spec (PL EL : List ℕ) (r t J hE w nD V j : ℕ) (d : DS VV MM) (hI : DigI PL EL r t J hE w nD d)
    (hj : d.env jI = j) (hjJ : j < J) (hrj : r * J + j < nD) (hPL : j < PL.length)
    (hEL : 2 * (r * J + j) + 1 < EL.length) (hw1 : 1 ≤ w) (hpw : w ^ nD * (w + 1) < 2 ^ C.Wd)
    (hV : ∀ x ∈ PL, x ≤ V) (hVE : ∀ x ∈ EL, x ≤ V) (hEV : hE ≤ V) (hwV : w ≤ V)
    (hbig : (J + 1) * (V * (2 * V + 2)) + EL.length + nD + r * J + J < 2 ^ C.Wd)
    (ha : d.env accP = accPf PL EL r J nD w t j) (hb : d.env accN = accNf PL EL r J hE j) :
    Hs C digB d (digCost nD PL.length EL.length) (fun g => g.env accP = accPf PL EL r J nD w t (j + 1) ∧
      g.env accN = accNf PL EL r J hE (j + 1) ∧ DigI PL EL r t J hE w nD g ∧ Fr d g digT ∧ Kp d g ∧ g.env jI = j) := by
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8, i9, i11⟩ := hI
  -- every product formed below is at most `V·(2V+2)`, and the sums stay below the bound
  have hPj : PL.getD j 0 ≤ V := by
    rw [List.getD_eq_getElem _ _ hPL]; exact hV _ (List.getElem_mem _)
  have hE0 : EL.getD (2 * (r * J + j)) 0 ≤ V := by
    rw [List.getD_eq_getElem _ _ (by omega)]; exact hVE _ (List.getElem_mem _)
  have hE1 : EL.getD (2 * (r * J + j) + 1) 0 ≤ V := by
    rw [List.getD_eq_getElem _ _ hEL]; exact hVE _ (List.getElem_mem _)
  have hdig : dig w nD t (r * J + j) < w := Nat.mod_lt _ (by omega)
  have hsumP : accPf PL EL r J nD w t (j + 1) ≤ (j + 1) * (V * (2 * V + 2)) := by
    unfold accPf
    calc ∑ j' ∈ Finset.range (j + 1), PL.getD j' 0 * (EL.getD (2 * (r * J + j')) 0 + 1 + dig w nD t (r * J + j'))
        ≤ ∑ _j' ∈ Finset.range (j + 1), V * (2 * V + 2) := by
          apply Finset.sum_le_sum
          intro j' hj'
          rw [Finset.mem_range] at hj'
          have h1 : PL.getD j' 0 ≤ V := by
            rcases Nat.lt_or_ge j' PL.length with h | h
            · rw [List.getD_eq_getElem _ _ h]; exact hV _ (List.getElem_mem _)
            · rw [List.getD_eq_default _ _ h]; omega
          have h2 : EL.getD (2 * (r * J + j')) 0 ≤ V := by
            rcases Nat.lt_or_ge (2 * (r * J + j')) EL.length with h | h
            · rw [List.getD_eq_getElem _ _ h]; exact hVE _ (List.getElem_mem _)
            · rw [List.getD_eq_default _ _ h]; omega
          have h3 : dig w nD t (r * J + j') < w := Nat.mod_lt _ (by omega)
          exact Nat.mul_le_mul h1 (by omega)
      _ = (j + 1) * (V * (2 * V + 2)) := by simp
  have hsumN : accNf PL EL r J hE (j + 1) ≤ (j + 1) * (V * (2 * V + 2)) := by
    unfold accNf
    calc ∑ j' ∈ Finset.range (j + 1), PL.getD j' 0 * (EL.getD (2 * (r * J + j') + 1) 0 + hE)
        ≤ ∑ _j' ∈ Finset.range (j + 1), V * (2 * V + 2) := by
          apply Finset.sum_le_sum
          intro j' hj'
          have h1 : PL.getD j' 0 ≤ V := by
            rcases Nat.lt_or_ge j' PL.length with h | h
            · rw [List.getD_eq_getElem _ _ h]; exact hV _ (List.getElem_mem _)
            · rw [List.getD_eq_default _ _ h]; omega
          have h2 : EL.getD (2 * (r * J + j') + 1) 0 ≤ V := by
            rcases Nat.lt_or_ge (2 * (r * J + j') + 1) EL.length with h | h
            · rw [List.getD_eq_getElem _ _ h]; exact hVE _ (List.getElem_mem _)
            · rw [List.getD_eq_default _ _ h]; omega
          exact Nat.mul_le_mul h1 (by omega)
      _ = (j + 1) * (V * (2 * V + 2)) := by simp
  have hJ1 : (j + 1) * (V * (2 * V + 2)) ≤ (J + 1) * (V * (2 * V + 2)) := Nat.mul_le_mul_right _ (by omega)
  have hstepP : accPf PL EL r J nD w t (j + 1) = accPf PL EL r J nD w t j +
      PL.getD j 0 * (EL.getD (2 * (r * J + j)) 0 + 1 + dig w nD t (r * J + j)) := by
    unfold accPf; rw [Finset.sum_range_succ]
  have hstepN : accNf PL EL r J hE (j + 1) = accNf PL EL r J hE j +
      PL.getD j 0 * (EL.getD (2 * (r * J + j) + 1) 0 + hE) := by
    unfold accNf; rw [Finset.sum_range_succ]
  have hprodP : PL.getD j 0 * (EL.getD (2 * (r * J + j)) 0 + 1 + dig w nD t (r * J + j)) ≤ V * (2 * V + 2) :=
    Nat.mul_le_mul hPj (by omega)
  have hprodN : PL.getD j 0 * (EL.getD (2 * (r * J + j) + 1) 0 + hE) ≤ V * (2 * V + 2) :=
    Nat.mul_le_mul hPj (by omega)
  have hVV : V * (2 * V + 2) ≤ (J + 1) * (V * (2 * V + 2)) := Nat.le_mul_of_pos_left _ (by omega)
  have hrJ : r * J ≤ r * J + j := by omega
  have hV1 : 1 ≤ V := le_trans hw1 hwV
  have h2V : 2 * V + 1 ≤ V * (2 * V + 2) := by nlinarith
  -- iI := r·J + j
  refine Hx.hs (Hs.then (o_mul rI vJ' iI d (by decide) (by decide) (by decide) (by rw [i1, i3]; omega))
    (fun e1 ⟨s1, s2, s3⟩ k1 hk1 => ?_))
  rw [i1, i3] at s1
  refine Hs.then (o_add iI jI e1 (by decide) (by simp (disch := decide) only [s2.ev]; rw [s1, hj]; omega))
    (fun e2 ⟨u1, u2, u3⟩ k2 hk2 => ?_)
  have e2i : e2.env iI = r * J + j := by rw [u1, s1]; simp (disch := decide) only [s2.ev]; rw [hj]
  -- q3 := nD − 1 − i
  refine Hs.then (o_copy q3 nDg e2 (by decide)) (fun e3 ⟨v1', v2', v3'⟩ k3 hk3 => ?_)
  have e3q : e3.env q3 = nD := by rw [v1']; simp (disch := decide) only [u2.ev, s2.ev]; exact i6
  have c3 : Cst e3 := cst_of (cst_of (cst_of i11 s2 (by decide)) u2 (by decide)) v2' (by decide)
  refine Hs.then (o_sub q3 v1 e3 (by decide) (by rw [c3.one, e3q]; omega)) (fun e4 ⟨w1, w2, w3⟩ k4 hk4 => ?_)
  rw [e3q, c3.one] at w1
  refine Hs.then (o_sub q3 iI e4 (by decide) (by
      rw [w1]; simp (disch := decide) only [w2.ev, v2'.ev]; rw [e2i]; omega)) (fun e5 ⟨x1, x2, x3⟩ k5 hk5 => ?_)
  have e5q : e5.env q3 = nD - 1 - (r * J + j) := by
    rw [x1, w1]; simp (disch := decide) only [w2.ev, v2'.ev]; rw [e2i]
  -- pw := w^(nD − 1 − i)
  have e5w : e5.env wW = w := by simp (disch := decide) only [x2.ev, w2.ev, v2'.ev, u2.ev, s2.ev]; exact i5
  have hpw' : w ^ (nD - 1 - (r * J + j)) * (w + 1) < 2 ^ C.Wd :=
    lt_of_le_of_lt (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hw1 (by omega))) hpw
  refine Hs.then (powL_spec e5 w _ e5w e5q hw1 hpw' (by omega)) (fun e6 ⟨y1, y2, y3⟩ k6 hk6 => ?_)
  have e6t : e6.env tI = t := by simp (disch := decide) only [y2.ev, x2.ev, w2.ev, v2'.ev, u2.ev, s2.ev]; exact i2
  have hpwpos : 0 < w ^ (nD - 1 - (r * J + j)) := Nat.pos_of_ne_zero (by positivity)
  have h2pw : w ^ (nD - 1 - (r * J + j)) * 2 ≤ w ^ (nD - 1 - (r * J + j)) * (w + 1) := Nat.mul_le_mul_left _ (by omega)
  refine Hs.then (o_dm tI pw f1 f2 e6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [y1]; exact hpwpos) (by rw [y1]; omega)) (fun e7 ⟨z1, z2, z3, z4⟩ k7 hk7 => ?_)
  rw [e6t, y1] at z1
  have e7w : e7.env wW = w := by simp (disch := decide) only [z3.ev, y2.ev]; exact e5w
  refine Hs.then (o_dm f1 wW f2 dV e7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [e7w]; omega) (by rw [e7w]; omega)) (fun e8 ⟨a1', a2', a3', a4'⟩ k8 hk8 => ?_)
  rw [z1, e7w] at a2'
  have e8dV : e8.env dV = dig w nD t (r * J + j) := a2'
  -- A_j
  have e8j : e8.env jI = j := by
    simp (disch := decide) only [a3'.ev, z3.ev, y2.ev, x2.ev, w2.ev, v2'.ev, u2.ev, s2.ev]; exact hj
  have Kp8 : Kp d e8 := Kp.of_same (Same.trans s3 (Same.trans u3 (Same.trans v3' (Same.trans w3 (Same.trans x3
    (Same.trans y3 (Same.trans z4 a4')))))))
  have rc8 : e8.rc = d.rc := (Same.trans s3 (Same.trans u3 (Same.trans v3' (Same.trans w3 (Same.trans x3
    (Same.trans y3 (Same.trans z4 a4'))))))).rc
  have c8 : Cst e8 := cst_of (cst_of (cst_of (cst_of (cst_of c3 w2 (by decide)) x2 (by decide)) y2 (by decide))
    z3 (by decide)) a3' (by decide)
  refine Hs.then (o_fetch sP jI f1 (by decide) (by decide) (by decide) e8 (by rw [e8j, Kp8.ram, i7]; exact hPL)
    (by rw [e8j]; omega)) (fun e9 ⟨b1', b2', b3', b4'⟩ k9 hk9 => ?_)
  rw [e8j, Kp8.ram, i7] at b1'
  have e9i : e9.env iI = r * J + j := by
    simp (disch := decide) only [b2'.ev, a3'.ev, z3.ev, y2.ev, x2.ev, w2.ev, v2'.ev]; exact e2i
  refine Hs.then (o_copy ix iI e9 (by decide)) (fun e10 ⟨c1', c2', c3'⟩ k10 hk10 => ?_)
  rw [e9i] at c1'
  refine Hs.then (o_shl ix e10 (by rw [c1']; omega)) (fun e11 ⟨d1, d2, d3⟩ k11 hk11 => ?_)
  rw [c1'] at d1
  have Kp11 : Kp d e11 := Kp.trans Kp8 (Kp.trans b3' (Kp.of_same (Same.trans c3' d3)))
  have rc9 : RcOK e9 := RcOK.fetch (RcOK.same i9 (Same.trans s3 (Same.trans u3 (Same.trans v3' (Same.trans w3
    (Same.trans x3 (Same.trans y3 (Same.trans z4 a4')))))))) b3' b4' (by rw [e8j, Kp8.ram, i7]; exact hPL)
  have rc11 : RcOK e11 := RcOK.same rc9 (Same.trans c3' d3)
  refine Hs.then (o_fetch sE ix f2 (by decide) (by decide) (by decide) e11 (by rw [d1, Kp11.ram, i8]; omega) (by rw [d1]; omega))
    (fun e12 ⟨g1, g2, g3, g4⟩ k12 hk12 => ?_)
  have rc12 : RcOK e12 := RcOK.fetch rc11 g3 g4 (by rw [d1, Kp11.ram, i8]; omega)
  rw [d1, Kp11.ram, i8] at g1
  have e12x : e12.env ix = 2 * (r * J + j) := by simp (disch := decide) only [g2.ev]; exact d1
  refine Hs.then (o_inc ix e12 (by rw [e12x]; omega)) (fun e13 ⟨h1', h2', h3'⟩ k13 hk13 => ?_)
  rw [e12x] at h1'
  have Kp13 : Kp d e13 := Kp.trans Kp11 (Kp.trans g3 (Kp.of_same h3'))
  have rc13 : RcOK e13 := RcOK.same rc12 h3'
  refine Hs.then (o_fetch sE ix f3 (by decide) (by decide) (by decide) e13 (by rw [h1', Kp13.ram, i8]; exact hEL)
    (by rw [h1']; omega)) (fun e14 ⟨l1, l2, l3, l4⟩ k14 hk14 => ?_)
  have rc14 : RcOK e14 := RcOK.fetch rc13 l3 l4 (by rw [h1', Kp13.ram, i8]; exact hEL)
  rw [h1', Kp13.ram, i8] at l1
  have e14f2 : e14.env f2 = EL.getD (2 * (r * J + j)) 0 := by simp (disch := decide) only [l2.ev, h2'.ev]; exact g1
  refine Hs.then (o_copy q1 f2 e14 (by decide)) (fun e15 ⟨m1, m2, m3⟩ k15 hk15 => ?_)
  rw [e14f2] at m1
  refine Hs.then (o_inc q1 e15 (by rw [m1]; omega)) (fun e16 ⟨n1', n2', n3'⟩ k16 hk16 => ?_)
  rw [m1] at n1'
  have e16d : e16.env dV = dig w nD t (r * J + j) := by
    simp (disch := decide) only [n2'.ev, m2.ev, l2.ev, h2'.ev, g2.ev, d2.ev, c2'.ev, b2'.ev]; exact e8dV
  refine Hs.then (o_add q1 dV e16 (by decide) (by rw [n1', e16d]; omega)) (fun e17 ⟨o1, o2, o3⟩ k17 hk17 => ?_)
  rw [n1', e16d] at o1
  have e17f1 : e17.env f1 = PL.getD j 0 := by
    simp (disch := decide) only [o2.ev, n2'.ev, m2.ev, l2.ev, h2'.ev, g2.ev, d2.ev, c2'.ev]; exact b1'
  refine Hs.then (o_mul f1 q1 q2 e17 (by decide) (by decide) (by decide) (by rw [e17f1, o1]; omega))
    (fun e18 ⟨r1, r2, r3⟩ k18 hk18 => ?_)
  rw [e17f1, o1] at r1
  have e18a : e18.env accP = accPf PL EL r J nD w t j := by
    simp (disch := decide) only [r2.ev, o2.ev, n2'.ev, m2.ev, l2.ev, h2'.ev, g2.ev, d2.ev, c2'.ev, b2'.ev, a3'.ev,
      z3.ev, y2.ev, x2.ev, w2.ev, v2'.ev, u2.ev, s2.ev]; exact ha
  refine Hs.then (o_add accP q2 e18 (by decide) (by rw [e18a, r1, ← hstepP]; omega))
    (fun e19 ⟨t1', t2', t3'⟩ k19 hk19 => ?_)
  rw [e18a, r1, ← hstepP] at t1'
  have e19f3 : e19.env f3 = EL.getD (2 * (r * J + j) + 1) 0 := by
    simp (disch := decide) only [t2'.ev, r2.ev, o2.ev, n2'.ev, m2.ev]; exact l1
  refine Hs.then (o_copy q1 f3 e19 (by decide)) (fun e20 ⟨v1'', v2'', v3''⟩ k20 hk20 => ?_)
  rw [e19f3] at v1''
  have e20h : e20.env vHE = hE := by
    simp (disch := decide) only [v2''.ev, t2'.ev, r2.ev, o2.ev, n2'.ev, m2.ev, l2.ev, h2'.ev, g2.ev, d2.ev, c2'.ev,
      b2'.ev, a3'.ev, z3.ev, y2.ev, x2.ev, w2.ev, v2'.ev, u2.ev, s2.ev]; exact i4
  refine Hs.then (o_add q1 vHE e20 (by decide) (by rw [v1'', e20h]; omega)) (fun e21 ⟨w1', w2', w3'⟩ k21 hk21 => ?_)
  rw [v1'', e20h] at w1'
  have e21f1 : e21.env f1 = PL.getD j 0 := by
    simp (disch := decide) only [w2'.ev, v2''.ev, t2'.ev, r2.ev]; exact e17f1
  refine Hs.then (o_mul f1 q1 q2 e21 (by decide) (by decide) (by decide) (by rw [e21f1, w1']; omega))
    (fun e22 ⟨x1', x2', x3'⟩ k22 hk22 => ?_)
  rw [e21f1, w1'] at x1'
  have e22n : e22.env accN = accNf PL EL r J hE j := by
    simp (disch := decide) only [x2'.ev, w2'.ev, v2''.ev, t2'.ev, r2.ev, o2.ev, n2'.ev, m2.ev, l2.ev, h2'.ev, g2.ev,
      d2.ev, c2'.ev, b2'.ev, a3'.ev, z3.ev, y2.ev, x2.ev, w2.ev, v2'.ev, u2.ev, s2.ev]; exact hb
  refine Hs.last (o_add accN q2 e22 (by decide) (by rw [e22n, x1', ← hstepN]; omega))
    (fun g ⟨y1', y2', y3'⟩ k23 hk23 => ?_)
  rw [e22n, x1', ← hstepN] at y1'
  have FR : Fr d g digT :=
    Fr.trans (s2.weaken (by decide)) (Fr.trans (u2.weaken (by decide)) (Fr.trans (v2'.weaken (by decide)) (Fr.trans (w2.weaken (by decide)) (Fr.trans (x2.weaken (by decide)) (Fr.trans (y2.weaken (by decide)) (Fr.trans (z3.weaken (by decide)) (Fr.trans (a3'.weaken (by decide)) (Fr.trans (b2'.weaken (by decide)) (Fr.trans (c2'.weaken (by decide)) (Fr.trans (d2.weaken (by decide)) (Fr.trans (g2.weaken (by decide)) (Fr.trans (h2'.weaken (by decide)) (Fr.trans (l2.weaken (by decide)) (Fr.trans (m2.weaken (by decide)) (Fr.trans (n2'.weaken (by decide)) (Fr.trans (o2.weaken (by decide)) (Fr.trans (r2.weaken (by decide)) (Fr.trans (t2'.weaken (by decide)) (Fr.trans (v2''.weaken (by decide)) (Fr.trans (w2'.weaken (by decide)) (Fr.trans (x2'.weaken (by decide)) (y2'.weaken (by decide)))))))))))))))))))))))
  have SM : Same e14 g := Same.trans m3 (Same.trans n3' (Same.trans o3 (Same.trans r3 (Same.trans t3'
    (Same.trans v3'' (Same.trans w3' (Same.trans x3' y3')))))))
  have KPg : Kp d g := Kp.trans Kp13 (Kp.trans l3 (Kp.of_same SM))
  have hgv : ∀ y, y ∉ digT → g.env y = d.env y := fun y hy => FR y hy
  refine ⟨⟨by simp (disch := decide) only [y2'.ev, x2'.ev, w2'.ev, v2''.ev]; exact t1', y1',
    ⟨by rw [hgv rI (by decide)]; exact i1, by rw [hgv tI (by decide)]; exact i2, by rw [hgv vJ' (by decide)]; exact i3,
      by rw [hgv vHE (by decide)]; exact i4, by rw [hgv wW (by decide)]; exact i5, by rw [hgv nDg (by decide)]; exact i6,
      by rw [KPg.ram]; exact i7, by rw [KPg.ram]; exact i8, RcOK.same rc14 SM, cst_of i11 FR (by decide)⟩,
    FR, KPg, by rw [hgv jI (by decide)]; exact hj⟩, ?_⟩
  have r8P : e8.rc sP ≤ PL.length := by have := RcOK.same i9 (Same.trans s3 (Same.trans u3 (Same.trans v3'
    (Same.trans w3 (Same.trans x3 (Same.trans y3 (Same.trans z4 a4'))))))) sP; rwa [Kp8.ram, i7] at this
  have r11E : e11.rc sE ≤ EL.length := by have := rc11 sE; rwa [Kp11.ram, i8] at this
  have r13E : e13.rc sE ≤ EL.length := by have := rc13 sE; rwa [Kp13.ram, i8] at this
  rw [e8j] at hk9
  rw [d1] at hk12
  rw [h1'] at hk14
  unfold digCost
  have : nD - 1 - (r * J + j) ≤ nD := by omega
  omega

/-! ## The digit sums of a role -/

def accL : St VV MM := .seq (.op (.zero accP)) (.seq (.op (.zero accN)) (forS jI vJ' digB))

def accT : List (Fin VV) := jI :: digT

def accCost (J nD lP lE : ℕ) : ℕ := J * (digCost nD lP lE + 4) + 10

theorem accL_spec (PL EL : List ℕ) (r t J hE w nD V : ℕ) (d : DS VV MM) (hI : DigI PL EL r t J hE w nD d)
    (hrJ : (r + 1) * J ≤ nD) (hPL : J ≤ PL.length) (hEL : 2 * ((r + 1) * J) ≤ EL.length) (hw1 : 1 ≤ w)
    (hpw : w ^ nD * (w + 1) < 2 ^ C.Wd)
    (hV : ∀ x ∈ PL, x ≤ V) (hVE : ∀ x ∈ EL, x ≤ V) (hEV : hE ≤ V) (hwV : w ≤ V)
    (hbig : (J + 1) * (V * (2 * V + 2)) + EL.length + nD + r * J + J < 2 ^ C.Wd) :
    Hs C accL d (accCost J nD PL.length EL.length) (fun g => g.env accP = accPf PL EL r J nD w t J ∧
      g.env accN = accNf PL EL r J hE J ∧ DigI PL EL r t J hE w nD g ∧ Fr d g accT ∧ Kp d g) := by
  refine Hx.hs (Hs.then (o_zero accP d) (fun e1 ⟨p1, p2, p3⟩ k1 hk1 => ?_))
  refine Hs.then (o_zero accN e1) (fun e2 ⟨q1, q2, q3⟩ k2 hk2 => ?_)
  have S2 : Same d e2 := Same.trans p3 q3
  have F2 : Fr d e2 accT := Fr.trans (p2.weaken (by decide)) (q2.weaken (by decide))
  have hI2 : DigI PL EL r t J hE w nD e2 := by
    obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8, i9, i11⟩ := hI
    exact ⟨by rw [F2 rI (by decide)]; exact i1, by rw [F2 tI (by decide)]; exact i2, by rw [F2 vJ' (by decide)]; exact i3,
      by rw [F2 vHE (by decide)]; exact i4, by rw [F2 wW (by decide)]; exact i5, by rw [F2 nDg (by decide)]; exact i6,
      by rw [S2.ram]; exact i7, by rw [S2.ram]; exact i8, RcOK.same i9 S2, cst_of i11 F2 (by decide)⟩
  let I : ℕ → DS VV MM → Prop := fun k e => e.env accP = accPf PL EL r J nD w t k ∧ e.env accN = accNf PL EL r J hE k ∧
    DigI PL EL r t J hE w nD e ∧ Fr d e accT ∧ Kp d e
  have hl := forS_spec' (C := C) jI vJ' (by decide) digB e2 J (by omega) I (digCost nD PL.length EL.length)
    (fun k e v ⟨i1, i2, ⟨j1, j2, j3, j4, j5, j6, j7, j8, j9, j11⟩, i4, i5⟩ =>
      ⟨by rw [DS.set_env_ne _ _ (by decide)]; exact i1, by rw [DS.set_env_ne _ _ (by decide)]; exact i2,
        ⟨by rw [DS.set_env_ne _ _ (by decide)]; exact j1, by rw [DS.set_env_ne _ _ (by decide)]; exact j2,
          by rw [DS.set_env_ne _ _ (by decide)]; exact j3, by rw [DS.set_env_ne _ _ (by decide)]; exact j4,
          by rw [DS.set_env_ne _ _ (by decide)]; exact j5, by rw [DS.set_env_ne _ _ (by decide)]; exact j6, j7, j8,
          RcOK.same j9 (Same.set e jI v), cst_of j11 (Fr.set e v (x := jI) (T := [jI]) (by simp)) (by decide)⟩,
        Fr.trans i4 (Fr.set e v (by decide)), Kp.trans i5 (Kp.of_same (Same.set e jI v))⟩)
    ⟨by rw [show e2.env accP = 0 by simp (disch := decide) only [q2.ev]; exact p1]; simp [accPf],
      by rw [q1]; simp [accNf], hI2, F2, Kp.of_same S2⟩
    (by rw [hI2.J]) (fun k hk e ⟨i1, i2, i3, i4, i5⟩ hek hem => by
      have hkJ : k < J := hk
      refine Hs.mono (digB_spec PL EL r t J hE w nD V k e i3 hek hkJ (by nlinarith) (by omega) (by nlinarith) hw1 hpw
        hV hVE hEV hwV hbig i1 i2) le_rfl ?_
      rintro g ⟨g1, g2, g3, g4, g5, g6⟩
      exact ⟨⟨g1, g2, g3, Fr.trans i4 (g4.weaken (by decide)), Kp.trans i5 g5⟩, g6,
        by rw [g4 vJ' (by decide)]; exact hem⟩)
  refine Hs.last hl (fun g ⟨⟨g1, g2, g3, g4, g5⟩, _, _⟩ k3 hk3 => ⟨⟨g1, g2, g3, g4, g5⟩, ?_⟩)
  unfold accCost
  omega

end NearCubicGates.Close.Cells.SystemsPhase
