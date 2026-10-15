import Proof.Gates.Expand.Cost6

set_option autoImplicit false

namespace NearCubicGates.Close.Expand.Layout

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.UnionMachine.RegRat (mulCost)
open NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Expand

theorem core_le' (r : FormulaReq) (v p m : ℕ) (hv2 : 2 ≤ v) (hp1 : 1 ≤ p) (hm1 : 1 ≤ m)
    (fL : (formulaWord r).length ≤ p) (fD : r.2.degree ≤ p) (fN : (toks r.2).length ≤ p) (fV : r.1 + 2 = v)
    (ffam : (fam r.1 r.2.degree).length ≤ m) (fwb2 : Wb2 r + 1 ≤ 40 * (v ^ 1 * p ^ 2))
    (fwb2a : Wb2 r + tokBits r.2 + 2 ≤ 41 * (v ^ 1 * p ^ 2))
    (fhE : maxExp r.2 + tokBits r.2 + r.1 + 2 ≤ 2 * (v * p))
    (fT : (termsWord (expandM r.2)).length ≤ 40 * (m * v * p ^ 2)) :
    coreCost r (Wt r) (Wb2 r) ≤ 10 ^ 10 * (m ^ 2 * v ^ 3 * p ^ 8) := by
  have mk := fun (K a b c x : ℕ) (ha : a ≤ 2) (hb : b ≤ 3) (hc : c ≤ 8) (hx : x ≤ K * (m ^ a * v ^ b * p ^ c)) =>
    monoK hv2 hp1 hm1 K a b c x ha hb hc hx
  set Z := m ^ 2 * v ^ 3 * p ^ 8 with hZd
  have w2 : Wb2 r + 1 ≤ 40 * (v * p ^ 2) := by simpa using fwb2
  have w2sq : (Wb2 r + 1) ^ 2 ≤ 1600 * (v ^ 2 * p ^ 4) := by
    have t : (Wb2 r + 1) ^ 2 ≤ (40 * (v * p ^ 2)) ^ 2 := Nat.pow_le_pow_left w2 2
    have e : (40 * (v * p ^ 2)) ^ 2 = 1600 * (v ^ 2 * p ^ 4) := by ring
    omega
  have hF : (famRecs r.1 r.2.degree).length ≤ m := by rw [famRecs_length]; exact ffam
  have horc : (orcRecs r.1 (Wt r) ((famRecs r.1 r.2.degree).map (valRec r.1 (Wt r) r.2))
      (famRecs r.1 r.2.degree)).length ≤ m := by
    unfold orcRecs; exact le_trans (List.length_filterMap_le _ _) hF
  -- the family
  have c1 : famPhaseCost (Wb2 r) r.1 r.2.degree (fam r.1 r.2.degree).length ≤ 320000 * Z :=
    mk 320000 1 2 3 _ (by omega) (by omega) (by omega) (by
      have h := famPhaseC (Wb2 r) r.1 r.2.degree (fam r.1 r.2.degree).length
      have t : 2000 * (Wb2 r + 1) * (r.1 + 1) * ((fam r.1 r.2.degree).length + 1) * (r.2.degree + 1) ≤
          2000 * (40 * (v * p ^ 2)) * v * (2 * m) * (2 * p) := by gcongr <;> omega
      have e : 2000 * (40 * (v * p ^ 2)) * v * (2 * m) * (2 * p) = 320000 * (m ^ 1 * v ^ 2 * p ^ 3) := by ring
      exact le_trans h (le_trans t (le_of_eq e)))
  -- the values
  have hc : hcost (Wb2 r) (tokBits r.2) (maxExp r.2) r.1 ≤ 16810000 * (v ^ 3 * p ^ 5) := by
    have := hcost_le (v := v) (p := p) (Wb2 r) (tokBits r.2) (maxExp r.2) r.1 41 1 fwb2a fhE
    simpa using this
  have ev := eval_le hv2 hp1 (Wb2 r) _ r.1 (toks r.2).length (formulaWord r).length 16810000 1 3 hc fwb2
    (by omega) fN fL (by omega) (by omega)
  have c2 : valPhaseCost (Wb2 r) (fam r.1 r.2.degree).length (valBodyCost (Wb2 r) (evalCost (Wb2 r)
      (hcost (Wb2 r) (tokBits r.2) (maxExp r.2) r.1) r.1 (toks r.2).length (formulaWord r).length)) ≤
      80000000 * Z := mk 80000000 1 3 6 _ (by omega) (by omega) (by omega) (by
    have h1 := valPhaseC (Wb2 r) (fam r.1 r.2.degree).length (valBodyCost (Wb2 r) (evalCost (Wb2 r)
      (hcost (Wb2 r) (tokBits r.2) (maxExp r.2) r.1) r.1 (toks r.2).length (formulaWord r).length))
    have h2 := valBodyC (Wb2 r) (evalCost (Wb2 r) (hcost (Wb2 r) (tokBits r.2) (maxExp r.2) r.1) r.1
      (toks r.2).length (formulaWord r).length)
    have u1 : v ^ 2 * p ^ 4 ≤ v ^ 3 * p ^ 6 :=
      Nat.mul_le_mul (Nat.pow_le_pow_right (by omega) (by omega)) (pk_le hp1 4 6 (by omega))
    have u2 : v * p ^ 2 ≤ v ^ 3 * p ^ 6 :=
      Nat.mul_le_mul (by calc v = v ^ 1 := (pow_one v).symm
        _ ≤ v ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)) (pk_le hp1 2 6 (by omega))
    have inner : valBodyCost (Wb2 r) (evalCost (Wb2 r) (hcost (Wb2 r) (tokBits r.2) (maxExp r.2) r.1) r.1
        (toks r.2).length (formulaWord r).length) + 100 * (Wb2 r + 1) ≤ 40000000 * (v ^ 3 * p ^ 6) := by
      have : 100 * (Wb2 r + 1) ≤ 4000 * (v * p ^ 2) := by omega
      have : 500 * (Wb2 r + 1) ^ 2 ≤ 800000 * (v ^ 2 * p ^ 4) := by omega
      omega
    calc _ ≤ ((fam r.1 r.2.degree).length + 1) * (valBodyCost (Wb2 r) _ + 100 * (Wb2 r + 1)) := h1
      _ ≤ (2 * m) * (40000000 * (v ^ 3 * p ^ 6)) := Nat.mul_le_mul (by omega) inner
      _ = 80000000 * (m ^ 1 * v ^ 3 * p ^ 6) := by ring)
  -- the Möbius sums
  have c3 : mobPhaseCost (Wb2 r) ((famRecs r.1 r.2.degree).map (valRec r.1 (Wt r) r.2)).length
      (famRecs r.1 r.2.degree).length ≤ 20000000 * Z := mk 20000000 2 2 4 _ (by omega) (by omega) (by omega) (by
    have h := mobPhaseC (Wb2 r) ((famRecs r.1 r.2.degree).map (valRec r.1 (Wt r) r.2)).length
      (famRecs r.1 r.2.degree).length
    have hl : ((famRecs r.1 r.2.degree).map (valRec r.1 (Wt r) r.2)).length + 1 ≤ 2 * m := by
      rw [List.length_map]; omega
    calc _ ≤ 3000 * (Wb2 r + 1) ^ 2 * (((famRecs r.1 r.2.degree).map (valRec r.1 (Wt r) r.2)).length + 1) *
          ((famRecs r.1 r.2.degree).length + 1) := h
      _ ≤ 3000 * (1600 * (v ^ 2 * p ^ 4)) * (2 * m) * (2 * m) := by gcongr; omega
      _ = 19200000 * (m ^ 2 * v ^ 2 * p ^ 4) := by ring
      _ ≤ 20000000 * (m ^ 2 * v ^ 2 * p ^ 4) := Nat.mul_le_mul_right _ (by norm_num))
  -- the printer
  have c4 : printCost (Wb2 r) r.1 (orcRecs r.1 (Wt r) ((famRecs r.1 r.2.degree).map (valRec r.1 (Wt r) r.2))
      (famRecs r.1 r.2.degree)).length (termsWord (expandM r.2)).length ≤ 10000000 * Z :=
    mk 10000000 1 3 4 _ (by omega) (by omega) (by omega) (by
      have h := printC (Wb2 r) r.1 (orcRecs r.1 (Wt r) ((famRecs r.1 r.2.degree).map (valRec r.1 (Wt r) r.2))
        (famRecs r.1 r.2.degree)).length (termsWord (expandM r.2)).length
      have t : 3000 * (Wb2 r + 1) ^ 2 * (r.1 + 1) * ((orcRecs r.1 (Wt r)
          ((famRecs r.1 r.2.degree).map (valRec r.1 (Wt r) r.2)) (famRecs r.1 r.2.degree)).length + 1) ≤
          3000 * (1600 * (v ^ 2 * p ^ 4)) * v * (2 * m) := by gcongr <;> omega
      have e : 3000 * (1600 * (v ^ 2 * p ^ 4)) * v * (2 * m) = 9600000 * (m ^ 1 * v ^ 3 * p ^ 4) := by ring
      have u : m * v * p ^ 2 ≤ m ^ 1 * v ^ 3 * p ^ 4 := by
        rw [pow_one]
        exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (by nlinarith)) (pk_le hp1 2 4 (by omega))
      calc _ ≤ 3000 * (Wb2 r + 1) ^ 2 * (r.1 + 1) * ((orcRecs r.1 (Wt r)
            ((famRecs r.1 r.2.degree).map (valRec r.1 (Wt r) r.2)) (famRecs r.1 r.2.degree)).length + 1) +
            5 * (termsWord (expandM r.2)).length := h
        _ ≤ 9600000 * (m ^ 1 * v ^ 3 * p ^ 4) + 5 * (40 * (m * v * p ^ 2)) := by rw [← e]; gcongr
        _ ≤ 10000000 * (m ^ 1 * v ^ 3 * p ^ 4) := by omega)
  have hZ : 1 ≤ Z := Nat.one_le_iff_ne_zero.mpr (by positivity)
  unfold coreCost
  omega

theorem core_le (r : FormulaReq) : coreCost r (Wt r) (Wb2 r) ≤ 10 ^ 10 * Zq r :=
  let f := facts r
  core_le' r (Vq r) (Pq r) (Mq r) f.v2 f.p1 f.m1 f.L f.D f.N f.V f.fam f.wb2 f.wb2a f.hE f.T

end NearCubicGates.Close.Expand.Layout
