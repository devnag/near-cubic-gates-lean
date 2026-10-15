import Proof.Gates.Dispatch.WitnessK

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxRecDepth 4000

namespace NearCubicGates.Close.Dispatch

open NearCubicGates NearCubicGates.Close.Counter NearCubicWires NearCubicWires.RepairRepresentation
  NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats

variable {C : Ctx}

def witCheck : St VV :=
  .seq (.op (.copy vWF v1)) (.seq (.op (.zero vBM)) (.seq coordsW (.seq setNR (.seq (.op (.zero xSum))
  (.seq (allW skipS lcAct) (.seq (.op (.copy xLC xSum)) (.seq (rdBits xLC vPK)
  (.seq (.op (.copy xRem vPK)) (allW skipS chkAct)))))))))

def witPrint : St VV := .seq coordPrint (.seq setNR (.seq (.op (.copy xRem vPK)) (allW emitNat prAct)))

/-- The cost class (both programs). -/
def witCost (L : ℕ) : ℕ := 10000 * (L + 10) ^ 3

/-! ## Cost arithmetic -/

theorem roleCost_le (L tp ta : ℕ) (htp : tp ≤ 100 * (L + 10)) (hta : ta ≤ 200 * (L + 10)) :
    roleCost L tp ta ≤ 400 * (L + 10) ^ 2 := by
  unfold roleCost
  have h1 : L * (70 * L + ta + 120) ≤ (L + 10) * (300 * (L + 10)) := Nat.mul_le_mul (by omega) (by omega)
  nlinarith

theorem allW_cost_le (L J R tp ta : ℕ) (hJ : J ≤ L + 1) (hR : R ≤ 2) (htp : tp ≤ 100 * (L + 10))
    (hta : ta ≤ 200 * (L + 10)) : J * (R * (roleCost L tp ta + 5) + 8) + 4 ≤ 1000 * (L + 10) ^ 3 := by
  have h1 := roleCost_le L tp ta htp hta
  have h2 : R * (roleCost L tp ta + 5) + 8 ≤ 2 * (400 * (L + 10) ^ 2 + 5) + 8 :=
    by have := Nat.mul_le_mul hR (show roleCost L tp ta + 5 ≤ 400 * (L + 10) ^ 2 + 5 by omega); omega
  have h3 : J * (R * (roleCost L tp ta + 5) + 8) ≤ (L + 10) * (2 * (400 * (L + 10) ^ 2 + 5) + 8) :=
    Nat.mul_le_mul (by omega) h2
  have h4 : (L + 10) * (2 * (400 * (L + 10) ^ 2 + 5) + 8) = 800 * (L + 10) ^ 3 + 18 * (L + 10) := by ring
  have h5 : 18 * (L + 10) + 4 ≤ 200 * (L + 10) ^ 3 := by nlinarith
  omega

theorem wd_facts (L Wd : ℕ) (hwd : 4000 * (L + 4) ^ 2 ≤ Wd) :
    L + 8 ≤ Wd ∧ 2 ^ (L + 2) ≤ 2 ^ Wd ∧ (L + 1) * L + 2 ≤ Wd ∧ L + 3 < 2 ^ Wd := by
  have h1 : L + 8 ≤ Wd := by nlinarith
  have h2 : 2 ^ (L + 2) ≤ 2 ^ Wd := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : (L + 1) * L + 2 ≤ Wd := by nlinarith
  have h4 : L + 3 < 2 ^ Wd := lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.pow_le_pow_right (by norm_num) (by omega))
  exact ⟨h1, h2, h3, h4⟩

theorem coPos0 (c : Call) (b : DS VV) (h : ParseOut c b) : b.env vCO1 = coPos c 0 := by
  rw [h.c1.co]; simp [coPos]

theorem coPos1 (c : Call) (b : DS VV) (h : ParseOut c b) : b.env vCO2 = coPos c 1 := by
  rw [h.c2.co]; simp [coPos]

/-! ## `witCheck` -/

theorem witCheck_spec (c : Call) (p : Params) (a : DS VV) (hP : WitPre C c p a) (hq : a.wq = 0) :
    Hs C witCheck a (witCost C.cw.length) (fun b => b.env vWF = bnat ((decodeWitness c p C.wit).isSome = true) ∧
      b.out = a.out ∧ Cst b ∧ Fr a b wT ∧ ((decodeWitness c p C.wit).isSome = true →
        b.env vBM = bitsValue (maskOf c.n (cl C.wit (Target.lambda c.n) p.k)) ∧ b.env vPK = bitsValue (L0 c p C.wit))) := by
  obtain ⟨hW8, hL2, hLL, hL3⟩ := wd_facts C.cw.length C.Wd hP.wd
  have hc := hP.cst
  have hnL := hP.nL
  have hkn := hP.kn
  have hJn := hP.Jn
  have hlam : Target.lambda c.n ≤ c.n := clog_le_self c.n
  have hR2 : roleCount c.kind ≤ 2 := by cases c.kind <;> simp [roleCount]
  have hLC : LCof c p ≤ (C.cw.length + 1) * C.cw.length := (LCof_le c p).trans (by rw [← hP.cw]; exact Nat.mul_le_mul_right _ (by omega))
  have hWbig : (C.cw.length + 1) * C.cw.length + 2 < 2 ^ C.Wd := lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by norm_num) hLL)
  refine Hx.hs (Hs.then (hs_copy C vWF v1 a (by decide)) (fun a1 ha1 n1 hn1 => ?_))
  subst ha1
  refine Hs.then (hs_zero C vBM _) (fun a2 ha2 n2 hn2 => ?_)
  subst ha2
  set a2 := (a.set vWF (a.env v1)).set vBM 0 with ha2d
  have a2fr : Fr a a2 wT := Fr.trans (Fr.set a _ (by decide)) (Fr.set _ _ (by decide))
  have a2c : Cst a2 := Cst.of_fr hc a2fr (by decide) (by vsimp [ha2d, hc.pos])
  have hv : ∀ y : Fin VV, y ∉ wT → a2.env y = a.env y := a2fr
  refine Hs.then (coordsW_spec a2 a2c c.n (Target.lambda c.n) p.k (by simp [ha2d, hq])
    (by rw [hv pLAM (by decide), hP.lam]) (by rw [hv vN (by decide), hP.parse.n]) (by rw [hv pK (by decide), hP.k])
    (by vsimp [ha2d]) (by vsimp [ha2d, hc.one]) (by omega) (by omega) (by omega))
    (fun a3 ⟨ml, h31, h32, h33, h34, h35, h36, h37, h38, h39⟩ n3 hn3 => ?_)
  have a3fr : Fr a a3 wT := Fr.trans a2fr (Fr.weaken h39 (by decide))
  refine Hs.then (setNR_spec a3 h38 c (by rw [a3fr vTAG (by decide), hP.parse.tag]) (by omega))
    (fun a4 ⟨h41, h42, h43, h44, h45, h46⟩ n4 hn4 => ?_)
  refine Hs.then (hs_zero C xSum a4) (fun a5 ha5 n5 hn5 => ?_)
  subst ha5
  have a5fr : Fr a (a4.set xSum 0) wT := Fr.trans a3fr (Fr.trans (Fr.weaken h46 (by decide)) (Fr.set _ _ (by decide)))
  have a5c : Cst (a4.set xSum 0) := Cst.of_fr h45 (Fr.set a4 _ (show xSum ∈ [xSum] by decide)) (by decide)
    (by vsimp [h45.pos])
  refine Hs.then (lcW_spec c p (a4.set xSum 0) a5c hP.cw (by rw [a5fr vCO1 (by decide)]; exact coPos0 c a hP.parse)
    (by rw [a5fr vCO2 (by decide)]; exact coPos1 c a hP.parse) (by vsimp [h41])
    (by rw [a5fr pJ (by decide), hP.J]) (by vsimp []) (by omega) hL2 (by omega) (by omega))
    (fun a6 ⟨h61, h62, h63, h64, h65⟩ n6 hn6 => ?_)
  refine Hs.then (hs_copy C xLC xSum a6 (by decide)) (fun a7 ha7 n7 hn7 => ?_)
  subst ha7
  have a7c : Cst (a6.set xLC (a6.env xSum)) := Cst.of_fr h64 (Fr.set a6 _ (show xLC ∈ [xLC] by decide)) (by decide)
    (by vsimp [h64.pos])
  have hwq7 : (a6.set xLC (a6.env xSum)).wq = min (p.k * Target.lambda c.n) C.wit.length := by
    simp [h62, h43, h35]
  refine Hs.then (rdBits_spec xLC vPK (Or.inr ⟨rfl, rfl⟩) _ a7c (p.k * Target.lambda c.n) (LCof c p) hwq7
    (by vsimp [h61]) (by omega)) (fun a8 ⟨h81, h82, h83, h84, h85, h86⟩ n8 hn8 => ?_)
  refine Hs.then (hs_copy C xRem vPK a8 (by decide)) (fun a9 ha9 n9 hn9 => ?_)
  subst ha9
  have a9c : Cst (a8.set xRem (a8.env vPK)) := Cst.of_fr h85 (Fr.set a8 _ (show xRem ∈ [xRem] by decide)) (by decide)
    (by vsimp [h85.pos])
  have a9fr : Fr a (a8.set xRem (a8.env vPK)) wT := Fr.trans a5fr (Fr.trans (Fr.weaken h65 (by decide))
    (Fr.trans (Fr.set _ _ (by decide)) (Fr.trans (Fr.weaken h86 (by decide)) (Fr.set _ _ (by decide)))))
  have hWF9 : (a8.set xRem (a8.env vPK)).env vWF = bnat (goodC c.n (cl C.wit (Target.lambda c.n) p.k)) := by
    vsimp [h86 vWF (by decide), h65 vWF (by decide), h46 vWF (by decide), h33]
  refine Hs.last (chkW_spec c p (goodC c.n (cl C.wit (Target.lambda c.n) p.k)) _ a9c hP.cw
    (by rw [a9fr vCO1 (by decide)]; exact coPos0 c a hP.parse) (by rw [a9fr vCO2 (by decide)]; exact coPos1 c a hP.parse)
    (by vsimp [h86 xNR (by decide), h65 xNR (by decide), h41])
    (by rw [a9fr pJ (by decide), hP.J]) (by vsimp [h81]; rfl) hWF9 (by omega) hL2 (by omega))
    (fun b ⟨b1, b2, b3, b4, b5⟩ n10 hn10 => ?_)
  have hiff := decode_isSome_iff c p C.wit
  refine ⟨⟨?_, ?_, b4, Fr.trans a9fr (Fr.weaken b5 (by decide)), fun hs => ⟨?_, ?_⟩⟩, ?_⟩
  · rw [b1]; unfold bnat; congr 1; exact decide_eq_decide.mpr hiff.symm
  · rw [b3]; simp [h84, h63, h44, h37, ha2d]
  · rw [b5 vBM (by decide)]; vsimp [h86 vBM (by decide), h65 vBM (by decide), h46 vBM (by decide), h32]
    rw [h34 (hiff.mp hs).1]
  · rw [b5 vPK (by decide)]; vsimp [h81]; rfl
  · -- the cost
    have hc3 : p.k * (10 * Target.lambda c.n + 7 * c.n + 45) ≤ 17 * (C.cw.length + 10) ^ 2 := by
      calc p.k * (10 * Target.lambda c.n + 7 * c.n + 45) ≤ (C.cw.length + 10) * (17 * (C.cw.length + 10)) :=
            Nat.mul_le_mul (by omega) (by omega)
        _ = 17 * (C.cw.length + 10) ^ 2 := by ring
    have hc6 := allW_cost_le C.cw.length p.J (roleCount c.kind) 1 1 (by omega) hR2 (by omega) (by omega)
    have hc10 := allW_cost_le C.cw.length p.J (roleCount c.kind) 1 (14 * C.cw.length + 50) (by omega) hR2 (by omega) (by omega)
    have hc8 : LCof c p ≤ (C.cw.length + 10) ^ 2 := hLC.trans (by
      calc (C.cw.length + 1) * C.cw.length ≤ (C.cw.length + 10) * (C.cw.length + 10) := Nat.mul_le_mul (by omega) (by omega)
        _ = (C.cw.length + 10) ^ 2 := by ring)
    have hX : 100 ≤ (C.cw.length + 10) ^ 2 := by
      have := Nat.pow_le_pow_left (show 10 ≤ C.cw.length + 10 by omega) 2; simpa using this
    have hY : 10 * (C.cw.length + 10) ^ 2 ≤ (C.cw.length + 10) ^ 3 := by
      calc 10 * (C.cw.length + 10) ^ 2 ≤ (C.cw.length + 10) * (C.cw.length + 10) ^ 2 := Nat.mul_le_mul_right _ (by omega)
        _ = (C.cw.length + 10) ^ 3 := by ring
    unfold witCost
    clear * - hn1 hn2 hn3 hn4 hn5 hn6 hn7 hn8 hn9 hn10 hc3 hc6 hc10 hc8 hX hY
    omega

/-! ## `witPrint` -/

theorem witPrint_spec (c : Call) (p : Params) (wt : Wit c.n) (hdec : decodeWitness c p C.wit = some wt) (b : DS VV)
    (hP : WitPre C c p b) (hBM : b.env vBM = bitsValue (maskOf c.n (cl C.wit (Target.lambda c.n) p.k)))
    (hPK : b.env vPK = bitsValue (L0 c p C.wit)) :
    Hs C witPrint b (witCost C.cw.length) (fun d => d.out = b.out ++ witWord c p wt ∧ Cst d ∧ Fr b d wT) := by
  obtain ⟨hW8, hL2, hLL, hL3⟩ := wd_facts C.cw.length C.Wd hP.wd
  have hc := hP.cst
  have hnL := hP.nL
  have hkn := hP.kn
  have hJn := hP.Jn
  have hR2 : roleCount c.kind ≤ 2 := by cases c.kind <;> simp [roleCount]
  have hkW : natBitLength p.k + 2 < 2 ^ C.Wd := by have := natBitLength_le_succ p.k; omega
  refine Hx.hs (Hs.then (coordPrint_spec b hc c.n p.k _ (maskOf_length _ _) hP.k hP.parse.n hBM (by omega) hkW)
    (fun d1 ⟨h11, h12, h13, h14, h15⟩ n1 hn1 => ?_))
  have d1fr : Fr b d1 wT := Fr.weaken h15 (by decide)
  refine Hs.then (setNR_spec d1 h14 c (by rw [d1fr vTAG (by decide), hP.parse.tag]) (by omega))
    (fun d2 ⟨h21, h22, h23, h24, h25, h26⟩ n2 hn2 => ?_)
  refine Hs.then (hs_copy C xRem vPK d2 (by decide)) (fun d3 hd3 n3 hn3 => ?_)
  subst hd3
  have d3fr : Fr b (d2.set xRem (d2.env vPK)) wT := Fr.trans d1fr (Fr.trans (Fr.weaken h26 (by decide))
    (Fr.set _ _ (by decide)))
  have d3c : Cst (d2.set xRem (d2.env vPK)) := Cst.of_fr h25 (Fr.set d2 _ (show xRem ∈ [xRem] by decide)) (by decide)
    (by vsimp [h25.pos])
  refine Hs.last (prW_spec c p _ d3c hP.cw (by rw [d3fr vCO1 (by decide)]; exact coPos0 c b hP.parse)
    (by rw [d3fr vCO2 (by decide)]; exact coPos1 c b hP.parse) (by vsimp [h21])
    (by rw [d3fr pJ (by decide), hP.J]) (by vsimp [h26 vPK (by decide), h15 vPK (by decide), hPK]) (by omega) hL2
    (by omega)) (fun e ⟨e1, e2, e3, e4⟩ n4 hn4 => ?_)
  refine ⟨⟨?_, e3, Fr.trans d3fr (Fr.weaken e4 (by decide))⟩, ?_⟩
  · rw [e1, witWord_eq c p C.wit wt hdec]; simp [h24, h11, List.append_assoc]
  · have hc1 : 40 * natBitLength p.k + 50 + c.n * (40 * c.n + 110) + 10 ≤ 200 * (C.cw.length + 10) ^ 2 := by
      have h1 : c.n * (40 * c.n + 110) ≤ (C.cw.length + 10) * (150 * (C.cw.length + 10)) := Nat.mul_le_mul (by omega)
        (by omega)
      have h2 : (C.cw.length + 10) * (150 * (C.cw.length + 10)) = 150 * (C.cw.length + 10) ^ 2 := by ring
      have h3 : 40 * natBitLength p.k + 60 ≤ 50 * (C.cw.length + 10) ^ 2 := by
        have := natBitLength_le_succ p.k
        have h4 : C.cw.length + 10 ≤ (C.cw.length + 10) ^ 2 := by nlinarith
        omega
      omega
    have hc4 := allW_cost_le C.cw.length p.J (roleCount c.kind) (40 * C.cw.length + 80) (100 * C.cw.length + 400)
      (by omega) hR2 (by omega) (by omega)
    have hY : 10 * (C.cw.length + 10) ^ 2 ≤ (C.cw.length + 10) ^ 3 := by
      calc 10 * (C.cw.length + 10) ^ 2 ≤ (C.cw.length + 10) * (C.cw.length + 10) ^ 2 := Nat.mul_le_mul_right _ (by omega)
        _ = (C.cw.length + 10) ^ 3 := by ring
    unfold witCost
    clear * - hn1 hn2 hn3 hn4 hc1 hc4 hY
    omega

/-! ## The fragment -/

theorem frW_of (a b : DS VV) (h : Fr a b wT) : FrW a b := fun y _ hy => h y (fun hm => hy (wT_witVar y hm))

theorem witCost_poly : ∃ K e : ℕ, ∀ L, witCost L ≤ K * (L + 1) ^ e := by
  refine ⟨10000000, 3, fun L => ?_⟩
  unfold witCost
  have h : (L + 10) ^ 3 ≤ (10 * (L + 1)) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have h2 : (10 * (L + 1)) ^ 3 = 1000 * (L + 1) ^ 3 := by ring
  omega

def witFrag : WitFrag where
  check := witCheck
  print := witPrint
  cost := witCost
  cost_poly := witCost_poly
  spec := fun C c p a hP hq => by
    refine Hs.mono (witCheck_spec c p a hP hq) le_rfl ?_
    rintro b ⟨b1, b2, b3, b4, b5⟩
    refine ⟨b1, b2, b3, frW_of a b b4, fun wt hdec b' hP' hag => ?_⟩
    obtain ⟨hBM, hPK⟩ := b5 (by rw [hdec]; rfl)
    refine Hs.mono (witPrint_spec c p wt hdec b' hP' (by rw [hag vBM (by decide) (by decide)]; exact hBM)
      (by rw [hag vPK (by decide) (by decide)]; exact hPK)) le_rfl ?_
    rintro d ⟨d1, d2, d3⟩
    exact ⟨d1, d2, frW_of b' d d3⟩

end NearCubicGates.Close.Dispatch
