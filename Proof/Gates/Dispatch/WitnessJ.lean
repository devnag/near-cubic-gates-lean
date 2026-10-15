import Proof.Gates.Dispatch.WitnessI

/-!
# Fragment (W), part J: printing the coefficients (`listWord intWord` per stage and role, `coefOf a v = v − |a|`)
-/

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

/-- Coefficient `i` of segment `g`. -/
def segCoef (c : Call) (p : Params) (w : List Bool) (g i : ℕ) : ℤ :=
  (fieldV c p w g i : ℤ) - ((circ c (g % roleCount c.kind)).coeffs.getD i 0).natAbs

/-- The printed words of segment `g`. -/
def segOut (c : Call) (p : Params) (w : List Bool) (g : ℕ) : List Bool :=
  listWord Interfaces.intWord ((List.range (circ c (g % roleCount c.kind)).coeffs.length).map (segCoef c p w g))

def prAct : St VV :=
  .seq extractW (.ite (.lt xV xA)
    (.seq (.op (.copy t3 v1)) (.seq emitNat (.seq (.op (.copy t3 xA)) (.seq (.op (.sub t3 xV)) emitNat))))
    (.seq (.op (.copy t3 vZ)) (.seq emitNat (.seq (.op (.copy t3 xV)) (.seq (.op (.sub t3 xA)) emitNat)))))

def prActT : List (Fin VV) := [xV, xP, xC, xQ, xR, xRem, vJ, t3, t5, t6, t7, t8, t9]

def prWT : List (Fin VV) := [vJ, vPOS, t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, xS, xRo, xM, xIc, xA, xT2, xW, xP, xV,
  xC, xQ, xR, xRem]

theorem intWord_sub (v A : ℕ) : Interfaces.intWord ((v : ℤ) - A) =
    if v < A then natWord 1 ++ natWord (A - v) else natWord 0 ++ natWord (v - A) := by
  unfold Interfaces.intWord
  split_ifs with h1 h2 h2
  · congr 2; omega
  · omega
  · omega
  · congr 2; omega

theorem nbl_lt_of_lt (x B : ℕ) (h : x < 2 ^ B) : natBitLength x ≤ B + 1 := by
  have := natBitLength_le_succ x
  by_cases hB : 1 ≤ B
  · exact ((natBitLength_le_iff x B hB).mpr h).trans (by omega)
  · have : B = 0 := by omega
    subst this; simp at h; subst h; simp [natBitLength]

/-- Printing one coefficient: `intWord (v − |a|)`. -/
theorem prAct_print (a : DS VV) (hc : Cst a) (v A : ℕ) (hv : a.env xV = v) (hA : a.env xA = A) (B : ℕ)
    (hvB : v < 2 ^ B) (hAB : A < 2 ^ B) (hW : B + 6 ≤ C.Wd) :
    Hs C (.ite (.lt xV xA)
      (.seq (.op (.copy t3 v1)) (.seq emitNat (.seq (.op (.copy t3 xA)) (.seq (.op (.sub t3 xV)) emitNat))))
      (.seq (.op (.copy t3 vZ)) (.seq emitNat (.seq (.op (.copy t3 xV)) (.seq (.op (.sub t3 xA)) emitNat))))) a
      (80 * B + 200) (fun b => b.out = a.out ++ Interfaces.intWord ((v : ℤ) - A) ∧ b.cp = a.cp ∧ b.wq = a.wq ∧ Cst b ∧
        Fr a b [t3, t5, t6, t7, t8, t9, vJ]) := by
  have hpw : ∀ x, x < 2 ^ B → natBitLength x + 2 < 2 ^ C.Wd := fun x hx => by
    have h1 := nbl_lt_of_lt x B hx
    have h2 : B + 3 < 2 ^ (B + 3) := Nat.lt_two_pow_self
    have h3 : 2 ^ (B + 3) ≤ 2 ^ C.Wd := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h1B : (1 : ℕ) < 2 ^ B ∨ B = 0 := by
    rcases Nat.eq_zero_or_pos B with h | h
    · right; exact h
    · left; exact Nat.one_lt_two_pow (by omega)
  have hnb : ∀ x, x < 2 ^ B → 40 * natBitLength x + 40 ≤ 40 * B + 80 := fun x hx => by
    have := nbl_lt_of_lt x B hx; omega
  rw [intWord_sub]
  refine Hs.ite (c := .lt xV xA) (show xV ≠ xA by decide) (fun he => ?_) (fun he => ?_)
  · have hlt : v < A := by simp only [Cnd.eval, decide_eq_true_eq] at he; rwa [hv, hA] at he
    rw [if_pos hlt]
    refine Hs.mono (Hs.seq (t1 := 1) (t2 := 40 * B + 80 + (1 + (1 + (40 * B + 80) + 1) + 1) + 1) (hs_copy C t3 v1 a (by decide))
      (fun b hb => ?_)) (by omega) (fun _ h => h)
    subst hb
    have bc : Cst (a.set t3 (a.env v1)) := Cst.of_fr hc (Fr.set a _ (show t3 ∈ [t3] by decide)) (by decide)
      (by vsimp [hc.pos])
    have b3 : (a.set t3 (a.env v1)).env t3 = 1 := by vsimp [hc.one]
    refine Hs.seq (t1 := 40 * B + 80) (t2 := 1 + (1 + (40 * B + 80) + 1) + 1)
      (Hs.mono (emitNat_spec (C := C) _ bc (by omega) (by rw [b3]; exact hpw 1 (by
      rcases h1B with h | h; exact h; subst h; omega))) (by rw [b3]; exact hnb 1 (by omega)) (fun _ h => h))
      (fun d ⟨d1, d2, d3, d4, d5⟩ => ?_)
    refine Hs.seq (t1 := 1) (t2 := 1 + (40 * B + 80) + 1) (hs_copy C t3 xA d (by decide)) (fun e he' => ?_)
    subst he'
    have eA : (d.set t3 (d.env xA)).env t3 = A := by vsimp [d5 xA (by decide), hA]
    have eV : (d.set t3 (d.env xA)).env xV = v := by vsimp [d5 xV (by decide), hv]
    refine Hs.seq (t1 := 1) (t2 := 40 * B + 80) (hs_sub C t3 xV _ (by decide) (by rw [eA, eV]; omega)) (fun f hf => ?_)
    subst hf
    set f := (d.set t3 (d.env xA)).set t3 ((d.set t3 (d.env xA)).env t3 - (d.set t3 (d.env xA)).env xV) with hfd
    have dA : d.env xA = A := by rw [d5 xA (by decide)]; vsimp [hA]
    have dV : d.env xV = v := by rw [d5 xV (by decide)]; vsimp [hv]
    have f3 : f.env t3 = A - v := by vsimp [hfd, dA, dV]
    have fc : Cst f := Cst.of_fr d4 (Fr.trans (Fr.set d _ (show t3 ∈ [t3] by decide)) (Fr.set _ _ (by decide)))
      (by decide) (by vsimp [hfd, d4.pos])
    refine Hs.mono (emitNat_spec (C := C) f fc (by omega) (by rw [f3]; exact hpw _ (by omega))) (by
      rw [f3]; exact hnb _ (by omega)) ?_
    rintro g ⟨g1, g2, g3, g4, g5⟩
    refine ⟨by rw [g1, f3]; simp [hfd, d1, hc.one], by rw [g2]; simp [hfd, d2], by rw [g3]; simp [hfd, d3], g4, ?_⟩
    exact Fr.trans (Fr.set a _ (by decide)) (Fr.trans (Fr.weaken d5 (by decide)) (Fr.trans (Fr.set _ _ (by decide))
      (Fr.trans (Fr.set _ _ (by decide)) (Fr.weaken g5 (by decide)))))
  · have hge : ¬ v < A := by simp only [Cnd.eval, decide_eq_false_iff_not] at he; rwa [hv, hA] at he
    rw [if_neg hge]
    refine Hs.mono (Hs.seq (t1 := 1) (t2 := 40 * B + 80 + (1 + (1 + (40 * B + 80) + 1) + 1) + 1) (hs_copy C t3 vZ a (by decide))
      (fun b hb => ?_)) (by omega) (fun _ h => h)
    subst hb
    have bc : Cst (a.set t3 (a.env vZ)) := Cst.of_fr hc (Fr.set a _ (show t3 ∈ [t3] by decide)) (by decide)
      (by vsimp [hc.pos])
    have b3 : (a.set t3 (a.env vZ)).env t3 = 0 := by vsimp [hc.z]
    refine Hs.seq (t1 := 40 * B + 80) (t2 := 1 + (1 + (40 * B + 80) + 1) + 1)
      (Hs.mono (emitNat_spec (C := C) _ bc (by omega) (by rw [b3]; exact hpw 0 (by positivity)))
      (by rw [b3]; exact hnb 0 (by positivity)) (fun _ h => h)) (fun d ⟨d1, d2, d3, d4, d5⟩ => ?_)
    refine Hs.seq (t1 := 1) (t2 := 1 + (40 * B + 80) + 1) (hs_copy C t3 xV d (by decide)) (fun e he' => ?_)
    subst he'
    have eV : (d.set t3 (d.env xV)).env t3 = v := by vsimp [d5 xV (by decide), hv]
    have eA : (d.set t3 (d.env xV)).env xA = A := by vsimp [d5 xA (by decide), hA]
    refine Hs.seq (t1 := 1) (t2 := 40 * B + 80) (hs_sub C t3 xA _ (by decide) (by rw [eV, eA]; omega)) (fun f hf => ?_)
    subst hf
    set f := (d.set t3 (d.env xV)).set t3 ((d.set t3 (d.env xV)).env t3 - (d.set t3 (d.env xV)).env xA) with hfd
    have dA : d.env xA = A := by rw [d5 xA (by decide)]; vsimp [hA]
    have dV : d.env xV = v := by rw [d5 xV (by decide)]; vsimp [hv]
    have f3 : f.env t3 = v - A := by vsimp [hfd, dA, dV]
    have fc : Cst f := Cst.of_fr d4 (Fr.trans (Fr.set d _ (show t3 ∈ [t3] by decide)) (Fr.set _ _ (by decide)))
      (by decide) (by vsimp [hfd, d4.pos])
    refine Hs.mono (emitNat_spec (C := C) f fc (by omega) (by rw [f3]; exact hpw _ (by omega))) (by
      rw [f3]; exact hnb _ (by omega)) ?_
    rintro g ⟨g1, g2, g3, g4, g5⟩
    refine ⟨by rw [g1, f3]; simp [hfd, d1, hc.z], by rw [g2]; simp [hfd, d2], by rw [g3]; simp [hfd, d3], g4, ?_⟩
    exact Fr.trans (Fr.set a _ (by decide)) (Fr.trans (Fr.weaken d5 (by decide)) (Fr.trans (Fr.set _ _ (by decide))
      (Fr.trans (Fr.set _ _ (by decide)) (Fr.weaken g5 (by decide)))))

theorem prW_spec (c : Call) (p : Params) (a0 : DS VV) (hc : Cst a0) (hcwc : C.cw = callWord c)
    (hco1 : a0.env vCO1 = coPos c 0) (hco2 : a0.env vCO2 = coPos c 1) (hNR : a0.env xNR = roleCount c.kind)
    (hJ : a0.env pJ = p.J) (hRem : a0.env xRem = bitsValue (L0 c p C.wit))
    (hW : C.cw.length + 8 ≤ C.Wd) (hL : 2 ^ (C.cw.length + 2) ≤ 2 ^ C.Wd) (hJW : p.J + 1 < 2 ^ C.Wd) :
    Hs C (allW emitNat prAct) a0
      (p.J * (roleCount c.kind * (roleCost C.cw.length (40 * C.cw.length + 80) (100 * C.cw.length + 400) + 5) + 8) + 4)
      (fun b => b.out = a0.out ++ (List.range (p.J * roleCount c.kind)).flatMap (segOut c p C.wit) ∧ b.wq = a0.wq ∧
        Cst b ∧ Fr a0 b prWT) := by
  set R := roleCount c.kind with hRd
  have hR2 : R ≤ 2 := by rw [hRd]; cases c.kind <;> simp [roleCount]
  have h4 : 4 ≤ 2 ^ (C.cw.length + 2) := by
    rw [pow_add]; have := Nat.one_le_two_pow (n := C.cw.length); omega
  let A : ℕ → DS VV → Prop := fun g b => Fr a0 b prWT ∧ b.env xRem = bitsValue (rsG c p C.wit g).2 ∧
    b.out = a0.out ++ (List.range g).flatMap (segOut c p C.wit) ∧ b.wq = a0.wq
  refine Hs.mono (allW_spec emitNat prAct R p.J A (roleCost C.cw.length (40 * C.cw.length + 80)
    (100 * C.cw.length + 400)) ?_ ?_ a0 ⟨Fr.refl _ _, by rw [hRem]; rfl, by simp, rfl⟩ hc hNR hJ (by omega) hJW)
    le_rfl ?_
  · intro g b v ⟨h1, h2, h3, h4⟩
    exact ⟨⟨Fr.trans h1 (Fr.set b _ (by decide)), by vsimp [h2], by simp [h3], h4⟩,
      ⟨Fr.trans h1 (Fr.set b _ (by decide)), by vsimp [h2], by simp [h3], h4⟩⟩
  · intro s hs r hr b hA hcb hS hRo hNRb hJb
    obtain ⟨rest, hrest⟩ := coeffs_at c r
    set cs := (circ c r).coeffs with hcs
    set g := s * R + r with hg
    have hgr : g % R = r := mod_role c s r hr
    have hgr' : g % roleCount c.kind = r := hgr
    have hco : b.env (if r = 0 then vCO1 else vCO2) = coPos c r := by
      have h1 : b.env vCO1 = coPos c 0 := by rw [hA.1 vCO1 (by decide), hco1]
      have h2 : b.env vCO2 = coPos c 1 := by rw [hA.1 vCO2 (by decide), hco2]
      exact co_at c b h1 h2 r
    set lg := (rsG c p C.wit g).2 with hlg
    have hws : wsR c (g % R) = cs.map coefWidth := by rw [hgr]; rfl
    have hfv : ∀ i (hi : i < cs.length), fieldV c p C.wit g i =
        bitsValue ((lg.drop (((cs.map coefWidth).take i).sum)).take (coefWidth cs[i])) := by
      intro i hi; unfold fieldV; rw [hws]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi, Option.getD_some]
      rfl
    have hsc : ∀ i (hi : i < cs.length), segCoef c p C.wit g i = (fieldV c p C.wit g i : ℤ) - (cs[i]).natAbs := by
      intro i hi; unfold segCoef; rw [hgr']
      show (fieldV c p C.wit g i : ℤ) - (((circ c r).coeffs.getD i 0).natAbs : ℤ) = _
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < (circ c r).coeffs.length from hi)]; rfl
    let P : ℕ → DS VV → Prop := fun k e => Fr a0 e prWT ∧
      e.env xRem = bitsValue (lg.drop (((cs.map coefWidth).take k).sum)) ∧
      e.out = a0.out ++ (List.range g).flatMap (segOut c p C.wit) ++ natWord cs.length ++
        ((List.range k).map (segCoef c p C.wit g)).flatMap Interfaces.intWord ∧ e.wq = a0.wq
    have hlwL : (listWord Interfaces.intWord cs).length ≤ C.cw.length := by
      have := len_le_of_drop (by rw [hcwc]; exact hrest : C.cw.drop (coPos c r) = listWord Interfaces.intWord cs ++ rest)
      exact this
    refine Hs.mono (seg_of_role emitNat prAct emitNatT prActT (by decide) (by decide) s r R p.J cs (coPos c r) rest
      (A g) (A (g + 1)) P ?_ (40 * C.cw.length + 80) ?_ ?_ (100 * C.cw.length + 400) ?_ ?_ b hA hcb
      ⟨hS, hRo, hNRb, hJb⟩ hco (by rw [hcwc]; exact hrest) (by omega) hL) le_rfl (fun e h => h)
    · intro d e ⟨h1, h2, h3, h4⟩ hf ho hw
      exact ⟨Fr.trans h1 (Fr.weaken hf (by decide)), by rw [hf xRem (by decide), h2], by rw [ho, h3], by rw [hw, h4]⟩
    · intro d ⟨h1, h2, h3, h4⟩ hcd ht hm
      have hcsL : cs.length ≤ C.cw.length := by
        have := length_le_flatMap cs Interfaces.intWord (fun z => by
          simp only [Interfaces.intWord, List.length_append, natWord_length]; omega)
        simp only [listWord, List.length_append] at hlwL; omega
      have hnb : natBitLength cs.length ≤ C.cw.length + 1 := by have := natBitLength_le_succ cs.length; omega
      have hpw : natBitLength (d.env t3) + 2 < 2 ^ C.Wd := by
        rw [ht]
        have : C.cw.length + 3 < 2 ^ C.Wd := lt_of_lt_of_le Nat.lt_two_pow_self
          (Nat.pow_le_pow_right (by norm_num) (by omega))
        omega
      refine Hs.mono (emitNat_spec (C := C) d hcd (by omega) hpw) (by rw [ht]; omega) ?_
      rintro e ⟨e1, e2, e3, e4, e5⟩
      refine ⟨⟨Fr.trans h1 (Fr.weaken e5 (by decide)), by rw [e5 xRem (by decide), h2]; simp; rfl, ?_, by rw [e3, h4]⟩,
        e2, e4, e5⟩
      rw [e1, h3, ht]; simp
    · intro k d e ⟨h1, h2, h3, h4⟩ hf ho hw
      exact ⟨Fr.trans h1 (Fr.weaken hf (by decide)), by rw [hf xRem (by decide), h2], by rw [ho, h3], by rw [hw, h4]⟩
    · intro k hk d ⟨h1, h2, h3, h4⟩ hcd hA' hW'
      have hlw : (Interfaces.intWord cs[k]).length ≤ C.cw.length := by
        have e2 := elem_len_le_flatMap cs Interfaces.intWord (List.getElem_mem hk)
        simp only [listWord, List.length_append] at hlwL; omega
      have hcwk : coefWidth cs[k] ≤ C.cw.length := (coefWidth_le_int cs[k]).trans hlw
      have hAk : cs[k].natAbs < 2 ^ C.cw.length :=
        lt_of_lt_of_le (natAbs_lt_pow cs[k]) (Nat.pow_le_pow_right (by norm_num) hlw)
      have hkw : ((cs.map coefWidth).take (k + 1)).sum = ((cs.map coefWidth).take k).sum + coefWidth cs[k] := by
        rw [List.take_add_one, List.getElem?_map, List.getElem?_eq_getElem hk]; simp
      refine Hs.mono (Hs.seq (t2 := 80 * C.cw.length + 200) (extractW_spec d hcd _ (coefWidth cs[k]) h2 hW' (by omega))
        (fun e ⟨e1, e2, e3, e4, e5, e6, e7⟩ => ?_)) (show 12 * coefWidth cs[k] + 10 + (80 * C.cw.length + 200) + 1 ≤
          100 * C.cw.length + 400 by omega) (fun _ h => h)
      have hvB : bitsValue ((lg.drop (((cs.map coefWidth).take k).sum)).take (coefWidth cs[k])) < 2 ^ C.cw.length :=
        lt_of_lt_of_le (bitsValue_lt _) (Nat.pow_le_pow_right (by norm_num) (by simp; omega))
      have eA : e.env xA = cs[k].natAbs := by rw [e7 xA (by decide), hA']
      refine Hs.mono (prAct_print e e6 _ _ e1 eA C.cw.length hvB hAk (by omega)) (by omega) ?_
      rintro f ⟨f1, f2, f3, f4, f5⟩
      refine ⟨⟨Fr.trans h1 (Fr.trans (Fr.weaken e7 (by decide)) (Fr.weaken f5 (by decide))), ?_, ?_, by
        rw [f3, e4, h4]⟩, by rw [f2, e3], f4, Fr.trans (Fr.weaken e7 (by decide)) (Fr.weaken f5 (by decide))⟩
      · rw [f5 xRem (by decide), e2, List.drop_drop, hkw]
      · rw [f1, e5, h3, List.range_succ, List.map_append, List.flatMap_append]
        simp only [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil]
        rw [hsc k hk, hfv k hk]; simp [List.append_assoc]
    · intro e ⟨h1, h2, h3, h4⟩
      refine ⟨h1, ?_, ?_, h4⟩
      · rw [h2, List.take_of_length_le (by simp)]
        show bitsValue (lg.drop (cs.map coefWidth).sum) = bitsValue (rsG c p C.wit (g + 1)).2
        rw [rsG_succ_snd c p C.wit s r hs hr]; rfl
      · rw [h3, List.range_succ, List.flatMap_append]
        simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]
        congr 2
        unfold segOut; rw [hgr']; simp [listWord]; rfl
  · rintro b ⟨⟨h1, h2, h3, h4⟩, h5⟩
    exact ⟨h3, h4, h5, h1⟩

end NearCubicGates.Close.Dispatch
