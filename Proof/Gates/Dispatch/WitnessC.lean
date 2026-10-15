import Proof.Gates.Dispatch.WitnessB

/-!
# Fragment (W), part C: walking the coefficient lists of the call word

`roleW co pre act`: put the cursor at `env co` (a coefficient list `listWord intWord cs` of the call word), read the
count into `xM`, run `pre`, then for every coefficient `a`: `xA := |a|`, `xW := ⌈lg(2|a|+1)⌉`, run `act`.
`rolesW`: role `r < env xNR` uses the list at `vCO1` (`r = 0`) or `vCO2`; `allW`: every stage `s < env pJ`.
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

/-! ## Where the coefficient lists sit -/

/-- The position of role `r`'s coefficient list in the call word. -/
def coPos (c : Call) (r : ℕ) : ℕ :=
  if r = 0 then pos1 c + (listWord gateWord c.first.gates).length else pos2 c + (listWord gateWord c.second.gates).length

theorem coeffs_at (c : Call) (r : ℕ) :
    ∃ rest, (callWord c).drop (coPos c r) = listWord Interfaces.intWord (circ c r).coeffs ++ rest := by
  rw [callWord_eq]
  by_cases hr : r = 0
  · subst hr
    refine ⟨listWord bitWord c.first.table ++ (circuitWord c.second ++ (listWord natWord c.parity ++ ratWord c.radius)), ?_⟩
    simp only [coPos, if_pos rfl, pos1, circ]
    rw [show natWord c.n ++ natWord (kindTag c.kind) ++ (circuitWord c.first ++ (circuitWord c.second ++
      (listWord natWord c.parity ++ ratWord c.radius))) = (natWord c.n ++ natWord (kindTag c.kind) ++
        listWord gateWord c.first.gates) ++ (listWord Interfaces.intWord c.first.coeffs ++ (listWord bitWord c.first.table ++
          (circuitWord c.second ++ (listWord natWord c.parity ++ ratWord c.radius)))) by
      simp [circuitWord, List.append_assoc]]
    rw [List.drop_left' (by simp; omega)]; simp
  · refine ⟨listWord bitWord c.second.table ++ (listWord natWord c.parity ++ ratWord c.radius), ?_⟩
    simp only [coPos, if_neg hr, pos2, pos1, circ]
    rw [show natWord c.n ++ natWord (kindTag c.kind) ++ (circuitWord c.first ++ (circuitWord c.second ++
      (listWord natWord c.parity ++ ratWord c.radius))) = (natWord c.n ++ natWord (kindTag c.kind) ++
        circuitWord c.first ++ listWord gateWord c.second.gates) ++ (listWord Interfaces.intWord c.second.coeffs ++
          (listWord bitWord c.second.table ++ (listWord natWord c.parity ++ ratWord c.radius))) by
      simp [circuitWord, List.append_assoc]]
    rw [List.drop_left' (by simp [List.length_append]; omega)]

theorem coefWidth_le (z : ℤ) : coefWidth z ≤ natBitLength z.natAbs + 1 := by
  unfold coefWidth
  apply Nat.clog_le_of_le_pow
  have := lt_natBitLength z.natAbs
  rw [pow_succ]; omega

theorem coefWidth_natAbs (z : ℤ) : coefWidth ((z.natAbs : ℕ) : ℤ) = coefWidth z := by
  simp only [coefWidth, Int.natAbs_natCast]

theorem natAbs_lt_pow (z : ℤ) : z.natAbs < 2 ^ (Interfaces.intWord z).length := by
  have h1 := lt_natBitLength z.natAbs
  have h2 : natBitLength z.natAbs ≤ (Interfaces.intWord z).length := by
    simp only [Interfaces.intWord, List.length_append, natWord_length]; omega
  exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by norm_num) h2)

/-! ## One coefficient list -/

def coefBody (act : St VV) : St VV := .seq readInt (.seq (.op (.copy xA t3)) (.seq widthW act))

def roleW (co : Fin VV) (pre act : St VV) : St VV :=
  .seq (seekW co) (.seq readNat (.seq (.op (.copy xM t3)) (.seq pre (.seq (.op (.zero xIc))
    (.loop (.lt xIc xM) (.seq (coefBody act) (.op (.inc xIc))))))))

/-- What the per-coefficient part may change before `act` (and the walk's counter). -/
def coefT : List (Fin VV) := [t0, t1, t2, t3, t4, t8, vJ, vPOS, xA, xT2, xW, xP, xIc]

theorem coefBody_spec (act : St VV) (cs : List ℤ) (k : ℕ) (hk : k < cs.length) (P : ℕ → DS VV → Prop)
    (hPfr : ∀ a b, P k a → Fr a b coefT → b.out = a.out → b.wq = a.wq → P k b) (ta : ℕ)
    (hact : ∀ a, P k a → Cst a → a.env xA = (cs[k]).natAbs → a.env xW = coefWidth cs[k] →
      Hs C act a ta (fun b => P (k + 1) b ∧ b.cp = a.cp ∧ Cst b ∧ b.env xIc = a.env xIc ∧ b.env xM = a.env xM))
    (a : DS VV) (hP : P k a) (hc : Cst a) (rest : List Bool)
    (hcw : C.cw.drop a.cp = Interfaces.intWord cs[k] ++ rest) (hW : C.cw.length + 4 ≤ C.Wd)
    (hL : 2 ^ (C.cw.length + 2) ≤ 2 ^ C.Wd) :
    Hs C (coefBody act) a (70 * C.cw.length + ta + 110) (fun b => P (k + 1) b ∧ Cst b ∧ b.env xIc = a.env xIc ∧
      b.env xM = a.env xM ∧ b.cp = a.cp + (Interfaces.intWord cs[k]).length) := by
  have hlen := len_le_of_drop hcw
  have hLW : C.cw.length + 2 < 2 ^ C.Wd := lt_of_lt_of_le (by
    calc C.cw.length + 2 < 2 ^ (C.cw.length + 2) := Nat.lt_two_pow_self
      _ = 2 ^ (C.cw.length + 2) := rfl) hL
  have hA := natAbs_lt_pow cs[k]
  have hcwk := coefWidth_le cs[k]
  have hnb := natBitLength_le_len cs[k].natAbs
  have hiw : (natWord cs[k].natAbs).length ≤ (Interfaces.intWord cs[k]).length := by
    simp [Interfaces.intWord, List.length_append]
  refine Hs.mono (Hs.seq (readInt_spec a hc cs[k] rest hcw (by omega) hLW) (fun b ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩ =>
    Hs.seq (hs_copy C xA t3 b (by decide)) (fun d hd => ?_))) (by omega : 60 * (Interfaces.intWord cs[k]).length + 70 +
      (1 + (5 * coefWidth cs[k] + 12 + ta + 1) + 1) + 1 ≤ _) (fun _ h => h)
  subst hd
  have dA : (b.set xA (b.env t3)).env xA = cs[k].natAbs := by vsimp [b2]
  have dc : Cst (b.set xA (b.env t3)) := Cst.of_fr b7 (Fr.set b _ (show xA ∈ [xA] by decide)) (by decide)
    (by vsimp [b7.pos])
  have hAW : 2 * cs[k].natAbs + 2 < 2 ^ C.Wd := by
    have h2 : 2 ^ (Interfaces.intWord cs[k]).length * 4 ≤ 2 ^ C.Wd := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  refine Hs.seq (widthW_spec _ dc cs[k].natAbs dA (by rw [coefWidth_natAbs]; omega) hAW) (fun e ⟨e1, e2, e3, e4, e5, e6⟩ => ?_)
  rw [coefWidth_natAbs] at e1
  have hPe : P k e := by
    refine hPfr a e hP ?_ (by rw [e4]; exact b6) (by rw [e3]; exact b5)
    exact Fr.trans (Fr.weaken b8 (by decide)) (Fr.trans (Fr.weaken (Fr.set b _ (show xA ∈ [xA] by decide)) (by decide))
      (Fr.weaken e6 (by decide)))
  have eA : e.env xA = cs[k].natAbs := by rw [e6 xA (by decide), dA]
  refine Hs.mono (hact e hPe e5 eA e1) le_rfl ?_
  rintro f ⟨f1, f2, f3, f4, f5⟩
  refine ⟨f1, f3, ?_, ?_, ?_⟩
  · rw [f4, e6 xIc (by decide), DS.set_env_ne _ _ (by decide), b8 xIc (by decide)]
  · rw [f5, e6 xM (by decide), DS.set_env_ne _ _ (by decide), b8 xM (by decide)]
  · rw [f2, e2]; exact b4

/-- What `roleW` changes before `pre`. -/
def roleT0 : List (Fin VV) := [t0, t1, t2, t3, t4, vJ, vPOS, xM]

def roleCost (L tp ta : ℕ) : ℕ := 40 * L + 50 + tp + L * (70 * L + ta + 120)

theorem roleW_spec (co : Fin VV) (hco : co = vCO1 ∨ co = vCO2) (pre act : St VV) (cs : List ℤ) (q : ℕ)
    (rest : List Bool) (Q : DS VV → Prop) (P : ℕ → DS VV → Prop)
    (hQfr : ∀ a b, Q a → Fr a b roleT0 → b.out = a.out → b.wq = a.wq → Q b)
    (tp : ℕ) (hpre : ∀ a, Q a → Cst a → a.env t3 = cs.length → a.env xM = cs.length →
      Hs C pre a tp (fun b => P 0 b ∧ b.cp = a.cp ∧ Cst b ∧ b.env xM = a.env xM))
    (hPfr : ∀ k a b, P k a → Fr a b coefT → b.out = a.out → b.wq = a.wq → P k b)
    (ta : ℕ) (hact : ∀ k (hk : k < cs.length), ∀ a, P k a → Cst a → a.env xA = (cs[k]).natAbs →
      a.env xW = coefWidth cs[k] →
      Hs C act a ta (fun b => P (k + 1) b ∧ b.cp = a.cp ∧ Cst b ∧ b.env xIc = a.env xIc ∧ b.env xM = a.env xM))
    (a : DS VV) (hQ : Q a) (hc : Cst a) (hq : a.env co = q)
    (hcw : C.cw.drop q = listWord Interfaces.intWord cs ++ rest)
    (hW : C.cw.length + 4 ≤ C.Wd) (hL : 2 ^ (C.cw.length + 2) ≤ 2 ^ C.Wd) :
    Hs C (roleW co pre act) a (roleCost C.cw.length tp ta) (fun b => P cs.length b ∧ Cst b) := by
  set L := C.cw.length with hLd
  have hlen := len_le_of_drop hcw
  have hql : q ≤ L := by
    have h1 := congrArg List.length hcw; simp only [List.length_drop, List.length_append] at h1
    have h2 : 1 ≤ (listWord Interfaces.intWord cs).length := by
      simp only [listWord, List.length_append, natWord_length]; omega
    omega
  have hLW : L < 2 ^ C.Wd := lt_of_lt_of_le (lt_of_lt_of_le Nat.lt_two_pow_self
    (Nat.pow_le_pow_right (by norm_num) (by omega))) hL
  have hLW2 : L + 2 < 2 ^ C.Wd := lt_of_lt_of_le Nat.lt_two_pow_self hL
  simp only [listWord, List.append_assoc] at hcw hlen
  rw [List.length_append] at hlen
  have hcsL : cs.length ≤ L := by
    have := length_le_flatMap cs Interfaces.intWord (fun z => by simp only [Interfaces.intWord, List.length_append, natWord_length]; omega); omega
  have hnb := natBitLength_le_len cs.length
  have hcoT : co ∉ [t0, vPOS, vJ] := by rcases hco with rfl | rfl <;> decide
  have hcoP : co ≠ vPOS := by rcases hco with rfl | rfl <;> decide
  refine Hs.mono (Hs.seq (seekW_spec co hcoT hcoP a hc q hq hql hLW) (fun b ⟨b1, b2, b3, b4, b5⟩ => ?_))
    (show 5 * q + 6 + (30 * natBitLength cs.length + 30 + (1 + (tp + (1 + (cs.length * (70 * L + ta + 110 + 2 + 2) + 2)
      + 1) + 1) + 1) + 1) + 1 ≤ roleCost L tp ta by
      unfold roleCost
      have : cs.length * (70 * L + ta + 110 + 2 + 2) ≤ L * (70 * L + ta + 120) := Nat.mul_le_mul hcsL (by omega)
      omega) (fun _ h => h)
  have bcw : C.cw.drop b.cp = natWord cs.length ++ (cs.flatMap Interfaces.intWord ++ rest) := by rw [b1]; exact hcw
  refine Hs.seq (readNat_spec b b4 cs.length _ bcw (by omega) hLW2) (fun d ⟨d1, d2, d3, d4, d5, d6, d7⟩ => ?_)
  refine Hs.seq (hs_copy C xM t3 d (by decide)) (fun e he => ?_)
  subst he
  have ec : Cst (d.set xM (d.env t3)) := Cst.of_fr d6 (Fr.set d _ (show xM ∈ [xM] by decide)) (by decide)
    (by vsimp [d6.pos])
  have eQ : Q (d.set xM (d.env t3)) := by
    refine hQfr a _ hQ ?_ (by simp [d5, b3]) (by simp [d4, b2])
    exact Fr.trans (Fr.weaken b5 (by decide)) (Fr.trans (Fr.weaken d7 (by decide))
      (Fr.weaken (Fr.set d _ (show xM ∈ [xM] by decide)) (by decide)))
  refine Hs.seq (hpre _ eQ ec (by vsimp [d1]) (by vsimp [d1])) (fun f ⟨f1, f2, f3, f4⟩ => ?_)
  refine Hs.seq (hs_zero C xIc f) (fun g hg => ?_)
  subst hg
  have gP : P 0 (f.set xIc 0) := hPfr 0 f _ f1 (Fr.set f _ (by decide)) rfl rfl
  have gc : Cst (f.set xIc 0) := Cst.of_fr f3 (Fr.set f _ (show xIc ∈ [xIc] by decide)) (by decide) (by vsimp [f3.pos])
  have gcw : C.cw.drop (f.set xIc 0).cp = cs.flatMap Interfaces.intWord ++ rest := by
    show C.cw.drop f.cp = _
    rw [f2]; show C.cw.drop d.cp = _
    rw [d3, ← List.drop_drop, bcw, List.drop_left]
  have l := walk (C := C) cs Interfaces.intWord xIc xM (by decide) (coefBody act) (fun k b => P k b ∧ Cst b)
    (70 * L + ta + 110) rest
    (fun k b v ⟨h1, h2⟩ => ⟨hPfr k b _ h1 (Fr.set b _ (by decide)) rfl rfl,
      Cst.of_fr h2 (Fr.set b _ (show xIc ∈ [xIc] by decide)) (by decide) (by vsimp [h2.pos])⟩)
    (fun k hk b ⟨h1, h2⟩ hi hm hd => by
      refine Hs.mono (coefBody_spec act cs k hk P (hPfr k) ta (hact k hk) b h1 h2 _ hd hW hL) le_rfl ?_
      rintro r ⟨r1, r2, r3, r4, r5⟩
      exact ⟨⟨r1, r2⟩, by rw [r3, hi], by rw [r4, hm], r5⟩)
    (by omega) _ ⟨gP, gc⟩ (by vsimp []) (by vsimp [f4, d1]) gcw
  exact Hs.mono l le_rfl (fun r ⟨⟨r1, r2⟩, _⟩ => ⟨r1, r2⟩)

/-! ## All roles, all stages -/

def roleSel (pre act : St VV) : St VV := .ite (.eq xRo vZ) (roleW vCO1 pre act) (roleW vCO2 pre act)
def rolesW (pre act : St VV) : St VV :=
  .seq (.op (.zero xRo)) (.loop (.lt xRo xNR) (.seq (roleSel pre act) (.op (.inc xRo))))
def allW (pre act : St VV) : St VV :=
  .seq (.op (.zero xS)) (.loop (.lt xS pJ) (.seq (rolesW pre act) (.op (.inc xS))))

theorem allW_spec (pre act : St VV) (R J : ℕ) (A : ℕ → DS VV → Prop) (T : ℕ)
    (hAfr : ∀ g a v, A g a → A g (a.set xRo v) ∧ A g (a.set xS v))
    (hseg : ∀ s < J, ∀ r < R, ∀ a, A (s * R + r) a → Cst a → a.env xS = s → a.env xRo = r → a.env xNR = R →
      a.env pJ = J → Hs C (if r = 0 then roleW vCO1 pre act else roleW vCO2 pre act) a T
        (fun b => A (s * R + r + 1) b ∧ Cst b ∧ b.env xS = s ∧ b.env xRo = r ∧ b.env xNR = R ∧ b.env pJ = J))
    (a : DS VV) (hA : A 0 a) (hc : Cst a) (hR : a.env xNR = R) (hJ : a.env pJ = J) (hRW : R + 1 < 2 ^ C.Wd)
    (hJW : J + 1 < 2 ^ C.Wd) :
    Hs C (allW pre act) a (J * (R * (T + 5) + 8) + 4) (fun b => A (J * R) b ∧ Cst b) := by
  -- the stage loop
  let I : ℕ → DS VV → Prop := fun s b => A (s * R) b ∧ Cst b ∧ b.env xS = s ∧ b.env xNR = R ∧ b.env pJ = J
  have l := Hs.loopN (C := C) (c := .lt xS pJ) (s := .seq (rolesW pre act) (.op (.inc xS))) (show xS ≠ pJ by decide) I J
    (R * (T + 5) + 6) ?_ ?_
  · refine Hs.mono (Hs.seq (hs_zero C xS a) (fun b hb => l b ?_)) (by
      rw [show R * (T + 5) + 6 + 2 = R * (T + 5) + 8 by ring]; omega) ?_
    · subst hb
      exact ⟨by simpa using (hAfr 0 a 0 hA).2, Cst.of_fr hc (Fr.set a _ (show xS ∈ [xS] by decide)) (by decide)
        (by vsimp [hc.pos]), by vsimp [], by vsimp [hR], by vsimp [hJ]⟩
    · rintro b ⟨b1, b2, -⟩; exact ⟨b1, b2⟩
  · intro s hs b ⟨b1, b2, b3, b4, b5⟩
    refine ⟨by simp [Cnd.eval, b3, b5, hs], ?_⟩
    -- the role loop of stage `s`
    let K : ℕ → DS VV → Prop := fun r d => A (s * R + r) d ∧ Cst d ∧ d.env xS = s ∧ d.env xRo = r ∧
      d.env xNR = R ∧ d.env pJ = J
    have l2 := Hs.loopN (C := C) (c := .lt xRo xNR) (s := .seq (roleSel pre act) (.op (.inc xRo))) (show xRo ≠ xNR by decide) K R
      (T + 3) ?_ ?_
    · refine Hs.seq (t1 := R * (T + 5) + 4) (t2 := 1) (Hs.mono (Hs.seq (hs_zero C xRo b) (fun d hd => l2 d ?_))
        (by rw [show T + 3 + 2 = T + 5 by ring]; omega) (fun d h => h)) (fun d ⟨d1, d2, d3, _, d5, d6⟩ => ?_)
      · subst hd
        exact ⟨by simpa using (hAfr _ b 0 b1).1, Cst.of_fr b2 (Fr.set b _ (show xRo ∈ [xRo] by decide)) (by decide)
          (by vsimp [b2.pos]), by vsimp [b3], by vsimp [], by vsimp [b4], by vsimp [b5]⟩
      · refine Hs.mono (hs_inc C xS d (by rw [d3]; omega)) le_rfl ?_
        rintro e rfl
        refine ⟨?_, Cst.of_fr d2 (Fr.set d _ (show xS ∈ [xS] by decide)) (by decide) (by vsimp [d2.pos]),
          by vsimp [d3], by vsimp [d5], by vsimp [d6]⟩
        have := (hAfr _ d (d.env xS + 1) d1).2
        rwa [show s * R + R = (s + 1) * R by ring] at this
    · intro r hr d ⟨d1, d2, d3, d4, d5, d6⟩
      refine ⟨by simp [Cnd.eval, d4, d5, hr], ?_⟩
      refine Hs.seq (t1 := T + 1) (t2 := 1) (Hs.ite (c := .eq xRo vZ) (show xRo ≠ vZ by decide)
        (R := fun e => A (s * R + r + 1) e ∧ Cst e ∧ e.env xS = s ∧ e.env xRo = r ∧ e.env xNR = R ∧ e.env pJ = J)
        (fun he => ?_) (fun he => ?_)) (fun e ⟨e1, e2, e3, e4, e5, e6⟩ => ?_)
      · have hr0 : r = 0 := by
          simp only [Cnd.eval, decide_eq_true_eq] at he; rw [d4, d2.z] at he; exact he
        have := hseg s hs r hr d d1 d2 d3 d4 d5 d6
        rwa [if_pos hr0] at this
      · have hr0 : r ≠ 0 := by
          simp only [Cnd.eval, decide_eq_false_iff_not] at he; rw [d4, d2.z] at he; exact he
        have := hseg s hs r hr d d1 d2 d3 d4 d5 d6
        rwa [if_neg hr0] at this
      · refine Hs.mono (hs_inc C xRo e (by rw [e4]; omega)) le_rfl ?_
        rintro f rfl
        exact ⟨(hAfr _ e _ e1).1, Cst.of_fr e2 (Fr.set e _ (show xRo ∈ [xRo] by decide)) (by decide)
          (by vsimp [e2.pos]), by vsimp [e3], by vsimp [e4], by vsimp [e5], by vsimp [e6]⟩
    · intro d ⟨_, _, _, d4, d5, _⟩
      simp [Cnd.eval, d4, d5]
  · intro b ⟨_, _, b3, _, b5⟩
    simp [Cnd.eval, b3, b5]

end NearCubicGates.Close.Dispatch
