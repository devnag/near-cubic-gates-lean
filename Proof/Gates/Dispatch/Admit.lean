import Proof.Gates.Dispatch.ParseCall

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxRecDepth 4000

namespace NearCubicGates.Close.Dispatch

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Interfaces

variable {C : Ctx}

def vADM : Fin VV := ⟨60, by decide⟩

/-! ## Flag steps -/

/-- Require `x = y`. -/
def needEq (x y : Fin VV) : St VV := .ite (.eq x y) skipS (.op (.zero vADM))
/-- Require `x ≤ y`. -/
def needLe (x y : Fin VV) : St VV := .ite (.lt y x) (.op (.zero vADM)) skipS

theorem needEq_spec (x y : Fin VV) (hxy : x ≠ y) (a : DS VV) (P : Prop) [Decidable P] (hP : a.env vADM = bnat P) :
    Hs C (needEq x y) a 2 (fun b => b.env vADM = bnat (P ∧ a.env x = a.env y) ∧ b.cp = a.cp ∧ b.wq = a.wq ∧
      b.out = a.out ∧ Fr a b [vADM, vJ]) := by
  refine Hs.ite (c := .eq x y) hxy (fun he => ?_) (fun he => ?_)
  · have h : a.env x = a.env y := by simpa [Cnd.eval] using he
    refine Hs.mono (skip_spec a) le_rfl ?_
    rintro b rfl
    exact ⟨by rw [DS.set_env_ne _ _ (by decide), hP]; exact bnat_congr (by simp [h]), rfl, rfl, rfl,
      Fr.set a _ (by decide)⟩
  · have h : a.env x ≠ a.env y := by simpa [Cnd.eval] using he
    refine Hs.mono (hs_zero C vADM a) le_rfl ?_
    rintro b rfl
    exact ⟨by rw [DS.set_env_self]; unfold bnat; simp [h], rfl, rfl, rfl, Fr.set a _ (by decide)⟩

theorem needLe_spec (x y : Fin VV) (hxy : y ≠ x) (a : DS VV) (P : Prop) [Decidable P] (hP : a.env vADM = bnat P) :
    Hs C (needLe x y) a 2 (fun b => b.env vADM = bnat (P ∧ a.env x ≤ a.env y) ∧ b.cp = a.cp ∧ b.wq = a.wq ∧
      b.out = a.out ∧ Fr a b [vADM, vJ]) := by
  refine Hs.ite (c := .lt y x) hxy (fun he => ?_) (fun he => ?_)
  · have h : a.env y < a.env x := by simpa [Cnd.eval] using he
    refine Hs.mono (hs_zero C vADM a) le_rfl ?_
    rintro b rfl
    exact ⟨by rw [DS.set_env_self]; unfold bnat; simp [show ¬ a.env x ≤ a.env y by omega], rfl, rfl, rfl,
      Fr.set a _ (by decide)⟩
  · have h : a.env x ≤ a.env y := by simpa [Cnd.eval] using he
    refine Hs.mono (skip_spec a) le_rfl ?_
    rintro b rfl
    exact ⟨by rw [DS.set_env_ne _ _ (by decide), hP]; exact bnat_congr (by simp [h]), rfl, rfl, rfl,
      Fr.set a _ (by decide)⟩

/-! ## Bounds from the call word -/

theorem lt_pow_len_of_natWord (v : ℕ) : v < 2 ^ (natWord v).length :=
  lt_of_lt_of_le (lt_natBitLength v) (Nat.pow_le_pow_right (by norm_num) (natBitLength_le_len v))

theorem topWeight_lt {n : ℕ} (Cc : NCircuit n) : Cc.topWeight < 2 ^ (circuitWord Cc).length := by
  have h := sum_natAbs_lt Cc.coeffs
  have hl : (Cc.coeffs.flatMap Interfaces.intWord).length ≤ (circuitWord Cc).length := by
    simp [circuitWord, listWord]; omega
  exact lt_of_lt_of_le h (Nat.pow_le_pow_right (by norm_num) hl)

/-- Numbers of the call word are below `2^{|callWord c|}`. -/
theorem call_bounds (c : Call) : c.n < 2 ^ (callWord c).length ∧ c.first.topWeight < 2 ^ (callWord c).length ∧
    c.second.topWeight < 2 ^ (callWord c).length ∧ c.radius.num.natAbs < 2 ^ (callWord c).length ∧
    c.radius.den < 2 ^ (callWord c).length ∧
    natBitLength (if c.radius.num < 0 then 1 else 0) + natBitLength c.radius.num.natAbs + natBitLength c.radius.den ≤
      (callWord c).length := by
  have hL := congrArg List.length (callWord_eq c)
  simp only [List.length_append] at hL
  have hr : (ratWord c.radius).length = (natWord (if c.radius.num < 0 then 1 else 0)).length +
      (natWord c.radius.num.natAbs).length + (natWord c.radius.den).length := by
    simp [ratWord, Interfaces.intWord]; ring
  have p2 : ∀ a b : ℕ, a ≤ b → 2 ^ a ≤ 2 ^ b := fun a b h => Nat.pow_le_pow_right (by norm_num) h
  refine ⟨lt_of_lt_of_le (lt_pow_len_of_natWord _) (p2 _ _ (by omega)),
    lt_of_lt_of_le (topWeight_lt _) (p2 _ _ (by omega)), lt_of_lt_of_le (topWeight_lt _) (p2 _ _ (by omega)),
    lt_of_lt_of_le (lt_pow_len_of_natWord _) (p2 _ _ (by omega)),
    lt_of_lt_of_le (lt_pow_len_of_natWord _) (p2 _ _ (by omega)), ?_⟩
  have := natBitLength_le_len (if c.radius.num < 0 then 1 else 0)
  have := natBitLength_le_len c.radius.num.natAbs
  have := natBitLength_le_len c.radius.den
  omega

/-! ## The admission program -/

def admA : St VV := .seq (.op (.copy vADM v1)) (.seq (setK t3 4) (needLe t3 vN))

def admW (g c tw t wok nz : Fin VV) : St VV :=
  .seq (needEq g c) (.seq (needEq nz v1) (.seq (.op (.copy t3 tw)) (.seq (.op (.shl t3)) (.seq (.op (.inc t3))
    (.seq (needEq t t3) (needEq wok v1))))))

def admK : St VV :=
  .seq (.ite (.eq vTAG v1) skipS (.seq (needEq vG2 vZ) (.seq (needEq vC2 vZ) (.seq (needEq vT2 v1) (needEq vTB2 vZ)))))
    (.seq (.ite (.eq vTAG v2) skipS (needEq vPL vZ)) (.seq (needEq vPOK v1) (needLe vPL vN)))

def admT : St VV :=
  .seq (.op (.copy t3 vN)) (.seq (powK 4) (.seq (.op (.shl t5)) (.seq (.op (.copy t7 vTW1)) (.seq (.op (.add t7 vTW2))
    (needLe t7 t5)))))

def admR1 (B1 : ℕ) : St VV :=
  .seq (.op (.copy t3 vN)) (.seq (powK B1) (.seq (.op (.mul t5 vNUM t7)) (.seq (needLe vDEN t7) (needEq vSG vZ))))
def admR2 : St VV :=
  .seq (setK t8 16) (.seq (.op (.mul t8 vNUM t9)) (.ite (.eq vSG vZ) (needLe t9 vDEN) skipS))
def admR3 (B2 : ℕ) : St VV :=
  .seq (.op (.copy t3 vN)) (.seq (powK B2) (.seq (.op (.copy t7 vRL)) (.seq (.op (.shl t7)) (.seq (incS t7 3)
    (needLe t7 t5)))))
def admR (B1 B2 : ℕ) : St VV := .seq (admR1 B1) (.seq admR2 (admR3 B2))

def admOne : St VV :=
  .seq admA (.seq (admW vG1 vC1 vTW1 vT1 vWOK1 vNZ1) (.seq (admW vG2 vC2 vTW2 vT2 vWOK2 vNZ2) admK))
def admTwo (B1 B2 : ℕ) : St VV := .seq admT (admR B1 B2)
def admitP (B1 B2 : ℕ) : St VV := .seq admOne (admTwo B1 B2)

def admT' : List (Fin VV) := [vADM, vJ, t3, t4, t5, t6, t7, t8, t9]

theorem admA_spec (a : DS VV) (hc : Cst a) (n : ℕ) (hN : a.env vN = n) (hW : 4 < 2 ^ C.Wd) :
    Hs C admA a 20 (fun b => b.env vADM = bnat (4 ≤ n) ∧ b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧
      Fr a b admT') := by
  refine Hx.hs (Hs.then (hs_copy C vADM v1 a (by decide)) (fun b hb n1 hn1 => ?_))
  subst hb
  refine Hs.then (setK_spec t3 (by decide) 4 _ hW) (fun d ⟨d1, d2, d3, d4, d5⟩ n2 hn2 => ?_)
  have dA : d.env vADM = bnat True := by rw [d5 vADM (by decide)]; vsimp [hc.one, bnat]
  refine Hs.last (needLe_spec t3 vN (by decide) d True dA) (fun e ⟨e1, e2, e3, e4, e5⟩ n3 hn3 => ?_)
  have dN : d.env vN = n := by rw [d5 vN (by decide)]; vsimp [hN]
  have hF : Fr a e admT' := Fr.trans (Fr.set a _ (by decide)) (Fr.trans (Fr.weaken d5 (by decide))
    (Fr.weaken e5 (by decide)))
  refine ⟨⟨by rw [e1, d1, dN]; exact bnat_congr (by simp), by rw [e2, d2]; rfl, by rw [e3, d3]; rfl,
    by rw [e4, d4]; rfl, Cst.of_fr hc hF (by decide) (by rw [hF vPOS (by decide), e2, d2]; exact hc.pos), hF⟩,
    by omega⟩

theorem admW_spec (g c tw t wok nz : Fin VV) (hgc : g ≠ c) (hnz : nz ≠ v1) (ht3 : t ≠ t3) (hwok : wok ≠ v1)
    (hT : g ∉ admT' ∧ c ∉ admT' ∧ tw ∉ admT' ∧ t ∉ admT' ∧ wok ∉ admT' ∧ nz ∉ admT')
    (a : DS VV) (hc : Cst a) (P : Prop) [Decidable P] (hP : a.env vADM = bnat P)
    (hW : 2 * a.env tw + 1 < 2 ^ C.Wd) :
    Hs C (admW g c tw t wok nz) a 30 (fun b => b.env vADM = bnat (P ∧ (a.env g = a.env c ∧ a.env nz = 1 ∧
      a.env t = 2 * a.env tw + 1 ∧ a.env wok = 1)) ∧ b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧
      Fr a b admT') := by
  obtain ⟨hg, hcT, htw, htT, hwT, hnT⟩ := hT
  refine Hx.hs (Hs.then (needEq_spec g c hgc a P hP) (fun b1 ⟨p1, p2, p3, p4, p5⟩ n1 hn1 => ?_))
  have F1 : Fr a b1 admT' := Fr.weaken p5 (by decide)
  refine Hs.then (needEq_spec nz v1 hnz b1 _ p1) (fun b2 ⟨q1, q2, q3, q4, q5⟩ n2 hn2 => ?_)
  have F2 : Fr a b2 admT' := Fr.trans F1 (Fr.weaken q5 (by decide))
  refine Hs.then (hs_copy C t3 tw b2 (fun e => htw (e ▸ (show t3 ∈ admT' by decide)))) (fun b3 h3 n3 hn3 => ?_)
  subst h3
  have b2tw : b2.env tw = a.env tw := F2 tw htw
  refine Hs.then (hs_shl C t3 _ (by rw [DS.set_env_self, b2tw]; omega)) (fun b4 h4 n4 hn4 => ?_)
  subst h4
  refine Hs.then (hs_inc C t3 _ (by rw [DS.set_env_self, DS.set_env_self, b2tw]; omega)) (fun b5 h5 n5 hn5 => ?_)
  subst h5
  set b5 := ((b2.set t3 (b2.env tw)).set t3 (2 * (b2.set t3 (b2.env tw)).env t3)).set t3
    (((b2.set t3 (b2.env tw)).set t3 (2 * (b2.set t3 (b2.env tw)).env t3)).env t3 + 1) with hb5
  have F5 : Fr a b5 admT' := Fr.trans F2 (Fr.trans (Fr.set _ _ (by decide)) (Fr.trans (Fr.set _ _ (by decide))
    (Fr.set _ _ (by decide))))
  have b5t3 : b5.env t3 = 2 * a.env tw + 1 := by rw [hb5]; vsimp [b2tw]
  have b5A : b5.env vADM = bnat ((P ∧ a.env g = a.env c) ∧ a.env nz = 1) := by
    have : b5.env vADM = b2.env vADM := by rw [hb5]; vsimp []
    rw [this, q1, F1 nz hnT, F1 v1 (by decide), hc.one]
  refine Hs.then (needEq_spec t t3 ht3 b5 _ b5A) (fun b6 ⟨r1, r2, r3, r4, r5⟩ n6 hn6 => ?_)
  have F6 : Fr a b6 admT' := Fr.trans F5 (Fr.weaken r5 (by decide))
  refine Hs.last (needEq_spec wok v1 hwok b6 _ r1) (fun b7 ⟨s1, s2, s3, s4, s5⟩ n7 hn7 => ?_)
  have F7 : Fr a b7 admT' := Fr.trans F6 (Fr.weaken s5 (by decide))
  refine ⟨⟨?_, by rw [s2, r2, hb5]; show b2.cp = _; rw [q2, p2], by rw [s3, r3, hb5]; show b2.wq = _; rw [q3, p3],
    by rw [s4, r4, hb5]; show b2.out = _; rw [q4, p4], Cst.of_fr hc F7 (by decide) ?_, F7⟩, by omega⟩
  · rw [s1, F6 wok hwT, F6 v1 (by decide), F5 t htT, b5t3, hc.one]
    exact bnat_congr (by tauto)
  · rw [F7 vPOS (by decide), hc.pos, s2, r2, hb5]; show a.cp = b2.cp; rw [q2, p2]

theorem admK_spec (a : DS VV) (hc : Cst a) (P : Prop) [Decidable P] (hP : a.env vADM = bnat P) :
    Hs C admK a 34 (fun b => b.env vADM = bnat (P ∧ ((a.env vTAG = 1 ∨ (a.env vG2 = 0 ∧ a.env vC2 = 0 ∧
      a.env vT2 = 1 ∧ a.env vTB2 = 0)) ∧ (a.env vTAG = 2 ∨ a.env vPL = 0) ∧ a.env vPOK = 1 ∧
      a.env vPL ≤ a.env vN)) ∧ b.cp = a.cp ∧
      b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧ Fr a b admT') := by
  -- the second circuit
  have s1 : Hs C (.ite (.eq vTAG v1) skipS (.seq (needEq vG2 vZ) (.seq (needEq vC2 vZ) (.seq (needEq vT2 v1)
      (needEq vTB2 vZ))))) a 12 (fun b => b.env vADM = bnat (P ∧ (a.env vTAG = 1 ∨ (a.env vG2 = 0 ∧ a.env vC2 = 0 ∧
        a.env vT2 = 1 ∧ a.env vTB2 = 0))) ∧ b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Fr a b [vADM, vJ]) := by
    refine Hs.ite (c := .eq vTAG v1) (show vTAG ≠ v1 by decide) (fun he => ?_) (fun he => ?_)
    · have h1 : a.env vTAG = 1 := by simpa [Cnd.eval, hc.one] using he
      refine Hs.mono (skip_spec a) (by omega) ?_
      rintro b rfl
      exact ⟨by rw [DS.set_env_ne _ _ (by decide), hP]; exact bnat_congr (by simp [h1]), rfl, rfl, rfl,
        Fr.set a _ (by decide)⟩
    · have h1 : a.env vTAG ≠ 1 := by simpa [Cnd.eval, hc.one] using he
      refine Hx.hs (Hs.then (needEq_spec vG2 vZ (by decide) a P hP) (fun b1 ⟨p1, p2, p3, p4, p5⟩ n1 hn1 => ?_))
      refine Hs.then (needEq_spec vC2 vZ (by decide) b1 _ p1) (fun b2 ⟨q1, q2, q3, q4, q5⟩ n2 hn2 => ?_)
      refine Hs.then (needEq_spec vT2 v1 (by decide) b2 _ q1) (fun b3 ⟨r1, r2, r3, r4, r5⟩ n3 hn3 => ?_)
      refine Hs.last (needEq_spec vTB2 vZ (by decide) b3 _ r1) (fun b4 ⟨w1, w2, w3, w4, w5⟩ n4 hn4 => ?_)
      have F : Fr a b3 [vADM, vJ] := Fr.trans p5 (Fr.trans q5 r5)
      refine ⟨⟨?_, by rw [w2, r2, q2, p2], by rw [w3, r3, q3, p3], by rw [w4, r4, q4, p4], Fr.trans F w5⟩, by omega⟩
      rw [w1, F vTB2 (by decide), F vZ (by decide), Fr.trans p5 q5 vT2 (by decide), Fr.trans p5 q5 v1 (by decide),
        p5 vC2 (by decide), p5 vZ (by decide), hc.z, hc.one]
      exact bnat_congr (by simp only [h1, false_or]; tauto)
  refine Hx.hs (Hs.then s1 (fun b1 ⟨p1, p2, p3, p4, p5⟩ n1 hn1 => ?_))
  have s2 : Hs C (.ite (.eq vTAG v2) skipS (needEq vPL vZ)) b1 3 (fun b => b.env vADM = bnat ((P ∧
      (a.env vTAG = 1 ∨ (a.env vG2 = 0 ∧ a.env vC2 = 0 ∧ a.env vT2 = 1 ∧ a.env vTB2 = 0))) ∧
      (a.env vTAG = 2 ∨ a.env vPL = 0)) ∧ b.cp = b1.cp ∧ b.wq = b1.wq ∧ b.out = b1.out ∧ Fr b1 b [vADM, vJ]) := by
    have tg : b1.env vTAG = a.env vTAG := p5 vTAG (by decide)
    refine Hs.ite (c := .eq vTAG v2) (show vTAG ≠ v2 by decide) (fun he => ?_) (fun he => ?_)
    · have h1 : a.env vTAG = 2 := by
        have := he; simp only [Cnd.eval, decide_eq_true_eq] at this; rw [tg, p5 v2 (by decide), hc.two] at this
        exact this
      refine Hs.mono (skip_spec b1) (by omega) ?_
      rintro b rfl
      exact ⟨by rw [DS.set_env_ne _ _ (by decide), p1]; exact bnat_congr (by simp [h1]), rfl, rfl, rfl,
        Fr.set b1 _ (by decide)⟩
    · have h1 : a.env vTAG ≠ 2 := by
        have := he; simp only [Cnd.eval, decide_eq_false_iff_not] at this; rw [tg, p5 v2 (by decide), hc.two] at this
        exact this
      refine Hs.mono (needEq_spec vPL vZ (by decide) b1 _ p1) (by omega) ?_
      rintro b ⟨w1, w2, w3, w4, w5⟩
      refine ⟨?_, w2, w3, w4, w5⟩
      rw [w1, p5 vPL (by decide), p5 vZ (by decide), hc.z]
      exact bnat_congr (by simp only [h1, false_or])
  refine Hs.then s2 (fun b2 ⟨q1, q2, q3, q4, q5⟩ n2 hn2 => ?_)
  refine Hs.then (needEq_spec vPOK v1 (by decide) b2 _ q1) (fun b3 ⟨r1, r2, r3, r4, r5⟩ n3 hn3 => ?_)
  refine Hs.last (needLe_spec vPL vN (by decide) b3 _ r1) (fun b4 ⟨s1, s2, s3, s4, s5⟩ n4 hn4 => ?_)
  have F : Fr a b4 admT' := Fr.weaken (Fr.trans p5 (Fr.trans q5 (Fr.trans r5 s5))) (by decide)
  have G : Fr a b3 [vADM, vJ] := Fr.trans p5 (Fr.trans q5 r5)
  refine ⟨⟨?_, by rw [s2, r2, q2, p2], by rw [s3, r3, q3, p3], by rw [s4, r4, q4, p4], Cst.of_fr hc F (by decide)
    (by rw [F vPOS (by decide), hc.pos, s2, r2, q2, p2]), F⟩, by omega⟩
  rw [s1, G vPL (by decide), G vN (by decide), Fr.trans p5 q5 vPOK (by decide), Fr.trans p5 q5 v1 (by decide), hc.one]
  exact bnat_congr (by tauto)

theorem admT_spec (a : DS VV) (hc : Cst a) (P : Prop) [Decidable P] (hP : a.env vADM = bnat P)
    (hW1 : ∀ j ≤ 4, a.env vN ^ j < 2 ^ C.Wd) (hW2 : 2 * a.env vN ^ 4 < 2 ^ C.Wd)
    (hW3 : a.env vTW1 + a.env vTW2 < 2 ^ C.Wd) :
    Hs C admT a 40 (fun b => b.env vADM = bnat (P ∧ a.env vTW1 + a.env vTW2 ≤ 2 * a.env vN ^ 4) ∧ b.cp = a.cp ∧
      b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧ Fr a b admT') := by
  refine Hx.hs (Hs.then (hs_copy C t3 vN a (by decide)) (fun b0 h0 n0 hn0 => ?_))
  subst h0
  have c0 : Cst (a.set t3 (a.env vN)) := Cst.of_fr (T := [t3]) hc (Fr.set a _ (by decide)) (by decide) (by vsimp [hc.pos])
  refine Hs.then (powK_spec _ c0 4 (by intro j hj; vsimp []; exact hW1 j hj))
    (fun b1 ⟨p1, p2, p3, p4, p5, p6, p7⟩ n1 hn1 => ?_)
  simp only [DS.env_set, Function.update_self] at p1
  refine Hs.then (hs_shl C t5 b1 (by rw [p1]; exact hW2)) (fun b2 h2 n2 hn2 => ?_)
  subst h2
  have F1 : Fr a b1 admT' := Fr.trans (Fr.set a _ (by decide)) (Fr.weaken p7 (by decide))
  refine Hs.then (hs_copy C t7 vTW1 _ (by decide)) (fun b3 h3 n3 hn3 => ?_)
  subst h3
  refine Hs.then (hs_add C t7 vTW2 _ (by decide) (by vsimp [F1 vTW1 (by decide), F1 vTW2 (by decide)]; exact hW3))
    (fun b4 h4 n4 hn4 => ?_)
  subst h4
  have b1A : b1.env vADM = bnat P := by rw [p7 vADM (by decide)]; vsimp [hP]
  refine Hs.last (needLe_spec t7 t5 (by decide) _ P (by vsimp [b1A])) (fun b5 ⟨r1, r2, r3, r4, r5⟩ n5 hn5 => ?_)
  have F : Fr a b5 admT' := Fr.trans F1 (Fr.trans (Fr.set _ _ (by decide)) (Fr.trans (Fr.set _ _ (by decide))
    (Fr.trans (Fr.set _ _ (by decide)) (Fr.weaken r5 (by decide)))))
  have hcp : b5.cp = a.cp := by rw [r2]; vsimp [p3]
  refine ⟨⟨?_, hcp, by rw [r3]; vsimp [p4], by rw [r4]; vsimp [p5], Cst.of_fr hc F (by decide)
    (by rw [F vPOS (by decide), hcp, hc.pos]), F⟩, by omega⟩
  rw [r1]; apply bnat_congr; vsimp [F1 vTW1 (by decide), F1 vTW2 (by decide), p1]

theorem admR1_spec (B1 : ℕ) (a : DS VV) (hc : Cst a) (P : Prop) [Decidable P] (hP : a.env vADM = bnat P)
    (hW1 : ∀ j ≤ B1, a.env vN ^ j < 2 ^ C.Wd) (hW2 : a.env vN ^ B1 * a.env vNUM < 2 ^ C.Wd) :
    Hs C (admR1 B1) a (4 * B1 + 20) (fun b => b.env vADM = bnat (P ∧ (a.env vDEN ≤ a.env vN ^ B1 * a.env vNUM ∧
      a.env vSG = 0)) ∧ b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧ Fr a b admT') := by
  refine Hx.hs (Hs.then (hs_copy C t3 vN a (by decide)) (fun b0 h0 n0 hn0 => ?_))
  subst h0
  have c0 : Cst (a.set t3 (a.env vN)) := Cst.of_fr (T := [t3]) hc (Fr.set a _ (by decide)) (by decide) (by vsimp [hc.pos])
  refine Hs.then (powK_spec _ c0 B1 (by intro j hj; vsimp []; exact hW1 j hj))
    (fun b1 ⟨p1, p2, p3, p4, p5, p6, p7⟩ n1 hn1 => ?_)
  simp only [DS.env_set, Function.update_self] at p1
  have F1 : Fr a b1 admT' := Fr.trans (Fr.set a _ (by decide)) (Fr.weaken p7 (by decide))
  refine Hs.then (hs_mul C t5 vNUM t7 b1 (by decide) (by decide) (by decide) (by rw [p1, F1 vNUM (by decide)]; exact hW2))
    (fun b2 h2 n2 hn2 => ?_)
  subst h2
  have b1A : b1.env vADM = bnat P := by rw [p7 vADM (by decide)]; vsimp [hP]
  refine Hs.then (needLe_spec vDEN t7 (by decide) _ P (by vsimp [b1A])) (fun b3 ⟨q1, q2, q3, q4, q5⟩ n3 hn3 => ?_)
  refine Hs.last (needEq_spec vSG vZ (by decide) b3 _ q1) (fun b4 ⟨r1, r2, r3, r4, r5⟩ n4 hn4 => ?_)
  have F : Fr a b4 admT' := Fr.trans F1 (Fr.trans (Fr.set _ _ (by decide)) (Fr.trans (Fr.weaken q5 (by decide))
    (Fr.weaken r5 (by decide))))
  have hcp : b4.cp = a.cp := by rw [r2, q2]; vsimp [p3]
  refine ⟨⟨?_, hcp, by rw [r3, q3]; vsimp [p4], by rw [r4, q4]; vsimp [p5], Cst.of_fr hc F (by decide)
    (by rw [F vPOS (by decide), hcp, hc.pos]), F⟩, by omega⟩
  rw [r1, q5 vSG (by decide), q5 vZ (by decide)]
  apply bnat_congr
  vsimp [F1 vDEN (by decide), F1 vNUM (by decide), F1 vSG (by decide), F1 vZ (by decide), hc.z, p1]
  tauto

theorem admR2_spec (a : DS VV) (hc : Cst a) (P : Prop) [Decidable P] (hP : a.env vADM = bnat P)
    (hW : 16 * a.env vNUM < 2 ^ C.Wd) (h16 : 16 < 2 ^ C.Wd) :
    Hs C admR2 a 60 (fun b => b.env vADM = bnat (P ∧ (a.env vSG = 0 → 16 * a.env vNUM ≤ a.env vDEN)) ∧
      b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧ Fr a b admT') := by
  refine Hx.hs (Hs.then (setK_spec t8 (by decide) 16 a (by omega)) (fun b1 ⟨p1, p2, p3, p4, p5⟩ n1 hn1 => ?_))
  have F1 : Fr a b1 admT' := Fr.weaken p5 (by decide)
  refine Hs.then (hs_mul C t8 vNUM t9 b1 (by decide) (by decide) (by decide) (by rw [p1, F1 vNUM (by decide)]; exact hW))
    (fun b2 h2 n2 hn2 => ?_)
  subst h2
  have b2A : (b1.set t9 (b1.env t8 * b1.env vNUM)).env vADM = bnat P := by
    vsimp [p5 vADM (by decide), hP]
  have b2SG : (b1.set t9 (b1.env t8 * b1.env vNUM)).env vSG = a.env vSG := by vsimp [F1 vSG (by decide)]
  have s3 : Hs C (.ite (.eq vSG vZ) (needLe t9 vDEN) skipS) (b1.set t9 (b1.env t8 * b1.env vNUM)) 3 (fun b =>
      b.env vADM = bnat (P ∧ (a.env vSG = 0 → 16 * a.env vNUM ≤ a.env vDEN)) ∧
      b.cp = b1.cp ∧ b.wq = b1.wq ∧ b.out = b1.out ∧ Fr (b1.set t9 (b1.env t8 * b1.env vNUM)) b [vADM, vJ]) := by
    refine Hs.ite (c := .eq vSG vZ) (show vSG ≠ vZ by decide) (fun he => ?_) (fun he => ?_)
    · have h0 : a.env vSG = 0 := by
        have := he; simp only [Cnd.eval, decide_eq_true_eq] at this; rw [b2SG] at this
        rw [this]; vsimp [F1 vZ (by decide), hc.z]
      refine Hs.mono (needLe_spec t9 vDEN (by decide) _ P b2A) le_rfl ?_
      rintro b ⟨w1, w2, w3, w4, w5⟩
      refine ⟨?_, w2, w3, w4, w5⟩
      rw [w1]; apply bnat_congr
      vsimp [p1, F1 vNUM (by decide), F1 vDEN (by decide), h0]
    · have h0 : a.env vSG ≠ 0 := by
        have := he; simp only [Cnd.eval, decide_eq_false_iff_not] at this; rw [b2SG] at this
        intro h; apply this; rw [h]; vsimp [F1 vZ (by decide), hc.z]
      refine Hs.mono (skip_spec _) (by omega) ?_
      rintro b rfl
      refine ⟨?_, rfl, rfl, rfl, Fr.set _ _ (by decide)⟩
      rw [DS.set_env_ne _ _ (by decide), b2A]; exact bnat_congr (by simp [h0])
  refine Hs.last s3 (fun b3 ⟨q1, q2, q3, q4, q5⟩ n3 hn3 => ?_)
  have F : Fr a b3 admT' := Fr.trans F1 (Fr.trans (Fr.set _ _ (by decide)) (Fr.weaken q5 (by decide)))
  have hcp : b3.cp = a.cp := by rw [q2, p2]
  exact ⟨⟨q1, hcp, by rw [q3, p3], by rw [q4, p4], Cst.of_fr hc F (by decide)
    (by rw [F vPOS (by decide), hcp, hc.pos]), F⟩, by omega⟩

theorem admR3_spec (B2 : ℕ) (a : DS VV) (hc : Cst a) (P : Prop) [Decidable P] (hP : a.env vADM = bnat P)
    (hW1 : ∀ j ≤ B2, a.env vN ^ j < 2 ^ C.Wd) (hW2 : 2 * a.env vRL + 3 < 2 ^ C.Wd) :
    Hs C (admR3 B2) a (4 * B2 + 30) (fun b => b.env vADM = bnat (P ∧ 2 * a.env vRL + 3 ≤ a.env vN ^ B2) ∧
      b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧ Fr a b admT') := by
  refine Hx.hs (Hs.then (hs_copy C t3 vN a (by decide)) (fun b0 h0 n0 hn0 => ?_))
  subst h0
  have c0 : Cst (a.set t3 (a.env vN)) := Cst.of_fr (T := [t3]) hc (Fr.set a _ (by decide)) (by decide) (by vsimp [hc.pos])
  refine Hs.then (powK_spec _ c0 B2 (by intro j hj; vsimp []; exact hW1 j hj))
    (fun b1 ⟨p1, p2, p3, p4, p5, p6, p7⟩ n1 hn1 => ?_)
  simp only [DS.env_set, Function.update_self] at p1
  have F1 : Fr a b1 admT' := Fr.trans (Fr.set a _ (by decide)) (Fr.weaken p7 (by decide))
  refine Hs.then (hs_copy C t7 vRL b1 (by decide)) (fun b2 h2 n2 hn2 => ?_)
  subst h2
  refine Hs.then (hs_shl C t7 _ (by vsimp [F1 vRL (by decide)]; omega)) (fun b3 h3 n3 hn3 => ?_)
  subst h3
  refine Hs.then (incS_spec t7 (by decide) 3 _ (by vsimp [F1 vRL (by decide)]; omega))
    (fun b4 ⟨q1, q2, q3, q4, q5⟩ n4 hn4 => ?_)
  have b4A : b4.env vADM = bnat P := by rw [q5 vADM (by decide)]; vsimp [p7 vADM (by decide), hP]
  refine Hs.last (needLe_spec t7 t5 (by decide) b4 P b4A) (fun b5 ⟨r1, r2, r3, r4, r5⟩ n5 hn5 => ?_)
  have F : Fr a b5 admT' := Fr.trans F1 (Fr.trans (Fr.set _ _ (by decide)) (Fr.trans (Fr.set _ _ (by decide))
    (Fr.trans (Fr.weaken q5 (by decide)) (Fr.weaken r5 (by decide)))))
  have hcp : b5.cp = a.cp := by rw [r2, q2]; vsimp [p3]
  refine ⟨⟨?_, hcp, by rw [r3, q3]; vsimp [p4], by rw [r4, q4]; vsimp [p5], Cst.of_fr hc F (by decide)
    (by rw [F vPOS (by decide), hcp, hc.pos]), F⟩, by omega⟩
  rw [r1, q1, q5 t5 (by decide)]
  apply bnat_congr
  vsimp [F1 vRL (by decide), p1]

/-! ## The whole admission test -/

theorem pow_le_of_lt (x L j B : ℕ) (hx : x < 2 ^ L) (hj : j ≤ B) : x ^ j ≤ 2 ^ (L * B) := by
  calc x ^ j ≤ (2 ^ L) ^ j := Nat.pow_le_pow_left hx.le j
    _ = 2 ^ (L * j) := by rw [← pow_mul]
    _ ≤ 2 ^ (L * B) := Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ hj)

/-- The conjunction the admission program computes (in its order). -/
def AdmFlag (B1 B2 : ℕ) (c : Call) : Prop :=
  ((((((4 ≤ c.n ∧ (c.first.gates.length = c.first.coeffs.length ∧ bnat (∀ x ∈ c.first.coeffs, x ≠ 0) = 1 ∧
    c.first.table.length = 2 * c.first.topWeight + 1 ∧ bnat (∀ g ∈ c.first.gates, GateOK (Call.B0 c.n) g) = 1)) ∧
  (c.second.gates.length = c.second.coeffs.length ∧ bnat (∀ x ∈ c.second.coeffs, x ≠ 0) = 1 ∧
    c.second.table.length = 2 * c.second.topWeight + 1 ∧ bnat (∀ g ∈ c.second.gates, GateOK (Call.B0 c.n) g) = 1)) ∧
  ((kindTag c.kind = 1 ∨ (c.second.gates.length = 0 ∧ c.second.coeffs.length = 0 ∧ c.second.table.length = 1 ∧
    (c.second.table.getD 0 false).toNat = 0)) ∧ (kindTag c.kind = 2 ∨ c.parity.length = 0) ∧
    bnat (∀ i ∈ c.parity, i < c.n) = 1 ∧ c.parity.length ≤ c.n)) ∧
  c.first.topWeight + c.second.topWeight ≤ 2 * c.n ^ 4) ∧
  (c.radius.den ≤ c.n ^ B1 * c.radius.num.natAbs ∧ (if c.radius.num < 0 then 1 else 0) = 0)) ∧
  ((if c.radius.num < 0 then 1 else 0) = 0 → 16 * c.radius.num.natAbs ≤ c.radius.den)) ∧
  2 * (natBitLength (if c.radius.num < 0 then 1 else 0) + natBitLength c.radius.num.natAbs +
    natBitLength c.radius.den) + 3 ≤ c.n ^ B2

instance (B1 B2 : ℕ) (c : Call) : Decidable (AdmFlag B1 B2 c) := by unfold AdmFlag; infer_instance

/-- The structural half of the flag. -/
def AdmS (c : Call) : Prop :=
  ((4 ≤ c.n ∧ (c.first.gates.length = c.first.coeffs.length ∧ bnat (∀ x ∈ c.first.coeffs, x ≠ 0) = 1 ∧
    c.first.table.length = 2 * c.first.topWeight + 1 ∧ bnat (∀ g ∈ c.first.gates, GateOK (Call.B0 c.n) g) = 1)) ∧
  (c.second.gates.length = c.second.coeffs.length ∧ bnat (∀ x ∈ c.second.coeffs, x ≠ 0) = 1 ∧
    c.second.table.length = 2 * c.second.topWeight + 1 ∧ bnat (∀ g ∈ c.second.gates, GateOK (Call.B0 c.n) g) = 1)) ∧
  ((kindTag c.kind = 1 ∨ (c.second.gates.length = 0 ∧ c.second.coeffs.length = 0 ∧ c.second.table.length = 1 ∧
    (c.second.table.getD 0 false).toNat = 0)) ∧ (kindTag c.kind = 2 ∨ c.parity.length = 0) ∧
    bnat (∀ i ∈ c.parity, i < c.n) = 1 ∧ c.parity.length ≤ c.n)

instance (c : Call) : Decidable (AdmS c) := by unfold AdmS; infer_instance

theorem admOne_spec (c : Call) (a : DS VV) (hc : Cst a) (hp : ParseOut c a)
    (hW : 2 * (callWord c).length + 5 ≤ C.Wd) :
    Hs C admOne a 120 (fun b => b.env vADM = bnat (AdmS c) ∧ b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧
      Fr a b admT') := by
  obtain ⟨bn, btw1, btw2, -, -, -⟩ := call_bounds c
  set L := (callWord c).length
  have hLW : 2 ^ (L + 1) ≤ 2 ^ C.Wd := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hL1 : 2 ^ (L + 1) = 2 * 2 ^ L := by ring
  have h4 : 4 < 2 ^ C.Wd := by
    have : 2 ^ 3 ≤ 2 ^ C.Wd := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  refine Hx.hs (Hs.then (admA_spec a hc c.n hp.n h4) (fun b1 ⟨p1, p2', p3, p4, p5, p6⟩ n1 hn1 => ?_))
  have v1 : ∀ x, x ∉ admT' → b1.env x = a.env x := fun x h => p6 x h
  refine Hs.then (admW_spec vG1 vC1 vTW1 vT1 vWOK1 vNZ1 (by decide) (by decide) (by decide) (by decide) (by decide)
    b1 p5 _ p1 (by rw [v1 vTW1 (by decide), hp.c1.tw]; omega)) (fun b2 ⟨q1, q2, q3, q4, q5, q6⟩ n2 hn2 => ?_)
  have v2 : ∀ x, x ∉ admT' → b2.env x = a.env x := fun x h => by rw [q6 x h, v1 x h]
  refine Hs.then (admW_spec vG2 vC2 vTW2 vT2 vWOK2 vNZ2 (by decide) (by decide) (by decide) (by decide) (by decide)
    b2 q5 _ q1 (by rw [v2 vTW2 (by decide), hp.c2.tw]; omega)) (fun b3 ⟨r1, r2, r3, r4, r5, r6⟩ n3 hn3 => ?_)
  have v3 : ∀ x, x ∉ admT' → b3.env x = a.env x := fun x h => by rw [r6 x h, v2 x h]
  refine Hs.last (admK_spec b3 r5 _ r1) (fun b4 ⟨s1, s2, s3, s4, s5, s6⟩ n4 hn4 => ?_)
  refine ⟨⟨?_, by rw [s2, r2, q2, p2'], by rw [s3, r3, q3, p3], by rw [s4, r4, q4, p4], s5,
    Fr.trans p6 (Fr.trans q6 (Fr.trans r6 s6))⟩, by omega⟩
  rw [s1]
  apply bnat_congr
  rw [v3 vTAG (by decide), v3 vG2 (by decide), v3 vC2 (by decide), v3 vT2 (by decide), v3 vTB2 (by decide),
    v3 vPL (by decide), v3 vPOK (by decide), v3 vN (by decide), v2 vG2 (by decide), v2 vC2 (by decide), v2 vTW2 (by decide),
    v2 vT2 (by decide), v2 vWOK2 (by decide), v2 vNZ2 (by decide), v1 vG1 (by decide), v1 vC1 (by decide),
    v1 vTW1 (by decide), v1 vT1 (by decide), v1 vWOK1 (by decide), v1 vNZ1 (by decide)]
  rw [hp.n, hp.tag, hp.c2.g, hp.c2.c, hp.c2.t, hp.c2.tb, hp.pl, hp.pok, hp.c1.g, hp.c1.c, hp.c1.t, hp.c1.wok, hp.c1.nz,
    hp.c2.wok, hp.c2.nz, hp.c1.tw, hp.c2.tw]
  unfold AdmS
  exact Iff.rfl

/-- The numeric half of the flag. -/
def AdmN (B1 B2 : ℕ) (c : Call) : Prop :=
  (((c.first.topWeight + c.second.topWeight ≤ 2 * c.n ^ 4) ∧
  (c.radius.den ≤ c.n ^ B1 * c.radius.num.natAbs ∧ (if c.radius.num < 0 then 1 else 0) = 0)) ∧
  ((if c.radius.num < 0 then 1 else 0) = 0 → 16 * c.radius.num.natAbs ≤ c.radius.den)) ∧
  2 * (natBitLength (if c.radius.num < 0 then 1 else 0) + natBitLength c.radius.num.natAbs +
    natBitLength c.radius.den) + 3 ≤ c.n ^ B2

instance (B1 B2 : ℕ) (c : Call) : Decidable (AdmN B1 B2 c) := by unfold AdmN; infer_instance

theorem admTwo_bounds (B1 B2 : ℕ) (c : Call) (W : ℕ) (hW : (B1 + B2 + 5) * ((callWord c).length + 1) ≤ W) :
    (∀ j ≤ 4, c.n ^ j < 2 ^ W) ∧ 2 * c.n ^ 4 < 2 ^ W ∧ c.first.topWeight + c.second.topWeight < 2 ^ W ∧
    (∀ j ≤ B1, c.n ^ j < 2 ^ W) ∧ c.n ^ B1 * c.radius.num.natAbs < 2 ^ W ∧ 16 * c.radius.num.natAbs < 2 ^ W ∧
    16 < 2 ^ W ∧ (∀ j ≤ B2, c.n ^ j < 2 ^ W) ∧
    2 * (natBitLength (if c.radius.num < 0 then 1 else 0) + natBitLength c.radius.num.natAbs +
      natBitLength c.radius.den) + 3 < 2 ^ W := by
  obtain ⟨bn, btw1, btw2, bnum, -, brl⟩ := call_bounds c
  generalize (callWord c).length = L at *
  have p2 : ∀ x y : ℕ, x < y → 2 ^ x < 2 ^ y := fun x y h => Nat.pow_lt_pow_right (by norm_num) h
  have hpow : ∀ B j, j ≤ B → L * B < W → c.n ^ j < 2 ^ W := fun B j hj h =>
    lt_of_le_of_lt (pow_le_of_lt c.n L j B bn hj) (p2 _ _ h)
  have hexp : (B1 + B2 + 5) * (L + 1) = L * B1 + L * B2 + 5 * L + B1 + B2 + 5 := by ring
  rw [hexp] at hW
  have e1 : L * 4 < W := by omega
  have e2 : L * B1 + L < W := by omega
  have e3 : L * B2 < W := by omega
  have e4 : L + 5 ≤ W := by omega
  refine ⟨fun j hj => hpow 4 j hj e1, ?_, ?_, fun j hj => hpow B1 j hj (by omega), ?_, ?_, ?_,
    fun j hj => hpow B2 j hj e3, ?_⟩
  · calc 2 * c.n ^ 4 ≤ 2 * 2 ^ (L * 4) := Nat.mul_le_mul_left _ (pow_le_of_lt c.n L 4 4 bn le_rfl)
      _ = 2 ^ (L * 4 + 1) := by ring
      _ < 2 ^ W := p2 _ _ (by omega)
  · calc c.first.topWeight + c.second.topWeight < 2 ^ L + 2 ^ L := by omega
      _ = 2 ^ (L + 1) := by ring
      _ < 2 ^ W := p2 _ _ (by omega)
  · calc c.n ^ B1 * c.radius.num.natAbs ≤ 2 ^ (L * B1) * 2 ^ L :=
          Nat.mul_le_mul (pow_le_of_lt c.n L B1 B1 bn le_rfl) bnum.le
      _ = 2 ^ (L * B1 + L) := by ring
      _ < 2 ^ W := p2 _ _ e2
  · calc 16 * c.radius.num.natAbs ≤ 16 * 2 ^ L := by omega
      _ = 2 ^ (L + 4) := by ring
      _ < 2 ^ W := p2 _ _ (by omega)
  · calc (16 : ℕ) = 2 ^ 4 := by norm_num
      _ < 2 ^ W := p2 _ _ (by omega)
  · have : 2 * L + 5 < 2 ^ (2 * L + 5) := Nat.lt_two_pow_self
    have h2 : 2 ^ (2 * L + 5) ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

theorem admTwo_spec (B1 B2 : ℕ) (c : Call) (a : DS VV) (hc : Cst a) (hp : ParseOut c a) (P : Prop) [Decidable P]
    (hP : a.env vADM = bnat P) (hW : (B1 + B2 + 5) * ((callWord c).length + 1) ≤ C.Wd) :
    Hs C (admTwo B1 B2) a (4 * B1 + 4 * B2 + 160) (fun b => b.env vADM = bnat (P ∧ AdmN B1 B2 c) ∧ b.cp = a.cp ∧
      b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧ Fr a b admT') := by
  obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8, w9⟩ := admTwo_bounds B1 B2 c C.Wd hW
  have ga : ∀ x, x ∉ admT' → ∀ b : DS VV, Fr a b admT' → b.env x = a.env x := fun x h b hb => hb x h
  refine Hx.hs (Hs.then (admT_spec a hc _ hP (by rw [hp.n]; exact w1) (by rw [hp.n]; exact w2)
    (by rw [hp.c1.tw, hp.c2.tw]; exact w3)) (fun b5 ⟨t1', t2', t3', t4', t5', t6'⟩ n5 hn5 => ?_))
  have v5 : ∀ x, x ∉ admT' → b5.env x = a.env x := fun x h => t6' x h
  refine Hs.then (admR1_spec B1 b5 t5' _ t1' (by rw [v5 vN (by decide), hp.n]; exact w4)
    (by rw [v5 vN (by decide), v5 vNUM (by decide), hp.n, hp.num]; exact w5))
    (fun b6 ⟨u1, u2, u3, u4, u5, u6⟩ n6 hn6 => ?_)
  have v6 : ∀ x, x ∉ admT' → b6.env x = a.env x := fun x h => by rw [u6 x h, v5 x h]
  refine Hs.then (admR2_spec b6 u5 _ u1 (by rw [v6 vNUM (by decide), hp.num]; exact w6) w7)
    (fun b7 ⟨y1, y2, y3, y4, y5, y6⟩ n7 hn7 => ?_)
  have v7 : ∀ x, x ∉ admT' → b7.env x = a.env x := fun x h => by rw [y6 x h, v6 x h]
  refine Hs.last (admR3_spec B2 b7 y5 _ y1 (by rw [v7 vN (by decide), hp.n]; exact w8)
    (by rw [v7 vRL (by decide), hp.rl]; exact w9)) (fun b8 ⟨x1, x2, x3, x4, x5, x6⟩ n8 hn8 => ?_)
  refine ⟨⟨?_, by rw [x2, y2, u2, t2'], by rw [x3, y3, u3, t3'], by rw [x4, y4, u4, t4'], x5,
    Fr.trans t6' (Fr.trans u6 (Fr.trans y6 x6))⟩, by omega⟩
  rw [x1]
  apply bnat_congr
  rw [v7 vRL (by decide), v7 vN (by decide), v6 vSG (by decide), v6 vNUM (by decide), v6 vDEN (by decide),
    v5 vDEN (by decide), v5 vN (by decide), v5 vNUM (by decide), v5 vSG (by decide)]
  rw [hp.rl, hp.n, hp.sg, hp.num, hp.den, hp.c1.tw, hp.c2.tw]
  unfold AdmN
  tauto

def admCost (B1 B2 : ℕ) : ℕ := 120 + (4 * B1 + 4 * B2 + 160) + 1

theorem admitP_spec (B1 B2 : ℕ) (c : Call) (a : DS VV) (hc : Cst a) (hp : ParseOut c a)
    (hW : (B1 + B2 + 5) * ((callWord c).length + 1) ≤ C.Wd) :
    Hs C (admitP B1 B2) a (admCost B1 B2) (fun b => b.env vADM = bnat (AdmS c ∧ AdmN B1 B2 c) ∧ b.cp = a.cp ∧
      b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧ Fr a b admT') := by
  have hexp : (B1 + B2 + 5) * ((callWord c).length + 1) = (callWord c).length * B1 + (callWord c).length * B2 +
      5 * (callWord c).length + B1 + B2 + 5 := by ring
  refine Hs.seq (admOne_spec c a hc hp (by omega)) (fun b ⟨b1, b2, b3, b4, b5, b6⟩ => ?_)
  have hpb : ParseOut c b := by
    have F := fun x (h : x ∉ admT') => b6 x h
    exact ⟨by rw [F vN (by decide)]; exact hp.n, by rw [F vTAG (by decide)]; exact hp.tag,
      by rw [F vB0 (by decide)]; exact hp.b0,
      ⟨by rw [F vG1 (by decide)]; exact hp.c1.g, by rw [F vC1 (by decide)]; exact hp.c1.c,
        by rw [F vTW1 (by decide)]; exact hp.c1.tw, by rw [F vT1 (by decide)]; exact hp.c1.t,
        by rw [F vTB1 (by decide)]; exact hp.c1.tb, by rw [F vWOK1 (by decide)]; exact hp.c1.wok,
        by rw [F vNZ1 (by decide)]; exact hp.c1.nz, by rw [F vCO1 (by decide)]; exact hp.c1.co⟩,
      ⟨by rw [F vG2 (by decide)]; exact hp.c2.g, by rw [F vC2 (by decide)]; exact hp.c2.c,
        by rw [F vTW2 (by decide)]; exact hp.c2.tw, by rw [F vT2 (by decide)]; exact hp.c2.t,
        by rw [F vTB2 (by decide)]; exact hp.c2.tb, by rw [F vWOK2 (by decide)]; exact hp.c2.wok,
        by rw [F vNZ2 (by decide)]; exact hp.c2.nz, by rw [F vCO2 (by decide)]; exact hp.c2.co⟩,
      by rw [F vPL (by decide)]; exact hp.pl, by rw [F vPP (by decide)]; exact hp.pp,
      by rw [F vPOK (by decide)]; exact hp.pok, by rw [F vSG (by decide)]; exact hp.sg,
      by rw [F vNUM (by decide)]; exact hp.num, by rw [F vDEN (by decide)]; exact hp.den,
      by rw [F vRL (by decide)]; exact hp.rl, by rw [F vCL (by decide)]; exact hp.cl⟩
  refine Hs.mono (admTwo_spec B1 B2 c b b5 hpb _ b1 hW) le_rfl ?_
  rintro d ⟨d1, d2, d3, d4, d5, d6⟩
  exact ⟨d1, by rw [d2, b2], by rw [d3, b3], by rw [d4, b4], d5, Fr.trans b6 d6⟩

/-! ## The flag is admission -/

theorem bnat_eq_one (P : Prop) [Decidable P] : bnat P = 1 ↔ P := by unfold bnat; by_cases h : P <;> simp [h]

theorem natBitLength_le_iff (x B : ℕ) (hB : 1 ≤ B) : natBitLength x ≤ B ↔ x < 2 ^ B := by
  unfold natBitLength
  rcases Nat.eq_zero_or_pos x with h | h
  · subst h; simp only [Nat.log_zero_right, zero_add]; exact ⟨fun _ => by positivity, fun _ => hB⟩
  · rw [show Nat.log 2 x + 1 ≤ B ↔ Nat.log 2 x < B by omega, Nat.log_lt_iff_lt_pow (by norm_num) (by omega)]

theorem gateOK_iff {n : ℕ} (B : ℕ) (hB : 1 ≤ B) (g : NormalizedThresholdGate n) :
    GateOK B g ↔ (∀ i, (g.weight i).natAbs < 2 ^ B) ∧ g.threshold.natAbs < 2 ^ B := by
  unfold GateOK
  rw [List.forall_mem_ofFn_iff]
  simp only [natBitLength_le_iff _ _ hB]

theorem wellFormed_iff {n : ℕ} (Cc : NCircuit n) (B : ℕ) (hB : 1 ≤ B) :
    Cc.WellFormed B ↔ (Cc.gates.length = Cc.coeffs.length ∧ bnat (∀ x ∈ Cc.coeffs, x ≠ 0) = 1 ∧
      Cc.table.length = 2 * Cc.topWeight + 1 ∧ bnat (∀ g ∈ Cc.gates, GateOK B g) = 1) := by
  rw [bnat_eq_one, bnat_eq_one]
  unfold NCircuit.WellFormed
  simp only [gateOK_iff B hB]

theorem empty_iff {n : ℕ} (Cc : NCircuit n) : Cc = NCircuit.empty n ↔ (Cc.gates.length = 0 ∧ Cc.coeffs.length = 0 ∧
    Cc.table.length = 1 ∧ (Cc.table.getD 0 false).toNat = 0) := by
  constructor
  · rintro rfl; simp [NCircuit.empty]
  · rintro ⟨h1, h2, h3, h4⟩
    obtain ⟨gs, cs, tb⟩ := Cc
    simp only [List.length_eq_zero_iff] at h1 h2
    subst h1; subst h2
    match tb, h3, h4 with
    | [b], _, h4 => cases b <;> simp_all [NCircuit.empty]

theorem kindTag_eq_one (k : CallKind) : kindTag k = 1 ↔ k = .pair := by cases k <;> simp [kindTag]
theorem kindTag_eq_two (k : CallKind) : kindTag k = 2 ↔ k = .parity := by cases k <;> simp [kindTag]

theorem one_le_mul_iff (q : ℚ) (m : ℕ) : (1 : ℚ) ≤ q * m ↔ (q.den : ℤ) ≤ q.num * m := by
  have hd : (0 : ℚ) < q.den := by exact_mod_cast q.den_pos
  conv_lhs => rw [← Rat.num_div_den q]
  rw [div_mul_eq_mul_div, le_div_iff₀ hd, one_mul]
  exact_mod_cast Iff.rfl

theorem le_sixteenth_iff (q : ℚ) : q ≤ 1 / 16 ↔ 16 * q.num ≤ q.den := by
  have hd : (0 : ℚ) < q.den := by exact_mod_cast q.den_pos
  conv_lhs => rw [← Rat.num_div_den q]
  rw [div_le_iff₀ hd]
  constructor
  · intro h; have : (16 : ℚ) * q.num ≤ q.den := by linarith
    exact_mod_cast this
  · intro h; have : (16 : ℚ) * q.num ≤ q.den := by exact_mod_cast h
    linarith

theorem ratWord_length (q : ℚ) : (ratWord q).length = 2 * (natBitLength (if q.num < 0 then 1 else 0) +
    natBitLength q.num.natAbs + natBitLength q.den) + 3 := by
  simp only [ratWord, Interfaces.intWord, List.length_append, natWord_length]; ring

theorem radius_one_iff (q : ℚ) (m : ℕ) : (1 : ℚ) ≤ q * (m : ℚ) ↔
    (q.den ≤ m * q.num.natAbs ∧ (if q.num < 0 then 1 else 0) = 0) := by
  rw [one_le_mul_iff]
  have hd := q.den_pos
  by_cases hn : q.num < 0
  · simp only [hn, if_true]
    constructor
    · intro h; nlinarith
    · rintro ⟨_, h⟩; exact absurd h (by norm_num)
  · simp only [hn, if_false, and_true]
    have : (q.num : ℤ) = (q.num.natAbs : ℤ) := by omega
    rw [this, mul_comm]
    exact_mod_cast Iff.rfl

theorem radius_le_iff (q : ℚ) : q ≤ 1 / 16 ↔ ((if q.num < 0 then 1 else 0) = 0 → 16 * q.num.natAbs ≤ q.den) := by
  rw [le_sixteenth_iff]
  by_cases hn : q.num < 0
  · simp only [hn, if_true, one_ne_zero, false_imp_iff, iff_true]; omega
  · simp only [hn, if_false, forall_const]
    omega

/-- **The computed flag is exactly admission** (`Call.Admitted`, lines 1544–1559). -/
theorem admFlag_iff (B1 B2 : ℕ) (c : Call) : (AdmS c ∧ AdmN B1 B2 c) ↔ c.Admitted B1 B2 := by
  unfold AdmS AdmN Call.Admitted
  constructor
  · rintro ⟨⟨⟨⟨h4, w1⟩, w2⟩, ⟨k1, k2, k3, k4⟩⟩, ⟨⟨⟨hw, r1⟩, r2⟩, r3⟩⟩
    have hB : 1 ≤ Call.B0 c.n := by
      unfold Call.B0; have : 1 ≤ Nat.clog 2 (c.n + 1) := Nat.clog_pos (by norm_num) (by omega); nlinarith
    refine ⟨h4, (wellFormed_iff _ _ hB).2 w1, (wellFormed_iff _ _ hB).2 w2, ?_, ?_, (bnat_eq_one _).1 k3, ?_, ?_, ?_, ?_,
      k4⟩
    · intro hk; rcases k1 with h | h
      · exact absurd ((kindTag_eq_one _).1 h) hk
      · exact (empty_iff _).2 h
    · intro hk; rcases k2 with h | h
      · exact absurd ((kindTag_eq_two _).1 h) hk
      · exact List.length_eq_zero_iff.1 h
    · exact hw
    · rw [show (c.n : ℚ) ^ B1 = ((c.n ^ B1 : ℕ) : ℚ) by push_cast; rfl, radius_one_iff]
      exact ⟨r1.1, r1.2⟩
    · exact (radius_le_iff _).2 r2
    · rw [ratWord_length]; exact r3
  · rintro ⟨h4, w1, w2, k1, k2, k3, hw, r1, r2, r3, k4⟩
    have hB : 1 ≤ Call.B0 c.n := by
      unfold Call.B0; have : 1 ≤ Nat.clog 2 (c.n + 1) := Nat.clog_pos (by norm_num) (by omega); nlinarith
    refine ⟨⟨⟨⟨h4, (wellFormed_iff _ _ hB).1 w1⟩, (wellFormed_iff _ _ hB).1 w2⟩, ⟨?_, ?_, (bnat_eq_one _).2 k3, k4⟩⟩,
      ⟨⟨⟨hw, ?_⟩, (radius_le_iff _).1 r2⟩, by rw [← ratWord_length]; exact r3⟩⟩
    · by_cases hk : c.kind = .pair
      · left; exact (kindTag_eq_one _).2 hk
      · right; exact (empty_iff _).1 (k1 hk)
    · by_cases hk : c.kind = .parity
      · left; exact (kindTag_eq_two _).2 hk
      · right; rw [k2 hk]; rfl
    · rw [show (c.n : ℚ) ^ B1 = ((c.n ^ B1 : ℕ) : ℚ) by push_cast; rfl, radius_one_iff] at r1
      exact ⟨r1.1, r1.2⟩

end NearCubicGates.Close.Dispatch
