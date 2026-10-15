import Proof.Gates.Dispatch.WitDock

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

theorem Hs.addValid {s : St VV} {a : DS VV} {t : ℕ} {R : DS VV → Prop} (hW : 1 ≤ C.Wd) (ha : Valid C a)
    (h : Hs C s a t R) : Hs C s a t (fun b => R b ∧ Valid C b) := by
  obtain ⟨b, n, hx, hn, hb⟩ := h
  exact ⟨b, n, hx, hn, hb, hx.valid hW ha⟩

theorem natBitLength_le_of_lt {x W : ℕ} (h : x < 2 ^ W) (hW : 1 ≤ W) : natBitLength x ≤ W := by
  unfold natBitLength
  rcases Nat.eq_zero_or_pos x with h0 | h0
  · subst h0; simp; omega
  · have := Nat.log_lt_of_lt_pow (by omega) h; omega

theorem wd_small (W : ℕ) (h : 3 ≤ W) : W + 2 < 2 ^ W := by
  induction W, h using Nat.le_induction with
  | base => norm_num
  | succ w hw ih => rw [pow_succ]; omega

/-! ## One variable -/

def pv (x : Fin VV) : St VV := .seq (assign t3 (.var x)) emitNat

def pvT : List (Fin VV) := [t3, t5, t6, t7, t8, t9, vJ]

def pvCost (W : ℕ) : ℕ := 40 * W + 100

theorem pv_spec (x : Fin VV) (hx : x.val < 200 ∧ x ≠ vJ) (a : DS VV) (hc : Cst a) (hv : Valid C a)
    (hW3 : 3 ≤ C.Wd) :
    Hs C (pv x) a (pvCost C.Wd) (fun b => b.out = a.out ++ natWord (a.env x) ∧ b.cp = a.cp ∧ b.wq = a.wq ∧
      Cst b ∧ FrS a b pvT) := by
  refine Hx.hs (Hs.then (assign_spec t3 (by decide) (by decide) (.var x) a (by simp [AE.vars_ok]; exact hx)
    (by aevar) hc (by trivial)) (fun b1 ⟨p1, p2, p3, p4, p5, p6⟩ k1 hk1 => ?_))
  simp only [AE.eval] at p1
  have hbl : natBitLength (a.env x) ≤ C.Wd := natBitLength_le_of_lt (hv.env_lt x) (by omega)
  have hW2 : C.Wd + 2 < 2 ^ C.Wd := wd_small _ hW3
  refine Hs.last (emitNat_spec b1 p6 (by omega) (by rw [p1]; omega)) (fun g ⟨g1, g2, g3, g4, g5⟩ k2 hk2 => ?_)
  rw [p1] at g1 hk2
  refine ⟨⟨by rw [g1, p5], by rw [g2, p3], by rw [g3, p4], g4,
    FrS.trans (p2.toS _ (by decide) (by decide)) (g5.toS.weaken (by decide))⟩, ?_⟩
  simp only [AE.cost] at hk1
  unfold pvCost; omega

/-! ## A list of variables -/

def printVars : List (Fin VV) → St VV
  | [] => skipS
  | x :: xs => .seq (pv x) (printVars xs)

theorem printVars_spec (xs : List (Fin VV)) (hxs : ∀ x ∈ xs, x.val < 200 ∧ x ∉ pvT) (hW3 : 3 ≤ C.Wd) :
    ∀ (a : DS VV), Cst a → Valid C a →
    Hs C (printVars xs) a (xs.length * (pvCost C.Wd + 1) + 1) (fun b =>
      b.out = a.out ++ xs.flatMap (fun x => natWord (a.env x)) ∧ b.cp = a.cp ∧ b.wq = a.wq ∧ Cst b ∧ Valid C b ∧
      FrS a b pvT) := by
  induction xs with
  | nil =>
    intro a hc hv
    refine Hs.mono (skip_spec a) (by simp) ?_
    rintro b rfl
    exact ⟨by simp, rfl, rfl, Cst.set hc _ _ (by decide), ⟨fun y => by
        by_cases hy : y = vJ
        · subst hy; rw [DS.set_env_self]; exact lt_of_lt_of_le (by norm_num) (Nat.one_le_two_pow)
        · rw [DS.set_env_ne _ _ hy]; exact hv.env_lt y, hv.cp_le, hv.wq_le⟩,
      Fr.toS (Fr.set _ _ (by decide))⟩
  | cons x xs ih =>
    intro a hc hv
    have hx := hxs x (List.mem_cons_self)
    refine Hs.mono (Hs.seq (Hs.addValid (by omega) hv (pv_spec x ⟨hx.1, fun h => hx.2 (by rw [h]; decide)⟩ a hc hv hW3)) (fun b ⟨⟨b1, b2, b3, b4, b5⟩, b6⟩ =>
      Hs.mono (ih (fun y hy => hxs y (List.mem_cons_of_mem _ hy)) b b4 b6) le_rfl
        (fun d ⟨d1, d2, d3, d4, d5, d6⟩ => ?_))) (by simp only [List.length_cons]; ring_nf; omega) (fun d h => h)
    refine ⟨?_, by rw [d2, b2], by rw [d3, b3], d4, d5, FrS.trans b5 d6⟩
    rw [d1, b1, List.flatMap_cons, List.append_assoc]
    congr 2
    apply List.flatMap_congr
    intro y hy
    have := hxs y (List.mem_cons_of_mem _ hy)
    rw [b5 y this.1 this.2]

/-! ## The sorted prime list -/

theorem sort_dyadic (P : ℕ) :
    (dyadicPrimes P).sort (· ≤ ·) = (List.range (P + 1)).filter (fun q => decide (DyP P q)) := by
  refine List.Perm.eq_of_pairwise' (r := (· ≤ ·)) (Finset.pairwise_sort _ _)
    (((List.pairwise_lt_range).filter _).imp le_of_lt) ?_
  rw [List.perm_ext_iff_of_nodup (Finset.sort_nodup _ _) ((List.nodup_range).filter _)]
  intro x
  rw [Finset.mem_sort, dyadicPrimes_eq]
  simp

open AE in
def prPBody : St VV :=
  .seq (assign IPQ (var pQ)) (.seq isPrimeV (.seq (assign pX8 (mul (lit 2) (var pQ)))
    (.seq (.ite (.eq IPF v1) (.ite (.lt pP pX8) (pv pQ) skipS) skipS) (assign pQ (add (var pQ) (lit 1))))))

open AE in
def prPrint : St VV :=
  .seq (assign pQ (lit 0)) (.seq (assign pX7 (add (var pP) (lit 1))) (.loop (.lt pQ pX7) prPBody))

def prPT : List (Fin VV) := [pQ, pX7, pX8, IPQ, IPF, IPD, IPQ2, IPR, t3, t5, t6, t7, t8, t9, vJ]

def PPI (a0 : DS VV) (P j : ℕ) (b : DS VV) : Prop :=
  b.env pQ = j ∧ b.env pX7 = P + 1 ∧ b.env pP = P ∧
    b.out = a0.out ++ ((List.range j).filter (fun q => decide (DyP P q))).flatMap natWord ∧ b.cp = a0.cp ∧
    b.wq = a0.wq ∧ Cst b ∧ Valid C b ∧ FrS a0 b prPT

theorem prPBody_spec (a0 : DS VV) (P j : ℕ) (hj : j < P + 1) (hW3 : 3 ≤ C.Wd)
    (hW : 2 * (P + 1) + 8 < 2 ^ C.Wd) (b : DS VV) (hb : PPI (C := C) a0 P j b) :
    Hs C prPBody b (9 * P + pvCost C.Wd + 100) (PPI (C := C) a0 P (j + 1)) := by
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8, i9⟩ := hb
  have hW1 : 1 ≤ C.Wd := by omega
  refine Hx.hs (Hs.then (Hs.addValid hW1 i8 (assign_spec IPQ (by decide) (by decide) (.var pQ) b (by aevar) (by aevar)
    i7 (by trivial))) (fun b1 ⟨⟨p1, p2, p3, p4, p5, p6⟩, p7⟩ k1 hk1 => ?_))
  simp only [AE.eval, i1] at p1
  refine Hs.then (Hs.addValid hW1 p7 (isPrimeV_spec b1 p6 j p1 (by omega)))
    (fun b2 ⟨⟨q1, q2, q3, q4, q5, q6⟩, q7⟩ k2 hk2 => ?_)
  have b2Q : b2.env pQ = j := by simp (disch := decide) only [q6.ev, p2.ev]; exact i1
  refine Hs.then (Hs.addValid hW1 q7 (assign_spec pX8 (by decide) (by decide) (.mul (.lit 2) (.var pQ)) b2 (by aevar)
    (by aevar) q5 (by aeok [b2Q]))) (fun b3 ⟨⟨r1, r2, r3, r4, r5, r6⟩, r7⟩ k3 hk3 => ?_)
  simp only [AE.eval, b2Q] at r1
  have b3P : b3.env pP = P := by simp (disch := decide) only [r2.ev, q6.ev, p2.ev]; exact i3
  have b3F : b3.env IPF = bnat (Nat.Prime j) := by simp (disch := decide) only [r2.ev]; exact q1
  have b3Q : b3.env pQ = j := by simp (disch := decide) only [r2.ev]; exact b2Q
  have step : Hs C (.ite (.eq IPF v1) (.ite (.lt pP pX8) (pv pQ) skipS) skipS) b3 (pvCost C.Wd + 2) (fun g =>
      g.out = b3.out ++ (if DyP P j then natWord j else []) ∧ g.cp = b3.cp ∧ g.wq = b3.wq ∧ Cst g ∧ Valid C g ∧
      FrS b3 g pvT) := by
    have sk : Hs C skipS b3 (pvCost C.Wd) (fun g => g.out = b3.out ∧ g.cp = b3.cp ∧ g.wq = b3.wq ∧ Cst g ∧
        Valid C g ∧ FrS b3 g pvT) := by
      refine Hs.mono (skip_spec b3) (by unfold pvCost; omega) ?_
      rintro g rfl
      exact ⟨rfl, rfl, rfl, Cst.set r6 _ _ (by decide), ⟨fun y => by
          by_cases hy : y = vJ
          · subst hy; rw [DS.set_env_self]; exact lt_of_lt_of_le (by norm_num) (Nat.one_le_two_pow)
          · rw [DS.set_env_ne _ _ hy]; exact r7.env_lt y, r7.cp_le, r7.wq_le⟩,
        Fr.toS (Fr.set _ _ (by decide))⟩
    by_cases hd : DyP P j
    · rw [if_pos hd]
      have hF : b3.env IPF = 1 := by rw [b3F]; unfold bnat; simp [hd.1]
      refine Hs.iteT (show IPF ≠ v1 by decide) (by simp [Cnd.eval, hF, r6.one]) ?_
      refine Hs.mono (Hs.iteT (show pP ≠ pX8 by decide) (by simp [Cnd.eval, b3P, r1, hd.2]) ?_) le_rfl (fun g h => h)
      refine Hs.mono (Hs.addValid hW1 r7 (pv_spec pQ ⟨by decide, by decide⟩ b3 r6 r7 hW3)) le_rfl ?_
      rintro g ⟨⟨g1, g2, g3, g4, g5⟩, g6⟩
      exact ⟨by rw [g1, b3Q], g2, g3, g4, g6, g5⟩
    · rw [if_neg hd]
      refine Hs.ite (show IPF ≠ v1 by decide) (fun he => ?_) (fun _ => Hs.mono sk (by omega)
        (fun g ⟨g1, g2⟩ => ⟨by rw [g1, List.append_nil], g2⟩))
      have hp : Nat.Prime j := by
        have : b3.env IPF = 1 := by simpa [Cnd.eval, r6.one] using he
        rw [b3F] at this; unfold bnat at this; by_contra h; simp [h] at this
      have hle : ¬ P < 2 * j := fun h => hd ⟨hp, h⟩
      refine Hs.iteF (show pP ≠ pX8 by decide) (by simp [Cnd.eval, b3P, r1, hle]) ?_
      exact Hs.mono sk (by omega) (fun g ⟨g1, g2⟩ => ⟨by rw [g1, List.append_nil], g2⟩)
  refine Hs.then step (fun b4 ⟨s1, s2, s3, s4, s5, s6⟩ k4 hk4 => ?_)
  have b4Q : b4.env pQ = j := by simp (disch := decide) only [s6.ev]; exact b3Q
  refine Hs.last (Hs.addValid hW1 s5 (assign_spec pQ (by decide) (by decide) (.add (.var pQ) (.lit 1)) b4 (by aevar)
    (by aevar) s4 (by aeok [b4Q]))) (fun g ⟨⟨g1, g2, g3, g4, g5, g6⟩, g7⟩ k5 hk5 => ?_)
  simp only [AE.eval, b4Q] at g1
  refine ⟨⟨g1, ?_, ?_, ?_, by rw [g3, s2, r3, q2, p3, i5], by rw [g4, s3, r4, q3, p4, i6], g6, g7, ?_⟩, ?_⟩
  · simp (disch := decide) only [g2.ev, s6.ev, r2.ev, q6.ev, p2.ev]; exact i2
  · simp (disch := decide) only [g2.ev, s6.ev, r2.ev, q6.ev, p2.ev]; exact i3
  · rw [g5, s1, r5, q4, p5, i4, List.range_succ, List.filter_append, List.flatMap_append, List.append_assoc]
    by_cases hd : DyP P j <;> simp [hd]
  · exact FrS.trans i9 (FrS.trans (p2.toS _ (by decide) (by decide)) (FrS.trans (q6.toS.weaken (by decide))
      (FrS.trans (r2.toS _ (by decide) (by decide)) (FrS.trans (s6.weaken (by decide))
      (g2.toS _ (by decide) (by decide))))))
  · simp only [AE.cost] at hk1 hk3 hk5
    omega

def prPrintCost (P W : ℕ) : ℕ := (P + 1) * (9 * P + pvCost W + 100 + 2) + 100

theorem prPrint_spec (a : DS VV) (hc : Cst a) (hv : Valid C a) (P : ℕ) (hP : a.env pP = P) (hW3 : 3 ≤ C.Wd)
    (hW : 2 * (P + 1) + 8 < 2 ^ C.Wd) :
    Hs C prPrint a (prPrintCost P C.Wd) (fun b => b.out = a.out ++ ((dyadicPrimes P).sort (· ≤ ·)).flatMap natWord ∧
      b.cp = a.cp ∧ b.wq = a.wq ∧ Cst b ∧ Valid C b ∧ FrS a b prPT) := by
  have hW1 : 1 ≤ C.Wd := by omega
  refine Hx.hs (Hs.then (Hs.addValid hW1 hv (assign_spec pQ (by decide) (by decide) (.lit 0) a (by aevar) (by aevar) hc
    (by aeok []))) (fun b1 ⟨⟨p1, p2, p3, p4, p5, p6⟩, p7⟩ k1 hk1 => ?_))
  have b1P : b1.env pP = P := by simp (disch := decide) only [p2.ev]; exact hP
  refine Hs.then (Hs.addValid hW1 p7 (assign_spec pX7 (by decide) (by decide) (.add (.var pP) (.lit 1)) b1 (by aevar)
    (by aevar) p6 (by aeok [b1P]))) (fun b2 ⟨⟨q1, q2, q3, q4, q5, q6⟩, q7⟩ k2 hk2 => ?_)
  simp only [AE.eval, b1P] at q1 p1
  have hI : PPI (C := C) b2 P 0 b2 := ⟨by simp (disch := decide) only [q2.ev]; exact p1, q1,
    by simp (disch := decide) only [q2.ev]; exact b1P, by simp, rfl, rfl, q6, q7, fun _ _ _ => rfl⟩
  have l := Hs.loopN (C := C) (c := .lt pQ pX7) (s := prPBody) (show pQ ≠ pX7 by decide) (PPI (C := C) b2 P) (P + 1)
    (9 * P + pvCost C.Wd + 100) (fun j hj d hd => ⟨by simp [Cnd.eval, hd.1, hd.2.1, hj],
      prPBody_spec b2 P j hj hW3 hW d hd⟩) (fun d hd => by simp [Cnd.eval, hd.1, hd.2.1]) b2 hI
  refine Hs.last l (fun g ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9⟩ k3 hk3 => ?_)
  refine ⟨⟨by rw [g4, q5, p5, sort_dyadic], by rw [g5, q3, p3], by rw [g6, q4, p4], g7, g8,
    FrS.trans (p2.toS _ (by decide) (by decide)) (FrS.trans (q2.toS _ (by decide) (by decide)) g9)⟩, ?_⟩
  simp only [AE.cost] at hk1 hk2
  unfold prPrintCost
  omega

/-! ## Copying the call word -/

def copyCW : St VV := .seq (.op .rstC) (.seq (.op (.zero vPOS)) (.loop (.lt vPOS vCL) (.seq rdc (emitB t0))))

def CWI (a0 : DS VV) (j : ℕ) (b : DS VV) : Prop :=
  b.cp = j ∧ b.env vPOS = j ∧ b.env vCL = C.cw.length ∧ b.out = a0.out ++ C.cw.take j ∧ b.wq = a0.wq ∧ Cst b ∧
    Valid C b ∧ FrS a0 b [t0, vPOS, vJ]

theorem decide_bitOf (l : List Bool) (j : ℕ) (hj : j < l.length) : decide (bitOf l j = 1) = l[j] := by
  unfold bitOf
  rw [List.getD_eq_getElem _ _ hj]
  cases l[j] <;> rfl

theorem copyCW_spec (a : DS VV) (hc : Cst a) (hv : Valid C a) (hcl : a.env vCL = C.cw.length)
    (hW : C.cw.length < 2 ^ C.Wd) (hW1 : 1 ≤ C.Wd) :
    Hs C copyCW a (C.cw.length * 8 + 6) (fun b => b.out = a.out ++ C.cw ∧ b.cp = C.cw.length ∧ b.wq = a.wq ∧
      Cst b ∧ Valid C b ∧ FrS a b [t0, vPOS, vJ]) := by
  refine Hx.hs (Hs.then (hs_rstC (C := C) a) (fun b1 e1 k1 hk1 => ?_))
  subst e1
  refine Hs.then (hs_zero C vPOS _) (fun b2 e2 k2 hk2 => ?_)
  subst e2
  have hI : CWI (C := C) a 0 ({ a with cp := 0 }.set vPOS 0) := by
    refine ⟨rfl, by rw [DS.set_env_self], by rw [DS.set_env_ne _ _ (by decide)]; exact hcl, by simp [DS.set],
      rfl, ⟨by rw [DS.set_env_ne _ _ (by decide)]; exact hc.z, by rw [DS.set_env_ne _ _ (by decide)]; exact hc.one,
        by rw [DS.set_env_ne _ _ (by decide)]; exact hc.two, by rw [DS.set_env_self]; rfl⟩,
      ⟨fun y => ?_, by simp [DS.set], hv.wq_le⟩, fun y _ hy => ?_⟩
    · by_cases hy : y = vPOS
      · subst hy; rw [DS.set_env_self]; exact Nat.two_pow_pos _
      · rw [DS.set_env_ne _ _ hy]; exact hv.env_lt y
    · rw [DS.set_env_ne _ _ (fun h => hy (by simp [h]))]
  have l := Hs.loopN (C := C) (c := .lt vPOS vCL) (s := .seq rdc (emitB t0)) (show vPOS ≠ vCL by decide)
    (CWI (C := C) a) C.cw.length 6 (fun j hj d ⟨d1, d2, d3, d4, d5, d6, d7, d8⟩ => ⟨by simp [Cnd.eval, d2, d3, hj], ?_⟩)
    (fun d hd => by simp [Cnd.eval, hd.2.1, hd.2.2.1]) _ hI
  · refine Hs.last l (fun g hg k3 hk3 => ⟨⟨by rw [hg.2.2.2.1, List.take_length], hg.1, hg.2.2.2.2.1, hg.2.2.2.2.2.1,
      hg.2.2.2.2.2.2.1, hg.2.2.2.2.2.2.2⟩, by omega⟩)
  · refine Hs.seq (t2 := 2) (rdc_spec d (by rw [d2, d1]) (by omega) hW) (fun e ⟨e1, e2, e3, e4, e5, e6⟩ => ?_)
    refine Hs.mono (emitB_spec t0 (by decide) e (Cst.of_fr d6 e6 (by decide) (by rw [e2, e3]))) le_rfl ?_
    rintro f ⟨f1, f2, f3, f4⟩
    have hfe : ∀ y, f.env y = e.env y := fun y => by rw [f4]
    refine ⟨by rw [f2, e3, d1], by rw [hfe, e2, d1], by rw [hfe, e6 vCL (by decide), d3], ?_, by rw [f3, e4, d5],
      ⟨by rw [hfe, e6 vZ (by decide)]; exact d6.z, by rw [hfe, e6 v1 (by decide)]; exact d6.one,
        by rw [hfe, e6 v2 (by decide)]; exact d6.two, by rw [hfe, e2, f2, e3, d1]⟩,
      ⟨fun y => by rw [hfe]; by_cases hy : y ∈ [t0, vPOS]
                   · simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
                     rcases hy with rfl | rfl
                     · rw [e1]; exact lt_of_le_of_lt (bitOf_le _ _) (Nat.one_lt_two_pow (by omega))
                     · rw [e2]; omega
                   · rw [e6 y hy]; exact d7.env_lt y,
        by rw [f2, e3, d1]; omega, by rw [f3, e4]; exact d7.wq_le⟩,
      fun y hy hT => by rw [hfe, e6 y (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hT ⊢; tauto),
        d8 y hy hT]⟩
    have hb : decide (e.env t0 = 1) = C.cw[j]'(by omega) := by rw [e1, d1]; exact decide_bitOf C.cw j (by omega)
    rw [f1, e5, d4, hb, List.append_assoc, List.take_add_one, List.getElem?_eq_getElem (by omega)]
    rfl

end NearCubicGates.Close.Dispatch
