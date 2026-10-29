import SourceAdapters.ShortPCP.Machines.FLangDGt
import SourceAdapters.ShortPCP.Machines.FLangParseMask

/-!
# Single-run time, machine layer 28: the answers of a sub-verifier run

proof of `thm:short-pcp-ours` ("The queries of V0 are computed from the random string alone") and proof of `thm:short-pcp-ours` (the proof bits are
read at addresses below `L_π`): the decision half reads the answer words of all queries from the answer bits in `16`
(block `3` of `f` bits per query, in query order). For each effective position `k` of the outer verifier
(`TimeBlocks`), `ansBody` computes the query (`qOutP`), its source (`kindP`), reads the block word, adds `p_x` at the
implicit-input point for `V_I` (an abstract machine `P` with the `pxP` interface), and appends the answer word to the
packed list in `11` (`ansLoop_spec`). The value is `ansVal` (`answersN` of the join's tables once the block words are the
oracle's words).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace NearCubicGates.Adapters.ShortPCP.Machines.FL

open NearCubicWires.WireExponent3_5 NearCubicGates.Adapters.ShortPCP.Time NearCubicGates.Published.BCGT13
open NearCubicWires.CanonicalBinary

variable (G : Glob)

/-- The value of an answer: the block word (plus `p_x` at the point for the implicit input of `V_I`), or `0`. -/
def ansVal {F : Type} [Field F] (o : Option ℕ) (nS len : ℕ) (w : F) (pxv : ℕ → F) (px : Bool) : F :=
  match o with
  | none => 0
  | some j => if 1 ≤ j ∧ j ≤ nS then w + (if px then pxv (j - 1) else 0) else if j - nS - 1 < len ∧ nS < j then w
    else 0

/-- `p_x` at the point of an implicit-input answer (`V_I` only): `5 := 5 ⊕ p_x(9 − 1)`. -/
def pxPart : Option S → S
  | some P => .ite (.eq (.v 12) (.k 1)) (.seq (.set 52 (.sub (.v 9) (.k 1))) (.seq P (.set 5 (.fadd (.v 5) (.v 53)))))
      .skip
  | none => .skip

/-- One answer (position `14 + 1`; block `3`; packed list `11`). -/
def ansBody (v : Bool) (pxS : Option S) (lenE pBE πBE : E) : S :=
  .seq (qOutP v) (.seq (kindP lenE pBE πBE)
    (.seq (.set 5 (.md (.shr (.v 16) (.mul (.v 3) (.v 23))) nSE))
    (.seq (pxPart pxS)
    (.seq (.ite (.eq (.v 12) (.k 0)) (.set 12 (.k 0)) (.set 12 (.v 5)))
    (.seq (.set 3 (.add (.v 3) (.k 1)))
      (.set 11 (.add (.v 11) (.shl (.v 12) (.mul (.add (.v 14) (.k 1)) (.v 23))))))))))

/-- **The answers of a sub-verifier run**: `11 := 0`, then one answer per effective position. -/
def ansLoop (v : Bool) (pxS : Option S) (lenE pBE πBE qcE : E) : S :=
  .seq (.set 11 (.k 0)) (.loop 14 qcE (ansBody v pxS lenE pBE πBE))

/-- The variables the answer machines write (besides those of the `p_x` machine). -/
def ansW : List Var := [3, 5, 11, 12, 13, 14, 52, 53] ++ qW ++ pxW

theorem QC.jb4 {s : FS} {l0 : List ℕ} {u : List Bool} (c : QC G s l0 u) : 4 * jB s.fl + 4 * 2 ^ s.fl ≤ G.cap := by
  have hK := c.K
  have hf1 := (fl_bounds c.ok).1
  have e : 10 * s.fl + 34 ≤ 2 * ((s.fl + 1) * (8 * s.fl + 16)) := by nlinarith
  have := pow_le_cap (G := G) (a := 10 * s.fl + 34) (by omega)
  rw [show 10 * s.fl + 34 = (10 * s.fl + 30) + 4 by ring, pow_add] at this
  have : 2 ^ s.fl ≤ 2 ^ (10 * s.fl + 30) := Nat.pow_le_pow_right (by norm_num) (by omega)
  unfold jB; omega

variable {F : Type} [Field F] [CharP F 2] [DecidableEq F]

omit [CharP F 2] [DecidableEq F] in
theorem kindOf_cases (o : Option ℕ) (nS len : ℕ) :
    (kindOf o nS len = 0 ∧ ∀ (w : F) pxv px, ansVal o nS len w pxv px = 0) ∨
    (∃ j, o = some j ∧ 1 ≤ j ∧ j ≤ nS ∧ kindOf o nS len = 1 ∧
      ∀ (w : F) pxv px, ansVal o nS len w pxv px = w + (if px then pxv (j - 1) else 0)) ∨
    (kindOf o nS len = 2 ∧ ∀ (w : F) pxv px, ansVal o nS len w pxv px = w) := by
  cases o with
  | none => left; exact ⟨rfl, fun _ _ _ => rfl⟩
  | some j =>
    by_cases h1 : 1 ≤ j ∧ j ≤ nS
    · right; left; exact ⟨j, rfl, h1.1, h1.2, by simp [kindOf, h1], fun w pxv px => by simp [ansVal, h1]⟩
    by_cases h2 : j - nS - 1 < len ∧ nS < j
    · right; right; exact ⟨by simp [kindOf, h1, h2], fun w pxv px => by simp only [ansVal, if_neg h1, if_pos h2]⟩
    · left; exact ⟨by simp [kindOf, h1, h2], fun w pxv px => by simp only [ansVal, if_neg h1, if_neg h2]⟩

/-- **One answer.** -/
theorem ansBody_spec (v : Bool) (pxS : Option S) (lenE pBE πBE : E) (s : FS) (φ : AdjoinRoot (GF.toPoly s.fp) →+* F)
    (u : List Bool) (l0 : List ℕ) (BH : List F) (OH : F) (d j len pB πB W b A : ℕ) (pxv : ℕ → F)
    (c : QC G s l0 u) (h14 : s.env 14 = j) (h6 : s.env 6 = innD v BH.length d)
    (hk : j + 1 ≤ qcO v s.fl (innD v BH.length d))
    (hdb : (innD v BH.length d + 4) * 2 ^ (8 * s.fl + 20) ≤ G.cap)
    (h16 : s.env 16 = W) (h3 : s.env 3 = b) (h11 : s.env 11 = A)
    (hlen : ∀ t, Wr qW s t → evalE G t lenE = len) (hpB : ∀ t, Wr qW s t → evalE G t pBE = pB)
    (hπB : ∀ t, Wr qW s t → evalE G t πBE = πB) (hpb : pB + 2 ^ s.fl ≤ G.cap) (hπb : πB + len ≤ G.cap)
    (hb : (b + 1) * s.fl ≤ G.cap) (hA : A < 2 ^ ((j + 1) * s.fl)) (hAc : 2 ^ ((j + 2) * s.fl) ≤ G.cap + 1)
    (hpx : ∀ P, pxS = some P → ∀ t : FS, QC G t l0 u → Wr ansW s t → t.env 52 < 2 ^ s.fl →
      (evalS G P t).env 53 < 2 ^ s.fl ∧ ev φ ((evalS G P t).env 53) = pxv (t.env 52) ∧ Wr pxW t (evalS G P t)) :
    let t := evalS G (ansBody v pxS lenE pBE πBE) s
    ∃ y, y < 2 ^ s.fl ∧ ev φ y = ansVal ((outV v (l0.map (ev φ)) 0 BH OH d).Q u (idxO s.fl (innD v BH.length d) (j + 1)))
        (2 ^ s.fl) len (ev φ (W / 2 ^ (b * s.fl) % 2 ^ s.fl)) pxv pxS.isSome ∧
      t.env 11 = A + y * 2 ^ ((j + 1) * s.fl) ∧ t.env 3 = b + 1 ∧ Wr ansW s t := by
  intro t
  obtain ⟨hf1, hfK, hmod, -⟩ := fl_bounds c.ok
  have hjb := c.jb4
  have hcK := cap_ge G
  obtain ⟨q1, q9, qw⟩ := qOutP_spec G v s φ u l0 BH OH d (j + 1) c (by rw [h14]) h6 hk hdb
  generalize ht1 : evalS G (qOutP v) s = t1 at q1 q9 qw
  have c1 : QC G t1 l0 u := c.wr qw (by decide) qw.fp
  have hfl1 : t1.fl = s.fl := qw.fl
  obtain ⟨k12, k13, kw⟩ := kindP_spec G lenE pBE πBE t1 s.fl len pB πB (c1.h23.trans hfl1) (by omega) (hlen t1 qw)
    (hpB t1 qw) (hπB t1 qw) (by omega) hpb hπb (by have := tf_le c.ok; omega)
  generalize ht2 : evalS G (kindP lenE pBE πBE) t1 = t2 at k12 k13 kw
  have c2 : QC G t2 l0 u := c1.wr kw (by decide) kw.fp
  have hfl2 : t2.fl = s.fl := kw.fl.trans hfl1
  have A2 : Atoms G t2 s.fl := by have := c2.atoms; rwa [hfl2] at this
  have e16 : t2.env 16 = W := by rw [kw.env 16 (by decide), qw.env 16 (by decide), h16]
  have e3 : t2.env 3 = b := by rw [kw.env 3 (by decide), qw.env 3 (by decide), h3]
  have e11 : t2.env 11 = A := by rw [kw.env 11 (by decide), qw.env 11 (by decide), h11]
  have e14 : t2.env 14 = j := by rw [kw.env 14 (by decide), qw.env 14 (by decide), h14]
  have e9 : t2.env 9 = t1.env 9 := kw.env 9 (by decide)
  set w := W / 2 ^ (b * s.fl) % 2 ^ s.fl with hw
  have hwl : w < 2 ^ s.fl := Nat.mod_lt _ (by positivity)
  have ew : evalE G t2 (.md (.shr (.v 16) (.mul (.v 3) (.v 23))) nSE) = w :=
    eE_md (eE_shr (eE_v 16 |>.trans e16) (eE_mul (eE_v 3 |>.trans e3) (eE_v 23 |>.trans (c2.h23.trans hfl2))
      (by have : (b + 1) * s.fl ≥ b * s.fl := Nat.mul_le_mul_right _ (by omega); omega))) A2.n
  have hjc : j + 2 < 2 ^ ((j + 2) * s.fl) :=
    lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_of_pos_right _ hf1))
  -- the tail: select, count, append
  have tail : ∀ t4 : FS, t4.env 23 = s.fl → t4.env 14 = j → t4.env 3 = b → t4.env 11 = A → t4.env 12 = t2.env 12 →
      (if t2.env 12 = 0 then 0 else t4.env 5) < 2 ^ s.fl →
      evalS G (.seq (.ite (.eq (.v 12) (.k 0)) (.set 12 (.k 0)) (.set 12 (.v 5)))
        (.seq (.set 3 (.add (.v 3) (.k 1)))
          (.set 11 (.add (.v 11) (.shl (.v 12) (.mul (.add (.v 14) (.k 1)) (.v 23))))))) t4 =
      ((t4.setv 12 (if t2.env 12 = 0 then 0 else t4.env 5)).setv 3 (b + 1)).setv 11
        (A + (if t2.env 12 = 0 then 0 else t4.env 5) * 2 ^ ((j + 1) * s.fl)) := by
    intro t4 h23 h14' h3' h11' h12 hy
    generalize hyd : (if t2.env 12 = 0 then 0 else t4.env 5) = y at hy ⊢
    have hsel : evalS G (.ite (.eq (.v 12) (.k 0)) (.set 12 (.k 0)) (.set 12 (.v 5))) t4 = t4.setv 12 y := by
      rw [evalS_ite, eE_eq (eE_v 12 |>.trans h12) (eE_k (by omega))]
      by_cases hz : t2.env 12 = 0
      · rw [if_pos hz] at hyd ⊢; rw [if_neg one_ne_zero, evalS_set, eE_k (by omega), hyd]
      · rw [if_neg hz] at hyd ⊢; rw [if_pos rfl, evalS_set, eE_v, hyd]
    have hp : y * 2 ^ ((j + 1) * s.fl) < 2 ^ ((j + 2) * s.fl) := by
      rw [show (j + 2) * s.fl = s.fl + (j + 1) * s.fl by ring, pow_add]
      exact Nat.mul_lt_mul_of_pos_right hy (by positivity)
    have hsum : A + y * 2 ^ ((j + 1) * s.fl) < 2 ^ ((j + 2) * s.fl) := by
      have : y * 2 ^ ((j + 1) * s.fl) + 2 ^ ((j + 1) * s.fl) ≤ 2 ^ ((j + 2) * s.fl) := by
        rw [show (j + 2) * s.fl = s.fl + (j + 1) * s.fl by ring, pow_add]
        have := Nat.mul_le_mul_right (2 ^ ((j + 1) * s.fl)) (show y + 1 ≤ 2 ^ s.fl by omega)
        rw [add_mul, one_mul] at this; exact this
      omega
    have hb1 : b + 1 ≤ (b + 1) * s.fl := Nat.le_mul_of_pos_right _ hf1
    have e3 : evalE G (t4.setv 12 y) (.add (.v 3) (.k 1)) = b + 1 :=
      eE_add (show evalE G _ (.v 3) = b by simp [evalE, h3']) (eE_k (by omega)) (by omega)
    have e11 : evalE G ((t4.setv 12 y).setv 3 (b + 1))
        (.add (.v 11) (.shl (.v 12) (.mul (.add (.v 14) (.k 1)) (.v 23)))) = A + y * 2 ^ ((j + 1) * s.fl) := by
      have em : evalE G ((t4.setv 12 y).setv 3 (b + 1)) (.mul (.add (.v 14) (.k 1)) (.v 23)) = (j + 1) * s.fl :=
        eE_mul (eE_add (show evalE G _ (.v 14) = j by simp [evalE, h14']) (eE_k (by omega)) (by omega))
          (show evalE G _ (.v 23) = s.fl by simp [evalE, h23]) (by
            have : (j + 1) * s.fl < 2 ^ ((j + 1) * s.fl) := Nat.lt_two_pow_self
            have : 2 ^ ((j + 1) * s.fl) ≤ 2 ^ ((j + 2) * s.fl) := Nat.pow_le_pow_right (by norm_num)
              (Nat.mul_le_mul_right _ (by omega))
            omega)
      have es : evalE G ((t4.setv 12 y).setv 3 (b + 1)) (.shl (.v 12) (.mul (.add (.v 14) (.k 1)) (.v 23))) =
          y * 2 ^ ((j + 1) * s.fl) := by
        show min (evalE G _ (.v 12) * 2 ^ evalE G _ (.mul (.add (.v 14) (.k 1)) (.v 23))) G.cap = _
        rw [em, show evalE G ((t4.setv 12 y).setv 3 (b + 1)) (.v 12) = y by simp [evalE]]
        exact min_eq_left (by omega)
      exact eE_add (show evalE G _ (.v 11) = A by simp [evalE, h11']) es (by omega)
    rw [evalS_seq, hsel, evalS_seq, evalS_set, evalS_set, e3, e11]
  have hpre : t = evalS G (.seq (pxPart pxS)
      (.seq (.ite (.eq (.v 12) (.k 0)) (.set 12 (.k 0)) (.set 12 (.v 5)))
        (.seq (.set 3 (.add (.v 3) (.k 1))) (.set 11 (.add (.v 11) (.shl (.v 12) (.mul (.add (.v 14) (.k 1)) (.v 23))))))))
      (t2.setv 5 w) := by
    show evalS G (ansBody v pxS lenE pBE πBE) s = _
    rw [ansBody, evalS_seq, ht1, evalS_seq, ht2, evalS_seq, evalS_set, ew]
  have w2 : Wr ansW s (t2.setv 5 w) :=
    (((qw.mono (by decide)).trans (kw.mono (by decide))).trans (Wr.setv _ (by decide) _))
  have hpxp : ∃ t3 : FS, evalS G (pxPart pxS) (t2.setv 5 w) = t3 ∧ t3.env 23 = s.fl ∧ t3.env 14 = j ∧ t3.env 3 = b ∧ t3.env 11 = A ∧
      t3.env 12 = t2.env 12 ∧ (if t2.env 12 = 0 then 0 else t3.env 5) < 2 ^ s.fl ∧
      ev φ (if t2.env 12 = 0 then 0 else t3.env 5) = ansVal (optOf t1) (2 ^ s.fl) len (ev φ w) pxv pxS.isSome ∧
      Wr ansW s t3 := by
    have base : ∀ X : S, evalS G X (t2.setv 5 w) = t2.setv 5 w → ¬ (t2.env 12 = 1 ∧ pxS.isSome = true) →
        ∃ t3 : FS, evalS G X (t2.setv 5 w) = t3 ∧ t3.env 23 = s.fl ∧ t3.env 14 = j ∧ t3.env 3 = b ∧ t3.env 11 = A ∧
          t3.env 12 = t2.env 12 ∧ (if t2.env 12 = 0 then 0 else t3.env 5) < 2 ^ s.fl ∧
          ev φ (if t2.env 12 = 0 then 0 else t3.env 5) = ansVal (optOf t1) (2 ^ s.fl) len (ev φ w) pxv pxS.isSome ∧
          Wr ansW s t3 := by
      intro X hX hn
      refine ⟨_, hX, by simp [c2.h23, hfl2], by simp [e14], by simp [e3], by simp [e11], by simp, ?_, ?_, w2⟩
      · split_ifs <;> simp [hwl]
      · rcases kindOf_cases (F := F) (optOf t1) (2 ^ s.fl) len with ⟨hk0, hv0⟩ | ⟨j9, ho, hj1, hj2, hk1, hv1⟩ | ⟨hk2, hv2⟩
        · rw [k12, hk0, if_pos rfl, hv0, ev_zero]
        · rw [k12, hk1, if_neg one_ne_zero, hv1]
          have : pxS.isSome = false := by
            by_contra h; exact hn ⟨by rw [k12, hk1], by simpa only [Bool.not_eq_false] using h⟩
          simp [this]
        · rw [k12, hk2, if_neg (by omega), hv2]; simp
    cases pxS with
    | none => exact base _ rfl (by simp)
    | some P =>
      by_cases hk1 : t2.env 12 = 1
      · rcases kindOf_cases (F := F) (optOf t1) (2 ^ s.fl) len with ⟨hk0, -⟩ | ⟨j9, ho, hj1, hj2, -, hv1⟩ | ⟨hk2, -⟩
        · omega
        · have h9 : t1.env 9 = j9 := by
            simp only [optOf] at ho; split_ifs at ho; exact Option.some.inj ho
          have c5 : QC G ((t2.setv 5 w).setv 52 (j9 - 1)) l0 u := (c2.setv 5 _).setv 52 _
          obtain ⟨p1, p2, pw⟩ := hpx P rfl _ c5 (w2.trans (Wr.setv _ (by decide) _)) (by simp; omega)
          generalize hp : evalS G P ((t2.setv 5 w).setv 52 (j9 - 1)) = t5 at p1 p2 pw
          have f5 : t5.env 5 = w := by rw [pw.env 5 (by decide)]; simp
          have ef : evalE G t5 (.fadd (.v 5) (.v 53)) = w ^^^ t5.env 53 := by
            have hfl5 : t5.fl = s.fl := pw.fl.trans hfl2
            show (evalE G t5 (.v 5) ^^^ evalE G t5 (.v 53)) % 2 ^ t5.fl = _
            rw [hfl5, eE_v, eE_v, f5]; exact Nat.mod_eq_of_lt (Nat.xor_lt_two_pow hwl p1)
          refine ⟨t5.setv 5 (w ^^^ t5.env 53), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · rw [pxPart, evalS_ite, eE_eq (show evalE G (t2.setv 5 w) (.v 12) = t2.env 12 by simp [evalE]) (eE_k (by omega)),
              if_pos hk1, if_neg one_ne_zero, evalS_seq, evalS_set, eE_sub (show evalE G (t2.setv 5 w) (.v 9) = j9 by
                simp [evalE, e9, h9]) (eE_k (by omega)), evalS_seq, hp, evalS_set, ef]
          · simp; rw [pw.env 23 (by decide)]; simp [c2.h23, hfl2]
          · simp; rw [pw.env 14 (by decide)]; simp [e14]
          · simp; rw [pw.env 3 (by decide)]; simp [e3]
          · simp; rw [pw.env 11 (by decide)]; simp [e11]
          · simp; rw [pw.env 12 (by decide)]; simp
          · rw [if_neg (by omega)]; simp; exact Nat.xor_lt_two_pow hwl p1
          · rw [if_neg (by omega), hv1]; simp [ev_xor, p2, h9]
          · exact ((w2.trans (Wr.setv _ (by decide) _)).trans (pw.mono (by decide))).trans (Wr.setv _ (by decide) _)
        · omega
      · refine base _ ?_ (fun h => hk1 h.1)
        rw [pxPart, evalS_ite, eE_eq (show evalE G (t2.setv 5 w) (.v 12) = t2.env 12 by simp [evalE]) (eE_k (by omega)),
          if_neg hk1, if_pos rfl, evalS_skip]
  obtain ⟨t3, ht3, t23, t14, t3', t11, t12, ty, tev, tw⟩ := hpxp
  rw [hpre, evalS_seq, ht3, tail t3 t23 t14 t3' t11 t12 ty, q1]
  exact ⟨_, ty, tev, by simp, by simp, ((tw.trans (Wr.setv _ (by decide) _)).trans (Wr.setv _ (by decide) _)).trans
    (Wr.setv _ (by decide) _)⟩

/-- The answer value at effective position `k` (block `b0 + k − 1` of `W`). -/
noncomputable def ansAt {p : ℕ} (φ : AdjoinRoot (GF.toPoly p) →+* F) (v : Bool) (l0 : List ℕ) (BH : List F) (OH : F)
    (d f len W b0 : ℕ) (u : List Bool) (pxv : ℕ → F) (px : Bool) (k : ℕ) : F :=
  ansVal ((outV v (l0.map (ev φ)) 0 BH OH d).Q u (idxO f (innD v BH.length d) k)) (2 ^ f) len
    (ev φ (W / 2 ^ ((b0 + (k - 1)) * f) % 2 ^ f)) pxv px

/-- **The answers of a sub-verifier run** at its effective positions. -/
theorem ansLoop_spec (v : Bool) (pxS : Option S) (lenE pBE πBE qcE : E) (s : FS) (φ : AdjoinRoot (GF.toPoly s.fp) →+* F)
    (u : List Bool) (l0 : List ℕ) (BH : List F) (OH : F) (d len pB πB W b0 : ℕ) (pxv : ℕ → F)
    (c : QC G s l0 u) (h6 : s.env 6 = innD v BH.length d)
    (hqc : evalE G (s.setv 11 0) qcE = qcO v s.fl (innD v BH.length d)) (hqN : qcO v s.fl (innD v BH.length d) ≤ G.N)
    (hdb : (innD v BH.length d + 4) * 2 ^ (8 * s.fl + 20) ≤ G.cap)
    (h16 : s.env 16 = W) (h3 : s.env 3 = b0)
    (hlen : ∀ t, Wr ansW s t → evalE G t lenE = len) (hpB : ∀ t, Wr ansW s t → evalE G t pBE = pB)
    (hπB : ∀ t, Wr ansW s t → evalE G t πBE = πB) (hpb : pB + 2 ^ s.fl ≤ G.cap) (hπb : πB + len ≤ G.cap)
    (hb : (b0 + qcO v s.fl (innD v BH.length d)) * s.fl ≤ G.cap)
    (hAc : 2 ^ ((qcO v s.fl (innD v BH.length d) + 1) * s.fl) ≤ G.cap + 1)
    (hpx : ∀ P, pxS = some P → ∀ t : FS, QC G t l0 u → Wr ansW s t → t.env 52 < 2 ^ s.fl →
      (evalS G P t).env 53 < 2 ^ s.fl ∧ ev φ ((evalS G P t).env 53) = pxv (t.env 52) ∧ Wr pxW t (evalS G P t)) :
    let t := evalS G (ansLoop v pxS lenE pBE πBE qcE) s
    (∃ ansl : List ℕ, t.env 11 = packW s.fl ansl ∧ (∀ a ∈ ansl, a < 2 ^ s.fl) ∧
      ∀ k, 1 ≤ k → k ≤ qcO v s.fl (innD v BH.length d) →
        ev φ (ansl.getD k 0) = ansAt φ v l0 BH OH d s.fl len W b0 u pxv pxS.isSome k) ∧
      t.env 3 = b0 + qcO v s.fl (innD v BH.length d) ∧ t.env 6 = innD v BH.length d ∧ t.fp = s.fp ∧ t.fl = s.fl ∧
      Wr ansW s t := by
  intro t
  set qc := qcO v s.fl (innD v BH.length d) with hqcd
  have hc0 : min 0 G.cap = 0 := Nat.zero_min _
  have hloop := loop_inv (G := G) (i := 14) (n := qcE) (body := ansBody v pxS lenE pBE πBE) (s := s.setv 11 0)
    (fun j t => t.fp = s.fp ∧ t.fl = s.fl ∧ QC G t l0 u ∧ t.env 6 = innD v BH.length d ∧ t.env 16 = W ∧
      t.env 3 = b0 + j ∧ Wr ansW s t ∧
      ∃ l : List ℕ, l.length = j ∧ (∀ a ∈ l, a < 2 ^ s.fl) ∧ t.env 11 = packW s.fl (0 :: l) ∧
        ∀ k < j, ev φ (l.getD k 0) = ansAt φ v l0 BH OH d s.fl len W b0 u pxv pxS.isSome (k + 1))
    ⟨rfl, rfl, c.setv 11 0, by simp [h6], by simp [h16], by simp [h3], Wr.setv s (by decide) _,
      [], rfl, by simp, by simp [packW], by simp⟩
    (by
      intro j hj t ⟨tfp, tfl, ct, t6, t16, t3, tw, l, hl, hlw, t11, hlv⟩
      have hjq : j < qc := by rw [hqc] at hj; exact lt_of_lt_of_le hj (min_le_left _ _)
      obtain ⟨env, out, fl, fp, ip, bad⟩ := t
      obtain rfl : fp = s.fp := tfp
      obtain rfl : fl = s.fl := tfl
      set t0 : FS := ⟨env, out, s.fl, s.fp, ip, bad⟩ with ht0
      have w0 : Wr ansW s (t0.setv 14 j) := tw.trans (Wr.setv _ (by decide) _)
      have hA : packW s.fl (0 :: l) < 2 ^ ((j + 1) * s.fl) := by
        have := packW_lt s.fl (0 :: l) (by
          intro a ha; simp only [List.mem_cons] at ha; rcases ha with rfl | ha
          · positivity
          · exact hlw a ha)
        simpa [hl, mul_comm] using this
      have hAc' : 2 ^ ((j + 2) * s.fl) ≤ G.cap + 1 :=
        le_trans (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ (by omega))) hAc
      obtain ⟨y, hy, hyv, e11, e3, ew⟩ := ansBody_spec G v pxS lenE pBE πBE (t0.setv 14 j) φ u l0 BH OH d j len pB πB W
        (b0 + j) (packW s.fl (0 :: l)) pxv (ct.setv 14 j) (by simp) (by simp [t6]) (show j + 1 ≤ qc by omega) hdb
        (by simp [t16])
        (by simp [t3]) (by simp [t11]) (fun t' w' => hlen t' (w0.trans (w'.mono (by decide))))
        (fun t' w' => hpB t' (w0.trans (w'.mono (by decide)))) (fun t' w' => hπB t' (w0.trans (w'.mono (by decide))))
        hpb hπb (le_trans (Nat.mul_le_mul_right _ (by omega)) hb) hA hAc'
        (fun P hP t' c' w' h' => hpx P hP t' c' (w0.trans w') h')
      generalize ht1 : evalS G (ansBody v pxS lenE pBE πBE) (t0.setv 14 j) = t1 at hy hyv e11 e3 ew
      refine ⟨ew.fp, ew.fl, (ct.setv 14 j).wr ew (by decide) ew.fp, by rw [ew.env 6 (by decide)]; simp [t6],
        by rw [ew.env 16 (by decide)]; simp [t16], by rw [e3]; omega, w0.trans (ew.mono (by decide)),
        l ++ [y], by simp [hl], ?_, ?_, ?_⟩
      · intro a ha; simp only [List.mem_append, List.mem_singleton] at ha; rcases ha with ha | rfl
        · exact hlw a ha
        · exact hy
      · rw [e11, show (0 :: (l ++ [y])) = (0 :: l) ++ [y] from rfl, packW_append]
        simp [packW, hl, mul_comm]
        exact Or.inl (mul_comm _ _)
      · intro k hk
        rcases Nat.lt_or_ge k j with h | h
        · rw [List.getD_append _ _ _ _ (by omega)]; exact hlv k h
        · obtain rfl : k = j := by omega
          rw [List.getD_append_right _ _ _ _ (by omega), hl, Nat.sub_self]
          simp only [List.getD_cons_zero]
          exact hyv.trans (by unfold ansAt; simp only [FS.setv_fl, Nat.add_sub_cancel]; rfl))
  have hmq : min (evalE G (s.setv 11 0) qcE) G.N = qc := by rw [hqc]; exact min_eq_left hqN
  rw [hmq] at hloop
  have ht : t = evalS G (.loop 14 qcE (ansBody v pxS lenE pBE πBE)) (s.setv 11 0) := by
    show evalS G (ansLoop v pxS lenE pBE πBE qcE) s = _
    rw [ansLoop, evalS_seq, evalS_set, show evalE G s (.k 0) = 0 from hc0]
  rw [ht]
  obtain ⟨tfp, tfl, -, t6, -, t3, tw, l, hl, hlw, t11, hlv⟩ := hloop
  refine ⟨⟨0 :: l, t11, ?_, ?_⟩, t3, t6, tfp, tfl, tw⟩
  · intro a ha; simp only [List.mem_cons] at ha; rcases ha with rfl | ha
    · positivity
    · exact hlw a ha
  · intro k hk1 hk2
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    simp only [List.getD_cons_succ]
    exact hlv k' (by omega)

end NearCubicGates.Adapters.ShortPCP.Machines.FL
