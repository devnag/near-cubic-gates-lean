import Proof.Gates.Dispatch.PrintP

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

def oODD : Fin VV := ⟨56, by decide⟩
def oJ : Fin VV := ⟨57, by decide⟩
def oI : Fin VV := ⟨58, by decide⟩
def oX : Fin VV := ⟨59, by decide⟩
def oC : Fin VV := ⟨198, by decide⟩
def oR : Fin VV := ⟨199, by decide⟩

theorem drop_app (l1 l2 : List Bool) (k : ℕ) : (l1 ++ l2).drop (l1.length + k) = l2.drop k := by
  rw [← List.drop_drop, List.drop_left]

theorem drop_parity (c : Call) : (callWord c).drop (pos3 c + (natWord c.parity.length).length) =
    c.parity.flatMap natWord ++ ratWord c.radius := by
  rw [callWord_eq]
  have e : pos3 c + (natWord c.parity.length).length = (natWord c.n).length + ((natWord (kindTag c.kind)).length +
      ((circuitWord c.first).length + ((circuitWord c.second).length + (natWord c.parity.length).length))) := by
    simp only [pos3, pos2, pos1]; ring
  rw [e, List.append_assoc, drop_app, drop_app, drop_app, drop_app]
  simp only [listWord, List.append_assoc]
  rw [← add_zero (natWord c.parity.length).length, drop_app, List.drop_zero]

theorem len_le_flatMap {α : Type} (g : α → List Bool) (xs : List α) (x : α) (hx : x ∈ xs) :
    (g x).length ≤ (xs.flatMap g).length := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
    rw [List.flatMap_cons, List.length_append]
    rcases List.mem_cons.1 hx with h | h
    · subst h; omega
    · have := ih h; omega

theorem oddIndices_nil_iff (c : Call) (hall : ∀ i ∈ c.parity, i < c.n) :
    oddIndices c = [] ↔ ¬ ∃ x ∈ c.parity, c.parity.count x % 2 = 1 := by
  unfold oddIndices
  rw [List.filter_eq_nil_iff]
  constructor
  · rintro h ⟨x, hx, hodd⟩
    exact h x (List.mem_range.2 (hall x hx)) (by simpa using hodd)
  · intro h i _ hi
    have hodd : c.parity.count i % 2 = 1 := by simpa using hi
    have hpos : 0 < c.parity.count i := by omega
    exact h ⟨i, List.count_pos_iff.1 hpos, hodd⟩

/-! ## Seeking the parity list -/

def seekP : St VV := .seq (.op .rstC) (.seq (.op (.zero vPOS)) (.loop (.lt vPOS vPP) rdc))

theorem seekP_spec (a : DS VV) (hc : Cst a) (P : ℕ) (hP : a.env vPP = P) (hPL : P ≤ C.cw.length)
    (hW : C.cw.length + 2 < 2 ^ C.Wd) :
    Hs C seekP a (P * 5 + 6) (fun b => b.cp = P ∧ Cst b ∧ b.wq = a.wq ∧ b.out = a.out ∧ Fr a b [t0, vPOS, vJ]) := by
  refine Hx.hs (Hs.then (hs_rstC (C := C) a) (fun b1 e1 k1 hk1 => ?_))
  subst e1
  refine Hs.then (hs_zero C vPOS _) (fun b2 e2 k2 hk2 => ?_)
  subst e2
  let I : ℕ → DS VV → Prop := fun k b => b.cp = k ∧ b.env vPOS = k ∧ b.env vPP = P ∧ b.wq = a.wq ∧ b.out = a.out ∧
    b.env vZ = 0 ∧ b.env v1 = 1 ∧ b.env v2 = 2 ∧ Fr a b [t0, vPOS, vJ]
  have hI : I 0 ({ a with cp := 0 }.set vPOS 0) := ⟨rfl, by rw [DS.set_env_self], by
      rw [DS.set_env_ne _ _ (by decide)]; exact hP, rfl, rfl, by rw [DS.set_env_ne _ _ (by decide)]; exact hc.z,
    by rw [DS.set_env_ne _ _ (by decide)]; exact hc.one, by rw [DS.set_env_ne _ _ (by decide)]; exact hc.two,
    fun y hy => by rw [DS.set_env_ne _ _ (fun h => hy (by simp [h]))]⟩
  have l := Hs.loopN (C := C) (c := .lt vPOS vPP) (s := rdc) (show vPOS ≠ vPP by decide) I P 3
    (fun k hk d ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9⟩ => ⟨by simp [Cnd.eval, d2, d3, hk], by
      refine Hs.mono (rdc_spec d (by rw [d2, d1]) (by omega) (by omega)) le_rfl ?_
      rintro e ⟨e1, e2, e3, e4, e5, e6⟩
      exact ⟨by rw [e3, d1], by rw [e2, d1], by rw [e6 vPP (by decide)]; exact d3, by rw [e4, d4], by rw [e5, d5],
        by rw [e6 vZ (by decide)]; exact d6, by rw [e6 v1 (by decide)]; exact d7, by rw [e6 v2 (by decide)]; exact d8,
        Fr.trans d9 (e6.weaken (by decide))⟩⟩)
    (fun d hd => by simp [Cnd.eval, hd.2.1, hd.2.2.1]) _ hI
  refine Hs.last l (fun g ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9⟩ k3 hk3 => ⟨⟨g1, ⟨g6, g7, g8, by rw [g2, g1]⟩, g4, g5, g9⟩,
    by omega⟩)

/-! ## Skipping and counting entries -/

def skipW : St VV := .seq (.op (.zero oI)) (.loop (.lt oI oJ) (.seq readNat (.op (.inc oI))))

def zwT : List (Fin VV) := [oI, oC, t0, t1, t2, t3, t4, vJ, vPOS]

theorem take_flatMap_drop {α : Type} (xs : List α) (g : α → List Bool) (j : ℕ) (R : List Bool) :
    xs.flatMap g ++ R = (xs.take j).flatMap g ++ ((xs.drop j).flatMap g ++ R) := by
  conv_lhs => rw [← List.take_append_drop j xs]
  rw [List.flatMap_append, List.append_assoc]

theorem skipW_spec (c : Call) (a : DS VV) (hc : Cst a) (j : ℕ) (R : List Bool) (hj : j ≤ c.parity.length)
    (hJ : a.env oJ = j) (hcw : C.cw.drop a.cp = c.parity.flatMap natWord ++ R)
    (hWb : ∀ v ∈ c.parity, natBitLength v + 2 ≤ C.Wd) (hL : C.cw.length + 2 < 2 ^ C.Wd)
    (hlen : c.parity.length < 2 ^ C.Wd) :
    Hs C skipW a (j * (30 * C.Wd + 64) + 4) (fun b => C.cw.drop b.cp = (c.parity.drop j).flatMap natWord ++ R ∧
      Cst b ∧ b.wq = a.wq ∧ b.out = a.out ∧ Fr a b zwT) := by
  refine Hx.hs (Hs.then (hs_zero C oI a) (fun b1 e1 k1 hk1 => ?_))
  subst e1
  have htake : (c.parity.take j).length = j := by simp; omega
  have hW1 : 1 ≤ C.Wd := by
    by_contra h
    have : C.Wd = 0 := by omega
    rw [this] at hL; simp at hL
  let P : ℕ → DS VV → Prop := fun _ b => Cst b ∧ b.wq = a.wq ∧ b.out = a.out ∧ Fr a b zwT
  have w := walk (C := C) (c.parity.take j) natWord oI oJ (by decide) readNat P (30 * C.Wd + 60)
    ((c.parity.drop j).flatMap natWord ++ R)
    (fun k b v ⟨h1, h2, h3, h4⟩ => ⟨Cst.set h1 _ _ (by decide), h2, h3, Fr.trans h4 (Fr.set _ _ (by decide))⟩)
    (fun k hk d ⟨d1, d2, d3, d4⟩ dI dN dcw => by
      have hmem : (c.parity.take j)[k] ∈ c.parity := List.mem_of_mem_take (List.getElem_mem hk)
      have hb := hWb _ hmem
      refine Hs.mono (readNat_spec d d1 _ _ dcw (by omega) hL) (by nlinarith) ?_
      rintro e ⟨e1, e2, e3, e4, e5, e6, e7⟩
      exact ⟨⟨e6, by rw [e4, d2], by rw [e5, d3], Fr.trans d4 (e7.weaken (by decide))⟩,
        by rw [e7 oI (by decide), dI], by rw [e7 oJ (by decide), dN], e3⟩)
    (by rw [htake]; omega)
  refine Hs.last (w (a.set oI 0) ⟨Cst.set hc _ _ (by decide), rfl, rfl, Fr.set _ _ (by decide)⟩ (by rw [DS.set_env_self])
    (by rw [DS.set_env_ne _ _ (by decide), hJ, htake]) (by
      show C.cw.drop a.cp = _
      rw [hcw, take_flatMap_drop c.parity natWord j R]))
    (fun g ⟨⟨g1, g2, g3, g4⟩, g5, g6, g7⟩ k2 hk2 => ⟨⟨?_, g1, g2, g3, g4⟩, ?_⟩)
  · show C.cw.drop g.cp = _
    rw [g7]
    show C.cw.drop (a.cp + _) = _
    rw [← List.drop_drop, hcw, take_flatMap_drop c.parity natWord j R, List.drop_left]
  · rw [htake] at hk2
    have : j * (30 * C.Wd + 60 + 2 + 2) = j * (30 * C.Wd + 64) := by ring
    omega

def cntW : St VV := .seq (.op (.zero oI)) (.seq (.op (.zero oC))
  (.loop (.lt oI vPL) (.seq (.seq readNat (.ite (.eq t3 oX) (.op (.inc oC)) skipS)) (.op (.inc oI)))))

theorem count_take_succ (xs : List ℕ) (x k : ℕ) (hk : k < xs.length) :
    (xs.take (k + 1)).count x = (xs.take k).count x + (if xs[k] = x then 1 else 0) := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, List.count_append]
  by_cases h : xs[k] = x
  · rw [if_pos h, h]; simp
  · rw [if_neg h]
    have : List.count x [xs[k]] = 0 := List.count_eq_zero_of_not_mem (by simp; exact Ne.symm h)
    omega

theorem cntW_spec (c : Call) (a : DS VV) (hc : Cst a) (x : ℕ) (hX : a.env oX = x) (R : List Bool)
    (hL' : a.env vPL = c.parity.length) (hcw : C.cw.drop a.cp = c.parity.flatMap natWord ++ R)
    (hWb : ∀ v ∈ c.parity, natBitLength v + 2 ≤ C.Wd) (hL : C.cw.length + 2 < 2 ^ C.Wd)
    (hlen : c.parity.length + 1 < 2 ^ C.Wd) :
    Hs C cntW a (c.parity.length * (30 * C.Wd + 70) + 6) (fun b => b.env oC = c.parity.count x ∧
      Cst b ∧ b.wq = a.wq ∧ b.out = a.out ∧ Fr a b zwT) := by
  refine Hx.hs (Hs.then (hs_zero C oI a) (fun b1 e1 k1 hk1 => ?_))
  subst e1
  refine Hs.then (hs_zero C oC _) (fun b2 e2 k2 hk2 => ?_)
  subst e2
  have hW1 : 1 ≤ C.Wd := by
    by_contra h
    have : C.Wd = 0 := by omega
    rw [this] at hL; simp at hL
  let P : ℕ → DS VV → Prop := fun k b => b.env oC = (c.parity.take k).count x ∧ b.env oX = x ∧ Cst b ∧
    b.wq = a.wq ∧ b.out = a.out ∧ Fr a b zwT
  have w := walk (C := C) c.parity natWord oI vPL (by decide) (.seq readNat (.ite (.eq t3 oX) (.op (.inc oC)) skipS))
    P (30 * C.Wd + 64) R
    (fun k b v ⟨h1, h2, h3, h4, h5, h6⟩ => ⟨by rw [DS.set_env_ne _ _ (by decide), h1],
      by rw [DS.set_env_ne _ _ (by decide), h2], Cst.set h3 _ _ (by decide), h4, h5,
      Fr.trans h6 (Fr.set _ _ (by decide))⟩)
    (fun k hk d ⟨d1, d2, d3, d4, d5, d6⟩ dI dN dcw => by
      have hb := hWb _ (List.getElem_mem hk)
      refine Hs.seq (t1 := 30 * natBitLength c.parity[k] + 30) (t2 := 3) (readNat_spec d d3 _ _ dcw (by omega) hL)
        (fun e ⟨e1, e2, e3, e4, e5, e6, e7⟩ => ?_) |> fun h => Hs.mono h (by nlinarith) (fun g hg => hg)
      have eX : e.env oX = x := by rw [e7 oX (by decide), d2]
      have eC : e.env oC = (c.parity.take k).count x := by rw [e7 oC (by decide), d1]
      have hcnt : (c.parity.take k).count x + 1 < 2 ^ C.Wd := by
        have : (c.parity.take k).count x ≤ k := le_trans (List.count_le_length) (by simp)
        omega
      refine Hs.ite (show t3 ≠ oX by decide) (fun he => ?_) (fun he => ?_)
      · have heq : c.parity[k] = x := by simpa [Cnd.eval, e1, eX] using he
        refine Hs.mono (hs_inc C oC e (by rw [eC]; exact hcnt)) (by omega) ?_
        rintro g rfl
        refine ⟨⟨by rw [DS.set_env_self, eC, count_take_succ _ _ _ hk, if_pos heq],
          by rw [DS.set_env_ne _ _ (by decide), eX], Cst.set e6 _ _ (by decide), by show e.wq = a.wq; rw [e4, d4],
          by show e.out = a.out; rw [e5, d5],
          Fr.trans d6 (Fr.trans (e7.weaken (by decide)) (Fr.set _ _ (by decide)))⟩,
          by rw [DS.set_env_ne _ _ (by decide), e7 oI (by decide), dI],
          by rw [DS.set_env_ne _ _ (by decide), e7 vPL (by decide), dN], by show e.cp = _; rw [e3]⟩
      · have hne : c.parity[k] ≠ x := by simpa [Cnd.eval, e1, eX] using he
        refine Hs.mono (skip_spec e) (by omega) ?_
        rintro g rfl
        refine ⟨⟨by rw [DS.set_env_ne _ _ (by decide), eC, count_take_succ _ _ _ hk, if_neg hne, Nat.add_zero],
          by rw [DS.set_env_ne _ _ (by decide), eX], Cst.set e6 _ _ (by decide), by show e.wq = a.wq; rw [e4, d4],
          by show e.out = a.out; rw [e5, d5],
          Fr.trans d6 (Fr.trans (e7.weaken (by decide)) (Fr.set _ _ (by decide)))⟩,
          by rw [DS.set_env_ne _ _ (by decide), e7 oI (by decide), dI],
          by rw [DS.set_env_ne _ _ (by decide), e7 vPL (by decide), dN], by show e.cp = _; rw [e3]⟩)
    (by omega)
  refine Hs.last (w _ ⟨by rw [DS.set_env_self]; simp, by rw [DS.set_env_ne _ _ (by decide),
      DS.set_env_ne _ _ (by decide), hX], Cst.set (Cst.set hc _ _ (by decide)) _ _ (by decide), rfl, rfl,
      Fr.trans (Fr.set _ _ (by decide)) (Fr.set _ _ (by decide))⟩ (by rw [DS.set_env_ne _ _ (by decide),
      DS.set_env_self]) (by rw [DS.set_env_ne _ _ (by decide), DS.set_env_ne _ _ (by decide), hL'])
      (by show C.cw.drop a.cp = _; exact hcw))
    (fun g ⟨⟨g1, _, g2, g3, g4, g5⟩, _, _, _⟩ k3 hk3 => ⟨⟨by rw [g1, List.take_length], g2, g3, g4, g5⟩, ?_⟩)
  have : c.parity.length * (30 * C.Wd + 64 + 2 + 2) ≤ c.parity.length * (30 * C.Wd + 70) :=
    Nat.mul_le_mul_left _ (by omega)
  omega

/-! ## The odd-count flag -/

open AE in
def oddBody : St VV :=
  .seq seekP (.seq skipW (.seq readNat (.seq (.op (.copy oX t3)) (.seq seekP (.seq cntW
    (.seq (assign oR (mod (var oC) (lit 2))) (.seq (.ite (.eq oR v1) (.op (.copy oODD v1)) skipS) (.op (.inc oJ)))))))))

def oddP : St VV := .seq (.op (.zero oODD)) (.seq (.op (.zero oJ)) (.loop (.lt oJ vPL) oddBody))

def oddT : List (Fin VV) := [oODD, oJ, oI, oX, oC, oR, t0, t1, t2, t3, t4, vJ, vPOS]

/-- Some entry of the first `j` has an odd count. -/
def OddSome (c : Call) (j : ℕ) : Prop := ∃ x ∈ c.parity.take j, c.parity.count x % 2 = 1

instance (c : Call) (j : ℕ) : Decidable (OddSome c j) :=
  decidable_of_iff ((c.parity.take j).any (fun x => c.parity.count x % 2 == 1) = true) (by
    unfold OddSome; simp)

def OddI (c : Call) (a0 : DS VV) (P0 : ℕ) (j : ℕ) (b : DS VV) : Prop :=
  b.env oJ = j ∧ b.env oODD = bnat (OddSome c j) ∧
    b.env vPL = c.parity.length ∧ b.env vPP = P0 ∧ Cst b ∧ b.wq = a0.wq ∧ b.out = a0.out ∧ FrS a0 b oddT

def oddCost (L len W : ℕ) : ℕ := 10 * L + 2 * len * (30 * W + 70) + 30 * W + 200

theorem oddBody_spec (c : Call) (a0 : DS VV) (P0 : ℕ) (R : List Bool) (hP0 : P0 ≤ C.cw.length)
    (hcw : C.cw.drop P0 = c.parity.flatMap natWord ++ R) (hWb : ∀ v ∈ c.parity, natBitLength v + 2 ≤ C.Wd)
    (hL : C.cw.length + 2 < 2 ^ C.Wd) (hlen : c.parity.length + 1 < 2 ^ C.Wd) (hW4 : 4 < 2 ^ C.Wd) (j : ℕ)
    (hj : j < c.parity.length)
    (b : DS VV) (hb : OddI c a0 P0 j b) :
    Hs C oddBody b (oddCost C.cw.length c.parity.length C.Wd) (OddI c a0 P0 (j + 1)) := by
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩ := hb
  have hW1 : 1 ≤ C.Wd := by
    by_contra h
    have : C.Wd = 0 := by omega
    rw [this] at hL; simp at hL
  refine Hx.hs (Hs.then (seekP_spec b i5 P0 i4 hP0 hL) (fun b1 ⟨p1, p2, p3, p4, p5⟩ k1 hk1 => ?_))
  refine Hs.then (skipW_spec c b1 p2 j R hj.le (by rw [p5 oJ (by decide), i1]) (by rw [p1]; exact hcw) hWb hL
    (by omega)) (fun b2 ⟨q1, q2, q3, q4, q5⟩ k2 hk2 => ?_)
  rw [flatMap_drop_get c.parity natWord j hj, List.append_assoc] at q1
  have hb := hWb _ (List.getElem_mem hj)
  refine Hs.then (readNat_spec b2 q2 _ _ q1 (by omega) hL) (fun b3 ⟨r1, r2, r3, r4, r5, r6, r7⟩ k3 hk3 => ?_)
  refine Hs.then (hs_copy C oX t3 b3 (by decide)) (fun b4 e4 k4 hk4 => ?_)
  subst e4
  have c4 : Cst (b3.set oX (b3.env t3)) := Cst.set r6 _ _ (by decide)
  have b4PP : (b3.set oX (b3.env t3)).env vPP = P0 := by
    rw [DS.set_env_ne _ _ (by decide), r7 vPP (by decide), q5 vPP (by decide), p5 vPP (by decide), i4]
  refine Hs.then (seekP_spec _ c4 P0 b4PP hP0 hL) (fun b5 ⟨s1, s2, s3, s4, s5⟩ k5 hk5 => ?_)
  have b5X : b5.env oX = c.parity[j] := by rw [s5 oX (by decide), DS.set_env_self, r1]
  have b5L : b5.env vPL = c.parity.length := by
    rw [s5 vPL (by decide), DS.set_env_ne _ _ (by decide), r7 vPL (by decide), q5 vPL (by decide),
      p5 vPL (by decide), i3]
  refine Hs.then (cntW_spec c b5 s2 _ b5X R b5L (by rw [s1]; exact hcw) hWb hL hlen)
    (fun b6 ⟨u1, u2, u3, u4, u5⟩ k6 hk6 => ?_)
  have hcnt : c.parity.count c.parity[j] ≤ c.parity.length := List.count_le_length
  refine Hs.then (assign_spec oR (by decide) (by decide) (.mod (.var oC) (.lit 2)) b6 (by aevar) (by aevar) u2
    (by aeok [u1])) (fun b7 ⟨v1', v2', v3', v4', v5', v6'⟩ k7 hk7 => ?_)
  simp only [AE.eval, u1] at v1'
  have b7O : b7.env oODD = bnat (OddSome c j) := by
    rw [v2' oODD (by decide) (by decide) (by decide), u5 oODD (by decide), s5 oODD (by decide),
      DS.set_env_ne _ _ (by decide), r7 oODD (by decide), q5 oODD (by decide), p5 oODD (by decide), i2]
  have htake : OddSome c (j + 1) ↔ OddSome c j ∨ c.parity.count c.parity[j] % 2 = 1 := by
    unfold OddSome
    rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some]
    simp only [List.mem_append, List.mem_singleton]
    constructor
    · rintro ⟨x, hx | hx, hq⟩
      · exact Or.inl ⟨x, hx, hq⟩
      · subst hx; exact Or.inr hq
    · rintro (⟨x, hx, hq⟩ | hq)
      · exact ⟨x, Or.inl hx, hq⟩
      · exact ⟨_, Or.inr rfl, hq⟩
  have step : Hs C (.ite (.eq oR v1) (.op (.copy oODD v1)) skipS) b7 2 (fun g =>
      g.env oODD = bnat (OddSome c (j + 1)) ∧ g.cp = b7.cp ∧ g.wq = b7.wq ∧
      g.out = b7.out ∧ Cst g ∧ Fr b7 g [oODD, vJ]) := by
    refine Hs.ite (show oR ≠ v1 by decide) (fun he => ?_) (fun he => ?_)
    · have hodd : c.parity.count c.parity[j] % 2 = 1 := by simpa [Cnd.eval, v1', v6'.one] using he
      refine Hs.mono (hs_copy C oODD v1 b7 (by decide)) (by omega) ?_
      rintro g rfl
      exact ⟨by rw [DS.set_env_self, v6'.one]; exact (bnat_one_of (htake.2 (Or.inr hodd))).symm, rfl, rfl, rfl,
        Cst.set v6' _ _ (by decide), Fr.set _ _ (by decide)⟩
    · have hev : ¬ c.parity.count c.parity[j] % 2 = 1 := by simpa [Cnd.eval, v1', v6'.one] using he
      refine Hs.mono (skip_spec b7) (by omega) ?_
      rintro g rfl
      refine ⟨?_, rfl, rfl, rfl, Cst.set v6' _ _ (by decide), Fr.set _ _ (by decide)⟩
      rw [DS.set_env_ne _ _ (by decide), b7O]
      exact bnat_congr (by rw [htake]; tauto)
  refine Hs.then step (fun b8 ⟨w1, w2, w3, w4, w5, w6⟩ k8 hk8 => ?_)
  have b8J : b8.env oJ = j := by
    rw [w6 oJ (by decide), v2' oJ (by decide) (by decide) (by decide), u5 oJ (by decide), s5 oJ (by decide),
      DS.set_env_ne _ _ (by decide), r7 oJ (by decide), q5 oJ (by decide), p5 oJ (by decide), i1]
  refine Hs.last (hs_inc C oJ b8 (by rw [b8J]; omega)) (fun g e9 k9 hk9 => ?_)
  subst e9
  refine ⟨⟨by rw [DS.set_env_self, b8J], by rw [DS.set_env_ne _ _ (by decide), w1], ?_, ?_, Cst.set w5 _ _ (by decide),
    by show b8.wq = a0.wq; rw [w3, v4', u3, s3]; show b3.wq = _; rw [r4, q3, p3, i6],
    by show b8.out = a0.out; rw [w4, v5', u4, s4]; show b3.out = _; rw [r5, q4, p4, i7],
    ?_⟩, ?_⟩
  · rw [DS.set_env_ne _ _ (by decide), w6 vPL (by decide), v2' vPL (by decide) (by decide) (by decide),
      u5 vPL (by decide)]; exact b5L
  · rw [DS.set_env_ne _ _ (by decide), w6 vPP (by decide), v2' vPP (by decide) (by decide) (by decide),
      u5 vPP (by decide), s5 vPP (by decide)]; exact b4PP
  · exact FrS.trans i8 (FrS.trans (p5.toS.weaken (by decide)) (FrS.trans (q5.toS.weaken (by decide))
      (FrS.trans (r7.toS.weaken (by decide)) (FrS.trans (Fr.toS (Fr.set _ _ (by decide)))
      (FrS.trans (s5.toS.weaken (by decide)) (FrS.trans (u5.toS.weaken (by decide))
      (FrS.trans (v2'.toS _ (by decide) (by decide)) (FrS.trans (w6.toS.weaken (by decide))
      (Fr.toS (Fr.set _ _ (by decide)))))))))))
  · simp only [AE.cost] at hk7
    have e1 : j * (30 * C.Wd + 64) ≤ c.parity.length * (30 * C.Wd + 70) := Nat.mul_le_mul (by omega) (by omega)
    have e2 : natBitLength c.parity[j] ≤ C.Wd := by omega
    unfold oddCost
    have e3 : 2 * c.parity.length * (30 * C.Wd + 70) = 2 * (c.parity.length * (30 * C.Wd + 70)) := by ring
    omega

def oddCostT (L len W : ℕ) : ℕ := len * (oddCost L len W + 2) + 6

theorem oddP_spec (c : Call) (a : DS VV) (hc : Cst a) (hpo : ParseOut c a) (hcw : C.cw = callWord c)
    (hW : 2 * C.cw.length + 8 ≤ C.Wd) (hL : C.cw.length + 2 < 2 ^ C.Wd) :
    Hs C oddP a (oddCostT C.cw.length c.parity.length C.Wd) (fun b =>
      b.env oODD = bnat (∃ x ∈ c.parity, c.parity.count x % 2 = 1) ∧ Cst b ∧ b.wq = a.wq ∧ b.out = a.out ∧
      FrS a b oddT) := by
  set P0 := pos3 c + (natWord c.parity.length).length with hP0
  have hdrop : C.cw.drop P0 = c.parity.flatMap natWord ++ ratWord c.radius := by rw [hcw]; exact drop_parity c
  have hrat : 0 < (ratWord c.radius).length := by simp [ratWord, Interfaces.intWord, natWord_length]
  have hlenD : (C.cw.drop P0).length = C.cw.length - P0 := List.length_drop
  have hP0L : P0 ≤ C.cw.length := by
    rw [hdrop, List.length_append] at hlenD; omega
  have hflat : (c.parity.flatMap natWord).length ≤ C.cw.length := by
    rw [hdrop, List.length_append] at hlenD; omega
  have hWb : ∀ v ∈ c.parity, natBitLength v + 2 ≤ C.Wd := fun v hv => by
    have := len_le_flatMap natWord c.parity v hv
    have := natBitLength_le_len v
    omega
  have hlenL : c.parity.length ≤ C.cw.length := by
    have : c.parity.length ≤ (c.parity.flatMap natWord).length := by
      clear hWb
      induction c.parity with
      | nil => simp
      | cons y ys ih => simp only [List.length_cons, List.flatMap_cons, List.length_append]; rw [natWord_length]; omega
    omega
  have hW4 : 4 < 2 ^ C.Wd := lt_of_lt_of_le (by norm_num : 4 < 2 ^ 3) (Nat.pow_le_pow_right (by norm_num) (by omega))
  refine Hx.hs (Hs.then (hs_zero C oODD a) (fun b1 e1 k1 hk1 => ?_))
  subst e1
  refine Hs.then (hs_zero C oJ _) (fun b2 e2 k2 hk2 => ?_)
  subst e2
  have hI : OddI c a P0 0 ((a.set oODD 0).set oJ 0) := ⟨by rw [DS.set_env_self], by
      rw [DS.set_env_ne _ _ (by decide), DS.set_env_self]; symm; apply bnat_zero_of_not; simp [OddSome],
    by rw [DS.set_env_ne _ _ (by decide), DS.set_env_ne _ _ (by decide)]; exact hpo.pl,
    by rw [DS.set_env_ne _ _ (by decide), DS.set_env_ne _ _ (by decide)]; exact hpo.pp,
    Cst.set (Cst.set hc _ _ (by decide)) _ _ (by decide), rfl, rfl,
    FrS.trans (Fr.toS (Fr.set _ _ (by decide))) (Fr.toS (Fr.set _ _ (by decide)))⟩
  have l := Hs.loopN (C := C) (c := .lt oJ vPL) (s := oddBody) (show oJ ≠ vPL by decide) (OddI c a P0)
    c.parity.length (oddCost C.cw.length c.parity.length C.Wd)
    (fun j hj d hd => ⟨by simp [Cnd.eval, hd.1, hd.2.2.1, hj],
      oddBody_spec c a P0 _ hP0L hdrop hWb hL (by omega) hW4 j hj d hd⟩)
    (fun d hd => by simp [Cnd.eval, hd.1, hd.2.2.1]) _ hI
  refine Hs.last l (fun g ⟨g1, g2, g3, g4, g5, g6, g7, g8⟩ k3 hk3 => ⟨⟨?_, g5, g6, g7, g8⟩, ?_⟩)
  · rw [g2]; exact bnat_congr (by unfold OddSome; rw [List.take_length])
  · unfold oddCostT; omega

/-! ## The `W = 0` output and the default -/

def zw (v : ℚ) : List Bool := natWord 0 ++ outputWord (v, 0)
def defW : List Bool := natWord 0 ++ outputWord defaultValue

open AE in
def zeroOut : St VV :=
  .seq oddP (.seq (.ite (.eq vTAG v1) (assign oC (mod (add (var vTB1) (var vTB2)) (lit 2)))
      (.ite (.eq oODD v1) (assign oC (lit 2)) (assign oC (var vTB1))))
    (.ite (.eq oC vZ) (emitL (zw 0)) (.ite (.eq oC v1) (emitL (zw 1)) (emitL (zw (1 / 2))))))

def defOut : St VV := emitL defW

/-- The first coordinate of `zeroWeightValue` (with the odd-index test in list form). -/
def zval (c : Call) : ℚ :=
  match c.kind with
  | .single => if c.first.table.getD 0 false then 1 else 0
  | .pair => if xor (c.first.table.getD 0 false) (c.second.table.getD 0 false) then 1 else 0
  | .parity => if (∃ x ∈ c.parity, c.parity.count x % 2 = 1) then 1 / 2 else
      (if c.first.table.getD 0 false then 1 else 0)

theorem zeroWeightValue_eq (c : Call) (hW : c.W = 0) (hall : ∀ i ∈ c.parity, i < c.n) :
    zeroWeightValue c = (zval c, 0) := by
  have h1 : c.first.topWeight = 0 := by unfold Call.W at hW; omega
  have h2 : c.second.topWeight = 0 := by unfold Call.W at hW; omega
  have e1 : topLookup c.first 0 = c.first.table.getD 0 false := by unfold topLookup; rw [h1]; rfl
  have e2 : topLookup c.second 0 = c.second.table.getD 0 false := by unfold topLookup; rw [h2]; rfl
  unfold zeroWeightValue zval
  rw [e1, e2]
  cases hk : c.kind with
  | single => rfl
  | pair => rfl
  | parity =>
    simp only []
    by_cases ho : ∃ x ∈ c.parity, c.parity.count x % 2 = 1
    · rw [if_neg (fun h => (oddIndices_nil_iff c hall).1 h ho), if_pos ho]
    · rw [if_pos ((oddIndices_nil_iff c hall).2 ho), if_neg ho]

def zoT : List (Fin VV) := oddT ++ [oC, vJ]

def zwLen : ℕ := (zw 0).length + (zw 1).length + (zw (1 / 2)).length

theorem zeroOut_spec (B1 B2 : ℕ) (c : Call) (hadm : c.Admitted B1 B2) (hW0 : c.W = 0) (a : DS VV) (hc : Cst a)
    (hpo : ParseOut c a) (hcw : C.cw = callWord c) (hW : 2 * C.cw.length + 8 ≤ C.Wd)
    (hL : C.cw.length + 2 < 2 ^ C.Wd) :
    Hs C zeroOut a (oddCostT C.cw.length c.parity.length C.Wd + 2 * zwLen + 50) (fun b =>
      b.out = a.out ++ (natWord 0 ++ outputWord (zeroWeightValue c)) ∧ Cst b ∧ b.wq = a.wq ∧ FrS a b zoT) := by
  obtain ⟨h4, -, -, -, hpar, hall, -⟩ := hadm
  have h4W : 4 < 2 ^ C.Wd := lt_of_lt_of_le (by norm_num : 4 < 2 ^ 3) (Nat.pow_le_pow_right (by norm_num) (by omega))
  rw [zeroWeightValue_eq c hW0 hall]
  refine Hx.hs (Hs.then (oddP_spec c a hc hpo hcw hW hL) (fun b1 ⟨p1, p2, p3, p4, p5⟩ k1 hk1 => ?_))
  have b1T : b1.env vTAG = kindTag c.kind := by simp (disch := decide) only [p5.ev]; exact hpo.tag
  have b1T1 : b1.env vTB1 = (c.first.table.getD 0 false).toNat := by
    simp (disch := decide) only [p5.ev]; exact hpo.c1.tb
  have b1T2 : b1.env vTB2 = (c.second.table.getD 0 false).toNat := by
    simp (disch := decide) only [p5.ev]; exact hpo.c2.tb
  have hb1 : (c.first.table.getD 0 false).toNat ≤ 1 := Bool.toNat_le _
  have hb2 : (c.second.table.getD 0 false).toNat ≤ 1 := Bool.toNat_le _
  -- the selector
  set sel : ℕ := if c.kind = .pair then ((c.first.table.getD 0 false).toNat + (c.second.table.getD 0 false).toNat) % 2
    else if (∃ x ∈ c.parity, c.parity.count x % 2 = 1) then 2 else (c.first.table.getD 0 false).toNat with hsel
  have step : Hs C (.ite (.eq vTAG v1) (assign oC (.mod (.add (.var vTB1) (.var vTB2)) (.lit 2)))
      (.ite (.eq oODD v1) (assign oC (.lit 2)) (assign oC (.var vTB1)))) b1 30 (fun g => g.env oC = sel ∧
        g.out = b1.out ∧ g.wq = b1.wq ∧ Cst g ∧ AsgFr b1 g oC) := by
    refine Hs.ite (show vTAG ≠ v1 by decide) (fun he => ?_) (fun he => ?_)
    · have hk : c.kind = .pair := (kindTag_eq_one _).1 (by rw [← b1T]; simpa [Cnd.eval, p2.one] using he)
      refine Hs.mono (assign_spec oC (by decide) (by decide) (.mod (.add (.var vTB1) (.var vTB2)) (.lit 2)) b1
        (by aevar) (by aevar) p2 (by aeok [b1T1, b1T2])) (by simp [AE.cost]) ?_
      rintro g ⟨g1, g2, g3, g4, g5, g6⟩
      exact ⟨by rw [g1, hsel, if_pos hk]; simp [AE.eval, b1T1, b1T2], g5, g4, g6, g2⟩
    · have hk : c.kind ≠ .pair := fun h => by
        have : b1.env vTAG = 1 := by rw [b1T, h]; rfl
        simp [Cnd.eval, p2.one, this] at he
      refine Hs.ite (show oODD ≠ v1 by decide) (fun he2 => ?_) (fun he2 => ?_)
      · have ho : ∃ x ∈ c.parity, c.parity.count x % 2 = 1 := by
          have : b1.env oODD = 1 := by simpa [Cnd.eval, p2.one] using he2
          rw [p1] at this; exact (bnat_eq_one _).1 this
        refine Hs.mono (assign_spec oC (by decide) (by decide) (.lit 2) b1 (by aevar) (by aevar) p2 (by aeok []))
          (by simp [AE.cost]) ?_
        rintro g ⟨g1, g2, g3, g4, g5, g6⟩
        exact ⟨by rw [g1, hsel, if_neg hk, if_pos ho]; rfl, g5, g4, g6, g2⟩
      · have ho : ¬ ∃ x ∈ c.parity, c.parity.count x % 2 = 1 := by
          intro h
          have : b1.env oODD = 1 := by rw [p1]; exact bnat_one_of h
          simp [Cnd.eval, p2.one, this] at he2
        refine Hs.mono (assign_spec oC (by decide) (by decide) (.var vTB1) b1 (by aevar) (by aevar) p2 (by trivial))
          (by simp [AE.cost]) ?_
        rintro g ⟨g1, g2, g3, g4, g5, g6⟩
        exact ⟨by rw [g1, hsel, if_neg hk, if_neg ho]; simp [AE.eval, b1T1], g5, g4, g6, g2⟩
  refine Hs.then step (fun b2 ⟨q1, q2, q3, q4, q5⟩ k2 hk2 => ?_)
  -- the emitted word
  have hz : zw (zval c) = (if sel = 0 then zw 0 else if sel = 1 then zw 1 else zw (1 / 2)) := by
    rw [hsel]
    unfold zval
    cases hk : c.kind with
    | single =>
      have hp : c.parity = [] := hpar (by simp [hk])
      have ho : ¬ ∃ x ∈ c.parity, c.parity.count x % 2 = 1 := by rw [hp]; simp
      cases ht : c.first.table.getD 0 false <;> simp [ht, ho]
    | pair =>
      cases ht1 : c.first.table.getD 0 false <;> cases ht2 : c.second.table.getD 0 false <;> simp [ht1, ht2]
    | parity =>
      by_cases ho : ∃ x ∈ c.parity, c.parity.count x % 2 = 1
      · simp [ho]
      · cases ht : c.first.table.getD 0 false <;> simp [ht, ho]
  have hsel3 : sel ≤ 2 := by
    rw [hsel]; split_ifs
    · omega
    · omega
    · exact le_trans hb1 (by norm_num)
  have hzl : ∀ v, 1 ≤ (zw v).length := fun v => by unfold zw; rw [List.length_append, natWord_length]; omega
  have l0 := hzl 0
  have l1 := hzl 1
  have l2 := hzl (1 / 2)
  refine Hs.last (Hs.ite (show oC ≠ vZ by decide) (fun he => ?_) (fun he => ?_)) (fun g ⟨g1, g2, g3, g4⟩ k3 hk3 =>
    ⟨⟨by rw [g1, q2, p4, ← hz]; rfl, g2, by rw [g3, q3, p3],
      FrS.trans (p5.weaken (by decide)) (FrS.trans (q5.toS _ (by decide) (by decide)) (g4.toS.weaken (by decide)))⟩,
      by omega⟩)
    (R1 := fun g => g.out = b2.out ++ (if sel = 0 then zw 0 else if sel = 1 then zw 1 else zw (1 / 2)) ∧ Cst g ∧
      g.wq = b2.wq ∧ Fr b2 g [vJ]) (t := 2 * zwLen + 2)
  · have h0 : sel = 0 := by rw [← q1]; simpa [Cnd.eval, q4.z] using he
    refine Hs.mono (emitL_spec (zw 0) b2) (by unfold zwLen; omega) ?_
    rintro g ⟨g1, g2, g3, g4⟩
    have hcg : Cst g := Cst.of_fr q4 g4 (by decide) (by rw [g4 vPOS (by decide), g2]; exact q4.pos)
    exact ⟨by rw [g1, if_pos h0], hcg, g3, g4⟩
  · have h0 : sel ≠ 0 := by rw [← q1]; simpa [Cnd.eval, q4.z] using he
    refine Hs.ite (show oC ≠ v1 by decide) (fun he2 => ?_) (fun he2 => ?_)
    · have h1 : sel = 1 := by rw [← q1]; simpa [Cnd.eval, q4.one] using he2
      refine Hs.mono (emitL_spec (zw 1) b2) (by unfold zwLen; omega) ?_
      rintro g ⟨g1, g2, g3, g4⟩
      have hcg : Cst g := Cst.of_fr q4 g4 (by decide) (by rw [g4 vPOS (by decide), g2]; exact q4.pos)
      exact ⟨by rw [g1, if_neg h0, if_pos h1], hcg, g3, g4⟩
    · have h1 : sel ≠ 1 := by rw [← q1]; simpa [Cnd.eval, q4.one] using he2
      refine Hs.mono (emitL_spec (zw (1 / 2)) b2) (by unfold zwLen; omega) ?_
      rintro g ⟨g1, g2, g3, g4⟩
      have hcg : Cst g := Cst.of_fr q4 g4 (by decide) (by rw [g4 vPOS (by decide), g2]; exact q4.pos)
      exact ⟨by rw [g1, if_neg h0, if_neg h1], hcg, g3, g4⟩

theorem defOut_spec (a : DS VV) (hc : Cst a) :
    Hs C defOut a (2 * defW.length + 1) (fun b => b.out = a.out ++ (natWord 0 ++ outputWord defaultValue) ∧ Cst b ∧ b.wq = a.wq ∧
      b.cp = a.cp ∧ Fr a b [vJ]) := by
  refine Hs.mono (emitL_spec defW a) le_rfl ?_
  rintro g ⟨g1, g2, g3, g4⟩
  have hcg : Cst g := Cst.of_fr hc g4 (by decide) (by rw [g4 vPOS (by decide), g2]; exact hc.pos)
  exact ⟨g1, hcg, g3, g2, g4⟩

end NearCubicGates.Close.Dispatch
