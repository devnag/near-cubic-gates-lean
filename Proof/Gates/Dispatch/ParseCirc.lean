import Proof.Gates.Dispatch.Walk

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxRecDepth 4000

namespace NearCubicGates.Close.Dispatch

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Interfaces

variable {C : Ctx}

def vB0 : Fin VV := ⟨17, by decide⟩
def cG : Fin VV := ⟨18, by decide⟩
def cC : Fin VV := ⟨19, by decide⟩
def cTW : Fin VV := ⟨20, by decide⟩
def cT : Fin VV := ⟨21, by decide⟩
def cTB : Fin VV := ⟨22, by decide⟩
def cWOK : Fin VV := ⟨23, by decide⟩
def cNZ : Fin VV := ⟨24, by decide⟩
def cCO : Fin VV := ⟨25, by decide⟩
def cWN : Fin VV := ⟨26, by decide⟩
def ci : Fin VV := ⟨27, by decide⟩
def cj : Fin VV := ⟨28, by decide⟩

/-- A proposition as `0`/`1`. -/
def bnat (p : Prop) [Decidable p] : ℕ := (decide p).toNat

theorem bnat_le (p : Prop) [Decidable p] : bnat p ≤ 1 := by unfold bnat; cases decide p <;> simp

theorem bnat_congr {P Q : Prop} [Decidable P] [Decidable Q] (h : P ↔ Q) : bnat P = bnat Q := by
  unfold bnat; congr 1; exact decide_eq_decide.mpr h

/-- A gate's parameters fit `B` bits. -/
def GateOK {n : ℕ} (B : ℕ) (g : NormalizedThresholdGate n) : Prop :=
  (∀ x ∈ List.ofFn g.weight, natBitLength x.natAbs ≤ B) ∧ natBitLength g.threshold.natAbs ≤ B

instance {n : ℕ} (B : ℕ) (g : NormalizedThresholdGate n) : Decidable (GateOK B g) := by
  unfold GateOK; infer_instance

theorem len_le_of_drop {cw u rest : List Bool} {cp : ℕ} (h : cw.drop cp = u ++ rest) : u.length ≤ cw.length := by
  have := congrArg List.length h; simp at this; omega

theorem length_le_flatMap {α : Type} (xs : List α) (g : α → List Bool) (hg : ∀ x, 1 ≤ (g x).length) :
    xs.length ≤ (xs.flatMap g).length := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.flatMap_cons, List.length_append, List.length_cons]; have := hg x; omega

theorem intWord_len_pos (z : ℤ) : 1 ≤ (Interfaces.intWord z).length := by
  unfold Interfaces.intWord; simp [natWord_length]; omega

theorem natAbs_lt_of_drop {cw rest : List Bool} {cp : ℕ} {z : ℤ} (h : cw.drop cp = Interfaces.intWord z ++ rest) :
    z.natAbs < 2 ^ cw.length := by
  have h1 := len_le_of_drop h
  have h2 : (natWord z.natAbs).length ≤ (Interfaces.intWord z).length := by unfold Interfaces.intWord; simp
  have h3 := natBitLength_le_len z.natAbs
  calc z.natAbs < 2 ^ natBitLength z.natAbs := lt_natBitLength _
    _ ≤ 2 ^ cw.length := Nat.pow_le_pow_right (by norm_num) (by omega)

/-! ## A weight or threshold: read and test -/

def clrB : St VV := .ite (.lt vB0 t4) (.op (.zero cWOK)) skipS

def wBody : St VV := .seq readInt clrB

def wBodyT : List (Fin VV) := [t0, t1, t2, t3, t4, t8, vJ, vPOS, cWOK]

theorem wBody_spec (a : DS VV) (hc : Cst a) (z : ℤ) (rest : List Bool) (f : Prop) [Decidable f]
    (hf : a.env cWOK = bnat f) (hcw : C.cw.drop a.cp = Interfaces.intWord z ++ rest) (hW : C.cw.length + 2 ≤ C.Wd)
    (hL : C.cw.length + 2 < 2 ^ C.Wd) :
    Hs C wBody a (60 * C.cw.length + 80) (fun b => b.env cWOK = bnat (f ∧ natBitLength z.natAbs ≤ a.env vB0) ∧
      b.cp = a.cp + (Interfaces.intWord z).length ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧ Fr a b wBodyT) := by
  have hlz := len_le_of_drop hcw
  refine Hx.hs (Hs.then (readInt_spec a hc z rest hcw hW hL) (fun b ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩ n1 hn1 => ?_))
  have bB : b.env vB0 = a.env vB0 := b8 vB0 (by decide)
  have bW : b.env cWOK = bnat f := by rw [b8 cWOK (by decide), hf]
  have step : Hs C clrB b 2 (fun d => d.env cWOK = bnat (f ∧ natBitLength z.natAbs ≤ a.env vB0) ∧
      d.cp = b.cp ∧ d.wq = b.wq ∧ d.out = b.out ∧ Fr b d [cWOK, vJ]) := by
    refine Hs.ite (c := .lt vB0 t4) (show vB0 ≠ t4 by decide) (fun he => ?_) (fun he => ?_)
    · have hlt : a.env vB0 < natBitLength z.natAbs := by
        simp only [Cnd.eval, decide_eq_true_eq, bB, b3] at he; exact he
      refine Hs.mono (hs_zero C cWOK b) le_rfl ?_
      rintro d rfl
      exact ⟨by vsimp [bnat, show ¬ (natBitLength z.natAbs ≤ a.env vB0) by omega], rfl, rfl, rfl,
        Fr.set b _ (by decide)⟩
    · have hle : natBitLength z.natAbs ≤ a.env vB0 := by
        simp only [Cnd.eval, decide_eq_false_iff_not, not_lt, bB, b3] at he; exact he
      refine Hs.mono (skip_spec b) le_rfl ?_
      rintro d rfl
      exact ⟨by vsimp [bW, bnat, hle], rfl, rfl, rfl, Fr.set b _ (by decide)⟩
  refine Hs.last step (fun d ⟨d1, d2, d3, d4, d5⟩ n2 hn2 => ⟨⟨d1, by rw [d2, b4], by rw [d3, b5], by rw [d4, b6],
    Cst.of_fr (T := [cWOK, vJ]) b7 d5 (by decide) (by rw [d5 vPOS (by decide), b7.pos, d2]),
    Fr.trans (Fr.weaken b8 (by decide)) (Fr.weaken d5 (by decide))⟩, by omega⟩)

/-! ## A gate -/

def gateBody : St VV :=
  .seq readNat (.seq (.op (.copy cWN t3)) (.seq (.op (.zero cj))
    (.seq (.loop (.lt cj cWN) (.seq wBody (.op (.inc cj)))) wBody)))

def gateT : List (Fin VV) := [t0, t1, t2, t3, t4, t8, vJ, vPOS, cWOK, cWN, cj]

theorem gateBody_spec {n : ℕ} (a : DS VV) (hc : Cst a) (g : NormalizedThresholdGate n) (rest : List Bool)
    (f : Prop) [Decidable f] (hf : a.env cWOK = bnat f) (hcw : C.cw.drop a.cp = gateWord g ++ rest)
    (hW : C.cw.length + 2 ≤ C.Wd) (hL : C.cw.length + 2 < 2 ^ C.Wd) :
    Hs C gateBody a (100 * (C.cw.length + 2) ^ 2) (fun b => b.env cWOK = bnat (f ∧ GateOK (a.env vB0) g) ∧
      b.cp = a.cp + (gateWord g).length ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧ Fr a b gateT) := by
  set ws := List.ofFn g.weight with hws
  have hg : gateWord g = natWord ws.length ++ (ws.flatMap Interfaces.intWord ++ Interfaces.intWord g.threshold) := by
    simp [gateWord, listWord, hws, List.append_assoc]
  have hlg := len_le_of_drop hcw
  rw [hg] at hlg
  simp only [List.length_append] at hlg
  rw [hg, List.append_assoc] at hcw
  have hwsL : ws.length ≤ C.cw.length := by
    have := length_le_flatMap ws Interfaces.intWord intWord_len_pos
    omega
  have hnbw := natBitLength_le_len ws.length
  refine Hx.hs (Hs.then (readNat_spec a hc ws.length _ hcw (by omega) hL)
    (fun b ⟨b1, b2, b3, b4, b5, b6, b7⟩ n1 hn1 => ?_))
  refine Hs.then (hs_copy C cWN t3 b (by decide)) (fun b' hb' n2 hn2 => ?_)
  subst hb'
  refine Hs.then (hs_zero C cj _) (fun b'' hb'' n3 hn3 => ?_)
  subst hb''
  set d := (b.set cWN (b.env t3)).set cj 0 with hd
  have dc : Cst d := Cst.of_fr (T := [cWN, cj]) b6 (Fr.trans (Fr.set b _ (by decide)) (Fr.set _ _ (by decide)))
    (by decide) (by vsimp [hd, b6.pos])
  have dcw : C.cw.drop d.cp = ws.flatMap Interfaces.intWord ++ Interfaces.intWord g.threshold ++ rest := by
    show C.cw.drop b.cp = _
    rw [b3, ← List.drop_drop, hcw, List.drop_left, List.append_assoc]
  -- the weights
  let P : ℕ → DS VV → Prop := fun k e => e.env cWOK = bnat (f ∧ ∀ x ∈ ws.take k, natBitLength x.natAbs ≤ a.env vB0) ∧
    e.env vB0 = a.env vB0 ∧ e.wq = a.wq ∧ e.out = a.out ∧ Cst e ∧ Fr a e gateT
  have hP : ∀ k e v, P k e → P k (e.set cj v) := by
    rintro k e v ⟨p1, p2, p3, p4, p5, p6⟩
    exact ⟨by vsimp [p1], by vsimp [p2], p3, p4, Cst.of_fr (T := [cj]) p5 (Fr.set e _ (by decide)) (by decide)
      (by vsimp [p5.pos]), Fr.trans p6 (Fr.set e _ (by decide))⟩
  have l := walk (C := C) ws Interfaces.intWord cj cWN (by decide) wBody P (60 * C.cw.length + 80)
    (Interfaces.intWord g.threshold ++ rest) hP
    (by
      intro k hk e ⟨p1, p2, p3, p4, p5, p6⟩ hi hn hd'
      refine Hs.mono (wBody_spec e p5 ws[k] _ _ p1 hd' hW hL) le_rfl ?_
      rintro r ⟨r1, r2, r3, r4, r5, r6⟩
      refine ⟨⟨?_, by rw [r6 vB0 (by decide), p2], by rw [r3, p3], by rw [r4, p4], r5,
        Fr.trans p6 (Fr.weaken r6 (by decide))⟩, by rw [r6 cj (by decide), hi], by rw [r6 cWN (by decide), hn], r2⟩
      rw [r1, p2]
      unfold bnat
      congr 1
      apply decide_eq_decide.mpr
      rw [List.take_add_one, List.getElem?_eq_getElem hk]
      simp only [Option.toList, List.mem_append, List.mem_singleton]
      constructor
      · rintro ⟨⟨hf', hall⟩, hlast⟩; exact ⟨hf', fun x hx => hx.elim (hall x) (fun e => e ▸ hlast)⟩
      · rintro ⟨hf', hall⟩; exact ⟨⟨hf', fun x hx => hall x (Or.inl hx)⟩, hall _ (Or.inr rfl)⟩)
    (by omega) d
    ⟨by vsimp [hd, b7 cWOK (by decide), hf, bnat], by vsimp [hd, b7 vB0 (by decide)], by vsimp [hd, b4],
      by vsimp [hd, b5], dc, Fr.trans (Fr.weaken b7 (by decide)) (Fr.trans (Fr.set b _ (by decide))
        (Fr.set _ _ (by decide)))⟩ (by vsimp [hd]) (by vsimp [hd, b1]) (by rw [dcw, List.append_assoc])
  refine Hs.then l (fun e ⟨⟨p1, p2, p3, p4, p5, p6⟩, e2, e3, e4⟩ n4 hn4 => ?_)
  -- the threshold
  have ecw : C.cw.drop e.cp = Interfaces.intWord g.threshold ++ rest := by
    rw [e4, ← List.drop_drop, dcw, List.append_assoc, List.drop_left]
  refine Hs.last (wBody_spec e p5 g.threshold rest _ p1 ecw hW hL) ?_
  rintro r ⟨r1, r2, r3, r4, r5, r6⟩ n5 hn5
  refine ⟨⟨?_, ?_, by rw [r3, p3], by rw [r4, p4], r5, Fr.trans p6 (Fr.weaken r6 (by decide))⟩, ?_⟩
  · rw [r1, p2, List.take_length]
    unfold bnat GateOK
    congr 1
    apply decide_eq_decide.mpr
    simp only [hws, and_assoc]
  · rw [r2, e4]; show b.cp + _ + _ = _
    rw [b3, hg]; simp only [List.length_append]; ring
  · have hwsc : ws.length * (60 * C.cw.length + 80 + 2 + 2) ≤ C.cw.length * (60 * C.cw.length + 84) :=
      Nat.mul_le_mul_right _ hwsL
    have hQ : C.cw.length * (60 * C.cw.length + 84) = 60 * (C.cw.length * C.cw.length) + 84 * C.cw.length := by
      ring
    have hsq : 100 * (C.cw.length + 2) ^ 2 = 100 * (C.cw.length * C.cw.length) + 400 * C.cw.length + 400 := by
      ring
    omega

/-! ## The coefficients and the table -/

def cBody : St VV := .seq readInt (.seq (.ite (.eq t3 vZ) (.op (.zero cNZ)) skipS) (.op (.add cTW t3)))

def cBodyT : List (Fin VV) := [t0, t1, t2, t3, t4, t8, vJ, vPOS, cNZ, cTW]

theorem cBody_spec (a : DS VV) (hc : Cst a) (z : ℤ) (rest : List Bool) (f : Prop) [Decidable f] (s : ℕ)
    (hf : a.env cNZ = bnat f) (hs : a.env cTW = s) (hcw : C.cw.drop a.cp = Interfaces.intWord z ++ rest)
    (hW : C.cw.length + 2 ≤ C.Wd) (hL : C.cw.length + 2 < 2 ^ C.Wd) (hs' : s + z.natAbs < 2 ^ C.Wd) :
    Hs C cBody a (60 * C.cw.length + 80) (fun b => b.env cNZ = bnat (f ∧ z ≠ 0) ∧ b.env cTW = s + z.natAbs ∧
      b.cp = a.cp + (Interfaces.intWord z).length ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧ Fr a b cBodyT) := by
  have hlz := len_le_of_drop hcw
  refine Hx.hs (Hs.then (readInt_spec a hc z rest hcw hW hL) (fun b ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩ n1 hn1 => ?_))
  have bZ : b.env vZ = 0 := b7.z
  have bN : b.env cNZ = bnat f := by rw [b8 cNZ (by decide), hf]
  have bT : b.env cTW = s := by rw [b8 cTW (by decide), hs]
  have step : Hs C (.ite (.eq t3 vZ) (.op (.zero cNZ)) skipS) b 2 (fun d => d.env cNZ = bnat (f ∧ z ≠ 0) ∧
      d.env cTW = s ∧ d.env t3 = z.natAbs ∧ d.cp = b.cp ∧ d.wq = b.wq ∧ d.out = b.out ∧ Fr b d [cNZ, vJ]) := by
    refine Hs.ite (c := .eq t3 vZ) (show t3 ≠ vZ by decide) (fun he => ?_) (fun he => ?_)
    · have hz : z = 0 := by
        simp only [Cnd.eval, decide_eq_true_eq, bZ, b2] at he; omega
      refine Hs.mono (hs_zero C cNZ b) le_rfl ?_
      rintro d rfl
      exact ⟨by vsimp [bnat, hz], by vsimp [bT], by vsimp [b2], rfl, rfl, rfl, Fr.set b _ (by decide)⟩
    · have hz : z ≠ 0 := by
        simp only [Cnd.eval, decide_eq_false_iff_not, bZ, b2] at he; omega
      refine Hs.mono (skip_spec b) le_rfl ?_
      rintro d rfl
      exact ⟨by vsimp [bN, bnat, hz], by vsimp [bT], by vsimp [b2], rfl, rfl, rfl, Fr.set b _ (by decide)⟩
  refine Hs.then step (fun d ⟨d1, d2, d3, d4, d5, d6, d7⟩ n2 hn2 => ?_)
  refine Hs.last (hs_add C cTW t3 d (by decide) (by rw [d2, d3]; exact hs')) (fun e he n3 hn3 => ?_)
  subst he
  refine ⟨⟨by vsimp [d1], by vsimp [d2, d3], by show d.cp = _; rw [d4, b4], by show d.wq = _; rw [d5, b5],
    by show d.out = _; rw [d6, b6], ?_, ?_⟩, by omega⟩
  · exact Cst.of_fr (T := [cNZ, vJ, cTW]) b7 (Fr.trans (Fr.weaken d7 (by decide)) (Fr.set d _ (by decide)))
      (by decide) (by vsimp [d7 vPOS (by decide), b7.pos, d4])
  · exact Fr.trans (Fr.weaken b8 (by decide)) (Fr.trans (Fr.weaken d7 (by decide)) (Fr.set d _ (by decide)))

def tBody : St VV := .seq readNat (.ite (.eq ci vZ) (.op (.copy cTB t3)) skipS)

def tBodyT : List (Fin VV) := [t0, t1, t2, t3, t4, vJ, vPOS, cTB]

theorem tBody_spec (a : DS VV) (hc : Cst a) (bt : Bool) (rest : List Bool) (k : ℕ) (hk : a.env ci = k)
    (hcw : C.cw.drop a.cp = bitWord bt ++ rest) (hW : C.cw.length + 2 ≤ C.Wd) (hL : C.cw.length + 2 < 2 ^ C.Wd) :
    Hs C tBody a 70 (fun b => b.env cTB = (if k = 0 then bt.toNat else a.env cTB) ∧
      b.cp = a.cp + (bitWord bt).length ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧ Fr a b tBodyT) := by
  have hbt : bitWord bt = natWord (bt.toNat) := by cases bt <;> rfl
  rw [hbt] at hcw ⊢
  have hnb : natBitLength bt.toNat = 1 := by cases bt <;> rfl
  have hlb := len_le_of_drop hcw
  rw [natWord_length] at hlb
  refine Hx.hs (Hs.then (readNat_spec a hc bt.toNat rest hcw (by omega) hL)
    (fun b ⟨b1, b2, b3, b4, b5, b6, b7⟩ n1 hn1 => ?_))
  have bZ : b.env vZ = 0 := b6.z
  have bi : b.env ci = k := by rw [b7 ci (by decide), hk]
  have step : Hs C (.ite (.eq ci vZ) (.op (.copy cTB t3)) skipS) b 2 (fun d =>
      d.env cTB = (if k = 0 then bt.toNat else a.env cTB) ∧ d.cp = b.cp ∧ d.wq = b.wq ∧ d.out = b.out ∧
        Fr b d [cTB, vJ]) := by
    refine Hs.ite (c := .eq ci vZ) (show ci ≠ vZ by decide) (fun he => ?_) (fun he => ?_)
    · have hk0 : k = 0 := by simp only [Cnd.eval, decide_eq_true_eq, bZ, bi] at he; exact he
      refine Hs.mono (hs_copy C cTB t3 b (by decide)) le_rfl ?_
      rintro d rfl
      exact ⟨by vsimp [hk0, b1], rfl, rfl, rfl, Fr.set b _ (by decide)⟩
    · have hk0 : k ≠ 0 := by simp only [Cnd.eval, decide_eq_false_iff_not, bZ, bi] at he; exact he
      refine Hs.mono (skip_spec b) le_rfl ?_
      rintro d rfl
      exact ⟨by vsimp [hk0, b7 cTB (by decide)], rfl, rfl, rfl, Fr.set b _ (by decide)⟩
  refine Hs.last step (fun d ⟨d1, d2, d3, d4, d5⟩ n2 hn2 => ⟨⟨d1, by rw [d2, b3], by rw [d3, b4], by rw [d4, b5],
    Cst.of_fr (T := [cTB, vJ]) b6 d5 (by decide) (by rw [d5 vPOS (by decide), b6.pos, d2]),
    Fr.trans (Fr.weaken b7 (by decide)) (Fr.weaken d5 (by decide))⟩, by omega⟩)

/-! ## The whole circuit -/

theorem sum_natAbs_lt (xs : List ℤ) : (xs.map Int.natAbs).sum < 2 ^ (xs.flatMap Interfaces.intWord).length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, List.flatMap_cons, List.length_append, pow_add]
    have h1 : x.natAbs < 2 ^ (Interfaces.intWord x).length := by
      have h2 : (natWord x.natAbs).length ≤ (Interfaces.intWord x).length := by unfold Interfaces.intWord; simp
      have h3 := natBitLength_le_len x.natAbs
      calc x.natAbs < 2 ^ natBitLength x.natAbs := lt_natBitLength _
        _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hA : 1 ≤ 2 ^ (Interfaces.intWord x).length := Nat.one_le_two_pow
    have hB : 1 ≤ 2 ^ (xs.flatMap Interfaces.intWord).length := Nat.one_le_two_pow
    nlinarith

theorem take_sum_succ (l : List ℕ) (k : ℕ) (hk : k < l.length) : (l.take (k + 1)).sum = (l.take k).sum + l[k] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, List.sum_append, List.sum_singleton]

theorem take_sum_le (l : List ℕ) (k : ℕ) : (l.take k).sum ≤ l.sum := by
  have := List.sum_take_add_sum_drop l k; omega

theorem take_succ_iff {α : Type} (xs : List α) (P : α → Prop) (k : ℕ) (hk : k < xs.length) :
    ((∀ x ∈ xs.take k, P x) ∧ P (xs[k]'hk)) ↔ ∀ x ∈ xs.take (k + 1), P x := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk]
  simp only [Option.toList, List.mem_append, List.mem_singleton]
  constructor
  · rintro ⟨hall, hlast⟩; exact fun x hx => hx.elim (hall x) (fun e => e ▸ hlast)
  · intro hall; exact ⟨fun x hx => hall x (Or.inl hx), hall _ (Or.inr rfl)⟩

/-! ### Phase 1: the gates -/

def pc1 : St VV :=
  .seq readNat (.seq (.op (.copy cG t3)) (.seq (.op (.copy cWOK v1)) (.seq (.op (.zero ci))
    (.loop (.lt ci cG) (.seq gateBody (.op (.inc ci)))))))

def parseCircT : List (Fin VV) := [t0, t1, t2, t3, t4, t8, vJ, vPOS, cG, cC, cTW, cT, cTB, cWOK, cNZ, cCO, cWN, ci, cj]
def pc1T : List (Fin VV) := [t0, t1, t2, t3, t4, t8, vJ, vPOS, cG, cWOK, ci, cWN, cj]
def pc2T : List (Fin VV) := [t0, t1, t2, t3, t4, t8, vJ, vPOS, cCO, cC, cTW, cNZ, ci]
def pc3T : List (Fin VV) := [t0, t1, t2, t3, t4, vJ, vPOS, cT, cTB, ci]

theorem pc1_spec {n : ℕ} (gs : List (NormalizedThresholdGate n)) (a : DS VV) (hc : Cst a) (rest : List Bool)
    (hcw : C.cw.drop a.cp = listWord gateWord gs ++ rest) (hW : 2 * C.cw.length + 2 ≤ C.Wd)
    (hL : C.cw.length + 2 < 2 ^ C.Wd) :
    Hs C pc1 a (200 * (C.cw.length + 2) ^ 3) (fun b => b.env cWOK = bnat (∀ g ∈ gs, GateOK (a.env vB0) g) ∧
      b.env cG = gs.length ∧ b.cp = a.cp + (listWord gateWord gs).length ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧
      Fr a b pc1T) := by
  set L := C.cw.length with hLdef
  have hlen := len_le_of_drop hcw
  simp only [listWord, List.length_append] at hlen
  simp only [listWord, List.append_assoc] at hcw
  have hgsL : gs.length ≤ L := by
    have := length_le_flatMap gs gateWord (fun g => by unfold gateWord listWord; simp [natWord_length]; omega)
    omega
  have hnb := natBitLength_le_len gs.length
  refine Hx.hs (Hs.then (readNat_spec a hc gs.length _ hcw (by omega) hL)
    (fun b ⟨b1, b2, b3, b4, b5, b6, b7⟩ n1 hn1 => ?_))
  refine Hs.then (hs_copy C cG t3 b (by decide)) (fun b' hb' n2 hn2 => ?_)
  subst hb'
  refine Hs.then (hs_copy C cWOK v1 _ (by decide)) (fun b'' hb'' n3 hn3 => ?_)
  subst hb''
  refine Hs.then (hs_zero C ci _) (fun d hd n4 hn4 => ?_)
  subst hd
  set d := ((b.set cG (b.env t3)).set cWOK ((b.set cG (b.env t3)).env v1)).set ci 0 with hd
  have dcw : C.cw.drop d.cp = gs.flatMap gateWord ++ rest := by
    show C.cw.drop b.cp = _
    rw [b3, ← List.drop_drop, hcw, List.drop_left]
  have dT : Fr a d pc1T := Fr.trans (Fr.weaken b7 (by decide)) (Fr.trans (Fr.set b _ (by decide))
    (Fr.trans (Fr.set _ _ (by decide)) (Fr.set _ _ (by decide))))
  have dc : Cst d := Cst.of_fr hc dT (by decide) (by vsimp [hd, b6.pos])
  let PG : ℕ → DS VV → Prop := fun k e => e.env cWOK = bnat (∀ g ∈ gs.take k, GateOK (a.env vB0) g) ∧
    e.env vB0 = a.env vB0 ∧ e.wq = a.wq ∧ e.out = a.out ∧ Cst e ∧ Fr a e pc1T
  have hPG : ∀ k e v, PG k e → PG k (e.set ci v) := by
    rintro k e v ⟨p1, p2, p3, p4, p5, p6⟩
    exact ⟨by vsimp [p1], by vsimp [p2], p3, p4, Cst.of_fr (T := [ci]) p5 (Fr.set e _ (by decide)) (by decide)
      (by vsimp [p5.pos]), Fr.trans p6 (Fr.set e _ (by decide))⟩
  have lg := walk (C := C) gs gateWord ci cG (by decide) gateBody PG (100 * (L + 2) ^ 2) _ hPG
    (by
      intro k hk e ⟨p1, p2, p3, p4, p5, p6⟩ hi hn hd'
      refine Hs.mono (gateBody_spec e p5 gs[k] _ _ p1 hd' (by omega) hL) le_rfl ?_
      rintro r ⟨r1, r2, r3, r4, r5, r6⟩
      refine ⟨⟨?_, by rw [r6 vB0 (by decide), p2], by rw [r3, p3], by rw [r4, p4], r5,
        Fr.trans p6 (Fr.weaken r6 (by decide))⟩, by rw [r6 ci (by decide), hi], by rw [r6 cG (by decide), hn], r2⟩
      rw [r1, p2]; unfold bnat; congr 1; exact decide_eq_decide.mpr (take_succ_iff gs _ k hk))
    (by omega) d
    ⟨by vsimp [hd, hc.one, b7 v1 (by decide), bnat], by vsimp [hd, b7 vB0 (by decide)], by vsimp [hd, b4],
      by vsimp [hd, b5], dc, dT⟩ (by vsimp [hd]) (by vsimp [hd, b1]) dcw
  refine Hs.last lg (fun e ⟨⟨p1, p2, p3, p4, p5, p6⟩, e2, e3, e4⟩ n5 hn5 => ?_)
  rw [List.take_length] at p1
  refine ⟨⟨p1, e3, ?_, p3, p4, p5, p6⟩, ?_⟩
  · rw [e4]; show b.cp + _ = _
    rw [b3]; simp only [listWord, List.length_append]; ring
  · have hb1 : n1 ≤ 30 * L + 30 := by omega
    set S := (L + 2) ^ 2 with hS
    have hgs : gs.length * (100 * S + 2 + 2) ≤ L * (100 * S + 4) := Nat.mul_le_mul_right _ hgsL
    have e1 : L * (100 * S + 4) = 100 * (L * S) + 4 * L := by ring
    have e4' : L * S + 2 * S = (L + 2) ^ 3 := by rw [hS]; ring
    have e5 : L ≤ S := by rw [hS]; nlinarith
    have e6 : 4 ≤ S := by rw [hS]; nlinarith
    omega

/-! ### Phase 2: the coefficients -/

def pc2 : St VV :=
  .seq (.op (.copy cCO vPOS)) (.seq readNat (.seq (.op (.copy cC t3)) (.seq (.op (.zero cTW))
    (.seq (.op (.copy cNZ v1)) (.seq (.op (.zero ci)) (.loop (.lt ci cC) (.seq cBody (.op (.inc ci)))))))))

theorem pc2_spec (cs : List ℤ) (a : DS VV) (hc : Cst a) (rest : List Bool)
    (hcw : C.cw.drop a.cp = listWord Interfaces.intWord cs ++ rest) (hW : 2 * C.cw.length + 2 ≤ C.Wd)
    (hL : C.cw.length + 2 < 2 ^ C.Wd) :
    Hs C pc2 a (200 * (C.cw.length + 2) ^ 2) (fun b => b.env cNZ = bnat (∀ x ∈ cs, x ≠ 0) ∧
      b.env cTW = (cs.map Int.natAbs).sum ∧ b.env cC = cs.length ∧ b.env cCO = a.cp ∧
      b.cp = a.cp + (listWord Interfaces.intWord cs).length ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧
      Fr a b pc2T) := by
  set L := C.cw.length with hLdef
  have hlen := len_le_of_drop hcw
  simp only [listWord, List.length_append] at hlen
  simp only [listWord, List.append_assoc] at hcw
  have hcsL : cs.length ≤ L := by
    have := length_le_flatMap cs Interfaces.intWord intWord_len_pos; omega
  have hTW : (cs.map Int.natAbs).sum < 2 ^ C.Wd := by
    have := sum_natAbs_lt cs
    calc (cs.map Int.natAbs).sum < _ := this
      _ ≤ 2 ^ C.Wd := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hnb := natBitLength_le_len cs.length
  refine Hx.hs (Hs.then (hs_copy C cCO vPOS a (by decide)) (fun f hf n6 hn6 => ?_))
  subst hf
  have fc : Cst (a.set cCO (a.env vPOS)) := Cst.of_fr (T := [cCO]) hc (Fr.set a _ (by decide)) (by decide)
    (by vsimp [hc.pos])
  refine Hs.then (readNat_spec _ fc cs.length _ hcw (by omega) hL)
    (fun g ⟨g1, g2, g3, g4, g5, g6, g7⟩ n7 hn7 => ?_)
  simp only [DS.set_cp, DS.set_wq, DS.set_out] at g3 g4 g5
  refine Hs.then (hs_copy C cC t3 g (by decide)) (fun g' hg' n8 hn8 => ?_)
  subst hg'
  refine Hs.then (hs_zero C cTW _) (fun g'' hg'' n9 hn9 => ?_)
  subst hg''
  refine Hs.then (hs_copy C cNZ v1 _ (by decide)) (fun g3' hg3 n10 hn10 => ?_)
  subst hg3
  refine Hs.then (hs_zero C ci _) (fun h0 hh0 n11 hn11 => ?_)
  subst hh0
  set q := ((((g.set cC (g.env t3)).set cTW 0).set cNZ (((g.set cC (g.env t3)).set cTW 0).env v1)).set ci 0)
    with hq
  have qcw : C.cw.drop q.cp = cs.flatMap Interfaces.intWord ++ rest := by
    show C.cw.drop g.cp = _
    rw [g3, ← List.drop_drop, hcw, List.drop_left]
  have qT : Fr a q pc2T := Fr.trans (Fr.set a _ (by decide)) (Fr.trans (Fr.weaken g7 (by decide))
    (Fr.trans (Fr.set _ _ (by decide)) (Fr.trans (Fr.set _ _ (by decide)) (Fr.trans (Fr.set _ _ (by decide))
      (Fr.set _ _ (by decide))))))
  have qc : Cst q := Cst.of_fr hc qT (by decide) (by vsimp [hq, g6.pos])
  have hco : q.env cCO = a.cp := by
    rw [show q.env cCO = a.env vPOS by vsimp [hq, g7 cCO (by decide)], hc.pos]
  let PC : ℕ → DS VV → Prop := fun k r => r.env cNZ = bnat (∀ x ∈ cs.take k, x ≠ 0) ∧
    r.env cTW = ((cs.map Int.natAbs).take k).sum ∧ r.env cCO = a.cp ∧
    r.wq = a.wq ∧ r.out = a.out ∧ Cst r ∧ Fr a r pc2T
  have hPC : ∀ k r v, PC k r → PC k (r.set ci v) := by
    rintro k r v ⟨p1', p2', p3', p4', p5', p6', p7'⟩
    exact ⟨by vsimp [p1'], by vsimp [p2'], by vsimp [p3'], p4', p5',
      Cst.of_fr (T := [ci]) p6' (Fr.set r _ (by decide)) (by decide) (by vsimp [p6'.pos]),
      Fr.trans p7' (Fr.set r _ (by decide))⟩
  have lc := walk (C := C) cs Interfaces.intWord ci cC (by decide) cBody PC (60 * L + 80) _ hPC
    (by
      intro k hk r ⟨p1', p2', p3', p4', p5', p6', p7'⟩ hi hn hd'
      have hk' : k < (cs.map Int.natAbs).length := by simpa using hk
      have hsum : ((cs.map Int.natAbs).take k).sum + cs[k].natAbs < 2 ^ C.Wd := by
        have h1 := take_sum_succ (cs.map Int.natAbs) k hk'
        have h2 := take_sum_le (cs.map Int.natAbs) (k + 1)
        simp only [List.getElem_map] at h1
        omega
      refine Hs.mono (cBody_spec r p6' cs[k] _ _ _ p1' p2' hd' (by omega) hL hsum) le_rfl ?_
      rintro r' ⟨r1, r2, r3, r4, r5, r6, r7⟩
      refine ⟨⟨?_, ?_, by rw [r7 cCO (by decide), p3'], by rw [r4, p4'], by rw [r5, p5'], r6,
        Fr.trans p7' (Fr.weaken r7 (by decide))⟩, by rw [r7 ci (by decide), hi], by rw [r7 cC (by decide), hn], r3⟩
      · rw [r1]; unfold bnat; congr 1; exact decide_eq_decide.mpr (take_succ_iff cs (· ≠ 0) k hk)
      · rw [r2, take_sum_succ (cs.map Int.natAbs) k hk']; simp)
    (by omega) q
    ⟨by vsimp [hq, g6.one, bnat], by vsimp [hq], hco, by vsimp [hq, g4], by vsimp [hq, g5], qc, qT⟩
    (by vsimp [hq]) (by vsimp [hq, g1]) qcw
  refine Hs.last lc (fun r ⟨⟨q1, q2, q3, q4, q5, q6, q7⟩, r2, r3, r4⟩ n12 hn12 => ?_)
  rw [List.take_length] at q1
  rw [List.take_of_length_le (by simp)] at q2
  refine ⟨⟨q1, q2, r3, q3, ?_, q4, q5, q6, q7⟩, ?_⟩
  · rw [r4]; show g.cp + _ = _
    rw [g3]; simp only [listWord, List.length_append]; ring
  · have hb7 : n7 ≤ 30 * L + 30 := by omega
    have hcs : cs.length * (60 * L + 80 + 2 + 2) ≤ L * (60 * L + 84) := Nat.mul_le_mul_right _ hcsL
    have e2 : L * (60 * L + 84) = 60 * (L * L) + 84 * L := by ring
    have e3 : 200 * (L + 2) ^ 2 = 200 * (L * L) + 800 * L + 800 := by ring
    omega

/-! ### Phase 3: the table -/

def pc3 : St VV :=
  .seq readNat (.seq (.op (.copy cT t3)) (.seq (.op (.zero cTB)) (.seq (.op (.zero ci))
    (.loop (.lt ci cT) (.seq tBody (.op (.inc ci)))))))

theorem pc3_spec (tb : List Bool) (a : DS VV) (hc : Cst a) (rest : List Bool)
    (hcw : C.cw.drop a.cp = listWord bitWord tb ++ rest) (hW : 2 * C.cw.length + 2 ≤ C.Wd)
    (hL : C.cw.length + 2 < 2 ^ C.Wd) :
    Hs C pc3 a (100 * (C.cw.length + 2) ^ 2) (fun b => b.env cTB = (tb.getD 0 false).toNat ∧ b.env cT = tb.length ∧
      b.cp = a.cp + (listWord bitWord tb).length ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧ Fr a b pc3T) := by
  set L := C.cw.length with hLdef
  have hlen := len_le_of_drop hcw
  simp only [listWord, List.length_append] at hlen
  simp only [listWord, List.append_assoc] at hcw
  have htbL : tb.length ≤ L := by
    have := length_le_flatMap tb bitWord (fun b => by cases b <;> simp [bitWord, natWord_length]); omega
  have hnb := natBitLength_le_len tb.length
  refine Hx.hs (Hs.then (readNat_spec a hc tb.length _ hcw (by omega) hL)
    (fun u ⟨u1, u2, u3, u4, u5, u6, u7⟩ n13 hn13 => ?_))
  refine Hs.then (hs_copy C cT t3 u (by decide)) (fun u' hu' n14 hn14 => ?_)
  subst hu'
  refine Hs.then (hs_zero C cTB _) (fun u'' hu'' n15 hn15 => ?_)
  subst hu''
  refine Hs.then (hs_zero C ci _) (fun z' hz' n16 hn16 => ?_)
  subst hz'
  set z := ((u.set cT (u.env t3)).set cTB 0).set ci 0 with hz
  have zcw : C.cw.drop z.cp = tb.flatMap bitWord ++ rest := by
    show C.cw.drop u.cp = _
    rw [u3, ← List.drop_drop, hcw, List.drop_left]
  have zT : Fr a z pc3T := Fr.trans (Fr.weaken u7 (by decide)) (Fr.trans (Fr.set _ _ (by decide))
    (Fr.trans (Fr.set _ _ (by decide)) (Fr.set _ _ (by decide))))
  have zc : Cst z := Cst.of_fr hc zT (by decide) (by vsimp [hz, u6.pos])
  let PT : ℕ → DS VV → Prop := fun k x => x.env cTB = ((tb.take k).getD 0 false).toNat ∧
    x.wq = a.wq ∧ x.out = a.out ∧ Cst x ∧ Fr a x pc3T
  have hPT : ∀ k x v, PT k x → PT k (x.set ci v) := by
    rintro k x v ⟨p1', p2', p3', p4', p5'⟩
    exact ⟨by vsimp [p1'], p2', p3', Cst.of_fr (T := [ci]) p4' (Fr.set x _ (by decide)) (by decide)
      (by vsimp [p4'.pos]), Fr.trans p5' (Fr.set x _ (by decide))⟩
  have lt := walk (C := C) tb bitWord ci cT (by decide) tBody PT 70 _ hPT
    (by
      intro k hk x ⟨p1', p2', p3', p4', p5'⟩ hi hn hd'
      refine Hs.mono (tBody_spec x p4' tb[k] _ k hi hd' (by omega) hL) le_rfl ?_
      rintro y ⟨y1, y2, y3, y4, y5, y6⟩
      refine ⟨⟨?_, by rw [y3, p2'], by rw [y4, p3'], y5, Fr.trans p5' (Fr.weaken y6 (by decide))⟩,
        by rw [y6 ci (by decide), hi], by rw [y6 cT (by decide), hn], y2⟩
      rw [y1, p1']
      rcases Nat.eq_zero_or_pos k with hk0 | hk0
      · subst hk0; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
      · rw [if_neg (by omega), List.take_add_one, List.getElem?_eq_getElem hk]
        simp only [Option.toList]
        rw [List.getD_append _ _ _ _ (by simp; omega)])
    (by omega) z
    ⟨by vsimp [hz], by vsimp [hz, u4], by vsimp [hz, u5], zc, zT⟩
    (by vsimp [hz]) (by vsimp [hz, u1]) zcw
  refine Hs.last lt (fun x ⟨⟨x1, x2, x3, x4, x5⟩, xi, xn, xcp⟩ n17 hn17 => ?_)
  rw [List.take_length] at x1
  refine ⟨⟨x1, xn, ?_, x2, x3, x4, x5⟩, ?_⟩
  · rw [xcp]; show u.cp + _ = _
    rw [u3]; simp only [listWord, List.length_append]; ring
  · have hb : n13 ≤ 30 * L + 30 := by omega
    have htb : tb.length * (70 + 2 + 2) ≤ L * 74 := Nat.mul_le_mul_right _ htbL
    have e3 : 100 * (L + 2) ^ 2 = 100 * (L * L) + 400 * L + 400 := by ring
    omega

/-! ### The whole circuit -/

def parseCirc : St VV := .seq pc1 (.seq pc2 pc3)

/-- The results of `parseCirc` on circuit `Cc` (with bit bound `B`), read at cursor `p`. -/
structure CircOut {n : ℕ} (Cc : NCircuit n) (B p : ℕ) (b : DS VV) : Prop where
  g : b.env cG = Cc.gates.length
  c : b.env cC = Cc.coeffs.length
  tw : b.env cTW = Cc.topWeight
  t : b.env cT = Cc.table.length
  tb : b.env cTB = (Cc.table.getD 0 false).toNat
  wok : b.env cWOK = bnat (∀ g ∈ Cc.gates, GateOK B g)
  nz : b.env cNZ = bnat (∀ x ∈ Cc.coeffs, x ≠ 0)
  co : b.env cCO = p + (listWord gateWord Cc.gates).length

/-- Its cost bound. -/
def circCost (L : ℕ) : ℕ := 600 * (L + 2) ^ 3

theorem parseCirc_spec {n : ℕ} (Cc : NCircuit n) (a : DS VV) (hc : Cst a) (rest : List Bool)
    (hcw : C.cw.drop a.cp = circuitWord Cc ++ rest) (hW : 2 * C.cw.length + 2 ≤ C.Wd)
    (hL : C.cw.length + 2 < 2 ^ C.Wd) :
    Hs C parseCirc a (circCost C.cw.length) (fun b => CircOut Cc (a.env vB0) a.cp b ∧
      b.cp = a.cp + (circuitWord Cc).length ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧ Fr a b parseCircT) := by
  have hcwd : circuitWord Cc = listWord gateWord Cc.gates ++ (listWord Interfaces.intWord Cc.coeffs ++
      listWord bitWord Cc.table) := by simp [circuitWord, List.append_assoc]
  rw [hcwd, List.append_assoc] at hcw
  refine Hx.hs (Hs.then (pc1_spec Cc.gates a hc _ hcw hW hL) (fun b ⟨b1, b2, b3, b4, b5, b6, b7⟩ n1 hn1 => ?_))
  have bcw : C.cw.drop b.cp = listWord Interfaces.intWord Cc.coeffs ++ (listWord bitWord Cc.table ++ rest) := by
    rw [b3, ← List.drop_drop, hcw, List.drop_left, List.append_assoc]
  refine Hs.then (pc2_spec Cc.coeffs b b6 _ bcw hW hL) (fun d ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9⟩ n2 hn2 => ?_)
  have dcw : C.cw.drop d.cp = listWord bitWord Cc.table ++ rest := by
    rw [d5, ← List.drop_drop, bcw, List.drop_left]
  refine Hs.last (pc3_spec Cc.table d d8 _ dcw hW hL) (fun e ⟨e1, e2, e3, e4, e5, e6, e7⟩ n3 hn3 => ?_)
  refine ⟨⟨⟨?_, ?_, ?_, e2, e1, ?_, ?_, ?_⟩, ?_, by rw [e4, d6, b4], by rw [e5, d7, b5], e6,
    Fr.trans (Fr.weaken b7 (by decide)) (Fr.trans (Fr.weaken d9 (by decide)) (Fr.weaken e7 (by decide)))⟩, ?_⟩
  · rw [e7 cG (by decide), d9 cG (by decide), b2]
  · rw [e7 cC (by decide), d3]
  · rw [e7 cTW (by decide), d2]; rfl
  · rw [e7 cWOK (by decide), d9 cWOK (by decide), b1]
  · rw [e7 cNZ (by decide), d1]
  · rw [e7 cCO (by decide), d4, b3]
  · rw [e3, d5, b3, hcwd]; simp only [List.length_append]; ring
  · unfold circCost
    have h1 : (C.cw.length + 2) ^ 2 ≤ (C.cw.length + 2) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
    have h0 : 1 ≤ (C.cw.length + 2) ^ 3 := Nat.one_le_pow _ _ (by omega)
    omega

end NearCubicGates.Close.Dispatch
