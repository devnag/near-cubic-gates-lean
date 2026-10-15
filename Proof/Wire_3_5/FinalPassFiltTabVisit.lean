import Proof.Wire_3_5.FinalPassFiltTabCopy

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Filt
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.SignedSortKey
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.GF2
open NearCubicWires.WireExponent3_5.Filters

variable (cap : ℕ)

/-- All copies of the vertex: one per digit, until the end marker of `V`. -/
def copies : TProg := .whs qV copyT

/-- The scratch words have the right shapes. -/
def Shaped (y : TSt) : Prop :=
  (∃ n, y.fv = frame (binary y.m n)) ∧ (∃ n, y.fu = frame (binary y.m n)) ∧ (∃ n, y.pw = frame (binary y.m n)) ∧
  (∃ n, y.acc = frame (binary y.m n)) ∧ (∃ n, y.st = frame (binary y.m n)) ∧
  (∃ n, y.kw = frame (binary y.lb n)) ∧ (∃ n, y.bw = frame (binary y.lb n)) ∧
  (∃ E : List Bool, y.ep = frame E ∧ E.length = y.lb + (y.lb - 1))

/-- The words of the copies `j, …, j+n−1`. -/
def copiesOut (p m lb a tv X L j n : ℕ) : List Bool :=
  (List.range' j n).flatMap fun j' => copyWord (coefOf p m lb a tv X (wOf m lb * j') L)

theorem copiesOut_succ (p m lb a tv X L j n : ℕ) :
    copiesOut p m lb a tv X L j (n + 1) =
      copyWord (coefOf p m lb a tv X (wOf m lb * j) L) ++ copiesOut p m lb a tv X L (j + 1) n := by
  simp [copiesOut, List.range'_succ]

theorem copyWord_length (cs : List Bool) : (copyWord cs).length = 2 * cs.length + 2 := by
  simp [copyWord, frame_eq_frameP]

theorem coefOf_length (p m lb a tv X d L : ℕ) : (coefOf p m lb a tv X d L).length = L := by simp [coefOf]

theorem copiesOut_length (p m lb a tv X L j n : ℕ) : (copiesOut p m lb a tv X L j n).length = n * (2 * L + 2) := by
  induction n generalizing j with
  | zero => simp [copiesOut]
  | succ n ih => rw [copiesOut_succ, List.length_append, ih, copyWord_length, coefOf_length]; ring

/-- The cost of the copies. -/
def copiesCost (m lb a L n : ℕ) : ℕ := n * (copyCost m lb a L + 3) + 1

theorem copies_spec (p tv r X : ℕ) (restV : List Bool) (hrest : ∃ t, restV = false :: t) :
    ∀ (n j : ℕ) (y : TSt), y.vw = frameP (binary r X) ++ restV → y.vh = 2 * (wOf y.m y.lb * j) →
      r = wOf y.m y.lb * (j + n) → 1 ≤ y.m → 1 ≤ y.lb → y.a ≤ y.lb → Shaped y →
      y.tauw = frame (binary y.m tv) → y.pmw = frame (binary y.m p) →
      y.f = 0 → y.ns = 0 → y.tf = 0 → y.s = 0 → y.j = 0 → y.eph = 0 → y.bwh = 0 → y.ck = 0 →
      2 * r + 4 * y.lb + 2 * y.m + y.L + 10 ≤ cap → y.ow.length + n * (2 * y.L + 2) + 4 < cap →
      ∃ z : TSt, WExec cap copies y.w z.w (copiesCost y.m y.lb y.a y.L n) ∧ Shaped z ∧
        z = { y with vh := 2 * r, ow := y.ow ++ copiesOut p y.m y.lb y.a tv X y.L j n,
                     fv := z.fv, fu := z.fu, pw := z.pw, acc := z.acc, st := z.st, kw := z.kw, bw := z.bw,
                     ep := z.ep }
  | 0, j, y, hV, hvh, hr, _, _, _, hsh, _, _, _, _, _, _, _, _, _, _, _, _ => by
    refine ⟨y, ?_, hsh, ?_⟩
    · refine WExec.mono (WExec.whsF ?_) (by unfold copiesCost; omega)
      obtain ⟨t, rfl⟩ := hrest
      show readTapeBit y.vw y.vh = false
      simp only [Nat.add_zero] at hr
      rw [hV, hvh, ← hr, show 2 * r = (frameP (binary r X)).length by simp [frameP_length]]
      exact readTapeBit_mid _ _ _
    · cases y
      simp only at hvh hr ⊢
      subst hr
      simp [copiesOut, ← hvh]
  | n + 1, j, y, hV, hvh, hr, hm, hlb, ha, hsh, htau, hpm, hf, hns, htf, hs, hj, heph, hbwh, hck, hcap, hO => by
    obtain ⟨⟨fv0, hfv⟩, ⟨fu0, hfu⟩, ⟨pw0, hpw⟩, ⟨a0, hacc⟩, ⟨s0, hst⟩, ⟨kw0, hkw⟩, ⟨bw0, hbw⟩, ⟨E, hep, hE⟩⟩ := hsh
    have hdr : wOf y.m y.lb * j + wOf y.m y.lb ≤ r := by rw [hr]; ring_nf; omega
    obtain ⟨a1, s1, h1⟩ := copyT_spec cap y r X (wOf y.m y.lb * j) p tv fv0 fu0 pw0 a0 s0 kw0 bw0 E restV hV hvh hdr hm
      hlb ha hfv hfu hpw hacc hst hkw hbw hep hE htau hpm hf hns htf hs hj heph hbwh hck
      (by omega) (by nlinarith)
    have hread : wbit y.w qV = true := by
      show readTapeBit y.vw y.vh = true
      rw [hV, hvh]
      have hlt : wOf y.m y.lb * j < (binary r X).length := by
        simp only [binary_length]; have : 1 ≤ wOf y.m y.lb := by unfold wOf; omega
        nlinarith
      rw [readTapeBit_frameP_marker _ _ _ hlt]
    obtain ⟨Y1, hY1⟩ : ∃ z : TSt, z =
        { y with vh := 2 * (wOf y.m y.lb * j + wOf y.m y.lb),
                 ow := y.ow ++ copyWord (coefOf p y.m y.lb y.a tv X (wOf y.m y.lb * j) y.L),
                 fv := frame (binary y.m (X / 2 ^ (wOf y.m y.lb * j) % 2 ^ y.m)),
                 fu := frame (binary y.m (X / 2 ^ (wOf y.m y.lb * j + y.m) % 2 ^ y.m)),
                 pw := frame (binary y.m (powN p y.m (X / 2 ^ (wOf y.m y.lb * j) % 2 ^ y.m) y.L)),
                 acc := frame (binary y.m a1), st := frame (binary y.m s1), kw := frame (binary y.lb y.L),
                 bw := frame (binary y.lb (X / 2 ^ (wOf y.m y.lb * j + 2 * y.m))),
                 ep := frame (epOf y.lb X (wOf y.m y.lb * j + 2 * y.m + y.lb)) } := ⟨_, rfl⟩
    rw [← hY1] at h1
    have hm1 : Y1.m = y.m := by rw [hY1]
    have hlb1 : Y1.lb = y.lb := by rw [hY1]
    have ha1 : Y1.a = y.a := by rw [hY1]
    have hL1 : Y1.L = y.L := by rw [hY1]
    have hsh1 : Shaped Y1 := by
      rw [hY1]
      exact ⟨⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl, epOf_length _ _ _⟩⟩
    have hvh1 : Y1.vh = 2 * (wOf y.m y.lb * j + wOf y.m y.lb) := by rw [hY1]
    have how1 : Y1.ow = y.ow ++ copyWord (coefOf p y.m y.lb y.a tv X (wOf y.m y.lb * j) y.L) := by rw [hY1]
    obtain ⟨z, hz, hzsh, hzeq⟩ := copies_spec p tv r X restV hrest n (j + 1) Y1 (by rw [hY1]; exact hV)
      (by rw [hvh1, hm1, hlb1]; ring) (by rw [hm1, hlb1, hr]; ring) (by rw [hm1]; exact hm) (by rw [hlb1]; exact hlb)
      (by rw [hlb1, ha1]; exact ha) hsh1 (by rw [hm1, hY1]; exact htau) (by rw [hm1, hY1]; exact hpm)
      (by rw [hY1]; exact hf) (by rw [hY1]; exact hns) (by rw [hY1]; exact htf) (by rw [hY1]; exact hs)
      (by rw [hY1]; exact hj) (by rw [hY1]; exact heph) (by rw [hY1]; exact hbwh) (by rw [hY1]; exact hck)
      (by rw [hlb1, hm1, hL1]; exact hcap)
      (by rw [how1, hL1]; simp only [List.length_append, copyWord_length, coefOf_length]; nlinarith)
    refine ⟨z, WExec.cast cap (WExec.whsT hread h1 hz) rfl ?_, hzsh, ?_⟩
    · rw [hm1, hlb1, ha1, hL1]; unfold copiesCost; nlinarith
    · rw [hzeq, hY1]
      rw [copiesOut_succ]
      cases y
      simp only [List.append_assoc]

/-! ## One visit -/

theorem w_v_rewind (x : TSt) : (x.w.setv gVP 0).seth qV (x.w.sh qV - x.vh) = { x with vh := 0 }.w := by tst_eq

/-- **One visit**: the marker, all copies, the end marker, `V` back to its start. -/
def visitT : TProg := .seq (emitC qO gOP true) (.seq copies (.seq (emitC qO gOP false) (WM.rewind qV gVP)))

/-- The coefficient words of the copies `0, …, n−1` of the vertex word `X`. -/
def copyList (p m lb a tv X L n : ℕ) : List (List Bool) :=
  (List.range n).map fun j => coefOf p m lb a tv X (wOf m lb * j) L

theorem copiesOut_eq (p m lb a tv X L n : ℕ) :
    copiesOut p m lb a tv X L 0 n = (copyList p m lb a tv X L n).flatMap copyWord := by
  simp [copiesOut, copyList, List.range'_eq_map_range, List.flatMap_map]

/-- The cost of one visit. -/
def visitCost (m lb a L n : ℕ) : ℕ := copiesCost m lb a L n + 5 * (2 * (wOf m lb * n)) + 20

theorem visitT_spec (p tv X n : ℕ) (restV : List Bool) (hrest : ∃ t, restV = false :: t) (y : TSt)
    (hV : y.vw = frameP (binary (wOf y.m y.lb * n) X) ++ restV) (hvh : y.vh = 0)
    (hm : 1 ≤ y.m) (hlb : 1 ≤ y.lb) (ha : y.a ≤ y.lb) (hsh : Shaped y)
    (htau : y.tauw = frame (binary y.m tv)) (hpm : y.pmw = frame (binary y.m p))
    (hf : y.f = 0) (hns : y.ns = 0) (htf : y.tf = 0) (hs : y.s = 0) (hj : y.j = 0) (heph : y.eph = 0)
    (hbwh : y.bwh = 0) (hck : y.ck = 0)
    (hcap : 2 * (wOf y.m y.lb * n) + 4 * y.lb + 2 * y.m + y.L + 10 ≤ cap)
    (hO : y.ow.length + n * (2 * y.L + 2) + 8 < cap) :
    ∃ z : TSt, WExec cap visitT y.w z.w (visitCost y.m y.lb y.a y.L n) ∧ Shaped z ∧
      z = { y with ow := y.ow ++ visitWord (copyList p y.m y.lb y.a tv X y.L n),
                   fv := z.fv, fu := z.fu, pw := z.pw, acc := z.acc, st := z.st, kw := z.kw, bw := z.bw,
                   ep := z.ep } := by
  have s1 := emitC_spec cap qO gOP true y.w rfl (by show y.ow.length < cap; omega)
  rw [w_o_emit] at s1
  obtain ⟨x1, hx1⟩ : ∃ z : TSt, z = { y with ow := y.ow ++ [true] } := ⟨_, rfl⟩
  rw [← hx1] at s1
  obtain ⟨z2, h2, hsh2, hz2⟩ := copies_spec cap p tv (wOf y.m y.lb * n) X restV hrest n 0 x1
    (by rw [hx1]; exact hV) (by rw [hx1]; simp [hvh]) (by rw [hx1]; ring) (by rw [hx1]; exact hm)
    (by rw [hx1]; exact hlb) (by rw [hx1]; exact ha) (by rw [hx1]; exact hsh) (by rw [hx1]; exact htau)
    (by rw [hx1]; exact hpm) (by rw [hx1]; exact hf) (by rw [hx1]; exact hns) (by rw [hx1]; exact htf)
    (by rw [hx1]; exact hs) (by rw [hx1]; exact hj) (by rw [hx1]; exact heph) (by rw [hx1]; exact hbwh)
    (by rw [hx1]; exact hck) (by rw [hx1]; exact hcap) (by rw [hx1]; simp; omega)
  have how2 : z2.ow = y.ow ++ [true] ++ copiesOut p y.m y.lb y.a tv X y.L 0 n := by rw [hz2, hx1]
  have s3 := emitC_spec cap qO gOP false z2.w rfl
    (by show z2.ow.length < cap; rw [how2]; simp [copiesOut_length]; omega)
  rw [w_o_emit] at s3
  obtain ⟨x3, hx3⟩ : ∃ z : TSt, z = { z2 with ow := z2.ow ++ [false] } := ⟨_, rfl⟩
  rw [← hx3] at s3
  have hvh3 : x3.vh = 2 * (wOf y.m y.lb * n) := by rw [hx3, hz2]
  have s4 := wrewind_spec cap qV gVP x3.vh x3.w rfl (by show x3.vh ≤ cap; rw [hvh3]; omega)
  rw [w_v_rewind] at s4
  refine ⟨{ x3 with vh := 0 }, WExec.cast cap (WExec.seq s1 (WExec.seq h2 (WExec.seq s3 s4))) rfl ?_, ?_, ?_⟩
  · have hm1 : x1.m = y.m := by rw [hx1]
    have hlb1 : x1.lb = y.lb := by rw [hx1]
    have ha1 : x1.a = y.a := by rw [hx1]
    have hL1 : x1.L = y.L := by rw [hx1]
    rw [hm1, hlb1, ha1, hL1, hvh3]; unfold visitCost; omega
  · rw [hx3]; exact hsh2
  · rw [hx3, hz2, hx1]
    simp only [visitWord, copiesOut_eq, List.append_assoc, List.cons_append, List.nil_append]
    cases y
    simp only at hvh ⊢
    subst hvh
    rfl

/-! ## The coefficient words are the table's -/

theorem binary_eq_map (n y : ℕ) : binary n y = (List.range n).map fun i => y.testBit i := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  have := binary_getD' n y i (by simpa using h1)
  rw [List.getD_eq_getElem _ _ h1] at this
  rw [this]; simp

theorem wOf_seedW (P : GapParams) : wOf P.fieldBits P.labelBits = seedW P := by unfold wOf seedW; omega

theorem epOf_eq (P : GapParams) (X j : ℕ) :
    epOf P.labelBits X (seedW P * j + 2 * P.fieldBits + P.labelBits) = epWord P X j := by
  unfold epOf epWord
  rw [binary_eq_map, binary_eq_map]
  congr 1
  · congr 1
    apply List.map_congr_left
    intro i _
    unfold lowBit
    rw [Nat.testBit_div_two_pow]; congr 1; omega
  · apply List.map_congr_left
    intro i _
    unfold upBit
    rw [Nat.testBit_div_two_pow]; congr 1; omega

theorem not_any_eq_all (l : List ℕ) (f : ℕ → Bool) : (!l.any f) = l.all (fun i => !f i) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.any_cons, List.all_cons, ih]

/-- **The builder's coefficient word is the table's** (`coefBits`, `filterTable_bits`). -/
theorem coefOf_eq (P : GapParams) (X j L : ℕ) :
    coefOf (GF.firstPrimitive P.fieldBits) P.fieldBits P.labelBits P.prefixBits
      (tau (GF.firstPrimitive P.fieldBits) P.fieldBits) X (wOf P.fieldBits P.labelBits * j) L = coefBits P X j L := by
  rw [wOf_seedW]
  unfold coefOf coefBits
  apply List.map_congr_left
  intro k _
  unfold cbit coefBit selB trB mism
  rw [epOf_eq]
  congr 1
  · rw [← List.range_eq_range', not_any_eq_all]
    have e : ∀ i < P.prefixBits,
        (!(xor ((binary P.labelBits (X / 2 ^ (seedW P * j + 2 * P.fieldBits))).getD i false)
          (parW (binary P.labelBits k) (winOf (epWord P X j) P.labelBits i)))) =
        !(xor (transBit P X j i) (parityDot (rowWin P X j i) (binary P.labelBits k))) := by
      intro i hi
      rw [binary_getD' _ _ _ (by have := prefixBits_le P; omega), Nat.testBit_div_two_pow, parW_eq, parityDot_comm]
      unfold transBit
      rw [show i + (seedW P * j + 2 * P.fieldBits) = seedW P * j + 2 * P.fieldBits + i by omega]
      rfl
    apply Bool.eq_iff_iff.mpr
    simp only [List.all_eq_true, List.mem_range]
    constructor
    · intro h i hi; rw [← e i hi]; exact h i hi
    · intro h i hi; rw [e i hi]; exact h i hi
  · rw [parW_eq, parityDot_comm]; rfl

end NearCubicWires.WireExponent3_5.FinalPass.Filt
