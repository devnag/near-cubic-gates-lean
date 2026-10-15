import Proof.Gates.Cells.Forms3

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.Cells

open NearCubicWires NearCubicGates
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter
open NearCubicGates.Close.CounterMachine (gateN intN)

variable {C : Ctx}

/-! ## Agreement outside given stores and variables -/

structure Agr (a b : DS VV MM) (ms : List (Fin MM)) (T : List (Fin VV)) : Prop where
  ram : ∀ m, m ∉ ms → b.ram m = a.ram m
  rc : ∀ m, m ∉ ms → b.rc m = a.rc m
  ip : b.ip = a.ip
  out : b.out = a.out
  kin : b.kin = a.kin
  kout : b.kout = a.kout
  kc : b.kc = a.kc
  fr : Fr a b T

theorem Agr.refl (a : DS VV MM) (ms : List (Fin MM)) (T : List (Fin VV)) : Agr a a ms T :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl, Fr.refl _ _⟩

theorem Agr.trans {a b d : DS VV MM} {ms : List (Fin MM)} {T : List (Fin VV)} (h1 : Agr a b ms T)
    (h2 : Agr b d ms T) : Agr a d ms T :=
  ⟨fun m hm => (h2.ram m hm).trans (h1.ram m hm), fun m hm => (h2.rc m hm).trans (h1.rc m hm),
    h2.ip.trans h1.ip, h2.out.trans h1.out, h2.kin.trans h1.kin, h2.kout.trans h1.kout, h2.kc.trans h1.kc,
    Fr.trans h1.fr h2.fr⟩

theorem Agr.weaken {a b : DS VV MM} {ms ms' : List (Fin MM)} {T T' : List (Fin VV)} (h : Agr a b ms T)
    (hm : ∀ m ∈ ms, m ∈ ms') (hT : ∀ y ∈ T, y ∈ T') : Agr a b ms' T' :=
  ⟨fun m h' => h.ram m (fun h'' => h' (hm m h'')), fun m h' => h.rc m (fun h'' => h' (hm m h'')), h.ip, h.out,
    h.kin, h.kout, h.kc, Fr.weaken h.fr hT⟩

theorem Agr.set (a : DS VV MM) (ms : List (Fin MM)) {x : Fin VV} (v : ℕ) {T : List (Fin VV)} (hx : x ∈ T) :
    Agr a (a.set x v) ms T :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl, Fr.set a v hx⟩

theorem Agr.rew (a : DS VV MM) {m : Fin MM} {ms : List (Fin MM)} (hm : m ∈ ms) (T : List (Fin VV)) :
    Agr a (a.rew m) ms T := by
  refine ⟨fun _ _ => rfl, fun m' hm' => ?_, rfl, rfl, rfl, rfl, rfl, Fr.refl _ _⟩
  have : m' ≠ m := fun e => hm' (e ▸ hm)
  simp [DS.rew, Function.update_of_ne this]

theorem Agr.of_seek {a b : DS VV MM} {m : Fin MM} {ms : List (Fin MM)} {T : List (Fin VV)} {v : ℕ} (hm : m ∈ ms)
    (hT : c0 ∈ T ∧ vJ ∈ T)
    (h : b.ram = a.ram ∧ b.rc = Function.update a.rc m v ∧ b.ip = a.ip ∧ b.out = a.out ∧ b.kin = a.kin ∧
      b.kout = a.kout ∧ b.kc = a.kc ∧ Fr a b [c0, vJ]) : Agr a b ms T := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  refine ⟨fun m' _ => by rw [h1], fun m' hm' => ?_, h3, h4, h5, h6, h7, Fr.weaken h8 (by simp [hT.1, hT.2])⟩
  have : m' ≠ m := fun e => hm' (e ▸ hm)
  rw [h2, Function.update_of_ne this]

/-! ## Part 1: the gate bits of the role -/

def xGS : Fin VV := ⟨50, by decide⟩
def xG : Fin VV := ⟨51, by decide⟩
def xCS : Fin VV := ⟨52, by decide⟩
def xNC : Fin VV := ⟨53, by decide⟩
def xWS : Fin VV := ⟨54, by decide⟩
def xFS : Fin VV := ⟨55, by decide⟩
def xP : Fin VV := ⟨64, by decide⟩
def xN : Fin VV := ⟨65, by decide⟩

def gatesPart : St VV MM := .seq (seekP sN xGS) (.seq (.op (.copy gG xG)) (.seq (.op (.rwM sB)) gatesP))

def gatesPartT : List (Fin VV) := [c0, vJ, gG, c4, c3, gS0, gS1, gZ, gPos, gNeg]

theorem gatesPart_spec {n : ℕ} (a : DS VV MM) (hc : Cst a) (hn : a.env gN = n) (hnW : n < 2 ^ C.Wd)
    (gs : List (NormalizedThresholdGate n)) (R : List ℕ)
    (hGS : (a.ram sN).drop (a.env xGS) = gs.flatMap gateN ++ R) (hGSl : a.env xGS ≤ (a.ram sN).length)
    (hGSW : a.env xGS < 2 ^ C.Wd) (hG : a.env xG = gs.length) (hGW : gs.length < 2 ^ C.Wd)
    (zb : List ℕ) (hzb : a.ram sZb = zb) (hzl : zb.length = n) (hz0 : a.rc sZb = 0)
    (hW : ∀ g ∈ gs, ((List.ofFn g.weight).map Int.natAbs).sum + g.threshold.natAbs < 2 ^ C.Wd) :
    Hs C gatesPart a (a.rc sN + 5 * a.env xGS + a.rc sB + gs.length * (15 * n + 28) + 16) (fun b =>
      b.ram sB = gs.map (gbit · zb) ++ (a.ram sB).drop gs.length ∧ b.rc sB = gs.length ∧
      b.rc sN = a.env xGS + gs.length * (2 * n + 3) ∧ b.ram sN = a.ram sN ∧ Agr a b [sN, sB] gatesPartT) := by
  have hsb : sN ≠ sB := by decide
  refine Hs.mono (Hs.seq (seekP_spec sN xGS (by decide) (by decide) a hGSl hGSW) (fun e1 he1 => ?_))
    (show a.rc sN + 5 * a.env xGS + 6 + (1 + (a.rc sB + 1 + (gs.length * (15 * n + 24 + 4) + 4) + 1) + 1) + 1 ≤ _
      by ring_nf; omega) (fun _ h => h)
  have ag1 : Agr a e1 [sN, sB] gatesPartT := Agr.of_seek (m := sN) (by simp) (by simp [gatesPartT]) he1
  obtain ⟨h1, h2, -, -, -, -, -, h8⟩ := he1
  refine Hs.seq (hs_copy C gG xG e1 (by decide)) (fun e2 he2 => ?_)
  subst he2
  have ag2 : Agr a (e1.set gG (e1.env xG)) [sN, sB] gatesPartT := ag1.trans (Agr.set _ _ _ (by simp [gatesPartT]))
  have e1B : e1.rc sB = a.rc sB := by rw [h2, Function.update_of_ne (Ne.symm hsb)]
  refine Hs.seq (t1 := a.rc sB + 1) (Hs.mono (hs_rwM C sB _) (by simp [e1B]) (fun _ h => h)) (fun e3 he3 => ?_)
  subst he3
  set e3 := (e1.set gG (e1.env xG)).rew sB with he3
  have ag3 : Agr a e3 [sN, sB] gatesPartT := ag2.trans (Agr.rew _ (by simp) _)
  have e3c : Cst e3 := Cst.of_fr hc ag3.fr (by decide)
  have e3n : e3.env gN = n := by rw [ag3.fr gN (by decide)]; exact hn
  have e3G : e3.env gG = gs.length := by simp only [he3, DS.rew]; vsimp [h8 xG (by decide), hG]
  have e3N : (e3.ram sN).drop (e3.rc sN) = gs.flatMap gateN ++ R := by
    simp only [he3, DS.rew, DS.set_ram, DS.set_rc]; rw [Function.update_of_ne hsb, h2, Function.update_self, h1, hGS]
  have e3Z : e3.ram sZb = zb := by rw [ag3.ram sZb (by decide), hzb]
  have e3Zc : e3.rc sZb = 0 := by rw [ag3.rc sZb (by decide), hz0]
  have e3B : e3.rc sB = 0 := by simp [he3, DS.rew]
  refine Hs.mono (gatesP_spec (C := C) e3 e3c e3n hnW gs e3G hGW R e3N zb e3Z hzl e3Zc e3B hW) le_rfl ?_
  rintro b ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩
  have e3Bram : e3.ram sB = a.ram sB := by simp [he3, DS.rew, h1]
  have e3Nc : e3.rc sN = a.env xGS := by
    simp only [he3, DS.rew, DS.set_rc]; rw [Function.update_of_ne hsb, h2, Function.update_self]
  refine ⟨by rw [b1, Function.update_self, e3Bram], by rw [b2, Function.update_self], ?_, ?_, ?_⟩
  · rw [b2, Function.update_of_ne hsb, Function.update_self, e3Nc]
  · rw [b1, Function.update_of_ne hsb]; simp [he3, DS.rew, h1]
  · refine ag3.trans ⟨fun m hm => ?_, fun m hm => ?_, b3, b4, b5, b6, b7, Fr.weaken b8 (by decide)⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hm
      rw [b1, Function.update_of_ne hm.2]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hm
      rw [b2, Function.update_of_ne hm.2, Function.update_of_ne hm.1]

/-! ## Budget-passing sequencing -/

theorem Hs.bseq {s u : St VV MM} {a : DS VV MM} {t t1 : ℕ} {R1 R2 : DS VV MM → Prop} (h1 : Hs C s a t1 R1)
    (ht : t1 + 1 ≤ t) (h2 : ∀ b, R1 b → Hs C u b (t - t1 - 1) R2) : Hs C (.seq s u) a t R2 :=
  Hs.mono (Hs.seq h1 h2) (by omega) (fun _ h => h)

theorem Agr.of_fr_same {a b : DS VV MM} {ms : List (Fin MM)} {T T' : List (Fin VV)} (hT : ∀ y ∈ T, y ∈ T')
    (h : b.ram = a.ram ∧ b.rc = a.rc ∧ b.ip = a.ip ∧ b.out = a.out ∧ b.kin = a.kin ∧ b.kout = a.kout ∧
      b.kc = a.kc ∧ Fr a b T) : Agr a b ms T' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨fun m _ => by rw [h1], fun m _ => by rw [h2], h3, h4, h5, h6, h7, Fr.weaken h8 hT⟩

/-! ## Part 2: the score of the role -/

def scorePart : St VV MM :=
  .seq (seekP sN xCS) (.seq (.op (.copy fL xNC)) (.seq (.op (.zero gPos)) (.seq (.op (.zero gNeg))
  (.seq (.op (.rwM sB)) (.seq linP (.seq (normP gPos gNeg) (.seq (.op (.copy xP gPos)) (.seq (.op (.copy xN gNeg))
    (.op (.rwM sB))))))))))

def spT : List (Fin VV) := [c0, vJ, fL, gPos, gNeg, c3, gS0, gS1, gZ, xP, xN]

theorem scorePart_spec (a : DS VV MM) (hc : Cst a) (cs : List ℤ) (R : List ℕ)
    (hCS : (a.ram sN).drop (a.env xCS) = cs.flatMap intN ++ R) (hCSl : a.env xCS ≤ (a.ram sN).length)
    (hCSW : a.env xCS < 2 ^ C.Wd) (hNC : a.env xNC = cs.length) (hNCW : cs.length < 2 ^ C.Wd)
    (zb Z : List ℕ) (hsB : a.ram sB = zb ++ Z) (hzl : zb.length = cs.length)
    (hB : (cs.map Int.natAbs).sum < 2 ^ C.Wd) :
    Hs C scorePart a (a.rc sN + 5 * a.env xCS + a.rc sB + 15 * cs.length + 40) (fun b =>
      [b.env xP, b.env xN] = pairOf ((posPart cs zb : ℤ) - negPart cs zb) ∧
      b.rc sB = 0 ∧ b.rc sN = a.env xCS + 2 * cs.length ∧ b.ram sN = a.ram sN ∧ b.ram sB = a.ram sB ∧
      Agr a b [sN, sB] spT) := by
  have hsb : sN ≠ sB := by decide
  set L := cs.length with hL
  refine Hs.bseq (seekP_spec sN xCS (by decide) (by decide) a hCSl hCSW) (by omega) (fun e1 he1 => ?_)
  have ag1 : Agr a e1 [sN, sB] spT := Agr.of_seek (m := sN) (by simp) (by simp [spT]) he1
  obtain ⟨h1, h2, -, -, -, -, -, h8⟩ := he1
  refine Hs.bseq (hs_copy C fL xNC e1 (by decide)) (by omega) (fun e2 he2 => ?_)
  subst he2
  refine Hs.bseq (hs_zero C gPos _) (by omega) (fun e3 he3 => ?_)
  subst he3
  refine Hs.bseq (hs_zero C gNeg _) (by omega) (fun e4 he4 => ?_)
  subst he4
  set e4 := ((e1.set fL (e1.env xNC)).set gPos 0).set gNeg 0 with he4
  have ag4 : Agr a e4 [sN, sB] spT :=
    ag1.trans ((Agr.set _ _ _ (by simp [spT])).trans ((Agr.set _ _ _ (by simp [spT])).trans
      (Agr.set _ _ _ (by simp [spT]))))
  have e4B : e4.rc sB = a.rc sB := by simp only [he4, DS.set_rc]; rw [h2, Function.update_of_ne (Ne.symm hsb)]
  refine Hs.bseq (Hs.mono (hs_rwM C sB e4) (show e4.rc sB + 1 ≤ a.rc sB + 1 by rw [e4B]) (fun _ h => h))
    (by omega) (fun e5 he5 => ?_)
  subst he5
  have ag5 : Agr a (e4.rew sB) [sN, sB] spT := ag4.trans (Agr.rew _ (by simp) _)
  have e5c : Cst (e4.rew sB) := Cst.of_fr hc ag5.fr (by decide)
  have e5L : (e4.rew sB).env fL = L := by simp only [he4, DS.rew]; vsimp [h8 xNC (by decide), hNC]
  have e5N : ((e4.rew sB).ram sN).drop ((e4.rew sB).rc sN) = cs.flatMap intN ++ R := by
    simp only [he4, DS.rew, DS.set_ram, DS.set_rc]; rw [Function.update_of_ne hsb, h2, Function.update_self, h1, hCS]
  have e5B : (e4.rew sB).ram sB = zb ++ Z := by simp only [he4, DS.rew, DS.set_ram]; rw [h1, hsB]
  have e5B0 : (e4.rew sB).rc sB = 0 := by simp [DS.rew]
  have e5p : (e4.rew sB).env gPos = 0 := by simp only [he4, DS.rew]; vsimp []
  have e5n : (e4.rew sB).env gNeg = 0 := by simp only [he4, DS.rew]; vsimp []
  refine Hs.bseq (linP_spec (C := C) (e4.rew sB) e5c L e5L hNCW cs rfl R e5N zb Z e5B hzl e5B0 e5p e5n hB)
    (by omega) (fun e6 he6 => ?_)
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10⟩ := he6
  have ag6 : Agr a e6 [sN, sB] spT := ag5.trans ⟨fun m hm => by rw [l4], fun m hm => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hm
    rw [l3, Function.update_of_ne hm.2, Function.update_of_ne hm.1], l5, l6, l7, l8, l9,
    Fr.weaken l10 (by decide)⟩
  refine Hs.bseq (normP_spec gPos gNeg (by decide) e6) (by omega) (fun e7 he7 => ?_)
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9⟩ := he7
  have ag7 : Agr a e7 [sN, sB] spT := ag6.trans (Agr.of_fr_same (by decide) ⟨n4, n5, n2, n3, n6, n7, n8, n9⟩)
  refine Hs.bseq (hs_copy C xP gPos e7 (by decide)) (by omega) (fun e8 he8 => ?_)
  subst he8
  refine Hs.bseq (hs_copy C xN gNeg _ (by decide)) (by omega) (fun e9 he9 => ?_)
  subst he9
  set e9 := (e7.set xP (e7.env gPos)).set xN ((e7.set xP (e7.env gPos)).env gNeg) with he9
  have ag9 : Agr a e9 [sN, sB] spT :=
    ag7.trans ((Agr.set _ _ _ (by simp [spT])).trans (Agr.set _ _ _ (by simp [spT])))
  have e9B : e9.rc sB = L := by simp only [he9, DS.set_rc]; rw [n5, l3, Function.update_self]
  refine Hs.mono (Hs.mono (hs_rwM C sB e9) (show e9.rc sB + 1 ≤ L + 1 by rw [e9B]) (fun _ h => h)) (by omega) ?_
  rintro b rfl
  have hxP : e9.env xP = e7.env gPos := by simp only [he9]; vsimp []
  have hxN : e9.env xN = e7.env gNeg := by simp only [he9]; vsimp []
  have hP : [e7.env gPos, e7.env gNeg] = pairOf ((posPart cs zb : ℤ) - negPart cs zb) := by rw [n1, l1, l2]
  refine ⟨by simp only [DS.rew]; rw [hxP, hxN]; exact hP, by simp [DS.rew], ?_, ?_, ?_,
    ag9.trans (Agr.rew _ (by simp) _)⟩
  · simp only [DS.rew]; rw [Function.update_of_ne hsb]
    simp only [he9, DS.set_rc]; rw [n5, l3, Function.update_of_ne hsb, Function.update_self]
    simp only [he4, DS.rew, DS.set_rc]; rw [Function.update_of_ne hsb, h2, Function.update_self]
  · simp only [DS.rew, he9, DS.set_ram]; rw [n4, l4]; simp only [he4, DS.rew, DS.set_ram]; rw [h1]
  · simp only [DS.rew, he9, DS.set_ram]; rw [n4, l4]; simp only [he4, DS.rew, DS.set_ram]; rw [h1]

end NearCubicGates.Close.Cells
