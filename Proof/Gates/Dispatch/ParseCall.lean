import Proof.Gates.Dispatch.ParseCirc
import Proof.Gates.Dispatch.Arith

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxRecDepth 4000

namespace NearCubicGates.Close.Dispatch

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Interfaces

variable {C : Ctx}

def vN : Fin VV := ⟨30, by decide⟩
def vTAG : Fin VV := ⟨31, by decide⟩
def vG1 : Fin VV := ⟨32, by decide⟩
def vC1 : Fin VV := ⟨33, by decide⟩
def vTW1 : Fin VV := ⟨34, by decide⟩
def vT1 : Fin VV := ⟨35, by decide⟩
def vTB1 : Fin VV := ⟨36, by decide⟩
def vWOK1 : Fin VV := ⟨37, by decide⟩
def vNZ1 : Fin VV := ⟨38, by decide⟩
def vCO1 : Fin VV := ⟨39, by decide⟩
def vG2 : Fin VV := ⟨40, by decide⟩
def vC2 : Fin VV := ⟨41, by decide⟩
def vTW2 : Fin VV := ⟨42, by decide⟩
def vT2 : Fin VV := ⟨43, by decide⟩
def vTB2 : Fin VV := ⟨44, by decide⟩
def vWOK2 : Fin VV := ⟨45, by decide⟩
def vNZ2 : Fin VV := ⟨46, by decide⟩
def vCO2 : Fin VV := ⟨47, by decide⟩
def vPL : Fin VV := ⟨48, by decide⟩
def vPP : Fin VV := ⟨49, by decide⟩
def vPOK : Fin VV := ⟨50, by decide⟩
def vSG : Fin VV := ⟨51, by decide⟩
def vNUM : Fin VV := ⟨52, by decide⟩
def vDEN : Fin VV := ⟨53, by decide⟩
def vRL : Fin VV := ⟨54, by decide⟩
def vCL : Fin VV := ⟨55, by decide⟩

/-! ## The head: `n`, the tag, `B₀` -/

def pHead : St VV :=
  .seq readNat (.seq (.op (.copy vN t3)) (.seq readNat (.seq (.op (.copy vTAG t3))
  (.seq (.op (.copy t3 vN)) (.seq (.op (.inc t3)) (.seq clog2 (.seq (.op (.copy t9 t5))
  (.seq (setK t7 4) (.seq (.op (.mul t7 vN t8)) (.op (.mul t8 t9 vB0)))))))))))

def headT : List (Fin VV) := [t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, vJ, vPOS, vN, vTAG, vB0]

theorem pHead_spec (c : Call) (a : DS VV) (hc : Cst a) (rest : List Bool)
    (hcw : C.cw.drop a.cp = natWord c.n ++ natWord (kindTag c.kind) ++ rest) (hW : 2 * C.cw.length + 8 ≤ C.Wd)
    (hL : C.cw.length + 2 < 2 ^ C.Wd) :
    Hs C pHead a (100 * C.cw.length + 200) (fun b => b.env vN = c.n ∧ b.env vTAG = kindTag c.kind ∧
      b.env vB0 = Call.B0 c.n ∧ b.cp = a.cp + (natWord c.n).length + (natWord (kindTag c.kind)).length ∧
      b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧ Fr a b headT) := by
  set L := C.cw.length
  have hlen := len_le_of_drop hcw
  simp only [List.length_append] at hlen
  rw [List.append_assoc] at hcw
  have hn1 := natBitLength_le_len c.n
  have hn2 := natBitLength_le_len (kindTag c.kind)
  have hnL : c.n < 2 ^ L := lt_of_lt_of_le (lt_natBitLength c.n) (Nat.pow_le_pow_right (by norm_num) (by omega))
  have h2L : 2 ^ (L + 4) ≤ 2 ^ C.Wd := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hpL : 2 ^ (L + 4) = 16 * 2 ^ L := by ring
  refine Hx.hs (Hs.then (readNat_spec a hc c.n _ hcw (by omega) hL) (fun b ⟨b1, b2, b3, b4, b5, b6, b7⟩ n1 hn1' => ?_))
  refine Hs.then (hs_copy C vN t3 b (by decide)) (fun b' hb' n2 hn2' => ?_)
  subst hb'
  have bcw : C.cw.drop (b.set vN (b.env t3)).cp = natWord (kindTag c.kind) ++ rest := by
    show C.cw.drop b.cp = _; rw [b3, ← List.drop_drop, hcw, List.drop_left]
  have bc : Cst (b.set vN (b.env t3)) := Cst.of_fr (T := [vN]) b6 (Fr.set b _ (by decide)) (by decide)
    (by vsimp [b6.pos])
  refine Hs.then (readNat_spec _ bc (kindTag c.kind) _ bcw (by omega) hL)
    (fun d ⟨d1, d2, d3, d4, d5, d6, d7⟩ n3 hn3 => ?_)
  refine Hs.then (hs_copy C vTAG t3 d (by decide)) (fun e1 he1 n4 hn4 => ?_)
  have e1N : e1.env vN = c.n := by rw [he1]; vsimp [d7 vN (by decide), b1]
  have e1T : e1.env vTAG = kindTag c.kind := by rw [he1]; vsimp [d1]
  have e1c : Cst e1 := by
    rw [he1]; exact Cst.of_fr (T := [vTAG]) d6 (Fr.set _ _ (by decide)) (by decide) (by vsimp [d6.pos])
  have e1F : Fr a e1 headT := by
    rw [he1]
    exact Fr.trans (Fr.weaken b7 (by decide)) (Fr.trans (Fr.set b _ (by decide)) (Fr.trans
      (Fr.weaken d7 (by decide)) (Fr.set _ _ (by decide))))
  have e1cp : e1.cp = a.cp + (natWord c.n).length + (natWord (kindTag c.kind)).length := by
    rw [he1]; show d.cp = _; rw [d3]; show b.cp + _ = _; rw [b3]
  have e1wq : e1.wq = a.wq := by rw [he1]; show d.wq = _; rw [d4]; show b.wq = _; rw [b4]
  have e1out : e1.out = a.out := by rw [he1]; show d.out = _; rw [d5]; show b.out = _; rw [b5]
  refine Hs.then (hs_copy C t3 vN e1 (by decide)) (fun e2 he2 n5 hn5 => ?_)
  refine Hs.then (hs_inc C t3 e2 (by rw [he2]; vsimp [e1N]; omega)) (fun e3 he3 n6 hn6 => ?_)
  have e3t3 : e3.env t3 = c.n + 1 := by rw [he3, he2]; vsimp [e1N]
  have e3F : Fr e1 e3 [t3] := by rw [he3, he2]; exact Fr.trans (Fr.set _ _ (by decide)) (Fr.set _ _ (by decide))
  have e3c : Cst e3 := Cst.of_fr e1c e3F (by decide) (by rw [he3, he2]; vsimp [e1c.pos])
  refine Hs.then (clog2_spec e3 e3c (by rw [e3t3]; omega)) (fun g ⟨g1, g2, g3, g4, g5, g6, g7⟩ n7 hn7 => ?_)
  rw [e3t3] at g1 hn7
  have hcl : Nat.clog 2 (c.n + 1) ≤ L + 1 := by
    apply Nat.clog_le_of_le_pow
    have : 2 ^ L < 2 ^ (L + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  refine Hs.then (hs_copy C t9 t5 g (by decide)) (fun g1' hg1 n8 hn8 => ?_)
  have g1t9 : g1'.env t9 = Nat.clog 2 (c.n + 1) := by rw [hg1]; vsimp [g1]
  have g1c : Cst g1' := by
    rw [hg1]; exact Cst.of_fr (T := [t9]) g6 (Fr.set _ _ (by decide)) (by decide) (by vsimp [g6.pos])
  refine Hs.then (setK_spec t7 (by decide) 4 g1' (by have := Nat.lt_two_pow_self (n := C.Wd); omega))
    (fun h1 ⟨h1a, h1b, h1c, h1d, h1e⟩ n9 hn9 => ?_)
  have h1N : h1.env vN = c.n := by
    rw [h1e vN (by decide), hg1]; vsimp [g7 vN (by decide), e3F vN (by decide), e1N]
  have h1t9 : h1.env t9 = Nat.clog 2 (c.n + 1) := by rw [h1e t9 (by decide), g1t9]
  refine Hs.then (hs_mul C t7 vN t8 h1 (by decide) (by decide) (by decide) (by rw [h1a, h1N]; omega))
    (fun h2 hh2 n10 hn10 => ?_)
  have h2t8 : h2.env t8 = 4 * c.n := by rw [hh2]; vsimp [h1a, h1N]
  have h2t9 : h2.env t9 = Nat.clog 2 (c.n + 1) := by rw [hh2]; vsimp [h1t9]
  have hprod : 4 * c.n * Nat.clog 2 (c.n + 1) < 2 ^ C.Wd := by
    have h4 : L + 1 < 2 ^ (L + 1) := Nat.lt_two_pow_self
    calc 4 * c.n * Nat.clog 2 (c.n + 1) ≤ 4 * c.n * (L + 1) := Nat.mul_le_mul_left _ hcl
      _ ≤ 4 * 2 ^ L * 2 ^ (L + 1) := Nat.mul_le_mul (Nat.mul_le_mul_left _ hnL.le) h4.le
      _ = 2 ^ (2 * L + 3) := by ring
      _ < 2 ^ C.Wd := Nat.pow_lt_pow_right (by norm_num) (by omega)
  refine Hs.last (hs_mul C t8 t9 vB0 h2 (by decide) (by decide) (by decide) (by rw [h2t8, h2t9]; exact hprod))
    (fun h3 hh3 n11 hn11 => ?_)
  have hF : Fr a h3 headT := by
    rw [hh3, hh2]
    exact Fr.trans e1F (Fr.trans (Fr.weaken e3F (by decide)) (Fr.trans (Fr.weaken g7 (by decide))
      (Fr.trans (by rw [hg1]; exact Fr.set _ _ (by decide)) (Fr.trans (Fr.weaken h1e (by decide))
        (Fr.trans (Fr.set _ _ (by decide)) (Fr.set _ _ (by decide)))))))
  have hcp : h3.cp = e1.cp := by
    rw [hh3, hh2]; show h1.cp = _; rw [h1b, hg1]; show g.cp = _; rw [g3, he3, he2]; rfl
  have h1c' : Cst h1 := Cst.of_fr g1c h1e (by decide) (by rw [h1e vPOS (by decide), h1b]; exact g1c.pos)
  have h2c : Cst h2 := by
    rw [hh2]; exact Cst.of_fr (T := [t8]) h1c' (Fr.set _ _ (by decide)) (by decide) (by vsimp [h1c'.pos])
  have h3c : Cst h3 := by
    rw [hh3]; exact Cst.of_fr (T := [vB0]) h2c (Fr.set _ _ (by decide)) (by decide) (by vsimp [h2c.pos])
  refine ⟨⟨by rw [hh3, hh2]; vsimp [h1N], ?_, ?_, by rw [hcp, e1cp], ?_, ?_, h3c, hF⟩, ?_⟩
  · rw [hh3, hh2]; vsimp [h1e vTAG (by decide), hg1, g7 vTAG (by decide), e3F vTAG (by decide), e1T]
  · rw [hh3]; vsimp [h2t8, h2t9, Call.B0]
  · rw [hh3, hh2]; show h1.wq = _; rw [h1c, hg1]; show g.wq = _; rw [g4, he3, he2]; exact e1wq
  · rw [hh3, hh2]; show h1.out = _; rw [h1d, hg1]; show g.out = _; rw [g5, he3, he2]; exact e1out
  · have hA : natBitLength c.n + natBitLength (kindTag c.kind) ≤ L := by omega
    have hD : n7 ≤ 5 * (L + 1) + 6 := by omega
    clear * - hA hD hn1' hn2' hn3 hn4 hn5 hn6 hn8 hn9 hn10 hn11
    omega

/-! ## Saving one circuit's results -/

def save1 : St VV :=
  .seq (.op (.copy vG1 cG)) (.seq (.op (.copy vC1 cC)) (.seq (.op (.copy vTW1 cTW)) (.seq (.op (.copy vT1 cT))
  (.seq (.op (.copy vTB1 cTB)) (.seq (.op (.copy vWOK1 cWOK)) (.seq (.op (.copy vNZ1 cNZ)) (.op (.copy vCO1 cCO))))))))

theorem save1_spec (a : DS VV) (hc : Cst a) :
    Hs C save1 a 15 (fun b => b.env vG1 = a.env cG ∧ b.env vC1 = a.env cC ∧ b.env vTW1 = a.env cTW ∧
      b.env vT1 = a.env cT ∧ b.env vTB1 = a.env cTB ∧ b.env vWOK1 = a.env cWOK ∧ b.env vNZ1 = a.env cNZ ∧
      b.env vCO1 = a.env cCO ∧ b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧
      Fr a b [vG1, vC1, vTW1, vT1, vTB1, vWOK1, vNZ1, vCO1]) := by
  refine Hx.hs (Hs.then (hs_copy C vG1 cG a (by decide)) (fun b1 h1 n1 hn1 => ?_))
  subst h1
  refine Hs.then (hs_copy C vC1 cC _ (by decide)) (fun b2 h2 n2 hn2 => ?_)
  subst h2
  refine Hs.then (hs_copy C vTW1 cTW _ (by decide)) (fun b3 h3 n3 hn3 => ?_)
  subst h3
  refine Hs.then (hs_copy C vT1 cT _ (by decide)) (fun b4 h4 n4 hn4 => ?_)
  subst h4
  refine Hs.then (hs_copy C vTB1 cTB _ (by decide)) (fun b5 h5 n5 hn5 => ?_)
  subst h5
  refine Hs.then (hs_copy C vWOK1 cWOK _ (by decide)) (fun b6 h6 n6 hn6 => ?_)
  subst h6
  refine Hs.then (hs_copy C vNZ1 cNZ _ (by decide)) (fun b7 h7 n7 hn7 => ?_)
  subst h7
  refine Hs.last (hs_copy C vCO1 cCO _ (by decide)) (fun b8 h8 n8 hn8 => ?_)
  subst h8
  refine ⟨⟨by vsimp [], by vsimp [], by vsimp [], by vsimp [], by vsimp [], by vsimp [], by vsimp [], by vsimp [],
    rfl, rfl, rfl, ?_, ?_⟩, by omega⟩
  · exact ⟨by vsimp [hc.z], by vsimp [hc.one], by vsimp [hc.two], by vsimp [hc.pos]⟩
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    vsimp [Function.update_of_ne hy.1, Function.update_of_ne hy.2.1, Function.update_of_ne hy.2.2.1,
      Function.update_of_ne hy.2.2.2.1, Function.update_of_ne hy.2.2.2.2.1, Function.update_of_ne hy.2.2.2.2.2.1,
      Function.update_of_ne hy.2.2.2.2.2.2.1, Function.update_of_ne hy.2.2.2.2.2.2.2]

def save2 : St VV :=
  .seq (.op (.copy vG2 cG)) (.seq (.op (.copy vC2 cC)) (.seq (.op (.copy vTW2 cTW)) (.seq (.op (.copy vT2 cT))
  (.seq (.op (.copy vTB2 cTB)) (.seq (.op (.copy vWOK2 cWOK)) (.seq (.op (.copy vNZ2 cNZ)) (.op (.copy vCO2 cCO))))))))

theorem save2_spec (a : DS VV) (hc : Cst a) :
    Hs C save2 a 15 (fun b => b.env vG2 = a.env cG ∧ b.env vC2 = a.env cC ∧ b.env vTW2 = a.env cTW ∧
      b.env vT2 = a.env cT ∧ b.env vTB2 = a.env cTB ∧ b.env vWOK2 = a.env cWOK ∧ b.env vNZ2 = a.env cNZ ∧
      b.env vCO2 = a.env cCO ∧ b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧
      Fr a b [vG2, vC2, vTW2, vT2, vTB2, vWOK2, vNZ2, vCO2]) := by
  refine Hx.hs (Hs.then (hs_copy C vG2 cG a (by decide)) (fun b1 h1 n1 hn1 => ?_))
  subst h1
  refine Hs.then (hs_copy C vC2 cC _ (by decide)) (fun b2 h2 n2 hn2 => ?_)
  subst h2
  refine Hs.then (hs_copy C vTW2 cTW _ (by decide)) (fun b3 h3 n3 hn3 => ?_)
  subst h3
  refine Hs.then (hs_copy C vT2 cT _ (by decide)) (fun b4 h4 n4 hn4 => ?_)
  subst h4
  refine Hs.then (hs_copy C vTB2 cTB _ (by decide)) (fun b5 h5 n5 hn5 => ?_)
  subst h5
  refine Hs.then (hs_copy C vWOK2 cWOK _ (by decide)) (fun b6 h6 n6 hn6 => ?_)
  subst h6
  refine Hs.then (hs_copy C vNZ2 cNZ _ (by decide)) (fun b7 h7 n7 hn7 => ?_)
  subst h7
  refine Hs.last (hs_copy C vCO2 cCO _ (by decide)) (fun b8 h8 n8 hn8 => ?_)
  subst h8
  refine ⟨⟨by vsimp [], by vsimp [], by vsimp [], by vsimp [], by vsimp [], by vsimp [], by vsimp [], by vsimp [],
    rfl, rfl, rfl, ?_, ?_⟩, by omega⟩
  · exact ⟨by vsimp [hc.z], by vsimp [hc.one], by vsimp [hc.two], by vsimp [hc.pos]⟩
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    vsimp [Function.update_of_ne hy.1, Function.update_of_ne hy.2.1, Function.update_of_ne hy.2.2.1,
      Function.update_of_ne hy.2.2.2.1, Function.update_of_ne hy.2.2.2.2.1, Function.update_of_ne hy.2.2.2.2.2.1,
      Function.update_of_ne hy.2.2.2.2.2.2.1, Function.update_of_ne hy.2.2.2.2.2.2.2]

/-! ## The parity list -/

def pBody : St VV := .seq readNat (.ite (.lt t3 vN) skipS (.op (.zero vPOK)))

def pPar : St VV :=
  .seq readNat (.seq (.op (.copy vPL t3)) (.seq (.op (.copy vPP vPOS)) (.seq (.op (.copy vPOK v1))
    (.seq (.op (.zero ci)) (.loop (.lt ci vPL) (.seq pBody (.op (.inc ci))))))))

def parT : List (Fin VV) := [t0, t1, t2, t3, t4, vJ, vPOS, vPL, vPP, vPOK, ci]

theorem pBody_spec (a : DS VV) (hc : Cst a) (v n : ℕ) (rest : List Bool) (f : Prop) [Decidable f]
    (hf : a.env vPOK = bnat f) (hn : a.env vN = n) (hcw : C.cw.drop a.cp = natWord v ++ rest)
    (hW : C.cw.length + 2 ≤ C.Wd) (hL : C.cw.length + 2 < 2 ^ C.Wd) :
    Hs C pBody a (30 * C.cw.length + 40) (fun b => b.env vPOK = bnat (f ∧ v < n) ∧
      b.cp = a.cp + (natWord v).length ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧ Fr a b [t0, t1, t2, t3, t4, vJ, vPOS, vPOK]) := by
  have hl := len_le_of_drop hcw
  have hnb := natBitLength_le_len v
  refine Hx.hs (Hs.then (readNat_spec a hc v rest hcw (by omega) hL) (fun b ⟨b1, b2, b3, b4, b5, b6, b7⟩ n1 hn1 => ?_))
  have bN : b.env vN = n := by rw [b7 vN (by decide), hn]
  have bP : b.env vPOK = bnat f := by rw [b7 vPOK (by decide), hf]
  have step : Hs C (.ite (.lt t3 vN) skipS (.op (.zero vPOK))) b 2 (fun d => d.env vPOK = bnat (f ∧ v < n) ∧
      d.cp = b.cp ∧ d.wq = b.wq ∧ d.out = b.out ∧ Fr b d [vPOK, vJ]) := by
    refine Hs.ite (c := .lt t3 vN) (show t3 ≠ vN by decide) (fun he => ?_) (fun he => ?_)
    · have hlt : v < n := by simp only [Cnd.eval, decide_eq_true_eq, bN, b1] at he; exact he
      refine Hs.mono (skip_spec b) le_rfl ?_
      rintro d rfl
      exact ⟨by vsimp [bP, bnat, hlt], rfl, rfl, rfl, Fr.set b _ (by decide)⟩
    · have hlt : ¬ v < n := by simp only [Cnd.eval, decide_eq_false_iff_not, bN, b1] at he; exact he
      refine Hs.mono (hs_zero C vPOK b) le_rfl ?_
      rintro d rfl
      exact ⟨by vsimp [bnat, hlt], rfl, rfl, rfl, Fr.set b _ (by decide)⟩
  refine Hs.last step (fun d ⟨d1, d2, d3, d4, d5⟩ n2 hn2 => ⟨⟨d1, by rw [d2, b3], by rw [d3, b4], by rw [d4, b5],
    Cst.of_fr (T := [vPOK, vJ]) b6 d5 (by decide) (by rw [d5 vPOS (by decide), b6.pos, d2]),
    Fr.trans (Fr.weaken b7 (by decide)) (Fr.weaken d5 (by decide))⟩, by omega⟩)

theorem pPar_spec (par : List ℕ) (n : ℕ) (a : DS VV) (hc : Cst a) (hn : a.env vN = n) (rest : List Bool)
    (hcw : C.cw.drop a.cp = listWord natWord par ++ rest) (hW : C.cw.length + 2 ≤ C.Wd)
    (hL : C.cw.length + 2 < 2 ^ C.Wd) :
    Hs C pPar a (40 * (C.cw.length + 2) ^ 2) (fun b => b.env vPL = par.length ∧
      b.env vPP = a.cp + (natWord par.length).length ∧ b.env vPOK = bnat (∀ i ∈ par, i < n) ∧
      b.cp = a.cp + (listWord natWord par).length ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧ Fr a b parT) := by
  set L := C.cw.length
  have hlen := len_le_of_drop hcw
  simp only [listWord, List.length_append] at hlen
  simp only [listWord, List.append_assoc] at hcw
  have hpL : par.length ≤ L := by
    have := length_le_flatMap par natWord (fun v => by rw [natWord_length]; omega); omega
  have hnb := natBitLength_le_len par.length
  refine Hx.hs (Hs.then (readNat_spec a hc par.length _ hcw (by omega) hL)
    (fun b ⟨b1, b2, b3, b4, b5, b6, b7⟩ n1 hn1 => ?_))
  refine Hs.then (hs_copy C vPL t3 b (by decide)) (fun b' hb' n2 hn2 => ?_)
  subst hb'
  refine Hs.then (hs_copy C vPP vPOS _ (by decide)) (fun b'' hb'' n3 hn3 => ?_)
  subst hb''
  refine Hs.then (hs_copy C vPOK v1 _ (by decide)) (fun b3' hb3 n4 hn4 => ?_)
  subst hb3
  refine Hs.then (hs_zero C ci _) (fun d hd n5 hn5 => ?_)
  subst hd
  set d := (((b.set vPL (b.env t3)).set vPP ((b.set vPL (b.env t3)).env vPOS)).set vPOK
    (((b.set vPL (b.env t3)).set vPP ((b.set vPL (b.env t3)).env vPOS)).env v1)).set ci 0 with hd
  have dcw : C.cw.drop d.cp = par.flatMap natWord ++ rest := by
    show C.cw.drop b.cp = _
    rw [b3, ← List.drop_drop, hcw, List.drop_left]
  have dT : Fr a d parT := Fr.trans (Fr.weaken b7 (by decide)) (Fr.trans (Fr.set b _ (by decide))
    (Fr.trans (Fr.set _ _ (by decide)) (Fr.trans (Fr.set _ _ (by decide)) (Fr.set _ _ (by decide)))))
  have dc : Cst d := Cst.of_fr hc dT (by decide) (by vsimp [hd, b6.pos])
  let P : ℕ → DS VV → Prop := fun k e => e.env vPOK = bnat (∀ i ∈ par.take k, i < n) ∧ e.env vN = n ∧
    e.env vPP = a.cp + (natWord par.length).length ∧ e.wq = a.wq ∧ e.out = a.out ∧ Cst e ∧ Fr a e parT
  have hP : ∀ k e v, P k e → P k (e.set ci v) := by
    rintro k e v ⟨p1, p2, p3, p4, p5, p6, p7⟩
    exact ⟨by vsimp [p1], by vsimp [p2], by vsimp [p3], p4, p5, Cst.of_fr (T := [ci]) p6 (Fr.set e _ (by decide))
      (by decide) (by vsimp [p6.pos]), Fr.trans p7 (Fr.set e _ (by decide))⟩
  have l := walk (C := C) par natWord ci vPL (by decide) pBody P (30 * L + 40) rest hP
    (by
      intro k hk e ⟨p1, p2, p3, p4, p5, p6, p7⟩ hi hl hd'
      refine Hs.mono (pBody_spec e p6 par[k] n _ _ p1 p2 hd' hW hL) le_rfl ?_
      rintro r ⟨r1, r2, r3, r4, r5, r6⟩
      refine ⟨⟨?_, by rw [r6 vN (by decide), p2], by rw [r6 vPP (by decide), p3], by rw [r3, p4], by rw [r4, p5],
        r5, Fr.trans p7 (Fr.weaken r6 (by decide))⟩, by rw [r6 ci (by decide), hi], by rw [r6 vPL (by decide), hl], r2⟩
      rw [r1]; unfold bnat; congr 1; exact decide_eq_decide.mpr (take_succ_iff par (· < n) k hk))
    (by omega) d
    ⟨by vsimp [hd, hc.one, b7 v1 (by decide), bnat], by vsimp [hd, b7 vN (by decide), hn],
      by vsimp [hd, b6.pos, b3], by vsimp [hd, b4], by vsimp [hd, b5], dc, dT⟩ (by vsimp [hd]) (by vsimp [hd, b1]) dcw
  refine Hs.last l (fun e ⟨⟨p1, p2, p3, p4, p5, p6, p7⟩, e2, e3, e4⟩ n6 hn6 => ?_)
  rw [List.take_length] at p1
  refine ⟨⟨e3, p3, p1, ?_, p4, p5, p6, p7⟩, ?_⟩
  · rw [e4]; show b.cp + _ = _
    rw [b3]; simp only [listWord, List.length_append]; ring
  · have hb1 : n1 ≤ 30 * L + 30 := by omega
    have hp : par.length * (30 * L + 40 + 2 + 2) ≤ L * (30 * L + 44) := Nat.mul_le_mul_right _ hpL
    have e2' : L * (30 * L + 44) = 30 * (L * L) + 44 * L := by ring
    have e3' : 40 * (L + 2) ^ 2 = 40 * (L * L) + 160 * L + 160 := by ring
    omega

/-! ## The radius -/

def pRad : St VV :=
  .seq readNat (.seq (.op (.copy vSG t3)) (.seq (.op (.copy vRL t4)) (.seq readNat (.seq (.op (.copy vNUM t3))
  (.seq (.op (.add vRL t4)) (.seq readNat (.seq (.op (.copy vDEN t3)) (.seq (.op (.add vRL t4))
    (.op (.copy vCL vPOS))))))))))

def radT : List (Fin VV) := [t0, t1, t2, t3, t4, vJ, vPOS, vSG, vRL, vNUM, vDEN, vCL]

theorem pRad_spec (q : ℚ) (a : DS VV) (hc : Cst a) (rest : List Bool)
    (hcw : C.cw.drop a.cp = ratWord q ++ rest) (hW : C.cw.length + 2 ≤ C.Wd) (hL : C.cw.length + 2 < 2 ^ C.Wd) :
    Hs C pRad a (100 * C.cw.length + 120) (fun b => b.env vSG = (if q.num < 0 then 1 else 0) ∧
      b.env vNUM = q.num.natAbs ∧ b.env vDEN = q.den ∧
      b.env vRL = natBitLength (if q.num < 0 then 1 else 0) + natBitLength q.num.natAbs + natBitLength q.den ∧
      b.env vCL = a.cp + (ratWord q).length ∧ b.cp = a.cp + (ratWord q).length ∧ b.wq = a.wq ∧ b.out = a.out ∧
      Cst b ∧ Fr a b radT) := by
  set L := C.cw.length
  have hq : ratWord q = natWord (if q.num < 0 then 1 else 0) ++ (natWord q.num.natAbs ++ natWord q.den) := by
    simp [ratWord, Interfaces.intWord, List.append_assoc]
  rw [hq] at hcw
  have hlen := len_le_of_drop hcw
  simp only [List.length_append] at hlen
  simp only [List.append_assoc] at hcw
  have hb1 := natBitLength_le_len (if q.num < 0 then 1 else 0)
  have hb2 := natBitLength_le_len q.num.natAbs
  have hb3 := natBitLength_le_len q.den
  have hLW : L < 2 ^ C.Wd := by omega
  refine Hx.hs (Hs.then (readNat_spec a hc _ _ hcw (by omega) hL) (fun b ⟨b1, b2, b3, b4, b5, b6, b7⟩ n1 hn1 => ?_))
  refine Hs.then (hs_copy C vSG t3 b (by decide)) (fun b' hb' n2 hn2 => ?_)
  subst hb'
  refine Hs.then (hs_copy C vRL t4 _ (by decide)) (fun b'' hb'' n3 hn3 => ?_)
  subst hb''
  set d := (b.set vSG (b.env t3)).set vRL ((b.set vSG (b.env t3)).env t4) with hd
  have dcw : C.cw.drop d.cp = natWord q.num.natAbs ++ (natWord q.den ++ rest) := by
    show C.cw.drop b.cp = _; rw [b3, ← List.drop_drop, hcw, List.drop_left]
  have dc : Cst d := Cst.of_fr (T := [vSG, vRL]) b6 (Fr.trans (Fr.set _ _ (by decide)) (Fr.set _ _ (by decide)))
    (by decide) (by vsimp [hd, b6.pos])
  refine Hs.then (readNat_spec d dc _ _ dcw (by omega) hL) (fun e ⟨e1, e2, e3, e4, e5, e6, e7⟩ n4 hn4 => ?_)
  refine Hs.then (hs_copy C vNUM t3 e (by decide)) (fun e' he' n5 hn5 => ?_)
  subst he'
  have dRL : d.env vRL = natBitLength (if q.num < 0 then 1 else 0) := by
    rw [hd, DS.set_env_self]; rw [DS.set_env_ne _ _ (by decide), b2]
  have eRL0 : e.env vRL = natBitLength (if q.num < 0 then 1 else 0) := by rw [e7 vRL (by decide), dRL]
  have eRL : (e.set vNUM (e.env t3)).env vRL = natBitLength (if q.num < 0 then 1 else 0) := by
    rw [DS.set_env_ne _ _ (by decide), eRL0]
  have et4 : (e.set vNUM (e.env t3)).env t4 = natBitLength q.num.natAbs := by
    rw [DS.set_env_ne _ _ (by decide), e2]
  refine Hs.then (hs_add C vRL t4 _ (by decide) (by rw [eRL, et4]; omega)) (fun f hf n6 hn6 => ?_)
  subst hf
  set g := ((e.set vNUM (e.env t3)).set vRL ((e.set vNUM (e.env t3)).env vRL + (e.set vNUM (e.env t3)).env t4))
    with hg
  have gcw : C.cw.drop g.cp = natWord q.den ++ rest := by
    show C.cw.drop e.cp = _; rw [e3, ← List.drop_drop, dcw, List.drop_left]
  have gc : Cst g := Cst.of_fr (T := [vNUM, vRL]) e6 (Fr.trans (Fr.set _ _ (by decide)) (Fr.set _ _ (by decide)))
    (by decide) (by vsimp [hg, e6.pos])
  refine Hs.then (readNat_spec g gc _ _ gcw (by omega) hL) (fun h ⟨h1, h2, h3, h4, h5, h6, h7⟩ n7 hn7 => ?_)
  refine Hs.then (hs_copy C vDEN t3 h (by decide)) (fun h' hh' n8 hn8 => ?_)
  subst hh'
  have gRL : g.env vRL = natBitLength (if q.num < 0 then 1 else 0) + natBitLength q.num.natAbs := by
    rw [hg, DS.set_env_self, eRL, et4]
  have hRL : (h.set vDEN (h.env t3)).env vRL = natBitLength (if q.num < 0 then 1 else 0) +
      natBitLength q.num.natAbs := by
    rw [DS.set_env_ne _ _ (by decide), h7 vRL (by decide), gRL]
  have ht4 : (h.set vDEN (h.env t3)).env t4 = natBitLength q.den := by rw [DS.set_env_ne _ _ (by decide), h2]
  refine Hs.then (hs_add C vRL t4 _ (by decide) (by rw [hRL, ht4]; omega)) (fun k hk n9 hn9 => ?_)
  subst hk
  refine Hs.last (hs_copy C vCL vPOS _ (by decide)) (fun r hr n10 hn10 => ?_)
  subst hr
  have hcp : h.cp = a.cp + (ratWord q).length := by
    rw [h3]; show e.cp + _ = _; rw [e3]; show b.cp + _ + _ = _; rw [b3, hq]; simp only [List.length_append]; ring
  have hSG : h.env vSG = (if q.num < 0 then 1 else 0) := by
    rw [h7 vSG (by decide), hg, DS.set_env_ne _ _ (by decide), DS.set_env_ne _ _ (by decide), e7 vSG (by decide), hd,
      DS.set_env_ne _ _ (by decide), DS.set_env_self, b1]
  have hNUM : h.env vNUM = q.num.natAbs := by
    rw [h7 vNUM (by decide), hg, DS.set_env_ne _ _ (by decide), DS.set_env_self, e1]
  have hwq : h.wq = a.wq := by rw [h4]; show e.wq = _; rw [e4]; show b.wq = _; rw [b4]
  have hout : h.out = a.out := by rw [h5]; show e.out = _; rw [e5]; show b.out = _; rw [b5]
  refine ⟨⟨by vsimp [hSG], by vsimp [hNUM], by vsimp [h1],
    by rw [DS.set_env_ne _ _ (by decide), DS.set_env_self, hRL, ht4], by vsimp [h6.pos, hcp], hcp, hwq,
    hout, ?_, ?_⟩, ?_⟩
  · exact Cst.of_fr (T := [vDEN, vRL, vCL]) h6 (Fr.trans (Fr.set _ _ (by decide)) (Fr.trans (Fr.set _ _ (by decide))
      (Fr.set _ _ (by decide)))) (by decide) (by vsimp [h6.pos])
  · exact Fr.trans (Fr.weaken b7 (by decide)) (Fr.trans (Fr.trans (Fr.set _ _ (by decide)) (Fr.set _ _ (by decide)))
      (Fr.trans (Fr.weaken e7 (by decide)) (Fr.trans (Fr.trans (Fr.set _ _ (by decide)) (Fr.set _ _ (by decide)))
        (Fr.trans (Fr.weaken h7 (by decide)) (Fr.trans (Fr.set _ _ (by decide)) (Fr.trans (Fr.set _ _ (by decide))
          (Fr.set _ _ (by decide))))))))
  · omega

/-! ## The whole call word -/

def parseA : St VV := .seq pHead (.seq parseCirc save1)
def parseB : St VV := .seq parseCirc (.seq save2 (.seq pPar pRad))
def parseCall : St VV := .seq parseA parseB

/-- One circuit's values on eight variables. -/
structure CircV {n : ℕ} (Cc : NCircuit n) (B p : ℕ) (g c tw t tb wok nz co : Fin VV) (b : DS VV) : Prop where
  g : b.env g = Cc.gates.length
  c : b.env c = Cc.coeffs.length
  tw : b.env tw = Cc.topWeight
  t : b.env t = Cc.table.length
  tb : b.env tb = (Cc.table.getD 0 false).toNat
  wok : b.env wok = bnat (∀ g ∈ Cc.gates, GateOK B g)
  nz : b.env nz = bnat (∀ x ∈ Cc.coeffs, x ≠ 0)
  co : b.env co = p + (listWord gateWord Cc.gates).length

/-- Cursor positions of the pieces of `callWord c`. -/
def pos1 (c : Call) : ℕ := (natWord c.n).length + (natWord (kindTag c.kind)).length
def pos2 (c : Call) : ℕ := pos1 c + (circuitWord c.first).length
def pos3 (c : Call) : ℕ := pos2 c + (circuitWord c.second).length

structure ParseOut (c : Call) (b : DS VV) : Prop where
  n : b.env vN = c.n
  tag : b.env vTAG = kindTag c.kind
  b0 : b.env vB0 = Call.B0 c.n
  c1 : CircV c.first (Call.B0 c.n) (pos1 c) vG1 vC1 vTW1 vT1 vTB1 vWOK1 vNZ1 vCO1 b
  c2 : CircV c.second (Call.B0 c.n) (pos2 c) vG2 vC2 vTW2 vT2 vTB2 vWOK2 vNZ2 vCO2 b
  pl : b.env vPL = c.parity.length
  pp : b.env vPP = pos3 c + (natWord c.parity.length).length
  pok : b.env vPOK = bnat (∀ i ∈ c.parity, i < c.n)
  sg : b.env vSG = (if c.radius.num < 0 then 1 else 0)
  num : b.env vNUM = c.radius.num.natAbs
  den : b.env vDEN = c.radius.den
  rl : b.env vRL = natBitLength (if c.radius.num < 0 then 1 else 0) + natBitLength c.radius.num.natAbs +
    natBitLength c.radius.den
  cl : b.env vCL = (callWord c).length

def parseT : List (Fin VV) := headT ++ parseCircT ++ [vG1, vC1, vTW1, vT1, vTB1, vWOK1, vNZ1, vCO1, vG2, vC2, vTW2,
  vT2, vTB2, vWOK2, vNZ2, vCO2] ++ parT ++ radT

def parseCost (L : ℕ) : ℕ := 1500 * (L + 2) ^ 3

theorem callWord_eq (c : Call) : callWord c = natWord c.n ++ natWord (kindTag c.kind) ++ (circuitWord c.first ++
    (circuitWord c.second ++ (listWord natWord c.parity ++ ratWord c.radius))) := by
  simp [callWord, List.append_assoc]

def parseAT : List (Fin VV) := headT ++ parseCircT ++ [vG1, vC1, vTW1, vT1, vTB1, vWOK1, vNZ1, vCO1]
def parseBT : List (Fin VV) := parseCircT ++ [vG2, vC2, vTW2, vT2, vTB2, vWOK2, vNZ2, vCO2] ++ parT ++ radT

theorem parseA_spec (c : Call) (a : DS VV) (hc : Cst a) (hcp : a.cp = 0) (hcw : C.cw = callWord c)
    (hW : 2 * C.cw.length + 8 ≤ C.Wd) (hL : C.cw.length + 2 < 2 ^ C.Wd) :
    Hs C parseA a (100 * C.cw.length + 216 + circCost C.cw.length + 1) (fun b => b.env vN = c.n ∧
      b.env vTAG = kindTag c.kind ∧ b.env vB0 = Call.B0 c.n ∧
      CircV c.first (Call.B0 c.n) (pos1 c) vG1 vC1 vTW1 vT1 vTB1 vWOK1 vNZ1 vCO1 b ∧
      b.cp = pos2 c ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧ Fr a b parseAT) := by
  have h0 : C.cw.drop a.cp = natWord c.n ++ natWord (kindTag c.kind) ++ (circuitWord c.first ++
      (circuitWord c.second ++ (listWord natWord c.parity ++ ratWord c.radius))) := by
    rw [hcp, List.drop_zero, hcw, callWord_eq]
  refine Hx.hs (Hs.then (pHead_spec c a hc _ h0 hW hL) (fun b ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩ n1 hn1 => ?_))
  have bcw : C.cw.drop b.cp = circuitWord c.first ++ (circuitWord c.second ++ (listWord natWord c.parity ++
      ratWord c.radius)) := by
    rw [show b.cp = a.cp + (natWord c.n ++ natWord (kindTag c.kind)).length by rw [b4, List.length_append]; ring]
    exact drop_adv h0
  refine Hs.then (parseCirc_spec c.first b b7 _ bcw (by omega) hL) (fun d ⟨d1, d2, d3, d4, d5, d6⟩ n2 hn2 => ?_)
  refine Hs.last (save1_spec d d5) (fun e ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13⟩ n3 hn3 => ?_)
  have pb : b.cp = pos1 c := by rw [b4, hcp, Nat.zero_add]; rfl
  rw [b3, pb] at d1
  have ed : ∀ x, x ∉ [vG1, vC1, vTW1, vT1, vTB1, vWOK1, vNZ1, vCO1] → e.env x = d.env x := fun x h => e13 x h
  have db : ∀ x, x ∉ parseCircT → d.env x = b.env x := fun x h => d6 x h
  refine ⟨⟨by rw [ed vN (by decide), db vN (by decide), b1], by rw [ed vTAG (by decide), db vTAG (by decide), b2],
    by rw [ed vB0 (by decide), db vB0 (by decide), b3],
    ⟨by rw [e1, d1.g], by rw [e2, d1.c], by rw [e3, d1.tw], by rw [e4, d1.t], by rw [e5, d1.tb], by rw [e6, d1.wok],
      by rw [e7, d1.nz], by rw [e8, d1.co]⟩, by rw [e9, d2, pb]; rfl, by rw [e10, d3, b5], by rw [e11, d4, b6], e12,
    Fr.trans (Fr.weaken b8 (by decide)) (Fr.trans (Fr.weaken d6 (by decide)) (Fr.weaken e13 (by decide)))⟩, ?_⟩
  omega

theorem parseB_spec (c : Call) (a : DS VV) (hc : Cst a) (hcp : a.cp = pos2 c) (hcw : C.cw = callWord c)
    (hN : a.env vN = c.n) (hW : 2 * C.cw.length + 8 ≤ C.Wd) (hL : C.cw.length + 2 < 2 ^ C.Wd) :
    Hs C parseB a (circCost C.cw.length + 15 + 40 * (C.cw.length + 2) ^ 2 + 100 * C.cw.length + 120 + 3)
      (fun b => CircV c.second (a.env vB0) (pos2 c) vG2 vC2 vTW2 vT2 vTB2 vWOK2 vNZ2 vCO2 b ∧
      b.env vPL = c.parity.length ∧ b.env vPP = pos3 c + (natWord c.parity.length).length ∧
      b.env vPOK = bnat (∀ i ∈ c.parity, i < c.n) ∧ b.env vSG = (if c.radius.num < 0 then 1 else 0) ∧
      b.env vNUM = c.radius.num.natAbs ∧ b.env vDEN = c.radius.den ∧
      b.env vRL = natBitLength (if c.radius.num < 0 then 1 else 0) + natBitLength c.radius.num.natAbs +
        natBitLength c.radius.den ∧ b.env vCL = (callWord c).length ∧
      b.cp = (callWord c).length ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧ Fr a b parseBT) := by
  have ecw : C.cw.drop a.cp = circuitWord c.second ++ (listWord natWord c.parity ++ ratWord c.radius) := by
    have hd : C.cw.drop 0 = (natWord c.n ++ natWord (kindTag c.kind) ++ circuitWord c.first) ++
        (circuitWord c.second ++ (listWord natWord c.parity ++ ratWord c.radius)) := by
      rw [List.drop_zero, hcw, callWord_eq]; simp only [List.append_assoc]
    rw [hcp, show pos2 c = 0 + (natWord c.n ++ natWord (kindTag c.kind) ++ circuitWord c.first).length by
      simp only [pos2, pos1, List.length_append]; ring]
    exact drop_adv hd
  refine Hx.hs (Hs.then (parseCirc_spec c.second a hc _ ecw (by omega) hL) (fun f ⟨f1, f2, f3, f4, f5, f6⟩ n4 hn4 => ?_))
  refine Hs.then (save2_spec f f5) (fun g ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13⟩ n5 hn5 => ?_)
  have gcw : C.cw.drop g.cp = listWord natWord c.parity ++ ratWord c.radius := by
    rw [g9, f2, ← List.drop_drop, ecw, List.drop_left]
  have gN : g.env vN = c.n := by rw [g13 vN (by decide), f6 vN (by decide), hN]
  refine Hs.then (pPar_spec c.parity c.n g g12 gN _ gcw (by omega) hL)
    (fun h ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ n6 hn6 => ?_)
  have hcw' : C.cw.drop h.cp = ratWord c.radius ++ [] := by
    rw [h4, ← List.drop_drop, gcw, List.drop_left, List.append_nil]
  refine Hs.last (pRad_spec c.radius h h7 [] hcw' (by omega) hL)
    (fun r ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10⟩ n7 hn7 => ?_)
  have pg : g.cp = pos3 c := by rw [g9, f2, hcp]; rfl
  have pr : r.cp = (callWord c).length := by
    rw [r6, h4, pg, callWord_eq]; simp only [pos3, pos2, pos1, List.length_append]; ring
  have rh : ∀ x, x ∉ parT → x ∉ radT → r.env x = g.env x := fun x h1 h2 => by rw [r10 x h2, h8 x h1]
  rw [hcp] at f1
  refine ⟨⟨⟨by rw [rh vG2 (by decide) (by decide), g1, f1.g], by rw [rh vC2 (by decide) (by decide), g2, f1.c],
    by rw [rh vTW2 (by decide) (by decide), g3, f1.tw], by rw [rh vT2 (by decide) (by decide), g4, f1.t],
    by rw [rh vTB2 (by decide) (by decide), g5, f1.tb], by rw [rh vWOK2 (by decide) (by decide), g6, f1.wok],
    by rw [rh vNZ2 (by decide) (by decide), g7, f1.nz], by rw [rh vCO2 (by decide) (by decide), g8, f1.co]⟩,
    by rw [r10 vPL (by decide), h1], by rw [r10 vPP (by decide), h2, pg], by rw [r10 vPOK (by decide), h3],
    r1, r2, r3, r4, by rw [r5, ← r6, pr], pr, by rw [r7, h5, g10, f3], by rw [r8, h6, g11, f4], r9,
    Fr.trans (Fr.weaken f6 (by decide)) (Fr.trans (Fr.weaken g13 (by decide)) (Fr.trans (Fr.weaken h8 (by decide))
      (Fr.weaken r10 (by decide))))⟩, ?_⟩
  omega

theorem parseT_cover : (∀ y ∈ parseAT, y ∈ parseT) ∧ (∀ y ∈ parseBT, y ∈ parseT) := by decide

theorem parseOut_of (c : Call) (b r : DS VV) (T : ∀ x, x ∉ parseBT → r.env x = b.env x)
    (b1 : b.env vN = c.n) (b2 : b.env vTAG = kindTag c.kind) (b3 : b.env vB0 = Call.B0 c.n)
    (b4 : CircV c.first (Call.B0 c.n) (pos1 c) vG1 vC1 vTW1 vT1 vTB1 vWOK1 vNZ1 vCO1 b)
    (r1 : CircV c.second (b.env vB0) (pos2 c) vG2 vC2 vTW2 vT2 vTB2 vWOK2 vNZ2 vCO2 r)
    (r2 : r.env vPL = c.parity.length) (r3 : r.env vPP = pos3 c + (natWord c.parity.length).length)
    (r4 : r.env vPOK = bnat (∀ i ∈ c.parity, i < c.n)) (r5 : r.env vSG = (if c.radius.num < 0 then 1 else 0))
    (r6 : r.env vNUM = c.radius.num.natAbs) (r7 : r.env vDEN = c.radius.den)
    (r8 : r.env vRL = natBitLength (if c.radius.num < 0 then 1 else 0) + natBitLength c.radius.num.natAbs +
        natBitLength c.radius.den) (r9 : r.env vCL = (callWord c).length) : ParseOut c r := by
  rw [b3] at r1
  exact ⟨by rw [T vN (by decide), b1], by rw [T vTAG (by decide), b2], by rw [T vB0 (by decide), b3],
    ⟨by rw [T vG1 (by decide), b4.g], by rw [T vC1 (by decide), b4.c], by rw [T vTW1 (by decide), b4.tw],
      by rw [T vT1 (by decide), b4.t], by rw [T vTB1 (by decide), b4.tb], by rw [T vWOK1 (by decide), b4.wok],
      by rw [T vNZ1 (by decide), b4.nz], by rw [T vCO1 (by decide), b4.co]⟩, r1, r2, r3, r4, r5, r6, r7, r8, r9⟩

theorem parseCost_ge (L : ℕ) : 100 * L + 216 + circCost L + 1 + (circCost L + 15 + 40 * (L + 2) ^ 2 + 100 * L + 120 + 3)
    + 1 ≤ parseCost L := by
  unfold parseCost circCost
  have hX2 : (L + 2) ^ 2 ≥ L + 4 := by nlinarith
  have hX3 : (L + 2) ^ 3 ≥ 2 * (L + 2) ^ 2 := by
    have : (L + 2) ^ 3 = (L + 2) ^ 2 * (L + 2) := by ring
    rw [this]; nlinarith
  have hX8 : (L + 2) ^ 3 ≥ 8 := by nlinarith
  omega

theorem parseCall_spec (c : Call) (a : DS VV) (hc : Cst a) (hcp : a.cp = 0) (hcw : C.cw = callWord c)
    (hW : 2 * C.cw.length + 8 ≤ C.Wd) (hL : C.cw.length + 2 < 2 ^ C.Wd) :
    Hs C parseCall a (parseCost C.cw.length) (fun b => ParseOut c b ∧ b.cp = (callWord c).length ∧ b.wq = a.wq ∧
      b.out = a.out ∧ Cst b ∧ Fr a b parseT) := by
  refine Hx.hs (Hs.then (parseA_spec c a hc hcp hcw hW hL) (fun b ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ n1 hn1 => ?_))
  refine Hs.last (parseB_spec c b b8 b5 hcw b1 hW hL) (fun r ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13,
    r14⟩ n2 hn2 => ?_)
  exact ⟨⟨parseOut_of c b r (fun x h => r14 x h) b1 b2 b3 b4 r1 r2 r3 r4 r5 r6 r7 r8 r9, r10, by rw [r11, b6],
    by rw [r12, b7], r13, Fr.trans (Fr.weaken b9 parseT_cover.1) (Fr.weaken r14 parseT_cover.2)⟩,
    le_trans (by omega) (parseCost_ge C.cw.length)⟩

end NearCubicGates.Close.Dispatch
