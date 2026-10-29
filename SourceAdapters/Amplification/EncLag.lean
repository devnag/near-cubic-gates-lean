import SourceAdapters.Amplification.EncFmul
import SourceAdapters.Amplification.EncRef

/-!
# The Lagrange basis of `H` and the product over the coordinates, in the cell language

STV Lemma 25 (rounded, `app:sources`, "Full-range amplification interface"): the value of the low-degree extension at a point is a sum of products of
Lagrange basis values. Routines (on the globals `Glob g`):

* `lagP`: `GL := lag p t h GV GX = ∏_{w<2^h, w≠v}(x+w) · (∏_{w<2^h, w≠v}(v+w))^{-1}` (`EncRef.lag`);
* `prodP`: `QP := prodAt p t h m QI QC = ∏_{j<m} L_{blk h i j}(zc t c j)` (`EncRef.prodAt`), the coordinates and
  blocks obtained by repeated division by `2^t` and `2^h`.
-/

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Adapters.Amplification.Enc

open NearCubicGates.Close.Cells NearCubicWires.WireExponent3_5

/-! ## The Lagrange basis -/

abbrev vGV : Var := 46
abbrev vGX : Var := 47
abbrev vGL : Var := 48
abbrev vGW : Var := 49
abbrev vGN : Var := 50
abbrev vGD : Var := 51

def lagS : List Var := [vGL, vGW, vGN, vGD, vIA] ++ finvS

def lagAdd : Sc :=
  .seq (.op (.copy vXA vGX)) <| .seq (.op (.copy vXB vGW)) <| .seq xorP <|
  .seq (.op (.copy vMA vGN)) <| .seq (.op (.copy vMB vXR)) <| .seq fmulP <| .seq (.op (.copy vGN vMR)) <|
  .seq (.op (.copy vXA vGV)) <| .seq (.op (.copy vXB vGW)) <| .seq xorP <|
  .seq (.op (.copy vMA vGD)) <| .seq (.op (.copy vMB vXR)) <| .seq fmulP (.op (.copy vGD vMR))

def lagBody : Sc := .seq (.ite (.eq vGW vGV) (.op (.zero vMQ)) lagAdd) (.op (.inc vGW))

def lagP : Sc :=
  .seq (.op (.copy vGN vONE)) <| .seq (.op (.copy vGD vONE)) <| .seq (.op (.zero vGW)) <|
  .seq (.loop (.lt vGW vPOWH) lagBody) <|
  .seq (.op (.copy vIA vGD)) <| .seq finvP <| .seq (.op (.copy vMA vGN)) <| .seq (.op (.copy vMB vIY)) <|
  .seq fmulP (.op (.copy vGL vMR))

def lagBodyCost (t : ℕ) : ℕ := 2 * fmulCost t + 50 * t + 120

def lagCost (t h : ℕ) : ℕ := 2 ^ h * (lagBodyCost t + 2) + finvCost t + fmulCost t + 40

/-- The state of the loop of `lagP` before round `j`. -/
def LagInv (g : Prm) (a0 : Ds) (v x j : ℕ) (b : Ds) : Prop :=
  Fr lagS [] a0 b ∧ b.env vGN = prodFold g.p g.t (fun w => x ^^^ w) v j 1 ∧
    b.env vGD = prodFold g.p g.t (fun w => v ^^^ w) v j 1 ∧ b.env vGW = j ∧ b.env vGN < 2 ^ g.t ∧
    b.env vGD < 2 ^ g.t

theorem lagBody_spec (C : Ctx) (g : Prm) (hw : WOk g C) (hp : GF.ModulusOk g.p g.t) (a0 b : Ds) (hg : Glob g b)
    (v x j : ℕ) (hv : v < 2 ^ g.h) (hx : x < 2 ^ g.t) (hj : j < 2 ^ g.h) (hbv : b.env vGV = v) (hbx : b.env vGX = x)
    (hinv : LagInv g a0 v x j b) : Runs C lagBody b (lagBodyCost g.t) lagS [] (LagInv g a0 v x (j + 1)) := by
  obtain ⟨hf, hN, hD, hW, hNl, hDl⟩ := hinv
  have ht1 : 2 ^ g.t ≤ 2 ^ (g.t + 1) := two_pow_mono (by omega)
  have hht : 2 ^ g.h ≤ 2 ^ g.t := two_pow_mono hw.2.2.1
  have hjW : j + 1 < 2 ^ C.Wd := lt_W hw (by
    have := two_pow_mono (show g.h + 1 ≤ g.L + 3 by have := hw.2.1; have := hw.2.2.1; omega)
    rw [pow_succ] at this; omega)
  have hW2 : g.t + 1 + 2 ≤ C.Wd := by have := hw.1; have := hw.2.1; omega
  have hite : Runs C (.ite (.eq vGW vGV) (.op (.zero vMQ)) lagAdd) b (lagBodyCost g.t - 2) lagS []
      (fun c => c.env vGN = prodFold g.p g.t (fun w => x ^^^ w) v (j + 1) 1 ∧
        c.env vGD = prodFold g.p g.t (fun w => v ^^^ w) v (j + 1) 1 ∧ c.env vGW = j ∧ c.env vGN < 2 ^ g.t ∧
        c.env vGD < 2 ^ g.t) := by
    by_cases hjv : j = v
    · refine Runs.iteT' (by unfold Cnd.wf; decide) (by simp [Cnd.eval, hW, hbv, hjv]) ?_
        (by unfold lagBodyCost; omega)
      refine Runs.last (run_zero C lagS b vMQ (by decide)) ?_ (by unfold lagBodyCost; omega)
      intro _
      norm_env
      rw [prodFold_succ, prodFold_succ, if_pos hjv, if_pos hjv]
      exact ⟨hN, hD, hW, hNl, hDl⟩
    · refine Runs.iteF' (by unfold Cnd.wf; decide) (by simp [Cnd.eval, hW, hbv, hjv]) ?_
        (by unfold lagBodyCost; omega)
      rw [prodFold_succ, prodFold_succ, if_neg hjv, if_neg hjv]
      refine Runs.op1 (run_copy C lagS b vXA vGX (by decide) (by decide)) ?_ (by unfold lagBodyCost; omega)
      refine Runs.op1 (run_copy C lagS _ vXB vGW (by decide) (by decide)) ?_ (by unfold lagBodyCost; omega)
      norm_env
      refine Runs.callS (xorP_spec C _ ⟨by norm_env; exact hg.c.1, by norm_env; exact hg.c.2.1,
          by norm_env; exact hg.c.2.2⟩ (g.t + 1) (by norm_env; exact hg.tb) x j (by norm_env; exact hbx)
          (by norm_env; exact hW) (lt_of_lt_of_le hx ht1) (by omega) hW2) (by decide) ?_
        (by unfold lagBodyCost; omega)
      intro c1 hc1 hc1v
      have hg1 : Glob g c1 := (hg.of_fr (((Fr.refl lagS b).set_right vXA _ (by decide)).set_right vXB _
        (by decide)) (by decide)).of_fr hc1 (by decide)
      refine Runs.op1 (run_copy C lagS _ vMA vGN (by decide) (by decide)) ?_ (by unfold lagBodyCost; omega)
      refine Runs.op1 (run_copy C lagS _ vMB vXR (by decide) (by decide)) ?_ (by unfold lagBodyCost; omega)
      have hc1N : c1.env vGN = prodFold g.p g.t (fun w => x ^^^ w) v j 1 := by
        rw [hc1.env vGN (by decide)]; norm_env; exact hN
      refine Runs.callS (fmulP_spec C g hw hp _ (hg1.of_fr (((Fr.refl lagS c1).set_right vMA _ (by decide)).set_right
          vMB _ (by decide)) (by decide)) _ (x ^^^ j) (by norm_env; exact hc1N) (by norm_env; exact hc1v)
          (by rw [← hc1N]; rw [hc1.env vGN (by decide)]; norm_env; exact hNl)) (by decide) ?_
        (by unfold lagBodyCost; omega)
      rintro c2 hc2 ⟨hc2v, hc2l⟩
      have hg2 : Glob g c2 := (hg1.of_fr (((Fr.refl lagS c1).set_right vMA _ (by decide)).set_right vMB _
        (by decide)) (by decide)).of_fr hc2 (by decide)
      refine Runs.op1 (run_copy C lagS _ vGN vMR (by decide) (by decide)) ?_ (by unfold lagBodyCost; omega)
      refine Runs.op1 (run_copy C lagS _ vXA vGV (by decide) (by decide)) ?_ (by unfold lagBodyCost; omega)
      refine Runs.op1 (run_copy C lagS _ vXB vGW (by decide) (by decide)) ?_ (by unfold lagBodyCost; omega)
      have hc2V : c2.env vGV = v := by
        rw [hc2.env vGV (by decide)]; norm_env; rw [hc1.env vGV (by decide)]; norm_env; exact hbv
      have hc2W : c2.env vGW = j := by
        rw [hc2.env vGW (by decide)]; norm_env; rw [hc1.env vGW (by decide)]; norm_env; exact hW
      have hc2D : c2.env vGD = prodFold g.p g.t (fun w => v ^^^ w) v j 1 := by
        rw [hc2.env vGD (by decide)]; norm_env; rw [hc1.env vGD (by decide)]; norm_env; exact hD
      refine Runs.callS (xorP_spec C _ ⟨by norm_env; exact hg2.c.1, by norm_env; exact hg2.c.2.1,
          by norm_env; exact hg2.c.2.2⟩ (g.t + 1) (by norm_env; exact hg2.tb) v j (by norm_env; exact hc2V)
          (by norm_env; exact hc2W) (by omega) (by omega) hW2) (by decide) ?_
        (by unfold lagBodyCost; omega)
      intro c3 hc3 hc3v
      have hg3 : Glob g c3 := (hg2.of_fr ((((Fr.refl lagS c2).set_right vGN _ (by decide)).set_right vXA _
        (by decide)).set_right vXB _ (by decide)) (by decide)).of_fr hc3 (by decide)
      refine Runs.op1 (run_copy C lagS _ vMA vGD (by decide) (by decide)) ?_ (by unfold lagBodyCost; omega)
      refine Runs.op1 (run_copy C lagS _ vMB vXR (by decide) (by decide)) ?_ (by unfold lagBodyCost; omega)
      have hc3D : c3.env vGD = prodFold g.p g.t (fun w => v ^^^ w) v j 1 := by
        rw [hc3.env vGD (by decide)]; norm_env; exact hc2D
      refine Runs.callS (fmulP_spec C g hw hp _ (hg3.of_fr (((Fr.refl lagS c3).set_right vMA _ (by decide)).set_right
          vMB _ (by decide)) (by decide)) _ (v ^^^ j) (by norm_env; exact hc3D) (by norm_env; exact hc3v)
          (by norm_env; rw [← hD]; exact hDl)) (by decide) ?_
        (by unfold lagBodyCost; omega)
      rintro c4 hc4 ⟨hc4v, hc4l⟩
      refine Runs.last (run_copy C lagS _ vGD vMR (by decide) (by decide)) ?_ (by unfold lagBodyCost; omega)
      intro _
      norm_env
      have hc4N : c4.env vGN = fmul g.p g.t (prodFold g.p g.t (fun w => x ^^^ w) v j 1) (x ^^^ j) := by
        rw [hc4.env vGN (by decide)]; norm_env; rw [hc3.env vGN (by decide)]; norm_env; exact hc2v
      refine ⟨hc4N, hc4v, ?_, ?_, hc4l⟩
      · rw [hc4.env vGW (by decide)]; norm_env; rw [hc3.env vGW (by decide)]; norm_env; exact hc2W
      · rw [hc4N, ← hc2v]; exact hc2l
  refine Runs.call hite ?_ (by unfold lagBodyCost; omega)
  rintro c hc ⟨hcN, hcD, hcW, hcNl, hcDl⟩
  refine Runs.last (run_inc C lagS c vGW (by decide) (by rw [hcW]; exact hjW)) ?_ (by unfold lagBodyCost; omega)
  intro _
  refine ⟨(hf.trans0 hc).set_right _ _ (by decide), ?_, ?_, ?_, ?_, ?_⟩ <;> norm_env
  · exact hcN
  · exact hcD
  · rw [hcW]
  · exact hcNl
  · exact hcDl

theorem lagP_spec (C : Ctx) (g : Prm) (hw : WOk g C) (hp : GF.ModulusOk g.p g.t) (a : Ds) (hg : Glob g a)
    (v x : ℕ) (hv : v < 2 ^ g.h) (hx : x < 2 ^ g.t) (hav : a.env vGV = v) (hax : a.env vGX = x) :
    Runs C lagP a (lagCost g.t g.h) lagS [] (fun b => b.env vGL = lag g.p g.t g.h v x ∧ b.env vGL < 2 ^ g.t) := by
  have hone : 1 < 2 ^ g.t := Nat.one_lt_two_pow (by have := hw.2.2.2.2.2; omega)
  refine Runs.op1 (run_copy C lagS a vGN vONE (by decide) (by decide)) ?_ (by unfold lagCost; omega)
  refine Runs.op1 (run_copy C lagS _ vGD vONE (by decide) (by decide)) ?_ (by unfold lagCost; omega)
  refine Runs.op1 (run_zero C lagS _ vGW (by decide)) ?_ (by unfold lagCost; omega)
  norm_env
  rw [hg.c.2.1]
  have hf0 : Fr lagS [] a (((a.set vGN 1).set vGD 1).set vGW 0) :=
    (((Fr.refl lagS a).set_right _ _ (by decide)).set_right _ _ (by decide)).set_right _ _ (by decide)
  refine Runs.call (Runs.loopN0 (C := C) (c := .lt vGW vPOWH) (body := lagBody) (S := lagS)
    (by unfold Cnd.wf; decide) (2 ^ g.h) (lagBodyCost g.t) (LagInv g a v x) ?step ?stop _ ?init) ?cont
    (by unfold lagCost; omega)
  case init =>
    refine ⟨hf0, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_env <;> simp [prodFold_zero, hone]
  case stop =>
    rintro b ⟨hf, -, -, hW, -, -⟩
    have hgb : Glob g b := hg.of_fr hf (by decide)
    simp [Cnd.eval, hW, hgb.powh]
  case step =>
    rintro j hj b hinv
    have hgb : Glob g b := hg.of_fr hinv.1 (by decide)
    refine ⟨by simp [Cnd.eval, hinv.2.2.2.1, hgb.powh, hj], ?_⟩
    exact lagBody_spec C g hw hp a b hgb v x j hv hx hj ((hinv.1.env vGV (by decide)).trans hav)
      ((hinv.1.env vGX (by decide)).trans hax) hinv
  case cont =>
    rintro b hfb ⟨hf, hN, hD, -, hNl, hDl⟩
    have hgb : Glob g b := hg.of_fr hf (by decide)
    refine Runs.op1 (run_copy C lagS b vIA vGD (by decide) (by decide)) ?_ (by unfold lagCost; omega)
    refine Runs.callS (finvP_spec C g hw hp _ (hgb.of_fr (Fr.set lagS b vIA _ (by decide)) (by decide))
      (b.env vGD) (by norm_env)) (by decide) ?_ (by unfold lagCost; omega)
    rintro c hc ⟨hcv, hcl⟩
    have hgc : Glob g c := (hgb.of_fr (Fr.set lagS b vIA _ (by decide)) (by decide)).of_fr hc (by decide)
    refine Runs.op1 (run_copy C lagS _ vMA vGN (by decide) (by decide)) ?_ (by unfold lagCost; omega)
    refine Runs.op1 (run_copy C lagS _ vMB vIY (by decide) (by decide)) ?_ (by unfold lagCost; omega)
    have hcN : c.env vGN = b.env vGN := by rw [hc.env vGN (by decide)]; norm_env
    refine Runs.callS (fmulP_spec C g hw hp _ (hgc.of_fr (((Fr.refl lagS c).set_right vMA _ (by decide)).set_right
        vMB _ (by decide)) (by decide)) (b.env vGN) (finv g.p g.t (b.env vGD)) (by norm_env; exact hcN)
        (by norm_env; exact hcv) hNl) (by decide) ?_ (by unfold lagCost; omega)
    rintro d hd ⟨hdv, hdl⟩
    refine Runs.last (run_copy C lagS _ vGL vMR (by decide) (by decide)) ?_ (by unfold lagCost; omega)
    intro _
    norm_env
    refine ⟨?_, hdl⟩
    rw [hdv, hN, hD]
    rfl

/-! ## The product over the coordinates -/

abbrev vQI : Var := 52
abbrev vQC : Var := 53
abbrev vQP : Var := 54
abbrev vQJ : Var := 55
abbrev vQQ : Var := 56
abbrev vQBL : Var := 57
abbrev vQZ : Var := 58
abbrev vQB : Var := 59
abbrev vQT : Var := 60

def prodS : List Var := [vQP, vQJ, vQQ, vQBL, vQZ, vQB, vQT, vGV, vGX] ++ lagS

def prodBody : Sc :=
  .seq (.op (.dm vQQ vPOWT vQT vQZ)) <| .seq (.op (.copy vQQ vQT)) <|
  .seq (.op (.dm vQBL vPOWH vQT vQB)) <| .seq (.op (.copy vQBL vQT)) <|
  .seq (.op (.copy vGV vQB)) <| .seq (.op (.copy vGX vQZ)) <| .seq lagP <|
  .seq (.op (.copy vMA vQP)) <| .seq (.op (.copy vMB vGL)) <| .seq fmulP <|
  .seq (.op (.copy vQP vMR)) (.op (.inc vQJ))

def prodP : Sc :=
  .seq (.op (.copy vQP vONE)) <| .seq (.op (.zero vQJ)) <| .seq (.op (.dm vQC vPOWT vQQ vQZ)) <|
  .seq (.op (.copy vQBL vQI)) <| .loop (.lt vQJ vM) prodBody

def prodBodyCost (t h : ℕ) : ℕ := lagCost t h + fmulCost t + 40

def prodCost (t h m : ℕ) : ℕ := m * (prodBodyCost t h + 2) + 20

/-- The state of `prodP` before round `j`. -/
def ProdInv (g : Prm) (a0 : Ds) (i c j : ℕ) (b : Ds) : Prop :=
  Fr prodS [] a0 b ∧
    b.env vQP = prodFold g.p g.t (fun j => lag g.p g.t g.h (blk g.h i j) (zc g.t c j)) g.m j 1 ∧
    b.env vQP < 2 ^ g.t ∧ b.env vQQ = c / 2 ^ ((j + 1) * g.t) ∧ b.env vQBL = i / 2 ^ (j * g.h) ∧ b.env vQJ = j

theorem prodBody_spec (C : Ctx) (g : Prm) (hw : WOk g C) (hp : GF.ModulusOk g.p g.t) (a0 b : Ds) (hg : Glob g b)
    (i c j : ℕ) (hj : j < g.m) (hinv : ProdInv g a0 i c j b) :
    Runs C prodBody b (prodBodyCost g.t g.h) prodS [] (ProdInv g a0 i c (j + 1)) := by
  obtain ⟨hf, hP, hPl, hQ, hBL, hJ⟩ := hinv
  have hT2 : 2 * 2 ^ g.t ≤ 2 ^ C.Wd := by
    have := pow_lt_W hw (x := g.t + 1) (by have := hw.2.1; omega); rw [pow_succ] at this; omega
  have hH2 : 2 * 2 ^ g.h ≤ 2 ^ C.Wd := by
    have := pow_lt_W hw (x := g.h + 1) (by have := hw.2.1; have := hw.2.2.1; omega); rw [pow_succ] at this; omega
  have hjW : j + 1 < 2 ^ C.Wd := lt_W hw (by
    have := Nat.lt_two_pow_self (n := g.L + 3); have := hw.2.2.2.2.1; omega)
  refine Runs.op1 (run_dm C prodS b vQQ vPOWT vQT vQZ (by decide) (by decide) (by decide)
    (by rw [hg.powt]; exact Nat.two_pow_pos _) (by rw [hg.powt]; exact hT2)) ?_ (by unfold prodBodyCost; omega)
  refine Runs.op1 (run_copy C prodS _ vQQ vQT (by decide) (by decide)) ?_ (by unfold prodBodyCost; omega)
  norm_env
  refine Runs.op1 (run_dm C prodS _ vQBL vPOWH vQT vQB (by decide) (by decide) (by decide)
    (by norm_env; rw [hg.powh]; exact Nat.two_pow_pos _) (by norm_env; rw [hg.powh]; exact hH2)) ?_
    (by unfold prodBodyCost; omega)
  refine Runs.op1 (run_copy C prodS _ vQBL vQT (by decide) (by decide)) ?_ (by unfold prodBodyCost; omega)
  refine Runs.op1 (run_copy C prodS _ vGV vQB (by decide) (by decide)) ?_ (by unfold prodBodyCost; omega)
  refine Runs.op1 (run_copy C prodS _ vGX vQZ (by decide) (by decide)) ?_ (by unfold prodBodyCost; omega)
  norm_env
  rw [hg.powt, hg.powh, hQ, hBL]
  have hblk : i / 2 ^ (j * g.h) % 2 ^ g.h = blk g.h i j := rfl
  have hzc : c / 2 ^ ((j + 1) * g.t) % 2 ^ g.t = zc g.t c j := rfl
  rw [hblk, hzc]
  have hf1 : Fr prodS [] b ((((((((b.set vQT (c / 2 ^ ((j + 1) * g.t) / 2 ^ g.t)).set vQZ (zc g.t c j)).set vQQ
      (c / 2 ^ ((j + 1) * g.t) / 2 ^ g.t)).set vQT (i / 2 ^ (j * g.h) / 2 ^ g.h)).set vQB (blk g.h i j)).set vQBL
      (i / 2 ^ (j * g.h) / 2 ^ g.h)).set vGV (blk g.h i j)).set vGX (zc g.t c j)) := by
    repeat (first | exact Fr.refl prodS b | refine Fr.set_right ?_ _ _ (by decide))
  refine Runs.callS (lagP_spec C g hw hp _ (hg.of_fr hf1 (by decide)) (blk g.h i j) (zc g.t c j) (blk_lt _ _ _)
    (zc_lt _ _ _) (by norm_env) (by norm_env)) (by decide) ?_ (by unfold prodBodyCost; omega)
  rintro c1 hc1 ⟨hc1v, hc1l⟩
  have hg1 : Glob g c1 := (hg.of_fr hf1 (by decide)).of_fr hc1 (by decide)
  refine Runs.op1 (run_copy C prodS _ vMA vQP (by decide) (by decide)) ?_ (by unfold prodBodyCost; omega)
  refine Runs.op1 (run_copy C prodS _ vMB vGL (by decide) (by decide)) ?_ (by unfold prodBodyCost; omega)
  have hc1P : c1.env vQP = b.env vQP := by rw [hc1.env vQP (by decide)]; norm_env
  refine Runs.callS (fmulP_spec C g hw hp _ (hg1.of_fr (((Fr.refl prodS c1).set_right vMA _ (by decide)).set_right
      vMB _ (by decide)) (by decide)) (b.env vQP) (lag g.p g.t g.h (blk g.h i j) (zc g.t c j))
      (by norm_env; exact hc1P) (by norm_env; exact hc1v) hPl) (by decide) ?_ (by unfold prodBodyCost; omega)
  rintro c2 hc2 ⟨hc2v, hc2l⟩
  refine Runs.op1 (run_copy C prodS _ vQP vMR (by decide) (by decide)) ?_ (by unfold prodBodyCost; omega)
  have hc2J : c2.env vQJ = j := by
    rw [hc2.env vQJ (by decide)]; norm_env; rw [hc1.env vQJ (by decide)]; norm_env; exact hJ
  refine Runs.last (run_inc C prodS _ vQJ (by decide) (by norm_env; rw [hc2J]; exact hjW)) ?_
    (by unfold prodBodyCost; omega)
  intro _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have e1 := (hf.trans0 hf1).trans0 (hc1.mono (by decide))
    have e2 := e1.trans0 ((((Fr.refl prodS c1).set_right vMA _ (by decide)).set_right vMB _ (by decide)).trans0
      (hc2.mono (by decide)))
    exact (e2.set_right _ _ (by decide)).set_right _ _ (by decide)
  · norm_env
    rw [hc2v, prodFold_succ, if_neg (by omega), hP]
  · norm_env; exact hc2l
  · norm_env
    rw [hc2.env vQQ (by decide)]; norm_env; rw [hc1.env vQQ (by decide)]; norm_env
    rw [Nat.div_div_eq_div_mul, ← pow_add]; congr 2; ring
  · norm_env
    rw [hc2.env vQBL (by decide)]; norm_env; rw [hc1.env vQBL (by decide)]; norm_env
    rw [Nat.div_div_eq_div_mul, ← pow_add]; congr 2; ring
  · norm_env; rw [hc2J]

theorem prodP_spec (C : Ctx) (g : Prm) (hw : WOk g C) (hp : GF.ModulusOk g.p g.t) (a : Ds) (hg : Glob g a)
    (i c : ℕ) (hai : a.env vQI = i) (hac : a.env vQC = c) :
    Runs C prodP a (prodCost g.t g.h g.m) prodS []
      (fun b => b.env vQP = prodAt g.p g.t g.h g.m i c ∧ b.env vQP < 2 ^ g.t) := by
  have hone : 1 < 2 ^ g.t := Nat.one_lt_two_pow (by have := hw.2.2.2.2.2; omega)
  have hT2 : 2 * 2 ^ g.t ≤ 2 ^ C.Wd := by
    have := pow_lt_W hw (x := g.t + 1) (by have := hw.2.1; omega); rw [pow_succ] at this; omega
  refine Runs.op1 (run_copy C prodS a vQP vONE (by decide) (by decide)) ?_ (by unfold prodCost; omega)
  refine Runs.op1 (run_zero C prodS _ vQJ (by decide)) ?_ (by unfold prodCost; omega)
  refine Runs.op1 (run_dm C prodS _ vQC vPOWT vQQ vQZ (by decide) (by decide) (by decide)
    (by norm_env; rw [hg.powt]; exact Nat.two_pow_pos _) (by norm_env; rw [hg.powt]; exact hT2)) ?_
    (by unfold prodCost; omega)
  refine Runs.op1 (run_copy C prodS _ vQBL vQI (by decide) (by decide)) ?_ (by unfold prodCost; omega)
  norm_env
  rw [hg.c.2.1, hg.powt, hac, hai]
  refine (Runs.loopN0 (C := C) (c := .lt vQJ vM) (body := prodBody) (S := prodS) (by unfold Cnd.wf; decide)
    g.m (prodBodyCost g.t g.h) (ProdInv g a i c) ?step ?stop _ ?init).mono ?cost (List.Subset.refl _) ?post
  case cost => unfold prodCost; omega
  case post =>
    rintro b - ⟨-, hP, hPl, -, -, -⟩
    exact ⟨hP, hPl⟩
  case step =>
    rintro j hj b hinv
    have hgb : Glob g b := hg.of_fr hinv.1 (by decide)
    refine ⟨by simp [Cnd.eval, hinv.2.2.2.2.2, hgb.m, hj], ?_⟩
    exact prodBody_spec C g hw hp a b hgb i c j hj hinv
  case stop =>
    rintro b ⟨hf, -, -, -, -, hJ⟩
    have hgb : Glob g b := hg.of_fr hf (by decide)
    simp [Cnd.eval, hJ, hgb.m]
  case init =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · repeat (first | exact Fr.refl prodS a | refine Fr.set_right ?_ _ _ (by decide))
    all_goals norm_env
    · rfl
    · exact hone
    · simp
    · simp

end NearCubicGates.Adapters.Amplification.Enc
