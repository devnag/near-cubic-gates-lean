import Proof.Gates.CellsGather.Copy
import Proof.Gates.CellsSys.PrF
import Proof.Gates.Cells.Inv

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.Cells.GatherPhase

open NearCubicGates.Close.Cells
open NearCubicWires NearCubicGates
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter

/-- **The gathering phase**, given the emission `eP`. -/
def gatherPOf (eP : St VV MM) : St VV MM :=
  .seq eP (.seq (.op (.rwM sG)) (.seq (.op (.srtM sG)) (.seq sweepP (.seq (.op (.rwM sA)) (.seq (.op (.srtM sA))
    (.seq stripP copyP))))))

/-- A bound on `gWork` from the call and the parameters. -/
def GWB (c : Call) (p : Params) : ℕ :=
  (reqIds c p).length + 2 * wWin p ^ nDig c p * (c.n + 1) ^ 3 + 100 * (c.n + 1) ^ 5

/-- **The gathering cost.** -/
def gatherCostOf (et : Ctx → Call → Params → ℕ → ℕ) (C : Ctx) (c : Call) (p : Params) (Big : ℕ) : ℕ :=
  et C c p Big + 100 * (GWB c p + 1)

theorem padRec_eq (c : Call) (p : Params) : padRec c p = 2 * 2 ^ keyW c p * 2 ^ gZ c p := by
  unfold padRec tRec; ring

theorem gZ_eq (c : Call) (p : Params) : gZ c p = valueWidth c p + keyW c p := rfl

theorem widths (C : Ctx) (c : Call) (p : Params) (wt : Wit c.n) (Big : ℕ) (hwd : wdNeed c p wt Big ≤ C.Wd) :
    2 * (valueWidth c p + keyW c p) + 2 ≤ C.Wd := by
  unfold wdNeed recWidth at hwd
  unfold keyW
  have hX : 2 ≤ 256 * (p.J + 4) * (Big + c.n + 16) := by
    have : 4 * 16 ≤ (p.J + 4) * (Big + c.n + 16) := Nat.mul_le_mul (by omega) (by omega)
    rw [Nat.mul_assoc]; omega
  generalize 256 * (p.J + 4) * (Big + c.n + 16) = X at hwd hX
  omega

theorem swT2_scratch : ∀ x ∈ swT2, gScratch x := by unfold gScratch; decide
theorem stT_scratch : ∀ x ∈ stT, gScratch x := by unfold gScratch; decide
theorem cpT_scratch : ∀ x ∈ cpT, gScratch x := by unfold gScratch; decide

variable {C : Ctx}

theorem pw_le {a b : ℕ} (h : a ≤ b) : 2 ^ a ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) h

/-- **The gathering phase meets `GatherGoal`, given the emission.** -/
theorem gatherPOf_spec (eP : St VV MM) (et : Ctx → Call → Params → ℕ → ℕ) (heP : EmitGoal eP et) :
    GatherGoal (gatherPOf eP) (gatherCostOf et) := by
  intro C cT c p wt i a Big hs hw hadm hi ht hpre hbig hwd
  obtain ⟨w, hw'⟩ := hw
  obtain ⟨B1, B2, hadm'⟩ := hadm
  obtain ⟨b1, n0, ex0, hn0, hperm, hsB, hram1, hrc1, hip1, hout1, hkin1, hkout1, hkc1, henv1⟩ :=
    heP C c p wt i a Big hs ⟨w, hw'⟩ ⟨B1, B2, hadm'⟩ hi ht hpre hbig hwd
  -- notation
  set y := cellOf wt.I i with hy
  set N := (rowVals c p wt y).length with hN
  set g := gWork c p wt y with hg
  set R := realS c p wt i with hR
  set nc := (CounterMachine.cellN c p wt).length with hnc
  have hRV : (rowVals c p wt (cellOf wt.I i)).length = N := rfl
  have hWd := widths C c p wt Big hwd
  have hlenG1 : (b1.ram sG).length = g := by rw [hperm.length_eq, gWork_eq]
  have hRlen : R.length = (reqIds c p).length + N := realS_length c p wt i
  have hglen : g = (reqIds c p).length + N + nc := rfl
  have hnc1 : 1 ≤ nc := by
    have : p.J ∈ CounterMachine.paramsN p := by simp [CounterMachine.paramsN]
    have h := SystemsPhase.mem_cellN_of_params c p wt this
    rw [hnc]; exact List.length_pos_of_mem h
  have hNk : N < 2 ^ keyW c p := by rw [hN, ← rowKeys_length]; exact rowKeys_lt c p wt y hs
  have hKWd : 2 ^ keyW c p * 4 ≤ 2 ^ C.Wd := by
    rw [show 4 = 2 ^ 2 by norm_num, ← pow_add]; exact pw_le (by omega)
  have hnsc : ∀ x : Fin VV, ¬ gScratch x → x ∉ swT2 ∧ x ∉ stT ∧ x ∉ cpT := fun x hx =>
    ⟨fun h => hx (swT2_scratch x h), fun h => hx (stT_scratch x h), fun h => hx (cpT_scratch x h)⟩
  -- the cursors of b1
  have hrcG1 : b1.rc sG ≤ g := by rw [← hlenG1]; exact hrc1 sG
  have hsA1 : b1.ram sA = a.ram sA := hram1 sA (by decide) (by decide)
  have hrcA1 : b1.rc sA ≤ N := by have := hrc1 sA; rw [hsA1] at this; exact this.trans hpre.aLen
  -- rewind and sort sG
  obtain ⟨s2, n2, ex2, hn2, h2⟩ := hs_rwM C sG b1
  subst h2
  obtain ⟨s3, n3, ex3, hn3, h3⟩ := hs_srtM C sG (b1.rew sG) (by simp [DS.rew])
  subst h3
  set e2 := (b1.rew sG).srt sG with he2
  have he2G : e2.ram sG = R ++ List.replicate nc (padRec c p) := by
    rw [he2]; simp only [DS.srt, DS.rew, Function.update_self]
    exact sorted_split c p wt i hs (b1.ram sG) hperm
  have he2O : ∀ m, m ≠ sG → e2.ram m = b1.ram m := by
    intro m hm; rw [he2]; simp only [DS.srt, DS.rew]; rw [Function.update_of_ne hm]
  have he2env : e2.env = b1.env := by rw [he2]; rfl
  have he2rcG : e2.rc sG = 0 := by rw [he2]; simp [DS.srt, DS.rew]
  have he2rcA : e2.rc sA = b1.rc sA := by
    rw [he2]; simp only [DS.srt, DS.rew]; rw [Function.update_of_ne (by decide : sA ≠ sG)]
  have hns : ∀ x : Fin VV, ¬ gScratch x → e2.env x = a.env x := fun x hx => by rw [he2env]; exact henv1 x hx
  have hcst : Cst e2 := ⟨by rw [hns vZ (by unfold gScratch; decide)]; exact hpre.cst.z,
    by rw [hns v1 (by unfold gScratch; decide)]; exact hpre.cst.one,
    by rw [hns v2 (by unfold gScratch; decide)]; exact hpre.cst.two⟩
  have hVW2 : e2.env p2VW = 2 ^ valueWidth c p := by rw [hns p2VW (by unfold gScratch; decide)]; exact hpre.VW
  have hKW2 : e2.env p2K = 2 ^ keyW c p := by rw [hns p2K (by unfold gScratch; decide)]; exact hpre.KW
  -- the sweep
  have hans : (sweep (gZ c p) (valueWidth c p) R 0).length = N := answers_length c p wt i hs w hw'
  have H : SwH C (gZ c p) (valueWidth c p) R nc (2 * 2 ^ keyW c p * 2 ^ gZ c p) e2 := by
    refine ⟨hcst, hVW2, by rw [he2G, padRec_eq], hnc1, fun x hx => ?_, ?_, ?_, ?_, ?_⟩
    · rw [← padRec_eq]
      exact realL_lt c p wt i hs x ((List.perm_insertionSort _ _).mem_iff.mp hx)
    · rw [← pow_succ']; exact pw_le (by rw [gZ_eq]; omega)
    · calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ C.Wd := pw_le (by omega)
    · have : 2 ^ gZ c p * 2 ^ valueWidth c p + 2 ^ gZ c p ≤ 2 ^ (gZ c p + valueWidth c p + 1) := by
        have : 2 ^ gZ c p ≤ 2 ^ gZ c p * 2 ^ valueWidth c p := Nat.le_mul_of_pos_right _ (by positivity)
        rw [pow_succ, pow_add]
        omega
      exact this.trans (pw_le (by rw [gZ_eq]; omega))
    · rw [hans]
      omega
  have hWp : 2 * (2 ^ keyW c p * 2 ^ gZ c p) < 2 ^ C.Wd := by
    rw [← pow_add, ← pow_succ']
    exact Nat.pow_lt_pow_right (by norm_num) (by rw [gZ_eq]; omega)
  obtain ⟨b3, n4, ex4, hn4, I3⟩ := sweepP_spec (C := C) e2 (gZ c p) (valueWidth c p) (keyW c p) R nc H hKW2
    (gZ_eq c p) he2rcG hWp
  have I3A := I3.ramA
  have I3rcA := I3.rcA
  have I3nq := I3.nq
  rw [List.take_length] at I3A I3rcA I3nq
  have hb3A : b3.ram sA = sweep (gZ c p) (valueWidth c p) R 0 := by
    rw [I3A, he2O sA (by decide), hsA1, List.drop_eq_nil_of_le, List.append_nil]
    rw [hans]; exact hpre.aLen
  have hb3rcA : b3.rc sA = N := by rw [I3rcA, hans]

  obtain ⟨s5, n5, ex5, hn5, h5⟩ := hs_rwM C sA b3
  subst h5
  obtain ⟨s6, n6, ex6, hn6, h6⟩ := hs_srtM C sA (b3.rew sA) (by simp [DS.rew])
  subst h6
  set e6 := (b3.rew sA).srt sA with he6
  have he6A : e6.ram sA = (qryQ c p wt i).map (aRec (valueWidth c p) (F c p wt y)) := by
    rw [he6]; simp only [DS.srt, DS.rew, Function.update_self]; rw [hb3A]
    exact answers_eq c p wt i hs w hw'
  have he6G : e6.ram sG = R ++ List.replicate nc (padRec c p) := by
    rw [he6]; simp only [DS.srt, DS.rew]; rw [Function.update_of_ne (by decide : sG ≠ sA), I3.ramO sG (by decide),
      he2G]
  have he6O : ∀ m, m ≠ sA → e6.ram m = e2.ram m := by
    intro m hm; rw [he6]; simp only [DS.srt, DS.rew]; rw [Function.update_of_ne hm, I3.ramO m hm]
  have he6env : e6.env = b3.env := by rw [he6]; rfl
  have he6rcA : e6.rc sA = 0 := by rw [he6]; simp [DS.srt, DS.rew]
  have he6rcG : e6.rc sG = R.length + 1 := by
    rw [he6]; simp only [DS.srt, DS.rew]; rw [Function.update_of_ne (by decide : sG ≠ sA), I3.rcG]
  have he6q : e6.env gNQ = N := by rw [he6env, I3nq, hans]
  have he6v : e6.env p2VW = 2 ^ valueWidth c p := by rw [he6env, I3.fr.ev (by decide), hVW2]
  have hQlen : ((qryQ c p wt i).map (aRec (valueWidth c p) (F c p wt y))).length = N := by
    rw [List.length_map, qryQ_length]
  have hGlen : (R ++ List.replicate nc (padRec c p)).length = g := by
    rw [List.length_append, List.length_replicate, hRlen, hglen]
  -- strip
  obtain ⟨b7, n7, ex7, hn7, s7G, s7A, s7O, s7rcA, s7rcG, s7fr, s7ip, s7out, s7kin, s7kout, s7kc⟩ :=
    stripP_spec (C := C) e6 (valueWidth c p) N _ _ he6A he6G hQlen (by rw [hGlen, hglen]; omega) he6q he6v
      (by rw [← pow_succ']; exact pw_le (by omega)) (by have := pw_le (show keyW c p ≤ C.Wd by omega); omega)
  rw [strip_main c p wt i hs w hw'] at s7G
  -- copy
  obtain ⟨b8, n8, ex8, hn8, s8A, s8O, s8fr, s8ip, s8out, s8kin, s8kout, s8kc⟩ :=
    copyP_spec (C := C) b7 N (rowVals c p wt y) _ _ s7G rfl s7A hQlen
      (by rw [s7fr.ev (by decide), he6q]) (by have := pw_le (show keyW c p ≤ C.Wd by omega); omega)
  -- the run
  have ex : Ex C (gatherPOf eP) a b8 (n0 + (n2 + (n3 + (n4 + (n5 + (n6 + (n7 + n8 + 1) + 1) + 1) + 1) + 1) + 1) + 1) :=
    Ex.seq ex0 (Ex.seq ex2 (Ex.seq ex3 (Ex.seq ex4 (Ex.seq ex5 (Ex.seq ex6 (Ex.seq ex7 ex8))))))
  refine ⟨b8, _, ex, ?_, s8A, ?_, ?_, ?_, ex.rc_le hpre.rcur, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the cost
    have hgB : g ≤ GWB c p := by
      have h1 := rowKeys_le_n c p wt y hs
      have h2 := SystemsPhase.cellN_len c p wt w hadm' hs hw'
      rw [rowKeys_length] at h1
      unfold GWB; rw [hglen]; omega
    have hc3 : n3 ≤ g + 1 := by
      have : n3 ≤ ((b1.rew sG).ram sG).length + 1 := hn3
      simp only [DS.rew] at this; omega
    have hc4 : n4 ≤ N + 16 * R.length + 16 := by rw [he2rcA] at hn4; omega
    have hc5 : n5 ≤ N + 1 := by rw [hb3rcA] at hn5; exact hn5
    have hc6 : n6 ≤ N + 1 := by
      have : n6 ≤ ((b3.rew sA).ram sA).length + 1 := hn6
      simp only [DS.rew] at this; rw [hb3A, hans] at this; exact this
    have hc7 : n7 ≤ R.length + 1 + 9 * N + 8 := by rw [he6rcA, he6rcG] at hn7; omega
    have hc8 : n8 ≤ N + N + 7 * N + 8 := by rw [s7rcA, s7rcG] at hn8; exact hn8
    have hc2 : n2 ≤ g + 1 := by omega
    unfold gatherCostOf
    omega
  · intro m hm1 hm2 hm3
    rw [s8O m hm3, s7O m hm1, he6O m hm3, he2O m hm1]; exact hram1 m hm1 hm2
  · rw [s8O sG (by decide), s7G, List.length_append, List.length_drop, hGlen]; omega
  · rw [s8O sB (by decide), s7O sB (by decide), he6O sB (by decide), he2O sB (by decide)]; exact hsB
  · rw [s8ip, s7ip]; show b3.ip = a.ip; rw [I3.ip, he2]; exact hip1
  · rw [s8out, s7out]; show b3.out = a.out; rw [I3.out, he2]; exact hout1
  · rw [s8kin, s7kin]; show b3.kin = a.kin; rw [I3.kin, he2]; exact hkin1
  · rw [s8kout, s7kout]; show b3.kout = a.kout; rw [I3.kout, he2]; exact hkout1
  · rw [s8kc, s7kc]; show b3.kc = a.kc; rw [I3.kc, he2]; exact hkc1
  · intro x hx
    obtain ⟨h1, h2, h3⟩ := hnsc x hx
    rw [s8fr.ev h3, s7fr.ev h2, he6env, I3.fr.ev h1]; exact hns x hx

/-- **The class of the gathering cost.** -/
theorem gatherCostOf_class (et : Ctx → Call → Params → ℕ → ℕ) (hc : EmitClass et) :
    GatherClass (gatherCostOf et) := by
  obtain ⟨K, e, hK⟩ := hc
  refine ⟨K + 20300, e + 5, fun C c p Big => ?_⟩
  set X := c.n + Big + C.Wd + 2 with hX
  set A := (reqIds c p).length + wWin p ^ nDig c p + 1 with hA
  have hX1 : 1 ≤ X := by omega
  have hn : c.n + 1 ≤ X := by omega
  have h5 : X ^ 5 ≤ X ^ (e + 5) := Nat.pow_le_pow_right hX1 (by omega)
  have he : X ^ e ≤ X ^ (e + 5) := Nat.pow_le_pow_right hX1 (by omega)
  have h3 : (c.n + 1) ^ 3 ≤ X ^ 5 :=
    (Nat.pow_le_pow_left hn 3).trans (Nat.pow_le_pow_right hX1 (by omega))
  have h5' : (c.n + 1) ^ 5 ≤ X ^ 5 := Nat.pow_le_pow_left hn 5
  have hX5 : 1 ≤ X ^ 5 := Nat.one_le_pow _ _ hX1
  have hGWB : GWB c p + 1 ≤ A * (203 * X ^ 5) := by
    unfold GWB
    have hBN : wWin p ^ nDig c p ≤ A := by omega
    have hR : (reqIds c p).length ≤ A := by omega
    have hA1 : 1 ≤ A := by omega
    have e1 : 2 * wWin p ^ nDig c p * (c.n + 1) ^ 3 ≤ 2 * A * X ^ 5 :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ hBN) h3
    have e2 : 100 * (c.n + 1) ^ 5 ≤ 100 * A * X ^ 5 := by
      have := Nat.mul_le_mul hA1 h5'; nlinarith
    have e3 : (reqIds c p).length + 1 ≤ 100 * A * X ^ 5 := by nlinarith
    nlinarith
  unfold gatherCostOf
  have h1 : et C c p Big ≤ K * A * X ^ e := hK C c p Big
  have h2 : K * A * X ^ e ≤ K * A * X ^ (e + 5) := Nat.mul_le_mul_left _ he
  have h3' : 100 * (A * (203 * X ^ 5)) ≤ 20300 * A * X ^ (e + 5) := by
    have := Nat.mul_le_mul_left (20300 * A) h5
    nlinarith
  calc et C c p Big + 100 * (GWB c p + 1) ≤ K * A * X ^ (e + 5) + 20300 * A * X ^ (e + 5) := by
        have := Nat.mul_le_mul_left 100 hGWB
        omega
    _ = (K + 20300) * A * X ^ (e + 5) := by ring

end NearCubicGates.Close.Cells.GatherPhase
