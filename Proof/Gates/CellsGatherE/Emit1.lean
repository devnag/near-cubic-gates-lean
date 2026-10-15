import Proof.Gates.CellsGather.EmitSpec
import Proof.Gates.CellsGatherE.QSpec
import Proof.Gates.CounterMachine.CellTablesCst2
import Proof.Gates.CounterMachine.CellTablesLoop5
import Proof.Gates.CellsSys.Kit
import Proof.Gates.CellsSys.PrF

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.Cells.RecordEmission

open NearCubicWires NearCubicGates NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Counter

/-! ## Variables (all in `gScratch`: 50 … 99) -/

def eND : Fin VV := ⟨51, by decide⟩   -- `nDig = roleCount·J`
def eW : Fin VV := ⟨52, by decide⟩    -- `wWin = 2h_E − 1`
def eD : Fin VV := ⟨53, by decide⟩    -- `D = roleCount·J + roleCount`
def eR : Fin VV := ⟨54, by decide⟩    -- `|reqIds|`
def eS : Fin VV := ⟨55, by decide⟩    -- `Σ_q q^D`
def ePar : Fin VV := ⟨57, by decide⟩  -- `|parts|`
def eI : Fin VV := ⟨58, by decide⟩
def eIdx : Fin VV := ⟨59, by decide⟩
def eQ : Fin VV := ⟨60, by decide⟩
def ePw : Fin VV := ⟨61, by decide⟩
def eI2 : Fin VV := ⟨62, by decide⟩
def eT2 : Fin VV := ⟨63, by decide⟩
def eA : Fin VV := ⟨88, by decide⟩
def eB : Fin VV := ⟨89, by decide⟩
def eJk : Fin VV := ⟨86, by decide⟩

/-! ## The number of requests -/

theorem reqIds_length (c : Call) (p : Params) :
    (reqIds c p).length = (parts c).length * ((p.primes.sort (· ≤ ·)).map fun q => q ^ CounterMachine.CellTablesProg.dOf c p).sum +
      roleCount c.kind * (p.J + 1) := by
  rw [← CounterMachine.CellTablesProg.enum_eq, List.length_append, List.length_flatMap, List.length_flatMap]
  have h1 : ∀ part : Option Bool, ((p.primes.sort (· ≤ ·)).flatMap fun q =>
      (List.range (q ^ CounterMachine.CellTablesProg.dOf c p)).map (CounterMachine.CellTablesProg.resId c p part q)).length =
      ((p.primes.sort (· ≤ ·)).map fun q => q ^ CounterMachine.CellTablesProg.dOf c p).sum := by
    intro part; rw [List.length_flatMap]; simp
  simp only [h1, List.map_const', List.sum_replicate, smul_eq_mul]
  congr 1
  simp [CounterMachine.CellTablesProg.momIds]

theorem dOf_eq (c : Call) (p : Params) : CounterMachine.CellTablesProg.dOf c p = roleCount c.kind * p.J + roleCount c.kind := by
  unfold CounterMachine.CellTablesProg.dOf; ring

/-! ## The constants -/

def cstE : St VV MM :=
  .seq (.op (.mul p2VW p2K eG2)) (.seq (.op (.mul gRC gJ eND)) (.seq (.op (.copy eW vHE)) (.seq (.op (.shl eW))
  (.seq (.op (.sub eW v1)) (.seq (.op (.copy eD eND)) (.seq (.op (.add eD gRC)) (.seq (.op (.copy ePar v1))
  (.ite (.eq gKd v2) (.op (.copy ePar v2)) (.op (.zero eJk))))))))))

def cstT : List (Fin VV) := [eG2, eND, eW, eD, ePar, eJk]

/-- The constants' values. -/
structure CV (c : Call) (p : Params) (e : DS VV MM) : Prop where
  g2 : e.env eG2 = 2 ^ valueWidth c p * 2 ^ keyW c p
  nd : e.env eND = nDig c p
  w : e.env eW = wWin p
  d : e.env eD = CounterMachine.CellTablesProg.dOf c p
  par : e.env ePar = (parts c).length

theorem cstE_spec (C : Ctx) (c : Call) (p : Params) (a : DS VV MM) (hc : Cst a) (hE1 : 1 ≤ p.hE)
    (hVW : a.env p2VW = 2 ^ valueWidth c p) (hKW : a.env p2K = 2 ^ keyW c p) (hJ : a.env gJ = p.J)
    (hrc : a.env gRC = roleCount c.kind) (hhE : a.env vHE = p.hE) (hkd : a.env gKd = kindTag c.kind)
    (hW1 : 2 ^ valueWidth c p * 2 ^ keyW c p < 2 ^ C.Wd) (hW2 : 2 * p.hE + roleCount c.kind * (p.J + 1) < 2 ^ C.Wd) :
    Hs C cstE a 20 (fun e => CV c p e ∧ Same a e ∧ Fr a e cstT ∧ Cst e) := by
  have hrc2 : roleCount c.kind ≤ 2 := by cases c.kind <;> decide
  apply Hx.hs
  refine Hs.then (hs_mul C p2VW p2K eG2 a (by decide) (by decide) (by decide) (by rw [hVW, hKW]; exact hW1))
    (fun b1 hb1 n1 hn1 => ?_); subst hb1
  refine Hs.then (hs_mul C gRC gJ eND _ (by decide) (by decide) (by decide) (by vsimp [hrc, hJ]; nlinarith))
    (fun b2 hb2 n2 hn2 => ?_); subst hb2
  refine Hs.then (hs_copy C eW vHE _ (by decide)) (fun b3 hb3 n3 hn3 => ?_); subst hb3
  refine Hs.then (hs_shl C eW _ (by vsimp [hhE]; omega)) (fun b4 hb4 n4 hn4 => ?_); subst hb4
  refine Hs.then (hs_sub C eW v1 _ (by decide) (by vsimp [hhE, hc.one]; omega)) (fun b5 hb5 n5 hn5 => ?_); subst hb5
  refine Hs.then (hs_copy C eD eND _ (by decide)) (fun b6 hb6 n6 hn6 => ?_); subst hb6
  refine Hs.then (hs_add C eD gRC _ (by decide) (by vsimp [hrc, hJ]; nlinarith)) (fun b7 hb7 n7 hn7 => ?_)
  subst hb7
  refine Hs.then (hs_copy C ePar v1 _ (by decide)) (fun b8 hb8 n8 hn8 => ?_); subst hb8
  have hkind : kindTag c.kind = 2 ↔ c.kind = .parity := by cases c.kind <;> decide
  have hparts : (parts c).length = if c.kind = .parity then 2 else 1 := by unfold parts; split <;> simp
  refine Hs.last (Hs.ite (t := 1) (R := fun e => CV c p e ∧ Same a e ∧ Fr a e cstT ∧ Cst e) (show gKd ≠ v2 by decide) ?_ ?_)
    (fun e he n hn => ⟨he, by omega⟩)
  · intro h
    have hk : c.kind = .parity := by
      simp only [Cnd.eval, decide_eq_true_eq] at h; vsimp [hkd, hc.two] at h; exact hkind.mp h
    refine Hs.mono (hs_copy C ePar v2 _ (by decide)) le_rfl ?_
    rintro e rfl
    refine ⟨⟨by vsimp [hVW, hKW], by vsimp [hrc, hJ], by vsimp [hhE, hc.one], by vsimp [hrc, hJ, dOf_eq],
      by vsimp [hparts, hk, hc.two]⟩, ?_, ?_, ?_⟩
    · exact (Same.set _ _ _).trans ((Same.set _ _ _).trans ((Same.set _ _ _).trans ((Same.set _ _ _).trans
        ((Same.set _ _ _).trans ((Same.set _ _ _).trans ((Same.set _ _ _).trans ((Same.set _ _ _).trans
        (Same.set _ _ _))))))))
    · intro z hz; simp only [cstT, List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hz
      simp only [DS.set, Function.update_apply, h1, h2, h3, h4, h5, if_false]
    · exact ⟨by vsimp [hc.z], by vsimp [hc.one], by vsimp [hc.two]⟩
  · intro h
    have hk : c.kind ≠ .parity := by
      simp only [Cnd.eval, decide_eq_false_iff_not] at h; vsimp [hkd, hc.two] at h
      exact fun e => h (hkind.mpr e)
    refine Hs.mono (hs_zero C eJk _) le_rfl ?_
    rintro e rfl
    refine ⟨⟨by vsimp [hVW, hKW], by vsimp [hrc, hJ], by vsimp [hhE, hc.one], by vsimp [hrc, hJ, dOf_eq],
      by vsimp [hparts, hk, hc.one]⟩, ?_, ?_, ?_⟩
    · exact (Same.set _ _ _).trans ((Same.set _ _ _).trans ((Same.set _ _ _).trans ((Same.set _ _ _).trans
        ((Same.set _ _ _).trans ((Same.set _ _ _).trans ((Same.set _ _ _).trans ((Same.set _ _ _).trans
        (Same.set _ _ _))))))))
    · intro z hz; simp only [cstT, List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hz
      simp only [DS.set, Function.update_apply, h1, h2, h3, h4, h5, h6, if_false]
    · exact ⟨by vsimp [hc.z], by vsimp [hc.one], by vsimp [hc.two]⟩

end NearCubicGates.Close.Cells.RecordEmission
