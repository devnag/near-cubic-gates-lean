import Proof.Gates.CellsGatherQ.Query4

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSectionVars false

namespace NearCubicGates.Close.Cells.QueryPass

open NearCubicWires NearCubicGates NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Counter
open NearCubicGates.Close.Cells.RecordEmission (GW eG2 qScratch QPre)
open NearCubicGates.Close.Cells.QueryKey (kPC kQ kT kS kKey keyScratch KeyGoal qKey)

/-! ## Re-indexing -/

theorem flatMap_range {α β : Type} (d : α) (G : α → List β) : ∀ l : List α,
    l.flatMap G = (List.range l.length).flatMap (fun k => G (l.getD k d))
  | [] => rfl
  | x :: l => by
    rw [List.flatMap_cons, flatMap_range d G l, List.length_cons, List.range_succ_eq_map, List.flatMap_cons,
      List.flatMap_map]
    simp

/-- The `k`-th part. -/
def pOf (c : Call) (k : ℕ) : Option Bool := (parts c).getD k none

/-- **The query keys in the order of the loops.** -/
theorem rowKeys_loops (c : Call) (p : Params) (wt : Wit c.n) (y : Cells wt.I) :
    GatherPhase.rowKeys c p wt y = (List.range (parts c).length).flatMap fun k => lT c p wt y (pOf c k) := by
  rw [QueryKey.rowKeys_eq, flatMap_range none _ (parts c)]
  unfold lT lJ lS pOf prJ
  congr 1; funext k; congr 1; funext t
  rw [flatMap_range 0 _ (p.primes.sort (· ≤ ·))]
  congr 1; funext j
  rw [List.map_eq_flatMap]

theorem pOf_mem (c : Call) (k : ℕ) (hk : k < (parts c).length) : pOf c k ∈ parts c := by
  unfold pOf; rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem _

theorem partCode_pOf (c : Call) (k : ℕ) (hk : k < (parts c).length) :
    partCode (pOf c k) = if kindTag c.kind = 2 then k + 1 else 0 := by
  have hkind : kindTag c.kind = 2 ↔ c.kind = .parity := by cases c.kind <;> decide
  unfold pOf; unfold parts at hk ⊢
  by_cases h : c.kind = .parity
  · rw [if_pos h] at hk ⊢; rw [if_pos (hkind.mpr h)]
    simp at hk; interval_cases k <;> rfl
  · rw [if_neg h] at hk ⊢; rw [if_neg (fun e => h (hkind.mp e))]
    simp at hk; subst hk; rfl

theorem parts_len_eq (c : Call) : (parts c).length = if kindTag c.kind = 2 then 2 else 1 := by
  have hkind : kindTag c.kind = 2 ↔ c.kind = .parity := by cases c.kind <;> decide
  unfold parts
  by_cases h : c.kind = .parity
  · rw [if_pos h, if_pos (hkind.mpr h)]; rfl
  · rw [if_neg h, if_neg (fun e => h (hkind.mp e))]; rfl

/-! ## The part body -/

def pcS : St VV MM := .ite (.eq gKd v2) (.seq (.op (.copy kPC qPi)) (.op (.inc kPC))) (.op (.zero kPC))

theorem pcS_spec (C : Ctx) (c : Call) (d : DS VV MM) (k : ℕ) (hc : Cst d) (hkd : d.env gKd = kindTag c.kind)
    (hki : d.env qPi = k) (hk : k < (parts c).length) (hW : k + 1 < 2 ^ C.Wd) :
    Hs C pcS d 4 (fun e => e.env kPC = partCode (pOf c k) ∧ Fr d e [kPC] ∧ Same d e) := by
  rw [partCode_pOf c k hk]
  refine Hs.ite (t := 3) (show gKd ≠ v2 by decide) (fun h => ?_) (fun h => ?_)
  · have h2 : kindTag c.kind = 2 := by
      simp only [Cnd.eval, decide_eq_true_eq] at h; rw [hkd, hc.two] at h; exact h
    refine Hs.mono (Hs.seq (t2 := 1) (hs_copy C kPC qPi d (by decide)) (fun b hb => ?_)) (by norm_num) (fun _ h => h)
    subst hb
    refine Hs.mono (hs_inc C kPC _ (by vsimp [hki]; omega)) le_rfl ?_
    rintro e rfl
    refine ⟨by vsimp [hki, h2], fun y hy => ?_, Same.of_sh (by simp)⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    simp [DS.set, Function.update_apply, hy]
  · have h2 : kindTag c.kind ≠ 2 := by
      simp only [Cnd.eval, decide_eq_false_iff_not] at h; rw [hkd, hc.two] at h; exact h
    refine Hs.mono (hs_zero C kPC d) (by omega) ?_
    rintro e rfl
    refine ⟨by vsimp [h2], fun y hy => ?_, Same.of_sh (by simp)⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    simp [DS.set, Function.update_apply, hy]

def partB (kP : St VV MM) : St VV MM := .seq pcS (cL kP)

def aT : List (Fin VV) := qPi :: kPC :: cT'

theorem aT_ok : ∀ x ∈ aT, gScratch x ∧ x ≠ eG2 := by unfold aT cT' tT pT sT uT kList gScratch; decide

/-- The cost of the digit-vector loop. -/
def costC (kc : Ctx → Call → Params → ℕ → ℕ) (C : Ctx) (c : Call) (p : Params) (wt : Wit c.n) (Big : ℕ) : ℕ :=
  wWin p ^ nDig c p * ((p.primes.sort (· ≤ ·)).length * (costP kc C c p wt Big + 4) + 4 + 4) + 4

theorem partB_spec (kP : St VV MM) (kc : Ctx → Call → Params → ℕ → ℕ) (hk : KeyGoal kP kc) (C : Ctx) (c : Call)
    (p : Params) (wt : Wit c.n) (i : ℕ) (a0 : DS VV MM) (Big : ℕ) (hy : Hy C c p wt Big) (d : DS VV MM)
    (S Wc : List ℕ) (n1 : ℕ) (k : ℕ) (hkN : k < (parts c).length)
    (hQ : QPre c p wt i a0 d) (hG : GW d S Wc) (hT : d.env qT = n1) (hki : d.env qPi = k)
    (hn : n1 + (lT c p wt (cellOf wt.I i) (pOf c k)).length ≤ 2 ^ keyW c p) :
    Hs C (partB kP) d (4 + costC kc C c p wt Big + 1) (fun e => QPre c p wt i a0 e ∧
      GW e S (Wc ++ QR (GatherPhase.gZ c p) (lT c p wt (cellOf wt.I i) (pOf c k)) n1) ∧
      e.env qT = n1 + (lT c p wt (cellOf wt.I i) (pOf c k)).length ∧ Fr d e (kPC :: cT')) := by
  obtain ⟨hc, -, -, -, -, -, -, hkd, -, -, -⟩ := QPre.vals hQ
  have h2 := two_pow_gt C c p wt Big hy.wd
  have hp2 : (parts c).length ≤ 2 := GatherPhase.parts_len c
  refine Hs.seq (pcS_spec C c d k hc hkd hki hkN (by omega)) (fun e ⟨e1, e2, e3⟩ => ?_)
  have Qe : QPre c p wt i a0 e :=
    QPre.step hQ ⟨fun m _ => by rw [e3.ram], e3.ip, e3.out, e3.kin, e3.kout, e3.kc⟩
      (fun m => by rw [e3.rc, e3.ram]; exact hQ.rcur m) [kPC] (by unfold gScratch; decide) e2
  have Ge : GW e S Wc := GW.congr hG (by rw [e3.ram]) (by rw [e3.rc])
  refine Hs.mono (cL_spec kP kc hk C c p wt i a0 Big hy e S Wc n1 (pOf c k) (pOf_mem c k hkN) Qe Ge
    (by rw [e2 qT (by decide)]; exact hT) e1 hn) le_rfl ?_
  rintro f ⟨f1, f2, f3, f4⟩
  exact ⟨f1, f2, f3, Fr.trans (Fr.weaken e2 (by decide)) (Fr.weaken f4 (by decide))⟩

end NearCubicGates.Close.Cells.QueryPass
