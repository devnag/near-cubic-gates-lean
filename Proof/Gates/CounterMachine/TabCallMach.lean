import Proof.Gates.CounterMachine.TabCallUnif

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicGates.Close.CounterMachine.TabCallProg

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.CounterMachine
open NearCubicGates.Close.Counter NearCubicGates.Close.CheckedPCPP

/-! ## Sizes of the request word's parts -/

section Parts
variable {B1 B2 cT : ℕ}

theorem pfx_le (x : TabCallReq B1 B2 cT) : (pfxOf x).length ≤ (prefixesWord x.r).length := by
  obtain ⟨h, hw⟩ := prefix_sel x
  rw [prefixesWord_eq]
  have := TabCallSizes.len_le_flatMap RepairOrdinary.frame (wsOf x.r) _ (List.getElem_mem h)
  rw [hw] at this
  have : (pfxOf x).length ≤ (RepairOrdinary.frame (pfxOf x)).length := by
    simp [RepairOrdinary.frame]; omega
  omega

theorem toks_le (x : TabCallReq B1 B2 cT) :
    ((formulaToks x).flatMap tokWord).length + (formulaToks x).length ≤ 2 * tabSize (tabCallTab x) := by
  rw [← toks_tabCallTab]
  have h1 : (toks (tabCallTab x).F).length ≤ ((toks (tabCallTab x).F).flatMap tokWord).length :=
    flatMap_len_ge tokWord (fun t => by cases t <;> simp [tokWord, TabCallSizes.natWord_len] <;> omega) _
  have h2 : ((toks (tabCallTab x).F).flatMap tokWord).length ≤ (formulaWord ⟨(tabCallTab x).V, (tabCallTab x).F⟩).length := by
    simp [formulaWord, listWord]; omega
  have h3 : (formulaWord ⟨(tabCallTab x).V, (tabCallTab x).F⟩).length ≤ tabSize (tabCallTab x) := by unfold tabSize; omega
  omega

end Parts

/-! ## The constants -/

section Const
variable (B1 B2 : ℕ) (PolyTab : TabMachine)

noncomputable def CK : ℕ := Classical.choose PolyTab.cls

noncomputable def eK : ℕ := Classical.choose (Classical.choose_spec PolyTab.cls)

theorem polyTab_le (R : TabReq) : PolyTab.budget R ≤ CK PolyTab * 2 ^ R.s * tabSize R ^ eK PolyTab :=
  Classical.choose_spec (Classical.choose_spec PolyTab.cls) R

theorem polyW (eP : ℕ) : PolyB (nI (B1 := B1) (B2 := B2)) (fun i => ((cellInput i.2.r).length + 1) ^ eP) :=
  PolyB.pow (PolyB.add polyCin (PolyB.const 1)) eP

theorem polyK : PolyB (nI (B1 := B1) (B2 := B2)) (fun i => tabSize (tabCallTab i.2) ^ eK PolyTab) :=
  PolyB.pow polyTab _

noncomputable def C1 (eP : ℕ) : ℕ := Classical.choose (polyW B1 B2 eP)
noncomputable def e1 (eP : ℕ) : ℕ := Classical.choose (Classical.choose_spec (polyW B1 B2 eP))
noncomputable def C2 : ℕ := Classical.choose (polyK B1 B2 PolyTab)
noncomputable def e2 : ℕ := Classical.choose (Classical.choose_spec (polyK B1 B2 PolyTab))

theorem w_le (eP : ℕ) (i : TabCallIndex B1 B2) :
    ((cellInput i.2.r).length + 1) ^ eP ≤ C1 B1 B2 eP * (nI i + 1) ^ e1 B1 B2 eP :=
  Classical.choose_spec (Classical.choose_spec (polyW B1 B2 eP)) i

theorem t_le (i : TabCallIndex B1 B2) : tabSize (tabCallTab i.2) ^ eK PolyTab ≤ C2 B1 B2 PolyTab * (nI i + 1) ^ e2 B1 B2 PolyTab :=
  Classical.choose_spec (Classical.choose_spec (polyK B1 B2 PolyTab)) i

/-- The log exponent: independent of `c_T`. -/
noncomputable def ElOf (eP : ℕ) : ℕ := e1 B1 B2 eP + e2 B1 B2 PolyTab

/-- The log constant. -/
noncomputable def ClOf (CP eP : ℕ) : ℕ := CP * C1 B1 B2 eP + CK PolyTab * C2 B1 B2 PolyTab

end Const

/-! ## The log bounds -/

section Log
variable {B1 B2 cT : ℕ} (PolyTab : TabMachine) (PM : PrefixMachine B1 B2 cT) (CP eP : ℕ)
  (hPM : ∀ r, PM.budget r ≤ CP * 2 ^ r.p.k * ((cellInput r).length + 1) ^ eP)

include hPM in
theorem pm_log (x : TabCallReq B1 B2 cT) :
    PM.budget x.r ≤ lcap (ClOf B1 B2 PolyTab CP eP) (ElOf B1 B2 PolyTab eP) x.r.c.n x.r.p.k := by
  have h1 := hPM x.r
  have h2 := w_le B1 B2 eP ⟨cT, x⟩
  have h3 := two_k_le (B1 := B1) (B2 := B2) ⟨cT, x⟩
  have h4 : (x.r.c.n + 1) ^ e1 B1 B2 eP ≤ (x.r.c.n + 1) ^ ElOf B1 B2 PolyTab eP :=
    Nat.pow_le_pow_right (by omega) (by unfold ElOf; omega)
  unfold nI sI at *
  unfold lcap ClOf
  calc PM.budget x.r ≤ CP * 2 ^ x.r.p.k * ((cellInput x.r).length + 1) ^ eP := h1
    _ ≤ CP * 2 ^ (x.r.c.n - x.r.p.k) * (C1 B1 B2 eP * (x.r.c.n + 1) ^ ElOf B1 B2 PolyTab eP) := by
        gcongr; exact h2.trans (Nat.mul_le_mul_left _ h4)
    _ = (CP * C1 B1 B2 eP) * 2 ^ (x.r.c.n - x.r.p.k) * (x.r.c.n + 1) ^ ElOf B1 B2 PolyTab eP := by ring
    _ ≤ (CP * C1 B1 B2 eP + CK PolyTab * C2 B1 B2 PolyTab) * 2 ^ (x.r.c.n - x.r.p.k) *
        (x.r.c.n + 1) ^ ElOf B1 B2 PolyTab eP := by gcongr; omega

theorem polyTab_log (x : TabCallReq B1 B2 cT) :
    PolyTab.budget (tabCallTab x) ≤ lcap (ClOf B1 B2 PolyTab CP eP) (ElOf B1 B2 PolyTab eP) x.r.c.n x.r.p.k := by
  have h1 := polyTab_le PolyTab (tabCallTab x)
  rw [tabCallTab_s] at h1
  have h2 := t_le B1 B2 PolyTab ⟨cT, x⟩
  have h4 : (x.r.c.n + 1) ^ e2 B1 B2 PolyTab ≤ (x.r.c.n + 1) ^ ElOf B1 B2 PolyTab eP :=
    Nat.pow_le_pow_right (by omega) (by unfold ElOf; omega)
  unfold nI at h2
  unfold lcap ClOf
  calc PolyTab.budget (tabCallTab x) ≤ CK PolyTab * 2 ^ (x.r.c.n - x.r.p.k) * tabSize (tabCallTab x) ^ eK PolyTab := h1
    _ ≤ CK PolyTab * 2 ^ (x.r.c.n - x.r.p.k) * (C2 B1 B2 PolyTab * (x.r.c.n + 1) ^ ElOf B1 B2 PolyTab eP) := by
        gcongr; exact h2.trans (Nat.mul_le_mul_left _ h4)
    _ = (CK PolyTab * C2 B1 B2 PolyTab) * 2 ^ (x.r.c.n - x.r.p.k) * (x.r.c.n + 1) ^ ElOf B1 B2 PolyTab eP := by ring
    _ ≤ (CP * C1 B1 B2 eP + CK PolyTab * C2 B1 B2 PolyTab) * 2 ^ (x.r.c.n - x.r.p.k) *
        (x.r.c.n + 1) ^ ElOf B1 B2 PolyTab eP := by gcongr; omega

/-- RK's budget. -/
noncomputable def tabCallBud (x : TabCallReq B1 B2 cT) : ℕ :=
  tabCallCost PolyTab PM x (Λf x) (ClOf B1 B2 PolyTab CP eP) (ElOf B1 B2 PolyTab eP)

end Log

/-! ## The machine -/

/-- RK's word function for a prefix machine with an explicit class. -/
noncomputable def tabCallWF {B1 B2 cT : ℕ} (PolyTab : TabMachine) (hord : ∀ R, PolyTab.order R = printerOrder R.s)
    (PM : PrefixMachine B1 B2 cT) (CP eP : ℕ)
    (hPM : ∀ r, PM.budget r ≤ CP * 2 ^ r.p.k * ((cellInput r).length + 1) ^ eP) :
    WordFunction (TabCallReq B1 B2 cT) tabCallInput (tabCallOutput PolyTab) (tabCallBud PolyTab PM CP eP) :=
  wordFunction_of_wmx (tabCallProg PolyTab PM (ClOf B1 B2 PolyTab CP eP) (ElOf B1 B2 PolyTab eP)) (tabCallOut PolyTab PM) (tabCallOut_ne PolyTab PM)
    (fun x => capf x (ClOf B1 B2 PolyTab CP eP) (ElOf B1 B2 PolyTab eP))
    (fun x => tabCall_run PolyTab PM x (Λf x) _ _ _ (ahyp_of x _ _) (bcond_of x _ _) (pm_log PolyTab PM CP eP hPM x)
      (polyTab_log PolyTab CP eP x) (hord _))

end NearCubicGates.Close.CounterMachine.TabCallProg
