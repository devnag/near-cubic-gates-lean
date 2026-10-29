import SourceAdapters.Refuter.RMachReq
import SourceAdapters.Refuter.RRealization

/-!
# One round of R's search, in binary (input 7, R: STEP's arithmetic)

Paper anchor: (`lem:multitape-refuter` Step 4: the binary searches of [CLW20, Cor. 4.5] and
the least-hit search, `O(N)` adaptive queries; `N`-bit numbers are handled in binary, polynomially in `T(N)`).

`arith` updates the stored search state (`LO HI FU` in binary of width `W = g+2`, the phase flags
`P0 P1 P3`, the bit `ELO`) by one `round` of the protocol of `RSearch.lean` with the oracle's answer in
`ANS`; on an end of the search it sets `FIN` and leaves the selected index in `LO` (`arith_spec`).
-/

namespace NearCubicGates.Adapters.Refuter.RM

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicGates.Close.WordPrograms NearCubicGates.Adapters.Refuter
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {tc tT : ℕ} (cap W : ℕ)

local notation "WS" => WState (NS tc tT) NR

/-! ## Binary operations on the layout -/

section Ops
variable {cap W}

def cp (A B : Fin (NS tc tT + 1)) : WMX (NS tc tT) NR := BinW.copy A B bF bR
def ad (A B : Fin (NS tc tT + 1)) : WMX (NS tc tT) NR := BinW.add A B bF bR
def sb (A B : Fin (NS tc tT + 1)) : WMX (NS tc tT) NR := BinW.sub A B bF bR
def hf (A : Fin (NS tc tT + 1)) : WMX (NS tc tT) NR := BinW.half A bR
def lt (A B : Fin (NS tc tT + 1)) (F : Fin NR) : WMX (NS tc tT) NR := BinW.lt A B F bR

theorem wr1 (X : Fin (NS tc tT + 1)) (b x : Bool) (σ : WS) (hX : σ.st X = [x]) (hh : σ.sh X = 0) :
    WXExec cap (WMX.wr X b) σ (σ.sets X [b]) 1 := by
  have := WXExec.wr cap X b σ
  rwa [hX, hh] at this

theorem cp_spec (A B : Fin (NS tc tT + 1)) (hAB : A ≠ B) (σ : WS) (a b : ℕ) (hA : σ.st A = num W a)
    (hB : σ.st B = num W b) (hsh : ∀ i, σ.sh i = 0) (hF : σ.val bF = 0) (hR : σ.val bR = 0)
    (hcap : 2 * W + 1 ≤ cap) : WXExec cap (cp A B) σ (σ.sets A (num W b)) (41 * W + 3) :=
  BinW.copy_spec cap W hAB (by decide) σ a b ⟨hA, hsh A⟩ ⟨hB, hsh B⟩ hF hR hcap

theorem ad_spec (A B : Fin (NS tc tT + 1)) (hAB : A ≠ B) (σ : WS) (a b : ℕ) (hA : σ.st A = num W a)
    (hB : σ.st B = num W b) (hsh : ∀ i, σ.sh i = 0) (hF : σ.val bF = 0) (hR : σ.val bR = 0)
    (hab : a + b < 2 ^ W) (hcap : 2 * W + 1 ≤ cap) :
    WXExec cap (ad A B) σ (σ.sets A (num W (a + b))) (41 * W + 3) :=
  BinW.add_spec cap W hAB (by decide) σ a b ⟨hA, hsh A⟩ ⟨hB, hsh B⟩ hF hR hab hcap

theorem sb_spec (A B : Fin (NS tc tT + 1)) (hAB : A ≠ B) (σ : WS) (a b : ℕ) (hA : σ.st A = num W a)
    (hB : σ.st B = num W b) (hsh : ∀ i, σ.sh i = 0) (hF : σ.val bF = 0) (hR : σ.val bR = 0)
    (hba : b ≤ a) (ha : a < 2 ^ W) (hcap : 2 * W + 1 ≤ cap) :
    WXExec cap (sb A B) σ (σ.sets A (num W (a - b))) (41 * W + 9) :=
  BinW.sub_spec cap W hAB (by decide) σ a b ⟨hA, hsh A⟩ ⟨hB, hsh B⟩ hF hR hba ha hcap

theorem hf_spec (A : Fin (NS tc tT + 1)) (σ : WS) (a : ℕ) (hA : σ.st A = num W a) (hsh : ∀ i, σ.sh i = 0)
    (hR : σ.val bR = 0) (ha : a < 2 ^ W) (hcap : 2 * W + 1 ≤ cap) :
    WXExec cap (hf A) σ (σ.sets A (num W (a / 2))) (34 * W + 3) :=
  BinW.half_spec cap W (A := A) (R := bR) σ a ⟨hA, hsh A⟩ hR ha (by omega)

theorem lt_spec (A B : Fin (NS tc tT + 1)) (hAB : A ≠ B) (F : Fin NR) (hFR : F ≠ bR) (σ : WS) (a b : ℕ)
    (hA : σ.st A = num W a) (hB : σ.st B = num W b) (hsh : ∀ i, σ.sh i = 0) (hF : σ.val F = 0)
    (hR : σ.val bR = 0) (ha : a < 2 ^ W) (hb : b < 2 ^ W) (hcap : 2 * W + 1 ≤ cap) :
    WXExec cap (lt A B F) σ (σ.setv F (decide (a < b)).toNat) (41 * W + 3) :=
  BinW.lt_spec cap W hAB hFR σ a b ⟨hA, hsh A⟩ ⟨hB, hsh B⟩ hF hR ha hb hcap

end Ops

/-! ## The programs -/

/-- Phase 0 → 1: pose `M(x_0)`. -/
def a0 : WMX (NS tc tT) NR := .seq (WMX.wr sP0 false) (WMX.wr sP1 true)

/-- Phase 1: absorb `M(x_0)`; start the least-hit search (`P3`) or the chain search. -/
def a1 : WMX (NS tc tT) NR :=
  .seq (WMX.wr sP1 false) (.seq (.ifs sANS (WMX.wr sP3 true) WMX.skip) (.seq (cp sLO sZ)
    (.seq (cp sHI sSV) (.seq (cp sFU sFF) (WMX.wr sELO false)))))

/-- One bisection step: `Q := (lo+hi)/2`, move the end that the answer selects, `fuel -= 1`. -/
def bis : WMX (NS tc tT) NR :=
  .seq (cp sQ sLO) (.seq (ad sQ sHI) (.seq (hf sQ) (.seq (.ifs sANS (.ifs sELO (cp sLO sQ) (cp sHI sQ))
    (.ifs sELO (cp sHI sQ) (cp sLO sQ))) (sb sFU sONE))))

/-- The least-hit search ended: start the final chain search on `[0, lo+1)`, or finish. -/
def ph4 : WMX (NS tc tT) NR :=
  .seq (WMX.wr sP3 false) (.seq (cp sHI sTMP) (.seq (cp sLO sZ) (.seq (cp sFU sFF) (WMX.wr sELO true))))

def fin : WMX (NS tc tT) NR := WMX.wr sFIN true

def ended : WMX (NS tc tT) NR :=
  .ifs sP3 (.seq (lt sZ sLO rF) (.ifr rF (.seq (WMX.dec rF) ph4) fin)) fin

/-- Settle: continue while `fuel ≠ 0` and `lo + 1 < hi`. -/
def settleP : WMX (NS tc tT) NR :=
  .seq (cp sTMP sLO) (.seq (ad sTMP sONE) (.seq (lt sTMP sHI rF) (.seq (lt sZ sFU rF2)
    (.ifr rF (.ifr rF2 (.seq (WMX.dec rF) (WMX.dec rF2)) (.seq (WMX.dec rF) ended))
      (.ifr rF2 (.seq (WMX.dec rF2) ended) ended)))))

/-- **One round of the search.** -/
def arith : WMX (NS tc tT) NR := .ifs sP0 a0 (.ifs sP1 a1 (.seq bis settleP))

/-- Equalities of word states on the layout. -/
macro "wsl" : tactic => `(tactic| (apply WState.eq <;> (try funext x) <;>
  simp only [WState.setv_sh, WState.seth_sh, WState.sets_sh, WState.setc_sh, WState.setv_st, WState.seth_st,
    WState.sets_st, WState.setc_st, WState.setv_val, WState.seth_val, WState.sets_val, WState.setc_val,
    WState.setv_cell, WState.seth_cell, WState.sets_cell, WState.setc_cell, Function.update_apply] <;>
  (try split_ifs) <;> (try subst_vars) <;> simp_all [Fin.ext_iff] <;> omega))

/-! ## Specs -/

section Specs
variable {cap W}

theorem bis_spec (σ : WS) (lo hi fu vq : ℕ) (β e : Bool)
    (hLO : σ.st sLO = num W lo) (hHI : σ.st sHI = num W hi) (hFU : σ.st sFU = num W fu)
    (hQ : σ.st sQ = num W vq) (hONE : σ.st sONE = num W 1) (hANS : σ.st sANS = [β])
    (hELO : σ.st sELO = [e]) (hsh : ∀ i, σ.sh i = 0) (hF : σ.val bF = 0) (hR : σ.val bR = 0)
    (hlh : lo + hi < 2 ^ W) (hfu : 1 ≤ fu) (hfuW : fu < 2 ^ W) (hcap : 2 * W + 1 ≤ cap) :
    WXExec cap bis σ ((((σ.sets sQ (num W ((lo + hi) / 2))).sets sLO
      (num W (if β = e then (lo + hi) / 2 else lo))).sets sHI
      (num W (if β = e then hi else (lo + hi) / 2))).sets sFU (num W (fu - 1))) (200 * W + 30) := by
  have e1 := cp_spec (cap := cap) sQ sLO (by ds) σ vq lo hQ hLO hsh hF hR hcap
  have e2 := ad_spec (cap := cap) sQ sHI (by ds) (σ.sets sQ (num W lo)) lo hi (by simp)
    (by simp [Function.update_apply, Fin.ext_iff, hHI]) (by simp [hsh]) (by simp [hF]) (by simp [hR]) hlh hcap
  have e3 := hf_spec (cap := cap) sQ ((σ.sets sQ (num W lo)).sets sQ (num W (lo + hi))) (lo + hi) (by simp)
    (by simp [hsh]) (by simp [hR]) hlh hcap
  set σ3 := ((σ.sets sQ (num W lo)).sets sQ (num W (lo + hi))).sets sQ (num W ((lo + hi) / 2)) with hσ3
  have hq : (lo + hi) / 2 < 2 ^ W := lt_of_le_of_lt (Nat.div_le_self _ _) hlh
  have cLO := cp_spec (cap := cap) sLO sQ (by ds) σ3 lo ((lo + hi) / 2)
    (by simp [σ3, Function.update_apply, Fin.ext_iff, hLO]) (by simp [σ3]) (by simp [σ3, hsh]) (by simp [σ3, hF])
    (by simp [σ3, hR]) hcap
  have cHI := cp_spec (cap := cap) sHI sQ (by ds) σ3 hi ((lo + hi) / 2)
    (by simp [σ3, Function.update_apply, Fin.ext_iff, hHI]) (by simp [σ3]) (by simp [σ3, hsh]) (by simp [σ3, hF])
    (by simp [σ3, hR]) hcap
  have hA : wbit σ3 sANS = β := by simp [σ3, wbit, Function.update_apply, Fin.ext_iff, hANS, hsh, readTapeBit]
  have hE : wbit σ3 sELO = e := by simp [σ3, wbit, Function.update_apply, Fin.ext_iff, hELO, hsh, readTapeBit]
  have e4 : WXExec cap (.ifs sANS (.ifs sELO (cp sLO sQ) (cp sHI sQ)) (.ifs sELO (cp sHI sQ) (cp sLO sQ))) σ3
      ((σ3.sets sLO (num W (if β = e then (lo + hi) / 2 else lo))).sets sHI
        (num W (if β = e then hi else (lo + hi) / 2))) (41 * W + 5) := by
    have hh : σ3.st sHI = num W hi := by simp [σ3, Function.update_apply, Fin.ext_iff, hHI]
    have hl : σ3.st sLO = num W lo := by simp [σ3, Function.update_apply, Fin.ext_iff, hLO]
    cases β <;> cases e
    · refine WXExec.ifsF (by rw [hA]) (WXExec.ifsF (by rw [hE]) cLO) |>.cast cap ?_ le_rfl
      rw [if_pos rfl, if_pos rfl]
      exact (BinW.sets_same (by simp [Function.update_apply, Fin.ext_iff, hh] :
        (σ3.sets sLO (num W ((lo + hi) / 2))).st sHI = num W hi)).symm
    · refine WXExec.ifsF (by rw [hA]) (WXExec.ifsT (by rw [hE]) cHI) |>.cast cap ?_ le_rfl
      simp only [Bool.false_eq_true, if_false]; rw [BinW.sets_same hl]
    · refine WXExec.ifsT (by rw [hA]) (WXExec.ifsF (by rw [hE]) cHI) |>.cast cap ?_ le_rfl
      simp only [Bool.true_eq_false, if_false]; rw [BinW.sets_same hl]
    · refine WXExec.ifsT (by rw [hA]) (WXExec.ifsT (by rw [hE]) cLO) |>.cast cap ?_ le_rfl
      rw [if_pos rfl, if_pos rfl]
      exact (BinW.sets_same (by simp [Function.update_apply, Fin.ext_iff, hh] :
        (σ3.sets sLO (num W ((lo + hi) / 2))).st sHI = num W hi)).symm
  set σ4 := (σ3.sets sLO (num W (if β = e then (lo + hi) / 2 else lo))).sets sHI
    (num W (if β = e then hi else (lo + hi) / 2)) with hσ4
  have e5 := sb_spec (cap := cap) sFU sONE (by ds) σ4 fu 1 (by simp [σ4, σ3, Function.update_apply, Fin.ext_iff, hFU])
    (by simp [σ4, σ3, Function.update_apply, Fin.ext_iff, hONE]) (by simp [σ4, σ3, hsh]) (by simp [σ4, σ3, hF])
    (by simp [σ4, σ3, hR]) hfu hfuW hcap
  refine (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4 e5)))).cast cap ?_ (by omega)
  simp only [σ4, σ3]
  wsl

/-- The state after the final chain search is started (phase 4: `[0, lo+1)`, fuel `F`, end value `1`). -/
def ph4St (σ : WS) (W lo F : ℕ) : WS :=
  ((((σ.sets sP3 [false]).sets sHI (num W (lo + 1))).sets sLO (num W 0)).sets sFU (num W F)).sets sELO [true]

theorem ph4_spec (σ : WS) (lo F hh fu : ℕ) (e : Bool) (hLO : σ.st sLO = num W lo) (hHI : σ.st sHI = num W hh)
    (hFU : σ.st sFU = num W fu) (hTMP : σ.st sTMP = num W (lo + 1)) (hZ : σ.st sZ = num W 0)
    (hFF : σ.st sFF = num W F) (hP3 : σ.st sP3 = [true]) (hELO : σ.st sELO = [e])
    (hsh : ∀ i, σ.sh i = 0) (hF : σ.val bF = 0) (hR : σ.val bR = 0) (hcap : 2 * W + 1 ≤ cap) :
    WXExec cap ph4 σ (ph4St σ W lo F) (123 * W + 15) := by
  have e1 := wr1 (cap := cap) sP3 false true σ hP3 (hsh _)
  have e2 := cp_spec (cap := cap) sHI sTMP (by ds) (σ.sets sP3 [false]) hh (lo + 1)
    (by simp [Function.update_apply, Fin.ext_iff, hHI]) (by simp [Function.update_apply, Fin.ext_iff, hTMP])
    (by simp [hsh]) (by simp [hF]) (by simp [hR]) hcap
  have e3 := cp_spec (cap := cap) sLO sZ (by ds) ((σ.sets sP3 [false]).sets sHI (num W (lo + 1))) lo 0
    (by simp [Function.update_apply, Fin.ext_iff, hLO]) (by simp [Function.update_apply, Fin.ext_iff, hZ])
    (by simp [hsh]) (by simp [hF]) (by simp [hR]) hcap
  have e4 := cp_spec (cap := cap) sFU sFF (by ds) (((σ.sets sP3 [false]).sets sHI (num W (lo + 1))).sets sLO
    (num W 0)) fu F (by simp [Function.update_apply, Fin.ext_iff, hFU])
    (by simp [Function.update_apply, Fin.ext_iff, hFF]) (by simp [hsh]) (by simp [hF]) (by simp [hR]) hcap
  have e5 := wr1 (cap := cap) sELO true e ((((σ.sets sP3 [false]).sets sHI (num W (lo + 1))).sets sLO
    (num W 0)).sets sFU (num W F)) (by simp [Function.update_apply, Fin.ext_iff, hELO]) (by simp [hsh])
  exact (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4 e5)))).cast cap rfl (by omega)

/-- The outcome of `ended`. -/
def endedSt (σ : WS) (W lo F : ℕ) (p3 : Bool) : WS :=
  if p3 = true ∧ 0 < lo then ph4St σ W lo F else σ.sets sFIN [true]

theorem ended_spec (σ : WS) (lo F hh fu : ℕ) (p3 e : Bool) (hLO : σ.st sLO = num W lo)
    (hHI : σ.st sHI = num W hh) (hFU : σ.st sFU = num W fu) (hTMP : σ.st sTMP = num W (lo + 1))
    (hZ : σ.st sZ = num W 0) (hFF : σ.st sFF = num W F) (hP3 : σ.st sP3 = [p3]) (hELO : σ.st sELO = [e])
    (hFIN : σ.st sFIN = [false]) (hsh : ∀ i, σ.sh i = 0) (hF : σ.val bF = 0) (hR : σ.val bR = 0)
    (hrF : σ.val rF = 0) (hlo : lo < 2 ^ W) (hcap : 2 * W + 1 ≤ cap) :
    WXExec cap ended σ (endedSt σ W lo F p3) (170 * W + 30) := by
  have hfin := wr1 (cap := cap) sFIN true false σ hFIN (hsh _)
  cases p3
  · refine (WXExec.ifsF (by simp [wbit, hP3, hsh, readTapeBit]) hfin).cast cap ?_ (by omega)
    simp [endedSt]
  · have e1 := lt_spec (cap := cap) sZ sLO (by ds) rF (by decide) σ 0 lo hZ hLO hsh hrF hR (by positivity) hlo hcap
    rcases Nat.eq_zero_or_pos lo with h0 | hpos
    · subst h0
      have e2 : WXExec cap (.ifr rF (.seq (WMX.dec rF) ph4) fin) (σ.setv rF (decide (0 < 0)).toNat)
          (σ.sets sFIN [true]) 2 := by
        have : σ.setv rF (decide (0 < 0)).toNat = σ := by simp; exact BinW.setv_same hrF
        rw [this]; exact WXExec.ifrF hrF hfin
      refine (WXExec.ifsT (by simp [wbit, hP3, hsh, readTapeBit]) (WXExec.seq e1 e2)).cast cap ?_ (by omega)
      simp [endedSt]
    · have hv : (σ.setv rF (decide (0 < lo)).toNat).val rF = 1 := by simp [hpos]
      have d1 := WXExec.dec cap rF (σ.setv rF (decide (0 < lo)).toNat) (by rw [hv]; omega)
      have hσ : (σ.setv rF (decide (0 < lo)).toNat).setv rF ((σ.setv rF (decide (0 < lo)).toNat).val rF - 1) = σ := by
        rw [hv]; wsl
      rw [hσ] at d1
      have e3 := ph4_spec (cap := cap) σ lo F hh fu e hLO hHI hFU hTMP hZ hFF hP3 hELO hsh hF hR hcap
      refine (WXExec.ifsT (by simp [wbit, hP3, hsh, readTapeBit]) (WXExec.seq e1
        (WXExec.ifrT (by rw [hv]; omega) (WXExec.seq d1 e3)))).cast cap ?_ (by omega)
      simp [endedSt, hpos]

theorem regs_back (ρ : WS) (h1 : ρ.val rF = 0) (h2 : ρ.val rF2 = 0) :
    ((((ρ.setv rF 1).setv rF2 1).setv rF (((ρ.setv rF 1).setv rF2 1).val rF - 1)).setv rF2
      ((((ρ.setv rF 1).setv rF2 1).setv rF (((ρ.setv rF 1).setv rF2 1).val rF - 1)).val rF2 - 1)) = ρ := by
  have n12 : rF ≠ rF2 := by decide
  apply WState.eq
  · rfl
  · rfl
  swap
  · rfl
  funext r
  simp only [WState.setv_val]
  by_cases a : r = rF2
  · subst a; simp [Function.update_of_ne n12, Function.update_of_ne n12.symm, h2]
  · by_cases b : r = rF
    · subst b; simp [Function.update_of_ne n12, h1]
    · simp [Function.update_of_ne a, Function.update_of_ne b]

/-- The outcome of `settleP`. -/
def settleSt (σ : WS) (W lo hi fu F : ℕ) (p3 : Bool) : WS :=
  if fu ≠ 0 ∧ lo + 1 < hi then σ.sets sTMP (num W (lo + 1)) else endedSt (σ.sets sTMP (num W (lo + 1))) W lo F p3

theorem settle_spec (σ : WS) (lo hi fu vt F : ℕ) (p3 e : Bool) (hLO : σ.st sLO = num W lo)
    (hHI : σ.st sHI = num W hi) (hFU : σ.st sFU = num W fu) (hTMP : σ.st sTMP = num W vt)
    (hONE : σ.st sONE = num W 1) (hZ : σ.st sZ = num W 0) (hFF : σ.st sFF = num W F) (hP3 : σ.st sP3 = [p3])
    (hELO : σ.st sELO = [e]) (hFIN : σ.st sFIN = [false]) (hsh : ∀ i, σ.sh i = 0) (hF : σ.val bF = 0)
    (hR : σ.val bR = 0) (hrF : σ.val rF = 0) (hrF2 : σ.val rF2 = 0) (hlo : lo + 1 < 2 ^ W) (hhi : hi < 2 ^ W)
    (hfu : fu < 2 ^ W) (hcap : 2 * W + 1 ≤ cap) :
    WXExec cap settleP σ (settleSt σ W lo hi fu F p3) (340 * W + 60) := by
  have e1 := cp_spec (cap := cap) sTMP sLO (by ds) σ vt lo hTMP hLO hsh hF hR hcap
  have e2 := ad_spec (cap := cap) sTMP sONE (by ds) (σ.sets sTMP (num W lo)) lo 1 (by simp)
    (by simp [Function.update_apply, Fin.ext_iff, hONE]) (by simp [hsh]) (by simp [hF]) (by simp [hR]) hlo hcap
  rw [BinW.sets_sets] at e2
  set ρ := σ.sets sTMP (num W (lo + 1)) with hρ
  have e3 := lt_spec (cap := cap) sTMP sHI (by ds) rF (by decide) ρ (lo + 1) hi (by simp [ρ])
    (by simp [ρ, Function.update_apply, Fin.ext_iff, hHI]) (by simp [ρ, hsh]) (by simp [ρ, hrF]) (by simp [ρ, hR])
    hlo hhi hcap
  have e4 := lt_spec (cap := cap) sZ sFU (by ds) rF2 (by decide) (ρ.setv rF (decide (lo + 1 < hi)).toNat) 0 fu
    (by simp [ρ, Function.update_apply, Fin.ext_iff, hZ]) (by simp [ρ, Function.update_apply, Fin.ext_iff, hFU])
    (by simp [ρ, hsh]) (by simp [ρ, Function.update_apply, Fin.ext_iff, hrF2])
    (by simp [ρ, Function.update_apply, Fin.ext_iff, hR]) (by positivity) hfu hcap
  set ρ2 := (ρ.setv rF (decide (lo + 1 < hi)).toNat).setv rF2 (decide (0 < fu)).toNat with hρ2
  have hρ' : ρ.val rF = 0 ∧ ρ.val rF2 = 0 := ⟨by simp [ρ, hrF], by simp [ρ, hrF2]⟩
  have hen := ended_spec (cap := cap) ρ lo F hi fu p3 e (by simp [ρ, Function.update_apply, Fin.ext_iff, hLO])
    (by simp [ρ, Function.update_apply, Fin.ext_iff, hHI]) (by simp [ρ, Function.update_apply, Fin.ext_iff, hFU])
    (by simp [ρ]) (by simp [ρ, Function.update_apply, Fin.ext_iff, hZ])
    (by simp [ρ, Function.update_apply, Fin.ext_iff, hFF]) (by simp [ρ, Function.update_apply, Fin.ext_iff, hP3])
    (by simp [ρ, Function.update_apply, Fin.ext_iff, hELO]) (by simp [ρ, Function.update_apply, Fin.ext_iff, hFIN])
    (by simp [ρ, hsh]) (by simp [ρ, hF]) (by simp [ρ, hR]) hρ'.1 (by omega) hcap
  by_cases c1 : lo + 1 < hi <;> by_cases c2 : 0 < fu
  · -- continue
    have hd : WXExec cap (.seq (WMX.dec rF) (WMX.dec rF2)) ρ2 ρ 3 := by
      have d1 := WXExec.dec cap rF ρ2 (by simp [ρ2, c1, Function.update_apply, Fin.ext_iff]; omega)
      have d2 := WXExec.dec cap rF2 (ρ2.setv rF (ρ2.val rF - 1))
        (by simp [ρ2, c2, Function.update_apply, Fin.ext_iff]; omega)
      refine (WXExec.seq d1 d2).cast cap ?_ (by omega)
      simp only [ρ2, c1, c2, decide_true, Bool.toNat_true]
      exact regs_back ρ hρ'.1 hρ'.2
    refine (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4 (WXExec.ifrT (r := rF)
      (by simp [ρ2, c1, Function.update_apply, Fin.ext_iff])
      (WXExec.ifrT (r := rF2) (by simp [ρ2, c2, Function.update_apply, Fin.ext_iff]) hd)))))).cast cap ?_ (by omega)
    simp only [settleSt, if_pos (show fu ≠ 0 ∧ lo + 1 < hi from ⟨by omega, c1⟩)]
    rfl
  · -- fuel spent
    have d1 := WXExec.dec cap rF ρ2 (by simp [ρ2, c1, Function.update_apply, Fin.ext_iff]; omega)
    have h0 : ρ2.setv rF (ρ2.val rF - 1) = ρ := by simp only [ρ2]; wsl
    rw [h0] at d1
    refine (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4 (WXExec.ifrT (r := rF)
      (by simp [ρ2, c1, Function.update_apply, Fin.ext_iff])
      (WXExec.ifrF (r := rF2) (by simp [ρ2, c2, Function.update_apply, Fin.ext_iff]) (WXExec.seq d1 hen))))))).cast
      cap ?_ (by omega)
    simp only [settleSt, show ¬ (fu ≠ 0 ∧ lo + 1 < hi) by omega, if_false]
    rfl
  · -- interval exhausted
    have d2 := WXExec.dec cap rF2 ρ2 (by simp [ρ2, c2, Function.update_apply, Fin.ext_iff]; omega)
    have h0 : ρ2.setv rF2 (ρ2.val rF2 - 1) = ρ := by simp only [ρ2]; wsl
    rw [h0] at d2
    refine (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4 (WXExec.ifrF (r := rF)
      (by simp [ρ2, c1, Function.update_apply, Fin.ext_iff])
      (WXExec.ifrT (r := rF2) (by simp [ρ2, c2, Function.update_apply, Fin.ext_iff]) (WXExec.seq d2 hen))))))).cast
      cap ?_ (by omega)
    simp only [settleSt, show ¬ (fu ≠ 0 ∧ lo + 1 < hi) by omega, if_false]
    rfl
  · -- both
    have h0 : ρ2 = ρ := by simp only [ρ2]; wsl
    rw [h0] at e4
    refine (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4 (WXExec.ifrF (r := rF) hρ'.1
      (WXExec.ifrF (r := rF2) hρ'.2 hen)))))).cast cap ?_ (by omega)
    simp only [settleSt, show ¬ (fu ≠ 0 ∧ lo + 1 < hi) by omega, if_false]
    rfl

theorem a0_spec (σ : WS) (x : Bool) (hP0 : σ.st sP0 = [true]) (hP1 : σ.st sP1 = [x]) (hsh : ∀ i, σ.sh i = 0) :
    WXExec cap a0 σ ((σ.sets sP0 [false]).sets sP1 [true]) 3 := by
  have e1 := wr1 (cap := cap) sP0 false true σ hP0 (hsh _)
  have e2 := wr1 (cap := cap) sP1 true x (σ.sets sP0 [false]) (by simp [Function.update_apply, Fin.ext_iff, hP1])
    (by simp [hsh])
  exact (WXExec.seq e1 e2).cast cap rfl (by omega)

/-- The outcome of `a1`. -/
def a1St (σ : WS) (W s F : ℕ) (β : Bool) : WS :=
  (((((σ.sets sP1 [false]).sets sP3 [β]).sets sLO (num W 0)).sets sHI (num W s)).sets sFU (num W F)).sets sELO [false]

theorem a1_spec (σ : WS) (lo hi fu s F : ℕ) (β e : Bool) (hP1 : σ.st sP1 = [true]) (hP3 : σ.st sP3 = [false])
    (hANS : σ.st sANS = [β]) (hLO : σ.st sLO = num W lo) (hHI : σ.st sHI = num W hi) (hFU : σ.st sFU = num W fu)
    (hZ : σ.st sZ = num W 0) (hSV : σ.st sSV = num W s) (hFF : σ.st sFF = num W F) (hELO : σ.st sELO = [e])
    (hsh : ∀ i, σ.sh i = 0) (hF : σ.val bF = 0) (hR : σ.val bR = 0) (hcap : 2 * W + 1 ≤ cap) :
    WXExec cap a1 σ (a1St σ W s F β) (123 * W + 20) := by
  have e1 := wr1 (cap := cap) sP1 false true σ hP1 (hsh _)
  have e2 : WXExec cap (.ifs sANS (WMX.wr sP3 true) WMX.skip) (σ.sets sP1 [false]) ((σ.sets sP1 [false]).sets sP3 [β]) 2 := by
    cases β
    · refine (WXExec.ifsF (by simp [wbit, Function.update_apply, Fin.ext_iff, hANS, hsh, readTapeBit])
        (WXExec.skip cap _)).cast cap ?_ (by omega)
      exact (BinW.sets_same (by simp [Function.update_apply, Fin.ext_iff, hP3])).symm
    · exact (WXExec.ifsT (by simp [wbit, Function.update_apply, Fin.ext_iff, hANS, hsh, readTapeBit])
        (wr1 (cap := cap) sP3 true false _ (by simp [Function.update_apply, Fin.ext_iff, hP3]) (by simp [hsh]))).mono
        (by omega)
  set τ := (σ.sets sP1 [false]).sets sP3 [β] with hτ
  have e3 := cp_spec (cap := cap) sLO sZ (by ds) τ lo 0 (by simp [τ, Function.update_apply, Fin.ext_iff, hLO])
    (by simp [τ, Function.update_apply, Fin.ext_iff, hZ]) (by simp [τ, hsh]) (by simp [τ, hF]) (by simp [τ, hR]) hcap
  have e4 := cp_spec (cap := cap) sHI sSV (by ds) (τ.sets sLO (num W 0)) hi s
    (by simp [τ, Function.update_apply, Fin.ext_iff, hHI]) (by simp [τ, Function.update_apply, Fin.ext_iff, hSV])
    (by simp [τ, hsh]) (by simp [τ, hF]) (by simp [τ, hR]) hcap
  have e5 := cp_spec (cap := cap) sFU sFF (by ds) ((τ.sets sLO (num W 0)).sets sHI (num W s)) fu F
    (by simp [τ, Function.update_apply, Fin.ext_iff, hFU]) (by simp [τ, Function.update_apply, Fin.ext_iff, hFF])
    (by simp [τ, hsh]) (by simp [τ, hF]) (by simp [τ, hR]) hcap
  have e6 := wr1 (cap := cap) sELO false e (((τ.sets sLO (num W 0)).sets sHI (num W s)).sets sFU (num W F))
    (by simp [τ, Function.update_apply, Fin.ext_iff, hELO]) (by simp [τ, hsh])
  exact (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4 (WXExec.seq e5 e6))))).cast cap rfl (by omega)

/-! ## One round against the protocol -/

/-- The stored search state. -/
structure SRep (W : ℕ) (σ : WS) (S : SS) : Prop where
  lo : σ.st sLO = num W S.lo
  hi : σ.st sHI = num W S.hi
  fu : σ.st sFU = num W S.fuel
  p0 : σ.st sP0 = [decide (S.ph = 0)]
  p1 : σ.st sP1 = [decide (S.ph = 1)]
  p3 : σ.st sP3 = [decide (S.ph = 3)]
  elo : σ.st sELO = [S.elo]

/-- The streams `arith` may change. -/
def AL : List (Fin (NS tc tT + 1)) := [sLO, sHI, sFU, sP0, sP1, sP3, sELO, sQ, sTMP, sFIN]

/-- Unchanged outside `AL`, heads, registers and the cell unchanged. -/
def AFrame (σ τ : WS) : Prop :=
  (∀ i, i ∉ AL → τ.st i = σ.st i) ∧ τ.sh = σ.sh ∧ τ.val = σ.val ∧ τ.cell = σ.cell

theorem AFrame.refl (σ : WS) : AFrame σ σ := ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem AFrame.sets {σ τ : WS} (h : AFrame σ τ) (X : Fin (NS tc tT + 1)) (hX : X ∈ AL) (l : List Bool) :
    AFrame σ (τ.sets X l) := by
  refine ⟨fun i hi => ?_, h.2.1, h.2.2.1, h.2.2.2⟩
  have : i ≠ X := fun e => hi (e ▸ hX)
  simp only [WState.sets_st, Function.update_of_ne this]
  exact h.1 i hi

/-- What a round leaves: the next state, or the selected index in `LO` with `FIN` set. -/
def ROut (W F : ℕ) (τ : WS) : SS ⊕ ℕ → Prop
  | .inl S' => SRep W τ S' ∧ τ.st sFIN = [false] ∧ S'.fuel ≤ F
  | .inr p => τ.st sLO = num W p ∧ τ.st sFIN = [true]

theorem pow_facts (g : ℕ) : g + 1 < 2 ^ (g + 2) ∧ 2 ^ (g + 2) = 4 * 2 ^ g ∧ 1 ≤ 2 ^ g := by
  refine ⟨?_, by ring, Nat.one_le_two_pow⟩
  have := Nat.lt_two_pow_self (n := g + 2); omega

macro "inAL" : tactic => `(tactic| simp [AL])

/-- **One round of the search is computed.** -/
theorem arith_spec (g : ℕ) (hg : 1 ≤ g) (hcap : 2 * (g + 2) + 1 ≤ cap) (σ : WS) (S : SS) (β : Bool) (vq vt : ℕ)
    (hS : SRep (g + 2) σ S) (hfuel : S.fuel ≤ g + 1) (hgood : Good (2 ^ g) S)
    (hZ : σ.st sZ = num (g + 2) 0) (hONE : σ.st sONE = num (g + 2) 1) (hSV : σ.st sSV = num (g + 2) (2 ^ g))
    (hFF : σ.st sFF = num (g + 2) (g + 1)) (hANS : σ.st sANS = [β]) (hFIN : σ.st sFIN = [false])
    (hQ : σ.st sQ = num (g + 2) vq) (hTMP : σ.st sTMP = num (g + 2) vt) (hsh : ∀ i, σ.sh i = 0)
    (hbF : σ.val bF = 0) (hbR : σ.val bR = 0) (hrF : σ.val rF = 0) (hrF2 : σ.val rF2 = 0) :
    ∃ τ, WXExec cap arith σ τ (600 * (g + 2) + 100) ∧ AFrame σ τ ∧ (∃ v, τ.st sQ = num (g + 2) v) ∧
      (∃ v, τ.st sTMP = num (g + 2) v) ∧ ROut (g + 2) (g + 1) τ (round (2 ^ g) (g + 1) S β) := by
  obtain ⟨hp1, hp2, hp3⟩ := pow_facts g
  rcases hgood with rfl | ⟨hP, hR⟩
  · -- fresh
    have e := a0_spec (cap := cap) σ false (by rw [hS.p0]; rfl) (by rw [hS.p1]; rfl) hsh
    refine ⟨_, (WXExec.ifsT (by simp [wbit, hS.p0, hsh, readTapeBit, SS.fresh]) e).mono (by omega),
      (AFrame.refl σ).sets _ (by inAL) _ |>.sets _ (by inAL) _,
      ⟨vq, by simp [Function.update_apply, Fin.ext_iff, hQ]⟩, ⟨vt, by simp [Function.update_apply, Fin.ext_iff, hTMP]⟩, ?_⟩
    rw [fresh_round]
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, by simp [Function.update_apply, Fin.ext_iff, hFIN], by simp [SS.first]⟩ <;>
      simp [Function.update_apply, Fin.ext_iff, hS.lo, hS.hi, hS.fu, hS.p3, hS.elo, SS.first, SS.fresh]
  · have hph0 : S.ph ≠ 0 := by rcases hP with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
    have hwP0 : wbit σ sP0 = false := by simp [wbit, hS.p0, hsh, readTapeBit, hph0]
    rcases hP with ⟨h1, hlo0, hhi0⟩ | ⟨hph, hfu0, hlh⟩
    · -- phase 1
      have e := a1_spec (cap := cap) (W := g + 2) σ S.lo S.hi S.fuel (2 ^ g) (g + 1) β S.elo
        (by rw [hS.p1, h1]; rfl) (by rw [hS.p3, h1]; rfl) hANS hS.lo hS.hi hS.fu hZ hSV hFF hS.elo hsh hbF hbR hcap
      refine ⟨_, (WXExec.ifsF hwP0 (WXExec.ifsT (by simp [wbit, hS.p1, hsh, readTapeBit, h1]) e)).mono (by omega),
        ?_, ⟨vq, ?_⟩, ⟨vt, ?_⟩, ?_⟩
      · exact (((((((AFrame.refl σ).sets _ (by inAL) _).sets _ (by inAL) _).sets _ (by inAL) _).sets _ (by inAL) _).sets
          _ (by inAL) _).sets _ (by inAL) _)
      · simp [a1St, Function.update_apply, Fin.ext_iff, hQ]
      · simp [a1St, Function.update_apply, Fin.ext_iff, hTMP]
      · have hr : round (2 ^ g) (g + 1) S β = .inl ⟨if β then 3 else 2, 0, 2 ^ g, g + 1, false⟩ := by
          have h2 : 2 ≤ 2 ^ g := by
            calc 2 = 2 ^ 1 := rfl
              _ ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num) hg
          simp only [round, hph0, if_false, absorb, h1, if_true]
          cases β <;> simp [settle] <;> omega
        rw [hr]
        refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, by simp [a1St, Function.update_apply, Fin.ext_iff, hFIN], by simp⟩ <;>
          cases β <;> simp [a1St, Function.update_apply, Fin.ext_iff, hS.p0, h1]
    · -- phases 2, 3, 4
      have hn1 : S.ph ≠ 1 := by omega
      have hfu1 : 1 ≤ S.fuel := by omega
      have hlh2 : S.lo + S.hi < 2 ^ (g + 2) := by have := hR.2.1; have := hR.1; omega
      have eb := bis_spec (cap := cap) (W := g + 2) σ S.lo S.hi S.fuel vq β S.elo hS.lo hS.hi hS.fu hQ hONE hANS
        hS.elo hsh hbF hbR hlh2 hfu1 (by omega) hcap
      set q := (S.lo + S.hi) / 2 with hq
      set lo' := if β = S.elo then q else S.lo with hlo'
      set hi' := if β = S.elo then S.hi else q with hhi'
      set σb := (((σ.sets sQ (num (g + 2) q)).sets sLO (num (g + 2) lo')).sets sHI (num (g + 2) hi')).sets sFU
        (num (g + 2) (S.fuel - 1)) with hσb
      have hq1 : S.lo < q := by omega
      have hq2 : q < S.hi := by omega
      have hlo'b : lo' + 1 < 2 ^ (g + 2) := by have := hR.2.1; simp only [hlo']; split_ifs <;> omega
      have hhi'b : hi' < 2 ^ (g + 2) := by have := hR.2.1; simp only [hhi']; split_ifs <;> omega
      have es := settle_spec (cap := cap) (W := g + 2) σb lo' hi' (S.fuel - 1) vt (g + 1) (decide (S.ph = 3)) S.elo
        (by simp [σb, Function.update_apply, Fin.ext_iff]) (by simp [σb, Function.update_apply, Fin.ext_iff])
        (by simp [σb, Function.update_apply, Fin.ext_iff]) (by simp [σb, Function.update_apply, Fin.ext_iff, hTMP])
        (by simp [σb, Function.update_apply, Fin.ext_iff, hONE]) (by simp [σb, Function.update_apply, Fin.ext_iff, hZ])
        (by simp [σb, Function.update_apply, Fin.ext_iff, hFF]) (by simp [σb, Function.update_apply, Fin.ext_iff, hS.p3])
        (by simp [σb, Function.update_apply, Fin.ext_iff, hS.elo]) (by simp [σb, Function.update_apply, Fin.ext_iff, hFIN])
        (by simp [σb, hsh]) (by simp [σb, hbF]) (by simp [σb, hbR]) (by simp [σb, hrF]) (by simp [σb, hrF2])
        hlo'b hhi'b (by omega) hcap
      have hwP1 : wbit σ sP1 = false := by simp [wbit, hS.p1, hsh, readTapeBit, hn1]
      refine ⟨_, (WXExec.ifsF hwP0 (WXExec.ifsF hwP1 (WXExec.seq eb es))).mono (by omega), ?_, ?_, ?_, ?_⟩
      · have hb : AFrame σ σb := ((((AFrame.refl σ).sets _ (by inAL) _).sets _ (by inAL) _).sets _ (by inAL) _).sets
          _ (by inAL) _
        have hb2 : AFrame σ (σb.sets sTMP (num (g + 2) (lo' + 1))) := hb.sets _ (by inAL) _
        simp only [settleSt, endedSt, ph4St]
        split_ifs
        · exact hb2
        · exact ((((hb2.sets _ (by inAL) _).sets _ (by inAL) _).sets _ (by inAL) _).sets _ (by inAL) _).sets _ (by inAL) _
        · exact hb2.sets _ (by inAL) _
      · refine ⟨q, ?_⟩
        simp only [settleSt, endedSt, ph4St]
        split_ifs <;> simp [σb, Function.update_apply, Fin.ext_iff]
      · simp only [settleSt, endedSt, ph4St]
        split_ifs
        · exact ⟨lo' + 1, by simp⟩
        · exact ⟨lo' + 1, by simp [Function.update_apply, Fin.ext_iff]⟩
        · exact ⟨lo' + 1, by simp [Function.update_apply, Fin.ext_iff]⟩
      · -- the protocol's round
        have hT : absorb (2 ^ g) (g + 1) S β = ⟨S.ph, lo', hi', S.fuel - 1, S.elo⟩ := by
          simp only [absorb, hn1, if_false, SS.q, hlo', hhi', hq]
          split_ifs <;> rfl
        have hr : round (2 ^ g) (g + 1) S β = settle (g + 1) ⟨S.ph, lo', hi', S.fuel - 1, S.elo⟩ := by
          simp only [round, hph0, if_false, hT]
        rw [hr]
        simp only [settle, settleSt, endedSt, ph4St]
        by_cases hc : S.fuel - 1 ≠ 0 ∧ lo' + 1 < hi'
        · rw [if_neg (show ¬ (S.fuel - 1 = 0 ∨ hi' ≤ lo' + 1) by omega), if_pos hc]
          refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, show S.fuel - 1 ≤ g + 1 by omega⟩ <;>
            simp [σb, Function.update_apply, Fin.ext_iff, hS.p0, hS.p1, hS.p3, hS.elo, hFIN]
        · have hc' : S.fuel - 1 = 0 ∨ hi' ≤ lo' + 1 := by
            by_contra h; exact hc ⟨fun h0 => h (Or.inl h0), by omega⟩
          rw [if_pos hc', if_neg hc]
          by_cases h3 : S.ph = 3
          · by_cases hl : 0 < lo'
            · rw [if_pos h3, if_neg (show ¬ (g + 1 = 0 ∨ lo' + 1 ≤ 1) by omega),
                if_pos (show decide (S.ph = 3) = true ∧ 0 < lo' from ⟨by simp [h3], hl⟩)]
              refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, by simp⟩ <;>
                simp [σb, Function.update_apply, Fin.ext_iff, hS.p0, hS.p1, hFIN, h3]
            · rw [if_pos h3, if_pos (show g + 1 = 0 ∨ lo' + 1 ≤ 1 by omega),
                if_neg (show ¬ (decide (S.ph = 3) = true ∧ 0 < lo') by simp [h3]; omega)]
              have hl0 : lo' = 0 := by omega
              refine ⟨?_, by simp [Function.update_apply, Fin.ext_iff]⟩
              rw [← hl0]
              simp [σb, Function.update_apply, Fin.ext_iff]
          · rw [if_neg h3, if_neg (show ¬ (decide (S.ph = 3) = true ∧ 0 < lo') by simp [h3])]
            exact ⟨by simp [σb, Function.update_apply, Fin.ext_iff], by simp [Function.update_apply, Fin.ext_iff]⟩

end Specs

end NearCubicGates.Adapters.Refuter.RM
