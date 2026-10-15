import Proof.Wire_3_5.SelectionMachineSortW
import Proof.Wire_3_5.UnionMachineRoundBits

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.SelectionMachine.Sort
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.UnionMachine.Round (addO addN mapS_add' binary_succ)

variable {ns nr : ℕ}

/-! ## The passes' values -/

/-- The incrementer: sum bit and carry of `a + c` (the second word is ignored). -/
def incO (a _ c : Bool) : Bool := xor a c
def incN (a _ c : Bool) : Bool := a && c

theorem mapS_inc : ∀ (w x : ℕ) (bs : List Bool) (c : Bool), bs.length = w → x < 2 ^ w →
    mapS incO incN (binary w x) bs c = (binary w (x + c.toNat), decide (2 ^ w ≤ x + c.toNat))
  | 0, x, bs, c, hb, hx => by
    have : x = 0 := by simpa using hx
    subst this
    have : bs = [] := List.length_eq_zero_iff.mp hb
    subst this
    cases c <;> rfl
  | w + 1, x, bs, c, hb, hx => by
    obtain ⟨b, bs', rfl⟩ : ∃ b bs', bs = b :: bs' := by
      cases bs with
      | nil => simp at hb
      | cons b bs' => exact ⟨b, bs', rfl⟩
    have hx2 : x / 2 < 2 ^ w := by rw [Nat.pow_succ] at hx; omega
    simp only [binary_succ, mapS]
    rw [mapS_inc w (x / 2) bs' _ (by simpa using hb) hx2]
    have h1 : incO (x % 2 == 1) b c = ((x + c.toNat) % 2 == 1) := by
      rcases Nat.mod_two_eq_zero_or_one x with h | h <;> cases c <;> simp [incO, h, Bool.toNat] <;> omega
    have h2 : x / 2 + (incN (x % 2 == 1) b c).toNat = (x + c.toNat) / 2 := by
      rcases Nat.mod_two_eq_zero_or_one x with h | h <;> cases c <;> simp [incN, h, Bool.toNat] <;> omega
    rw [h1, h2]
    simp only [Prod.mk.injEq, true_and]
    rw [Nat.pow_succ]
    apply decide_eq_decide.mpr
    omega

theorem mapS_add_carry : ∀ (w x y : ℕ) (c : Bool), x < 2 ^ w → y < 2 ^ w →
    (mapS addO addN (binary w x) (binary w y) c).2 = decide (2 ^ w ≤ x + y + c.toNat)
  | 0, x, y, c, hx, hy => by
    have : x = 0 := by simpa using hx
    have : y = 0 := by simpa using hy
    subst_vars
    cases c <;> rfl
  | w + 1, x, y, c, hx, hy => by
    have hx2 : x / 2 < 2 ^ w := by rw [Nat.pow_succ] at hx; omega
    have hy2 : y / 2 < 2 ^ w := by rw [Nat.pow_succ] at hy; omega
    simp only [binary_succ, mapS]
    rw [mapS_add_carry w (x / 2) (y / 2) _ hx2 hy2]
    have h2 : x / 2 + y / 2 + (addN (x % 2 == 1) (y % 2 == 1) c).toNat = (x + y + c.toNat) / 2 := by
      rcases Nat.mod_two_eq_zero_or_one x with h | h <;> rcases Nat.mod_two_eq_zero_or_one y with h' | h' <;>
        cases c <;> simp [addN, h, h', Bool.toNat] <;> omega
    rw [h2, Nat.pow_succ]
    apply decide_eq_decide.mpr
    omega

/-! ## Skipping a frame, from any state -/

theorem skipGen (cap : ℕ) (S : Fin (ns + 1)) (C : Fin nr) : ∀ (bits pre post : List Bool) (σ : WState ns nr),
    σ.st S = pre ++ frameP bits ++ false :: post → σ.sh S = pre.length → σ.val C = pre.length →
    pre.length + 2 * bits.length < cap →
    WExec cap (.whs S (.seq (WM.fwdC S C) (WM.fwdC S C))) σ
      ((σ.seth S (pre.length + 2 * bits.length)).setv C (pre.length + 2 * bits.length)) (13 * bits.length + 1)
  | [], pre, post, σ, hS, hSh, hC, _ => by
    have hbit : wbit σ S = false := by
      simp only [wbit, hS, hSh, frameP_nil, List.append_nil, rd_app0, rd_cons0]
    have e : (σ.seth S (pre.length + 2 * ([] : List Bool).length)).setv C (pre.length + 2 * ([] : List Bool).length)
        = σ := by
      apply WState.eq
      · funext x; simp only [WState.setv_sh, WState.seth_sh, Function.update_apply]
        split_ifs <;> simp_all
      · rfl
      · funext x; simp only [WState.setv_val, WState.seth_val, Function.update_apply]
        split_ifs <;> simp_all
      · rfl
    rw [e]
    exact WExec.whsF hbit
  | b :: bits, pre, post, σ, hS, hSh, hC, hp => by
    have hS2 : σ.st S = pre ++ (true :: b :: (frameP bits ++ false :: post)) := by
      rw [hS, frameP_cons]; simp
    have hS' : σ.st S = (pre ++ [true, b]) ++ frameP bits ++ false :: post := by
      rw [hS, frameP_cons]; simp
    have hbit : wbit σ S = true := by
      simp only [wbit, hS2, hSh, rd_app0, rd_cons0]
    simp only [List.length_cons] at hp
    have f1 := wfwdC_spec cap S C σ (by omega)
    have f2 := wfwdC_spec cap S C ((σ.seth S (σ.sh S + 1)).setv C (σ.val C + 1)) (by simp; omega)
    set σ2 := ((((σ.seth S (σ.sh S + 1)).setv C (σ.val C + 1)).seth S
      (((σ.seth S (σ.sh S + 1)).setv C (σ.val C + 1)).sh S + 1)).setv C
      (((σ.seth S (σ.sh S + 1)).setv C (σ.val C + 1)).val C + 1)) with hσ2
    have h2 := skipGen cap S C bits (pre ++ [true, b]) post σ2 (by simp [hσ2, hS'])
      (by simp [hσ2, hSh]) (by simp [hσ2, hC]) (by simp; omega)
    refine WExec.cast cap (WExec.whsT hbit (WExec.seq f1 f2) h2) ?_ (by simp; omega)
    apply WState.eq
    · funext x; simp only [hσ2, WState.setv_sh, WState.seth_sh, Function.update_apply, List.length_append,
        List.length_cons, List.length_nil]
      split_ifs <;> simp_all <;> omega
    · rfl
    · funext x; simp only [hσ2, WState.setv_val, WState.seth_val, Function.update_apply, List.length_append,
        List.length_cons, List.length_nil]
      split_ifs <;> simp_all <;> omega
    · rfl

/-! ## The ops -/

/-- `CNT := CNT + 1` (the carry starts at `1` in `F`). -/
def incCNT (CNT TOT : Fin (ns + 1)) (F R : Fin nr) : WM ns nr := .seq (.inc F) (mapPass incO incN CNT TOT F R)

/-- `TOT := TOT + CNT`. -/
def addTOT (CNT TOT : Fin (ns + 1)) (F R : Fin nr) : WM ns nr := mapPass addO addN TOT CNT F R

/-- `CNT := 0`. -/
def zeroCNT (CNT TOT : Fin (ns + 1)) (F R : Fin nr) : WM ns nr := mapPass oneOut oneNxt CNT TOT F R

section Ops
variable (cap W : ℕ) {CNT TOT : Fin (ns + 1)} {F R : Fin nr} (hCT : CNT ≠ TOT) (hFR : F ≠ R)
include hCT hFR

theorem incCNT_spec (σ : WState ns nr) (c t : ℕ) (hC : NumOn σ CNT W c) (hT : NumOn σ TOT W t)
    (hF : σ.val F = 0) (hR : σ.val R = 0) (hc : c + 1 < 2 ^ W) (hcap : 2 * W + 1 ≤ cap) :
    WExec cap (incCNT CNT TOT F R) σ (σ.sets CNT (frame (binary W (c + 1)))) (41 * W + 7) := by
  have h1 := WExec.inc (cap := cap) F σ (by omega)
  set σ1 := σ.setv F (σ.val F + 1) with hσ1
  have h2 := mapPass_spec cap incO incN CNT TOT F R hCT hFR (by omega) (binary W c) (binary W t) [] [false] true σ1
    (by simp) (by simp [hσ1, hC.1, frame_eq_frameP]) (by simp [hσ1, hC.2]) (by simp [hσ1, hT.1, frame_eq_frameP])
    (by simp [hσ1, hT.2]) (by simp [hσ1, hF]) (by simp [hσ1, Ne.symm hFR, hR]) (by simp; omega)
  rw [mapS_inc W c (binary W t) true (by simp) (by omega)] at h2
  refine WExec.cast cap (WExec.seq h1 h2) ?_ (by simp; omega)
  apply WState.eq
  · rfl
  · funext x; simp only [hσ1, WState.setv_st, WState.sets_st, Function.update_apply, frame_eq_frameP]
    split_ifs <;> simp_all
  · funext x; simp only [hσ1, WState.setv_val, WState.sets_val, Function.update_apply]
    split_ifs with h <;> subst_vars <;> simp_all
  · rfl

theorem addTOT_spec (σ : WState ns nr) (c t : ℕ) (hC : NumOn σ CNT W c) (hT : NumOn σ TOT W t)
    (hF : σ.val F = 0) (hR : σ.val R = 0) (hct : t + c < 2 ^ W) (hcap : 2 * W + 1 ≤ cap) :
    WExec cap (addTOT CNT TOT F R) σ (σ.sets TOT (frame (binary W (t + c)))) (41 * W + 3) := by
  have h2 := mapPass_spec cap addO addN TOT CNT F R (Ne.symm hCT) hFR (by omega) (binary W t) (binary W c) []
    [false] false σ (by simp) (by simp [hT.1, frame_eq_frameP]) hT.2 (by simp [hC.1, frame_eq_frameP]) hC.2
    (by simp [hF]) hR (by simp; omega)
  rw [mapS_add' W t c false, mapS_add_carry W t c false (by omega) (by omega)] at h2
  refine WExec.cast cap h2 ?_ (by simp; omega)
  apply WState.eq
  · rfl
  · funext x; simp only [WState.setv_st, WState.sets_st, Function.update_apply, frame_eq_frameP]
    split_ifs <;> simp_all
  · funext x; simp only [WState.setv_val, WState.sets_val, Function.update_apply]
    split_ifs with h <;> subst_vars <;> simp_all
  · rfl

theorem zeroCNT_spec (σ : WState ns nr) (c t : ℕ) (hC : NumOn σ CNT W c) (hT : NumOn σ TOT W t)
    (hF : σ.val F = 0) (hR : σ.val R = 0) (hcap : 2 * W + 1 ≤ cap) :
    WExec cap (zeroCNT CNT TOT F R) σ (σ.sets CNT (frame (binary W 0))) (41 * W + 3) := by
  have h2 := mapPass_spec cap oneOut oneNxt CNT TOT F R hCT hFR (by omega) (binary W c) (binary W t) []
    [false] false σ (by simp) (by simp [hC.1, frame_eq_frameP]) hC.2 (by simp [hT.1, frame_eq_frameP]) hT.2
    (by simp [hF]) hR (by simp; omega)
  rw [mapS_zero_state _ _ (by simp)] at h2
  refine WExec.cast cap h2 ?_ (by simp; omega)
  apply WState.eq
  · rfl
  · funext x; simp only [WState.setv_st, WState.sets_st, Function.update_apply, frame_eq_frameP, binary_zero',
      binary_length]
  · funext x; simp only [WState.setv_val, WState.sets_val, Function.update_apply]
    split_ifs with h <;> subst_vars <;> simp_all
  · rfl

end Ops

/-! ## The sweep -/

/-- One record of the sweep: read the tag, update the count or the total, mark `G`, skip the rest. -/
def scanBody (S CNT TOT : Fin (ns + 1)) (C F R G : Fin nr) : WM ns nr :=
  .seq (WM.fwdC S C) (.seq (.ifs S (incCNT CNT TOT F R) (addTOT CNT TOT F R)) (.seq (WM.setF G)
    (.seq (WM.fwdC S C) (.seq (.whs S (.seq (WM.fwdC S C) (WM.fwdC S C))) (WM.fwdC S C)))))

/-- **The sweep**: every record, then rewind the stream and, if a record was read, zero the count. -/
def scanW (S CNT TOT : Fin (ns + 1)) (C F R G : Fin nr) : WM ns nr :=
  .seq (.whs S (scanBody S CNT TOT C F R G))
    (.seq (WM.rewind S C) (.ifr G (.seq (zeroCNT CNT TOT F R) (.dec G)) .skip))

/-- The sweep's cost for `m` records of width `W`. -/
def scanCost (W m : ℕ) : ℕ := m * (60 * W + 44) + 1 + 1 + (5 * (m * (2 * W + 1)) + 1) + 1 + (41 * W + 3 + 1 + 1 + 1)

theorem scanStep_shift : ∀ (l : List ℕ) (c t t0 : ℕ),
    l.foldl scanStep (c, t0 + t) = ((l.foldl scanStep (c, t)).1, t0 + (l.foldl scanStep (c, t)).2)
  | [], c, t, t0 => rfl
  | x :: l, c, t, t0 => by
    simp only [List.foldl_cons]
    by_cases h : x % 2 = 1
    · have e1 : scanStep (c, t0 + t) x = (c + 1, t0 + t) := by simp [scanStep, h]
      have e2 : scanStep (c, t) x = (c + 1, t) := by simp [scanStep, h]
      rw [e1, e2, scanStep_shift l (c + 1) t t0]
    · have e1 : scanStep (c, t0 + t) x = (c, t0 + (t + c)) := by simp [scanStep, h]; omega
      have e2 : scanStep (c, t) x = (c, t + c) := by simp [scanStep, h]
      rw [e1, e2, scanStep_shift l c (t + c) t0]

theorem scanStep_mono : ∀ (l : List ℕ) (c t : ℕ),
    c ≤ (l.foldl scanStep (c, t)).1 ∧ t ≤ (l.foldl scanStep (c, t)).2
  | [], c, t => ⟨le_rfl, le_rfl⟩
  | x :: l, c, t => by
    simp only [List.foldl_cons]
    by_cases h : x % 2 = 1
    · have e : scanStep (c, t) x = (c + 1, t) := by simp [scanStep, h]
      rw [e]; have := scanStep_mono l (c + 1) t; omega
    · have e : scanStep (c, t) x = (c, t + c) := by simp [scanStep, h]
      rw [e]; have := scanStep_mono l c (t + c); omega

theorem keyRec_bits (W x : ℕ) (hW : 1 ≤ W) :
    StablePartition.recordBits (keyRec W x) = true :: (x % 2 == 1) :: (frameP (binary (W - 1) (x / 2)) ++ [false]) := by
  obtain ⟨W', rfl⟩ : ∃ W', W = W' + 1 := ⟨W - 1, by omega⟩
  rw [recordBits_eq]
  simp [keyRec, record, binary]

section Sweep
variable (cap W : ℕ) (σ0 : WState ns nr) {S CNT TOT : Fin (ns + 1)} {C F R G : Fin nr}
variable (hSC : S ≠ CNT) (hST : S ≠ TOT) (hCT : CNT ≠ TOT) (hCF : C ≠ F) (hCR : C ≠ R) (hCG : C ≠ G)
  (hFR : F ≠ R) (hFG : F ≠ G) (hRG : R ≠ G)
include hSC hST hCT hCF hCR hCG hFR hFG hRG

/-- The sweep's state: `S` (and `C`) at `p`, count `c`, total `t`, mark `g`. -/
def sst (p c t g : ℕ) : WState ns nr :=
  ⟨Function.update σ0.sh S p, Function.update (Function.update σ0.st CNT (frame (binary W c))) TOT
    (frame (binary W t)), Function.update (Function.update σ0.val C p) G g, σ0.cell⟩

variable (hCNTh : σ0.sh CNT = 0) (hTOTh : σ0.sh TOT = 0) (hF0 : σ0.val F = 0) (hR0 : σ0.val R = 0)
include hCNTh hTOTh hF0 hR0

theorem sst_numC (p c t g : ℕ) : NumOn (sst W σ0 (S := S) (CNT := CNT) (TOT := TOT) (C := C) (G := G) p c t g)
    CNT W c := ⟨by simp [sst, hCT], by simp [sst, Ne.symm hSC, hCNTh]⟩

theorem sst_numT (p c t g : ℕ) : NumOn (sst W σ0 (S := S) (CNT := CNT) (TOT := TOT) (C := C) (G := G) p c t g)
    TOT W t := ⟨by simp [sst], by simp [sst, Ne.symm hST, hTOTh]⟩

theorem sst_F (p c t g : ℕ) : (sst W σ0 (S := S) (CNT := CNT) (TOT := TOT) (C := C) (G := G) p c t g).val F = 0 := by
  simp [sst, Ne.symm hCF, hFG, hF0]

theorem sst_R (p c t g : ℕ) : (sst W σ0 (S := S) (CNT := CNT) (TOT := TOT) (C := C) (G := G) p c t g).val R = 0 := by
  simp [sst, Ne.symm hCR, hRG, hR0]

theorem sst_fwd (p c t g : ℕ) (hp : p < cap) :
    WExec cap (WM.fwdC S C) (sst W σ0 (S := S) (CNT := CNT) (TOT := TOT) (C := C) (G := G) p c t g)
      (sst W σ0 (S := S) (CNT := CNT) (TOT := TOT) (C := C) (G := G) (p + 1) c t g) 5 := by
  have h := wfwdC_spec cap S C (sst W σ0 (S := S) (CNT := CNT) (TOT := TOT) (C := C) (G := G) p c t g)
    (by simp [sst, hCG]; exact hp)
  refine WExec.cast cap h ?_ le_rfl
  apply WState.eq
  · funext x; simp only [sst, WState.setv_sh, WState.seth_sh, Function.update_apply]
    split_ifs <;> simp_all
  · rfl
  · funext x; simp only [sst, WState.setv_val, WState.seth_val, Function.update_apply]
    split_ifs <;> simp_all
  · rfl

theorem sst_inc (p c t g : ℕ) (hc : c + 1 < 2 ^ W) (hcap : 2 * W + 1 ≤ cap) :
    WExec cap (incCNT CNT TOT F R) (sst W σ0 (S := S) (CNT := CNT) (TOT := TOT) (C := C) (G := G) p c t g)
      (sst W σ0 (S := S) (CNT := CNT) (TOT := TOT) (C := C) (G := G) p (c + 1) t g) (41 * W + 7) := by
  have h := incCNT_spec cap W hCT hFR _ c t (sst_numC W σ0 hSC hST hCT hCF hCR hCG hFR hFG hRG hCNTh hTOTh hF0 hR0 p c t g)
    (sst_numT W σ0 hSC hST hCT hCF hCR hCG hFR hFG hRG hCNTh hTOTh hF0 hR0 p c t g)
    (sst_F W σ0 hSC hST hCT hCF hCR hCG hFR hFG hRG hCNTh hTOTh hF0 hR0 p c t g)
    (sst_R W σ0 hSC hST hCT hCF hCR hCG hFR hFG hRG hCNTh hTOTh hF0 hR0 p c t g) hc hcap
  refine WExec.cast cap h ?_ le_rfl
  apply WState.eq
  · rfl
  · funext x; simp only [sst, WState.sets_st, Function.update_apply]
    split_ifs <;> simp_all
  · rfl
  · rfl

theorem sst_add (p c t g : ℕ) (hct : t + c < 2 ^ W) (hcap : 2 * W + 1 ≤ cap) :
    WExec cap (addTOT CNT TOT F R) (sst W σ0 (S := S) (CNT := CNT) (TOT := TOT) (C := C) (G := G) p c t g)
      (sst W σ0 (S := S) (CNT := CNT) (TOT := TOT) (C := C) (G := G) p c (t + c) g) (41 * W + 3) := by
  have h := addTOT_spec cap W hCT hFR _ c t (sst_numC W σ0 hSC hST hCT hCF hCR hCG hFR hFG hRG hCNTh hTOTh hF0 hR0 p c t g)
    (sst_numT W σ0 hSC hST hCT hCF hCR hCG hFR hFG hRG hCNTh hTOTh hF0 hR0 p c t g)
    (sst_F W σ0 hSC hST hCT hCF hCR hCG hFR hFG hRG hCNTh hTOTh hF0 hR0 p c t g)
    (sst_R W σ0 hSC hST hCT hCF hCR hCG hFR hFG hRG hCNTh hTOTh hF0 hR0 p c t g) hct hcap
  refine WExec.cast cap h ?_ le_rfl
  apply WState.eq
  · rfl
  · funext x; simp only [sst, WState.sets_st, Function.update_apply]
    split_ifs <;> simp_all
  · rfl
  · rfl

theorem sst_zero (p c t g : ℕ) (hcap : 2 * W + 1 ≤ cap) :
    WExec cap (zeroCNT CNT TOT F R) (sst W σ0 (S := S) (CNT := CNT) (TOT := TOT) (C := C) (G := G) p c t g)
      (sst W σ0 (S := S) (CNT := CNT) (TOT := TOT) (C := C) (G := G) p 0 t g) (41 * W + 3) := by
  have h := zeroCNT_spec cap W hCT hFR _ c t (sst_numC W σ0 hSC hST hCT hCF hCR hCG hFR hFG hRG hCNTh hTOTh hF0 hR0 p c t g)
    (sst_numT W σ0 hSC hST hCT hCF hCR hCG hFR hFG hRG hCNTh hTOTh hF0 hR0 p c t g)
    (sst_F W σ0 hSC hST hCT hCF hCR hCG hFR hFG hRG hCNTh hTOTh hF0 hR0 p c t g)
    (sst_R W σ0 hSC hST hCT hCF hCR hCG hFR hFG hRG hCNTh hTOTh hF0 hR0 p c t g) hcap
  refine WExec.cast cap h ?_ le_rfl
  apply WState.eq
  · rfl
  · funext x; simp only [sst, WState.sets_st, Function.update_apply]
    split_ifs <;> simp_all
  · rfl
  · rfl

theorem sst_setF (p c t g : ℕ) (hg : g ≤ 1) (hcap : 1 ≤ cap) :
    WExec cap (WM.setF G) (sst W σ0 (S := S) (CNT := CNT) (TOT := TOT) (C := C) (G := G) p c t g)
      (sst W σ0 (S := S) (CNT := CNT) (TOT := TOT) (C := C) (G := G) p c t 1) 4 := by
  have h := wsetF_spec cap G (sst W σ0 (S := S) (CNT := CNT) (TOT := TOT) (C := C) (G := G) p c t g)
    (by simp [sst]; exact hg) hcap
  refine WExec.cast cap h ?_ le_rfl
  apply WState.eq
  · rfl
  · rfl
  · funext x; simp only [sst, WState.setv_val, Function.update_apply]
    split_ifs <;> simp_all
  · rfl

end Sweep

theorem keyRec_bits_length (W x : ℕ) (hW : 1 ≤ W) :
    (StablePartition.recordBits (keyRec W x)).length = 2 * W + 1 := by
  rw [keyRec_bits W x hW]; simp; omega

section SweepLoop
variable (cap W : ℕ) (σ0 : WState ns nr) {S CNT TOT : Fin (ns + 1)} {C F R G : Fin nr}
variable (hSC : S ≠ CNT) (hST : S ≠ TOT) (hCT : CNT ≠ TOT) (hCF : C ≠ F) (hCR : C ≠ R) (hCG : C ≠ G)
  (hFR : F ≠ R) (hFG : F ≠ G) (hRG : R ≠ G)
variable (hCNTh : σ0.sh CNT = 0) (hTOTh : σ0.sh TOT = 0) (hF0 : σ0.val F = 0) (hR0 : σ0.val R = 0)
include hSC hST hCT hCF hCR hCG hFR hFG hRG hCNTh hTOTh hF0 hR0

/-- **One record of the sweep.** -/
theorem sst_record (hW : 1 ≤ W) (x : ℕ) (pre post : List Bool)
    (hS : σ0.st S = pre ++ StablePartition.recordBits (keyRec W x) ++ post) (c t g : ℕ) (hg : g ≤ 1)
    (hb1 : (scanStep (c, t) x).1 < 2 ^ W) (hb2 : (scanStep (c, t) x).2 < 2 ^ W) (hcap1 : 2 * W + 1 ≤ cap)
    (hp : pre.length + (2 * W + 1) ≤ cap) :
    WExec cap (scanBody S CNT TOT C F R G)
      (sst W σ0 (S := S) (CNT := CNT) (TOT := TOT) (C := C) (G := G) pre.length c t g)
      (sst W σ0 (S := S) (CNT := CNT) (TOT := TOT) (C := C) (G := G) (pre.length + (2 * W + 1))
        (scanStep (c, t) x).1 (scanStep (c, t) x).2 1) (60 * W + 42) := by
  have hS2 : σ0.st S = pre ++ (true :: (x % 2 == 1) :: (frameP (binary (W - 1) (x / 2)) ++ false :: post)) := by
    rw [hS, keyRec_bits W x hW]; simp
  have hS3 : σ0.st S = (pre ++ [true, x % 2 == 1]) ++ frameP (binary (W - 1) (x / 2)) ++ false :: post := by
    rw [hS, keyRec_bits W x hW]; simp
  have f1 := sst_fwd cap W σ0 hSC hST hCT hCF hCR hCG hFR hFG hRG hCNTh hTOTh hF0 hR0 pre.length c t g (by omega)
  have htag : wbit (sst W σ0 (S := S) (CNT := CNT) (TOT := TOT) (C := C) (G := G) (pre.length + 1) c t g) S =
      (x % 2 == 1) := by
    simp only [wbit, sst, Function.update_apply, hSC, hST, if_false, if_true, hS2]
    have := rd_app0 (pre ++ [true]) ((x % 2 == 1) :: (frameP (binary (W - 1) (x / 2)) ++ false :: post))
    simp only [List.append_assoc, List.singleton_append, List.length_append, List.length_singleton] at this
    simp [this, rd_cons0]
  -- the update
  have hop : WExec cap (.ifs S (incCNT CNT TOT F R) (addTOT CNT TOT F R))
      (sst W σ0 (S := S) (CNT := CNT) (TOT := TOT) (C := C) (G := G) (pre.length + 1) c t g)
      (sst W σ0 (S := S) (CNT := CNT) (TOT := TOT) (C := C) (G := G) (pre.length + 1)
        (scanStep (c, t) x).1 (scanStep (c, t) x).2 g) (41 * W + 8) := by
    by_cases hodd : x % 2 = 1
    · have e : scanStep (c, t) x = (c + 1, t) := by simp [scanStep, hodd]
      rw [e] at hb1 ⊢
      have hi := sst_inc cap W σ0 hSC hST hCT hCF hCR hCG hFR hFG hRG hCNTh hTOTh hF0 hR0 (pre.length + 1) c t g hb1
        hcap1
      exact WExec.ifsT (by rw [htag]; simp [hodd]) hi
    · have e : scanStep (c, t) x = (c, t + c) := by simp [scanStep, hodd]
      rw [e] at hb2 ⊢
      have ha := sst_add cap W σ0 hSC hST hCT hCF hCR hCG hFR hFG hRG hCNTh hTOTh hF0 hR0 (pre.length + 1) c t g hb2
        hcap1
      exact WExec.mono (WExec.ifsF (by rw [htag]; simp [hodd]) ha) (by omega)
  set c' := (scanStep (c, t) x).1
  set t' := (scanStep (c, t) x).2
  have hsf := sst_setF cap W σ0 hSC hST hCT hCF hCR hCG hFR hFG hRG hCNTh hTOTh hF0 hR0 (pre.length + 1) c' t' g hg
    (by omega)
  have f2 := sst_fwd cap W σ0 hSC hST hCT hCF hCR hCG hFR hFG hRG hCNTh hTOTh hF0 hR0 (pre.length + 1) c' t' 1
    (by omega)
  have hl : (pre ++ [true, x % 2 == 1]).length = pre.length + 1 + 1 := by simp
  have hsk := skipGen cap S C (binary (W - 1) (x / 2)) (pre ++ [true, x % 2 == 1]) post
    (sst W σ0 (S := S) (CNT := CNT) (TOT := TOT) (C := C) (G := G) (pre.length + 1 + 1) c' t' 1)
    (by simp only [sst, Function.update_apply, hSC, hST, if_false]; simp [hS3])
    (by simp [sst, hl]) (by simp [sst, hCG, hl]) (by rw [hl, binary_length]; omega)
  rw [hl, binary_length] at hsk
  set q := pre.length + 1 + 1 + 2 * (W - 1) with hq
  have e3 : ((sst W σ0 (S := S) (CNT := CNT) (TOT := TOT) (C := C) (G := G) (pre.length + 1 + 1) c' t' 1).seth S q).setv
      C q = sst W σ0 (S := S) (CNT := CNT) (TOT := TOT) (C := C) (G := G) q c' t' 1 := by
    apply WState.eq
    · funext y; simp only [sst, WState.setv_sh, WState.seth_sh, Function.update_apply]
      split_ifs <;> simp_all
    · rfl
    · funext y; simp only [sst, WState.setv_val, WState.seth_val, Function.update_apply]
      split_ifs <;> simp_all
    · rfl
  rw [e3] at hsk
  have f3 := sst_fwd cap W σ0 hSC hST hCT hCF hCR hCG hFR hFG hRG hCNTh hTOTh hF0 hR0 q c' t' 1 (by omega)
  have hq1 : q + 1 = pre.length + (2 * W + 1) := by omega
  rw [hq1] at f3
  exact WExec.mono (WExec.seq f1 (WExec.seq hop (WExec.seq hsf (WExec.seq f2 (WExec.seq hsk f3))))) (by omega)

/-- **The sweep's loop.** -/
theorem sst_loop (hW : 1 ≤ W) : ∀ (rest : List ℕ) (pre post : List Bool) (c t g : ℕ),
    σ0.st S = pre ++ StablePartition.recordsBits (rest.map (keyRec W)) ++ false :: post →
    g ≤ 1 → (rest.foldl scanStep (c, t)).1 < 2 ^ W → (rest.foldl scanStep (c, t)).2 < 2 ^ W →
    pre.length + (StablePartition.recordsBits (rest.map (keyRec W))).length < cap →
    WExec cap (.whs S (scanBody S CNT TOT C F R G))
      (sst W σ0 (S := S) (CNT := CNT) (TOT := TOT) (C := C) (G := G) pre.length c t g)
      (sst W σ0 (S := S) (CNT := CNT) (TOT := TOT) (C := C) (G := G)
        (pre.length + (StablePartition.recordsBits (rest.map (keyRec W))).length)
        (rest.foldl scanStep (c, t)).1 (rest.foldl scanStep (c, t)).2 (if rest = [] then g else 1))
      (rest.length * (60 * W + 44) + 1)
  | [], pre, post, c, t, g, hS, _, _, _, _ => by
    have hbit : wbit (sst W σ0 (S := S) (CNT := CNT) (TOT := TOT) (C := C) (G := G) pre.length c t g) S = false := by
      simp only [wbit, sst, Function.update_apply, hSC, hST, if_false, if_true, hS]
      simp [StablePartition.recordsBits, rd_app0, rd_cons0]
    have h := WExec.whsF (cap := cap) (P := scanBody S CNT TOT C F R G) hbit
    refine WExec.cast cap h ?_ (by simp)
    simp [StablePartition.recordsBits]
  | x :: rest, pre, post, c, t, g, hS, hg, hb1, hb2, hp => by
    have hlx := keyRec_bits_length W x hW
    have hS1 : σ0.st S = pre ++ StablePartition.recordBits (keyRec W x) ++
        (StablePartition.recordsBits (rest.map (keyRec W)) ++ false :: post) := by
      rw [hS, List.map_cons, recordsBits_cons]; simp
    have hS2 : σ0.st S = (pre ++ StablePartition.recordBits (keyRec W x)) ++
        StablePartition.recordsBits (rest.map (keyRec W)) ++ false :: post := by
      rw [hS, List.map_cons, recordsBits_cons]; simp
    have hbit : wbit (sst W σ0 (S := S) (CNT := CNT) (TOT := TOT) (C := C) (G := G) pre.length c t g) S = true := by
      simp only [wbit, sst, Function.update_apply, hSC, hST, if_false, if_true, hS1]
      rw [List.append_assoc, rd_app0, keyRec_bits W x hW]; rfl
    rw [List.map_cons, recordsBits_cons, List.length_append, hlx] at hp
    have hm := scanStep_mono rest (scanStep (c, t) x).1 (scanStep (c, t) x).2
    rw [Prod.mk.eta] at hm
    simp only [List.foldl_cons] at hb1 hb2
    have h1 := sst_record cap W σ0 hSC hST hCT hCF hCR hCG hFR hFG hRG hCNTh hTOTh hF0 hR0 hW x pre _ hS1 c t g hg
      (by omega) (by omega) (by omega) (by omega)
    have h2 := sst_loop hW rest (pre ++ StablePartition.recordBits (keyRec W x)) post (scanStep (c, t) x).1
      (scanStep (c, t) x).2 1 hS2 (le_refl _) (by rw [Prod.mk.eta]; exact hb1) (by rw [Prod.mk.eta]; exact hb2)
      (by rw [List.length_append, hlx]; omega)
    rw [List.length_append, hlx, Prod.mk.eta] at h2
    have ecost : (rest.length + 1) * (60 * W + 44) = rest.length * (60 * W + 44) + (60 * W + 44) := by ring
    refine WExec.cast cap (WExec.whsT hbit h1 h2) ?_ (by rw [List.length_cons, ecost]; omega)
    simp only [List.foldl_cons, List.map_cons, recordsBits_cons, List.length_append, hlx, reduceCtorEq, if_false]
    congr 1
    · omega
    · split_ifs <;> rfl

end SweepLoop

/-- **The sweep meets `ScanSpec`.** -/
theorem scanW_spec (cap W : ℕ) {S CNT TOT : Fin (ns + 1)} {C F R G : Fin nr}
    (hSC : S ≠ CNT) (hST : S ≠ TOT) (hCT : CNT ≠ TOT) (hCF : C ≠ F) (hCR : C ≠ R) (hCG : C ≠ G)
    (hFR : F ≠ R) (hFG : F ≠ G) (hRG : R ≠ G) :
    ScanSpec cap W (scanW S CNT TOT C F R G) S CNT TOT [C, F, R, G] scanCost := by
  intro σ l t0 hW hl hS hSh hC hT hc ht hr hcap
  obtain ⟨hC1, hC2⟩ := hC
  obtain ⟨hT1, hT2⟩ := hT
  have hC0 : σ.val C = 0 := hr C (by simp)
  have hF0 : σ.val F = 0 := hr F (by simp)
  have hR0 : σ.val R = 0 := hr R (by simp)
  have hG0 : σ.val G = 0 := hr G (by simp)
  have e0 : sst W σ (S := S) (CNT := CNT) (TOT := TOT) (C := C) (G := G) 0 0 t0 0 = σ := by
    apply WState.eq
    · funext y; simp only [sst, Function.update_apply]
      split_ifs <;> simp_all
    · funext y; simp only [sst, Function.update_apply]
      split_ifs <;> simp_all
    · funext y; simp only [sst, Function.update_apply]
      split_ifs <;> simp_all
    · rfl
  have hS' : σ.st S = [] ++ StablePartition.recordsBits (l.map (keyRec W)) ++ false :: [] := by
    rw [hS]; rfl
  have hshift := scanStep_shift l 0 0 t0
  simp only [Nat.add_zero] at hshift
  have hsc : scanRef l = l.foldl scanStep (0, 0) := rfl
  have hlen := keyStream_length W hW l
  have hrb : (StablePartition.recordsBits (l.map (keyRec W))).length = l.length * (2 * W + 1) := by
    have : (keyStream W l).length = (StablePartition.recordsBits (l.map (keyRec W))).length + 1 := by
      simp [keyStream, StablePartition.stream]
    omega
  have hloop := sst_loop cap W σ hSC hST hCT hCF hCR hCG hFR hFG hRG hC2 hT2 hF0 hR0 hW l [] [] 0 t0 0 hS'
    (by omega) (by rw [hshift, ← hsc]; exact hc) (by rw [hshift, ← hsc]; exact ht) (by simp; omega)
  simp only [List.length_nil, Nat.zero_add] at hloop
  rw [e0, hshift, ← hsc] at hloop
  set N := (StablePartition.recordsBits (l.map (keyRec W))).length with hN
  set gf := if l = [] then 0 else 1 with hgf
  set tf := t0 + (scanRef l).2 with htf
  set cf := (scanRef l).1 with hcf
  have hrw := wrewind_spec cap S C N (sst W σ (S := S) (CNT := CNT) (TOT := TOT) (C := C) (G := G) N cf tf gf)
    (by simp [sst, hCG]) (by simp [sst, hCG]; omega)
  have e1 : ((sst W σ (S := S) (CNT := CNT) (TOT := TOT) (C := C) (G := G) N cf tf gf).setv C 0).seth S
      ((sst W σ (S := S) (CNT := CNT) (TOT := TOT) (C := C) (G := G) N cf tf gf).sh S - N) =
      sst W σ (S := S) (CNT := CNT) (TOT := TOT) (C := C) (G := G) 0 cf tf gf := by
    apply WState.eq
    · funext y; simp only [sst, WState.seth_sh, WState.setv_sh, Function.update_apply]
      split_ifs <;> simp_all
    · rfl
    · funext y; simp only [sst, WState.seth_val, WState.setv_val, Function.update_apply]
      split_ifs <;> simp_all
    · rfl
  rw [e1] at hrw
  have efin : sst W σ (S := S) (CNT := CNT) (TOT := TOT) (C := C) (G := G) 0 0 tf 0 =
      σ.sets TOT (frame (binary W (t0 + (scanRef l).2))) := by
    apply WState.eq
    · funext y; simp only [sst, WState.sets_sh, Function.update_apply]
      split_ifs <;> simp_all
    · funext y; simp only [sst, WState.sets_st, Function.update_apply]
      split_ifs <;> simp_all
    · funext y; simp only [sst, WState.sets_val, Function.update_apply]
      split_ifs <;> simp_all
    · rfl
  by_cases hl0 : l = []
  · subst hl0
    have hgf0 : gf = 0 := by simp [hgf]
    have hcf0 : cf = 0 := by simp [hcf, scanRef]
    rw [hgf0, hcf0] at hrw
    have hG : (sst W σ (S := S) (CNT := CNT) (TOT := TOT) (C := C) (G := G) 0 0 tf 0).val G = 0 := by simp [sst]
    have hfin := WExec.ifrF (cap := cap) (P := (.seq (zeroCNT CNT TOT F R) (.dec G) : WM ns nr)) hG
      (WExec.skip (sst W σ (S := S) (CNT := CNT) (TOT := TOT) (C := C) (G := G) 0 0 tf 0))
    rw [hgf0, hcf0] at hloop
    have hfin' := WExec.cast cap hfin efin (le_refl _)
    refine WExec.cast cap (WExec.seq hloop (WExec.seq hrw hfin')) rfl ?_
    unfold scanCost
    simp at hrb
    omega
  · have hgf1 : gf = 1 := by simp [hgf, hl0]
    rw [hgf1] at hrw hloop
    have hne : 1 ≤ l.length := by
      rcases Nat.eq_zero_or_pos l.length with h0 | h0
      · exact absurd (List.length_eq_zero_iff.mp h0) hl0
      · exact h0
    have hcap1 : 2 * W + 1 ≤ cap := by
      have : 1 * (2 * W + 1) ≤ l.length * (2 * W + 1) := Nat.mul_le_mul_right _ hne
      omega
    have hz := sst_zero cap W σ hSC hST hCT hCF hCR hCG hFR hFG hRG hC2 hT2 hF0 hR0 0 cf tf 1 hcap1
    have hd := WExec.dec (cap := cap) G (sst W σ (S := S) (CNT := CNT) (TOT := TOT) (C := C) (G := G) 0 0 tf 1)
      (by simp [sst]; omega)
    have ed : (sst W σ (S := S) (CNT := CNT) (TOT := TOT) (C := C) (G := G) 0 0 tf 1).setv G
        ((sst W σ (S := S) (CNT := CNT) (TOT := TOT) (C := C) (G := G) 0 0 tf 1).val G - 1) =
        sst W σ (S := S) (CNT := CNT) (TOT := TOT) (C := C) (G := G) 0 0 tf 0 := by
      apply WState.eq
      · rfl
      · rfl
      · funext y; simp only [sst, WState.setv_val, Function.update_apply]
        split_ifs <;> simp_all
      · rfl
    rw [ed, efin] at hd
    have hG : (sst W σ (S := S) (CNT := CNT) (TOT := TOT) (C := C) (G := G) 0 cf tf 1).val G ≠ 0 := by simp [sst]
    have hfin := WExec.ifrT (cap := cap) (Q := (.skip : WM ns nr)) hG (WExec.seq hz hd)
    refine WExec.cast cap (WExec.seq hloop (WExec.seq hrw hfin)) rfl ?_
    unfold scanCost; omega

end NearCubicWires.WireExponent3_5.SelectionMachine.Sort
