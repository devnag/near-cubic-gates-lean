import Proof.Gates.Expand.Setup1

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.Expand.Layout

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Expand

theorem grN {i j : Fin 8} (h : i ≠ j) : GR i ≠ GR j := GR.injective.ne h

/-! ## Register arithmetic for the first width -/

def regA : WMX NS NR :=
  .seq (addR (GR 0) (GR 3) (GR 7)) (.seq (WMX.inc (GR 3)) (.seq (WMX.inc (GR 3)) (.seq (addR (GR 3) (GR 4) (GR 7))
    (mulR (GR 3) (GR 5) (GR 4) (GR 2) (GR 7)))))

def regACost (L : ℕ) : ℕ :=
  (18 * L + 3) + 1 + (3 + 1 + (3 + 1 + ((18 * (L + 2) + 3) + 1 + ((L + 2) * (18 * (L + 2) + 3 + 8) + 7 * (L + 2) + 3))))

theorem regA_spec (cap L : ℕ) (σ : WState NS NR) (h0 : σ.val (GR 0) = L) (h2 : σ.val (GR 2) = 0)
    (h3 : σ.val (GR 3) = 0) (h4 : σ.val (GR 4) = 0) (h5 : σ.val (GR 5) = 0) (h7 : σ.val (GR 7) = 0)
    (hcap : (L + 2) * (L + 2) + 2 * (L + 2) ≤ cap) :
    Runs cap regA σ (regACost L) (fun τ => SameExcept σ τ [] [GR 2, GR 3, GR 4] ∧ τ.val (GR 2) = (L + 2) * (L + 2) ∧
      τ.val (GR 3) = L + 2 ∧ τ.val (GR 4) = L + 2) := by
  have e1 := addR_spec cap (A := GR 0) (B := GR 3) (T := GR 7) (grN (by decide)) (grN (by decide)) (grN (by decide))
    σ h7 (by rw [h0, h3]; nlinarith)
  set σ1 := σ.setv (GR 3) (σ.val (GR 3) + σ.val (GR 0)) with hσ1
  have e2 := WXExec.inc cap (GR 3) σ1 (by rw [hσ1]; simp [h0, h3]; nlinarith)
  set σ2 := σ1.setv (GR 3) (σ1.val (GR 3) + 1) with hσ2
  have e3 := WXExec.inc cap (GR 3) σ2 (by rw [hσ2, hσ1]; simp [h0, h3]; nlinarith)
  set σ3 := σ2.setv (GR 3) (σ2.val (GR 3) + 1) with hσ3
  have v3 : σ3.val (GR 3) = L + 2 := by rw [hσ3, hσ2, hσ1]; simp [h0, h3]
  have v4 : σ3.val (GR 4) = 0 := by rw [hσ3, hσ2, hσ1]; simp [Function.update_apply, h4]
  have v7 : σ3.val (GR 7) = 0 := by rw [hσ3, hσ2, hσ1]; simp [Function.update_apply, h7]
  have e4 := addR_spec cap (A := GR 3) (B := GR 4) (T := GR 7) (grN (by decide)) (grN (by decide)) (grN (by decide))
    σ3 v7 (by rw [v3, v4]; nlinarith)
  set σ4 := σ3.setv (GR 4) (σ3.val (GR 4) + σ3.val (GR 3)) with hσ4
  have w3 : σ4.val (GR 3) = L + 2 := by rw [hσ4]; simp [Function.update_apply, v3]
  have w4 : σ4.val (GR 4) = L + 2 := by rw [hσ4]; simp [v3, v4]
  have w2 : σ4.val (GR 2) = 0 := by rw [hσ4, hσ3, hσ2, hσ1]; simp [Function.update_apply, h2]
  have w5 : σ4.val (GR 5) = 0 := by rw [hσ4, hσ3, hσ2, hσ1]; simp [Function.update_apply, h5]
  have w7 : σ4.val (GR 7) = 0 := by rw [hσ4]; simp [Function.update_apply, v7]
  have e5 := mulR_spec cap (A := GR 3) (A2 := GR 5) (B := GR 4) (C := GR 2) (T := GR 7) (by decide) σ4 w5 w7
    (by rw [w2, w3, w4]; nlinarith) (by rw [w3]; nlinarith)
  refine Runs.of (WXExec.mono (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4 e5))))
    (by unfold regACost; rw [h0, w3, w4]; omega)) ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨fun x _ => ⟨by simp [hσ4, hσ3, hσ2, hσ1], by simp [hσ4, hσ3, hσ2, hσ1]⟩, fun q hq => ?_,
      by simp [hσ4, hσ3, hσ2, hσ1]⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    simp [hσ4, hσ3, hσ2, hσ1, Function.update_apply, hq.1, hq.2.1, hq.2.2]
  · simp [Function.update_apply, w2, w3, w4]
  · simp [Function.update_apply, w3]
  · simp [Function.update_apply, w4]

/-! ## Block steps not in OpsF -/

section MOps
variable {k : ℕ} (cap W : ℕ) {S : Fin k ↪ Fin (NS + 1)} {v : Fin k → ℕ} {σ : WState NS NR} {F R : Fin NR}

theorem mShl (a b : Fin k) (hab : a ≠ b) (hFR : F ≠ R) (h : MV S W v σ) (hF : σ.val F = 0) (hR : σ.val R = 0)
    (hcap : 2 * W + 1 ≤ cap) :
    Runs cap (BinW.shl (S a) (S b) F R) σ (41 * W + 8)
      (fun τ => MV S W (Function.update v a (2 * v a)) τ ∧ SameExcept σ τ [S a] []) :=
  ⟨_, BinW.shl_spec cap W (sN hab) hFR σ (v a) (v b) (h a) (h b) hF hR hcap,
    h.upd a (sameExcept_sets (Rg := []) σ (by simp) _) _ (BinW.numOn_sets_self σ _ W _ (h a).2),
    sameExcept_sets σ (by simp) _⟩

theorem mHalf (a : Fin k) (h : MV S W v σ) (hR : σ.val R = 0) (hlt : v a < 2 ^ W) (hcap : 2 * W + 1 ≤ cap) :
    Runs cap (BinW.half (S a) R) σ (34 * W + 3)
      (fun τ => MV S W (Function.update v a (v a / 2)) τ ∧ SameExcept σ τ [S a] []) :=
  ⟨_, BinW.half_spec cap W σ (v a) (h a) hR hlt (by omega),
    h.upd a (sameExcept_sets (Rg := []) σ (by simp) _) _ (BinW.numOn_sets_self σ _ W _ (h a).2),
    sameExcept_sets σ (by simp) _⟩

end MOps

/-! ## Initialization and the stage-A constants -/

def F0 : Fin NR := GR 6
def R0 : Fin NR := GR 7

def shlLoop (j b : Fin 53) (K K2 : Fin NR) : WMX NS NR := repK K K2 (BinW.shl (NB j) (NB b) F0 R0)

/-- `U 8 := 1`, `U 7 := 2^{L+1}`, `U 6 := 2^{L+1} + 1` (block indices `7`, `6`, `5`). -/
def constA : WMX NS NR :=
  .seq (BinW.inc (NB 7) (NB 0) F0 R0) (.seq (BinW.copy (NB 6) (NB 7) F0 R0) (.seq (WMX.dec (GR 3))
    (.seq (shlLoop 6 7 (GR 3) (GR 5)) (.seq (BinW.copy (NB 5) (NB 6) F0 R0) (BinW.inc (NB 5) (NB 7) F0 R0)))))

def stageA1 : WMX NS NR := .seq (initL (GR 2) (GR 5) nbList) constA

/-- The values of the number block after the stage-A constants. -/
def wA (L : ℕ) : Fin 53 → ℕ := fun j => if j = 5 then 2 ^ (L + 1) + 1 else if j = 6 then 2 ^ (L + 1) else
  if j = 7 then 1 else 0

def shlCost (Wb n : ℕ) : ℕ := n * ((41 * Wb + 8) + 8) + 7 * n + 3

def stageA1Cost (Wb L : ℕ) : ℕ :=
  53 * (initCost Wb + 1) + 1 + ((41 * Wb + 7) + 1 + ((41 * Wb + 3) + 1 + (1 + 1 + (shlCost Wb (L + 1) + 1 +
    ((41 * Wb + 3) + 1 + (41 * Wb + 7))))))

theorem shlLoop_spec (cap Wb : ℕ) (j b : Fin 53) (hjb : j ≠ b) (n : ℕ) (σ : WState NS NR) (w : Fin 53 → ℕ)
    (hw : MV NB Wb w σ) (hF : σ.val F0 = 0) (hR : σ.val R0 = 0) (hK : σ.val (GR 3) = n) (hK2 : σ.val (GR 5) = 0)
    (hcap : 2 * Wb + 1 ≤ cap) (hcapn : 2 * n ≤ cap) :
    Runs cap (shlLoop j b (GR 3) (GR 5)) σ (shlCost Wb n) (fun τ => MV NB Wb (Function.update w j (2 ^ n * w j)) τ ∧
      SameExcept σ τ [NB j] [] ) := by
  have hFR : F0 ≠ R0 := grN (by decide)
  let Inv : ℕ → WState NS NR → Prop := fun i τ => MV NB Wb (Function.update w j (2 ^ i * w j)) τ ∧
    SameExcept σ τ [NB j] [GR 3, GR 5]
  have h := Runs.rep (cap := cap) (K := GR 3) (K2 := GR 5) (body := BinW.shl (NB j) (NB b) F0 R0)
    (grN (by decide)) (41 * Wb + 8) n Inv hcapn
    (fun i τ v ⟨h1, h2⟩ => ⟨h1.frame' (sameExcept_setv (S := []) (Rg := [GR 3]) τ (by simp) v) (by simp),
      h2.trans (sameExcept_setv _ (by simp) _)⟩)
    (fun i τ v ⟨h1, h2⟩ => ⟨h1.frame' (sameExcept_setv (S := []) (Rg := [GR 5]) τ (by simp) v) (by simp),
      h2.trans (sameExcept_setv _ (by simp) _)⟩)
    (fun i _ τ ⟨h1, h2⟩ => by
      have hF' : τ.val F0 = 0 := by rw [h2.val (by simp [F0]), hF]
      have hR' : τ.val R0 = 0 := by rw [h2.val (by simp [R0]), hR]
      refine (mShl cap Wb j b hjb hFR h1 hF' hR' hcap).post (fun ρ ⟨m, f⟩ => ⟨⟨?_, h2.trans (se_sub f (by simp) (by simp))⟩,
        f.val (by simp), f.val (by simp)⟩)
      simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using m)
    σ ⟨by simpa using hw, SameExcept.refl _ _ _⟩ hK hK2
  refine (h.post (fun τ ⟨⟨h1, h2⟩, h3, h4⟩ => ⟨h1, ⟨h2.1, fun q _ => ?_, h2.2.2⟩⟩))
  by_cases e3 : q = GR 3
  · subst e3; rw [h3, hK]
  · by_cases e5 : q = GR 5
    · subst e5; rw [h4, hK2]
    · exact h2.2.1 q (by simp [e3, e5])

theorem mv_init (k : ℕ) (σ τ : WState NS NR) (h1 : ∀ X ∈ nbList, τ.st X = frame (binary k 0))
    (hsh : ∀ X, τ.sh X = σ.sh X) (h0 : ∀ j, σ.sh (NB j) = 0) : MV NB k (fun _ => 0) τ :=
  fun j => ⟨h1 _ (mem_nbList j), by rw [hsh, h0]⟩

theorem stageA1_spec (cap L : ℕ) (σ : WState NS NR) (hnb : ∀ j, σ.st (NB j) = [] ∧ σ.sh (NB j) = 0)
    (h2 : σ.val (GR 2) = (L + 2) * (L + 2)) (h3 : σ.val (GR 3) = L + 2) (h5 : σ.val (GR 5) = 0)
    (h6 : σ.val (GR 6) = 0) (h7 : σ.val (GR 7) = 0) (hcap : 2 * ((L + 2) * (L + 2)) + 1 ≤ cap) :
    Runs cap stageA1 σ (stageA1Cost ((L + 2) * (L + 2)) L) (fun τ => MV NB ((L + 2) * (L + 2)) (wA L) τ ∧
      τ.val (GR 3) = L + 1 ∧ SameExcept σ τ nbList [GR 3]) := by
  set Wb := (L + 2) * (L + 2) with hWb
  have hFR : F0 ≠ R0 := grN (by decide)
  have hLW : L + 2 ≤ Wb := by nlinarith
  have hp : 2 ^ (L + 1) + 1 < 2 ^ Wb := by
    have : 2 ^ (L + 1) < 2 ^ (L + 2) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    have : 2 ^ (L + 2) ≤ 2 ^ Wb := Nat.pow_le_pow_right (by norm_num) hLW
    have : 2 ^ (L + 1) ≥ 1 := Nat.one_le_two_pow
    have : 2 ^ (L + 2) = 2 * 2 ^ (L + 1) := by ring
    omega
  refine Runs.seq (initL_spec cap (grN (by decide)) Wb (by omega) nbList σ
    (fun X hX => by
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hX
      simp [(hnb j).1, (hnb j).2]) h2 h5) (fun τ1 ⟨i1, f1, s1⟩ => ?_)
  have m1 := mv_init Wb σ τ1 i1 s1 (fun j => (hnb j).2)
  have z6 : τ1.val F0 = 0 := by rw [f1.val (by simp [F0])]; exact h6
  have z7 : τ1.val R0 = 0 := by rw [f1.val (by simp [R0])]; exact h7
  refine Runs.seq (mInc cap Wb 7 0 (by decide) hFR m1 z6 z7 (by simp <;> omega) (by omega)) (fun τ2 ⟨m2, f2⟩ => ?_)
  refine Runs.seq (mCopy cap Wb 6 7 (by decide) hFR m2 (by rw [f2.val (by simp)]; exact z6)
    (by rw [f2.val (by simp)]; exact z7) (by omega)) (fun τ3 ⟨m3, f3⟩ => ?_)
  have v3 : τ3.val (GR 3) = L + 2 := by rw [f3.val (by simp), f2.val (by simp), f1.val (by simp), h3]
  refine Runs.seq (Runs.of (WXExec.dec cap (GR 3) τ3 (by omega)) rfl) (fun τ4 e4 => ?_)
  subst e4
  have f4 : SameExcept τ3 (τ3.setv (GR 3) (τ3.val (GR 3) - 1)) [] [GR 3] := sameExcept_setv τ3 (by simp) _
  have m4 := m3.frame' f4 (by simp)
  refine Runs.seq (shlLoop_spec cap Wb 6 7 (by decide) (L + 1) _ _ m4
    (by rw [f4.val (by simp [F0]), f3.val (by simp), f2.val (by simp)]; exact z6)
    (by rw [f4.val (by simp [R0]), f3.val (by simp), f2.val (by simp)]; exact z7)
    (by simp [v3]) (by rw [f4.val (by simp), f3.val (by simp), f2.val (by simp), f1.val (by simp), h5])
    (by omega) (by nlinarith)) (fun τ5 ⟨m5, f5⟩ => ?_)
  have z6' : τ5.val F0 = 0 := by
    rw [f5.val (by simp), f4.val (by simp [F0]), f3.val (by simp), f2.val (by simp)]; exact z6
  have z7' : τ5.val R0 = 0 := by
    rw [f5.val (by simp), f4.val (by simp [R0]), f3.val (by simp), f2.val (by simp)]; exact z7
  refine Runs.seq (mCopy cap Wb 5 6 (by decide) hFR m5 z6' z7' (by omega)) (fun τ6 ⟨m6, f6⟩ => ?_)
  refine (mInc cap Wb 5 7 (by decide) hFR m6 (by rw [f6.val (by simp)]; exact z6')
    (by rw [f6.val (by simp)]; exact z7') (by simp <;> omega) (by omega)).post (fun τ7 ⟨m7, f7⟩ => ⟨?_, ?_, ?_⟩)
  · convert m7 using 1
    funext j
    simp only [wA, Function.update_apply]
    split_ifs <;> simp_all
  · rw [f7.val (by simp), f6.val (by simp), f5.val (by simp)]; simp [v3]
  · refine ⟨fun x hx => ?_, fun q hq => ?_, ?_⟩
    · have hx' : x ∉ [NB 7] ∧ x ∉ [NB 6] ∧ x ∉ [NB 5] := by
        refine ⟨?_, ?_, ?_⟩ <;> simp only [List.mem_singleton] <;> rintro rfl <;> exact hx (mem_nbList _)
      exact ⟨by rw [f7.st hx'.2.2, f6.st hx'.2.2, f5.st (by simpa using hx'.2.1), f4.st (by simp),
          f3.st hx'.2.1, f2.st hx'.1, f1.st hx],
        by rw [f7.sh hx'.2.2, f6.sh hx'.2.2, f5.sh (by simpa using hx'.2.1), f4.sh (by simp),
          f3.sh hx'.2.1, f2.sh hx'.1, f1.sh hx]⟩
    · simp only [List.mem_singleton] at hq
      rw [f7.val (by simp), f6.val (by simp), f5.val (by simp), f4.val (by simpa using hq), f3.val (by simp),
        f2.val (by simp), f1.val (by simp)]
    · rw [f7.cell, f6.cell, f5.cell, f4.cell, f3.cell, f2.cell, f1.cell]

end NearCubicGates.Close.Expand.Layout
