import Proof.Gates.Expand.PolyTabStage3b

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicGates.Close.Expand.PolyTab

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicGates.Close.CounterMachine NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats
open NearCubicWires.RepairRepresentation (natWord)

variable {te qa : ℕ}

local notation "WX" => WMX (NSx te qa) NRk
local notation "WSt" => WState (NSx te qa) NRk

def cmBody (X : Fin (NSx te qa + 1)) : WX :=
  .seq (rdF X (rX 31)) (.seq (skF X (rX 31)) (.seq (WMX.inc (rX 31)) (.seq (skF X (rX 31))
    (.seq (lnF X 32) (mxF 33 32)))))

def cmScan (X : Fin (NSx te qa + 1)) : WX :=
  .seq (rdF X (rX 30)) (.whr (rX 30) (.seq (WMX.dec (rX 30)) (cmBody X)))

/-- The per-step cost bound of the scan. -/
def Ctm {V : ℕ} (P : Terms V) : ℕ := 400 * (V + (termsWord P).length + 1) ^ 2 + 100

/-- What the scan's registers start from: everything it uses is `0`. -/
def ScanZero (g : Fin 64 → ℕ) : Prop := ∀ j : Fin 64, j.val ∈ [3, 4, 5, 6, 7, 30, 31, 32, 33, 34, 35, 36, 37, 38] → g j = 0

/-- The positions of monomial `k`'s fields. -/
theorem cm_idx {V : ℕ} (P : Terms V) (k : ℕ) (hk : k < P.length) :
    (termsN P)[posT P k]? = some ((P[k].1.sort (· ≤ ·)).map Fin.val).length ∧
    (termsN P)[posT P k + (((P[k].1.sort (· ≤ ·)).map Fin.val).length + 2)]? = some P[k].2.natAbs ∧
    posT P k + (((P[k].1.sort (· ≤ ·)).map Fin.val).length + 2) < (termsN P).length ∧
    posT P (k + 1) ≤ (termsN P).length := by
  have hl := termsN_length P
  have hsucc := posT_succ P k hk
  have hlast : posT P (k + 1) ≤ posT P P.length := by
    unfold posT
    have h1 : ((P.take (k + 1)).map fun t => (monoN t).length).sum ≤
        ((P.take P.length).map fun t => (monoN t).length).sum := by
      rw [List.take_length]
      exact ((List.take_sublist _ _).map _).sum_le_sum (fun _ _ => Nat.zero_le _)
    omega
  refine ⟨?_, ?_, by omega, by omega⟩
  · have := termsN_at P k 0 hk (by simp [monoN]); rw [Nat.add_zero] at this; rw [this]; simp [monoN]
  · rw [termsN_at P k _ hk (by rw [monoN_length]; omega)]
    simp [monoN, intN, List.getElem?_append_right]

theorem cmBody_spec (cap : ℕ) {V : ℕ} (P : Terms V) (σ0 : WSt) (X : Fin (NSx te qa + 1))
    (Sx : List (Fin (NSx te qa + 1))) (rest : List Bool) (g : Fin 64 → ℕ) (hg : ScanZero g)
    (hcap : 2 ^ ((termsWord P).length + 1) + 8 * (V + (termsWord P).length + 1) ^ 2 ≤ cap)
    (k : ℕ) (hk : k < P.length) (v : ℕ) (σ : WSt)
    (h : PS σ0 X Sx (termsN P) rest (posT P k) (Function.update (Function.update g 33 (cmx P k)) 30 v) σ) :
    Runs cap (cmBody X) σ (6 * (Ctm P + 1))
      (PS σ0 X Sx (termsN P) rest (posT P (k + 1)) (Function.update (Function.update g 33 (cmx P (k + 1))) 30 v)) := by
  set t := P[k] with ht
  set m := ((t.1.sort (· ≤ ·)).map Fin.val).length with hm
  have hmV : m ≤ V := by
    rw [hm, List.length_map, Finset.length_sort]; exact (Finset.card_le_univ _).trans (by simp)
  have hTW : ((termsN P).flatMap natWord).length = (termsWord P).length := by rw [termsWord_eq]
  have hfit : ∀ x ∈ termsN P, natBitLength x + 1 ≤ (termsWord P).length := fun x hx =>
    (natBitLength_le_word x).trans ((flatMap_natWord_ge _ x hx).trans hTW.le)
  have hpw := Nat.lt_two_pow_self (n := (termsWord P).length + 1)
  have hsq : V + (termsWord P).length + 1 ≤ (V + (termsWord P).length + 1) ^ 2 := by nlinarith
  have hfit' : ∀ x ∈ termsN P, natBitLength x + 1 ≤ cap := fun x hx => by have := hfit x hx; omega
  have hsucc := posT_succ P k hk
  obtain ⟨i0, i2, hlt2, hlast⟩ := cm_idx P k hk
  rw [← ht] at i0 i2 hlt2 hsucc
  rw [← hm] at i0 i2 hlt2 hsucc
  have hlt0 : posT P k < (termsN P).length := by omega
  have g3 := hg 3 (by simp); have g4 := hg 4 (by simp); have g5 := hg 5 (by simp); have g6 := hg 6 (by simp)
  have g7 := hg 7 (by simp); have g31 := hg 31 (by simp); have g32 := hg 32 (by simp)
  have g34 := hg 34 (by simp); have g35 := hg 35 (by simp); have g36 := hg 36 (by simp)
  have g37 := hg 37 (by simp); have g38 := hg 38 (by simp)
  have hCt : 400 * (V + (termsWord P).length + 1) ^ 2 + 100 ≤ Ctm P := le_refl _
  -- read the variable count
  have hrd := rdCost_le m (V + (termsWord P).length) (by omega)
  obtain ⟨τ1, e1, p1⟩ := (ps_rd cap 31 (by decide) h hlt0 (by simp [g3]) (by simp [g4]) (by simp [g5])
    (by simp [g6]) (by simp [g31]) (by
      have := hfit _ (List.getElem_mem hlt0)
      exact le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) (by omega))).cost (c' := Ctm P) (by
        rw [getElem_of_getElem? i0]; unfold Ctm; omega)
  rw [getElem_of_getElem? i0] at p1
  -- skip the variables
  obtain ⟨τ2, e2, p2⟩ := (ps_sk cap 31 (by decide) (m := m) p1 (by omega) (by simp [g3]) (by simp [g4])
    (by simp) hfit' (by omega)).cost (c' := Ctm P) (by
      have := skCost_le (termsN P) (posT P k + 1) m; unfold Ctm; nlinarith)
  -- skip the sign
  obtain ⟨τ3, e3, p3⟩ := (ps_inc cap 31 p2 0 (by simp) (by omega)).cost (c' := Ctm P) (by unfold Ctm; omega)
  obtain ⟨τ4, e4, p4⟩ := (ps_sk cap 31 (by decide) (m := 1) p3 (by omega) (by simp [g3]) (by simp [g4])
    (by simp) hfit' (by omega)).cost (c' := Ctm P) (by
      have := skCost_le (termsN P) (posT P k + 1 + m) 1; unfold Ctm; nlinarith)
  have q4 := p4.idx (show posT P k + 1 + m + 1 = posT P k + (m + 2) by omega)
  -- measure the magnitude
  have hnb : natBitLength t.2.natAbs + 1 ≤ (termsWord P).length := by
    have := hfit _ (List.getElem_mem hlt2); rwa [getElem_of_getElem? i2] at this
  obtain ⟨τ5, e5, p5⟩ := (ps_len cap 32 (by decide) q4 hlt2 (by simp [g36]) (by simp [g37]) (by simp [g38])
    (by simp [g32]; rw [getElem_of_getElem? i2]; omega)).cost (c' := Ctm P) (by
      rw [getElem_of_getElem? i2]; unfold Ctm; nlinarith)
  rw [getElem_of_getElem? i2] at p5
  -- the maximum
  have hcx := cmx_le P k
  obtain ⟨τ6, e6, p6⟩ := (ps_max cap 33 32 (by decide) p5 (by simp [g34]) (by simp [g35]) (by simp [g7])
    (by simp [g32]; omega)).cost (c' := Ctm P) (by simp [g32]; unfold Ctm; nlinarith)
  refine ⟨τ6, WXExec.mono (WXExec.seq e1 <| WXExec.seq e2 <| WXExec.seq e3 <| WXExec.seq e4 <| WXExec.seq e5 e6)
    (by omega), ?_⟩
  refine (p6.congr fun j => ?_).idx (by rw [hsucc]; omega)
  rw [cmx_succ P k hk, ← ht]
  simp only [Function.update_apply]
  by_cases j32 : j = 32
  · subst j32; simp [g32]
  · by_cases j33 : j = 33
    · subst j33; simp [g32]
    · by_cases j31 : j = 31
      · subst j31; simp [g31]
      · simp [j31, j32, j33]

theorem cmScan_spec (cap : ℕ) {V : ℕ} (P : Terms V) (σ0 : WSt) (X : Fin (NSx te qa + 1))
    (Sx : List (Fin (NSx te qa + 1))) (rest : List Bool) (g : Fin 64 → ℕ) (hg : ScanZero g)
    (hcap : 2 ^ ((termsWord P).length + 1) + 8 * (V + (termsWord P).length + 1) ^ 2 ≤ cap) (σ : WSt)
    (h : PS σ0 X Sx (termsN P) rest 0 g σ) :
    Runs cap (cmScan X) σ (Ctm P + 1 + (P.length * (6 * (Ctm P + 1) + 4) + 1))
      (PS σ0 X Sx (termsN P) rest (posT P P.length) (Function.update g 33 (cmx P P.length))) := by
  have hTW : ((termsN P).flatMap natWord).length = (termsWord P).length := by rw [termsWord_eq]
  have hfit : ∀ x ∈ termsN P, natBitLength x + 1 ≤ (termsWord P).length := fun x hx =>
    (natBitLength_le_word x).trans ((flatMap_natWord_ge _ x hx).trans hTW.le)
  have hpw := Nat.lt_two_pow_self (n := (termsWord P).length + 1)
  have hsq : V + (termsWord P).length + 1 ≤ (V + (termsWord P).length + 1) ^ 2 := by nlinarith
  have hPl : P.length ≤ (termsWord P).length := by
    have h1 : (termsN P).length ≤ ((termsN P).flatMap natWord).length := by
      rw [List.length_flatMap]
      calc (termsN P).length = ((termsN P).map fun _ => 1).sum := by simp
        _ ≤ ((termsN P).map fun x => (natWord x).length).sum :=
          List.sum_le_sum fun x _ => by have := natBitLength_le_word x; omega
    have h2 : P.length ≤ (termsN P).length := by
      have : P.length ≤ (P.map fun a => (monoN a).length).sum := by
        calc P.length = (P.map fun _ => 1).sum := by simp
          _ ≤ (P.map fun a => (monoN a).length).sum := List.sum_le_sum fun t _ => by rw [monoN_length]; omega
      simp [termsN, List.length_flatMap]; omega
    omega
  have i0 : (termsN P)[0]? = some P.length := by simp [termsN]
  have g30 := hg 30 (by simp); have g33 := hg 33 (by simp)
  have g3 := hg 3 (by simp); have g4 := hg 4 (by simp); have g5 := hg 5 (by simp); have g6 := hg 6 (by simp)
  have hl0 : 0 < (termsN P).length := by simp [termsN]
  obtain ⟨τ1, e1, p1⟩ := (ps_rd cap 30 (by decide) h hl0 g3 g4 g5 g6 g30 (by
      have := hfit _ (List.getElem_mem hl0)
      exact le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) (by omega))).cost (c' := Ctm P) (by
        rw [getElem_of_getElem? i0]
        have := rdCost_le P.length (V + (termsWord P).length) (by omega); unfold Ctm; omega)
  rw [getElem_of_getElem? i0] at p1
  let Inv : ℕ → WSt → Prop := fun k τ =>
    PS σ0 X Sx (termsN P) rest (posT P k) (Function.update (Function.update g 33 (cmx P k)) 30 (τ.val (rX 30))) τ
  have hI0 : Inv 0 τ1 := by
    refine (p1.congr fun j => ?_).idx (by simp [posT])
    rw [p1.x 30]
    by_cases j30 : j = 30
    · subst j30; simp
    · by_cases j33 : j = 33
      · subst j33; simp [cmx, g33]
      · simp [Function.update_apply, j30, j33]
  have hloop := Runs.count (cap := cap) (K := rX 30) (body := cmBody X) (6 * (Ctm P + 1)) P.length Inv
    (by omega) (by
      intro k hk τ hτ hK
      have hτ' : PS σ0 X Sx (termsN P) rest (posT P k)
          (Function.update (Function.update g 33 (cmx P k)) 30 (P.length - k - 1))
          (τ.setv (rX 30) (P.length - k - 1)) := by
        have := ps_reg hτ 30 (P.length - k - 1) rfl
        exact this.congr fun j => by simp [Function.update_apply]; split_ifs <;> simp_all
      refine (cmBody_spec cap P σ0 X Sx rest g hg hcap k hk _ _ hτ').post fun ρ hρ => ⟨?_, ?_⟩
      · refine hρ.congr fun j => ?_
        rw [hρ.x 30]; simp
      · rw [hρ.x 30]; simp)
    τ1 hI0 (by rw [p1.x 30]; simp)
  refine (Runs.seqE e1 hloop).cost (by omega) |>.post fun ρ ⟨hρ, hK⟩ => ?_
  refine hρ.congr fun j => ?_
  rw [hK]
  by_cases j30 : j = 30
  · subst j30; simp [g30]
  · simp [Function.update_apply, j30]

end NearCubicGates.Close.Expand.PolyTab
