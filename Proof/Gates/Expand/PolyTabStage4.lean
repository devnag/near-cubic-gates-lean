import Proof.Gates.Expand.PolyTabStage3c

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

namespace NearCubicGates.Close.Expand.PolyTab

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicGates.Close.CounterMachine NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats

variable {te qa : ℕ}

local notation "WX" => WMX (NSx te qa) NRk
local notation "WSt" => WState (NSx te qa) NRk

/-- The per-step cost bound of stage 4. -/
def C4 (E : ExpandMachine) (r : TabReq) : ℕ := 100 * (Wdk E r + 2) ^ 2

/-- The registers stage 4 reads, and the ones it writes are `0`. -/
structure WeakWorker (E : ExpandMachine) (r : TabReq) (f : Fin 64 → ℕ) : Prop where
  h10 : f 10 = r.n
  h11 : f 11 = r.k
  h12 : f 12 = r.s
  h13 : f 13 = r.B
  h18 : f 18 = r.V
  h33 : f 33 = Cm E r
  z7 : f 7 = 0
  z40 : f 40 = 0
  z41 : f 41 = 0
  z42 : f 42 = 0
  z44 : f 44 = 0
  z45 : f 45 = 0
  z46 : f 46 = 0
  z47 : f 47 = 0
  z48 : f 48 = 0
  z49 : f 49 = 0
  z50 : f 50 = 0
  z53 : f 53 = 0
  h14 : f 14 = r.G

theorem W4b (E : ExpandMachine) (r : TabReq) :
    Wk E r = (r.V + 2) * (3 * r.B + 2 * r.n + 6 * r.s + r.k + r.V * (r.s + 1) + 20) + Cm E r + r.G ∧
    (r.V + 2) * (3 * r.B + 2 * r.n + 6 * r.s + r.k + r.V * (r.s + 1) + 20) ≤ Wdk E r + 1 ∧
    (r.s + 1) * (Wk E r + 1) ≤ Wdk E r + 1 ∧
    3 * r.B + 2 * r.n + 6 * r.s + r.k + r.V * (r.s + 1) + 20 ≤ Wk E r ∧ Wk E r ≤ Wdk E r ∧
    r.V + 2 ≤ Wk E r ∧ r.s + 1 ≤ Wk E r ∧ Cm E r ≤ Wk E r ∧ r.V * (r.s + 1) ≤ Wk E r := by
  have hWdef : Wk E r = (r.V + 2) * (3 * r.B + 2 * r.n + 6 * r.s + r.k + r.V * (r.s + 1) + 20) + Cm E r + r.G := by
    unfold Wk Dm; ring
  have hWd : Wdk E r + 1 = (r.s + 1) * (Wk E r + 1) := Wdk_succ E r
  have h1 : 3 * r.B + 2 * r.n + 6 * r.s + r.k + r.V * (r.s + 1) + 20 ≤
      (r.V + 2) * (3 * r.B + 2 * r.n + 6 * r.s + r.k + r.V * (r.s + 1) + 20) := Nat.le_mul_of_pos_left _ (by omega)
  have h2 : Wk E r ≤ Wdk E r := by nlinarith
  have h3 : r.V + 2 ≤ (r.V + 2) * (3 * r.B + 2 * r.n + 6 * r.s + r.k + r.V * (r.s + 1) + 20) :=
    Nat.le_mul_of_pos_right _ (by omega)
  have h4 : r.s + 1 ≤ r.V * (r.s + 1) + r.s + 1 := by omega
  refine ⟨hWdef, by omega, by omega, by omega, h2, by omega, by omega, by omega, by omega⟩

theorem cap_add (E : ExpandMachine) (r : TabReq) (cap : ℕ) (hcap : 4 * (Wdk E r + 2) ^ 2 ≤ cap) (x y : ℕ)
    (hx : x ≤ Wdk E r + 1) (hy : y ≤ Wdk E r + 1) : x + y ≤ cap := by nlinarith
theorem cap_inc (E : ExpandMachine) (r : TabReq) (cap : ℕ) (hcap : 4 * (Wdk E r + 2) ^ 2 ≤ cap) (x : ℕ)
    (hx : x ≤ Wdk E r + 1) : x < cap := by nlinarith
theorem cap_dec (E : ExpandMachine) (r : TabReq) (cap : ℕ) (hcap : 4 * (Wdk E r + 2) ^ 2 ≤ cap) (x : ℕ)
    (hx : x ≤ Wdk E r + 1) : x ≤ cap := by nlinarith
theorem cap_mul1 (E : ExpandMachine) (r : TabReq) (cap : ℕ) (hcap : 4 * (Wdk E r + 2) ^ 2 ≤ cap) (x y : ℕ)
    (hxy : x * y ≤ Wdk E r + 1) : 0 + x * y ≤ cap := by nlinarith
theorem cap_mul2 (E : ExpandMachine) (r : TabReq) (cap : ℕ) (hcap : 4 * (Wdk E r + 2) ^ 2 ≤ cap) (x : ℕ)
    (hx : x ≤ Wdk E r + 1) : 2 * x ≤ cap := by nlinarith
theorem sq2 (E : ExpandMachine) (r : TabReq) : Wdk E r + 2 ≤ (Wdk E r + 2) ^ 2 := by nlinarith
theorem cst_add (E : ExpandMachine) (r : TabReq) (y : ℕ) (hy : y ≤ Wdk E r + 1) : 18 * y + 3 ≤ C4 E r := by
  have := sq2 E r; unfold C4; omega
theorem cst_c (E : ExpandMachine) (r : TabReq) (c : ℕ) (hc : c ≤ 3) : c ≤ C4 E r := by
  have := sq2 E r; unfold C4; omega
theorem cst_mul (E : ExpandMachine) (r : TabReq) (x y : ℕ) (hx : x ≤ Wdk E r + 1) (hxy : x * y ≤ Wdk E r + 1) :
    x * (18 * y + 3 + 8) + 7 * x + 3 ≤ C4 E r := by
  unfold C4; nlinarith

def st4a : WX :=
  .seq (addR (rX 12) (rX 45) (rX 7)) <|
  .seq (WMX.inc (rX 45)) <|
  mulR (rX 18) (rX 53) (rX 45) (rX 46) (rX 7)

theorem st4a_spec (cap : ℕ) (E : ExpandMachine) (r : TabReq) {σ0 : WSt} {X : Fin (NSx te qa + 1)}
    {Sx : List (Fin (NSx te qa + 1))} {L : List ℕ} {rest : List Bool} {i : ℕ} {f : Fin 64 → ℕ} {σ : WSt}
    (H : WeakWorker E r f) (hcap : 4 * (Wdk E r + 2) ^ 2 ≤ cap) (h : PS σ0 X Sx L rest i (f) σ) :
    Runs cap st4a σ (3 * (C4 E r + 1)) (PS σ0 X Sx L rest i (Function.update (Function.update f 45 (r.s + 1)) 46 (r.V * (r.s + 1)))) := by
  obtain ⟨h10, h11, h12, h13, h18, h33, z7, z40, z41, z42, z44, z45, z46, z47, z48, z49, z50, z53⟩ := H
  obtain ⟨hWdef, hP1, hP2, hb1, hb2, hb3, hb4, hb5, hb6⟩ := W4b E r
  have hWd' : (r.s + 1) * (Wk E r + 1) = Wdk E r + 1 := (Wdk_succ E r).symm
  obtain ⟨τ1, e1, p1⟩ := (ps_add cap 45 12 (by decide) (by decide) (by decide) h (0) (r.s)
    (by simp [Function.update_apply, h10, h11, h12, h13, h18, h33, z7, z40, z41, z42, z44, z45, z46, z47, z48, z49, z50, z53] <;> ring) (by simp [Function.update_apply, h10, h11, h12, h13, h18, h33, z7, z40, z41, z42, z44, z45, z46, z47, z48, z49, z50, z53] <;> ring)
    (by simp [Function.update_apply, h10, h11, h12, h13, h18, h33, z7, z40, z41, z42, z44, z45, z46, z47, z48, z49, z50, z53]) (cap_add E r cap hcap _ _ (by omega) (by omega))).cost
    (cst_add E r _ (by omega))
  obtain ⟨τ2, e2, p2⟩ := (ps_inc cap 45 p1 (r.s) (by simp [Function.update_apply, h10, h11, h12, h13, h18, h33, z7, z40, z41, z42, z44, z45, z46, z47, z48, z49, z50, z53] <;> ring)
    (cap_inc E r cap hcap _ (by omega))).cost (cst_c E r 3 (by norm_num))
  obtain ⟨τ3, e3, p3⟩ := (ps_mul cap 18 53 45 46 (by decide) p2 (r.V) (r.s + 1) (0)
    (by simp [Function.update_apply, h10, h11, h12, h13, h18, h33, z7, z40, z41, z42, z44, z45, z46, z47, z48, z49, z50, z53] <;> ring) (by simp [Function.update_apply, h10, h11, h12, h13, h18, h33, z7, z40, z41, z42, z44, z45, z46, z47, z48, z49, z50, z53] <;> ring)
    (by simp [Function.update_apply, h10, h11, h12, h13, h18, h33, z7, z40, z41, z42, z44, z45, z46, z47, z48, z49, z50, z53] <;> ring) (by simp [Function.update_apply, h10, h11, h12, h13, h18, h33, z7, z40, z41, z42, z44, z45, z46, z47, z48, z49, z50, z53])
    (by simp [Function.update_apply, h10, h11, h12, h13, h18, h33, z7, z40, z41, z42, z44, z45, z46, z47, z48, z49, z50, z53]) (cap_mul1 E r cap hcap _ _ (by omega)) (cap_mul2 E r cap hcap _ (by omega))).cost
    (cst_mul E r _ _ (by omega) (by omega))
  refine ⟨τ3, WXExec.mono (WXExec.seq e1 <| WXExec.seq e2 <| e3) (by omega), ?_⟩
  refine p3.congr fun j => ?_
  simp only [Function.update_apply]
  split_ifs <;> (try simp_all) <;> ring

def st4b : WX :=
  .seq (addR (rX 13) (rX 47) (rX 7)) <|
  .seq (addR (rX 13) (rX 47) (rX 7)) <|
  .seq (addR (rX 13) (rX 47) (rX 7)) <|
  .seq (addR (rX 10) (rX 47) (rX 7)) <|
  .seq (addR (rX 10) (rX 47) (rX 7)) <|
  .seq (addR (rX 12) (rX 47) (rX 7)) <|
  .seq (addR (rX 12) (rX 47) (rX 7)) <|
  .seq (addR (rX 12) (rX 47) (rX 7)) <|
  .seq (addR (rX 12) (rX 47) (rX 7)) <|
  .seq (addR (rX 12) (rX 47) (rX 7)) <|
  .seq (addR (rX 12) (rX 47) (rX 7)) <|
  .seq (addR (rX 11) (rX 47) (rX 7)) <|
  addR (rX 46) (rX 47) (rX 7)

theorem st4b_spec (cap : ℕ) (E : ExpandMachine) (r : TabReq) {σ0 : WSt} {X : Fin (NSx te qa + 1)}
    {Sx : List (Fin (NSx te qa + 1))} {L : List ℕ} {rest : List Bool} {i : ℕ} {f : Fin 64 → ℕ} {σ : WSt}
    (H : WeakWorker E r f) (hcap : 4 * (Wdk E r + 2) ^ 2 ≤ cap) (h : PS σ0 X Sx L rest i (Function.update (Function.update f 45 (r.s + 1)) 46 (r.V * (r.s + 1))) σ) :
    Runs cap st4b σ (13 * (C4 E r + 1)) (PS σ0 X Sx L rest i (Function.update (Function.update (Function.update f 45 (r.s + 1)) 46 (r.V * (r.s + 1))) 47 (3 * r.B + 2 * r.n + 6 * r.s + r.k + r.V * (r.s + 1)))) := by
  obtain ⟨h10, h11, h12, h13, h18, h33, z7, z40, z41, z42, z44, z45, z46, z47, z48, z49, z50, z53⟩ := H
  obtain ⟨hWdef, hP1, hP2, hb1, hb2, hb3, hb4, hb5, hb6⟩ := W4b E r
  have hWd' : (r.s + 1) * (Wk E r + 1) = Wdk E r + 1 := (Wdk_succ E r).symm
  obtain ⟨τ1, e1, p1⟩ := (ps_add cap 47 13 (by decide) (by decide) (by decide) h (0) (r.B)
    (by simp [Function.update_apply, h10, h11, h12, h13, h18, h33, z7, z40, z41, z42, z44, z45, z46, z47, z48, z49, z50, z53] <;> ring) (by simp [Function.update_apply, h10, h11, h12, h13, h18, h33, z7, z40, z41, z42, z44, z45, z46, z47, z48, z49, z50, z53] <;> ring)
    (by simp [Function.update_apply, h10, h11, h12, h13, h18, h33, z7, z40, z41, z42, z44, z45, z46, z47, z48, z49, z50, z53]) (cap_add E r cap hcap _ _ (by omega) (by omega))).cost
    (cst_add E r _ (by omega))
  obtain ⟨τ2, e2, p2⟩ := (ps_add cap 47 13 (by decide) (by decide) (by decide) p1 (r.B) (r.B)
    (by simp [Function.update_apply, h10, h11, h12, h13, h18, h33, z7, z40, z41, z42, z44, z45, z46, z47, z48, z49, z50, z53] <;> ring) (by simp [Function.update_apply, h10, h11, h12, h13, h18, h33, z7, z40, z41, z42, z44, z45, z46, z47, z48, z49, z50, z53] <;> ring)
    (by simp [Function.update_apply, h10, h11, h12, h13, h18, h33, z7, z40, z41, z42, z44, z45, z46, z47, z48, z49, z50, z53]) (cap_add E r cap hcap _ _ (by omega) (by omega))).cost
    (cst_add E r _ (by omega))
  obtain ⟨τ3, e3, p3⟩ := (ps_add cap 47 13 (by decide) (by decide) (by decide) p2 (2 * r.B) (r.B)
    (by simp [Function.update_apply, h10, h11, h12, h13, h18, h33, z7, z40, z41, z42, z44, z45, z46, z47, z48, z49, z50, z53] <;> ring) (by simp [Function.update_apply, h10, h11, h12, h13, h18, h33, z7, z40, z41, z42, z44, z45, z46, z47, z48, z49, z50, z53] <;> ring)
    (by simp [Function.update_apply, h10, h11, h12, h13, h18, h33, z7, z40, z41, z42, z44, z45, z46, z47, z48, z49, z50, z53]) (cap_add E r cap hcap _ _ (by omega) (by omega))).cost
    (cst_add E r _ (by omega))
  obtain ⟨τ4, e4, p4⟩ := (ps_add cap 47 10 (by decide) (by decide) (by decide) p3 (3 * r.B) (r.n)
    (by simp [Function.update_apply, h10, h11, h12, h13, h18, h33, z7, z40, z41, z42, z44, z45, z46, z47, z48, z49, z50, z53] <;> ring) (by simp [Function.update_apply, h10, h11, h12, h13, h18, h33, z7, z40, z41, z42, z44, z45, z46, z47, z48, z49, z50, z53] <;> ring)
    (by simp [Function.update_apply, h10, h11, h12, h13, h18, h33, z7, z40, z41, z42, z44, z45, z46, z47, z48, z49, z50, z53]) (cap_add E r cap hcap _ _ (by omega) (by omega))).cost
    (cst_add E r _ (by omega))
  obtain ⟨τ5, e5, p5⟩ := (ps_add cap 47 10 (by decide) (by decide) (by decide) p4 (3 * r.B + r.n) (r.n)
    (by simp [Function.update_apply, h10, h11, h12, h13, h18, h33, z7, z40, z41, z42, z44, z45, z46, z47, z48, z49, z50, z53] <;> ring) (by simp [Function.update_apply, h10, h11, h12, h13, h18, h33, z7, z40, z41, z42, z44, z45, z46, z47, z48, z49, z50, z53] <;> ring)
    (by simp [Function.update_apply, h10, h11, h12, h13, h18, h33, z7, z40, z41, z42, z44, z45, z46, z47, z48, z49, z50, z53]) (cap_add E r cap hcap _ _ (by omega) (by omega))).cost
    (cst_add E r _ (by omega))
  obtain ⟨τ6, e6, p6⟩ := (ps_add cap 47 12 (by decide) (by decide) (by decide) p5 (3 * r.B + 2 * r.n) (r.s)
    (by simp [Function.update_apply, h10, h11, h12, h13, h18, h33, z7, z40, z41, z42, z44, z45, z46, z47, z48, z49, z50, z53] <;> ring) (by simp [Function.update_apply, h10, h11, h12, h13, h18, h33, z7, z40, z41, z42, z44, z45, z46, z47, z48, z49, z50, z53] <;> ring)
    (by simp [Function.update_apply, h10, h11, h12, h13, h18, h33, z7, z40, z41, z42, z44, z45, z46, z47, z48, z49, z50, z53]) (cap_add E r cap hcap _ _ (by omega) (by omega))).cost
    (cst_add E r _ (by omega))
  obtain ⟨τ7, e7, p7⟩ := (ps_add cap 47 12 (by decide) (by decide) (by decide) p6 (3 * r.B + 2 * r.n + r.s) (r.s)
    (by simp [Function.update_apply, h10, h11, h12, h13, h18, h33, z7, z40, z41, z42, z44, z45, z46, z47, z48, z49, z50, z53] <;> ring) (by simp [Function.update_apply, h10, h11, h12, h13, h18, h33, z7, z40, z41, z42, z44, z45, z46, z47, z48, z49, z50, z53] <;> ring)
    (by simp [Function.update_apply, h10, h11, h12, h13, h18, h33, z7, z40, z41, z42, z44, z45, z46, z47, z48, z49, z50, z53]) (cap_add E r cap hcap _ _ (by omega) (by omega))).cost
    (cst_add E r _ (by omega))
  obtain ⟨τ8, e8, p8⟩ := (ps_add cap 47 12 (by decide) (by decide) (by decide) p7 (3 * r.B + 2 * r.n + 2 * r.s) (r.s)
    (by simp [Function.update_apply, h10, h11, h12, h13, h18, h33, z7, z40, z41, z42, z44, z45, z46, z47, z48, z49, z50, z53] <;> ring) (by simp [Function.update_apply, h10, h11, h12, h13, h18, h33, z7, z40, z41, z42, z44, z45, z46, z47, z48, z49, z50, z53] <;> ring)
    (by simp [Function.update_apply, h10, h11, h12, h13, h18, h33, z7, z40, z41, z42, z44, z45, z46, z47, z48, z49, z50, z53]) (cap_add E r cap hcap _ _ (by omega) (by omega))).cost
    (cst_add E r _ (by omega))
  obtain ⟨τ9, e9, p9⟩ := (ps_add cap 47 12 (by decide) (by decide) (by decide) p8 (3 * r.B + 2 * r.n + 3 * r.s) (r.s)
    (by simp [Function.update_apply, h10, h11, h12, h13, h18, h33, z7, z40, z41, z42, z44, z45, z46, z47, z48, z49, z50, z53] <;> ring) (by simp [Function.update_apply, h10, h11, h12, h13, h18, h33, z7, z40, z41, z42, z44, z45, z46, z47, z48, z49, z50, z53] <;> ring)
    (by simp [Function.update_apply, h10, h11, h12, h13, h18, h33, z7, z40, z41, z42, z44, z45, z46, z47, z48, z49, z50, z53]) (cap_add E r cap hcap _ _ (by omega) (by omega))).cost
    (cst_add E r _ (by omega))
  obtain ⟨τ10, e10, p10⟩ := (ps_add cap 47 12 (by decide) (by decide) (by decide) p9 (3 * r.B + 2 * r.n + 4 * r.s) (r.s)
    (by simp [Function.update_apply, h10, h11, h12, h13, h18, h33, z7, z40, z41, z42, z44, z45, z46, z47, z48, z49, z50, z53] <;> ring) (by simp [Function.update_apply, h10, h11, h12, h13, h18, h33, z7, z40, z41, z42, z44, z45, z46, z47, z48, z49, z50, z53] <;> ring)
    (by simp [Function.update_apply, h10, h11, h12, h13, h18, h33, z7, z40, z41, z42, z44, z45, z46, z47, z48, z49, z50, z53]) (cap_add E r cap hcap _ _ (by omega) (by omega))).cost
    (cst_add E r _ (by omega))
  obtain ⟨τ11, e11, p11⟩ := (ps_add cap 47 12 (by decide) (by decide) (by decide) p10 (3 * r.B + 2 * r.n + 5 * r.s) (r.s)
    (by simp [Function.update_apply, h10, h11, h12, h13, h18, h33, z7, z40, z41, z42, z44, z45, z46, z47, z48, z49, z50, z53] <;> ring) (by simp [Function.update_apply, h10, h11, h12, h13, h18, h33, z7, z40, z41, z42, z44, z45, z46, z47, z48, z49, z50, z53] <;> ring)
    (by simp [Function.update_apply, h10, h11, h12, h13, h18, h33, z7, z40, z41, z42, z44, z45, z46, z47, z48, z49, z50, z53]) (cap_add E r cap hcap _ _ (by omega) (by omega))).cost
    (cst_add E r _ (by omega))
  obtain ⟨τ12, e12, p12⟩ := (ps_add cap 47 11 (by decide) (by decide) (by decide) p11 (3 * r.B + 2 * r.n + 6 * r.s) (r.k)
    (by simp [Function.update_apply, h10, h11, h12, h13, h18, h33, z7, z40, z41, z42, z44, z45, z46, z47, z48, z49, z50, z53] <;> ring) (by simp [Function.update_apply, h10, h11, h12, h13, h18, h33, z7, z40, z41, z42, z44, z45, z46, z47, z48, z49, z50, z53] <;> ring)
    (by simp [Function.update_apply, h10, h11, h12, h13, h18, h33, z7, z40, z41, z42, z44, z45, z46, z47, z48, z49, z50, z53]) (cap_add E r cap hcap _ _ (by omega) (by omega))).cost
    (cst_add E r _ (by omega))
  obtain ⟨τ13, e13, p13⟩ := (ps_add cap 47 46 (by decide) (by decide) (by decide) p12 (3 * r.B + 2 * r.n + 6 * r.s + r.k) (r.V * (r.s + 1))
    (by simp [Function.update_apply, h10, h11, h12, h13, h18, h33, z7, z40, z41, z42, z44, z45, z46, z47, z48, z49, z50, z53] <;> ring) (by simp [Function.update_apply, h10, h11, h12, h13, h18, h33, z7, z40, z41, z42, z44, z45, z46, z47, z48, z49, z50, z53] <;> ring)
    (by simp [Function.update_apply, h10, h11, h12, h13, h18, h33, z7, z40, z41, z42, z44, z45, z46, z47, z48, z49, z50, z53]) (cap_add E r cap hcap _ _ (by omega) (by omega))).cost
    (cst_add E r _ (by omega))
  refine ⟨τ13, WXExec.mono (WXExec.seq e1 <| WXExec.seq e2 <| WXExec.seq e3 <| WXExec.seq e4 <| WXExec.seq e5 <| WXExec.seq e6 <| WXExec.seq e7 <| WXExec.seq e8 <| WXExec.seq e9 <| WXExec.seq e10 <| WXExec.seq e11 <| WXExec.seq e12 <| e13) (by omega), ?_⟩
  refine p13.congr fun j => ?_
  simp only [Function.update_apply]
  split_ifs <;> (try simp_all) <;> ring

def st4c : WX :=
  .seq (WMX.inc (rX 48)) <|
  .seq (WMX.inc (rX 48)) <|
  .seq (WMX.inc (rX 48)) <|
  .seq (WMX.inc (rX 48)) <|
  .seq (WMX.inc (rX 48)) <|
  .seq (addR (rX 48) (rX 49) (rX 7)) <|
  .seq (addR (rX 48) (rX 49) (rX 7)) <|
  .seq (addR (rX 49) (rX 47) (rX 7)) <|
  addR (rX 49) (rX 47) (rX 7)

theorem st4c_spec (cap : ℕ) (E : ExpandMachine) (r : TabReq) {σ0 : WSt} {X : Fin (NSx te qa + 1)}
    {Sx : List (Fin (NSx te qa + 1))} {L : List ℕ} {rest : List Bool} {i : ℕ} {f : Fin 64 → ℕ} {σ : WSt}
    (H : WeakWorker E r f) (hcap : 4 * (Wdk E r + 2) ^ 2 ≤ cap) (h : PS σ0 X Sx L rest i (Function.update (Function.update (Function.update f 45 (r.s + 1)) 46 (r.V * (r.s + 1))) 47 (3 * r.B + 2 * r.n + 6 * r.s + r.k + r.V * (r.s + 1))) σ) :
    Runs cap st4c σ (9 * (C4 E r + 1)) (PS σ0 X Sx L rest i (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update f 45 (r.s + 1)) 46 (r.V * (r.s + 1))) 47 (3 * r.B + 2 * r.n + 6 * r.s + r.k + r.V * (r.s + 1))) 48 5) 49 10) 47 (3 * r.B + 2 * r.n + 6 * r.s + r.k + r.V * (r.s + 1) + 20))) := by
  obtain ⟨h10, h11, h12, h13, h18, h33, z7, z40, z41, z42, z44, z45, z46, z47, z48, z49, z50, z53⟩ := H
  obtain ⟨hWdef, hP1, hP2, hb1, hb2, hb3, hb4, hb5, hb6⟩ := W4b E r
  have hWd' : (r.s + 1) * (Wk E r + 1) = Wdk E r + 1 := (Wdk_succ E r).symm
  obtain ⟨τ1, e1, p1⟩ := (ps_inc cap 48 h (0) (by simp [Function.update_apply, h10, h11, h12, h13, h18, h33, z7, z40, z41, z42, z44, z45, z46, z47, z48, z49, z50, z53] <;> ring)
    (cap_inc E r cap hcap _ (by omega))).cost (cst_c E r 3 (by norm_num))
  obtain ⟨τ2, e2, p2⟩ := (ps_inc cap 48 p1 (1) (by simp [Function.update_apply, h10, h11, h12, h13, h18, h33, z7, z40, z41, z42, z44, z45, z46, z47, z48, z49, z50, z53] <;> ring)
    (cap_inc E r cap hcap _ (by omega))).cost (cst_c E r 3 (by norm_num))
  obtain ⟨τ3, e3, p3⟩ := (ps_inc cap 48 p2 (2) (by simp [Function.update_apply, h10, h11, h12, h13, h18, h33, z7, z40, z41, z42, z44, z45, z46, z47, z48, z49, z50, z53] <;> ring)
    (cap_inc E r cap hcap _ (by omega))).cost (cst_c E r 3 (by norm_num))
  obtain ⟨τ4, e4, p4⟩ := (ps_inc cap 48 p3 (3) (by simp [Function.update_apply, h10, h11, h12, h13, h18, h33, z7, z40, z41, z42, z44, z45, z46, z47, z48, z49, z50, z53] <;> ring)
    (cap_inc E r cap hcap _ (by omega))).cost (cst_c E r 3 (by norm_num))
  obtain ⟨τ5, e5, p5⟩ := (ps_inc cap 48 p4 (4) (by simp [Function.update_apply, h10, h11, h12, h13, h18, h33, z7, z40, z41, z42, z44, z45, z46, z47, z48, z49, z50, z53] <;> ring)
    (cap_inc E r cap hcap _ (by omega))).cost (cst_c E r 3 (by norm_num))
  obtain ⟨τ6, e6, p6⟩ := (ps_add cap 49 48 (by decide) (by decide) (by decide) p5 (0) (5)
    (by simp [Function.update_apply, h10, h11, h12, h13, h18, h33, z7, z40, z41, z42, z44, z45, z46, z47, z48, z49, z50, z53] <;> ring) (by simp [Function.update_apply, h10, h11, h12, h13, h18, h33, z7, z40, z41, z42, z44, z45, z46, z47, z48, z49, z50, z53] <;> ring)
    (by simp [Function.update_apply, h10, h11, h12, h13, h18, h33, z7, z40, z41, z42, z44, z45, z46, z47, z48, z49, z50, z53]) (cap_add E r cap hcap _ _ (by omega) (by omega))).cost
    (cst_add E r _ (by omega))
  obtain ⟨τ7, e7, p7⟩ := (ps_add cap 49 48 (by decide) (by decide) (by decide) p6 (5) (5)
    (by simp [Function.update_apply, h10, h11, h12, h13, h18, h33, z7, z40, z41, z42, z44, z45, z46, z47, z48, z49, z50, z53] <;> ring) (by simp [Function.update_apply, h10, h11, h12, h13, h18, h33, z7, z40, z41, z42, z44, z45, z46, z47, z48, z49, z50, z53] <;> ring)
    (by simp [Function.update_apply, h10, h11, h12, h13, h18, h33, z7, z40, z41, z42, z44, z45, z46, z47, z48, z49, z50, z53]) (cap_add E r cap hcap _ _ (by omega) (by omega))).cost
    (cst_add E r _ (by omega))
  obtain ⟨τ8, e8, p8⟩ := (ps_add cap 47 49 (by decide) (by decide) (by decide) p7 (3 * r.B + 2 * r.n + 6 * r.s + r.k + r.V * (r.s + 1)) (10)
    (by simp [Function.update_apply, h10, h11, h12, h13, h18, h33, z7, z40, z41, z42, z44, z45, z46, z47, z48, z49, z50, z53] <;> ring) (by simp [Function.update_apply, h10, h11, h12, h13, h18, h33, z7, z40, z41, z42, z44, z45, z46, z47, z48, z49, z50, z53] <;> ring)
    (by simp [Function.update_apply, h10, h11, h12, h13, h18, h33, z7, z40, z41, z42, z44, z45, z46, z47, z48, z49, z50, z53]) (cap_add E r cap hcap _ _ (by omega) (by omega))).cost
    (cst_add E r _ (by omega))
  obtain ⟨τ9, e9, p9⟩ := (ps_add cap 47 49 (by decide) (by decide) (by decide) p8 (3 * r.B + 2 * r.n + 6 * r.s + r.k + r.V * (r.s + 1) + 10) (10)
    (by simp [Function.update_apply, h10, h11, h12, h13, h18, h33, z7, z40, z41, z42, z44, z45, z46, z47, z48, z49, z50, z53] <;> ring) (by simp [Function.update_apply, h10, h11, h12, h13, h18, h33, z7, z40, z41, z42, z44, z45, z46, z47, z48, z49, z50, z53] <;> ring)
    (by simp [Function.update_apply, h10, h11, h12, h13, h18, h33, z7, z40, z41, z42, z44, z45, z46, z47, z48, z49, z50, z53]) (cap_add E r cap hcap _ _ (by omega) (by omega))).cost
    (cst_add E r _ (by omega))
  refine ⟨τ9, WXExec.mono (WXExec.seq e1 <| WXExec.seq e2 <| WXExec.seq e3 <| WXExec.seq e4 <| WXExec.seq e5 <| WXExec.seq e6 <| WXExec.seq e7 <| WXExec.seq e8 <| e9) (by omega), ?_⟩
  refine p9.congr fun j => ?_
  simp only [Function.update_apply]
  split_ifs <;> (try simp_all) <;> ring

def st4d : WX :=
  .seq (addR (rX 18) (rX 50) (rX 7)) <|
  .seq (WMX.inc (rX 50)) <|
  .seq (WMX.inc (rX 50)) <|
  .seq (mulR (rX 50) (rX 53) (rX 47) (rX 40) (rX 7)) <|
  .seq (addR (rX 33) (rX 40) (rX 7)) (addR (rX 14) (rX 40) (rX 7))

theorem st4d_spec (cap : ℕ) (E : ExpandMachine) (r : TabReq) {σ0 : WSt} {X : Fin (NSx te qa + 1)}
    {Sx : List (Fin (NSx te qa + 1))} {L : List ℕ} {rest : List Bool} {i : ℕ} {f : Fin 64 → ℕ} {σ : WSt}
    (H : WeakWorker E r f) (hcap : 4 * (Wdk E r + 2) ^ 2 ≤ cap) (h : PS σ0 X Sx L rest i (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update f 45 (r.s + 1)) 46 (r.V * (r.s + 1))) 47 (3 * r.B + 2 * r.n + 6 * r.s + r.k + r.V * (r.s + 1))) 48 5) 49 10) 47 (3 * r.B + 2 * r.n + 6 * r.s + r.k + r.V * (r.s + 1) + 20)) σ) :
    Runs cap st4d σ (6 * (C4 E r + 1)) (PS σ0 X Sx L rest i (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update f 45 (r.s + 1)) 46 (r.V * (r.s + 1))) 47 (3 * r.B + 2 * r.n + 6 * r.s + r.k + r.V * (r.s + 1))) 48 5) 49 10) 47 (3 * r.B + 2 * r.n + 6 * r.s + r.k + r.V * (r.s + 1) + 20)) 50 (r.V + 2)) 40 (Wk E r))) := by
  have hH14 := H.h14
  obtain ⟨h10, h11, h12, h13, h18, h33, z7, z40, z41, z42, z44, z45, z46, z47, z48, z49, z50, z53⟩ := H
  obtain ⟨hWdef, hP1, hP2, hb1, hb2, hb3, hb4, hb5, hb6⟩ := W4b E r
  have hWd' : (r.s + 1) * (Wk E r + 1) = Wdk E r + 1 := (Wdk_succ E r).symm
  obtain ⟨τ1, e1, p1⟩ := (ps_add cap 50 18 (by decide) (by decide) (by decide) h (0) (r.V)
    (by simp [Function.update_apply, h10, h11, h12, h13, h18, h33, z7, z40, z41, z42, z44, z45, z46, z47, z48, z49, z50, z53, hWdef] <;> ring) (by simp [Function.update_apply, h10, h11, h12, h13, h18, h33, z7, z40, z41, z42, z44, z45, z46, z47, z48, z49, z50, z53, hWdef] <;> ring)
    (by simp [Function.update_apply, h10, h11, h12, h13, h18, h33, z7, z40, z41, z42, z44, z45, z46, z47, z48, z49, z50, z53, hWdef]) (cap_add E r cap hcap _ _ (by omega) (by omega))).cost
    (cst_add E r _ (by omega))
  obtain ⟨τ2, e2, p2⟩ := (ps_inc cap 50 p1 (r.V) (by simp [Function.update_apply, h10, h11, h12, h13, h18, h33, z7, z40, z41, z42, z44, z45, z46, z47, z48, z49, z50, z53, hWdef] <;> ring)
    (cap_inc E r cap hcap _ (by omega))).cost (cst_c E r 3 (by norm_num))
  obtain ⟨τ3, e3, p3⟩ := (ps_inc cap 50 p2 (r.V + 1) (by simp [Function.update_apply, h10, h11, h12, h13, h18, h33, z7, z40, z41, z42, z44, z45, z46, z47, z48, z49, z50, z53, hWdef] <;> ring)
    (cap_inc E r cap hcap _ (by omega))).cost (cst_c E r 3 (by norm_num))
  obtain ⟨τ4, e4, p4⟩ := (ps_mul cap 50 53 47 40 (by decide) p3 (r.V + 2) (3 * r.B + 2 * r.n + 6 * r.s + r.k + r.V * (r.s + 1) + 20) (0)
    (by simp [Function.update_apply, h10, h11, h12, h13, h18, h33, z7, z40, z41, z42, z44, z45, z46, z47, z48, z49, z50, z53, hWdef] <;> ring) (by simp [Function.update_apply, h10, h11, h12, h13, h18, h33, z7, z40, z41, z42, z44, z45, z46, z47, z48, z49, z50, z53, hWdef] <;> ring)
    (by simp [Function.update_apply, h10, h11, h12, h13, h18, h33, z7, z40, z41, z42, z44, z45, z46, z47, z48, z49, z50, z53, hWdef] <;> ring) (by simp [Function.update_apply, h10, h11, h12, h13, h18, h33, z7, z40, z41, z42, z44, z45, z46, z47, z48, z49, z50, z53, hWdef])
    (by simp [Function.update_apply, h10, h11, h12, h13, h18, h33, z7, z40, z41, z42, z44, z45, z46, z47, z48, z49, z50, z53, hWdef]) (cap_mul1 E r cap hcap _ _ (hP1)) (cap_mul2 E r cap hcap _ (by omega))).cost
    (cst_mul E r _ _ (by omega) (hP1))
  obtain ⟨τ5, e5, p5⟩ := (ps_add cap 40 33 (by decide) (by decide) (by decide) p4 ((r.V + 2) * (3 * r.B + 2 * r.n + 6 * r.s + r.k + r.V * (r.s + 1) + 20)) (Cm E r)
    (by simp [Function.update_apply, h10, h11, h12, h13, h18, h33, z7, z40, z41, z42, z44, z45, z46, z47, z48, z49, z50, z53, hWdef] <;> ring) (by simp [Function.update_apply, h10, h11, h12, h13, h18, h33, z7, z40, z41, z42, z44, z45, z46, z47, z48, z49, z50, z53, hWdef] <;> ring)
    (by simp [Function.update_apply, h10, h11, h12, h13, h18, h33, z7, z40, z41, z42, z44, z45, z46, z47, z48, z49, z50, z53, hWdef]) (cap_add E r cap hcap _ _ (by omega) (by omega))).cost
    (cst_add E r _ (by omega))
  obtain ⟨τ6, e6, p6⟩ := (ps_add cap 40 14 (by decide) (by decide) (by decide) p5
    ((r.V + 2) * (3 * r.B + 2 * r.n + 6 * r.s + r.k + r.V * (r.s + 1) + 20) + Cm E r) r.G
    (by simp [Function.update_apply]) (by simp [Function.update_apply, hH14])
    (by simp [Function.update_apply, z7]) (cap_add E r cap hcap _ _ (by omega) (by omega))).cost
    (cst_add E r _ (by omega))
  refine ⟨τ6, WXExec.mono (WXExec.seq e1 <| WXExec.seq e2 <| WXExec.seq e3 <| WXExec.seq e4 <| WXExec.seq e5 e6)
    (by omega), ?_⟩
  refine p6.congr fun j => ?_
  simp only [Function.update_apply]
  split_ifs <;> (try simp_all) <;> ring

def st4e : WX :=
  .seq (addR (rX 40) (rX 42) (rX 7)) <|
  .seq (WMX.inc (rX 42)) <|
  .seq (mulR (rX 45) (rX 53) (rX 42) (rX 44) (rX 7)) <|
  .seq (addR (rX 44) (rX 41) (rX 7)) <|
  WMX.dec (rX 41)

theorem st4e_spec (cap : ℕ) (E : ExpandMachine) (r : TabReq) {σ0 : WSt} {X : Fin (NSx te qa + 1)}
    {Sx : List (Fin (NSx te qa + 1))} {L : List ℕ} {rest : List Bool} {i : ℕ} {g : Fin 64 → ℕ} {σ : WSt}
    (g40 : g 40 = Wk E r) (g45 : g 45 = r.s + 1) (z7 : g 7 = 0) (z41 : g 41 = 0) (z42 : g 42 = 0) (z44 : g 44 = 0)
    (z53 : g 53 = 0) (hcap : 4 * (Wdk E r + 2) ^ 2 ≤ cap) (h : PS σ0 X Sx L rest i g σ) :
    Runs cap st4e σ (5 * (C4 E r + 1))
      (PS σ0 X Sx L rest i (Function.update (Function.update (Function.update g 42 (Wk E r + 1)) 44 (Wdk E r + 1)) 41
        (Wdk E r))) := by
  obtain ⟨hWdef, hP1, hP2, hb1, hb2, hb3, hb4, hb5, hb6⟩ := W4b E r
  have hWd' : (r.s + 1) * (Wk E r + 1) = Wdk E r + 1 := (Wdk_succ E r).symm
  obtain ⟨τ1, e1, p1⟩ := (ps_add cap 42 40 (by decide) (by decide) (by decide) h (0) (Wk E r)
    (by simp [Function.update_apply, g40, g45, z7, z41, z42, z44, z53, hWd'] <;> ring) (by simp [Function.update_apply, g40, g45, z7, z41, z42, z44, z53, hWd'] <;> ring)
    (by simp [Function.update_apply, g40, g45, z7, z41, z42, z44, z53, hWd']) (cap_add E r cap hcap _ _ (by omega) (by omega))).cost
    (cst_add E r _ (by omega))
  obtain ⟨τ2, e2, p2⟩ := (ps_inc cap 42 p1 (Wk E r) (by simp [Function.update_apply, g40, g45, z7, z41, z42, z44, z53, hWd'] <;> ring)
    (cap_inc E r cap hcap _ (by omega))).cost (cst_c E r 3 (by norm_num))
  obtain ⟨τ3, e3, p3⟩ := (ps_mul cap 45 53 42 44 (by decide) p2 (r.s + 1) (Wk E r + 1) (0)
    (by simp [Function.update_apply, g40, g45, z7, z41, z42, z44, z53, hWd'] <;> ring) (by simp [Function.update_apply, g40, g45, z7, z41, z42, z44, z53, hWd'] <;> ring)
    (by simp [Function.update_apply, g40, g45, z7, z41, z42, z44, z53, hWd'] <;> ring) (by simp [Function.update_apply, g40, g45, z7, z41, z42, z44, z53, hWd'])
    (by simp [Function.update_apply, g40, g45, z7, z41, z42, z44, z53, hWd']) (cap_mul1 E r cap hcap _ _ (hP2)) (cap_mul2 E r cap hcap _ (by omega))).cost
    (cst_mul E r _ _ (by omega) (hP2))
  obtain ⟨τ4, e4, p4⟩ := (ps_add cap 41 44 (by decide) (by decide) (by decide) p3 (0) (Wdk E r + 1)
    (by simp [Function.update_apply, g40, g45, z7, z41, z42, z44, z53, hWd'] <;> ring) (by simp [Function.update_apply, g40, g45, z7, z41, z42, z44, z53, hWd'] <;> ring)
    (by simp [Function.update_apply, g40, g45, z7, z41, z42, z44, z53, hWd']) (cap_add E r cap hcap _ _ (by omega) (by omega))).cost
    (cst_add E r _ (by omega))
  obtain ⟨τ5, e5, p5⟩ := (ps_dec cap 41 p4 (Wdk E r + 1) (by simp [Function.update_apply, g40, g45, z7, z41, z42, z44, z53, hWd'] <;> ring)
    (cap_dec E r cap hcap _ (by omega))).cost (cst_c E r 1 (by norm_num))
  refine ⟨τ5, WXExec.mono (WXExec.seq e1 <| WXExec.seq e2 <| WXExec.seq e3 <| WXExec.seq e4 <| e5) (by omega), ?_⟩
  refine p5.congr fun j => ?_
  simp only [Function.update_apply]
  split_ifs <;> (try simp_all) <;> ring

def st4 : WX := .seq st4a (.seq st4b (.seq st4c (.seq st4d st4e)))

theorem st4_spec (cap : ℕ) (E : ExpandMachine) (r : TabReq) {σ0 : WSt} {X : Fin (NSx te qa + 1)}
    {Sx : List (Fin (NSx te qa + 1))} {L : List ℕ} {rest : List Bool} {i : ℕ} {f : Fin 64 → ℕ} {σ : WSt}
    (H : WeakWorker E r f) (hcap : 4 * (Wdk E r + 2) ^ 2 ≤ cap) (h : PS σ0 X Sx L rest i f σ) :
    Runs cap st4 σ (36 * (C4 E r + 1) + 4) (fun τ => ∃ g, PS σ0 X Sx L rest i g τ ∧ g 40 = Wk E r ∧
      g 41 = Wdk E r ∧ g 42 = Wk E r + 1 ∧ g 44 = Wdk E r + 1 ∧ g 45 = r.s + 1 ∧
      ∀ j : Fin 64, j.val ∉ [40, 41, 42, 44, 45, 46, 47, 48, 49, 50] → g j = f j) := by
  have e := Runs.seq (st4a_spec cap E r H hcap h) fun τ1 h1 => Runs.seq (st4b_spec cap E r H hcap h1)
    fun τ2 h2 => Runs.seq (st4c_spec cap E r H hcap h2) fun τ3 h3 => Runs.seq (st4d_spec cap E r H hcap h3)
    fun τ4 h4 => st4e_spec cap E r (by simp) (by simp) (by simp [H.z7]) (by simp [H.z41]) (by simp [H.z42])
      (by simp [H.z44]) (by simp [H.z53]) hcap h4
  refine (e.cost (by omega)).post fun τ hτ => ⟨_, hτ, by simp, by simp, by simp, by simp, by simp, fun j hj => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
  simp only [Function.update_apply]
  split_ifs <;> simp_all

end NearCubicGates.Close.Expand.PolyTab
