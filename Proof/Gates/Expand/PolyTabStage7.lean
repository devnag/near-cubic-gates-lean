import Proof.Gates.Expand.PolyTabStage6b

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

namespace NearCubicGates.Close.Expand.PolyTab

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicGates.Close.CounterMachine NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.TabMachine
open StablePartition.Workspace (overlay)

variable {te qa : ℕ}

local notation "WX" => WMX (NSx te qa) NRk
local notation "WSt" => WState (NSx te qa) NRk

def st7a : WX :=
  .seq (mulR (rX 14) (rX 16) (rX 15) (rX 2) (rX 7)) <|
  .seq (addR (rX 11) (rX 2) (rX 7)) <|
  .seq (addR (rX 12) (rX 2) (rX 7)) <|
  .seq (WMX.inc (rX 2)) <|
  .seq (WMX.inc (rX 2)) <|
  .seq (WMX.inc (rX 2)) <|
  .seq (WMX.inc (rX 2)) <|
  .seq (WMX.inc (rX 2)) <|
  .seq (WMX.inc (rX 2)) <|
  .seq (WMX.inc (rX 2)) <|
  WMX.inc (rX 2)

theorem st7a_spec (cap : ℕ) (r : TabReq) {σ0 : WSt} {X : Fin (NSx te qa + 1)}
    {Sx : List (Fin (NSx te qa + 1))} {L : List ℕ} {rest : List Bool} {i : ℕ} {f : Fin 64 → ℕ} {σ : WSt}
    (H : Hdr cap r) (hcap : 20 * (Mh r + 1) ^ 2 ≤ cap) (g11 : f 11 = r.k) (g12 : f 12 = r.s)
    (g14 : f 14 = r.G) (g15 : f 15 = 2 * r.n + 3) (z16 : f 16 = 0) (z2 : f 2 = 0) (z7 : f 7 = 0)
    (h : PS σ0 X Sx L rest i f σ) :
    Runs cap st7a σ (11 * (Cst r + 1)) (PS σ0 X Sx L rest i (Function.update f 2 (pN r + 1))) := by
  have hb1 := H.bn; have hb2 := H.bk; have hb3 := H.bs; have hb4 := H.bG; have hb5 := H.bV; have hb6 := H.b2
  have hsq := H.sq; have hcst := H.cst; have hg2 := H.g2
  have hk2 := Nat.two_pow_pos r.k
  obtain ⟨τ1, e1, p1⟩ := (ps_mul cap 14 16 15 2 (by decide) h (r.G) (2 * r.n + 3) (0)
    (by simp [Function.update_apply, g11, g12, g14, g15, z16, z2, z7] <;> ring) (by simp [Function.update_apply, g11, g12, g14, g15, z16, z2, z7] <;> ring)
    (by simp [Function.update_apply, g11, g12, g14, g15, z16, z2, z7] <;> ring) (by simp [Function.update_apply, g11, g12, g14, g15, z16, z2, z7])
    (by simp [Function.update_apply, g11, g12, g14, g15, z16, z2, z7]) (by nlinarith) (by omega)).cost (c' := Cst r) (by nlinarith)
  obtain ⟨τ2, e2, p2⟩ := (ps_add cap 2 11 (by decide) (by decide) (by decide) p1 (r.G * (2 * r.n + 3)) (r.k)
    (by simp [Function.update_apply, g11, g12, g14, g15, z16, z2, z7] <;> ring) (by simp [Function.update_apply, g11, g12, g14, g15, z16, z2, z7] <;> ring)
    (by simp [Function.update_apply, g11, g12, g14, g15, z16, z2, z7]) (by omega)).cost (c' := Cst r) (by omega)
  obtain ⟨τ3, e3, p3⟩ := (ps_add cap 2 12 (by decide) (by decide) (by decide) p2 (r.G * (2 * r.n + 3) + r.k) (r.s)
    (by simp [Function.update_apply, g11, g12, g14, g15, z16, z2, z7] <;> ring) (by simp [Function.update_apply, g11, g12, g14, g15, z16, z2, z7] <;> ring)
    (by simp [Function.update_apply, g11, g12, g14, g15, z16, z2, z7]) (by omega)).cost (c' := Cst r) (by omega)
  obtain ⟨τ4, e4, p4⟩ := (ps_inc cap 2 p3 (r.G * (2 * r.n + 3) + r.k + r.s) (by simp [Function.update_apply, g11, g12, g14, g15, z16, z2, z7] <;> ring)
    (by omega)).cost (c' := Cst r) (by omega)
  obtain ⟨τ5, e5, p5⟩ := (ps_inc cap 2 p4 (r.G * (2 * r.n + 3) + r.k + r.s + 1) (by simp [Function.update_apply, g11, g12, g14, g15, z16, z2, z7] <;> ring)
    (by omega)).cost (c' := Cst r) (by omega)
  obtain ⟨τ6, e6, p6⟩ := (ps_inc cap 2 p5 (r.G * (2 * r.n + 3) + r.k + r.s + 2) (by simp [Function.update_apply, g11, g12, g14, g15, z16, z2, z7] <;> ring)
    (by omega)).cost (c' := Cst r) (by omega)
  obtain ⟨τ7, e7, p7⟩ := (ps_inc cap 2 p6 (r.G * (2 * r.n + 3) + r.k + r.s + 3) (by simp [Function.update_apply, g11, g12, g14, g15, z16, z2, z7] <;> ring)
    (by omega)).cost (c' := Cst r) (by omega)
  obtain ⟨τ8, e8, p8⟩ := (ps_inc cap 2 p7 (r.G * (2 * r.n + 3) + r.k + r.s + 4) (by simp [Function.update_apply, g11, g12, g14, g15, z16, z2, z7] <;> ring)
    (by omega)).cost (c' := Cst r) (by omega)
  obtain ⟨τ9, e9, p9⟩ := (ps_inc cap 2 p8 (r.G * (2 * r.n + 3) + r.k + r.s + 5) (by simp [Function.update_apply, g11, g12, g14, g15, z16, z2, z7] <;> ring)
    (by omega)).cost (c' := Cst r) (by omega)
  obtain ⟨τ10, e10, p10⟩ := (ps_inc cap 2 p9 (r.G * (2 * r.n + 3) + r.k + r.s + 6) (by simp [Function.update_apply, g11, g12, g14, g15, z16, z2, z7] <;> ring)
    (by omega)).cost (c' := Cst r) (by omega)
  obtain ⟨τ11, e11, p11⟩ := (ps_inc cap 2 p10 (r.G * (2 * r.n + 3) + r.k + r.s + 7) (by simp [Function.update_apply, g11, g12, g14, g15, z16, z2, z7] <;> ring)
    (by omega)).cost (c' := Cst r) (by omega)
  refine ⟨τ11, WXExec.mono (WXExec.seq e1 <| WXExec.seq e2 <| WXExec.seq e3 <| WXExec.seq e4 <| WXExec.seq e5 <| WXExec.seq e6 <| WXExec.seq e7 <| WXExec.seq e8 <| WXExec.seq e9 <| WXExec.seq e10 <| e11) (by omega), ?_⟩
  refine p11.congr fun j => ?_
  have e : pN r + 1 = r.G * (2 * r.n + 3) + r.k + r.s + 8 := by unfold pN ps pk; ring
  by_cases j2 : j = 2
  · subst j2; simp; omega
  · simp [Function.update_apply, j2]

end NearCubicGates.Close.Expand.PolyTab
