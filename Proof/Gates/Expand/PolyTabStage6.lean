import Proof.Gates.Expand.PolyTabStage5

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

theorem preN_length' (r : TabReq) :
    r.G * (2 * r.n + 3) + r.k + r.s + 2 ^ r.k + 2 * r.V + 9 = (preN r).length := by
  rw [preN_length]; unfold pV pN ps pk; ring

def st6a1 : WX :=
  .seq (addR (rX 10) (rX 15) (rX 7)) <|
  .seq (addR (rX 10) (rX 15) (rX 7)) <|
  .seq (WMX.inc (rX 15)) <|
  .seq (WMX.inc (rX 15)) <|
  .seq (WMX.inc (rX 15)) <|
  mulR (rX 14) (rX 16) (rX 15) (rX 9) (rX 7)

def st6a2 : WX :=
  .seq (addR (rX 11) (rX 9) (rX 7)) <|
  .seq (addR (rX 12) (rX 9) (rX 7)) <|
  .seq (addR (rX 19) (rX 9) (rX 7)) <|
  .seq (addR (rX 18) (rX 9) (rX 7)) <|
  .seq (addR (rX 18) (rX 9) (rX 7)) <|
  .seq (WMX.inc (rX 9)) <|
  .seq (WMX.inc (rX 9)) <|
  .seq (WMX.inc (rX 9)) <|
  .seq (WMX.inc (rX 9)) <|
  .seq (WMX.inc (rX 9)) <|
  .seq (WMX.inc (rX 9)) <|
  .seq (WMX.inc (rX 9)) <|
  .seq (WMX.inc (rX 9)) <|
  WMX.inc (rX 9)

def st6a : WX := .seq st6a1 st6a2

theorem st6a1_spec (cap : ℕ) (r : TabReq) {σ0 : WSt} {X : Fin (NSx te qa + 1)}
    {Sx : List (Fin (NSx te qa + 1))} {L : List ℕ} {rest : List Bool} {i : ℕ} {f : Fin 64 → ℕ} {σ : WSt}
    (H : Hdr cap r) (hcap : 20 * (Mh r + 1) ^ 2 ≤ cap) (h10 : f 10 = r.n) (h11 : f 11 = r.k) (h12 : f 12 = r.s)
    (h14 : f 14 = r.G) (h18 : f 18 = r.V) (h19 : f 19 = 2 ^ r.k) (z15 : f 15 = 0) (z16 : f 16 = 0) (z9 : f 9 = 0)
    (z7 : f 7 = 0) (h : PS σ0 X Sx L rest i f σ) :
    Runs cap st6a1 σ (6 * (Cst r + 1)) (PS σ0 X Sx L rest i
      (Function.update (Function.update f 15 (2 * r.n + 3)) 9 (r.G * (2 * r.n + 3)))) := by
  have hb1 := H.bn; have hb2 := H.bk; have hb3 := H.bs; have hb4 := H.bG; have hb5 := H.bV; have hb6 := H.b2
  have hsq := H.sq; have hcst := H.cst; have hg2 := H.g2
  have hk2 := Nat.two_pow_pos r.k
  obtain ⟨τ1, e1, p1⟩ := (ps_add cap 15 10 (by decide) (by decide) (by decide) h (0) (r.n)
    (by simp [Function.update_apply, h10, h11, h12, h14, h18, h19, z15, z16, z9, z7] <;> ring) (by simp [Function.update_apply, h10, h11, h12, h14, h18, h19, z15, z16, z9, z7] <;> ring)
    (by simp [Function.update_apply, h10, h11, h12, h14, h18, h19, z15, z16, z9, z7]) (by omega)).cost (c' := Cst r) (by omega)
  obtain ⟨τ2, e2, p2⟩ := (ps_add cap 15 10 (by decide) (by decide) (by decide) p1 (r.n) (r.n)
    (by simp [Function.update_apply, h10, h11, h12, h14, h18, h19, z15, z16, z9, z7] <;> ring) (by simp [Function.update_apply, h10, h11, h12, h14, h18, h19, z15, z16, z9, z7] <;> ring)
    (by simp [Function.update_apply, h10, h11, h12, h14, h18, h19, z15, z16, z9, z7]) (by omega)).cost (c' := Cst r) (by omega)
  obtain ⟨τ3, e3, p3⟩ := (ps_inc cap 15 p2 (2 * r.n) (by simp [Function.update_apply, h10, h11, h12, h14, h18, h19, z15, z16, z9, z7] <;> ring)
    (by omega)).cost (c' := Cst r) (by omega)
  obtain ⟨τ4, e4, p4⟩ := (ps_inc cap 15 p3 (2 * r.n + 1) (by simp [Function.update_apply, h10, h11, h12, h14, h18, h19, z15, z16, z9, z7] <;> ring)
    (by omega)).cost (c' := Cst r) (by omega)
  obtain ⟨τ5, e5, p5⟩ := (ps_inc cap 15 p4 (2 * r.n + 2) (by simp [Function.update_apply, h10, h11, h12, h14, h18, h19, z15, z16, z9, z7] <;> ring)
    (by omega)).cost (c' := Cst r) (by omega)
  obtain ⟨τ6, e6, p6⟩ := (ps_mul cap 14 16 15 9 (by decide) p5 (r.G) (2 * r.n + 3) (0)
    (by simp [Function.update_apply, h10, h11, h12, h14, h18, h19, z15, z16, z9, z7] <;> ring) (by simp [Function.update_apply, h10, h11, h12, h14, h18, h19, z15, z16, z9, z7] <;> ring)
    (by simp [Function.update_apply, h10, h11, h12, h14, h18, h19, z15, z16, z9, z7] <;> ring) (by simp [Function.update_apply, h10, h11, h12, h14, h18, h19, z15, z16, z9, z7])
    (by simp [Function.update_apply, h10, h11, h12, h14, h18, h19, z15, z16, z9, z7]) (by nlinarith) (by omega)).cost (c' := Cst r) (by nlinarith)
  refine ⟨τ6, WXExec.mono (WXExec.seq e1 <| WXExec.seq e2 <| WXExec.seq e3 <| WXExec.seq e4 <| WXExec.seq e5 <| e6) (by omega), ?_⟩
  refine p6.congr fun j => ?_
  by_cases j9 : j = 9
  · subst j9; simp
  · by_cases j15 : j = 15
    · subst j15; simp
    · simp [Function.update_apply, j9, j15]

theorem st6a2_spec (cap : ℕ) (r : TabReq) {σ0 : WSt} {X : Fin (NSx te qa + 1)}
    {Sx : List (Fin (NSx te qa + 1))} {L : List ℕ} {rest : List Bool} {i : ℕ} {g : Fin 64 → ℕ} {σ : WSt}
    (H : Hdr cap r) (hcap : 20 * (Mh r + 1) ^ 2 ≤ cap) (g11 : g 11 = r.k) (g12 : g 12 = r.s)
    (g14 : g 14 = r.G) (g18 : g 18 = r.V) (g19 : g 19 = 2 ^ r.k) (g9 : g 9 = r.G * (2 * r.n + 3)) (g15 : g 15 = 2 * r.n + 3)
    (z7 : g 7 = 0) (h : PS σ0 X Sx L rest i g σ) :
    Runs cap st6a2 σ (14 * (Cst r + 1)) (PS σ0 X Sx L rest i (Function.update g 9 (preN r).length)) := by
  have hb1 := H.bn; have hb2 := H.bk; have hb3 := H.bs; have hb4 := H.bG; have hb5 := H.bV; have hb6 := H.b2
  have hsq := H.sq; have hcst := H.cst; have hg2 := H.g2
  have hk2 := Nat.two_pow_pos r.k
  obtain ⟨τ1, e1, p1⟩ := (ps_add cap 9 11 (by decide) (by decide) (by decide) h (r.G * (2 * r.n + 3)) (r.k)
    (by simp [Function.update_apply, g11, g12, g14, g18, g19, g9, g15, z7] <;> ring) (by simp [Function.update_apply, g11, g12, g14, g18, g19, g9, g15, z7] <;> ring)
    (by simp [Function.update_apply, g11, g12, g14, g18, g19, g9, g15, z7]) (by omega)).cost (c' := Cst r) (by omega)
  obtain ⟨τ2, e2, p2⟩ := (ps_add cap 9 12 (by decide) (by decide) (by decide) p1 (r.G * (2 * r.n + 3) + r.k) (r.s)
    (by simp [Function.update_apply, g11, g12, g14, g18, g19, g9, g15, z7] <;> ring) (by simp [Function.update_apply, g11, g12, g14, g18, g19, g9, g15, z7] <;> ring)
    (by simp [Function.update_apply, g11, g12, g14, g18, g19, g9, g15, z7]) (by omega)).cost (c' := Cst r) (by omega)
  obtain ⟨τ3, e3, p3⟩ := (ps_add cap 9 19 (by decide) (by decide) (by decide) p2 (r.G * (2 * r.n + 3) + r.k + r.s) (2 ^ r.k)
    (by simp [Function.update_apply, g11, g12, g14, g18, g19, g9, g15, z7] <;> ring) (by simp [Function.update_apply, g11, g12, g14, g18, g19, g9, g15, z7] <;> ring)
    (by simp [Function.update_apply, g11, g12, g14, g18, g19, g9, g15, z7]) (by omega)).cost (c' := Cst r) (by omega)
  obtain ⟨τ4, e4, p4⟩ := (ps_add cap 9 18 (by decide) (by decide) (by decide) p3 (r.G * (2 * r.n + 3) + r.k + r.s + 2 ^ r.k) (r.V)
    (by simp [Function.update_apply, g11, g12, g14, g18, g19, g9, g15, z7] <;> ring) (by simp [Function.update_apply, g11, g12, g14, g18, g19, g9, g15, z7] <;> ring)
    (by simp [Function.update_apply, g11, g12, g14, g18, g19, g9, g15, z7]) (by omega)).cost (c' := Cst r) (by omega)
  obtain ⟨τ5, e5, p5⟩ := (ps_add cap 9 18 (by decide) (by decide) (by decide) p4 (r.G * (2 * r.n + 3) + r.k + r.s + 2 ^ r.k + r.V) (r.V)
    (by simp [Function.update_apply, g11, g12, g14, g18, g19, g9, g15, z7] <;> ring) (by simp [Function.update_apply, g11, g12, g14, g18, g19, g9, g15, z7] <;> ring)
    (by simp [Function.update_apply, g11, g12, g14, g18, g19, g9, g15, z7]) (by omega)).cost (c' := Cst r) (by omega)
  obtain ⟨τ6, e6, p6⟩ := (ps_inc cap 9 p5 (r.G * (2 * r.n + 3) + r.k + r.s + 2 ^ r.k + 2 * r.V) (by simp [Function.update_apply, g11, g12, g14, g18, g19, g9, g15, z7] <;> ring)
    (by omega)).cost (c' := Cst r) (by omega)
  obtain ⟨τ7, e7, p7⟩ := (ps_inc cap 9 p6 (r.G * (2 * r.n + 3) + r.k + r.s + 2 ^ r.k + 2 * r.V + 1) (by simp [Function.update_apply, g11, g12, g14, g18, g19, g9, g15, z7] <;> ring)
    (by omega)).cost (c' := Cst r) (by omega)
  obtain ⟨τ8, e8, p8⟩ := (ps_inc cap 9 p7 (r.G * (2 * r.n + 3) + r.k + r.s + 2 ^ r.k + 2 * r.V + 2) (by simp [Function.update_apply, g11, g12, g14, g18, g19, g9, g15, z7] <;> ring)
    (by omega)).cost (c' := Cst r) (by omega)
  obtain ⟨τ9, e9, p9⟩ := (ps_inc cap 9 p8 (r.G * (2 * r.n + 3) + r.k + r.s + 2 ^ r.k + 2 * r.V + 3) (by simp [Function.update_apply, g11, g12, g14, g18, g19, g9, g15, z7] <;> ring)
    (by omega)).cost (c' := Cst r) (by omega)
  obtain ⟨τ10, e10, p10⟩ := (ps_inc cap 9 p9 (r.G * (2 * r.n + 3) + r.k + r.s + 2 ^ r.k + 2 * r.V + 4) (by simp [Function.update_apply, g11, g12, g14, g18, g19, g9, g15, z7] <;> ring)
    (by omega)).cost (c' := Cst r) (by omega)
  obtain ⟨τ11, e11, p11⟩ := (ps_inc cap 9 p10 (r.G * (2 * r.n + 3) + r.k + r.s + 2 ^ r.k + 2 * r.V + 5) (by simp [Function.update_apply, g11, g12, g14, g18, g19, g9, g15, z7] <;> ring)
    (by omega)).cost (c' := Cst r) (by omega)
  obtain ⟨τ12, e12, p12⟩ := (ps_inc cap 9 p11 (r.G * (2 * r.n + 3) + r.k + r.s + 2 ^ r.k + 2 * r.V + 6) (by simp [Function.update_apply, g11, g12, g14, g18, g19, g9, g15, z7] <;> ring)
    (by omega)).cost (c' := Cst r) (by omega)
  obtain ⟨τ13, e13, p13⟩ := (ps_inc cap 9 p12 (r.G * (2 * r.n + 3) + r.k + r.s + 2 ^ r.k + 2 * r.V + 7) (by simp [Function.update_apply, g11, g12, g14, g18, g19, g9, g15, z7] <;> ring)
    (by omega)).cost (c' := Cst r) (by omega)
  obtain ⟨τ14, e14, p14⟩ := (ps_inc cap 9 p13 (r.G * (2 * r.n + 3) + r.k + r.s + 2 ^ r.k + 2 * r.V + 8) (by simp [Function.update_apply, g11, g12, g14, g18, g19, g9, g15, z7] <;> ring)
    (by omega)).cost (c' := Cst r) (by omega)
  refine ⟨τ14, WXExec.mono (WXExec.seq e1 <| WXExec.seq e2 <| WXExec.seq e3 <| WXExec.seq e4 <| WXExec.seq e5 <| WXExec.seq e6 <| WXExec.seq e7 <| WXExec.seq e8 <| WXExec.seq e9 <| WXExec.seq e10 <| WXExec.seq e11 <| WXExec.seq e12 <| WXExec.seq e13 <| e14) (by omega), ?_⟩
  refine p14.congr fun j => ?_
  have := preN_length' r
  by_cases j9 : j = 9
  · subst j9; simp; omega
  · simp [Function.update_apply, j9]

theorem st6a_spec (cap : ℕ) (r : TabReq) {σ0 : WSt} {X : Fin (NSx te qa + 1)}
    {Sx : List (Fin (NSx te qa + 1))} {L : List ℕ} {rest : List Bool} {i : ℕ} {f : Fin 64 → ℕ} {σ : WSt}
    (H : Hdr cap r) (hcap : 20 * (Mh r + 1) ^ 2 ≤ cap) (h10 : f 10 = r.n) (h11 : f 11 = r.k) (h12 : f 12 = r.s)
    (h14 : f 14 = r.G) (h18 : f 18 = r.V) (h19 : f 19 = 2 ^ r.k) (z15 : f 15 = 0) (z16 : f 16 = 0) (z9 : f 9 = 0)
    (z7 : f 7 = 0) (h : PS σ0 X Sx L rest i f σ) :
    Runs cap st6a σ (20 * (Cst r + 1) + 1) (PS σ0 X Sx L rest i
      (Function.update (Function.update f 15 (2 * r.n + 3)) 9 (preN r).length)) := by
  refine (Runs.seq (st6a1_spec cap r H hcap h10 h11 h12 h14 h18 h19 z15 z16 z9 z7 h) fun τ hτ =>
    (st6a2_spec cap r H hcap (by simp [h11]) (by simp [h12]) (by simp [h14]) (by simp [h18]) (by simp [h19])
      (by simp) (by simp) (by simp [z7]) hτ).post fun ρ hρ => hρ.congr fun j => ?_).cost (by omega)
  by_cases j9 : j = 9
  · subst j9; simp
  · simp [Function.update_apply, j9]

end NearCubicGates.Close.Expand.PolyTab
