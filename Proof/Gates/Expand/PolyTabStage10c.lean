import Proof.Gates.Expand.PolyTabStage10b

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

def st8preA : WX :=
  .seq (mulR (rX 14) (rX 16) (rX 15) (rX 25) (rX 7)) <| .seq (WMX.inc (rX 25)) <| .seq (WMX.inc (rX 25)) <|
  .seq (WMX.inc (rX 25)) <| .seq (WMX.inc (rX 25)) <| .seq (WMX.inc (rX 25)) (WMX.inc (rX 25))

def st8preB : WX :=
  .seq (addR (rX 2) (rX 43) (rX 7)) <| .seq (addR (rX 19) (rX 43) (rX 7)) <| .seq (WMX.inc (rX 43)) <|
  .seq (addR (rX 18) (rX 26) (rX 7)) <| .seq (addR (rX 11) (rX 27) (rX 7)) <| .seq (addR (rX 12) (rX 27) (rX 7)) <|
  .seq (WMX.inc (rX 27)) (WMX.inc (rX 27))

def st8pre : WX := .seq st8preA st8preB

/-- The registers after the prelude. -/
def f8 (r : TabReq) (f : Fin 64 → ℕ) : Fin 64 → ℕ := fun j =>
  if j = 25 then pk r + 1 else if j = 43 then pV r + 1 else if j = 26 then r.V else if j = 27 then r.k + r.s + 2
  else f j

def c8 (r : TabReq) : ℕ :=
  r.G * (18 * (2 * r.n + 3) + 3 + 8) + 7 * r.G + 3 + 1 + 3 * 7 + 6 * 1 + 18 * (pN r + 1 + 2 ^ r.k + r.V + r.k +
    r.s + 10) + 100

section Pre
variable {σ0 : WState (NSx te qa) NRk} {X : Fin (NSx te qa + 1)} {Sx : List (Fin (NSx te qa + 1))} {L : List ℕ}
  {rest : List Bool} {i : ℕ}

theorem st8preA_spec (cap : ℕ) (r : TabReq) {f : Fin 64 → ℕ} {σ : WSt} (h : PS σ0 X Sx L rest i f σ)
    (h14 : f 14 = r.G) (h15 : f 15 = 2 * r.n + 3) (h16 : f 16 = 0) (h7 : f 7 = 0) (z25 : f 25 = 0)
    (hcap : pk r + 2 * r.G + 10 ≤ cap) :
    Runs cap st8preA σ (r.G * (18 * (2 * r.n + 3) + 3 + 8) + 7 * r.G + 3 + 1 + (3 + 1 + (3 + 1 + (3 + 1 + (3 + 1 +
      (3 + 1 + 3))))))
      (PS σ0 X Sx L rest i (Function.update f 25 (pk r + 1))) := by
  have hpk : pk r = 5 + r.G * (2 * r.n + 3) := rfl
  obtain ⟨τ1, e1, p1⟩ := ps_mul cap 14 16 15 25 (by decide) h r.G (2 * r.n + 3) 0 h14 h15 z25 h16 h7 (by omega) (by omega)
  obtain ⟨τ2, e2, p2⟩ := ps_inc cap 25 p1 (0 + r.G * (2 * r.n + 3)) (by simp) (by omega)
  obtain ⟨τ3, e3, p3⟩ := ps_inc cap 25 p2 (0 + r.G * (2 * r.n + 3) + 1) (by simp) (by omega)
  obtain ⟨τ4, e4, p4⟩ := ps_inc cap 25 p3 (0 + r.G * (2 * r.n + 3) + 1 + 1) (by simp) (by omega)
  obtain ⟨τ5, e5, p5⟩ := ps_inc cap 25 p4 (0 + r.G * (2 * r.n + 3) + 1 + 1 + 1) (by simp) (by omega)
  obtain ⟨τ6, e6, p6⟩ := ps_inc cap 25 p5 (0 + r.G * (2 * r.n + 3) + 1 + 1 + 1 + 1) (by simp) (by omega)
  obtain ⟨τ7, e7, p7⟩ := ps_inc cap 25 p6 (0 + r.G * (2 * r.n + 3) + 1 + 1 + 1 + 1 + 1) (by simp) (by omega)
  refine ⟨τ7, WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4 (WXExec.seq e5 (WXExec.seq e6 e7))))),
    p7.congr fun j => ?_⟩
  by_cases hj : j = 25
  · subst hj; simp [hpk]; try ring
  · simp [Function.update_of_ne hj]

theorem st8preB_spec (cap : ℕ) (r : TabReq) {f : Fin 64 → ℕ} {σ : WSt} (h : PS σ0 X Sx L rest i f σ)
    (h2 : f 2 = pN r + 1) (h19 : f 19 = 2 ^ r.k) (h18 : f 18 = r.V) (h11 : f 11 = r.k) (h12 : f 12 = r.s)
    (h7 : f 7 = 0) (z43 : f 43 = 0) (z26 : f 26 = 0) (z27 : f 27 = 0)
    (hcap : pN r + 2 ^ r.k + r.V + r.k + r.s + 10 ≤ cap) :
    Runs cap st8preB σ (18 * (pN r + 1) + 3 + 1 + (18 * 2 ^ r.k + 3 + 1 + (3 + 1 + (18 * r.V + 3 + 1 +
      (18 * r.k + 3 + 1 + (18 * r.s + 3 + 1 + (3 + 1 + 3)))))))
      (PS σ0 X Sx L rest i (Function.update (Function.update (Function.update f 43 (pV r + 1)) 26 r.V) 27
        (r.k + r.s + 2))) := by
  have hpV : pV r = pN r + 2 ^ r.k + 1 := rfl
  obtain ⟨τ1, e1, p1⟩ := ps_add cap 43 2 (by decide) (by decide) (by decide) h 0 (pN r + 1) z43 h2 h7 (by omega)
  obtain ⟨τ2, e2, p2⟩ := ps_add cap 43 19 (by decide) (by decide) (by decide) p1 (0 + (pN r + 1)) (2 ^ r.k) (by simp)
    (by simp [h19]) (by simp [h7]) (by omega)
  obtain ⟨τ3, e3, p3⟩ := ps_inc cap 43 p2 (0 + (pN r + 1) + 2 ^ r.k) (by simp) (by omega)
  obtain ⟨τ4, e4, p4⟩ := ps_add cap 26 18 (by decide) (by decide) (by decide) p3 0 r.V (by simp [z26]) (by simp [h18])
    (by simp [h7]) (by omega)
  obtain ⟨τ5, e5, p5⟩ := ps_add cap 27 11 (by decide) (by decide) (by decide) p4 0 r.k (by simp [z27]) (by simp [h11])
    (by simp [h7]) (by omega)
  obtain ⟨τ6, e6, p6⟩ := ps_add cap 27 12 (by decide) (by decide) (by decide) p5 (0 + r.k) r.s (by simp) (by simp [h12])
    (by simp [h7]) (by omega)
  obtain ⟨τ7, e7, p7⟩ := ps_inc cap 27 p6 (0 + r.k + r.s) (by simp) (by omega)
  obtain ⟨τ8, e8, p8⟩ := ps_inc cap 27 p7 (0 + r.k + r.s + 1) (by simp) (by omega)
  refine ⟨τ8, WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4 (WXExec.seq e5 (WXExec.seq e6
    (WXExec.seq e7 e8)))))), p8.congr fun j => ?_⟩
  by_cases j27 : j = 27
  · subst j27; simp; try ring
  · by_cases j26 : j = 26
    · subst j26; simp
    · by_cases j43 : j = 43
      · subst j43; simp [hpV]; try ring
      · simp [Function.update_of_ne j27, Function.update_of_ne j26, Function.update_of_ne j43]

theorem st8pre_spec (cap : ℕ) (r : TabReq) {f : Fin 64 → ℕ} {σ : WSt} (h : PS σ0 X Sx L rest i f σ)
    (h14 : f 14 = r.G) (h15 : f 15 = 2 * r.n + 3) (h16 : f 16 = 0) (h7 : f 7 = 0) (z25 : f 25 = 0)
    (h2 : f 2 = pN r + 1) (h19 : f 19 = 2 ^ r.k) (h18 : f 18 = r.V) (h11 : f 11 = r.k) (h12 : f 12 = r.s)
    (z43 : f 43 = 0) (z26 : f 26 = 0) (z27 : f 27 = 0)
    (hcap : pk r + 2 * r.G + pN r + 2 ^ r.k + r.V + r.k + r.s + 20 ≤ cap) :
    Runs cap st8pre σ (c8 r) (PS σ0 X Sx L rest i (f8 r f)) := by
  obtain ⟨τ1, e1, p1⟩ := st8preA_spec cap r h h14 h15 h16 h7 z25 (by omega)
  obtain ⟨τ2, e2, p2⟩ := st8preB_spec cap r p1 (by simp [h2]) (by simp [h19]) (by simp [h18]) (by simp [h11])
    (by simp [h12]) (by simp [h7]) (by simp [z43]) (by simp [z26]) (by simp [z27]) (by omega)
  refine ⟨τ2, (WXExec.seq e1 e2).mono (by unfold c8; omega), p2.congr fun j => ?_⟩
  simp only [f8, Function.update_apply]
  split_ifs <;> simp_all

end Pre

end NearCubicGates.Close.Expand.PolyTab
