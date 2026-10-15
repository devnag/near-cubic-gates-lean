import Proof.Gates.Expand.PolyTabData
import Proof.Gates.CounterMachine.UnpackNats
import Proof.Gates.Codec.Unframe
import Proof.Gates.WordPrograms.RegArith

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.Expand.PolyTab

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat (enc stp enc_length readNatM readNatM_spec)
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.CounterMachine

variable {te qa : ℕ}

local notation "WX" => WMX (NSx te qa) NRk
local notation "WSt" => WState (NSx te qa) NRk

theorem se_hv (σ : WSt) (X : Fin (NSx te qa + 1)) (a : ℕ) (v : Fin NRk) (b : ℕ) :
    SameExcept σ ((σ.seth X a).setv v b) [X] [v] := by
  refine ⟨fun x hx => ?_, fun q hq => ?_, rfl⟩
  · simp only [List.mem_singleton] at hx; simp [Function.update_of_ne hx]
  · simp only [List.mem_singleton] at hq; simp [Function.update_of_ne hq]

theorem se_vh (σ : WSt) (X : Fin (NSx te qa + 1)) (a : ℕ) (v : Fin NRk) (b : ℕ) :
    SameExcept σ ((σ.setv v b).seth X a) [X] [v] := by
  refine ⟨fun x hx => ?_, fun q hq => ?_, rfl⟩
  · simp only [List.mem_singleton] at hx; simp [Function.update_of_ne hx]
  · simp only [List.mem_singleton] at hq; simp [Function.update_of_ne hq]

/-! ## Field steps on the input stream -/

/-- Read the next field of `X` into `v` (`rX 3–6` scratch). -/
def rdF (X : Fin (NSx te qa + 1)) (v : Fin NRk) : WX := .wm (readNatM true X (rX 3) (rX 4) v (rX 5) (rX 6))
/-- Skip `K` fields of `X` (`K` cleared). -/
def skF (X : Fin (NSx te qa + 1)) (K : Fin NRk) : WX := .wm (Codec.listLoop K (Codec.skipNat true X (rX 3) (rX 4)))

def rdCost (x : ℕ) : ℕ := (natBitLength x + 2) * (40 * 2 ^ natBitLength x + 40)
def skCost (xs : List ℕ) : ℕ := (xs.map fun x => 20 * natBitLength x + 20 + 4).sum + 1

theorem rdF_spec (cap : ℕ) (X : Fin (NSx te qa + 1)) (v : Fin NRk) (hv : ∀ j : Fin 64, j.val ∈ [3, 4, 5, 6] → rX j ≠ v)
    (L : List ℕ) (rest : List Bool) (σ : WSt) (i : ℕ) (hσ : NatAt X L rest σ i) (hi : i < L.length)
    (h3 : σ.val (rX 3) = 0) (h4 : σ.val (rX 4) = 0) (h5 : σ.val (rX 5) = 0) (h6 : σ.val (rX 6) = 0)
    (hv0 : σ.val v = 0) (hcap : 2 ^ (natBitLength L[i] + 1) ≤ cap) :
    Runs cap (rdF X v) σ (rdCost L[i]) (fun τ => NatAt X L rest τ (i + 1) ∧ τ.val v = L[i] ∧
      SameExcept σ τ [X] [v]) := by
  have hd : [rX 3, rX 4, v, rX 5, rX 6].Nodup := by
    have a3 := hv 3 (by simp); have a4 := hv 4 (by simp); have a5 := hv 5 (by simp); have a6 := hv 6 (by simp)
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true]
    refine ⟨⟨by polyTabNe, a3, by polyTabNe, by polyTabNe⟩, ⟨a4, by polyTabNe, by polyTabNe⟩, ⟨fun h => a5 h.symm, fun h => a6 h.symm⟩, by polyTabNe⟩
  have e := readN_spec cap X L rest (rX 3) (rX 4) v (rX 5) (rX 6) hd σ i hσ hi h3 h4 h5 h6 (by rw [hv0]; omega)
  refine ⟨_, WXExec.wm e, ⟨?_, ?_⟩, ?_, ?_⟩
  · simp [hσ.1]
  · simp
  · simp [hv0]
  · exact se_hv σ X _ v _

theorem skF_spec (cap : ℕ) (X : Fin (NSx te qa + 1)) (K : Fin NRk) (hK : ∀ j : Fin 64, j.val ∈ [3, 4] → rX j ≠ K)
    (L : List ℕ) (rest : List Bool) (σ : WSt) (i m : ℕ) (hσ : NatAt X L rest σ i) (hm : i + m ≤ L.length)
    (h3 : σ.val (rX 3) = 0) (h4 : σ.val (rX 4) = 0) (hKv : σ.val K = m)
    (hfit : ∀ x ∈ L, natBitLength x + 1 ≤ cap) (hcm : m ≤ cap) :
    Runs cap (skF X K) σ (skCost ((L.drop i).take m)) (fun τ => NatAt X L rest τ (i + m) ∧ τ.val K = 0 ∧
      SameExcept σ τ [X] [K]) := by
  have e := skipNs_spec cap X L rest K (rX 3) (rX 4) (fun h => hK 3 (by simp) h.symm) (fun h => hK 4 (by simp) h.symm)
    (by polyTabNe) σ i m hσ hKv hm h3 h4 hfit hcm
  refine ⟨_, WXExec.wm e, ⟨?_, ?_⟩, ?_, ?_⟩
  · simp [hσ.1]
  · simp
  · simp
  · exact se_vh σ X _ K _

end NearCubicGates.Close.Expand.PolyTab
