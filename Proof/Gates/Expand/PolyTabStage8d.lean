import Proof.Gates.Expand.PolyTabStage8c

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
open NearCubicGates.Close.CounterMachine NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.TabMachine
open NearCubicGates.Close.WordPrograms.SInt (encS)

variable {te qa : ℕ}

local notation "WX" => WMX (NSx te qa) NRk
local notation "WSt" => WState (NSx te qa) NRk

def vBlock : WX := .seq vA1 (.seq vA2 (.seq vB (.seq vC1 vC2)))

def vBlockCost (Wb N G n k s : ℕ) : ℕ :=
  vA1Cost Wb N + 1 + (vA2Cost G n + 1 + (vBCost Wb N + 1 + (vC1Cost Wb N k + 1 + vC2Cost Wb N s)))

/-- One variable's records. -/
def vRecs (Wb : ℕ) (E : ExpandMachine) (r : TabReq) (v : Fin r.V) : List Bool :=
  (occRecs (occ (tabT E r) v)).flatMap fun x => frame (binary Wb x)

theorem vRecs_eq (Wb : ℕ) (E : ExpandMachine) (r : TabReq) (v : Fin r.V) :
    vRecs Wb E r v = frame (binary Wb (if (r.role v).reference then 1 else 0)) ++
      frame (binary Wb (encS (r.gates (r.role v).gate).threshold)) ++
      crecs Wb r (r.role v).gate (innerIds r) r.k ++ crecs Wb r (r.role v).gate (outerIds r) r.s := by
  have t1 : (List.ofFn (innerIds r)).take r.k = List.ofFn (innerIds r) := List.take_of_length_le (by simp)
  have t2 : (List.ofFn (outerIds r)).take r.s = List.ofFn (outerIds r) := List.take_of_length_le (by simp)
  unfold vRecs crecs
  rw [t1, t2]
  unfold occRecs occ innerIds
  simp only [tabT, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]
  congr 1
  · cases (r.role v).reference <;> rfl
  · simp only [List.ofFn_eq_map, List.flatMap_map, List.map_map]
    rfl

/-- The registers the variable loop relies on. -/
structure VRegs (r : TabReq) (ρ : WSt) : Prop where
  z16 : ρ.val (rX 16) = 0
  z17 : ρ.val (rX 17) = 0
  z21 : ρ.val (rX 21) = 0
  z44 : ρ.val (rX 23) = 0
  z24 : ρ.val (rX 24) = 0
  z22 : ρ.val (rX 22) = 0
  r15 : ρ.val (rX 15) = 2 * r.n + 3
  r25 : ρ.val (rX 25) = pk r + 1
  r11 : ρ.val (rX 11) = r.k
  r12 : ρ.val (rX 12) = r.s

theorem vBlock_spec (cap Wb : ℕ) (E : ExpandMachine) (r : TabReq) (hW : 1 ≤ Wb) (inp : List Bool) (hd : ℕ)
    (σA : WSt) (outV : List Bool) (v : Fin r.V) (hWb : 2 * 2 ^ r.B + 1 < 2 ^ Wb) (hBn : r.n < 2 ^ Wb)
    (hGW : r.G < 2 ^ Wb) (τ : WSt)
    (hI : TS Wb inp hd (recStream (((preN r).map (· % 2 ^ Wb)).map (binary Wb))) σA outV τ)
    (h43 : τ.val (rX 43) = pV r + 1 + 2 * v.val) (hR : VRegs r τ)
    (hcap : ((preN r).length + 1) * (2 * Wb + 1) + 4 * (preN r).length + outV.length +
      (r.k + r.s + 2) * (2 * Wb + 1) + 4 * Wb + 40 + r.G * (2 * r.n + 3) ≤ cap) :
    Runs cap vBlock τ (vBlockCost Wb (preN r).length r.G r.n r.k r.s)
      (fun ρ => TS Wb inp hd (recStream (((preN r).map (· % 2 ^ Wb)).map (binary Wb))) σA (outV ++ vRecs Wb E r v) ρ ∧
        ρ.val (rX 43) = pV r + 1 + 2 * v.val + 2 ∧ VRegs r ρ ∧ KeepS [5, 20, 16, 17, 21, 23, 24, 43] τ ρ) := by
  set g := (r.role v).gate with hg
  have bl : ∀ (x : ℕ), (frame (binary Wb x)).length = 2 * Wb + 1 := fun x => by rw [frame_length, binary_length]
  obtain ⟨τ1, e1, h1, v1_43, v1_16, k1⟩ := vA1_spec cap Wb r hW inp hd σA outV v hBn hGW τ hI h43 hR.z16 (by nlinarith)
  obtain ⟨τ2, e2, h2, v2_17, v2_16, k2⟩ := vA2_spec cap Wb r inp hd _ σA _ g τ1 h1 v1_16
    (by rw [k1 17 (by decide), hR.z17]) (by rw [k1 22 (by decide), hR.z22]) (by rw [k1 15 (by decide), hR.r15])
    (by omega)
  obtain ⟨τ3, e3, h3, v3_21, k3⟩ := vB_spec cap Wb r hW inp hd σA _ g hWb τ2 h2 v2_17
    (by rw [k2 21 (by decide), k1 21 (by decide), hR.z21]) (by rw [k2 15 (by decide), k1 15 (by decide), hR.r15])
    (by simp only [List.length_append, bl]; nlinarith)
  have kk : KeepS [5, 20, 16, 17, 21, 43] τ τ3 := fun j hj => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
    rw [k3 j (by simp; omega), k2 j (by simp; omega), k1 j (by simp; omega)]
  obtain ⟨τ4, e4, h4, v4_17, v4_44, v4_16, v4_21, v4_24, k4⟩ := vC1_spec cap Wb r hW inp hd σA _ g hWb hBn τ3 h3
    (by rw [k3 17 (by decide), v2_17]) (by rw [k3 16 (by decide), v2_16]) v3_21
    (by rw [kk 23 (by decide), hR.z44]) (by rw [kk 24 (by decide), hR.z24]) (by rw [kk 25 (by decide), hR.r25])
    (by rw [kk 11 (by decide), hR.r11]) (by simp only [List.length_append, bl]; nlinarith)
  have kk4 : KeepS [5, 20, 16, 17, 21, 43, 23, 24] τ τ4 := fun j hj => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
    rw [k4 j (by simp; omega), kk j (by simp; omega)]
  have hl4 := crecs_length Wb r g (innerIds r) r.k
  obtain ⟨τ5, e5, h5, v5_17, v5_44, v5_16, v5_21, v5_24, k5⟩ := vC2_spec cap Wb r hW inp hd σA _ g hWb hBn τ4 h4 v4_17
    v4_16 v4_21 v4_44 v4_24 (by rw [kk4 12 (by decide), hR.r12])
    (by simp only [List.length_append, bl]; nlinarith)
  have kk5 : KeepS [5, 20, 16, 17, 21, 23, 24, 43] τ τ5 := fun j hj => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
    rw [k5 j (by simp; omega), kk4 j (by simp; omega)]
  refine ⟨τ5, WXExec.mono (WXExec.seq e1 <| WXExec.seq e2 <| WXExec.seq e3 <| WXExec.seq e4 e5)
    (by unfold vBlockCost; omega), ?_, ?_, ⟨v5_16, v5_17, v5_21, v5_44, v5_24, ?_, ?_, ?_, ?_, ?_⟩, kk5⟩
  · rw [vRecs_eq]; simp only [List.append_assoc] at h5 ⊢; exact h5
  · rw [k5 43 (by decide), k4 43 (by decide), k3 43 (by decide), k2 43 (by decide), v1_43]
  · rw [kk5 22 (by decide), hR.z22]
  · rw [kk5 15 (by decide), hR.r15]
  · rw [kk5 25 (by decide), hR.r25]
  · rw [kk5 11 (by decide), hR.r11]
  · rw [kk5 12 (by decide), hR.r12]

end NearCubicGates.Close.Expand.PolyTab
