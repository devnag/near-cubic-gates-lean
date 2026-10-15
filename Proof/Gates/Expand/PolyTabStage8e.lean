import Proof.Gates.Expand.PolyTabStage8d

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

def vLoop : WX := .whr (rX 26) (.seq (WMX.dec (rX 26)) vBlock)

/-- The records of the first `k` variables. -/
def vtRecs (Wb : ℕ) (E : ExpandMachine) (r : TabReq) (k : ℕ) : List Bool :=
  ((List.finRange r.V).take k).flatMap (vRecs Wb E r)

theorem occRecs_length (o : Occ) : (occRecs o).length = 2 + o.inW.length + o.outW.length := by
  simp [occRecs]; ring

theorem vRecs_length (Wb : ℕ) (E : ExpandMachine) (r : TabReq) (v : Fin r.V) :
    (vRecs Wb E r v).length = (r.k + r.s + 2) * (2 * Wb + 1) := by
  unfold vRecs
  rw [List.length_flatMap]
  have : ∀ x ∈ occRecs (occ (tabT E r) v), (frame (binary Wb x)).length = 2 * Wb + 1 := fun x _ => by
    rw [frame_length, binary_length]
  rw [List.map_congr_left this]
  simp only [List.map_const', List.sum_replicate, smul_eq_mul, occRecs_length, occ, List.length_ofFn]
  ring

theorem vtRecs_length (Wb : ℕ) (E : ExpandMachine) (r : TabReq) (k : ℕ) (hk : k ≤ r.V) :
    (vtRecs Wb E r k).length = k * ((r.k + r.s + 2) * (2 * Wb + 1)) := by
  unfold vtRecs
  rw [List.length_flatMap]
  simp only [vRecs_length, List.map_const', List.sum_replicate, smul_eq_mul, List.length_take, List.length_finRange]
  rw [min_eq_left hk]

theorem vLoop_spec (cap Wb : ℕ) (E : ExpandMachine) (r : TabReq) (hW : 1 ≤ Wb) (inp : List Bool) (hd : ℕ)
    (σA : WSt) (outV : List Bool) (hWb : 2 * 2 ^ r.B + 1 < 2 ^ Wb) (hBn : r.n < 2 ^ Wb) (hGW : r.G < 2 ^ Wb)
    (τ : WSt) (hI : TS Wb inp hd (recStream (((preN r).map (· % 2 ^ Wb)).map (binary Wb))) σA outV τ)
    (h43 : τ.val (rX 43) = pV r + 1) (hR : VRegs r τ) (h26 : τ.val (rX 26) = r.V)
    (hcap : ((preN r).length + 1) * (2 * Wb + 1) + 4 * (preN r).length + outV.length +
      (r.V + 1) * ((r.k + r.s + 2) * (2 * Wb + 1)) + 4 * Wb + 40 + r.G * (2 * r.n + 3) ≤ cap) :
    Runs cap vLoop τ (r.V * (vBlockCost Wb (preN r).length r.G r.n r.k r.s + 4) + 1)
      (fun ρ => TS Wb inp hd (recStream (((preN r).map (· % 2 ^ Wb)).map (binary Wb))) σA
        (outV ++ vtRecs Wb E r r.V) ρ ∧ VRegs r ρ ∧ ρ.val (rX 26) = 0 ∧
        KeepS [5, 20, 16, 17, 21, 23, 24, 43, 26] τ ρ) := by
  let Inv : ℕ → WSt → Prop := fun k ρ =>
    TS Wb inp hd (recStream (((preN r).map (· % 2 ^ Wb)).map (binary Wb))) σA (outV ++ vtRecs Wb E r k) ρ ∧
      ρ.val (rX 43) = pV r + 1 + 2 * k ∧ VRegs r ρ ∧ KeepS [5, 20, 16, 17, 21, 23, 24, 43, 26] τ ρ
  have hV : r.V ≤ cap := by
    have : r.V ≤ (r.V + 1) * ((r.k + r.s + 2) * (2 * Wb + 1)) := by
      have : 1 ≤ (r.k + r.s + 2) * (2 * Wb + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
      nlinarith
    omega
  obtain ⟨ρ, eρ, ⟨hρ, _, hRρ, kρ⟩, h26ρ⟩ := Runs.count (cap := cap) (K := rX 26) (body := vBlock)
    (vBlockCost Wb (preN r).length r.G r.n r.k r.s) r.V Inv hV (fun k hk μ ⟨hμ, m43, mR, mk⟩ _ => by
      have hμ' := ts_reg hμ 26 (by simp) (r.V - k - 1)
      have hR' : VRegs r (μ.setv (rX 26) (r.V - k - 1)) :=
        ⟨by simp [mR.z16], by simp [mR.z17], by simp [mR.z21], by simp [mR.z44], by simp [mR.z24], by simp [mR.z22],
          by simp [mR.r15], by simp [mR.r25], by simp [mR.r11], by simp [mR.r12]⟩
      have hl := vtRecs_length Wb E r k hk.le
      have hkX : (k + 1) * ((r.k + r.s + 2) * (2 * Wb + 1)) ≤ (r.V + 1) * ((r.k + r.s + 2) * (2 * Wb + 1)) :=
        Nat.mul_le_mul_right _ (by omega)
      have e1 : (k + 1) * ((r.k + r.s + 2) * (2 * Wb + 1)) = k * ((r.k + r.s + 2) * (2 * Wb + 1)) +
        (r.k + r.s + 2) * (2 * Wb + 1) := by ring
      refine (vBlock_spec cap Wb E r hW inp hd σA _ ⟨k, hk⟩ hWb hBn hGW _ hμ' (by simp [m43]) hR'
        (by simp only [List.length_append, hl]; omega)).post fun ν ⟨hν, n43, nR, nk⟩ => ⟨⟨?_, ?_, nR, ?_⟩, ?_⟩
      · have e : vtRecs Wb E r (k + 1) = vtRecs Wb E r k ++ vRecs Wb E r ⟨k, hk⟩ := by
          unfold vtRecs
          rw [List.take_add_one, List.getElem?_eq_getElem (by simp; exact hk)]
          simp
        rw [e, ← List.append_assoc]; exact hν
      · rw [n43]; ring
      · intro j hj
        rw [nk j (fun hm => hj (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hm ⊢; omega))]
        simp only [WState.setv_val]
        rw [Function.update_of_ne (rX_ne (fun e => hj (by rw [e]; simp)))]
        exact mk j hj
      · rw [nk 26 (by decide)]; simp)
    τ ⟨by simpa [vtRecs] using hI, by simp [h43], hR, fun _ _ => rfl⟩ h26
  exact ⟨ρ, eρ, hρ, hRρ, h26ρ, kρ⟩

end NearCubicGates.Close.Expand.PolyTab
