import Proof.Gates.Expand.PolyTabHead8

set_option autoImplicit false

namespace NearCubicGates.Close.Expand.PolyTab

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicGates.Close.CounterMachine NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.TabMachine
open NearCubicWires.RepairRepresentation

def TailSpec (E : ExpandMachine) (a : WilliamsAlgorithm) (prog : WMX (NSx (te E) (Qa a)) NRk) : Prop :=
  ∀ (r : TabReq) (cap : ℕ) (σ : WState (NSx (te E) (Qa a)) NRk), TailPre E a r cap σ →
    Runs cap prog σ (tailCost E a r) (fun τ => τ.st sOUT = tableWord (printerOrder r.s) (width E r) r)

/-- A cost class at the tabulation path. -/
def TabCls (f : TabReq → ℕ) : Prop := ∃ C e : ℕ, ∀ r : TabReq, f r ≤ C * 2 ^ r.s * tabSz r ^ e

theorem tabCls_add {f g : TabReq → ℕ} (hf : TabCls f) (hg : TabCls g) (c : ℕ) :
    TabCls (fun r => 2 * (f r + c + g r) + 2) := by
  obtain ⟨C1, e1, h1⟩ := hf
  obtain ⟨C2, e2, h2⟩ := hg
  refine ⟨2 * C1 + 2 * C2 + 2 * c + 2, e1 + e2, fun r => ?_⟩
  have ht : 1 ≤ tabSz r := by unfold tabSz; omega
  have hp : 1 ≤ 2 ^ r.s := Nat.one_le_two_pow
  have a1 : tabSz r ^ e1 ≤ tabSz r ^ (e1 + e2) := Nat.pow_le_pow_right ht (by omega)
  have a2 : tabSz r ^ e2 ≤ tabSz r ^ (e1 + e2) := Nat.pow_le_pow_right ht (by omega)
  have a3 : 1 ≤ tabSz r ^ (e1 + e2) := Nat.one_le_pow _ _ ht
  have b1 : C1 * 2 ^ r.s * tabSz r ^ e1 ≤ C1 * 2 ^ r.s * tabSz r ^ (e1 + e2) := Nat.mul_le_mul_left _ a1
  have b2 : C2 * 2 ^ r.s * tabSz r ^ e2 ≤ C2 * 2 ^ r.s * tabSz r ^ (e1 + e2) := Nat.mul_le_mul_left _ a2
  have b3 : 1 ≤ 2 ^ r.s * tabSz r ^ (e1 + e2) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have e : (2 * C1 + 2 * C2 + 2 * c + 2) * 2 ^ r.s * tabSz r ^ (e1 + e2) =
      2 * (C1 * 2 ^ r.s * tabSz r ^ (e1 + e2)) + 2 * (C2 * 2 ^ r.s * tabSz r ^ (e1 + e2)) +
        (2 * c + 2) * (2 ^ r.s * tabSz r ^ (e1 + e2)) := by ring
  have h1' := h1 r
  have h2' := h2 r
  have b4 : 2 * c + 2 ≤ (2 * c + 2) * (2 ^ r.s * tabSz r ^ (e1 + e2)) := Nat.le_mul_of_pos_right _ (by omega)
  show 2 * (f r + c + g r) + 2 ≤ (2 * C1 + 2 * C2 + 2 * c + 2) * 2 ^ r.s * tabSz r ^ (e1 + e2)
  rw [e]
  generalize C1 * 2 ^ r.s * tabSz r ^ (e1 + e2) = A at b1 ⊢
  generalize C2 * 2 ^ r.s * tabSz r ^ (e1 + e2) = B at b2 ⊢
  generalize (2 * c + 2) * (2 ^ r.s * tabSz r ^ (e1 + e2)) = D at b4 ⊢
  omega

theorem lensK_out (E : ExpandMachine) (a : WilliamsAlgorithm) (lcap : ℕ) :
    lensK (te E) (Qa a) lcap sOUT = 0 := by
  unfold lensK
  rw [if_neg]
  intro e; have := congrArg Fin.val e; rw [sOUT_val, sL_val] at this; omega

/-- **PolyTab.** -/
noncomputable def PolyTabOf (E : ExpandMachine) (a : WilliamsAlgorithm) (prog : WMX (NSx (te E) (Qa a)) NRk)
    (T : TailSpec E a prog) (hH : TabCls (headCost E)) (hT : TabCls (tailCost E a)) : TabMachine where
  order r := printerOrder r.s
  perm r := printerOrder_perm r.s
  width := width E
  fits := width_fits E
  budget r := 2 * (headCost E r + 1 + tailCost E a r) + 2
  wf := wordFunction_of_ideal (.seq (headP E a) prog) sOUT (by simp [sOUT]) (capH E)
    (fun r => lensK (te E) (Qa a) (E.budget ⟨r.V, r.F⟩)) (fun r => headCost E r + 1 + tailCost E a r)
    (fun _ => le_rfl) (fun r => ⟨lensK_out E a _, by
      obtain ⟨τ, e, hτ⟩ := Runs.seq (head_spec E a r (capH E r) le_rfl) (fun σ h => T r (capH E r) σ h)
      exact ⟨τ, e, hτ⟩⟩)
  cls := tabCls_add hH hT 1

theorem PolyTabOf_order (E : ExpandMachine) (a : WilliamsAlgorithm) (prog : WMX (NSx (te E) (Qa a)) NRk)
    (T : TailSpec E a prog) (hH : TabCls (headCost E)) (hT : TabCls (tailCost E a)) (r : TabReq) :
    (PolyTabOf E a prog T hH hT).order r = printerOrder r.s := rfl

end NearCubicGates.Close.Expand.PolyTab
