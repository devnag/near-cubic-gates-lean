import Proof.Gates.Succinct.Body
import Proof.Gates.CheckedPCPP.WMXReady
import Proof.MachineModel.UAcceptanceCarrier

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicGates.Close.Succinct

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicGates.Close.WordPrograms
open NearCubicGates.Close.CheckedPCPP (coldBank ConfRel runFrom_rel coldBank_s coldBank_c coldBank_r)
open NearCubicWires.WireExponent3_5.PrimAsm.DockW (tape_cases sTape_val cTape_val rTape_val wenc_A_c)

/-- A `WMX` derivation from the cold start (heads and registers `0`, blank cell) is a run of the compiled machine
from the cold bank, ending with the end state's heads and streams. -/
theorem cold_run {ns nr cap : ℕ} {P : WMX ns nr} {σ τ : WState ns nr} {n : ℕ} (h : WXExec cap P σ τ n)
    (hsh : ∀ i, σ.sh i = 0) (hval : ∀ r, σ.val r = 0) (hcell : σ.cell = false) :
    ∃ r, runFrom P.compile n (initialConfiguration P.compile (coldBank σ)) = some r ∧
      r.final.heads = (wenc cap τ).H ∧ ∀ i, r.final.tapes (sTape i) = τ.st i := by
  obtain ⟨r, hr, hh, ht, _⟩ := WXExec.run cap h hsh hval
  let E : Fin (ns + 2 + nr) → Prop := fun j => ∃ i, j = sTape i
  have hrel : ConfRel E (initialConfiguration P.compile (wenc cap σ).A)
      (initialConfiguration P.compile (coldBank σ)) := by
    refine ⟨rfl, rfl, ?_, ?_⟩
    · intro j
      simp only [initialConfiguration]
      rcases tape_cases j with ⟨i, rfl⟩ | rfl | ⟨q, rfl⟩
      · rw [wenc_A_s, coldBank_s]; exact RdEq.refl _
      · rw [wenc_A_c, coldBank_c, hcell]; exact rdEq_blank _ (by simp)
      · rw [wenc_A_r, coldBank_r, hval q, regTape_zero]; exact rdEq_blank _ (by simp)
    · rintro j ⟨i, rfl⟩
      simp only [initialConfiguration]
      rw [wenc_A_s, coldBank_s]
  obtain ⟨r', hr', hrel', _⟩ := runFrom_rel P.compile E n hrel r hr
  refine ⟨r', hr', by rw [← hrel'.heads, hh], fun i => ?_⟩
  rw [← hrel'.exact (sTape i) ⟨i, rfl⟩, ht, wenc_A_s]

section Machine
variable {k : ℕ} (H : OrdinaryHierarchy (fun n => n ^ (k + 2))) (G : ℕ)

/-- The hierarchy verifier's tape count. -/
def tH : ℕ := H.verifier.tapeCount

theorem two_le_tH : 2 ≤ tH H := H.verifier.twoTapes

/-- The succinct verifier's tape count. -/
abbrev vT : ℕ := (tH H + 4) + 2 + nrV

/-- The compiled body. -/
noncomputable def bodyM := (body G H.coefficient k (tH H) (two_le_tH H)).compile

/-- The hierarchy verifier's tapes: the body's streams `5 … tH + 4`. -/
def hmap : Fin (tH H) → Fin (vT H) := fun j => sTape (nr := nrV) (bs (tH H) (j.val + 5) (by omega))

theorem hmap_inj : Function.Injective (hmap H) := by
  intro a b h
  have := congrArg Fin.val h
  simp [hmap, sTape, bs] at this
  ext; omega

noncomputable def hDock := RecoveryFocus.machine (hmap H) H.verifier.machine

/-- The body, then the hierarchy verifier. -/
noncomputable def m0 := Composition.machine (bodyM H G) (hDock H)

/-- The tape renaming: the verifier's tapes `1` and `2` are swapped (the body's result cell is its tape `1`, its
witness stream its tape `2`). -/
def swap12 (t : ℕ) (ht : 3 ≤ t) : Fin t → Fin t :=
  fun j => if j.val = 1 then ⟨2, by omega⟩ else if j.val = 2 then ⟨1, by omega⟩ else j

theorem swap12_swap12 (t : ℕ) (ht : 3 ≤ t) (j : Fin t) : swap12 t ht (swap12 t ht j) = j := by
  unfold swap12; ext; split_ifs <;> simp_all <;> omega

theorem swap12_inj (t : ℕ) (ht : 3 ≤ t) : Function.Injective (swap12 t ht) := by
  intro a b h; rw [← swap12_swap12 t ht a, h, swap12_swap12]

theorem three_le_vT : 3 ≤ vT H := by have := two_le_tH H; unfold vT; omega

/-- **The succinct verifier `𝒱_G`** (paper lem:succinct-verifier). -/
noncomputable def verifierV : OrdinaryVerifier where
  tapeCount := vT H
  stateCount := (body G H.coefficient k (tH H) (two_le_tH H)).size + H.verifier.stateCount
  twoTapes := by have := three_le_vT H; omega
  machine := RecoveryFocus.machine (swap12 (vT H) (three_le_vT H)) (m0 H G)
  accepting := fun st => if h : (body G H.coefficient k (tH H) (two_le_tH H)).size ≤ st.val then
    H.verifier.accepting ⟨st.val - (body G H.coefficient k (tH H) (two_le_tH H)).size, by have := st.isLt; omega⟩
    else false

end Machine

end NearCubicGates.Close.Succinct
