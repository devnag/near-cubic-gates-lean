import Proof.SourceAssembly.SLoadSuffixFrame
import Proof.SourceAssembly.SLoadRequestLead

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace SLoad.RequestSuffix
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open FixedLivePackets PacketProduction MaskedFamilySource
noncomputable section

/-- Reserve profile for the packet's own slot family: the framed word exactly
on tape `0`, the retained zero backing on every other packet tape. -/
def reserve {tc : Nat} (blank : Fin tc → Nat) : Fin tc → Nat :=
  fun i => if i.val = 0 then 0 else blank i

/-- The second conjunct of `MaskSeedCode.Ready`, discharged for the supplied
mask producer's returned bank. -/
theorem request_suffix_step {U work : Nat} (slot : Fin 13 → Fin U)
    (hinj : Function.Injective slot)
    (maskSlots : Fin (5 + work) → Fin U) (hminj : Function.Injective maskSlots)
    (prog : Program) (slots : Fin prog.tapeCount → Fin U)
    (hsinj : Function.Injective slots)
    (a : DecompositionAlgorithm) (r : Request)
    (B : Fin (5 + work) → List Bool) (hB : B ⟨4, by omega⟩ = (maskData a r).word)
    (maskReserve : Fin (5 + work) → Nat) (blank : Fin prog.tapeCount → Nat)
    (capD cap : Nat)
    (cq : 2 * (B ⟨4, by omega⟩).length + 1 ≤ cap)
    (cn : 2 * r.nativeWord.length + 1 ≤ cap)
    (cs : 2 * (r.supportWord a).length + 1 ≤ cap)
    (ci : 2 * (r.indexWord a).length + 1 ≤ cap)
    (ct : 2 * (r.topWord a).length + 1 ≤ cap)
    (H : Fin U → Nat) (A : Fin U → List Bool)
    (hmsk : slot 0 = maskSlots ⟨4, by omega⟩)
    (hoffm : ∀ j : Fin 13, j ≠ 0 → ∀ i, maskSlots i ≠ slot j)
    (hslot0 : ∀ j : Fin prog.tapeCount, j.val = 0 → slots j = slot 11)
    (hoffp : ∀ j : Fin prog.tapeCount, j.val ≠ 0 → ∀ k, slot k ≠ slots j)
    (hmp : ∀ (j : Fin prog.tapeCount) (i : Fin (5 + work)), maskSlots i ≠ slots j)
    (hHm : ∀ i, H (maskSlots i) = 0) (hH : ∀ j, H (slot j) = 0)
    (hHs : ∀ j, H (slots j) = 0)
    (hA : ∀ j : Fin 13, j ≠ 0 → A (slot j)
      = SuffixFrame.entry (maskReserve ⟨4, by omega⟩) capD cap (B ⟨4, by omega⟩)
          r.nativeWord (r.supportWord a) (r.indexWord a) (r.topWord a) j)
    (hblank : ∀ j : Fin prog.tapeCount, j.val ≠ 0 →
      A (slots j) = List.replicate (blank j) false) :
    ∃ ambientA : Fin U → List Bool,
      Step (SuffixFrame.machine slot)
        (SuffixFrame.cost (B ⟨4, by omega⟩).length r.nativeWord.length
          (r.supportWord a).length (r.indexWord a).length (r.topWord a).length)
        (dockH maskSlots H (fun _ => 0))
        (install maskSlots A (fun i => ZeroPadding.pad (maskReserve i) (B i)))
        (dockH slots H (fun _ => 0))
        (install slots ambientA (fun i => ZeroPadding.pad (reserve blank i)
          (prog.inputTapes (r.input a) i))) ∧
      (∀ x, (∀ j, slot j ≠ x) →
        ambientA x = install maskSlots A (fun i => ZeroPadding.pad (maskReserve i) (B i)) x) := by
  classical
  set A1 : Fin U → List Bool :=
    install maskSlots A (fun i => ZeroPadding.pad (maskReserve i) (B i)) with hA1
  have hentry : ∀ j : Fin 13, A1 (slot j)
      = SuffixFrame.entry (maskReserve ⟨4, by omega⟩) capD cap (B ⟨4, by omega⟩)
          r.nativeWord (r.supportWord a) (r.indexWord a) (r.topWord a) j := by
    intro j
    by_cases hj : j = 0
    · subst hj
      rw [hA1, hmsk, install_slot maskSlots hminj]
      rfl
    · rw [hA1, install_other maskSlots A _ (slot j) (fun i => hoffm j hj i)]
      exact hA j hj
  obtain ⟨F, hstep, hout, hkeep⟩ := SuffixFrame.suffix_step slot hinj a r B hB
    (maskReserve ⟨4, by omega⟩) capD cap cq cn cs ci ct H A1 hH hentry
  have hdm : dockH maskSlots H (fun _ => 0) = H :=
    SLoad.dockH_existing maskSlots H (fun _ => 0) hHm
  have hds : dockH slots H (fun _ => 0) = H :=
    SLoad.dockH_existing slots H (fun _ => 0) hHs
  have hbank : F = install slots F
      (fun i => ZeroPadding.pad (reserve blank i) (prog.inputTapes (r.input a) i)) := by
    refine Lead.install_eq slots hsinj F F _ ?_ (fun i hi => rfl)
    intro j
    by_cases hj : j.val = 0
    · have h1 : reserve blank j = 0 := by simp only [reserve, if_pos hj]
      have h2 : prog.inputTapes (r.input a) j = frame (r.input a) := by
        simp only [Program.inputTapes, if_pos hj]
      rw [h1, h2, ZeroPadding.pad_zero, hslot0 j hj]
      exact hout
    · rw [hkeep (slots j) (fun k => hoffp j hj k), hA1,
        install_other maskSlots A _ (slots j) (fun i => hmp j i), hblank j hj,
        reserve, if_neg hj, Program.inputTapes, if_neg hj, Words.pad_nil]
  refine ⟨F, ?_, ?_⟩
  · rw [hdm, hds, ← hbank]
    exact hstep
  · intro x hx
    exact hkeep x hx

end
end SLoad.RequestSuffix
