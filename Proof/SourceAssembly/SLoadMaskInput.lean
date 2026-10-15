import Proof.SourceAssembly.SLoadLead

/-! The first conjunct of `MaskSeedCode.Ready`.

`Ready` demands, for the chosen prefix program,
`Step c.lead prefixFuel H A (dockH c.maskSlots maskH 0)
  (install c.maskSlots maskA (fun i => ZeroPadding.pad (maskReserve i)
    ((maskData a r).input mask.work i)))`.
This module discharges exactly that statement from the physical prefix run,
with `maskH := H`, `maskA := A`, and a `maskReserve` that is zero on the four
live input tapes and the ambient allocation on the worker's private tapes. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace SLoad.MaskInput
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairSource.VerifierDecoding SupplierEstimator
open FixedLivePackets PacketProduction MaskedFamilySource
noncomputable section

/-- The four live mask input tapes, inside the worker's slot family. -/
def live {U work : Nat} (maskSlots : Fin (5 + work) → Fin U) : Fin 4 → Fin U :=
  fun j => maskSlots ⟨j.val, by omega⟩

theorem live_injective {U work : Nat} (maskSlots : Fin (5 + work) → Fin U)
    (hinj : Function.Injective maskSlots) : Function.Injective (live maskSlots) := by
  intro i j hij
  have h := hinj hij
  have hv : i.val = j.val := by
    have hw := congrArg Fin.val h
    simpa using hw
  exact Fin.ext hv

/-- Reserve profile: exact words on the four live tapes, retained zero backing
on whatever the worker's private tapes were allocated. -/
def reserve {work : Nat} (blank : Fin (5 + work) → Nat) : Fin (5 + work) → Nat :=
  fun i => if i.val < 4 then 0 else blank i

/-- The physical prefix writes exactly `MaskData.input`. -/
theorem mask_input_step {U work : Nat} (maskSlots : Fin (5 + work) → Fin U)
    (hinj : Function.Injective maskSlots) (ret : Fin 4 → Fin U) (log : Fin U)
    (hrm : ∀ (i : Fin 4) (j : Fin (5 + work)), ret i ≠ maskSlots j)
    (hrl : ∀ i, ret i ≠ log) (hlm : ∀ j, log ≠ maskSlots j)
    (d : MaskData) (cap : Nat) (uq uK um : List Bool)
    (hq : uq.length = d.q) (hk : uK.length = d.K) (hmm : um.length = d.m)
    (cs : d.supportWord.length ≤ cap) (cq : 4 * uq.length + 3 ≤ cap)
    (ck : 4 * uK.length + 3 ≤ cap) (cm : 4 * um.length + 3 ≤ cap)
    (blank : Fin (5 + work) → Nat)
    (H : Fin U → Nat) (A : Fin U → List Bool)
    (hHr : ∀ i, H (ret i) = 0) (hHm : ∀ j, H (maskSlots j) = 0) (hHl : H log = 0)
    (hA0 : A (ret 0) = ZeroPadding.pad cap (frame d.supportWord))
    (hA1 : A (ret 1) = ZeroPadding.pad cap (frame uq))
    (hA2 : A (ret 2) = ZeroPadding.pad cap (frame uK))
    (hA3 : A (ret 3) = ZeroPadding.pad cap (frame um))
    (hLive : ∀ j : Fin (5 + work), j.val < 4 → A (maskSlots j) = [])
    (hPriv : ∀ j : Fin (5 + work), 4 ≤ j.val → A (maskSlots j) = List.replicate (blank j) false)
    (hAl : A log = List.replicate cap false) :
    Step (Lead.machine ret (live maskSlots) log)
      (Lead.cost d.supportWord.length d.q d.K d.m) H A
      (dockH maskSlots H (fun _ => 0))
      (install maskSlots A
        (fun i => ZeroPadding.pad (reserve blank i) (d.input work i))) := by
  classical
  have hminj := live_injective maskSlots hinj
  have hbase := Lead.lead_step ret (live maskSlots) log hminj
    (fun i j => hrm i _) (fun i => hrl i) (fun j => hlm _)
    cap d.supportWord uq uK um cs cq ck cm H A hHr
    (fun j => hHm _) hHl hA0 hA1 hA2 hA3
    (fun j => hLive _ j.isLt) hAl
  have hheads : dockH maskSlots H (fun _ => 0) = H :=
    SLoad.dockH_existing maskSlots H (fun _ => 0) hHm
  have hcost : Lead.cost d.supportWord.length uq.length uK.length um.length
      = Lead.cost d.supportWord.length d.q d.K d.m := by rw [hq, hk, hmm]
  rw [hcost] at hbase
  rw [hheads]
  refine hbase.congr rfl ?_
  refine Lead.install_eq maskSlots hinj A _ _ ?_ ?_
  · intro j
    by_cases hj : j.val < 4
    · have hslot : maskSlots j = live maskSlots ⟨j.val, hj⟩ := by
        refine congrArg maskSlots (Fin.ext ?_)
        rfl
      rw [hslot, install_slot (live maskSlots) hminj]
      rw [reserve, if_pos hj, ZeroPadding.pad_zero]
      have hcases : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨ j.val = 3 := by omega
      rcases hcases with hv | hv | hv | hv
      · have he : (⟨j.val, hj⟩ : Fin 4) = 0 := Fin.ext (by simpa using hv)
        rw [he]
        simp [Lead.payload, MaskData.input, hv]
      · have he : (⟨j.val, hj⟩ : Fin 4) = 1 := Fin.ext (by simpa using hv)
        rw [he]
        simp [Lead.payload, MaskData.input, hv, hq]
      · have he : (⟨j.val, hj⟩ : Fin 4) = 2 := Fin.ext (by simpa using hv)
        rw [he]
        simp [Lead.payload, MaskData.input, hv, hk]
      · have he : (⟨j.val, hj⟩ : Fin 4) = 3 := Fin.ext (by simpa using hv)
        rw [he]
        simp [Lead.payload, MaskData.input, hv, hmm]
    · have hout : ∀ k : Fin 4, live maskSlots k ≠ maskSlots j := by
        intro k hk'
        have := hinj hk'
        have hv : (Fin.castLE (show 4 ≤ 5 + work by omega) k).val = j.val := congrArg Fin.val this
        exact hj (by simpa [Fin.castLE] using hv ▸ k.isLt)
      rw [install_other (live maskSlots) A _ _ hout, hPriv j (by omega)]
      have hin : d.input work j = [] := by
        have h0 : j.val ≠ 0 := by omega
        have h1 : j.val ≠ 1 := by omega
        have h2 : j.val ≠ 2 := by omega
        have h3 : j.val ≠ 3 := by omega
        simp [MaskData.input, h0, h1, h2, h3]
      rw [hin, reserve, if_neg hj]
      simp [ZeroPadding.pad]
  · intro i hi
    exact install_other (live maskSlots) A _ i (fun k => hi _)

end
end SLoad.MaskInput
