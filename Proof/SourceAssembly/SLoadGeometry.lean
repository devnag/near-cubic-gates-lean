import Proof.SourceAssembly.SLoadMaskReady

/-! A concrete ambient layout for the physical source loader.

`SLoad.MaskReady.mask_ready` takes its slot geometry as hypotheses: the three
slot families are injective, the mask worker's output slot IS `slot 0`, the
packet program's framed tape IS `slot 11`, the families are otherwise
pairwise disjoint, and the six single scratch slots are fresh.  This module
exhibits one closed assignment that satisfies every one of them, on an ambient
universe of `27 + mask.work + packet.ordinary.program.tapeCount` tapes:

```
0 .. 12            the suffix frame `slot`,        with `slot 0` the mask output
13 .. 17+w         the mask worker, index 4 folded onto `slot 0`
18+w .. 17+w+t     the packet program, index 0 folded onto `slot 11`
18+w+t .. 21+w+t   the four retained request fields `ret`
22+w+t .. 26+w+t   retDrv, log, rawDrv, rawDst, rawLog
27+w+t .. 399+w+t  the 373 cold-cache pool slots
```

No `decide` over the whole universe is needed: every range is an interval of
numerals in `Fin.val`, so each disjointness is one `omega`. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace SLoad.Geometry
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open FixedLivePackets PacketProduction MaskedFamilySource
noncomputable section

theorem ne_of_val {n : Nat} {x y : Fin n} (h : x.val ≠ y.val) : x ≠ y :=
  fun e => h (congrArg Fin.val e)

/-- The ambient tape count of the concrete layout. -/
def univ (w t : Nat) : Nat := 400 + w + t

def maskVal (w : Nat) (i : Fin (5 + w)) : Nat := if i.val = 4 then 0 else 13 + i.val

def slotsVal (w t : Nat) (j : Fin t) : Nat := if j.val = 0 then 11 else 18 + w + j.val

def slot (w t : Nat) (j : Fin 13) : Fin (univ w t) :=
  ⟨j.val, by have := j.isLt; show j.val < 400 + w + t; omega⟩

def maskSlots (w t : Nat) (i : Fin (5 + w)) : Fin (univ w t) :=
  ⟨maskVal w i, by
    have := i.isLt
    show maskVal w i < 400 + w + t
    unfold maskVal; split_ifs <;> omega⟩

def slots (w t : Nat) (j : Fin t) : Fin (univ w t) :=
  ⟨slotsVal w t j, by
    have := j.isLt
    show slotsVal w t j < 400 + w + t
    unfold slotsVal; split_ifs <;> omega⟩

def ret (w t : Nat) (k : Fin 4) : Fin (univ w t) :=
  ⟨18 + w + t + k.val, by have := k.isLt; show 18 + w + t + k.val < 400 + w + t; omega⟩

def retDrv (w t : Nat) : Fin (univ w t) := ⟨22 + w + t, by show 22 + w + t < 400 + w + t; omega⟩
def log (w t : Nat) : Fin (univ w t) := ⟨23 + w + t, by show 23 + w + t < 400 + w + t; omega⟩
def rawDrv (w t : Nat) : Fin (univ w t) := ⟨24 + w + t, by show 24 + w + t < 400 + w + t; omega⟩
def rawDst (w t : Nat) : Fin (univ w t) := ⟨25 + w + t, by show 25 + w + t < 400 + w + t; omega⟩
def rawLog (w t : Nat) : Fin (univ w t) := ⟨26 + w + t, by show 26 + w + t < 400 + w + t; omega⟩

/-! ### The five `Fin.val` ranges -/

theorem slot_val (w t : Nat) (j : Fin 13) : (slot w t j).val = j.val := rfl

theorem slot_lt (w t : Nat) (j : Fin 13) : (slot w t j).val < 13 := j.isLt

theorem mask_val (w t : Nat) (i : Fin (5 + w)) :
    (maskSlots w t i).val = 0 ∨ (13 ≤ (maskSlots w t i).val ∧ (maskSlots w t i).val < 18 + w) := by
  have hi := i.isLt
  show maskVal w i = 0 ∨ (13 ≤ maskVal w i ∧ maskVal w i < 18 + w)
  unfold maskVal; split_ifs <;> omega

theorem slots_val (w t : Nat) (j : Fin t) :
    (slots w t j).val = 11 ∨
      (18 + w ≤ (slots w t j).val ∧ (slots w t j).val < 18 + w + t) := by
  have hj := j.isLt
  show slotsVal w t j = 11 ∨ (18 + w ≤ slotsVal w t j ∧ slotsVal w t j < 18 + w + t)
  unfold slotsVal; split_ifs <;> omega

theorem ret_val (w t : Nat) (k : Fin 4) : (ret w t k).val = 18 + w + t + k.val := rfl

theorem ret_lt (w t : Nat) (k : Fin 4) :
    18 + w + t ≤ (ret w t k).val ∧ (ret w t k).val < 22 + w + t := by
  have := k.isLt
  exact ⟨by show 18 + w + t ≤ 18 + w + t + k.val; omega,
    by show 18 + w + t + k.val < 22 + w + t; omega⟩

/-! ### Injectivity of the three families -/

theorem slot_injective (w t : Nat) : Function.Injective (slot w t) := by
  intro i j h
  have hv : (slot w t i).val = (slot w t j).val := congrArg Fin.val h
  exact Fin.ext hv

theorem mask_injective (w t : Nat) : Function.Injective (maskSlots w t) := by
  intro i j h
  have hv : maskVal w i = maskVal w j := congrArg Fin.val h
  have hi := i.isLt
  have hj := j.isLt
  apply Fin.ext
  unfold maskVal at hv
  split_ifs at hv <;> omega

theorem slots_injective (w t : Nat) : Function.Injective (slots w t) := by
  intro i j h
  have hv : slotsVal w t i = slotsVal w t j := congrArg Fin.val h
  have hi := i.isLt
  have hj := j.isLt
  apply Fin.ext
  unfold slotsVal at hv
  split_ifs at hv <;> omega

/-! ### The two deliberate identifications -/

theorem mask_output (w t : Nat) : slot w t 0 = maskSlots w t ⟨4, by omega⟩ := by
  apply Fin.ext
  show (0 : Fin 13).val = maskVal w ⟨4, by omega⟩
  unfold maskVal
  simp

theorem packet_frame (w t : Nat) (j : Fin t) (hj : j.val = 0) :
    slots w t j = slot w t 11 := by
  apply Fin.ext
  show slotsVal w t j = (11 : Fin 13).val
  unfold slotsVal
  simp [hj]

/-! ### Freshness -/

theorem mask_off (w t : Nat) (j : Fin 13) (hj : j ≠ 0) (i : Fin (5 + w)) :
    maskSlots w t i ≠ slot w t j := by
  have hj0 : j.val ≠ 0 := by
    intro h; apply hj; apply Fin.ext; simpa using h
  have := slot_lt w t j
  have hm := mask_val w t i
  refine ne_of_val ?_
  rw [slot_val]
  omega

theorem slot_off (w t : Nat) (j : Fin t) (hj : j.val ≠ 0) (k : Fin 13) :
    slot w t k ≠ slots w t j := by
  have := slot_lt w t k
  have hs : (slots w t j).val = 18 + w + j.val := by
    show slotsVal w t j = 18 + w + j.val
    unfold slotsVal; rw [if_neg hj]
  refine ne_of_val ?_
  omega

theorem mask_packet (w t : Nat) (j : Fin t) (i : Fin (5 + w)) :
    maskSlots w t i ≠ slots w t j := by
  have hm := mask_val w t i
  have hs := slots_val w t j
  exact ne_of_val (by omega)

theorem ret_mask (w t : Nat) (i : Fin 4) (j : Fin (5 + w)) :
    ret w t i ≠ maskSlots w t j := by
  have hr := ret_lt w t i
  have hm := mask_val w t j
  exact ne_of_val (by omega)

theorem ret_log (w t : Nat) (i : Fin 4) : ret w t i ≠ log w t := by
  have hr := ret_lt w t i
  refine ne_of_val ?_
  show (ret w t i).val ≠ 23 + w + t
  omega

theorem log_mask (w t : Nat) (j : Fin (5 + w)) : log w t ≠ maskSlots w t j := by
  have hm := mask_val w t j
  refine ne_of_val ?_
  show 23 + w + t ≠ (maskSlots w t j).val
  omega

theorem slot_ret (w t : Nat) (i : Fin 4) : slot w t 1 ≠ ret w t i := by
  have hr := ret_lt w t i
  have := slot_lt w t 1
  exact ne_of_val (by omega)

theorem slot_log (w t : Nat) : slot w t 1 ≠ log w t := by
  have := slot_lt w t 1
  refine ne_of_val ?_
  show (slot w t 1).val ≠ 23 + w + t
  omega

theorem drv_slot (w t : Nat) : retDrv w t ≠ slot w t 1 := by
  have := slot_lt w t 1
  refine ne_of_val ?_
  show 22 + w + t ≠ (slot w t 1).val
  omega

theorem drv_log (w t : Nat) : retDrv w t ≠ log w t :=
  ne_of_val (by show 22 + w + t ≠ 23 + w + t; omega)

theorem slot_rawDrv (w t : Nat) (j : Fin 13) : slot w t j ≠ rawDrv w t := by
  have := slot_lt w t j
  refine ne_of_val ?_
  show (slot w t j).val ≠ 24 + w + t
  omega

theorem slot_rawDst (w t : Nat) (j : Fin 13) : slot w t j ≠ rawDst w t := by
  have := slot_lt w t j
  refine ne_of_val ?_
  show (slot w t j).val ≠ 25 + w + t
  omega

theorem slot_rawLog (w t : Nat) (j : Fin 13) : slot w t j ≠ rawLog w t := by
  have := slot_lt w t j
  refine ne_of_val ?_
  show (slot w t j).val ≠ 26 + w + t
  omega

theorem mask_rawDrv (w t : Nat) (i : Fin (5 + w)) : maskSlots w t i ≠ rawDrv w t := by
  have := mask_val w t i
  refine ne_of_val ?_
  show (maskSlots w t i).val ≠ 24 + w + t
  omega

theorem mask_rawDst (w t : Nat) (i : Fin (5 + w)) : maskSlots w t i ≠ rawDst w t := by
  have := mask_val w t i
  refine ne_of_val ?_
  show (maskSlots w t i).val ≠ 25 + w + t
  omega

theorem mask_rawLog (w t : Nat) (i : Fin (5 + w)) : maskSlots w t i ≠ rawLog w t := by
  have := mask_val w t i
  refine ne_of_val ?_
  show (maskSlots w t i).val ≠ 26 + w + t
  omega

theorem slots_rawDrv (w t : Nat) (j : Fin t) : slots w t j ≠ rawDrv w t := by
  have := slots_val w t j
  refine ne_of_val ?_
  show (slots w t j).val ≠ 24 + w + t
  omega

theorem slots_rawDst (w t : Nat) (j : Fin t) : slots w t j ≠ rawDst w t := by
  have := slots_val w t j
  refine ne_of_val ?_
  show (slots w t j).val ≠ 25 + w + t
  omega

theorem slots_rawLog (w t : Nat) (j : Fin t) : slots w t j ≠ rawLog w t := by
  have := slots_val w t j
  refine ne_of_val ?_
  show (slots w t j).val ≠ 26 + w + t
  omega

theorem rawDrv_rawDst (w t : Nat) : rawDrv w t ≠ rawDst w t :=
  ne_of_val (by show 24 + w + t ≠ 25 + w + t; omega)

theorem rawDrv_rawLog (w t : Nat) : rawDrv w t ≠ rawLog w t :=
  ne_of_val (by show 24 + w + t ≠ 26 + w + t; omega)

theorem rawDst_rawLog (w t : Nat) : rawDst w t ≠ rawLog w t :=
  ne_of_val (by show 25 + w + t ≠ 26 + w + t; omega)

/-- The 373 cold-cache pool slots, placed above every loader slot. -/
def pool (w t : Nat) (i : Fin 373) : Fin (univ w t) :=
  ⟨27 + w + t + i.val, by
    have := i.isLt
    show 27 + w + t + i.val < 400 + w + t
    omega⟩

theorem pool_val (w t : Nat) (i : Fin 373) : (pool w t i).val = 27 + w + t + i.val := rfl

theorem pool_ge (w t : Nat) (i : Fin 373) : 27 + w + t ≤ (pool w t i).val := by
  show 27 + w + t ≤ 27 + w + t + i.val
  omega

theorem pool_injective (w t : Nat) : Function.Injective (pool w t) := by
  intro i j h
  have hv : (pool w t i).val = (pool w t j).val := congrArg Fin.val h
  rw [pool_val, pool_val] at hv
  exact Fin.ext (by omega)

theorem slot_pool (w t : Nat) (j : Fin 13) (i : Fin 373) : slot w t j ≠ pool w t i := by
  have := slot_lt w t j
  have := pool_ge w t i
  exact ne_of_val (by omega)

theorem mask_pool (w t : Nat) (j : Fin (5 + w)) (i : Fin 373) :
    maskSlots w t j ≠ pool w t i := by
  have := mask_val w t j
  have := pool_ge w t i
  exact ne_of_val (by omega)

theorem slots_pool (w t : Nat) (j : Fin t) (i : Fin 373) : slots w t j ≠ pool w t i := by
  have := slots_val w t j
  have := pool_ge w t i
  exact ne_of_val (by omega)

theorem rawDst_pool (w t : Nat) (i : Fin 373) : rawDst w t ≠ pool w t i := by
  have := pool_ge w t i
  refine ne_of_val ?_
  show 25 + w + t ≠ (pool w t i).val
  omega

/-! ### The loader on the concrete layout

`MaskReady.mask_ready` specialised to the assignment above.  All twenty-six
geometry hypotheses are discharged; what remains are only the head, bank and
capacity facts about the caller's ambient configuration. -/

/-- The physical source loader on the concrete ambient layout. -/
def layout (mask : MaskProducer) {selector : CyclicChoice.Laws}
    {a : DecompositionAlgorithm} (packet : PacketWriter selector a) :
    MaskSeedCode mask packet (univ mask.work packet.ordinary.program.tapeCount) :=
  MaskReady.code mask packet
    (maskSlots mask.work packet.ordinary.program.tapeCount)
    (mask_injective mask.work packet.ordinary.program.tapeCount)
    (slots mask.work packet.ordinary.program.tapeCount)
    (slots_injective mask.work packet.ordinary.program.tapeCount)
    (slot mask.work packet.ordinary.program.tapeCount)
    (ret mask.work packet.ordinary.program.tapeCount)
    (retDrv mask.work packet.ordinary.program.tapeCount)
    (log mask.work packet.ordinary.program.tapeCount)
    (rawDrv mask.work packet.ordinary.program.tapeCount)
    (rawDst mask.work packet.ordinary.program.tapeCount)
    (rawLog mask.work packet.ordinary.program.tapeCount)

/-- `MaskSeedCode.Ready` for the loader on the concrete layout, with no slot
geometry left as a hypothesis. -/
theorem mask_ready_at (mask : MaskProducer) {selector : CyclicChoice.Laws}
    {a : DecompositionAlgorithm} (packet : PacketWriter selector a)
    (r : Request) (cap capR capD capL : Nat) (uK um : List Bool)
    (hk : uK.length = normalizedLiveCount r.q r.liveScale)
    (hmm : um.length = (r.family a).occurrences.length)
    (cs : (r.supportWord a).length ≤ cap) (cq : 4 * r.q + 3 ≤ cap)
    (ck : 4 * uK.length + 3 ≤ cap) (cm : 4 * um.length + 3 ≤ cap)
    (cq2 : 2 * r.q + 1 ≤ cap) (cn : 2 * r.nativeWord.length + 1 ≤ cap)
    (cs2 : 2 * (r.supportWord a).length + 1 ≤ cap) (ci : 2 * (r.indexWord a).length + 1 ≤ cap)
    (ct : 2 * (r.topWord a).length + 1 ≤ cap)
    (cL : 2 * (r.raw selector a).length + 1 ≤ capL)
    (blank : Fin (5 + mask.work) → Nat)
    (blankP : Fin packet.ordinary.program.tapeCount → Nat)
    (H : Fin (univ mask.work packet.ordinary.program.tapeCount) → Nat)
    (A : Fin (univ mask.work packet.ordinary.program.tapeCount) → List Bool)
    (hHr : ∀ i, H (ret mask.work packet.ordinary.program.tapeCount i) = 0)
    (hHm : ∀ j, H (maskSlots mask.work packet.ordinary.program.tapeCount j) = 0)
    (hHl : H (log mask.work packet.ordinary.program.tapeCount) = 0)
    (hHD : H (retDrv mask.work packet.ordinary.program.tapeCount) = 0)
    (hHsl : ∀ j, H (slot mask.work packet.ordinary.program.tapeCount j) = 0)
    (hHs : ∀ j, H (slots mask.work packet.ordinary.program.tapeCount j) = 0)
    (hHrd : H (rawDrv mask.work packet.ordinary.program.tapeCount) = 0)
    (hHrt : H (rawDst mask.work packet.ordinary.program.tapeCount) = 0)
    (hHrg : H (rawLog mask.work packet.ordinary.program.tapeCount) = 0)
    (hAD : A (retDrv mask.work packet.ordinary.program.tapeCount)
      = ZeroPadding.pad cap (frame (List.replicate r.q true)))
    (hA0 : A (ret mask.work packet.ordinary.program.tapeCount 0)
      = ZeroPadding.pad cap (frame (r.supportWord a)))
    (hA1 : A (ret mask.work packet.ordinary.program.tapeCount 1)
      = ZeroPadding.pad cap (frame (List.replicate r.q true)))
    (hA2 : A (ret mask.work packet.ordinary.program.tapeCount 2)
      = ZeroPadding.pad cap (frame uK))
    (hA3 : A (ret mask.work packet.ordinary.program.tapeCount 3)
      = ZeroPadding.pad cap (frame um))
    (hLive : ∀ j : Fin (5 + mask.work), j.val < 4 →
      A (maskSlots mask.work packet.ordinary.program.tapeCount j) = [])
    (hPriv : ∀ j : Fin (5 + mask.work), 4 ≤ j.val →
      A (maskSlots mask.work packet.ordinary.program.tapeCount j)
        = List.replicate (blank j) false)
    (hAl : A (log mask.work packet.ordinary.program.tapeCount) = List.replicate cap false)
    (hAd : A (slot mask.work packet.ordinary.program.tapeCount 1) = [])
    (hAsuf : ∀ j : Fin 13, j ≠ 0 → j ≠ 1 →
      A (slot mask.work packet.ordinary.program.tapeCount j)
        = SuffixFrame.entry (MaskInput.reserve blank ⟨4, by omega⟩) 0 cap (maskData a r).word
            r.nativeWord (r.supportWord a) (r.indexWord a) (r.topWord a) j)
    (hblankP : ∀ j : Fin packet.ordinary.program.tapeCount, j.val ≠ 0 →
      A (slots mask.work packet.ordinary.program.tapeCount j) = List.replicate (blankP j) false)
    (hArd : A (rawDrv mask.work packet.ordinary.program.tapeCount)
      = ZeroPadding.pad capD (List.replicate (r.raw selector a).length true))
    (hArt : A (rawDst mask.work packet.ordinary.program.tapeCount) = List.replicate capR false)
    (hArg : A (rawLog mask.work packet.ordinary.program.tapeCount) = List.replicate capL false) :
    ∃ A' : Fin (univ mask.work packet.ordinary.program.tapeCount) → List Bool,
      (layout mask packet).Ready r (MaskReady.fuel mask packet r) H
        (dockH (slots mask.work packet.ordinary.program.tapeCount) H (fun _ => 0)) A A' ∧
      A' (rawDst mask.work packet.ordinary.program.tapeCount)
        = ZeroPadding.pad capR (frame (r.raw selector a)) :=
  MaskReady.mask_ready mask packet _ (mask_injective _ _) _ (slots_injective _ _) _
    (slot_injective _ _) _ _ _ _ _ _ r cap capR capD capL uK um hk hmm
    (mask_output _ _) (mask_off _ _) (packet_frame _ _) (slot_off _ _) (mask_packet _ _)
    (ret_mask _ _) (ret_log _ _) (log_mask _ _) (slot_ret _ _) (slot_log _ _)
    (drv_slot _ _) (drv_log _ _) (slot_rawDrv _ _) (slot_rawDst _ _) (slot_rawLog _ _)
    (mask_rawDrv _ _) (mask_rawDst _ _) (mask_rawLog _ _)
    (slots_rawDrv _ _) (slots_rawDst _ _) (slots_rawLog _ _)
    (rawDrv_rawDst _ _) (rawDrv_rawLog _ _) (rawDst_rawLog _ _)
    cs cq ck cm cq2 cn cs2 ci ct cL blank blankP H A
    hHr hHm hHl hHD hHsl hHs hHrd hHrt hHrg hAD hA0 hA1 hA2 hA3 hLive hPriv hAl hAd hAsuf
    hblankP hArd hArt hArg

end
end SLoad.Geometry
