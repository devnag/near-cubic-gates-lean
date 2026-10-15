import Proof.SourceAssembly.SourceRequestFields

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace NearCubicWires.SourceRequest.FactorLoop
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open FixedLivePackets PacketProduction
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.SourceRequest NearCubicWires.SourceRequest.Fields
noncomputable section

section
variable {q : Nat} {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit}

/-- The three segments of one factor slot (`none` = absent factor). -/
def segN (mode : Bool) (o : Option (C10TotalDecode.Atom pcpp)) : List Bool := (o.map (natSeg mode)).getD []
def segS (mode : Bool) (o : Option (C10TotalDecode.Atom pcpp)) : List Bool := (o.map (supSeg mode)).getD []
def segT (a : DecompositionAlgorithm) (mode : Bool) (o : Option (C10TotalDecode.Atom pcpp)) : List Bool :=
  (o.map (topSeg a mode)).getD []

structure FactorProducer (mode : Bool) (a : DecompositionAlgorithm) (pcpp : PointwisePCPP circuit) where
  t : Nat
  s : Nat
  machine : Machine t s
  d : Nat
  descSlots : Fin d → Fin t
  descInjective : Function.Injective descSlots
  outN : Fin t
  outS : Fin t
  outT : Fin t
  hNS : outN ≠ outS
  hNT : outN ≠ outT
  hST : outS ≠ outT
  /-- the slot's descriptor bank, written by factor selection -/
  Desc : Option (C10TotalDecode.Atom pcpp) → Fin d → List Bool
  /-- admission precondition on the slot's factor -/
  Ok : Option (C10TotalDecode.Atom pcpp) → Prop
  cost : Option (C10TotalDecode.Atom pcpp) → Nat
  /-- the blank backing the producer needs -/
  need : Option (C10TotalDecode.Atom pcpp) → Nat
  run : ∀ (o : Option (C10TotalDecode.Atom pcpp)) (R : Nat), Ok o → need o ≤ R →
    ∃ A' : Fin t → List Bool,
      Step machine (cost o) (fun _ => 0)
        (install descSlots (fun _ => List.replicate R false) (fun k => ZeroPadding.pad R (Desc o k)))
        (fun _ => 0) A' ∧
      A' outN = ZeroPadding.pad R (RepairOrdinary.frame (segN mode o)) ∧
      A' outS = ZeroPadding.pad R (RepairOrdinary.frame (segS mode o)) ∧
      A' outT = ZeroPadding.pad R (RepairOrdinary.frame (segT a mode o))

theorem segN_slot (mode : Bool) (atoms : List (C10TotalDecode.Atom pcpp)) (i : Fin 4) :
    segN mode atoms[i.val]? = nSlots mode atoms i := rfl
theorem segS_slot (mode : Bool) (atoms : List (C10TotalDecode.Atom pcpp)) (i : Fin 4) :
    segS mode atoms[i.val]? = sSlots mode atoms i := rfl
theorem segT_slot (a : DecompositionAlgorithm) (mode : Bool) (atoms : List (C10TotalDecode.Atom pcpp))
    (i : Fin 4) : segT a mode atoms[i.val]? = tSlots a mode atoms i := rfl

/-! ## The composed factor loop -/

theorem mul_add_inj {t i i' a b : Nat} (ha : a < t) (hb : b < t) (h : i * t + a = i' * t + b) :
    i = i' ∧ a = b := by
  have ht : 0 < t := by omega
  have h1 : (a + i * t) / t = i := by
    rw [Nat.add_mul_div_right _ _ ht, Nat.div_eq_of_lt ha, Nat.zero_add]
  have h2 : (b + i' * t) / t = i' := by
    rw [Nat.add_mul_div_right _ _ ht, Nat.div_eq_of_lt hb, Nat.zero_add]
  have hii : i = i' := by
    rw [← h1, ← h2, Nat.add_comm a, Nat.add_comm b, h]
  subst hii
  exact ⟨rfl, by omega⟩

variable {mode : Bool} {a : DecompositionAlgorithm} (P : FactorProducer mode a pcpp)

theorem slot_lt (i : Fin 4) (j : Fin P.t) : 19 + i.val * P.t + j.val < 19 + 4 * P.t := by
  have hi := i.isLt
  have hj := j.isLt
  have h := Nat.mul_le_mul_right P.t (show i.val + 1 ≤ 4 by omega)
  rw [Nat.succ_mul] at h
  omega

/-- Slot `i`'s producer tape `j`. -/
def cslot (i : Fin 4) (j : Fin P.t) : Fin (19 + 4 * P.t) := ⟨19 + i.val * P.t + j.val, slot_lt P i j⟩

theorem cslot_inj {i i' : Fin 4} {j j' : Fin P.t} (h : cslot P i j = cslot P i' j') : i = i' ∧ j = j' := by
  have hv := congrArg Fin.val h
  simp only [cslot] at hv
  obtain ⟨h1, h2⟩ := mul_add_inj j.isLt j'.isLt (show i.val * P.t + j.val = i'.val * P.t + j'.val by omega)
  exact ⟨Fin.ext h1, Fin.ext h2⟩

theorem cslot_injective (i : Fin 4) : Function.Injective (cslot P i) :=
  fun _ _ h => (cslot_inj P h).2

theorem cslot_ne (i i' : Fin 4) (j j' : Fin P.t) (h : i ≠ i') : cslot P i j ≠ cslot P i' j' :=
  fun e => h (cslot_inj P e).1

/-- The Fields machine's tapes: header `0`, slot segments on the four producers' output tapes, pass
privates on `1..18`. -/
def fslot (j : Fin 31) : Fin (19 + 4 * P.t) :=
  if h0 : j.val = 0 then ⟨0, by omega⟩
  else if h1 : j.val < 5 then cslot P ⟨j.val - 1, by omega⟩ P.outN
  else if h2 : j.val < 9 then cslot P ⟨j.val - 5, by omega⟩ P.outS
  else if h3 : j.val < 13 then cslot P ⟨j.val - 9, by omega⟩ P.outT
  else ⟨j.val - 12, by omega⟩

theorem fslot_injective : Function.Injective (fslot P) := by
  intro x y h
  have hx := x.isLt
  have hy := y.isLt
  have hNS := P.hNS
  have hNT := P.hNT
  have hST := P.hST
  apply Fin.ext
  unfold fslot at h
  split_ifs at h <;> first
    | (have hv := congrArg Fin.val h; (try simp only [cslot] at hv); omega)
    | (obtain ⟨e1, e2⟩ := cslot_inj P h; have e3 := congrArg Fin.val e1; simp only at e3; omega)

/-- The factor loop: the per-factor producer in slots `0..3`, then the three field passes. -/
def machine :=
  Composition.machine (RecoveryFocus.machine (cslot P 0) P.machine)
    (Composition.machine (RecoveryFocus.machine (cslot P 1) P.machine)
      (Composition.machine (RecoveryFocus.machine (cslot P 2) P.machine)
        (Composition.machine (RecoveryFocus.machine (cslot P 3) P.machine)
          (RecoveryFocus.machine (fslot P) Fields.machine))))

/-- The loop's entry bank: the header on tape `0`, slot `i`'s descriptor bank in its region, blank
backing everywhere else. -/
def entry (hdr : List Bool) (D : Fin 4 → Fin P.d → List Bool) (R : Nat) :
    Fin (19 + 4 * P.t) → List Bool := fun x =>
  if x.val = 0 then ZeroPadding.pad R (RepairOrdinary.frame hdr)
  else if h : 19 ≤ x.val then
    install P.descSlots (fun _ => List.replicate R false) (fun k => ZeroPadding.pad R
      (D ⟨(x.val - 19) / P.t, by
        have := x.isLt
        have ht : 0 < P.t := by omega
        exact (Nat.div_lt_iff_lt_mul ht).mpr (by omega)⟩ k))
      ⟨(x.val - 19) % P.t, Nat.mod_lt _ (by have := x.isLt; omega)⟩
  else List.replicate R false

theorem entry_cslot (hdr : List Bool) (D : Fin 4 → Fin P.d → List Bool) (R : Nat) (i : Fin 4)
    (j : Fin P.t) :
    entry P hdr D R (cslot P i j)
      = install P.descSlots (fun _ => List.replicate R false) (fun k => ZeroPadding.pad R (D i k)) j := by
  have hj := j.isLt
  have ht : 0 < P.t := by omega
  have hdiv : (i.val * P.t + j.val) / P.t = i.val := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ ht, Nat.div_eq_of_lt hj, Nat.zero_add]
  have hmod : (i.val * P.t + j.val) % P.t = j.val := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
  have hv : (cslot P i j).val - 19 = i.val * P.t + j.val := by simp only [cslot]; omega
  have h0 : (cslot P i j).val ≠ 0 := by simp only [cslot]; omega
  have h19 : 19 ≤ (cslot P i j).val := by simp only [cslot]; omega
  unfold entry
  rw [if_neg h0, dif_pos h19]
  have e1 : (⟨((cslot P i j).val - 19) / P.t, by rw [hv, hdiv]; exact i.isLt⟩ : Fin 4) = i :=
    Fin.ext (by simp only; rw [hv, hdiv])
  have e2 : (⟨((cslot P i j).val - 19) % P.t, by rw [hv, hmod]; exact hj⟩ : Fin P.t) = j :=
    Fin.ext (by simp only; rw [hv, hmod])
  rw [e1, e2]

theorem entry_small (hdr : List Bool) (D : Fin 4 → Fin P.d → List Bool) (R : Nat)
    (x : Fin (19 + 4 * P.t)) (h0 : x.val ≠ 0) (h19 : x.val < 19) :
    entry P hdr D R x = List.replicate R false := by
  unfold entry
  rw [if_neg h0, dif_neg (by omega)]

theorem entry_zero (hdr : List Bool) (D : Fin 4 → Fin P.d → List Bool) (R : Nat) :
    entry P hdr D R ⟨0, by omega⟩ = ZeroPadding.pad R (RepairOrdinary.frame hdr) := by
  unfold entry
  rw [if_pos rfl]

theorem cslot_ge (i : Fin 4) (j : Fin P.t) : 19 ≤ (cslot P i j).val := by
  simp only [cslot]; omega

def cost (L target : Nat) (atoms : List (C10TotalDecode.Atom pcpp)) : Nat :=
  P.cost atoms[0]? + 1 + (P.cost atoms[1]? + 1 + (P.cost atoms[2]? + 1 + (P.cost atoms[3]? + 1 +
    Fields.cost (header mode q L target atoms.length) (nSlots mode atoms) (sSlots mode atoms)
      (tSlots a mode atoms))))

theorem loop_step (L target : Nat) (atoms : List (C10TotalDecode.Atom pcpp)) (four : atoms.length ≤ 4)
    (R : Nat) (hOk : ∀ i : Fin 4, P.Ok atoms[i.val]?) (hneed : ∀ i : Fin 4, P.need atoms[i.val]? ≤ R)
    (hN : 2 * (monomialRequest L target mode atoms four).nativeWord.length + 1 ≤ R)
    (hS : 2 * ((monomialRequest L target mode atoms four).supportWord a).length + 1 ≤ R)
    (hT : 2 * ((monomialRequest L target mode atoms four).topWord a).length + 1 ≤ R) :
    let r := monomialRequest L target mode atoms four
    ∃ X : Fin (19 + 4 * P.t) → List Bool,
      Step (machine P) (cost P L target atoms) (fun _ => 0)
        (entry P (header mode q L target atoms.length) (fun i => P.Desc atoms[i.val]?) R)
        (fun _ => 0) X ∧
      X (fslot P 17) = ZeroPadding.pad R (RepairOrdinary.frame r.nativeWord) ∧
      X (fslot P 13) = ZeroPadding.pad R r.nativeWord ∧
      X (fslot P 15) = ZeroPadding.pad R (List.replicate r.nativeWord.length true) ∧
      X (fslot P 23) = ZeroPadding.pad R (RepairOrdinary.frame (r.supportWord a)) ∧
      X (fslot P 19) = ZeroPadding.pad R (r.supportWord a) ∧
      X (fslot P 21) = ZeroPadding.pad R (List.replicate (r.supportWord a).length true) ∧
      X (fslot P 29) = ZeroPadding.pad R (RepairOrdinary.frame (r.topWord a)) ∧
      X (fslot P 25) = ZeroPadding.pad R (r.topWord a) ∧
      X (fslot P 27) = ZeroPadding.pad R (List.replicate (r.topWord a).length true) := by
  intro r
  classical
  set hdr := header mode q L target atoms.length with hhdr
  set E := entry P hdr (fun i => P.Desc atoms[i.val]?) R with hE
  obtain ⟨A0, r0, n0, s0, t0⟩ := P.run atoms[(0 : Fin 4).val]? R (hOk 0) (hneed 0)
  obtain ⟨A1, r1, n1, s1, t1⟩ := P.run atoms[(1 : Fin 4).val]? R (hOk 1) (hneed 1)
  obtain ⟨A2, r2, n2, s2, t2⟩ := P.run atoms[(2 : Fin 4).val]? R (hOk 2) (hneed 2)
  obtain ⟨A3, r3, n3, s3, t3⟩ := P.run atoms[(3 : Fin 4).val]? R (hOk 3) (hneed 3)
  have hz : ∀ {t : Nat} (sl : Fin t → Fin (19 + 4 * P.t)),
      dockH sl (fun _ => 0) (fun _ => 0) = fun _ => 0 :=
    fun sl => SLoad.dockH_existing sl _ _ (fun _ => rfl)
  have ne : ∀ (i i' : Fin 4), i ≠ i' → ∀ (x y : Fin P.t), cslot P i x ≠ cslot P i' y :=
    fun i i' h x y => cslot_ne P i i' x y h
  -- the four slot runs
  have st0 := r0.dock (cslot P 0) (cslot_injective P 0) (fun _ => 0) E (fun _ => rfl)
    (fun j => entry_cslot P hdr _ R 0 j)
  rw [hz] at st0
  set B1 := install (cslot P 0) E A0 with hB1
  have st1 := r1.dock (cslot P 1) (cslot_injective P 1) (fun _ => 0) B1 (fun _ => rfl)
    (fun j => by
      rw [hB1, install_other _ _ _ _ (fun k => ne 0 1 (by decide) k j)]
      exact entry_cslot P hdr _ R 1 j)
  rw [hz] at st1
  set B2 := install (cslot P 1) B1 A1 with hB2
  have st2 := r2.dock (cslot P 2) (cslot_injective P 2) (fun _ => 0) B2 (fun _ => rfl)
    (fun j => by
      rw [hB2, install_other _ _ _ _ (fun k => ne 1 2 (by decide) k j), hB1,
        install_other _ _ _ _ (fun k => ne 0 2 (by decide) k j)]
      exact entry_cslot P hdr _ R 2 j)
  rw [hz] at st2
  set B3 := install (cslot P 2) B2 A2 with hB3
  have st3 := r3.dock (cslot P 3) (cslot_injective P 3) (fun _ => 0) B3 (fun _ => rfl)
    (fun j => by
      rw [hB3, install_other _ _ _ _ (fun k => ne 2 3 (by decide) k j), hB2,
        install_other _ _ _ _ (fun k => ne 1 3 (by decide) k j), hB1,
        install_other _ _ _ _ (fun k => ne 0 3 (by decide) k j)]
      exact entry_cslot P hdr _ R 3 j)
  rw [hz] at st3
  set B4 := install (cslot P 3) B3 A3 with hB4
  -- the bank after the four runs
  have hB4low : ∀ x : Fin (19 + 4 * P.t), x.val < 19 → B4 x = E x := by
    intro x hx
    have off : ∀ (i : Fin 4) (k : Fin P.t), cslot P i k ≠ x := fun i k e => by
      have := cslot_ge P i k; rw [e] at this; omega
    rw [hB4, install_other _ _ _ _ (off 3), hB3, install_other _ _ _ _ (off 2), hB2,
      install_other _ _ _ _ (off 1), hB1, install_other _ _ _ _ (off 0)]
  have hB4N : ∀ i : Fin 4, B4 (cslot P i P.outN)
      = ZeroPadding.pad R (RepairOrdinary.frame (nSlots mode atoms i)) := by
    have e0 : B4 (cslot P 0 P.outN) = ZeroPadding.pad R (RepairOrdinary.frame (nSlots mode atoms 0)) := by
      rw [hB4, install_other _ _ _ _ (fun k => ne 3 0 (by decide) k _), hB3,
        install_other _ _ _ _ (fun k => ne 2 0 (by decide) k _), hB2,
        install_other _ _ _ _ (fun k => ne 1 0 (by decide) k _), hB1,
        install_slot _ (cslot_injective P 0)]
      exact n0
    have e1 : B4 (cslot P 1 P.outN) = ZeroPadding.pad R (RepairOrdinary.frame (nSlots mode atoms 1)) := by
      rw [hB4, install_other _ _ _ _ (fun k => ne 3 1 (by decide) k _), hB3,
        install_other _ _ _ _ (fun k => ne 2 1 (by decide) k _), hB2,
        install_slot _ (cslot_injective P 1)]
      exact n1
    have e2 : B4 (cslot P 2 P.outN) = ZeroPadding.pad R (RepairOrdinary.frame (nSlots mode atoms 2)) := by
      rw [hB4, install_other _ _ _ _ (fun k => ne 3 2 (by decide) k _), hB3,
        install_slot _ (cslot_injective P 2)]
      exact n2
    have e3 : B4 (cslot P 3 P.outN) = ZeroPadding.pad R (RepairOrdinary.frame (nSlots mode atoms 3)) := by
      rw [hB4, install_slot _ (cslot_injective P 3)]
      exact n3
    intro i
    match i with
    | ⟨0, _⟩ => exact e0
    | ⟨1, _⟩ => exact e1
    | ⟨2, _⟩ => exact e2
    | ⟨3, _⟩ => exact e3
  have hB4S : ∀ i : Fin 4, B4 (cslot P i P.outS)
      = ZeroPadding.pad R (RepairOrdinary.frame (sSlots mode atoms i)) := by
    have e0 : B4 (cslot P 0 P.outS) = ZeroPadding.pad R (RepairOrdinary.frame (sSlots mode atoms 0)) := by
      rw [hB4, install_other _ _ _ _ (fun k => ne 3 0 (by decide) k _), hB3,
        install_other _ _ _ _ (fun k => ne 2 0 (by decide) k _), hB2,
        install_other _ _ _ _ (fun k => ne 1 0 (by decide) k _), hB1,
        install_slot _ (cslot_injective P 0)]
      exact s0
    have e1 : B4 (cslot P 1 P.outS) = ZeroPadding.pad R (RepairOrdinary.frame (sSlots mode atoms 1)) := by
      rw [hB4, install_other _ _ _ _ (fun k => ne 3 1 (by decide) k _), hB3,
        install_other _ _ _ _ (fun k => ne 2 1 (by decide) k _), hB2,
        install_slot _ (cslot_injective P 1)]
      exact s1
    have e2 : B4 (cslot P 2 P.outS) = ZeroPadding.pad R (RepairOrdinary.frame (sSlots mode atoms 2)) := by
      rw [hB4, install_other _ _ _ _ (fun k => ne 3 2 (by decide) k _), hB3,
        install_slot _ (cslot_injective P 2)]
      exact s2
    have e3 : B4 (cslot P 3 P.outS) = ZeroPadding.pad R (RepairOrdinary.frame (sSlots mode atoms 3)) := by
      rw [hB4, install_slot _ (cslot_injective P 3)]
      exact s3
    intro i
    match i with
    | ⟨0, _⟩ => exact e0
    | ⟨1, _⟩ => exact e1
    | ⟨2, _⟩ => exact e2
    | ⟨3, _⟩ => exact e3
  have hB4T : ∀ i : Fin 4, B4 (cslot P i P.outT)
      = ZeroPadding.pad R (RepairOrdinary.frame (tSlots a mode atoms i)) := by
    have e0 : B4 (cslot P 0 P.outT) = ZeroPadding.pad R (RepairOrdinary.frame (tSlots a mode atoms 0)) := by
      rw [hB4, install_other _ _ _ _ (fun k => ne 3 0 (by decide) k _), hB3,
        install_other _ _ _ _ (fun k => ne 2 0 (by decide) k _), hB2,
        install_other _ _ _ _ (fun k => ne 1 0 (by decide) k _), hB1,
        install_slot _ (cslot_injective P 0)]
      exact t0
    have e1 : B4 (cslot P 1 P.outT) = ZeroPadding.pad R (RepairOrdinary.frame (tSlots a mode atoms 1)) := by
      rw [hB4, install_other _ _ _ _ (fun k => ne 3 1 (by decide) k _), hB3,
        install_other _ _ _ _ (fun k => ne 2 1 (by decide) k _), hB2,
        install_slot _ (cslot_injective P 1)]
      exact t1
    have e2 : B4 (cslot P 2 P.outT) = ZeroPadding.pad R (RepairOrdinary.frame (tSlots a mode atoms 2)) := by
      rw [hB4, install_other _ _ _ _ (fun k => ne 3 2 (by decide) k _), hB3,
        install_slot _ (cslot_injective P 2)]
      exact t2
    have e3 : B4 (cslot P 3 P.outT) = ZeroPadding.pad R (RepairOrdinary.frame (tSlots a mode atoms 3)) := by
      rw [hB4, install_slot _ (cslot_injective P 3)]
      exact t3
    intro i
    match i with
    | ⟨0, _⟩ => exact e0
    | ⟨1, _⟩ => exact e1
    | ⟨2, _⟩ => exact e2
    | ⟨3, _⟩ => exact e3
  -- the three passes
  obtain ⟨Xf, sf, f1, f2, f3, f4, f5, f6, f7, f8, f9⟩ :=
    request_fields a L target mode atoms four R hN hS hT
  have hfe : ∀ j : Fin 31, B4 (fslot P j)
      = Fields.entry hdr (nSlots mode atoms) (sSlots mode atoms) (tSlots a mode atoms) R j := by
    intro j
    have hj := j.isLt
    by_cases h0 : j.val = 0
    · have e : fslot P j = ⟨0, by omega⟩ := by simp only [fslot, dif_pos h0]
      rw [e, hB4low _ (by show 0 < 19; omega), hE, entry_zero]
      simp only [Fields.entry, if_pos h0]
    by_cases h1 : j.val < 5
    · have e : fslot P j = cslot P ⟨j.val - 1, by omega⟩ P.outN := by
        simp only [fslot, dif_neg h0, dif_pos h1]
      rw [e, hB4N]
      simp only [Fields.entry, if_neg h0, dif_pos h1]
    by_cases h2 : j.val < 9
    · have e : fslot P j = cslot P ⟨j.val - 5, by omega⟩ P.outS := by
        simp only [fslot, dif_neg h0, dif_neg h1, dif_pos h2]
      rw [e, hB4S]
      simp only [Fields.entry, if_neg h0, dif_neg h1, dif_pos h2]
    by_cases h3 : j.val < 13
    · have e : fslot P j = cslot P ⟨j.val - 9, by omega⟩ P.outT := by
        simp only [fslot, dif_neg h0, dif_neg h1, dif_neg h2, dif_pos h3]
      rw [e, hB4T]
      simp only [Fields.entry, if_neg h0, dif_neg h1, dif_neg h2, dif_pos h3]
    · have e : fslot P j = ⟨j.val - 12, by omega⟩ := by
        simp only [fslot, dif_neg h0, dif_neg h1, dif_neg h2, dif_neg h3]
      rw [e, hB4low _ (by show j.val - 12 < 19; omega), hE,
        entry_small P _ _ R _ (by show j.val - 12 ≠ 0; omega) (by show j.val - 12 < 19; omega)]
      simp only [Fields.entry, if_neg h0, dif_neg h1, dif_neg h2, dif_neg h3]
  have stf := sf.dock (fslot P) (fslot_injective P) (fun _ => 0) B4 (fun _ => rfl) hfe
  rw [hz] at stf
  have hfin : ∀ j, install (fslot P) B4 Xf (fslot P j) = Xf j :=
    fun j => install_slot _ (fslot_injective P) _ _ j
  refine ⟨install (fslot P) B4 Xf, st0.seq (st1.seq (st2.seq (st3.seq stf))), ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩ <;> rw [hfin]
  · exact f1
  · exact f2
  · exact f3
  · exact f4
  · exact f5
  · exact f6
  · exact f7
  · exact f8
  · exact f9

/-- The site's monomial list. -/
abbrev monomials (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
      ComponentwisePolynomial.CircuitPolynomial (C10TotalDecode.Atom pcpp) 1)
    (ph : CloseoutRowsOriginalSchedule.Phase) (ci : Fin (2 ^ pcpp.clauseBits)) :=
  (CloseoutFinalC10SupplierCalls.siteCalls ph pcpp coordinate C10TotalDecode.Atom.systematic ci).monomials

def factorsAt (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
      ComponentwisePolynomial.CircuitPolynomial (C10TotalDecode.Atom pcpp) 1)
    (ph : CloseoutRowsOriginalSchedule.Phase) (ci : Fin (2 ^ pcpp.clauseBits)) (m : Nat) :
    List (C10TotalDecode.Atom pcpp) :=
  match (monomials coordinate ph ci)[m]? with
  | some mo => mo.factors
  | none => []

theorem factorsAt_le (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
      ComponentwisePolynomial.CircuitPolynomial (C10TotalDecode.Atom pcpp) 1)
    (ph : CloseoutRowsOriginalSchedule.Phase) (ci : Fin (2 ^ pcpp.clauseBits)) (m : Nat) :
    (factorsAt coordinate ph ci m).length ≤ 4 := by
  unfold factorsAt
  split
  · rename_i mo _
    exact mo.degree_le
  · exact Nat.zero_le 4

theorem factorsAt_of_lt (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
      ComponentwisePolynomial.CircuitPolynomial (C10TotalDecode.Atom pcpp) 1)
    (ph : CloseoutRowsOriginalSchedule.Phase) (ci : Fin (2 ^ pcpp.clauseBits)) (m : Nat)
    (hm : m < (monomials coordinate ph ci).length) :
    factorsAt coordinate ph ci m = ((monomials coordinate ph ci)[m]).factors := by
  unfold factorsAt
  rw [List.getElem?_eq_getElem hm]

theorem factorsAt_end (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
      ComponentwisePolynomial.CircuitPolynomial (C10TotalDecode.Atom pcpp) 1)
    (ph : CloseoutRowsOriginalSchedule.Phase) (ci : Fin (2 ^ pcpp.clauseBits)) :
    factorsAt coordinate ph ci (monomials coordinate ph ci).length = [] := by
  unfold factorsAt
  rw [List.getElem?_eq_none (Nat.le_refl _)]

structure FactorSelection {U : Nat} (P : FactorProducer mode a pcpp)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
      ComponentwisePolynomial.CircuitPolynomial (C10TotalDecode.Atom pcpp) 1)
    (ph : CloseoutRowsOriginalSchedule.Phase) (ci : Fin (2 ^ pcpp.clauseBits))
    (L target R b qCap : Nat) (reg : Fin (19 + 4 * P.t) → Fin U) (qTape nT : Fin U)
    (coefT : Fin 3 → Fin U) (Scr : Fin U → Prop)
    (Src : Nat → (Fin U → Nat) → (Fin U → List Bool) → Prop) where
  states : Nat
  machine : Machine U states
  cost : Nat → Nat
  select : ∀ (m : Nat), m ≤ (monomials coordinate ph ci).length →
    ∀ (H : Fin U → Nat) (A : Fin U → List Bool), Src m H A →
    H qTape = 0 →
    A qTape = ZeroPadding.pad qCap (natListWord
      [RepairRepresentation.literalIndex (pcpp.clauses ci).left,
       RepairRepresentation.literalIndex (pcpp.clauses ci).right]) →
    ∃ (H' : Fin U → Nat) (A' : Fin U → List Bool),
      Step machine (cost m) H A H' A' ∧
      H' nT = 0 ∧
      A' nT = ZeroPadding.pad R (RepairSource.VerifierDecoding.CompareMachine.word
        (monomials coordinate ph ci).length) ∧
      (∀ x, (∀ i, reg i ≠ x) → x ≠ nT → (∀ i, coefT i ≠ x) → ¬ Scr x →
        A' x = A x ∧ H' x = H x) ∧
      (∀ i, H' (reg i) = 0) ∧
      (∀ i, A' (reg i) = entry P
        (header mode q L target (factorsAt coordinate ph ci m).length)
        (fun k => P.Desc (factorsAt coordinate ph ci m)[k.val]?) R i) ∧
      (∀ hm : m < (monomials coordinate ph ci).length,
        (∀ i, H' (coefT i) = 0) ∧
        (∀ i : Fin 3, A' (coefT i) = ZeroPadding.pad R (RepairOrdinary.frame
          (CloseoutRowsEstimatorCoefficients.Stream.recordFields b
            (CloseoutFinalC10SupplierCalls.coefficientEstimate ((monomials coordinate ph ci)[m]).coefficient)
            0 0 ⟨i.val, by omega⟩))))

/-- **Selection then the factor loop**: at cursor `m ≤ N`, the framed request fields of
`monomialRequest L target mode (factorsAt m)` (monomial `m`'s factors, or none at `m = N`) land on the
loop region's tapes `reg (fslot 17 / 23 / 29)` (bare native on `13`, its unary length on `15`),
loop-region heads `0`. -/
theorem select_then_loop {U : Nat} (P : FactorProducer mode a pcpp)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
      ComponentwisePolynomial.CircuitPolynomial (C10TotalDecode.Atom pcpp) 1)
    (ph : CloseoutRowsOriginalSchedule.Phase) (ci : Fin (2 ^ pcpp.clauseBits))
    (L target R b qCap : Nat) (reg : Fin (19 + 4 * P.t) → Fin U) (hreg : Function.Injective reg)
    (qTape nT : Fin U) (coefT : Fin 3 → Fin U) (Scr : Fin U → Prop)
    (Src : Nat → (Fin U → Nat) → (Fin U → List Bool) → Prop)
    (S : FactorSelection P coordinate ph ci L target R b qCap reg qTape nT coefT Scr Src)
    (m : Nat) (hm : m ≤ (monomials coordinate ph ci).length)
    (H : Fin U → Nat) (A : Fin U → List Bool) (hsrc : Src m H A) (hqH : H qTape = 0)
    (hq : A qTape = ZeroPadding.pad qCap (natListWord
      [RepairRepresentation.literalIndex (pcpp.clauses ci).left,
       RepairRepresentation.literalIndex (pcpp.clauses ci).right])) :
    let fs := factorsAt coordinate ph ci m
    let r := monomialRequest L target mode fs (factorsAt_le coordinate ph ci m)
    (∀ i : Fin 4, P.Ok fs[i.val]?) → (∀ i : Fin 4, P.need fs[i.val]? ≤ R) →
    2 * r.nativeWord.length + 1 ≤ R → 2 * (r.supportWord a).length + 1 ≤ R →
    2 * (r.topWord a).length + 1 ≤ R →
    ∃ (H' : Fin U → Nat) (A' : Fin U → List Bool),
      Step (Composition.machine S.machine (RecoveryFocus.machine reg (machine P)))
        (S.cost m + 1 + cost P L target fs) H A H' A' ∧
      A' (reg (fslot P 17)) = ZeroPadding.pad R (RepairOrdinary.frame r.nativeWord) ∧
      A' (reg (fslot P 23)) = ZeroPadding.pad R (RepairOrdinary.frame (r.supportWord a)) ∧
      A' (reg (fslot P 29)) = ZeroPadding.pad R (RepairOrdinary.frame (r.topWord a)) ∧
      A' (reg (fslot P 13)) = ZeroPadding.pad R r.nativeWord ∧
      A' (reg (fslot P 15)) = ZeroPadding.pad R (List.replicate r.nativeWord.length true) ∧
      (∀ i, H' (reg i) = 0) := by
  intro fs r hOk hneed hN hS hT
  obtain ⟨H1, A1, s1, _, _, _, hH1, hA1, _⟩ := S.select m hm H A hsrc hqH hq
  obtain ⟨X, sx, x1, x2, x3, x4, x5, x6, x7, _, _⟩ :=
    loop_step P L target fs (factorsAt_le coordinate ph ci m) R hOk hneed hN hS hT
  have d := sx.dock reg hreg H1 A1 (fun i => hH1 i) (fun i => hA1 i)
  refine ⟨_, _, s1.seq d, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [install_slot reg hreg]; exact x1
  · rw [install_slot reg hreg]; exact x4
  · rw [install_slot reg hreg]; exact x7
  · rw [install_slot reg hreg]; exact x2
  · rw [install_slot reg hreg]; exact x3
  · intro i; rw [dockH_slot reg hreg]

end

end
end NearCubicWires.SourceRequest.FactorLoop
