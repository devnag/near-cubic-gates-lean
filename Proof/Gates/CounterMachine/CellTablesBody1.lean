import Proof.Gates.CounterMachine.CellTablesBodySpec

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.CounterMachine.CellTablesProg

open NearCubicWires NearCubicGates NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Counter NearCubicGates.Close.CounterMachine
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Cells.PrefixLoader (sN)

/-! ## Body scratch variables (all `BodyVar`) -/

def bKey : Fin VV := ⟨100, by decide⟩
def bPw : Fin VV := ⟨101, by decide⟩
def bQu : Fin VV := ⟨102, by decide⟩
def bJk : Fin VV := ⟨103, by decide⟩
def bDig : Fin VV := ⟨104, by decide⟩
def bI : Fin VV := ⟨105, by decide⟩
def bE : Fin VV := ⟨106, by decide⟩
def bTmp : Fin VV := ⟨107, by decide⟩

/-- The non-variable part, but `kin`. -/
structure SameN (a b : DS VV MM) : Prop where
  ip : b.ip = a.ip
  out : b.out = a.out
  ram : b.ram = a.ram
  rc : b.rc = a.rc
  kout : b.kout = a.kout
  kc : b.kc = a.kc

theorem SameN.refl (a : DS VV MM) : SameN a a := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
theorem SameN.trans {a b d : DS VV MM} (h1 : SameN a b) (h2 : SameN b d) : SameN a d :=
  ⟨h2.ip.trans h1.ip, h2.out.trans h1.out, h2.ram.trans h1.ram, h2.rc.trans h1.rc, h2.kout.trans h1.kout,
    h2.kc.trans h1.kc⟩
theorem SameN.set (a : DS VV MM) (x : Fin VV) (v : ℕ) : SameN a (a.set x v) := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem natBitLength_le_of_lt (v W : ℕ) (hW : 1 ≤ W) (h : v < 2 ^ W) : natBitLength v ≤ W := by
  unfold natBitLength
  rcases Nat.eq_zero_or_pos v with h0 | h0
  · subst h0; simp; omega
  · have := Nat.log_lt_of_lt_pow (by omega) h
    omega

theorem add_two_lt_pow (m : ℕ) (hm : 3 ≤ m) : m + 2 < 2 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih => rw [pow_succ]; omega

theorem nbl_fit (C : Ctx) (v : ℕ) (hv : v < 2 ^ C.Wd) (hW : 3 ≤ C.Wd) : natBitLength v + 2 < 2 ^ C.Wd := by
  have h1 := natBitLength_le_of_lt v C.Wd (by omega) hv
  have h2 := add_two_lt_pow C.Wd hW
  omega

/-! ## One natural -/

def emV (x : Fin VV) : St VV MM := .seq (.op (.copy t3 x)) emitNatK

def emT : List (Fin VV) := [t3, t5, t6, t7, t8, t9]

theorem emV_spec (C : Ctx) (x : Fin VV) (hx : x ≠ t3) (a : DS VV MM) (hc : Cst a) (hW : 3 ≤ C.Wd) (v : ℕ)
    (hv : a.env x = v) (hvW : v < 2 ^ C.Wd) (hk : a.kin.length + (natWord v).length ≤ C.Lk) :
    Hs C (emV x) a (40 * natBitLength v + 42) (fun e => e.kin = a.kin ++ natWord v ∧ SameN a e ∧ Cst e ∧
      Fr a e emT) := by
  unfold emV
  refine Hs.mono (Hs.seq (t1 := 1) (t2 := 40 * natBitLength v + 40) (hs_copy C t3 x a (Ne.symm hx)) (fun b hb => ?_))
    (by omega) (fun _ h => h)
  subst hb
  have hb3 : (a.set t3 (a.env x)).env t3 = v := by simp [hv]
  have hc' : Cst (a.set t3 (a.env x)) :=
    ⟨by rw [DS.set_env_ne _ _ (by decide)]; exact hc.z, by rw [DS.set_env_ne _ _ (by decide)]; exact hc.one,
      by rw [DS.set_env_ne _ _ (by decide)]; exact hc.two⟩
  have := emitNatK_spec (C := C) (a.set t3 (a.env x)) hc' (by omega) (by rw [hb3]; exact nbl_fit C v hvW hW)
    (by rw [hb3]; simpa using hk)
  rw [hb3] at this
  refine Hs.mono this le_rfl ?_
  rintro e ⟨e1, e2, e3, e4⟩
  simp only [Prod.mk.injEq] at e2
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := e2
  exact ⟨by rw [e1]; rfl, ⟨g1, g2, g3, g4, g5, g6⟩, e3, Fr.trans (Fr.set a _ (by decide)) (Fr.weaken e4 (by decide))⟩

/-! ## The loaded naturals -/

def emCell : St VV MM := .seq (.op (.rwM sN)) (forS bE wN (.seq (.op (.rdM sN t3)) emitNatK))

def emCellT : List (Fin VV) := [bE, t3, t5, t6, t7, t8, t9]

theorem emCell_spec (C : Ctx) (a : DS VV MM) (hc : Cst a) (hW : 3 ≤ C.Wd) (L : List ℕ) (Λ : ℕ)
    (hN : a.ram sN = L) (hwN : a.env wN = L.length) (hLW : L.length < 2 ^ C.Wd)
    (hfit : ∀ v ∈ L, v < 2 ^ C.Wd) (hΛ : ∀ v ∈ L, natBitLength v ≤ Λ)
    (hk : a.kin.length + (L.flatMap natWord).length ≤ C.Lk) :
    Hs C emCell a (a.rc sN + L.length * (40 * Λ + 42 + 4) + 7) (fun e => e.kin = a.kin ++ L.flatMap natWord ∧
      e.rc = Function.update a.rc sN L.length ∧ e.ip = a.ip ∧ e.out = a.out ∧ e.ram = a.ram ∧ e.kout = a.kout ∧
      e.kc = a.kc ∧ Cst e ∧ Fr a e emCellT) := by
  refine Hs.mono (Hs.seq (t1 := a.rc sN + 1) (t2 := L.length * ((40 * Λ + 42) + 4) + 4) (hs_rwM C sN a)
    (fun b hb => ?_)) (by omega) (fun _ h => h)
  subst hb
  let I : ℕ → DS VV MM → Prop := fun k e => e.kin = a.kin ++ (L.take k).flatMap natWord ∧
    e.rc = Function.update a.rc sN k ∧ e.ip = a.ip ∧ e.out = a.out ∧ e.ram = a.ram ∧ e.kout = a.kout ∧
    e.kc = a.kc ∧ Cst e ∧ Fr a e emCellT
  refine Hs.mono (forS_spec' (C := C) bE wN (by decide) _ (a.rew sN) L.length hLW I (40 * Λ + 42)
    (fun k e v ⟨i1, i2, i3, i4, i5, i6, i7, i8, i9⟩ => ⟨i1, i2, i3, i4, i5, i6, i7,
      ⟨by rw [DS.set_env_ne _ _ (by decide)]; exact i8.z, by rw [DS.set_env_ne _ _ (by decide)]; exact i8.one,
        by rw [DS.set_env_ne _ _ (by decide)]; exact i8.two⟩, Fr.trans i9 (Fr.set e v (by decide))⟩)
    ⟨by simp [DS.rew], by simp [DS.rew], rfl, rfl, rfl, rfl, rfl, by
      exact ⟨by simp [DS.rew, hc.z], by simp [DS.rew, hc.one], by simp [DS.rew, hc.two]⟩, fun _ _ => rfl⟩
    (by simp [DS.rew, hwN]) ?_) le_rfl ?_
  · intro k hk e ⟨i1, i2, i3, i4, i5, i6, i7, i8, i9⟩ hek hem
    have hrd : e.rc sN < (e.ram sN).length := by rw [i2, i5, hN]; simp; exact hk
    have hmem : L[k] ∈ L := List.getElem_mem hk
    refine Hs.mono (Hs.seq (t1 := 1) (t2 := 40 * natBitLength L[k] + 40) (hs_rdM C sN t3 e hrd) (fun f hf => ?_))
      (by have := hΛ _ hmem; omega) (fun _ h => h)
    subst hf
    have hv : ((e.set t3 ((e.ram sN).getD (e.rc sN) 0)).adv sN).env t3 = L[k] := by
      simp [DS.adv, i2, i5, hN, List.getElem?_eq_getElem hk]
    have hfc : Cst ((e.set t3 ((e.ram sN).getD (e.rc sN) 0)).adv sN) :=
      ⟨by simp [DS.adv, DS.set, Function.update_of_ne (show vZ ≠ t3 by decide), i8.z],
        by simp [DS.adv, DS.set, Function.update_of_ne (show v1 ≠ t3 by decide), i8.one],
        by simp [DS.adv, DS.set, Function.update_of_ne (show v2 ≠ t3 by decide), i8.two]⟩
    have hkin : ((e.set t3 ((e.ram sN).getD (e.rc sN) 0)).adv sN).kin.length + (natWord L[k]).length ≤ C.Lk := by
      have h1 : (L.take (k + 1)).flatMap natWord = (L.take k).flatMap natWord ++ natWord L[k] := by
        rw [List.take_add_one, List.flatMap_append]; simp [List.getElem?_eq_getElem hk]
      have h2 : ((L.take (k + 1)).flatMap natWord).length ≤ (L.flatMap natWord).length := by
        have := congrArg (fun l => (l.flatMap natWord).length) (List.take_append_drop (k + 1) L)
        simp only [List.flatMap_append, List.length_append] at this; omega
      simp only [DS.adv, DS.set, i1, List.length_append]
      rw [h1, List.length_append] at h2; omega
    have := emitNatK_spec (C := C) _ hfc (by omega) (by rw [hv]; exact nbl_fit C _ (hfit _ hmem) hW)
      (by rw [hv]; exact hkin)
    rw [hv] at this
    refine Hs.mono this le_rfl ?_
    rintro g ⟨g1, g2, g3, g4⟩
    simp only [Prod.mk.injEq] at g2
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := g2
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, g3, ?_⟩, ?_, ?_⟩
    · rw [g1]; simp only [DS.adv, DS.set, i1, List.take_add_one, List.flatMap_append, List.append_assoc]
      simp [List.getElem?_eq_getElem hk]
    · rw [h4]; simp [DS.adv, i2]
    · rw [h1]; simp [DS.adv, i3]
    · rw [h2]; simp [DS.adv, i4]
    · rw [h3]; simp [DS.adv, i5]
    · rw [h5]; simp [DS.adv, i6]
    · rw [h6]; simp [DS.adv, i7]
    · refine Fr.trans i9 (Fr.trans (fun y hy => ?_) (Fr.weaken g4 (by decide)))
      simp only [DS.adv, DS.set]
      rw [Function.update_of_ne (fun h => hy (by rw [h]; decide))]
    · rw [g4 bE (by decide)]; simp [DS.adv, DS.set, Function.update_of_ne (show bE ≠ t3 by decide), hek]
    · rw [g4 wN (by decide)]; simp [DS.adv, DS.set, Function.update_of_ne (show wN ≠ t3 by decide), hem]
  · rintro e ⟨⟨i1, i2, i3, i4, i5, i6, i7, i8, i9⟩, _, _⟩
    refine ⟨by rw [i1, List.take_of_length_le le_rfl], ?_, i3, i4, i5, i6, i7, i8, i9⟩
    rw [i2]

end NearCubicGates.Close.CounterMachine.CellTablesProg
