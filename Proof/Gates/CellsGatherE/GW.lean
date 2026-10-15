import Proof.Gates.CellsGather.EmitSpec
import Proof.Gates.CellsSys.Kit

set_option autoImplicit false

namespace NearCubicGates.Close.Cells.RecordEmission

open NearCubicWires NearCubicGates NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Counter

/-- `sG` = the records written so far over the stale content. -/
def GW (d : DS VV MM) (S W : List ℕ) : Prop := d.ram sG = W ++ S.drop W.length ∧ d.rc sG = W.length

theorem putAt_GW (S W : List ℕ) (v : ℕ) :
    putAt (W ++ S.drop W.length) W.length v = (W ++ [v]) ++ S.drop (W ++ [v]).length := by
  unfold putAt
  rw [List.length_append, List.length_drop]
  split_ifs with h
  · have hS : W.length < S.length := by omega
    rw [List.set_append_right _ _ (le_refl _), Nat.sub_self]
    rw [List.drop_eq_getElem_cons hS, List.set_cons_zero, List.length_append, List.length_singleton]
    simp
  · have hS : S.length ≤ W.length := by omega
    rw [List.drop_eq_nil_of_le hS, List.drop_eq_nil_of_le (by simp; omega)]
    simp

theorem GW.put {d : DS VV MM} {S W : List ℕ} (h : GW d S W) (x : Fin VV) :
    GW (d.put sG (d.env x)) S (W ++ [d.env x]) := by
  refine ⟨?_, ?_⟩
  · simp only [DS.put, Function.update_self]; rw [h.1, h.2]; exact putAt_GW S W _
  · simp only [DS.put, Function.update_self]; rw [h.2]; simp

theorem GW.final {d : DS VV MM} {S W : List ℕ} (h : GW d S W) (hl : S.length ≤ W.length) : d.ram sG = W := by
  rw [h.1, List.drop_eq_nil_of_le hl, List.append_nil]

theorem GW.len_le {d : DS VV MM} {S W : List ℕ} (h : GW d S W) : d.rc sG ≤ (d.ram sG).length := by
  rw [h.1, h.2]; simp

theorem GW.congr {d d' : DS VV MM} {S W : List ℕ} (h : GW d S W) (h1 : d'.ram sG = d.ram sG)
    (h2 : d'.rc sG = d.rc sG) : GW d' S W := by
  unfold GW at *; rw [h1, h2]; exact h

theorem GW.put' {d d' : DS VV MM} {S W : List ℕ} (h : GW d' S W) (x : Fin VV) {v : ℕ}
    (h1 : d.ram sG = d'.ram sG) (h2 : d.rc sG = d'.rc sG) (hv : d.env x = v) :
    GW (d.put sG (d.env x)) S (W ++ [v]) := by
  rw [← hv]; exact GW.put (GW.congr h h1 h2) x

/-! ## Frames under cursor moves and writes -/

@[simp] theorem adv_env (d : DS VV MM) (m : Fin MM) : (d.adv m).env = d.env := rfl
@[simp] theorem put_env (d : DS VV MM) (m : Fin MM) (v : ℕ) : (d.put m v).env = d.env := rfl
@[simp] theorem adv_ram (d : DS VV MM) (m : Fin MM) : (d.adv m).ram = d.ram := rfl
@[simp] theorem rew_env (d : DS VV MM) (m : Fin MM) : (d.rew m).env = d.env := rfl
@[simp] theorem rew_ram (d : DS VV MM) (m : Fin MM) : (d.rew m).ram = d.ram := rfl

theorem Fr.adv_r {a b : DS VV MM} {T : List (Fin VV)} (h : Fr a b T) (m : Fin MM) : Fr a (b.adv m) T := h
theorem Fr.put_r {a b : DS VV MM} {T : List (Fin VV)} (h : Fr a b T) (m : Fin MM) (v : ℕ) : Fr a (b.put m v) T := h
theorem Fr.set_r {a b : DS VV MM} {T : List (Fin VV)} (h : Fr a b T) {x : Fin VV} (v : ℕ) (hx : x ∈ T) :
    Fr a (b.set x v) T := Fr.trans h (Fr.set b v hx)

/-- The parts of the state the emission keeps (besides `sG`'s contents, the cursors and the variables). -/
structure Ke (a d : DS VV MM) : Prop where
  ram : ∀ m, m ≠ sG → d.ram m = a.ram m
  ip : d.ip = a.ip
  out : d.out = a.out
  kin : d.kin = a.kin
  kout : d.kout = a.kout
  kc : d.kc = a.kc

theorem Ke.refl (a : DS VV MM) : Ke a a := ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩
theorem Ke.trans {a b d : DS VV MM} (h1 : Ke a b) (h2 : Ke b d) : Ke a d :=
  ⟨fun m hm => (h2.ram m hm).trans (h1.ram m hm), h2.ip.trans h1.ip, h2.out.trans h1.out, h2.kin.trans h1.kin,
    h2.kout.trans h1.kout, h2.kc.trans h1.kc⟩
theorem Ke.set_r {a b : DS VV MM} (h : Ke a b) (x : Fin VV) (v : ℕ) : Ke a (b.set x v) :=
  ⟨h.ram, h.ip, h.out, h.kin, h.kout, h.kc⟩
theorem Ke.adv_r {a b : DS VV MM} (h : Ke a b) (m : Fin MM) : Ke a (b.adv m) :=
  ⟨h.ram, h.ip, h.out, h.kin, h.kout, h.kc⟩
theorem Ke.rew_r {a b : DS VV MM} (h : Ke a b) (m : Fin MM) : Ke a (b.rew m) :=
  ⟨h.ram, h.ip, h.out, h.kin, h.kout, h.kc⟩
theorem Ke.put_r {a b : DS VV MM} (h : Ke a b) (v : ℕ) : Ke a (b.put sG v) :=
  ⟨fun m hm => by simp only [DS.put, Function.update_of_ne hm]; exact h.ram m hm, h.ip, h.out, h.kin, h.kout, h.kc⟩

end NearCubicGates.Close.Cells.RecordEmission
