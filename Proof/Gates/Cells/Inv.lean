import Proof.Gates.Cells.OuterP
import Proof.Gates.Cells.GatherSpec

set_option autoImplicit false
set_option linter.unusedTactic false

namespace NearCubicGates.Close.Cells

variable {V M : ℕ} {C : Ctx}

theorem OpEx.kc_le {o : Op V M} {a b : DS V M} {k : ℕ} (h : OpEx C o a b k) (ha : a.kc ≤ a.kout.length) :
    b.kc ≤ b.kout.length := by
  cases h <;> simp_all [DS.set, DS.adv, DS.put, DS.rew, DS.srt, DS.called]

theorem Ex.kc_le {s : St V M} {a b : DS V M} {n : ℕ} (h : Ex C s a b n) (ha : a.kc ≤ a.kout.length) :
    b.kc ≤ b.kout.length := by
  induction h with
  | op h => exact h.kc_le ha
  | seq _ _ ih1 ih2 => exact ih2 (ih1 ha)
  | iteT _ _ _ ih => exact ih ha
  | iteF _ _ _ ih => exact ih ha
  | loopF _ _ => exact ha
  | loopT _ _ _ _ ih1 ih2 => exact ih2 (ih1 ha)
  | mono _ _ ih => exact ih ha

theorem OpEx.rc_le {o : Op V M} {a b : DS V M} {k : ℕ} (h : OpEx C o a b k) (ha : ∀ m, a.rc m ≤ (a.ram m).length) :
    ∀ m, b.rc m ≤ (b.ram m).length := by
  intro m'
  cases h with
  | rdM m x a hr =>
    by_cases hm : m' = m
    · subst hm; simp [DS.adv, DS.set]; omega
    · simp [DS.adv, DS.set, Function.update_of_ne hm]; exact ha m'
  | wrM m x a hr =>
    by_cases hm : m' = m
    · subst hm; simp only [DS.put, Function.update_self]; rw [putAt_length _ _ _ hr]; omega
    · simp only [DS.put, Function.update_of_ne hm]; exact ha m'
  | rwM m a =>
    by_cases hm : m' = m
    · subst hm; simp [DS.rew]
    · simp [DS.rew, Function.update_of_ne hm]; exact ha m'
  | srtM m a h0 =>
    by_cases hm : m' = m
    · subst hm; simp [DS.srt, h0]
    · simp only [DS.srt, Function.update_of_ne hm]; exact ha m'
  | _ => simpa [DS.set, DS.called] using ha m'

theorem Ex.rc_le {s : St V M} {a b : DS V M} {n : ℕ} (h : Ex C s a b n) (ha : ∀ m, a.rc m ≤ (a.ram m).length) :
    ∀ m, b.rc m ≤ (b.ram m).length := by
  induction h with
  | op h => exact h.rc_le ha
  | seq _ _ ih1 ih2 => exact ih2 (ih1 ha)
  | iteT _ _ _ ih => exact ih ha
  | iteF _ _ _ ih => exact ih ha
  | loopF _ _ => exact ha
  | loopT _ _ _ _ ih1 ih2 => exact ih2 (ih1 ha)
  | mono _ _ ih => exact ih ha

theorem Hs.rc_le {s : St V M} {a : DS V M} {t : ℕ} {R : DS V M → Prop} (h : Hs C s a t R)
    (ha : ∀ m, a.rc m ≤ (a.ram m).length) (hk : a.kc ≤ a.kout.length) :
    Hs C s a t (fun b => R b ∧ (∀ m, b.rc m ≤ (b.ram m).length) ∧ b.kc ≤ b.kout.length) := by
  obtain ⟨b, n, he, hn, hb⟩ := h
  exact ⟨b, n, he, hn, hb, he.rc_le ha, he.kc_le hk⟩

end NearCubicGates.Close.Cells
