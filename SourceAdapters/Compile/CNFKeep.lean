import SourceAdapters.Compile.CNFParse
import SourceAdapters.Compile.CNFGenF

/-!
# What a cell program leaves untouched

Support for composing the printer's phases (proof of `lem:multitape-refuter`, the whole query is written by one program): a register
the program never writes, a store it never names, the input head when it never reads input, and the output when it
never emits, are unchanged by every run (`ex_keep`). The test is syntactic (`St.wr`, `St.ms`, `St.rd`, `St.em`) and
decided by evaluation, so the phase specs need not carry frames for unrelated state.

-/

namespace NearCubicGates.Adapters.Compile
open NearCubicWires NearCubicGates.Close.Cells
set_option autoImplicit false

/-- `o` writes register `x`. -/
def opWr (x : Fin VV) : Op VV MM → Bool
  | .zero y => y == x
  | .inc y => y == x
  | .add y _ => y == x
  | .sub y _ => y == x
  | .copy y _ => y == x
  | .half y => y == x
  | .shl y => y == x
  | .mul _ _ z => z == x
  | .dm _ _ q r => q == x || r == x
  | .rdI y => y == x
  | .rdM _ y => y == x
  | .rdK y => y == x
  | _ => false

/-- `o` names store `m`. -/
def opMs (m : Fin MM) : Op VV MM → Bool
  | .rdM m' _ => m' == m
  | .wrM m' _ => m' == m
  | .rwM m' => m' == m
  | .srtM m' => m' == m
  | _ => false

/-- `o` moves the input head. -/
def opRd : Op VV MM → Bool
  | .rdI _ => true
  | .bkI => true
  | _ => false

/-- `o` emits. -/
def opEm : Op VV MM → Bool
  | .emit _ => true
  | _ => false

def sAny (f : Op VV MM → Bool) : St VV MM → Bool
  | .op o => f o
  | .seq s t => sAny f s || sAny f t
  | .ite _ s t => sAny f s || sAny f t
  | .loop _ s => sAny f s

/-- **Untouched state is preserved.** -/
theorem ex_keep {C : Ctx} {s : St VV MM} {a b : DS VV MM} {n : ℕ} (h : Ex C s a b n) :
    (∀ x, sAny (opWr x) s = false → b.env x = a.env x) ∧
    (∀ m, sAny (opMs m) s = false → b.ram m = a.ram m ∧ b.rc m = a.rc m) ∧
    (sAny opRd s = false → b.ip = a.ip) ∧ (sAny opEm s = false → b.out = a.out) := by
  induction h with
  | op ho =>
      cases ho with
      | zero y a => exact ⟨fun x hx => by simp [sAny, opWr] at hx; simp [DS.set, Function.update_of_ne (Ne.symm hx)],
          fun _ _ => ⟨rfl, rfl⟩, fun _ => rfl, fun _ => rfl⟩
      | inc y a _ => exact ⟨fun x hx => by simp [sAny, opWr] at hx; simp [DS.set, Function.update_of_ne (Ne.symm hx)],
          fun _ _ => ⟨rfl, rfl⟩, fun _ => rfl, fun _ => rfl⟩
      | add y z a _ _ => exact ⟨fun x hx => by simp [sAny, opWr] at hx; simp [DS.set, Function.update_of_ne (Ne.symm hx)],
          fun _ _ => ⟨rfl, rfl⟩, fun _ => rfl, fun _ => rfl⟩
      | sub y z a _ _ => exact ⟨fun x hx => by simp [sAny, opWr] at hx; simp [DS.set, Function.update_of_ne (Ne.symm hx)],
          fun _ _ => ⟨rfl, rfl⟩, fun _ => rfl, fun _ => rfl⟩
      | copy y z a _ => exact ⟨fun x hx => by simp [sAny, opWr] at hx; simp [DS.set, Function.update_of_ne (Ne.symm hx)],
          fun _ _ => ⟨rfl, rfl⟩, fun _ => rfl, fun _ => rfl⟩
      | half y a => exact ⟨fun x hx => by simp [sAny, opWr] at hx; simp [DS.set, Function.update_of_ne (Ne.symm hx)],
          fun _ _ => ⟨rfl, rfl⟩, fun _ => rfl, fun _ => rfl⟩
      | shl y a _ => exact ⟨fun x hx => by simp [sAny, opWr] at hx; simp [DS.set, Function.update_of_ne (Ne.symm hx)],
          fun _ _ => ⟨rfl, rfl⟩, fun _ => rfl, fun _ => rfl⟩
      | mul y z w a _ _ _ _ => exact ⟨fun x hx => by simp [sAny, opWr] at hx; simp [DS.set, Function.update_of_ne (Ne.symm hx)],
          fun _ _ => ⟨rfl, rfl⟩, fun _ => rfl, fun _ => rfl⟩
      | dm y z q r a _ _ _ _ _ _ _ _ =>
          exact ⟨fun x hx => by
            simp [sAny, opWr] at hx
            simp [DS.set, Function.update_of_ne (Ne.symm hx.1), Function.update_of_ne (Ne.symm hx.2)],
            fun _ _ => ⟨rfl, rfl⟩, fun _ => rfl, fun _ => rfl⟩
      | rdI y a _ => exact ⟨fun x hx => by simp [sAny, opWr] at hx; simp [DS.set, Function.update_of_ne (Ne.symm hx)],
          fun _ _ => ⟨rfl, rfl⟩, fun h => by simp [sAny, opRd] at h, fun _ => rfl⟩
      | bkI a _ => exact ⟨fun _ _ => rfl, fun _ _ => ⟨rfl, rfl⟩, fun h => by simp [sAny, opRd] at h, fun _ => rfl⟩
      | emit e a => exact ⟨fun _ _ => rfl, fun _ _ => ⟨rfl, rfl⟩, fun _ => rfl, fun h => by simp [sAny, opEm] at h⟩
      | rdM m' y a _ =>
          exact ⟨fun x hx => by simp [sAny, opWr] at hx; simp [DS.adv, DS.set, Function.update_of_ne (Ne.symm hx)],
            fun m hm => by simp [sAny, opMs] at hm; simp [DS.adv, DS.set, Function.update_of_ne (Ne.symm hm)],
            fun _ => rfl, fun _ => rfl⟩
      | wrM m' y a _ =>
          exact ⟨fun _ _ => rfl, fun m hm => by
            simp [sAny, opMs] at hm; simp [DS.put, Function.update_of_ne (Ne.symm hm)], fun _ => rfl, fun _ => rfl⟩
      | rwM m' a =>
          exact ⟨fun _ _ => rfl, fun m hm => by
            simp [sAny, opMs] at hm; simp [DS.rew, Function.update_of_ne (Ne.symm hm)], fun _ => rfl, fun _ => rfl⟩
      | srtM m' a _ =>
          exact ⟨fun _ _ => rfl, fun m hm => by
            simp [sAny, opMs] at hm; simp [DS.srt, Function.update_of_ne (Ne.symm hm)], fun _ => rfl, fun _ => rfl⟩
      | kem e a _ => exact ⟨fun _ _ => rfl, fun _ _ => ⟨rfl, rfl⟩, fun _ => rfl, fun _ => rfl⟩
      | kcall s a _ _ => exact ⟨fun _ _ => rfl, fun _ _ => ⟨rfl, rfl⟩, fun _ => rfl, fun _ => rfl⟩
      | rdK y a _ => exact ⟨fun x hx => by simp [sAny, opWr] at hx; simp [DS.set, Function.update_of_ne (Ne.symm hx)],
          fun _ _ => ⟨rfl, rfl⟩, fun _ => rfl, fun _ => rfl⟩
  | seq _ _ ih1 ih2 =>
      refine ⟨fun x hx => ?_, fun m hm => ?_, fun h => ?_, fun h => ?_⟩ <;> simp only [sAny, Bool.or_eq_false_iff] at *
      · rw [ih2.1 x hx.2, ih1.1 x hx.1]
      · exact ⟨(ih2.2.1 m hm.2).1.trans (ih1.2.1 m hm.1).1, (ih2.2.1 m hm.2).2.trans (ih1.2.1 m hm.1).2⟩
      · rw [ih2.2.2.1 h.2, ih1.2.2.1 h.1]
      · rw [ih2.2.2.2 h.2, ih1.2.2.2 h.1]
  | iteT _ _ _ ih =>
      refine ⟨fun x hx => ?_, fun m hm => ?_, fun h => ?_, fun h => ?_⟩ <;> simp only [sAny, Bool.or_eq_false_iff] at *
      · exact ih.1 x hx.1
      · exact ih.2.1 m hm.1
      · exact ih.2.2.1 h.1
      · exact ih.2.2.2 h.1
  | iteF _ _ _ ih =>
      refine ⟨fun x hx => ?_, fun m hm => ?_, fun h => ?_, fun h => ?_⟩ <;> simp only [sAny, Bool.or_eq_false_iff] at *
      · exact ih.1 x hx.2
      · exact ih.2.1 m hm.2
      · exact ih.2.2.1 h.2
      · exact ih.2.2.2 h.2
  | loopF _ _ => exact ⟨fun _ _ => rfl, fun _ _ => ⟨rfl, rfl⟩, fun _ => rfl, fun _ => rfl⟩
  | loopT _ _ _ _ ih1 ih2 =>
      refine ⟨fun x hx => ?_, fun m hm => ?_, fun h => ?_, fun h => ?_⟩
      · rw [ih2.1 x hx, ih1.1 x (by simpa [sAny] using hx)]
      · exact ⟨(ih2.2.1 m hm).1.trans (ih1.2.1 m (by simpa [sAny] using hm)).1,
          (ih2.2.1 m hm).2.trans (ih1.2.1 m (by simpa [sAny] using hm)).2⟩
      · rw [ih2.2.2.1 h, ih1.2.2.1 (by simpa [sAny] using h)]
      · rw [ih2.2.2.2 h, ih1.2.2.2 (by simpa [sAny] using h)]
  | mono _ _ ih => exact ih

/-- `Hs` with the untouched state. -/
theorem Hs.keep {C : Ctx} {s : St VV MM} {a : DS VV MM} {t : ℕ} {R : DS VV MM → Prop} (h : Hs C s a t R) :
    Hs C s a t (fun b => R b ∧ (∀ x, sAny (opWr x) s = false → b.env x = a.env x) ∧
      (∀ m, sAny (opMs m) s = false → b.ram m = a.ram m ∧ b.rc m = a.rc m) ∧
      (sAny opRd s = false → b.ip = a.ip) ∧ (sAny opEm s = false → b.out = a.out)) := by
  obtain ⟨b, n, he, hn, hb⟩ := h
  exact ⟨b, n, he, hn, hb, ex_keep he⟩

example : sAny (opMs sTK) runP = false := by decide
example : sAny (opWr dN) runP = false := by decide
example : sAny (opWr iIdx) tmplP = false := by decide
example : sAny opEm balP = false := by decide

end NearCubicGates.Adapters.Compile
