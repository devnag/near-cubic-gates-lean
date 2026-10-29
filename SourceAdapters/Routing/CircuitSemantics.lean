import SourceAdapters.Joins.AffineRouting
import Mathlib.Tactic

/-! Straight-line gate append semantics for the circuit generator; see `lem:generator`.-/
set_option autoImplicit false
noncomputable section
namespace NearCubicGates.Adapters.Routing.Circuit
open NearCubicGates.Adapters.ACSP
variable {F : Type} [Field F]

abbrev Gates (F : Type) := List (ArithGate F)
abbrev Poly (n : ℕ) (F : Type) [Field F] := MvPolynomial (Fin n) F

def values (n : ℕ) (gs : Gates F) : List (Poly n F) :=
  gs.foldl (fun prior g => prior ++ [g.poly n prior]) []

def GateOK (n i : ℕ) : ArithGate F → Prop
  | .input v => v < n
  | .const _ => True
  | .add a b | .mul a b => a < i ∧ b < i

def WF (n : ℕ) (gs : Gates F) : Prop := ∀ i : Fin gs.length, GateOK n i.val gs[i]

def Has (n : ℕ) (gs : Gates F) (i : ℕ) (p : Poly n F) : Prop :=
  i < gs.length ∧ (values n gs).getD i 0 = p

structure Ext (n : ℕ) (gs gs' : Gates F) : Prop where
  initial : gs <+: gs'
  wf : WF n gs'

@[simp] theorem values_nil (n : ℕ) : values n ([] : Gates F) = [] := rfl

@[simp] theorem values_length (n : ℕ) (gs : Gates F) : (values n gs).length = gs.length := by
  suffices h : ∀ (prior : List (Poly n F)),
      (gs.foldl (fun prior g => prior ++ [g.poly n prior]) prior).length = prior.length + gs.length by
    simpa [values] using h []
  induction gs with
  | nil => simp
  | cons g gs ih =>
      intro prior
      simpa [List.foldl_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (prior ++ [g.poly n prior])

@[simp] theorem values_push (n : ℕ) (gs : Gates F) (g : ArithGate F) :
    values n (gs ++ [g]) = values n gs ++ [g.poly n (values n gs)] := by
  simp [values, List.foldl_append]

theorem values_prefix (n : ℕ) {gs gs' : Gates F} (h : gs <+: gs') : values n gs <+: values n gs' := by
  obtain ⟨tail, rfl⟩ := h
  induction tail using List.reverseRecOn with
  | nil => simp
  | append_singleton tail g ih =>
      rw [← List.append_assoc, values_push]
      exact ih.trans (List.prefix_append _ _)

theorem Has.mono {n i : ℕ} {gs gs' : Gates F} {p : Poly n F}
    (h : Has n gs i p) (he : gs <+: gs') : Has n gs' i p := by
  refine ⟨lt_of_lt_of_le h.1 he.length_le, ?_⟩
  obtain ⟨tail, ht⟩ := values_prefix n he
  rw [← ht, List.getD_append _ _ _ _ (by simpa using h.1)]
  exact h.2

omit [Field F] in
theorem Ext.trans {n : ℕ} {g g' g'' : Gates F} (h : Ext n g g') (h' : Ext n g' g'') : Ext n g g'' :=
  ⟨h.initial.trans h'.initial, h'.wf⟩

omit [Field F] in
theorem Ext.refl {n : ℕ} {g : Gates F} (h : WF n g) : Ext n g g := ⟨List.prefix_refl _, h⟩

omit [Field F] in
theorem wf_push {n : ℕ} {gs : Gates F} (hw : WF n gs) (g : ArithGate F)
    (hg : GateOK n gs.length g) : WF n (gs ++ [g]) := by
  intro i
  change GateOK n i.val ((gs ++ [g])[i.val])
  by_cases hi : i.val < gs.length
  · rw [List.getElem_append_left hi]
    exact hw ⟨i.val, hi⟩
  · have ilt := i.isLt
    have he : i.val = gs.length := by simp only [List.length_append, List.length_singleton] at ilt; omega
    simpa [he, List.getElem_append_right (Nat.le_refl gs.length)] using hg

theorem has_push {n : ℕ} (gs : Gates F) (g : ArithGate F) :
    Has n (gs ++ [g]) gs.length (g.poly n (values n gs)) := by
  constructor
  · simp
  · rw [values_push, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by simp)]
    simp

omit [Field F] in
@[simp] theorem pushGate_run (gs : Gates F) (g : ArithGate F) :
    (pushGate g).run gs = (gs.length, gs ++ [g]) := rfl

theorem push_spec {n : ℕ} {gs : Gates F} (hw : WF n gs) (g : ArithGate F)
    (hg : GateOK n gs.length g) :
    Ext n gs ((pushGate g).run gs).2 ∧
    Has n ((pushGate g).run gs).2 ((pushGate g).run gs).1 (g.poly n (values n gs)) ∧
    ((pushGate g).run gs).2.length = gs.length + 1 :=
  ⟨⟨List.prefix_append _ _, wf_push hw g hg⟩, has_push gs g, by simp⟩

theorem has_const {n : ℕ} (gs : Gates F) (c : F) :
    Has n (gs ++ [.const c]) gs.length (MvPolynomial.C c) := has_push gs (.const c)

theorem has_add {n i j : ℕ} {gs : Gates F} {p q : Poly n F}
    (hp : Has n gs i p) (hq : Has n gs j q) :
    Has n (gs ++ [.add i j]) gs.length (p + q) := by
  simpa only [ArithGate.poly, hp.2, hq.2] using has_push (n := n) gs (.add i j)

theorem has_mul {n i j : ℕ} {gs : Gates F} {p q : Poly n F}
    (hp : Has n gs i p) (hq : Has n gs j q) :
    Has n (gs ++ [.mul i j]) gs.length (p * q) := by
  simpa only [ArithGate.poly, hp.2, hq.2] using has_push (n := n) gs (.mul i j)

/-- A transparent list loop for reasoning about the elaborated mutable for-loops. -/
def loop {α β : Type} (f : α → β → Builder F β) : List α → β → Builder F β
  | [], b => pure b
  | a :: as, b => do
      let b' ← f a b
      loop f as b'

omit [Field F] in
theorem forIn_eq_loop {α β : Type} (f : α → β → Builder F β) (as : List α) (b : β) :
    (forIn as b fun a b => do
      let b' ← f a b
      pure (ForInStep.yield b')) = loop f as b := by
  induction as generalizing b with
  | nil => rfl
  | cons a as ih =>
      simp only [List.forIn_cons, loop, bind_assoc]
      congr 1
      funext b'
      simp only [pure_bind]
      exact ih b'

end NearCubicGates.Adapters.Routing.Circuit
end
