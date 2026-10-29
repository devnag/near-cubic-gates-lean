import SourceAdapters.ShortPCP.Machines.FLangLag

/-!
# Packed coefficient operations for the coordinate solver

The construction in `lem:generator`: each triangular update uses reduced field masks and a polynomial
number of field operations. These routines read the stored coefficient vectors using width register 20. The
subsequent solver uses registers 23 and 24 for the desired row and the current triangular stage.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Routing.CoordinateMachine

open NearCubicGates.Adapters.ShortPCP.Machines.FL

/-- Read coefficient `i` from the vector stored in `v`, with width stored in register 20. -/
def getC (v : Var) (i : E) : E :=
  .md (.shr (.v v) (.mul i (.v 20))) (.shl (.k 1) (.v 20))

theorem getC_eval (G : Glob) (s : FS) (v : Var) (i : E) (w j : ℕ) (l : List ℕ)
    (hl : ∀ a ∈ l, a < 2 ^ w) (hv : s.env v = packW w l) (hw : s.env 20 = w)
    (hi : evalE G s i = j) (hj : j * w ≤ G.K) (hwidth : w + 1 ≤ G.K) :
    evalE G s (getC v i) = l.getD j 0 := by
  have hc := cap_ge G
  have h1 : min 1 G.cap = 1 := by omega
  have h2 : 2 ^ w ≤ G.cap := by
    have := pow_le_cap (G := G) (a := w + 1) hwidth
    rw [pow_succ] at this
    have := Nat.one_le_two_pow (n := w)
    omega
  simp only [getC, evalE, hv, hw, hi, h1, one_mul, min_eq_left h2, min_eq_left (hj.trans hc)]
  exact packW_get w l hl j

theorem getD_reduced (w : ℕ) (l : List ℕ) (hl : ∀ a ∈ l, a < 2 ^ w) (j : ℕ) :
    l.getD j 0 < 2 ^ w := by
  rcases Nat.lt_or_ge j l.length with hj | hj
  · rw [List.getD_eq_getElem _ _ hj]
    exact hl _ (List.getElem_mem _)
  · rw [List.getD_eq_default _ _ hj]
    positivity

theorem eval_fmul (G : Glob) (s : FS) (a b : E) (x y : ℕ)
    (ha : evalE G s a = x) (hb : evalE G s b = y)
    (hx : x < 2 ^ s.fl) (hy : y < 2 ^ s.fl) :
    evalE G s (.fmul a b) = mulW s.fp s.fl x y := by
  simp only [evalE, ha, hb, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]

theorem eval_fadd (G : Glob) (s : FS) (a b : E) (x y : ℕ)
    (ha : evalE G s a = x) (hb : evalE G s b = y)
    (hx : x < 2 ^ s.fl) (hy : y < 2 ^ s.fl) :
    evalE G s (.fadd a b) = x ^^^ y := by
  simp only [evalE, ha, hb, Nat.mod_eq_of_lt (Nat.xor_lt_two_pow hx hy)]

/-- Counted arithmetic routines do not read from the input tape. -/
def inputFree : S → Bool
  | .seq a b | .ite _ a b => inputFree a && inputFree b
  | .loop _ _ body => inputFree body
  | .rd _ | .whl _ _ => false
  | _ => true

theorem inputFree_ip (G : Glob) (prog : S) (h : inputFree prog = true) (s : FS) :
    (evalS G prog s).ip = s.ip := by
  induction prog generalizing s with
  | skip => rfl
  | set i e => rfl
  | seq a b iha ihb =>
      have hh : inputFree a = true ∧ inputFree b = true := by simpa [inputFree] using h
      obtain ⟨ha, hb⟩ := hh
      exact (ihb hb (evalS G a s)).trans (iha ha s)
  | ite c a b iha ihb =>
      have hh : inputFree a = true ∧ inputFree b = true := by simpa [inputFree] using h
      obtain ⟨ha, hb⟩ := hh
      simp only [evalS_ite]
      split
      · exact ihb hb s
      · exact iha ha s
  | loop i e body ih =>
      exact loop_inv G (fun _ t => t.ip = s.ip) rfl (by
        intro j _ t ht
        exact (ih h (t.setv i j)).trans ht)
  | whl c body ih => simp [inputFree] at h
  | emit e => rfl
  | field f p => simp only [evalS]; split <;> rfl
  | rd i => simp [inputFree] at h

end NearCubicGates.Adapters.Routing.CoordinateMachine
