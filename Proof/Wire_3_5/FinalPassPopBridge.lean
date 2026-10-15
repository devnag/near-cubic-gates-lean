import Proof.Wire_3_5.FinalPassPop
import Proof.Wire_3_5.StarMixedScore

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Pop
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Stars

theorem cornerBit_eq (sgn a b c d : Bool) :
    cornerBit sgn a b c d = if sgn then cornerPlus ![a, b, c, d] else cornerMinus ![a, b, c, d] := by
  cases sgn <;> cases a <;> cases b <;> cases c <;> cases d <;> decide

theorem cornerBit_f2 (sgn a b c d : Bool) :
    cornerBit sgn a b c d = F2Poly.eval (if sgn then zPlusF2 else zMinusF2) ![a, b, c, d] := by
  rw [cornerBit_eq]
  cases sgn <;> simp [zPlusF2_eval, zMinusF2_eval]

/-- **Entry `q` of the population bits** is the `𝔽₂` form of `Z^±` at the corners `4q, …, 4q+3`. -/
theorem popBits_getElem (sgn : Bool) :
    ∀ (n : ℕ) (X : List Bool) (hX : X.length = 4 * n) (q : ℕ) (hq : q < n),
      (popBits sgn X)[q]'(by rw [popBits_length sgn n X hX]; exact hq) =
        F2Poly.eval (if sgn then zPlusF2 else zMinusF2) (fun k : Fin 4 => X[4 * q + k.val]'(by omega))
  | 0, _, _, _, hq => absurd hq (Nat.not_lt_zero _)
  | n + 1, a :: b :: c :: d :: rest, hX, q, hq => by
    have hr : rest.length = 4 * n := by simp at hX; omega
    cases q with
    | zero =>
      simp only [popBits, List.getElem_cons_zero]
      rw [cornerBit_f2]
      congr 1
      funext k
      fin_cases k <;> rfl
    | succ q =>
      simp only [popBits, List.getElem_cons_succ]
      rw [popBits_getElem sgn n rest hr q (by omega)]
      congr 1
      funext k
      have e : 4 * (q + 1) + k.val = 4 * q + k.val + 1 + 1 + 1 + 1 := by omega
      simp only [e, List.getElem_cons_succ]
  | _ + 1, [], hX, _, _ => by simp only [List.length_nil] at hX; omega
  | _ + 1, [_], hX, _, _ => by simp only [List.length_cons, List.length_nil] at hX; omega
  | _ + 1, [_, _], hX, _, _ => by simp only [List.length_cons, List.length_nil] at hX; omega
  | _ + 1, [_, _, _], hX, _, _ => by simp only [List.length_cons, List.length_nil] at hX; omega

/-- The corner word of a gate list at `(c, u, v)`: the four corners of each gate (`Stars.corners`), gate after gate. -/
def cornerWord {n : ℕ} (Ts : List (BitInput n → Bool)) (c u v : BitInput n) : List Bool :=
  Ts.flatMap fun T => List.ofFn (corners T c u v)

theorem popBits_cornerWord {n : ℕ} (Ts : List (BitInput n → Bool)) (c u v : BitInput n) :
    popBits true (cornerWord Ts c u v) = Ts.map (fun T => residualPlus T c u v) ∧
      popBits false (cornerWord Ts c u v) = Ts.map (fun T => residualMinus T c u v) := by
  induction Ts with
  | nil => exact ⟨rfl, rfl⟩
  | cons T Ts ih =>
    have e : cornerWord (T :: Ts) c u v =
        corners T c u v 0 :: corners T c u v 1 :: corners T c u v 2 :: corners T c u v 3 :: cornerWord Ts c u v := by
      simp [cornerWord, List.ofFn_succ]
    rw [e]
    refine ⟨?_, ?_⟩
    · simp only [popBits, List.map_cons, ih.1, cornerBit_eq, if_true, residualPlus_eq_corner]
      rw [← fin4_fun_eq]
    · simp only [popBits, List.map_cons, ih.2, cornerBit_eq, Bool.false_eq_true, if_false, residualMinus_eq_corner]
      rw [← fin4_fun_eq]

end NearCubicWires.WireExponent3_5.FinalPass.Pop
