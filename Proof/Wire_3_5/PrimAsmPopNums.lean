import Proof.Wire_3_5.PrimAsmArith

/-! # PA (d)-SYM, part 13: the POP row's Route B capacities, computed

From the call's numbers in registers (`L`, `d = 3·listBound`, `c = capP`, `CAP = labSum labs`, `LL = |labs at level
2|`, `M`, `Mlab`, the walk length `n`, `lw = |levelWord|`, `Q = (8L+2)^d`), a straight-line program (`Arith`) computes
the block-length bound `BL`, the scrub capacity `R = popKc … + 1`, its log `Lg = R + 1`, the print bound `PW = popPW …`
and the log capacity `cap = popCapB n R PW` (**`popNums_spec`**, **`popNums_R`**, …): the numbers `PopCap.popStates_okB`
needs (Route B condition (1)).

Paper quantity of the main type: `PopCap.popKc`/`popPW`/`popCapB` (C2's capacities of the POP row, dominated). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.PrimAsm.PopNums
open NearCubicWires.WireExponent3_5.PrimAsm.Arith

/-- Register roles: inputs `0 L`, `1 d`, `2 c`, `3 CAP`, `4 LL`, `5 M`, `6 Mlab`, `7 n`, `8 lw`, `9 Q`; outputs `10 BL`,
`12 R`, `13 PW`, `14 cap`, `22 Lg`; the rest (from `0`) scratch and constants. -/
abbrev NReg := Fin 40

/-- The constants. -/
def constOps : List (AOp 40) :=
  [.inc 30 2, .inc 31 4, .inc 32 8, .inc 33 50, .inc 34 64, .inc 35 100, .inc 36 118, .inc 37 128]

/-- `BL = 128L + 4d + LL + 4·CAP + 4·lw + 4M + 64(c+1) + 124`. -/
def blOps : List (AOp 40) :=
  [.add 2 15, .inc 15 1, .mul 0 37 10, .mul 1 31 10, .add 4 10, .mul 3 31 10, .mul 8 31 10, .mul 5 31 10,
    .mul 15 34 10, .inc 10 124]

/-- `Y = 118L + 10 + 50(c+1)³ + 2·CAP + 100(4L+1)²`, then `R = 2·BL + Q·Y + 7`, `Lg = R + 1`. -/
def rOps : List (AOp 40) :=
  [.mul 15 15 16, .mul 16 15 17, .mul 0 31 18, .inc 18 1, .mul 18 18 19,
    .mul 0 36 11, .inc 11 10, .mul 17 33 11, .mul 3 30 11, .mul 19 35 11,
    .mul 10 30 12, .mul 9 11 12, .inc 12 7, .add 12 22, .inc 22 1]

/-- `PW = Q·(2d(Mlab+1) + 2) + 1`, `cap = n·(8R + 2·PW + 33) + 20`. -/
def pwOps : List (AOp 40) :=
  [.add 6 20, .inc 20 1, .mul 1 20 21, .mul 21 30 23, .inc 23 2, .mul 9 23 13, .inc 13 1,
    .mul 12 32 24, .mul 13 30 24, .inc 24 33, .mul 7 24 14, .inc 14 20]

/-- The whole program's operations. -/
def numOps : List (AOp 40) := constOps ++ blOps ++ rOps ++ pwOps

theorem evalL_append {k : ℕ} (v : Fin k → ℕ) (xs ys : List (AOp k)) : evalL v (xs ++ ys) = evalL (evalL v xs) ys := by
  induction xs generalizing v with
  | nil => rfl
  | cons o xs ih => exact ih (o.eval v)

/-- The block-length bound's formula. -/
def blF (L d c CAP LL lw M : ℕ) : ℕ := 128 * L + 4 * d + LL + 4 * CAP + 4 * lw + 4 * M + 64 * (c + 1) + 124

theorem const_vals (v : Fin 40 → ℕ) (hz : ∀ i : Fin 40, 30 ≤ i.val → v i = 0) :
    let w := evalL v constOps
    w 30 = 2 ∧ w 31 = 4 ∧ w 32 = 8 ∧ w 33 = 50 ∧ w 34 = 64 ∧ w 35 = 100 ∧ w 36 = 118 ∧ w 37 = 128 ∧
      (∀ i : Fin 40, i.val < 30 → w i = v i) := by
  intro w
  have h30 := hz 30 (by decide); have h31 := hz 31 (by decide); have h32 := hz 32 (by decide)
  have h33 := hz 33 (by decide); have h34 := hz 34 (by decide); have h35 := hz 35 (by decide)
  have h36 := hz 36 (by decide); have h37 := hz 37 (by decide)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [w, constOps, evalL, AOp.eval, Function.update_apply, h30, h31, h32, h33, h34, h35, h36, h37]
  intro i hi
  have n30 : i ≠ 30 := Fin.ne_of_val_ne (by simp; omega)
  have n31 : i ≠ 31 := Fin.ne_of_val_ne (by simp; omega)
  have n32 : i ≠ 32 := Fin.ne_of_val_ne (by simp; omega)
  have n33 : i ≠ 33 := Fin.ne_of_val_ne (by simp; omega)
  have n34 : i ≠ 34 := Fin.ne_of_val_ne (by simp; omega)
  have n35 : i ≠ 35 := Fin.ne_of_val_ne (by simp; omega)
  have n36 : i ≠ 36 := Fin.ne_of_val_ne (by simp; omega)
  have n37 : i ≠ 37 := Fin.ne_of_val_ne (by simp; omega)
  simp [n30, n31, n32, n33, n34, n35, n36, n37]

/-- The values the program computes (inputs in `0 … 9`, everything else from `0`). -/
theorem numOps_vals (v : Fin 40 → ℕ) (hz : ∀ i : Fin 40, 10 ≤ i.val → v i = 0) :
    let w := evalL v numOps
    w 10 = blF (v 0) (v 1) (v 2) (v 3) (v 4) (v 8) (v 5) ∧
    w 12 = 2 * blF (v 0) (v 1) (v 2) (v 3) (v 4) (v 8) (v 5) +
      v 9 * (118 * v 0 + 10 + 50 * (v 2 + 1) ^ 3 + 2 * v 3 + 100 * (4 * v 0 + 1) ^ 2) + 7 ∧
    w 22 = w 12 + 1 ∧
    w 13 = v 9 * (2 * v 1 * (v 6 + 1) + 2) + 1 ∧
    w 14 = v 7 * (8 * w 12 + 2 * w 13 + 33) + 20 := by
  intro w
  have z10 : v 10 = 0 := hz 10 (by decide)
  have z11 : v 11 = 0 := hz 11 (by decide)
  have z12 : v 12 = 0 := hz 12 (by decide)
  have z13 : v 13 = 0 := hz 13 (by decide)
  have z14 : v 14 = 0 := hz 14 (by decide)
  have z15 : v 15 = 0 := hz 15 (by decide)
  have z16 : v 16 = 0 := hz 16 (by decide)
  have z17 : v 17 = 0 := hz 17 (by decide)
  have z18 : v 18 = 0 := hz 18 (by decide)
  have z19 : v 19 = 0 := hz 19 (by decide)
  have z20 : v 20 = 0 := hz 20 (by decide)
  have z21 : v 21 = 0 := hz 21 (by decide)
  have z22 : v 22 = 0 := hz 22 (by decide)
  have z23 : v 23 = 0 := hz 23 (by decide)
  have z24 : v 24 = 0 := hz 24 (by decide)
  have z30 : v 30 = 0 := hz 30 (by decide)
  have z31 : v 31 = 0 := hz 31 (by decide)
  have z32 : v 32 = 0 := hz 32 (by decide)
  have z33 : v 33 = 0 := hz 33 (by decide)
  have z34 : v 34 = 0 := hz 34 (by decide)
  have z35 : v 35 = 0 := hz 35 (by decide)
  have z36 : v 36 = 0 := hz 36 (by decide)
  have z37 : v 37 = 0 := hz 37 (by decide)
  simp only [w, numOps, constOps, blOps, rOps, pwOps, List.cons_append, List.nil_append, evalL, AOp.eval,
    Function.update_apply]
  simp (config := { decide := true }) only [↓reduceIte, Fin.isValue]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  all_goals
    simp only [z10, z11, z12, z13, z14, z15, z16, z17, z18, z19, z20, z21, z22, z23, z24, z30, z31, z32, z33, z34, z35, z36, z37, blF]
    ring

/-- **The program's outputs are Route B's capacities** (at `Q = (8L+2)^d`): `R = popKc L d c CAP BL + 1`,
`PW = popPW L d Mlab`, `cap = popCapB n R PW`, `Lg = R + 1`. -/
theorem numOps_capacities (v : Fin 40 → ℕ) (hz : ∀ i : Fin 40, 10 ≤ i.val → v i = 0)
    (hQ : v 9 = (8 * v 0 + 2) ^ v 1) :
    evalL v numOps 10 = blF (v 0) (v 1) (v 2) (v 3) (v 4) (v 8) (v 5) ∧
    evalL v numOps 12 = PopCap.popKc (v 0) (v 1) (v 2) (v 3) (evalL v numOps 10) + 1 ∧
    evalL v numOps 22 = evalL v numOps 12 + 1 ∧
    evalL v numOps 13 = PopCap.popPW (v 0) (v 1) (v 6) ∧
    evalL v numOps 14 = PopCap.popCapB (v 7) (evalL v numOps 12) (evalL v numOps 13) := by
  obtain ⟨h10, h12, h22, h13, h14⟩ := numOps_vals v hz
  refine ⟨h10, ?_, h22, ?_, ?_⟩
  · rw [h12, h10, hQ]; unfold PopCap.popKc; ring
  · rw [h13, hQ]; unfold PopCap.popPW; ring
  · rw [h14]; unfold PopCap.popCapB; ring

end NearCubicWires.WireExponent3_5.PrimAsm.PopNums
