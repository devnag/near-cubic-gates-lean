import Proof.Gates.CounterMachine.CellNats

/-! # RG machine, part 6: where the fields of the cell input sit

Indices into `cellN` (the naturals of `callWord c ++ paramsWord p ++ witWord c p wt`): the gate block and the top
coefficients of role `r`'s circuit, the chain factors and `M₁`, `A` in the parameter record, the witness coordinates
and the coefficient list of stage `s` and role `r`. Each lemma states what `cellN` holds from that index on. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.CounterMachine

open NearCubicWires NearCubicGates NearCubicGates.Close.Counter NearCubicGates.Close.Tabulator
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats

theorem drop_append_left' {α : Type} (l1 l2 : List α) (i : ℕ) : (l1 ++ l2).drop (l1.length + i) = l2.drop i := by
  rw [List.drop_append]; simp

theorem intN_length (z : ℤ) : (intN z).length = 2 := rfl

theorem flatMap_intN_length (zs : List ℤ) : (zs.flatMap intN).length = 2 * zs.length := by
  induction zs with
  | nil => rfl
  | cons z zs ih => simp [List.flatMap_cons, intN_length, ih]; ring

theorem ratN_length (q : ℚ) : (ratN q).length = 3 := rfl

theorem gateN_length {n : ℕ} (g : NormalizedThresholdGate n) : (gateN g).length = 2 * n + 3 := by
  unfold gateN
  rw [List.length_append, List.length_append, flatMap_intN_length, List.length_ofFn, List.length_singleton,
    intN_length]; ring

theorem flatMap_gateN_length {n : ℕ} (gs : List (NormalizedThresholdGate n)) :
    (gs.flatMap gateN).length = gs.length * (2 * n + 3) := by
  induction gs with
  | nil => simp
  | cons g gs ih => rw [List.flatMap_cons, List.length_append, gateN_length, ih, List.length_cons]; ring

theorem circN_length {n : ℕ} (C : NCircuit n) :
    (circN C).length = 3 + C.gates.length * (2 * n + 3) + 2 * C.coeffs.length + C.table.length := by
  unfold circN
  simp only [List.length_append, List.length_singleton, List.length_map]
  rw [flatMap_gateN_length, flatMap_intN_length]; ring

/-! ## The call -/

section CallIdx
variable (c : Call)

/-- The gate block of role `r` (`circ c r`). -/
def gateIdx (r : ℕ) : ℕ := if r = 0 then 3 else 2 + (circN c.first).length + 1

/-- The first top coefficient of role `r`. -/
def scoreIdx (r : ℕ) : ℕ :=
  if r = 0 then 4 + c.first.gates.length * (2 * c.n + 3)
  else 2 + (circN c.first).length + 2 + c.second.gates.length * (2 * c.n + 3)

theorem callN_drop_gates (r : ℕ) :
    ∃ rest, (callN c).drop (gateIdx c r) = (circ c r).gates.flatMap gateN ++ rest := by
  unfold gateIdx circ
  by_cases hr : r = 0
  · simp only [hr, if_true]
    refine ⟨[(circ c 0).coeffs.length] ++ (circ c 0).coeffs.flatMap intN ++ [c.first.table.length] ++
      c.first.table.map bitN ++ circN c.second ++ [c.parity.length] ++ c.parity ++ ratN c.radius, ?_⟩
    simp [callN, circN, circ, List.append_assoc]
  · simp only [hr, if_false]
    refine ⟨[c.second.coeffs.length] ++ c.second.coeffs.flatMap intN ++ [c.second.table.length] ++
      c.second.table.map bitN ++ [c.parity.length] ++ c.parity ++ ratN c.radius, ?_⟩
    have e : callN c = ([c.n, kindTag c.kind] ++ circN c.first ++ [c.second.gates.length]) ++
        (c.second.gates.flatMap gateN ++ [c.second.coeffs.length] ++ c.second.coeffs.flatMap intN ++
          [c.second.table.length] ++ c.second.table.map bitN ++ [c.parity.length] ++ c.parity ++ ratN c.radius) := by
      simp [callN, circN, List.append_assoc]
    rw [e, show 2 + (circN c.first).length + 1 = ([c.n, kindTag c.kind] ++ circN c.first ++
      [c.second.gates.length]).length + 0 by simp; ring, drop_append_left']
    simp [List.append_assoc]

theorem callN_drop_score (r : ℕ) :
    ∃ rest, (callN c).drop (scoreIdx c r) = (circ c r).coeffs.flatMap intN ++ rest := by
  unfold scoreIdx circ
  by_cases hr : r = 0
  · simp only [hr, if_true]
    refine ⟨[c.first.table.length] ++ c.first.table.map bitN ++ circN c.second ++ [c.parity.length] ++ c.parity ++
      ratN c.radius, ?_⟩
    have e : callN c = ([c.n, kindTag c.kind, c.first.gates.length] ++ c.first.gates.flatMap gateN ++
        [c.first.coeffs.length]) ++ (c.first.coeffs.flatMap intN ++ [c.first.table.length] ++ c.first.table.map bitN ++
        circN c.second ++ [c.parity.length] ++ c.parity ++ ratN c.radius) := by
      simp [callN, circN, List.append_assoc]
    rw [e, show 4 + c.first.gates.length * (2 * c.n + 3) = ([c.n, kindTag c.kind, c.first.gates.length] ++
      c.first.gates.flatMap gateN ++ [c.first.coeffs.length]).length + 0 by
        simp only [List.length_append, List.length_cons, List.length_singleton, List.length_nil,
          flatMap_gateN_length]; ring,
      drop_append_left']
    simp [List.append_assoc]
  · simp only [hr, if_false]
    refine ⟨[c.second.table.length] ++ c.second.table.map bitN ++ [c.parity.length] ++ c.parity ++ ratN c.radius, ?_⟩
    have e : callN c = ([c.n, kindTag c.kind] ++ circN c.first ++ [c.second.gates.length] ++
        c.second.gates.flatMap gateN ++ [c.second.coeffs.length]) ++ (c.second.coeffs.flatMap intN ++
        [c.second.table.length] ++ c.second.table.map bitN ++ [c.parity.length] ++ c.parity ++ ratN c.radius) := by
      simp [callN, circN, List.append_assoc]
    rw [e, show 2 + (circN c.first).length + 2 + c.second.gates.length * (2 * c.n + 3) =
      ([c.n, kindTag c.kind] ++ circN c.first ++ [c.second.gates.length] ++ c.second.gates.flatMap gateN ++
        [c.second.coeffs.length]).length + 0 by
        simp only [List.length_append, List.length_cons, List.length_singleton, List.length_nil,
          flatMap_gateN_length]; ring, drop_append_left']
    simp [List.append_assoc]

end CallIdx

/-! ## The parameters -/

section ParIdx
variable (p : Params)

/-- `M₁`, then `J`, the factor count, the factors, `A`, `Λ` follow at this offset of `paramsN`. -/
def m1Off : ℕ := 22 + (p.primes.sort (· ≤ ·)).length

theorem paramsN_drop_m1 : (paramsN p).drop (m1Off p) =
    [p.M1, p.J, p.factors.length] ++ p.factors ++ [p.A, p.Lambda] := by
  have e : paramsN p = ([p.n, bitN p.pair, p.W] ++ ratN p.beta ++ [p.k, p.T, p.m, p.Dmax, p.P, p.e,
      (p.primes.sort (· ≤ ·)).length] ++ p.primes.sort (· ≤ ·) ++ [p.window, p.L2, p.Lw, p.hE, p.h, p.R0] ++
      ratN p.ell0) ++ ([p.M1, p.J, p.factors.length] ++ p.factors ++ [p.A, p.Lambda]) := by
    simp [paramsN, List.append_assoc]
  rw [e, show m1Off p = ([p.n, bitN p.pair, p.W] ++ ratN p.beta ++ [p.k, p.T, p.m, p.Dmax, p.P, p.e,
      (p.primes.sort (· ≤ ·)).length] ++ p.primes.sort (· ≤ ·) ++ [p.window, p.L2, p.Lw, p.hE, p.h, p.R0] ++
      ratN p.ell0).length + 0 by
    simp only [List.length_append, List.length_cons, List.length_nil, ratN_length, m1Off]; ring,
    drop_append_left', List.drop_zero]

end ParIdx

end NearCubicGates.Close.CounterMachine
