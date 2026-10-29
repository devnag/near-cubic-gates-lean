import SourceAdapters.ShortPCP.TimeDegree

/-!
# Single-run time, reference layer 5: `V_{RS,=}`, `V_{RS,<}`, `V_{RS,>}`, `V_RS`, `V_VRS` in poly-time form

The flat verifiers of the literal leaf (`PublishedStatements/BCGT13.lean`: `vEq`, `vLt`, `vGt`, `vRS`, `vVRS`) for the
tuple `(2, 4, 0, 1)`, with `Translate`, `D_{RS,=}`, the degree test, GetIndexOfElt of a random element and the
vanishing polynomial of `H` replaced by their poly-time forms. The theorems `vRS_eq`, `vVRS_eq` are equalities of
`FlatVerifier` records (same randomness, query count, length, query function, decision function) on independent
bases; so a machine computing the `F` forms computes the leaf's `V_RS` and `V_VRS` exactly (proof of `thm:short-pcp-ours`,
"A single run of V_RS or V_VRS takes poly(f) field operations … [BCGT13, Algorithms 12–16]").
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.ShortPCP.Time

open Finset NearCubicGates.Published.BCGT13 NearCubicWires.CanonicalBinary

variable {F : Type} [Field F] [DecidableEq F]

/-- `Q_{RS,=}`, poly-time form. -/
def qEqF (B : List F) (O : F) (r : List Bool) (i : ℕ) : Option ℕ :=
  match translateF B.length B O r i with
  | .inp _ j => some j
  | .prf j => some j

/-- `D_{RS,=}`, poly-time form (base case by `degreeTestF`). -/
def dEqR (B : List F) (O : F) (r : List Bool) (ans : ℕ → F) : Bool := dEqFF degreeTestF B.length B O r ans

/-- `V_{RS,=}`, poly-time form. -/
def vEqF (B : List F) (O : F) : FlatVerifier F where
  rand := randEq T0 B.length
  query := queryEq T0 B.length
  length := lengthEq T0 B.length
  Q := qEqF B O
  D := dEqR B O

/-- `V_{RS,<}`, poly-time form (the leaf's `vLt` with `Q_{RS,=}`, `D_{RS,=}` in poly-time form). -/
def vLtF (B : List F) (O : F) (d : ℕ) : FlatVerifier F where
  rand := randEq T0 B.length
  query := 2 * queryEq T0 B.length
  length := 2 * lengthEq T0 B.length
  Q := fun r i =>
    let qE := queryEq T0 B.length
    if 1 ≤ i ∧ i ≤ qE then qEqF B O r i
    else
      match qEqF B O r (i - qE) with
      | some j' => if 0 < j' ∧ j' ≤ 2 ^ B.length then some j' else some (lengthEq T0 B.length + j')
      | none => none
  D := fun r ans =>
    let qE := queryEq T0 B.length
    let b1 := dEqR B O r ans
    let ans2 : ℕ → F := fun i =>
      match qEqF B O r i with
      | some j' =>
        if 0 < j' ∧ j' ≤ 2 ^ B.length then
          eltWithIndex B O j' ^ (dKE B.length T0.η - d) * ans (qE + i)
        else ans (qE + i)
      | none => ans (qE + i)
    b1 && dEqR B O r ans2

/-- `V_{RS,>}`, poly-time form (GetIndexOfElt of the random `γ` is its coin value plus one). -/
def vGtF (B : List F) (O : F) (d : ℕ) : FlatVerifier F :=
  let κ := B.length
  let nS := 2 ^ κ
  let D' := dKE κ T0.η
  let m := mKED κ T0.η d
  let dd := d - m * (D' + 1)
  let one : Bool := decide (m * (D' + 1) < d + 1)
  let qE := queryEq T0 κ
  let lE := lengthEq T0 κ
  let vL := vLtF B O dd
  let qL := if one then vL.query else 0
  { rand := max (max (randEq T0 κ) (if one then randEq T0 κ else 0)) κ
    query := m * qE + qL + 1 + 2 ^ T0.η
    length := m * (nS + lE) + (if one then nS + vL.length else 0)
    Q := fun r i =>
      if d ≥ nS then none
      else if 1 ≤ i ∧ i ≤ m * qE then
        let zz := (i - 1) / qE
        (qEqF B O r (i - zz * qE)).map fun j' => nS + zz * (nS + lE) + j'
      else if one ∧ 1 ≤ i - m * qE ∧ i - m * qE ≤ qL then
        (vL.Q r (i - m * qE)).map fun j' => nS + m * (nS + lE) + j'
      else
        let i0 := i - (m * qE + qL)
        let ιγ := 1 + bitsValue (r.take κ)
        if i0 = 1 then some ιγ
        else if 1 < i0 ∧ i0 ≤ m + 1 then some (nS + (i0 - 2) * (nS + lE) + ιγ)
        else if one ∧ i0 = m + 2 then some (nS + m * (nS + lE) + ιγ)
        else none
    D := fun r ans =>
      if d ≥ nS then true
      else
        let γ := getRandElt B O (r.take κ)
        let bs := (List.range m).all fun z => dEqR B O r fun i => ans (z * qE + i)
        let bm := if one then vL.D r (fun i => ans (m * qE + i)) else true
        let base := m * qE + qL
        let v := ans (base + 1)
        let bc := decide (v = ∑ i ∈ Finset.range (2 ^ T0.η), γ ^ (i * (D' + 1)) * ans (base + 2 + i))
        bc && bs && bm }

/-- `V_RS`, poly-time form. -/
def vRSF (B : List F) (O : F) (d : ℕ) : FlatVerifier F :=
  if B.length ≤ T0.η then
    { rand := 0, query := 2 ^ B.length, length := 0, Q := fun _ i => some i,
      D := fun _ ans => degreeTestF B O d ans }
  else if d < dKE B.length T0.η then vLtF B O d
  else if d = dKE B.length T0.η then vEqF B O
  else vGtF B O d

/-- `V_VRS`, poly-time form (`Z_H` by Algorithm 21's recursion). -/
def vVRSF (B : List F) (O : F) (BH : List F) (OH : F) (d : ℕ) : FlatVerifier F :=
  let κ := B.length
  let nS := 2 ^ κ
  let V := vRSF B O (d - 2 ^ BH.length)
  { rand := max V.rand κ
    query := V.query + 2
    length := nS + V.length
    Q := fun r i =>
      if 1 ≤ i ∧ i ≤ V.query then (V.Q r i).map fun j => nS + j
      else
        if i = V.query + 1 then some (1 + bitsValue (r.take κ))
        else if i = V.query + 2 then some (nS + (1 + bitsValue (r.take κ)))
        else none
    D := fun r ans =>
      let bRS := V.D r ans
      let α := getRandElt B O (r.take κ)
      let τ := zFast BH (α + OH)
      bRS && decide (ans (V.query + 1) = τ * ans (V.query + 2)) }

/-! ## Equal to the leaf on independent bases -/

section Two

variable [CharP F 2]

theorem indexOfElt_getRandElt_take {B : List F} (hB : Indep B) (O : F) (r : List Bool) :
    indexOfElt B O (getRandElt B O (r.take B.length)) = 1 + bitsValue (r.take B.length) := by
  rw [indexOfElt_getRandElt hB, Nat.mod_eq_of_lt]
  exact lt_of_lt_of_le (bitsValue_lt _) (Nat.pow_le_pow_right (by norm_num) (by simp))

theorem qEq_eq {B : List F} (hB : Indep B) (O : F) : qEq T0 B O = qEqF B O := by
  funext r i
  simp only [qEq, qEqF, (translate_eq B.length B O r i hB).1]
  rfl

theorem dEq_eq {B : List F} (hB : Indep B) (O : F) : dEq T0 B O = dEqR B O := by
  funext r ans
  exact dEqF_eq degreeTestF (fun B O d ans hB => degreeTestF_eq hB O d ans) B.length B O r ans hB

theorem vEq_eq {B : List F} (hB : Indep B) (O : F) : vEq T0 B O = vEqF B O := by
  unfold vEq vEqF
  rw [qEq_eq hB, dEq_eq hB]

theorem vLt_eq {B : List F} (hB : Indep B) (O : F) (d : ℕ) : vLt T0 B O d = vLtF B O d := by
  unfold vLt vLtF
  rw [qEq_eq hB, dEq_eq hB]
  rfl

theorem vGt_eq {B : List F} (hB : Indep B) (O : F) (d : ℕ) : vGt T0 B O d = vGtF B O d := by
  unfold vGt vGtF
  simp only [qEq_eq hB, dEq_eq hB, vLt_eq hB, indexOfElt_getRandElt_take hB]

/-- **`V_RS` in poly-time form** (Algorithm 13 / §12.3.4). -/
theorem vRS_eq {B : List F} (hB : Indep B) (O : F) (d : ℕ) : vRS T0 B O d = vRSF B O d := by
  unfold vRS vRSF
  simp only [vLt_eq hB, vEq_eq hB, vGt_eq hB, degreeTestF_eq hB]

/-- **`V_VRS` in poly-time form** (Algorithm 12 / §12.3.5). -/
theorem vVRS_eq {B : List F} (hB : Indep B) (O : F) {BH : List F} (hBH : Indep BH) (OH : F) (d : ℕ) :
    vVRS T0 B O BH OH d = vVRSF B O BH OH d := by
  unfold vVRS vVRSF
  simp only [vRS_eq hB, indexOfElt_getRandElt_take hB, zEval_eq hBH, zFast_eq]

end Two

end NearCubicGates.Adapters.ShortPCP.Time
