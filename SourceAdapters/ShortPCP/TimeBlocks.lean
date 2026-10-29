import SourceAdapters.ShortPCP.TimeReadSet
import SourceAdapters.ShortPCP.TimeVerdict

/-!
# Single-run time, reference layer 10: the parameters of one sub-verifier run and its effective queries

Paper context: proof of `thm:short-pcp-ours`, Step 2, “Time and queries”. A single sub-verifier run
uses polynomially many field operations, and its queries depend on the random string alone.
All three sub-verifiers of `runVerdictN` (`TimeVerdict.lean`) use the domain basis `dom := q.domBasis φ`
and offset zero. Their actual parameters are
`V_R = vRSF dom 0 q.dA`,
`V_H = vVRSF dom 0 (q.hB φ) (q.hO φ) q.dB`, and
`V_I = vVRSF dom 0 (q.iB φ) (q.iO φ) q.dA`.
Thus the H-test uses its own basis, offset and supplied degree `q.dB`; the I-test uses the input-subspace
basis and offset with the assignment degree bound `q.dA`. This module gives
* closed forms `qRS`, `lRS`, `rRS` of `query`, `length`, `rand` of `vRSF` (`vRSF_params`);
* the case `V_{RS,>}` with `d ≥ 2^f` (`trivB`): no query, accept (`vRSF_triv`). There `query` is not polynomial
  in the input (it grows with `d`), so the machine asks only the **effective** queries: `1, …, qcI` of the
  `V_RS` part (`qcI = 0` in that case, else `query`), then the two queries of `V_VRS`'s `Z_H` test;
* `outD`, the decision on the answers at the effective positions, and `acceptsN_out`: it equals `acceptsN`.
-/

set_option autoImplicit false

noncomputable section

namespace NearCubicGates.Adapters.ShortPCP.Time

open NearCubicGates.Published.BCGT13 NearCubicWires.CanonicalBinary

/-! ## Closed forms of the parameters of `vRSF` -/

/-- The flag `m·(d_{κ,2}+1) < d + 1` of `V_{RS,>}`. -/
def gtOne (f d : ℕ) : Bool := decide (mKED f 2 d * (dKE f 2 + 1) < d + 1)

/-- `query` of `vRSF` on a basis of length `f`. -/
def qRS (f d : ℕ) : ℕ :=
  if f ≤ 2 then 2 ^ f else if d < dKE f 2 then 2 * queryEq T0 f else if d = dKE f 2 then queryEq T0 f
  else mKED f 2 d * queryEq T0 f + (if gtOne f d then 2 * queryEq T0 f else 0) + 1 + 4

/-- `length` of `vRSF`. -/
def lRS (f d : ℕ) : ℕ :=
  if f ≤ 2 then 0 else if d < dKE f 2 then 2 * lengthEq T0 f else if d = dKE f 2 then lengthEq T0 f
  else mKED f 2 d * (2 ^ f + lengthEq T0 f) + (if gtOne f d then 2 ^ f + 2 * lengthEq T0 f else 0)

/-- `rand` of `vRSF`. -/
def rRS (f d : ℕ) : ℕ :=
  if f ≤ 2 then 0 else if d < dKE f 2 then randEq T0 f else if d = dKE f 2 then randEq T0 f
  else max (randEq T0 f) f

variable {F : Type} [Field F] [DecidableEq F]

theorem vRSF_params (B : List F) (O : F) (d : ℕ) :
    (vRSF B O d).query = qRS B.length d ∧ (vRSF B O d).length = lRS B.length d ∧
      (vRSF B O d).rand = rRS B.length d := by
  unfold vRSF qRS lRS rRS gtOne
  simp only [T0_η]
  split_ifs <;> simp only [vLtF, vEqF, vGtF, T0_η] <;> (try split_ifs) <;> (simp_all; try omega)

/-! ## The trivial case -/

/-- `V_{RS,>}` with `d ≥ 2^f`. -/
def trivB (f d : ℕ) : Bool := decide (2 < f ∧ 2 ^ f ≤ d)

theorem dKE_lt (f : ℕ) : dKE f 2 < 2 ^ f := by
  unfold dKE
  have : 2 ^ f / 2 ^ 2 ≤ 2 ^ f := Nat.div_le_self _ _
  have : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  omega

theorem vRSF_triv (B : List F) (O : F) (d : ℕ) (h : trivB B.length d = true) :
    (∀ r i, (vRSF B O d).Q r i = none) ∧ ∀ r a, (vRSF B O d).D r a = true := by
  simp only [trivB, decide_eq_true_eq] at h
  have hk := dKE_lt B.length
  have e1 : ¬ B.length ≤ T0.η := by simp; omega
  have e2 : ¬ d < dKE B.length T0.η := by simp; omega
  have e3 : ¬ d = dKE B.length T0.η := by simp; omega
  have e4 : d ≥ 2 ^ B.length := h.2
  refine ⟨fun r i => ?_, fun r a => ?_⟩ <;> simp only [vRSF, e1, e2, e3, if_false, vGtF, e4, if_true]

/-! ## Effective positions -/

/-- The number of effective queries of the `V_RS` part. -/
def qcI (f d : ℕ) : ℕ := if trivB f d then 0 else qRS f d

/-- The number of effective queries (`v`: a `V_VRS` run, with its two `Z_H` queries). -/
def qcO (v : Bool) (f d : ℕ) : ℕ := qcI f d + if v then 2 else 0

/-- The query index of effective position `k` (`1 ≤ k`). -/
def idxO (f d k : ℕ) : ℕ := if k ≤ qcI f d then k else qRS f d + (k - qcI f d)

/-- The outer verifier: `V_VRS` or `V_RS`. -/
def outV (v : Bool) (B : List F) (O : F) (BH : List F) (OH : F) (d : ℕ) : FlatVerifier F :=
  if v then vVRSF B O BH OH d else vRSF B O d

/-- The degree of the `V_RS` part. -/
def innD (v : Bool) (h d : ℕ) : ℕ := if v then d - 2 ^ h else d

/-- `length` of the outer verifier. -/
def outLen (v : Bool) (f di : ℕ) : ℕ := (if v then 2 ^ f else 0) + lRS f di

/-- `rand` of the outer verifier. -/
def outRand (v : Bool) (f di : ℕ) : ℕ := if v then max (rRS f di) f else rRS f di

theorem outV_params (v : Bool) (B : List F) (O : F) (BH : List F) (OH : F) (d : ℕ) :
    (outV v B O BH OH d).length = outLen v B.length (innD v BH.length d) ∧
      (outV v B O BH OH d).rand = outRand v B.length (innD v BH.length d) := by
  obtain ⟨-, h2, h3⟩ := vRSF_params B O (innD v BH.length d)
  cases v <;> simp only [outV, outLen, outRand, innD, vVRSF, Bool.false_eq_true, ↓reduceIte] at h2 h3 ⊢ <;>
    simp [h2, h3]

/-- The `Z_H` test of `V_VRS` on the answers at effective positions `q + 1`, `q + 2`. -/
def vrsCheck (B : List F) (O : F) (BH : List F) (OH : F) (u : List Bool) (a : ℕ → F) (q : ℕ) : Bool :=
  decide (a (q + 1) = zFast BH (getRandElt B O (u.take B.length) + OH) * a (q + 2))

/-- **The decision on the answers at the effective positions.** -/
def outD (v : Bool) (B : List F) (O : F) (BH : List F) (OH : F) (di : ℕ) (u : List Bool) (a : ℕ → F) : Bool :=
  (if v then vrsCheck B O BH OH u a (qcI B.length di) else true) &&
    (if trivB B.length di then true else (vRSF B O di).D u a)

/-- **`acceptsN` from the answers at the effective positions.** -/
theorem acceptsN_out (v : Bool) (B : List F) (O : F) (BH : List F) (OH : F) (d : ℕ) (p : F → F) (πN : ℕ → F)
    (c : ℕ → Bool) (a : ℕ → F)
    (ha : ∀ k, 1 ≤ k → k ≤ qcO v B.length (innD v BH.length d) →
      a k = answersN (outV v B O BH OH d) B O p πN ((List.range (outV v B O BH OH d).rand).map c)
        (idxO B.length (innD v BH.length d) k)) :
    acceptsN (outV v B O BH OH d) B O p πN c =
      outD v B O BH OH (innD v BH.length d) ((List.range (outV v B O BH OH d).rand).map c) a := by
  generalize hu : (List.range (outV v B O BH OH d).rand).map c = u at ha
  have hq := (vRSF_params B O (innD v BH.length d)).1
  unfold acceptsN
  rw [hu]
  generalize hA : answersN (outV v B O BH OH d) B O p πN u = A at ha
  cases v with
  | false =>
    simp only [outV, outD, innD, Bool.false_eq_true, ↓reduceIte, Bool.true_and] at ha hA hq ⊢
    by_cases ht : trivB B.length d = true
    · rw [if_pos ht]; exact (vRSF_triv B O d ht).2 u A
    · rw [if_neg ht]
      refine vRSF_D_congr B O d u (fun i h1 h2 => ?_)
      have hi : i ≤ qcI B.length d := by simp only [qcI, ht, Bool.false_eq_true, ↓reduceIte]; exact hq ▸ h2
      have := ha i h1 (by simp only [qcO]; omega)
      rw [idxO, if_pos hi] at this
      exact this.symm
  | true =>
    simp only [outV, outD, innD, ↓reduceIte] at ha hA hq ⊢
    simp only [vVRSF]
    set di := d - 2 ^ BH.length
    have hx : ∀ j, 1 ≤ j → j ≤ 2 → A ((vRSF B O di).query + j) = a (qcI B.length di + j) := by
      intro j h1 h2
      rw [ha (qcI B.length di + j) (by omega) (by simp [qcO]; omega), idxO, if_neg (by omega), hq]
      congr 2; omega
    have hc : vrsCheck B O BH OH u a (qcI B.length di) =
        decide (A ((vRSF B O di).query + 1) = zFast BH (getRandElt B O (u.take B.length) + OH) *
          A ((vRSF B O di).query + 2)) := by
      rw [vrsCheck, hx 1 le_rfl (by omega), hx 2 (by omega) le_rfl]
    rw [hc, Bool.and_comm]
    congr 1
    by_cases ht : trivB B.length di = true
    · rw [if_pos ht]; exact (vRSF_triv B O di ht).2 u A
    · rw [if_neg ht]
      refine vRSF_D_congr B O di u (fun i h1 h2 => ?_)
      have hi : i ≤ qcI B.length di := by simp only [qcI, ht, Bool.false_eq_true, ↓reduceIte]; exact hq ▸ h2
      have := ha i h1 (by simp only [qcO]; omega)
      rw [idxO, if_pos hi] at this
      exact this.symm

/-- **The query at an effective position** (what the query machine computes). -/
theorem outV_Q_eff (v : Bool) (B : List F) (O : F) (BH : List F) (OH : F) (d : ℕ) (u : List Bool) (k : ℕ)
    (hk1 : 1 ≤ k) (hk : k ≤ qcO v B.length (innD v BH.length d)) :
    (outV v B O BH OH d).Q u (idxO B.length (innD v BH.length d) k) =
      if k ≤ qcI B.length (innD v BH.length d) then
        ((vRSF B O (innD v BH.length d)).Q u k).map fun j => (if v then 2 ^ B.length else 0) + j
      else some ((if k = qcI B.length (innD v BH.length d) + 2 then 2 ^ B.length else 0) +
        (1 + bitsValue (u.take B.length))) := by
  have hq := (vRSF_params B O (innD v BH.length d)).1
  by_cases hle : k ≤ qcI B.length (innD v BH.length d)
  · rw [idxO, if_pos hle, if_pos hle]
    have hn : ¬ trivB B.length (innD v BH.length d) = true := by
      intro h; simp only [qcI, h, if_true] at hle; omega
    have hkq : k ≤ (vRSF B O (innD v BH.length d)).query := by
      rw [hq]; simpa [qcI, hn] using hle
    cases v
    · simp [outV, innD]
    · simp only [outV, vVRSF, innD, ↓reduceIte] at hkq ⊢
      rw [if_pos ⟨hk1, hkq⟩]
  · rw [idxO, if_neg hle, if_neg hle]
    cases v
    · simp only [qcO, Bool.false_eq_true, ↓reduceIte] at hk; omega
    · simp only [qcO, innD, ↓reduceIte] at hk hle
      simp only [outV, vVRSF, innD, ↓reduceIte] at hq ⊢
      rw [if_neg (by omega), hq]
      by_cases h1 : k = qcI B.length (d - 2 ^ BH.length) + 1
      · rw [if_pos (by omega), if_neg (by omega)]; simp
      · rw [if_neg (by omega), if_pos (by omega), if_pos (by omega)]

end NearCubicGates.Adapters.ShortPCP.Time
