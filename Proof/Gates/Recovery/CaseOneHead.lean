import Proof.Gates.Recovery.CaseOneProg

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicGates.Close.Recovery.CaseOneMachine

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP NearCubicGates.Close.Recovery.HTParts
open NearCubicGates.Close.CheckedPCPP.ClauseFront (named dblW dblW_exec)

/-- The header written by `headW`. -/
def hdr (q : ℕ) : List Bool := (q.bits.flatMap fun b => marks [true, b]) ++ marks [false]

theorem hdr_length (q : ℕ) : (hdr q).length = 4 * q.bits.length + 2 := by
  unfold hdr
  have : ∀ l : List Bool, (l.flatMap fun b => marks [true, b]).length = 4 * l.length := by
    intro l; induction l with
    | nil => simp
    | cons b l ih => simp [marks] at ih ⊢; omega
  simp [this, marks]; ring

/-- The cost of the head. -/
def headCost (q : ℕ) : ℕ := 100 * (q + 1) * (2 ^ q + 1)

theorem bits_len_le (v : ℕ) : v.bits.length ≤ v := by
  have e := Nat.size_eq_bits_len v
  have := Nat.size_le.mpr (Nat.lt_two_pow_self (n := v))
  omega

/-- **The head.** -/
theorem head_exec (tA cap : ℕ) (word addr : List Bool) (q : ℕ) (hcap : 4 * 2 ^ q + 8 * q + 16 ≤ cap) :
    ∃ τ n, WXExec cap (headW tA) (initCaseOne tA word addr q) τ n ∧ n ≤ headCost q ∧
      τ.st (X tA) = hdr q ∧ τ.sh (X tA) = (hdr q).length ∧ τ.val opX = (hdr q).length ∧
      τ.val rK = 2 ^ q ∧ τ.val SC = 0 ∧ τ.cell = false ∧
      (∀ i, i ≠ X tA → τ.st i = (initCaseOne tA word addr q).st i ∧ τ.sh i = 0) := by
  set s0 := initCaseOne tA word addr q with hs0
  have z : ∀ r : Fin 16, s0.val r = 0 := fun _ => rfl
  have h0 : ∀ i, s0.sh i = 0 := fun _ => rfl
  have hQ : s0.st (Q tA) = List.replicate q true := by simp [hs0, initCaseOne, threeWords]
  have hX : s0.st (X tA) = [] := by simp [hs0, initCaseOne]
  have dQX : Q tA ≠ X tA := by cdst
  have dXQ : X tA ≠ Q tA := by cdst
  have hq2 : q < 2 ^ q := Nat.lt_two_pow_self
  have hbl := bits_len_le q
  have fm : ∀ l : List Bool, (l.flatMap fun _ => ([] : List Bool)) = [] := by
    intro l; induction l with
    | nil => rfl
    | cons a l ih => simp [ih]
  -- 1. rQ := q
  have x1 := oneLoop_spec (cap := cap) (src := Q tA) (dst := X tA) (OP := opX) (SC := rQ) dQX (by decide)
    (emits_none cap) [] rfl q [] s0 (by rw [hQ]; simp) (by rw [h0]; rfl) (by rw [hX, h0]; rfl)
    (by rw [z]; simp) (by rw [z]; omega)
  obtain ⟨s1, hs1, e1⟩ := named (WXExec.wm x1)
  have hs1' : s1 = (s0.seth (Q tA) q).setv rQ q := by
    rw [hs1]; simp [adv, appendO_nil, h0, z, fm]
  clear hs1
  -- 2. rT1 := q
  have x2 := addR_spec cap (A := rQ) (B := rT1) (T := rT) (by decide) (by decide) (by decide) s1
    (by simp (config := { decide := true }) [hs1', Function.update_apply, z])
    (by simp (config := { decide := true }) [hs1', Function.update_apply, z]; omega)
  obtain ⟨s2, hs2, e2⟩ := named x2
  -- 3. rewind Q
  have x3 := wrewind_spec (cap := cap) (Q tA) rT1 q s2
    (by simp (config := { decide := true }) [hs2, hs1', Function.update_apply, z])
    (by simp (config := { decide := true }) [hs2, hs1', Function.update_apply, z]; omega)
  obtain ⟨s3, hs3, e3⟩ := named (WXExec.wm x3)
  have hs3' : s3 = s0.setv rQ q := by
    rw [hs3, hs2, hs1']
    apply WState.eq
    · funext j
      by_cases j1 : j = Q tA
      · subst j1; simp [Function.update_apply, h0]
      · simp [Function.update_apply, j1]
    · rfl
    · funext r
      by_cases r1 : r = rT1
      · subst r1; simp (config := { decide := true }) [Function.update_apply, z]
      · simp (config := { decide := true }) [Function.update_apply, r1]
    · rfl
  clear hs3 hs2
  -- 4. rK := 1
  have x4 := WXExec.inc (cap := cap) rK s3 (by simp (config := { decide := true }) [hs3', Function.update_apply, z]; omega)
  obtain ⟨s4, hs4, e4⟩ := named x4
  -- 5. rE := q
  have x5 := addR_spec cap (A := rQ) (B := rE) (T := rT) (by decide) (by decide) (by decide) s4
    (by simp (config := { decide := true }) [hs4, hs3', Function.update_apply, z])
    (by simp (config := { decide := true }) [hs4, hs3', Function.update_apply, z]; omega)
  obtain ⟨s5, hs5, e5⟩ := named x5
  -- 6. rK := 2^q
  have x6 := dblW_exec (cap := cap) (M := rK) (K := rE) (Q := rQd) (T := rTd) (by decide) (2 ^ q) (by omega) q s5
    (by simp (config := { decide := true }) [hs5, hs4, hs3', Function.update_apply, z]) (by omega)
    (by simp (config := { decide := true }) [hs5, hs4, hs3', Function.update_apply, z])
    (by simp (config := { decide := true }) [hs5, hs4, hs3', Function.update_apply, z])
    (by simp (config := { decide := true }) [hs5, hs4, hs3', Function.update_apply, z])
  obtain ⟨s6, hs6, e6⟩ := named x6
  have v4 : s4.val rQ = q := by simp (config := { decide := true }) [hs4, hs3', Function.update_apply]
  have hs6' : s6 = (s0.setv rQ q).setv rK (2 ^ q) := by
    rw [hs6, hs5, hs4, hs3']
    apply WState.eq <;> try rfl
    funext r
    by_cases r1 : r = rK
    · subst r1; simp (config := { decide := true }) [Function.update_apply, z]
    · by_cases r2 : r = rE
      · subst r2; simp (config := { decide := true }) [Function.update_apply, z]
      · simp (config := { decide := true }) [Function.update_apply, r1, r2]
  clear hs6 hs5 hs4
  -- 7. rB0 := q
  have x7 := addR_spec cap (A := rQ) (B := rB0) (T := rT) (by decide) (by decide) (by decide) s6
    (by simp (config := { decide := true }) [hs6', Function.update_apply, z])
    (by simp (config := { decide := true }) [hs6', Function.update_apply, z]; omega)
  obtain ⟨s7, hs7, e7⟩ := named x7
  -- 8. the bits of q
  have x8 := bitsQ_exec (cap := cap) (X := rB0) (H := rH) (B := rB) (OP := opX) (dst := X tA) (by decide) q (by omega)
    q s7 le_rfl
    (by simp (config := { decide := true }) [hs7, hs6', Function.update_apply, z])
    (by simp (config := { decide := true }) [hs7, hs6', Function.update_apply, z])
    (by simp (config := { decide := true }) [hs7, hs6', Function.update_apply, z])
    (by simp (config := { decide := true }) [hs7, hs6', h0, hX])
    (by simp (config := { decide := true }) [hs7, hs6', Function.update_apply, z]; omega)
  obtain ⟨s8, hs8, e8⟩ := named x8
  -- 9. marks [false]
  have x9 := Codec.emitMarks_spec (cap := cap) (X tA) opX [false] s8
    (by rw [hs8]; simp [appendO, hs7, hs6', h0, hX])
    (by rw [hs8]; simp (config := { decide := true }) [appendO, hs7, hs6', Function.update_apply, z, hdr_length]
        have := hdr_length q; unfold hdr at this; simp [marks] at this; omega)
  obtain ⟨s9, hs9, e9⟩ := named (WXExec.wm x9)
  have whole := WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4 (WXExec.seq e5 (WXExec.seq e6
    (WXExec.seq e7 (WXExec.seq e8 e9)))))))
  refine ⟨s9, _, whole, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- cost
    have v1 : s1.val rQ = q := by simp (config := { decide := true }) [hs1', Function.update_apply]
    have v6 : s6.val rQ = q := by simp (config := { decide := true }) [hs6', Function.update_apply]
    have c1 : q * (25 * 2 ^ q + 10) = 25 * (q * 2 ^ q) + 10 * q := by ring
    have h3 : q * q ≤ q * 2 ^ q := Nat.mul_le_mul_left _ hq2.le
    have c2 : q.bits.length * (12 * q + 60) ≤ 12 * (q * 2 ^ q) + 60 * q := by
      have := Nat.mul_le_mul_right (12 * q + 60) hbl
      nlinarith
    have c3 : headCost q = 100 * (q * 2 ^ q) + 100 * q + 100 * 2 ^ q + 100 := by unfold headCost; ring
    rw [v1, v4, v6, c1, c3]
    simp only [List.length_singleton]
    omega
  · rw [hs9, hs8]; simp [appendO, hs7, hs6', hX, hdr]
  · rw [hs9, hs8]; simp [appendO, hs7, hs6', h0, hdr]
  · rw [hs9, hs8]; simp (config := { decide := true }) [appendO, hs7, hs6', Function.update_apply, z, hdr]
  · rw [hs9, hs8]; simp (config := { decide := true }) [appendO, hs7, hs6', Function.update_apply, z]
  · rw [hs9, hs8]; simp (config := { decide := true }) [appendO, hs7, hs6', Function.update_apply, z]
  · rw [hs9, hs8]; simp [appendO, hs7, hs6', hs0, initCaseOne]
  · intro i hi
    rw [hs9, hs8]
    simp [appendO, hs7, hs6', Function.update_apply, hi, h0]
end NearCubicGates.Close.Recovery.CaseOneMachine
