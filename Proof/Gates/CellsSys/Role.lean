import Proof.Gates.CellsSys.Bnd

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000

namespace NearCubicGates.Close.Cells.SystemsPhase

open NearCubicGates.Close.Cells
open NearCubicWires NearCubicGates NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter

variable {C : Ctx}

theorem length_flatMap_const {α β : Type} (l : List α) (f : α → List β) (k : ℕ) (h : ∀ a ∈ l, (f a).length = k) :
    (l.flatMap f).length = l.length * k := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.flatMap_cons, List.length_append, h a (by simp), ih (fun b hb => h b (by simp [hb])),
      List.length_cons]
    ring

section Len
variable (c : Call) (p : Params) (wt : Wit c.n) (y : Cells wt.I)

theorem tailL_length : (tailL p).length = p.J := by simp [tailL]

theorem ctrL_length : (ctrL c p wt y).length = roleCount c.kind * (p.J * 2) := by
  unfold ctrL
  rw [length_flatMap_const _ _ (p.J * 2) (fun r _ => by
    rw [length_flatMap_const _ _ 2 (fun j _ => by simp [pairOf])]; simp)]
  simp

theorem kxL_length : (kxL c p wt y).length = roleCount c.kind * 4 := by
  unfold kxL
  rw [length_flatMap_const _ _ 4 (fun r _ => by simp [pairOf])]
  simp

end Len

/-! ## Digit-sum bounds -/

theorem accPf_le (PL EL : List ℕ) (r J nD w t k V : ℕ) (hV : ∀ x ∈ PL, x ≤ V) (hVE : ∀ x ∈ EL, x ≤ V)
    (hwV : w ≤ V) (hw1 : 1 ≤ w) : accPf PL EL r J nD w t k ≤ k * (V * (2 * V + 2)) := by
  unfold accPf
  calc ∑ j' ∈ Finset.range k, PL.getD j' 0 * (EL.getD (2 * (r * J + j')) 0 + 1 + dig w nD t (r * J + j'))
      ≤ ∑ _j' ∈ Finset.range k, V * (2 * V + 2) := by
        apply Finset.sum_le_sum
        intro j' _
        have h1 : PL.getD j' 0 ≤ V := by
          rcases Nat.lt_or_ge j' PL.length with h | h
          · rw [List.getD_eq_getElem _ _ h]; exact hV _ (List.getElem_mem _)
          · rw [List.getD_eq_default _ _ h]; omega
        have h2 : EL.getD (2 * (r * J + j')) 0 ≤ V := by
          rcases Nat.lt_or_ge (2 * (r * J + j')) EL.length with h | h
          · rw [List.getD_eq_getElem _ _ h]; exact hVE _ (List.getElem_mem _)
          · rw [List.getD_eq_default _ _ h]; omega
        have h3 : dig w nD t (r * J + j') < w := Nat.mod_lt _ (by omega)
        exact Nat.mul_le_mul h1 (by omega)
    _ = k * (V * (2 * V + 2)) := by simp

theorem accNf_le (PL EL : List ℕ) (r J hE k V : ℕ) (hV : ∀ x ∈ PL, x ≤ V) (hVE : ∀ x ∈ EL, x ≤ V)
    (hEV : hE ≤ V) : accNf PL EL r J hE k ≤ k * (V * (2 * V + 2)) := by
  unfold accNf
  calc ∑ j' ∈ Finset.range k, PL.getD j' 0 * (EL.getD (2 * (r * J + j') + 1) 0 + hE)
      ≤ ∑ _j' ∈ Finset.range k, V * (2 * V + 2) := by
        apply Finset.sum_le_sum
        intro j' _
        have h1 : PL.getD j' 0 ≤ V := by
          rcases Nat.lt_or_ge j' PL.length with h | h
          · rw [List.getD_eq_getElem _ _ h]; exact hV _ (List.getElem_mem _)
          · rw [List.getD_eq_default _ _ h]; omega
        have h2 : EL.getD (2 * (r * J + j') + 1) 0 ≤ V := by
          rcases Nat.lt_or_ge (2 * (r * J + j') + 1) EL.length with h | h
          · rw [List.getD_eq_getElem _ _ h]; exact hVE _ (List.getElem_mem _)
          · rw [List.getD_eq_default _ _ h]; omega
        exact Nat.mul_le_mul h1 (by omega)
    _ = k * (V * (2 * V + 2)) := by simp

/-- `J·V(2V+2) ≤ 2^{J + 2E + 2}` for `V = 2^E`. -/
theorem jvv_le (J E : ℕ) : J * (2 ^ E * (2 * 2 ^ E + 2)) ≤ 2 ^ (J + 2 * E + 2) := by
  have hJ : J ≤ 2 ^ J := Nat.lt_two_pow_self.le
  have h1 : 2 * 2 ^ E + 2 ≤ 2 ^ (E + 2) := by
    have : 1 ≤ 2 ^ E := Nat.one_le_two_pow
    rw [pow_add]; omega
  calc J * (2 ^ E * (2 * 2 ^ E + 2)) ≤ 2 ^ J * (2 ^ E * 2 ^ (E + 2)) :=
        Nat.mul_le_mul hJ (Nat.mul_le_mul_left _ h1)
    _ = 2 ^ (J + 2 * E + 2) := by rw [← pow_add, ← pow_add]; ring_nf

/-! ## Small programs -/

def normB : St VV MM :=
  .ite (.lt lP lN) (.seq (.op (.sub lN lP)) (.op (.zero lP))) (.seq (.op (.sub lP lN)) (.op (.zero lN)))

theorem normB_spec (a : DS VV MM) (P N : ℕ) (h1 : a.env lP = P) (h2 : a.env lN = N) :
    Hs C normB a 4 (fun b => b.env lP = (zOf P N).toNat ∧ b.env lN = (-zOf P N).toNat ∧ Fr a b [lP, lN] ∧
      Same a b) := by
  refine Hs.mono (Hs.ite (show lP ≠ lN by decide) (fun he => ?_) (fun he => ?_)) (le_refl 4) (fun _ h => h)
  · have hlt : P < N := by simpa [Cnd.eval, h1, h2] using he
    refine Hs.mono (Hs.seq (t1 := 1) (t2 := 1) (o_sub lN lP a (by decide) (by rw [h1, h2]; omega))
      (fun e ⟨e1, e2, e3⟩ => ?_)) (by norm_num) (fun _ h => h)
    refine Hs.mono (o_zero lP e) le_rfl ?_
    rintro g ⟨g1, g2, g3⟩
    have hn := norm_neg P N hlt
    refine ⟨by rw [g1, hn.1], ?_, Fr.trans (e2.weaken (by decide)) (g2.weaken (by decide)), Same.trans e3 g3⟩
    simp (disch := decide) only [g2.ev]; rw [e1, h1, h2, hn.2]
  · have hle : ¬ P < N := by simpa [Cnd.eval, h1, h2] using he
    refine Hs.mono (Hs.seq (t1 := 1) (t2 := 1) (o_sub lP lN a (by decide) (by rw [h1, h2]; omega))
      (fun e ⟨e1, e2, e3⟩ => ?_)) (by norm_num) (fun _ h => h)
    refine Hs.mono (o_zero lN e) le_rfl ?_
    rintro g ⟨g1, g2, g3⟩
    have hn := norm_pos P N hle
    refine ⟨?_, by rw [g1, hn.2], Fr.trans (e2.weaken (by decide)) (g2.weaken (by decide)), Same.trans e3 g3⟩
    simp (disch := decide) only [g2.ev]; rw [e1, h1, h2, hn.1]

def setW : St VV MM := .ite (.eq rI vZ) (.op (.copy Wv vTW0)) (.op (.copy Wv vTW1))

theorem setW_spec (a : DS VV MM) (hc : Cst a) (r W0 W1 : ℕ) (hr : a.env rI = r) (h0 : a.env vTW0 = W0)
    (h1 : a.env vTW1 = W1) :
    Hs C setW a 2 (fun b => b.env Wv = (if r = 0 then W0 else W1) ∧ Fr a b [Wv] ∧ Same a b) := by
  refine Hs.ite (show rI ≠ vZ by decide) (fun he => ?_) (fun he => ?_)
  · have : r = 0 := by simpa [Cnd.eval, hr, hc.z] using he
    refine Hs.mono (o_copy Wv vTW0 a (by decide)) le_rfl ?_
    rintro g ⟨g1, g2, g3⟩
    exact ⟨by rw [g1, h0, if_pos this], g2, g3⟩
  · have : r ≠ 0 := by simpa [Cnd.eval, hr, hc.z] using he
    refine Hs.mono (o_copy Wv vTW1 a (by decide)) le_rfl ?_
    rintro g ⟨g1, g2, g3⟩
    exact ⟨by rw [g1, h1, if_neg this], g2, g3⟩

/-! ## The box of one role -/

def boxR1 : St VV MM := .seq accL (.seq kxB ctrB)
def boxR2 : St VV MM := .seq setW (.seq loB (.seq normB (.seq hiB lenB)))
def boxR : St VV MM := .seq boxR1 boxR2

def boxT : List (Fin VV) :=
  [jI, iI, q3, pw, f1, c1, f2, dV, ix, f3, q1, q2, accP, accN, c0, vJ, kP, kN, xP, xN, Cp, Cn, Wv, q4, lP, lN,
    hP, hN, nL]

/-- The cost of one role's box, for any `J` (two roles at most). -/
def boxCost (J : ℕ) : ℕ := accCost J (2 * J) J (4 * J) + 24 * 8 + 300

theorem Keep.ev {a0 a : DS VV MM} (hK : Keep a0 a) {x : Fin VV} (h : x.val < 3 ∨ (20 ≤ x.val ∧ x.val < 50))
    (hx : x ≠ vCnt) : a.env x = a0.env x := hK.env x h hx

theorem Keep.cst {S : SolveMachine} {c : Call} {p : Params} {wt : Wit c.n} {y : Cells wt.I} {a0 a : DS VV MM}
    (h0 : SysPre S C c p wt y a0) (hK : Keep a0 a) : Cst a :=
  ⟨by rw [hK.ev (x := vZ) (by decide) (by decide)]; exact h0.cst.z,
   by rw [hK.ev (x := v1) (by decide) (by decide)]; exact h0.cst.one,
   by rw [hK.ev (x := v2) (by decide) (by decide)]; exact h0.cst.two⟩

theorem lt_two_pow_of {x k W : ℕ} (hx : x ≤ 2 ^ k) (hk : k < W) : x < 2 ^ W :=
  lt_of_le_of_lt hx (Nat.pow_lt_pow_right (by norm_num) hk)

end NearCubicGates.Close.Cells.SystemsPhase
