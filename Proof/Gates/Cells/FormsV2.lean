import Proof.Gates.Cells.FormsV

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace NearCubicGates.Close.Cells

open NearCubicWires NearCubicGates
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter
open NearCubicGates.Close.CounterMachine

variable {C : Ctx}

theorem circ_idx {n : ℕ} (Cc : NCircuit n) (L R0 : List ℕ) (base : ℕ) (hb : L.drop base = circN Cc ++ R0) :
    base + 1 + Cc.gates.length * (2 * n + 3) + 1 + 2 * Cc.coeffs.length + 1 + Cc.table.length ≤ L.length := by
  have h := drop_eq_len hb (by simp [circN])
  simp only [circN, List.length_append, List.length_singleton, flatMap_intN_length, flatMap_gateN_length,
    List.length_map] at h
  omega

/-- The cost bound of one role (kept opaque so that linear arithmetic treats it as an atom). -/
@[irreducible] def roleCost (L n : ℕ) : ℕ := 300 * (L + 1) * (L + n + 1)

theorem roleCost_eq (L n : ℕ) : roleCost L n = 300 * (L + 1) * (L + n + 1) := by unfold roleCost; rfl

section V
variable {B1 B2 cT : ℕ} (c : Call) (p : Params) (wt : Wit c.n) (hadm : c.Admitted B1 B2)
  (hs : Spec cT (header c) p) (w : List Bool) (hw : decodeWitness c p w = some wt)

include hadm hs hw in
/-- **One role at the value level.** -/
theorem roleP_val (i Big : ℕ) (hBig : ∀ x ∈ cellN c p wt, natBitLength x ≤ Big)
    (hWd : 3 * Big + 6 * c.n + 20 ≤ C.Wd) (r : Role c) (e : DS VV MM) (hc : Cst e)
    (hN : e.ram sN = cellN c p wt) (hzb : e.ram sZb = zbL wt.I i) (hz0 : e.rc sZb = 0)
    (hn : e.env gN = c.n) (hR : e.env fR = r.val) (hRC : e.env gRC = roleCount c.kind) (hJ : e.env gJ = p.J)
    (base : ℕ) (R0 : List ℕ) (hbase : (cellN c p wt).drop base = circN (circ c r.val) ++ R0)
    (hGS : e.env xGS = base + 1) (hG : e.env xG = (circ c r.val).gates.length)
    (hCS : e.env xCS = base + 1 + (circ c r.val).gates.length * (2 * c.n + 3) + 1)
    (hNC : e.env xNC = (circ c r.val).coeffs.length)
    (hWS : e.env xWS = iOm (cellN c p wt) + 1 + fld (cellN c p wt) (iOm (cellN c p wt)))
    (hFS : e.env xFS = iPsi (cellN c p wt) + 24 + nPr (cellN c p wt))
    (E0 Pre : List ℕ) (hE : e.ram sE = wr E0 0 Pre) (hEc : e.rc sE = Pre.length)
    (X0 PreX : List ℕ) (hX : e.ram sX = wr X0 0 PreX) (hXc : e.rc sX = PreX.length) :
    Hs C roleP e (e.rc sN + e.rc sB + e.rc sG + roleCost (cellN c p wt).length c.n) (fun b =>
      b.ram sE = wr E0 0 (Pre ++ (List.finRange p.J).flatMap fun j => pairOf (ctr c p wt (cellOf wt.I i) (r, j))) ∧
      b.rc sE = Pre.length + 2 * p.J ∧
      b.ram sX = wr X0 0 (PreX ++ (pairOf (stageForm c wt r.val (p.J - 1)
        (extend wt.I (cellOf wt.I i) (zeroPoint wt.I))) ++
        pairOf (scoreForm c r.val (extend wt.I (cellOf wt.I i) (zeroPoint wt.I))))) ∧
      b.rc sX = PreX.length + 4 ∧ b.ram sN = e.ram sN ∧ b.rc sB = 0 ∧
      (b.ram sB).length ≤ max (e.ram sB).length (cellN c p wt).length ∧
      (b.ram sG).length ≤ max (e.ram sG).length (2 * p.J) ∧ 2 * p.J ≤ (b.ram sG).length ∧ b.rc sG = 2 * p.J ∧
      b.rc sN = iPsi (cellN c p wt) + 24 + nPr (cellN c p wt) + p.J ∧ Agr e b roleMs roleT) := by
  have hwf := circ_wf c hadm r.val
  have hgc : (circ c r.val).gates.length = (circ c r.val).coeffs.length := hwf.1
  have hrc : roleCount c.kind = 1 ∨ roleCount c.kind = 2 := by cases c.kind <;> simp [roleCount]
  have hJ1 := hs.J_pos
  have hnf := nfactors_eq c p wt hadm hs w hw
  have hr := r.isLt
  obtain ⟨-, f2, -, f4, -, -, -⟩ := circ_fields (circ c r.val) (cellN c p wt) R0 base hbase
  have hix := circ_idx (circ c r.val) (cellN c p wt) R0 base hbase
  have hg3 : (circ c r.val).gates.length ≤ (circ c r.val).gates.length * (2 * c.n + 3) :=
    Nat.le_mul_of_pos_right _ (by omega)
  have hdb := Call.drop_blocks c p wt
  have hwsl := drop_eq_len hdb (by simpa using blocksAll_ne c p wt hadm hs w hw)
  simp only [List.length_append, List.length_nil, add_zero] at hwsl
  have hdf := Call.drop_factors c p wt
  have hfsl := drop_eq_len hdf (by simp)
  simp only [List.length_append, List.length_singleton, List.length_cons, List.length_nil] at hfsl
  have hLW := sz_len c p wt hadm hs w hw Big C.Wd hWd
  have hnW : c.n < 2 ^ C.Wd := sz_big c p wt Big C.Wd hBig hWd (n_mem c p wt)
  have hGW : (circ c r.val).gates.length < 2 ^ C.Wd := sz_big c p wt Big C.Wd hBig hWd (gates_len_mem c p wt r.val)
  have hJW : p.J < 2 ^ C.Wd := sz_big c p wt Big C.Wd hBig hWd (J_mem c p wt)
  have hFB1 : p.factors.length ≤ 2 ^ Big := (lt_of_big c p wt hBig (nfactors_mem c p wt)).le
  have hspec := roleP_spec (C := C) e hc hn hnW (circ c r.val).gates _ (by rw [hN, hGS]; exact f2)
    (by rw [hN, hGS]; omega) (by rw [hGS]; omega) hG hGW (zbL wt.I i) hzb (zbL_length c wt i) hz0
    (fun g hg => sz_gate c p wt Big C.Wd hBig hWd r.val g hg)
    (circ c r.val).coeffs _ (by rw [hN, hCS]; exact f4) (by rw [hN, hCS]; omega) (by rw [hCS]; omega) hNC hgc
    (sz_coeffs c p wt Big C.Wd hBig hWd r.val)
    (roleCount c.kind) r.val hrc hr hR hRC p.J hJ hJW wt.coef [] (by rw [hN, hWS]; exact hdb)
    (by rw [hN, hWS]; omega) (by rw [hWS]; omega)
    (fun s hs' => by have := sz_cf c p wt w hw s r.val hs' hr; omega)
    (cellN c p wt).length (fun s hs' ρ hρ => (sz_cf c p wt w hw s ρ hs' hρ).trans (coeffs_le_len c p wt ρ)) hLW
    (fun s hs' ρ hρ => lt_of_le_of_lt (sz_coef c p wt hadm hs w hw Big hBig s ρ hs' hρ)
      (lt_of_le_of_lt (Nat.le_add_right _ _) (sz_kb c Big C.Wd hWd)))
    p.factors ([p.A, p.Lambda] ++ witN c p wt) (by rw [hN, hFS]; exact hdf) (by omega) (by rw [hFS]; omega)
    (2 ^ Big) (2 ^ (2 * Big)) hFB1 (fun f hf => (lt_of_big c p wt hBig (factor_mem c p wt hf)).le)
    (fun s hs' => sz_coef c p wt hadm hs w hw Big hBig s r.val hs' hr) (sz_kb c Big C.Wd hWd) E0 Pre hE hEc X0 PreX hX hXc
  have hgb : (circ c r.val).gates.map (gbit · (zbL wt.I i)) = gbOf c wt i r.val := rfl
  rw [hgb, ePairs_eq c p wt i r, kx_eq c p wt i r hJ1, hGS, hCS, hWS, hFS] at hspec
  refine Hs.mono hspec ?_ ?_
  · rw [roleCost_eq]
    set L := (cellN c p wt).length
    set G := (circ c r.val).gates.length
    set Cn := (circ c r.val).coeffs.length
    set BA := (blocksAll wt.coef (roleCount c.kind) p.J).length
    have hGL : G ≤ L := by omega
    have hCL : Cn ≤ L := by omega
    have hJL : p.J ≤ L := by omega
    have m1 : G * (15 * c.n + 28) ≤ L * (15 * c.n + 28) := Nat.mul_le_mul_right _ hGL
    have m2 : G * (2 * c.n + 3) ≤ L * (2 * c.n + 3) := Nat.mul_le_mul_right _ hGL
    have m3 : p.J * (30 * L + 40 + 4) ≤ L * (30 * L + 40 + 4) := Nat.mul_le_mul_right _ hJL
    nlinarith
  · rintro b ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11⟩
    refine ⟨b1, b2, b3, b4, b5, b7, ?_, ?_, ?_, b9, b10, b11⟩
    · have hGL' : (circ c r.val).gates.length ≤ (cellN c p wt).length := by omega
      rw [b6]
      simp only [gbOf, List.length_append, List.length_drop, List.length_map]
      omega
    · rw [b8, wr_length_eq, kPairs_length]
    · rw [b8, wr_length_eq, kPairs_length]; omega

end V

end NearCubicGates.Close.Cells
