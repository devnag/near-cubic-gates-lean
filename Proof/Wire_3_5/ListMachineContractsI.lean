import Proof.Wire_3_5.ListMachineContracts
import Proof.Wire_3_5.ListMachineInterp
import Proof.Wire_3_5.ListMachineEncoding
import Proof.Wire_3_5.FinalPassList

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.ListMachine
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.Lists NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Machine
open NearCubicWires.WireExponent3_5.ListMachine.Ref Finset

theorem evalP_eq (p : Poly) (ρ : ℕ → Bool) : Interp.evalP p ρ = F2Poly.eval p ρ := rfl

namespace ListTable
variable (T : ListTable)

/-- The binary width of `L + 1` (the load's `log₂(L+1)`). -/
def width : ℕ := Nat.clog 2 (T.L + 1)

theorem lt_two_pow_width : T.L < 2 ^ T.width :=
  Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_pow_clog (by norm_num) _)

/-- The state bit the printer interpolates: `P_s` at an input, through the final pass's fast report. -/
def stateBit (s : ℕ) (Z : List Bool) : Bool := decide (FinalPass.ListFast.listReportFast T.data Z = s)

/-- The printer's enumeration bound, computable from the windows in unary: `Σ_{j<J} 4W_j + 1 ≥ degreeBound`
(`degreeBound_le_dPrint`). The print does not depend on it (`Interp.interpPrint_congr`). -/
def dPrint : ℕ := ∑ j ∈ range T.J, 4 * T.data.W j + 1

/-- **The interpolation reference**: `P_0, …, P_M` printed from their values. -/
def printedI : List Poly :=
  (List.range (T.M + 1)).map fun s => Interp.interpPrint (T.stateBit s) T.L T.dPrint

theorem bitF2_inj {a b : Bool} (h : bitF2 a = bitF2 b) : a = b := by
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

/-- At an `L`-bit input the state bit is the value of the explicit expansion `stateRef`. -/
theorem stateBit_eq (hT : T.Nested) (s : ℕ) (hs : s ≤ T.M) (Z : List Bool) (hZ : Z.length = T.L) :
    T.stateBit s Z = F2Poly.eval (stateRef T.data T.L s) fun i => Z.getD i false := by
  set z : Fin T.L → Bool := fun i => Z[i.val]'(by rw [hZ]; exact i.isLt) with hz
  have hext : (fun i => Z.getD i false) = ext z := by
    funext i
    unfold ext
    split_ifs with hi
    · rw [List.getD_eq_getElem _ _ (by omega)]
    · rw [List.getD_eq_default _ _ (by omega)]
  have hofFn : List.ofFn z = Z := by
    apply List.ext_getElem (by simp [hZ])
    intro k h1 h2
    simp [hz]
  have he := stateRef_eval T.data hT T.L s z
  rw [hofFn] at he
  rw [hext]
  apply bitF2_inj
  rw [he]
  unfold stateBit
  have hiff := T.data.listStates_eq_one_iff Z s hs
  rw [FinalPass.ListFast.listReport_eq_fast] at hiff
  by_cases h : FinalPass.ListFast.listReportFast T.data Z = s
  · rw [decide_eq_true h, hiff.mpr h.symm]; rfl
  · rw [decide_eq_false h]
    have h1 : T.data.listStates Z s ≠ 1 := fun h' => h (hiff.mp h').symm
    have h0 : ∀ x : ZMod 2, x ≠ 1 → x = 0 := by decide
    rw [h0 _ h1]; rfl

theorem ell_bound (j : ℕ) : 2 ^ T.data.ell j - 1 ≤ 4 * T.data.W j := by
  rcases Nat.eq_zero_or_pos (T.data.ell j) with h0 | hpos
  · rw [h0]; simp
  · have hlt : 2 ^ (T.data.ell j - 1) < 2 * T.data.W j + 1 := by
      unfold ListData.ell at hpos ⊢
      have h1 : 1 < 2 * T.data.W j + 1 := by
        by_contra hc
        have : 2 * T.data.W j + 1 ≤ 1 := by omega
        have := Nat.clog_of_right_le_one (b := 2) this
        omega
      exact Nat.pow_pred_clog_lt_self (by norm_num) h1
    have e : 2 ^ T.data.ell j = 2 * 2 ^ (T.data.ell j - 1) := by
      rw [← pow_succ']; congr 1; omega
    omega

/-- The degree bound in the windows: `Σ_{j<J}(H_j − 1) ≤ Σ_{j<J} 4W_j`. -/
theorem degreeBound_le : T.degreeBound ≤ ∑ j ∈ range T.J, 4 * T.data.W j :=
  Finset.sum_le_sum fun j _ => T.ell_bound j

theorem degreeBound_le_dPrint : T.degreeBound ≤ T.dPrint := by
  unfold dPrint; have := T.degreeBound_le; omega

theorem length_pointOf (L : ℕ) (U : List ℕ) : (Interp.pointOf L U).length = L := by simp [Interp.pointOf]

/-- **The interpolation reference meets `c2d`'s error field** on every admissible table (the verified consumer
statement `T.Correct`, now for `printedI`). -/
theorem printedI_correct (hT : T.Nested) : T.Correct T.printedI := by
  refine ⟨by simp [printedI], fun s hs => ?_⟩
  have hget : T.printedI.getD s [] = Interp.interpPrint (T.stateBit s) T.L T.dPrint := by
    unfold printedI
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
    rfl
  rw [hget]
  obtain ⟨hdeg, hat⟩ := stateRef_size T.data T.L s
  have hf := fun U => T.stateBit_eq hT s hs _ (length_pointOf T.L U)
  refine ⟨fun z => ?_, ?_, ?_,
    Interp.length_interpPrint_le (T.stateBit s) T.L T.dPrint (stateRef T.data T.L s) T.degreeBound hdeg hat hf⟩
  · have hev := Interp.interpPrint_eval (T.stateBit s) T.L T.dPrint (stateRef T.data T.L s)
      (fun m hm => (hdeg m hm).trans T.degreeBound_le_dPrint) hat hf (ext z)
    rw [evalP_eq, evalP_eq] at hev
    rw [hev]
    exact stateRef_eval T.data hT T.L s z
  · intro S hS
    obtain ⟨m, hm, hmS⟩ := Interp.interpPrint_support _ _ _ _ hat hf hS
    exact (Interp.length_le_of_nodup_pairwise (Interp.mem_monos (List.mem_of_mem_filter hS)).1 hmS).trans
      (hdeg m hm)
  · intro S hS
    exact (Interp.mem_monos (List.mem_of_mem_filter hS)).2.1

/-! ## The load and the description size -/

/-- **The printer's load**: `2^{psiC2d}` bounds the `(L+1)^{d'}·2^{d'}` interpolation steps (`d' = dPrint`). -/
def psiC2d : ℕ := T.dPrint * (T.width + 1)

/-- **The load in the table's parameters** (for the assembly's `psiC2d ≤ cpsi·Ψ` link):
`(Σ_{j<J} 4W_j + 1)·(⌈log₂(L+1)⌉ + 1)`. -/
theorem psiC2d_eq : T.psiC2d = (∑ j ∈ range T.J, 4 * T.data.W j + 1) * (Nat.clog 2 (T.L + 1) + 1) := rfl

end ListTable

/-! ## The contract -/

def polysWord (out : List Poly) : List Bool := out.flatMap (fun p => true :: Rec.polyWord p) ++ [false]

def c2dI (E : Envelope) (coef : ℕ) : MachineContract E where
  Req := ListTable
  input := fun T => NearCubicWires.RepairOrdinary.frame (encodeTable T)
  pre := ListTable.Nested
  Out := List Poly
  ref := ListTable.printedI
  encode := polysWord
  cls := .preprocessing
  q := fun T => (encodeTable T).length
  k := fun _ => 0
  psi := ListTable.psiC2d
  coef := coef
  errSpec := fun T out => T.Correct out

/-- The error half of `Certified (c2dI E coef)`. -/
theorem c2dI_err (E : Envelope) (coef : ℕ) :
    ∀ T, (c2dI E coef).pre T → (c2dI E coef).errSpec T ((c2dI E coef).ref T) :=
  fun T hT => T.printedI_correct hT

end NearCubicWires.WireExponent3_5.ListMachine
