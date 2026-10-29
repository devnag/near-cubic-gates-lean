import SourceAdapters.Refuter.RMachEmit
import SourceAdapters.Refuter.RSearchLists
import SourceAdapters.Refuter.CNFDock

/-!
# The tape layout of R's two machines and the words R writes (input 7, R)

Paper anchor: (`lem:multitape-refuter` Steps 3–4: the queries and the search), 
(the records), (`cor:framed-refuter`: queries written in full).

One word-program bank serves both machines (`INIT`, `STEP`): `NS tc tT + 1` streams (`tc` the compiler's
tapes, `tT` the clock function's tapes, both blocks after 41 fixed streams), 16 registers.

`memWord`/`intWord` are the request words of join X5(b) (`CNFCompilationRequest.word`) for R's two query
kinds, written as concatenations of the pieces R emits; `memberRequest_word`/`intervalRequest_word` identify
them (at the lengths where records are valid, `machineIndex M + 2 + ⌊N/16⌋ ≤ N`).
-/

namespace NearCubicGates.Adapters.Refuter.RM

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicGates.Close.WordPrograms NearCubicGates.Adapters.Compile
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-! ## The layout -/

/-- `ns` of the bank: 41 fixed streams, then the compiler's `tc` tapes, then the clock function's `tT`. -/
abbrev NS (tc tT : ℕ) : ℕ := 40 + tc + tT

/-- The register count. -/
abbrev NR : ℕ := 16

section Layout
variable {tc tT : ℕ}

def sIN : Fin (NS tc tT + 1) := ⟨0, by unfold NS; omega⟩
def sOUT : Fin (NS tc tT + 1) := ⟨1, by unfold NS; omega⟩
def sDONE : Fin (NS tc tT + 1) := ⟨2, by unfold NS; omega⟩
def sANS : Fin (NS tc tT + 1) := ⟨3, by unfold NS; omega⟩
def sCODE : Fin (NS tc tT + 1) := ⟨4, by unfold NS; omega⟩
def sNU : Fin (NS tc tT + 1) := ⟨5, by unfold NS; omega⟩
def sGU : Fin (NS tc tT + 1) := ⟨6, by unfold NS; omega⟩
def sTU : Fin (NS tc tT + 1) := ⟨7, by unfold NS; omega⟩
def sMU : Fin (NS tc tT + 1) := ⟨8, by unfold NS; omega⟩
def sXU : Fin (NS tc tT + 1) := ⟨9, by unfold NS; omega⟩
def sZ : Fin (NS tc tT + 1) := ⟨10, by unfold NS; omega⟩
def sONE : Fin (NS tc tT + 1) := ⟨11, by unfold NS; omega⟩
def sSV : Fin (NS tc tT + 1) := ⟨12, by unfold NS; omega⟩
def sFF : Fin (NS tc tT + 1) := ⟨13, by unfold NS; omega⟩
def sLO : Fin (NS tc tT + 1) := ⟨14, by unfold NS; omega⟩
def sHI : Fin (NS tc tT + 1) := ⟨15, by unfold NS; omega⟩
def sFU : Fin (NS tc tT + 1) := ⟨16, by unfold NS; omega⟩
def sQ : Fin (NS tc tT + 1) := ⟨17, by unfold NS; omega⟩
def sTMP : Fin (NS tc tT + 1) := ⟨18, by unfold NS; omega⟩
def sP0 : Fin (NS tc tT + 1) := ⟨19, by unfold NS; omega⟩
def sP1 : Fin (NS tc tT + 1) := ⟨20, by unfold NS; omega⟩
def sP3 : Fin (NS tc tT + 1) := ⟨21, by unfold NS; omega⟩
def sELO : Fin (NS tc tT + 1) := ⟨22, by unfold NS; omega⟩
def sG : Fin (NS tc tT + 1) := ⟨23, by unfold NS; omega⟩
def sTL : Fin (NS tc tT + 1) := ⟨24, by unfold NS; omega⟩
def sLOG : Fin (NS tc tT + 1) := ⟨25, by unfold NS; omega⟩
def sTLI : Fin (NS tc tT + 1) := ⟨26, by unfold NS; omega⟩
def sXH : Fin (NS tc tT + 1) := ⟨27, by unfold NS; omega⟩
def sFIN : Fin (NS tc tT + 1) := ⟨28, by unfold NS; omega⟩

/-- The compiler's tape `j`. -/
def sC (j : Fin tc) : Fin (NS tc tT + 1) := ⟨41 + j.val, by unfold NS; omega⟩
/-- The clock function's tape `j`. -/
def sK (j : Fin tT) : Fin (NS tc tT + 1) := ⟨41 + tc + j.val, by unfold NS; omega⟩

@[simp] theorem sIN_val : (sIN (tc := tc) (tT := tT)).val = 0 := rfl
@[simp] theorem sOUT_val : (sOUT (tc := tc) (tT := tT)).val = 1 := rfl
@[simp] theorem sDONE_val : (sDONE (tc := tc) (tT := tT)).val = 2 := rfl
@[simp] theorem sANS_val : (sANS (tc := tc) (tT := tT)).val = 3 := rfl
@[simp] theorem sCODE_val : (sCODE (tc := tc) (tT := tT)).val = 4 := rfl
@[simp] theorem sNU_val : (sNU (tc := tc) (tT := tT)).val = 5 := rfl
@[simp] theorem sGU_val : (sGU (tc := tc) (tT := tT)).val = 6 := rfl
@[simp] theorem sTU_val : (sTU (tc := tc) (tT := tT)).val = 7 := rfl
@[simp] theorem sMU_val : (sMU (tc := tc) (tT := tT)).val = 8 := rfl
@[simp] theorem sXU_val : (sXU (tc := tc) (tT := tT)).val = 9 := rfl
@[simp] theorem sZ_val : (sZ (tc := tc) (tT := tT)).val = 10 := rfl
@[simp] theorem sONE_val : (sONE (tc := tc) (tT := tT)).val = 11 := rfl
@[simp] theorem sSV_val : (sSV (tc := tc) (tT := tT)).val = 12 := rfl
@[simp] theorem sFF_val : (sFF (tc := tc) (tT := tT)).val = 13 := rfl
@[simp] theorem sLO_val : (sLO (tc := tc) (tT := tT)).val = 14 := rfl
@[simp] theorem sHI_val : (sHI (tc := tc) (tT := tT)).val = 15 := rfl
@[simp] theorem sFU_val : (sFU (tc := tc) (tT := tT)).val = 16 := rfl
@[simp] theorem sQ_val : (sQ (tc := tc) (tT := tT)).val = 17 := rfl
@[simp] theorem sTMP_val : (sTMP (tc := tc) (tT := tT)).val = 18 := rfl
@[simp] theorem sP0_val : (sP0 (tc := tc) (tT := tT)).val = 19 := rfl
@[simp] theorem sP1_val : (sP1 (tc := tc) (tT := tT)).val = 20 := rfl
@[simp] theorem sP3_val : (sP3 (tc := tc) (tT := tT)).val = 21 := rfl
@[simp] theorem sELO_val : (sELO (tc := tc) (tT := tT)).val = 22 := rfl
@[simp] theorem sG_val : (sG (tc := tc) (tT := tT)).val = 23 := rfl
@[simp] theorem sTL_val : (sTL (tc := tc) (tT := tT)).val = 24 := rfl
@[simp] theorem sLOG_val : (sLOG (tc := tc) (tT := tT)).val = 25 := rfl
@[simp] theorem sTLI_val : (sTLI (tc := tc) (tT := tT)).val = 26 := rfl
@[simp] theorem sXH_val : (sXH (tc := tc) (tT := tT)).val = 27 := rfl
@[simp] theorem sFIN_val : (sFIN (tc := tc) (tT := tT)).val = 28 := rfl
@[simp] theorem sC_val (j : Fin tc) : (sC (tT := tT) j).val = 41 + j.val := rfl
@[simp] theorem sK_val (j : Fin tT) : (sK (tc := tc) j).val = 41 + tc + j.val := rfl

/-- Distinctness of layout streams. -/
macro "ds" : tactic => `(tactic| (simp [sIN, sOUT, sDONE, sANS, sCODE, sNU, sGU, sTU, sMU, sXU, sZ, sONE, sSV,
  sFF, sLO, sHI, sFU, sQ, sTMP, sP0, sP1, sP3, sELO, sG, sTL, sLOG, sTLI, sXH, sFIN, sC, sK, Fin.ext_iff] <;> omega))

theorem sC_inj : Function.Injective (sC (tc := tc) (tT := tT)) := by
  intro a b h; simp [sC, sK, Fin.ext_iff] at h; exact Fin.ext h

theorem sK_inj : Function.Injective (sK (tc := tc) (tT := tT)) := by
  intro a b h; simp [sC, sK, Fin.ext_iff] at h; exact Fin.ext h

end Layout

/-- Registers. -/
def r0 : Fin NR := 0
def r1 : Fin NR := 1
def rC : Fin NR := 2
def rG : Fin NR := 3
def rT : Fin NR := 4
def bF : Fin NR := 5
def bR : Fin NR := 6
def rF : Fin NR := 7
def rF2 : Fin NR := 8
def rO : Fin NR := 9

@[simp] theorem r0_val : r0.val = 0 := rfl
@[simp] theorem r1_val : r1.val = 1 := rfl
@[simp] theorem rC_val : rC.val = 2 := rfl
@[simp] theorem rG_val : rG.val = 3 := rfl
@[simp] theorem rT_val : rT.val = 4 := rfl
@[simp] theorem bF_val : bF.val = 5 := rfl
@[simp] theorem bR_val : bR.val = 6 := rfl
@[simp] theorem rF_val : rF.val = 7 := rfl
@[simp] theorem rF2_val : rF2.val = 8 := rfl
@[simp] theorem rO_val : rO.val = 9 := rfl

/-- A stored number of width `W`. -/
abbrev num (W v : ℕ) : List Bool := RepairOrdinary.frame (binary W v)

/-! ## The request words -/

/-- The record `1^mi 0 1^xr 0 w` as a list. -/
def recList (mi xr g q : ℕ) : List Bool :=
  List.replicate mi true ++ false :: (List.replicate xr true ++ false :: wbits g q)

/-- The membership request word (record of rank `q`, full witness range). -/
def memWord (code : List Bool) (mi xr g TN q : ℕ) : List Bool :=
  RepairOrdinary.frame code ++ RepairOrdinary.frame (recList mi xr g q) ++
    RepairOrdinary.frame (List.replicate g true) ++ RepairOrdinary.frame (List.replicate TN true) ++
    RepairOrdinary.frame (List.replicate g false ++ [true])

/-- The interval request word (record of rank `0`, prefix `[0, q)`). -/
def intWord (code : List Bool) (mi xr g TN q : ℕ) : List Bool :=
  RepairOrdinary.frame code ++ RepairOrdinary.frame (recList mi xr g 0) ++
    RepairOrdinary.frame (List.replicate g true) ++ RepairOrdinary.frame (List.replicate TN true) ++
    RepairOrdinary.frame q.bits

theorem bits_two_pow (g : ℕ) : (2 ^ g).bits = List.replicate g false ++ [true] := by
  induction g with
  | zero => simp
  | succ g ih =>
    have h : 2 ^ (g + 1) = Nat.bit false (2 ^ g) := by simp [Nat.bit, pow_succ]; ring
    rw [h, Nat.bits_append_bit _ _ (by simp), ih]
    rfl

theorem record_list (M : OrdinaryWeakMachine) (N q : ℕ) (h : Refuter.machineIndex M + 2 + N / 16 ≤ N) :
    List.ofFn (Refuter.record M N q) =
      recList (Refuter.machineIndex M) (N - N / 16 - Refuter.machineIndex M - 2) (N / 16) q := by
  rw [Refuter.record_ofFn M N q h]
  rfl

theorem memberRequest_word (M : OrdinaryWeakMachine) (T : ℕ → ℕ) (N q : ℕ)
    (h : Refuter.machineIndex M + 2 + N / 16 ≤ N) :
    (Refuter.memberRequest M N (Refuter.record M N q) (T N)).word =
      memWord (VerifierEncoding.code M.verifier) (Refuter.machineIndex M)
        (N - N / 16 - Refuter.machineIndex M - 2) (N / 16) (T N) q := by
  simp only [CNFCompilationRequest.word, Refuter.memberRequest, memWord, record_list M N q h, bits_two_pow]

theorem intervalRequest_word (M : OrdinaryWeakMachine) (T : ℕ → ℕ) (N q : ℕ)
    (h : Refuter.machineIndex M + 2 + N / 16 ≤ N) :
    (Refuter.intervalRequest M T N q).word =
      intWord (VerifierEncoding.code M.verifier) (Refuter.machineIndex M)
        (N - N / 16 - Refuter.machineIndex M - 2) (N / 16) (T N) q := by
  simp only [CNFCompilationRequest.word, Refuter.intervalRequest, intWord, record_list M N 0 h]

end NearCubicGates.Adapters.Refuter.RM
