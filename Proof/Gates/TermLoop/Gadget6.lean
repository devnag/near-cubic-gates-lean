import Proof.Gates.TermLoop.Gadget5

set_option autoImplicit false

namespace NearCubicGates.Close.TermLoop

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutLanguage
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.RepairOrdinary.Streaming NearCubicWires.RepairOrdinary.RadixSemantics
open NearCubicWires.CanonicalWitnessCodec
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Close.Gadget NearCubicGates.Close.Transfer
open NearCubicGates.Close NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP NearCubicGates.Close.Interfaces
open NearCubicGates.Close.Setup
open NearCubicGates.Close.Worker (width pcpp gadgets sysCount Opd model1 model2)
open NearCubicGates.Close.WorkerArith (TermFit termW1 termW2 termCost bud1 bud2 entryWord)
open NearCubicGates.Close.CheckedPCPP.LitDecode (litVar litNeg)
open NearCubicGates.Close.Worker.Format (readField)

noncomputable section

variable {s : GateSources} {P : ThreeQueryPCPP} {g : GateParams} (D : SetupData s P g)
variable {N : ℕ} (x : BitInput N) (bits : List Bool) (pad : ℕ) (B : Outer.OuterGuess (width s g N))
  (jk : Fin (nsW D + 1) → List Bool)
variable {B1 B2 : ℕ} (ctr : Counter B1 B2) (hct : ctr.program.program.tapeCount = D.tc) (ω : ℚ)

/-! ## Clearing a list of registers, then `rA := rA + 1` -/

/-- Clear the registers `rs` in order, then increment `rA`. -/
def clearsInc (rs : List (Fin nrW)) : WM (nsW D) nrW := rs.foldr (fun r Q => .seq (WM.clear r) Q) (.inc rA)

theorem finishW_eq :
    finishW D = clearsInc D [48, 49, 50, 51, 52, 53, 54, 55, 66, 67, 68, 69, 70, 71] := rfl

/-- The register file with `rs` cleared. -/
def zeroL (rs : List (Fin nrW)) (u : Fin nrW → ℕ) : Fin nrW → ℕ := rs.foldr (fun r v => Function.update v r 0) u

/-- The clearing cost. -/
def clearCost (rs : List (Fin nrW)) (u : Fin nrW → ℕ) : ℕ := (rs.map fun r => 3 * u r + 2).sum

theorem zeroL_other (rs : List (Fin nrW)) (u : Fin nrW → ℕ) (r : Fin nrW) (h : r ∉ rs) : zeroL rs u r = u r := by
  induction rs with
  | nil => rfl
  | cons a rs ih =>
    simp only [List.mem_cons, not_or] at h
    simp only [zeroL, List.foldr_cons] at ih ⊢
    rw [Function.update_of_ne h.1, ih h.2]

theorem zeroL_mem (rs : List (Fin nrW)) (u : Fin nrW → ℕ) (r : Fin nrW) (h : r ∈ rs) : zeroL rs u r = 0 := by
  induction rs with
  | nil => simp at h
  | cons a rs ih =>
    simp only [zeroL, List.foldr_cons] at ih ⊢
    by_cases ha : r = a
    · subst ha; simp
    · rw [Function.update_of_ne ha]; exact ih (by simpa [ha] using h)

theorem clearsInc_shape (cap : ℕ) (vi : List Bool) (wh : ℕ) :
    ∀ (rs : List (Fin nrW)) (u : Fin nrW → ℕ), rs.Nodup → (∀ r ∈ rs, r ≠ regE 9 ∧ r ≠ rA ∧ u r ≤ cap) → u rA < cap →
      WExec cap (clearsInc D rs) (Shape D x bits pad B jk vi wh u)
        (Shape D x bits pad B jk vi wh (Function.update (zeroL rs u) rA (u rA + 1))) (clearCost rs u + 3)
  | [], u, _, _, hA => by
    have e := WExec.inc (cap := cap) rA (Shape D x bits pad B jk vi wh u)
      (by simp only [shape_val]; rw [Function.update_of_ne (by decide)]; exact hA)
    rw [shape_setv D x bits pad B jk vi wh u rA (by decide)] at e
    simp only [shape_val] at e
    rw [Function.update_of_ne (by decide : rA ≠ regE 9)] at e
    simpa [clearCost, zeroL, clearsInc] using e
  | r :: rs, u, hnd, hr, hA => by
    obtain ⟨h9, hrA, hc⟩ := hr r (List.mem_cons_self)
    have hnd' := hnd
    simp only [List.nodup_cons] at hnd'
    have e1 := wclear_spec cap r (u r) (Shape D x bits pad B jk vi wh u)
      (by simp only [shape_val]; rw [Function.update_of_ne h9]) (by simp only [shape_val]; rw [Function.update_of_ne h9]; exact hc)
    rw [shape_setv D x bits pad B jk vi wh u r h9] at e1
    have ih := clearsInc_shape cap vi wh rs (Function.update u r 0) hnd'.2
      (fun r' hr' => by
        obtain ⟨a, b, c⟩ := hr r' (List.mem_cons_of_mem _ hr')
        refine ⟨a, b, ?_⟩
        rw [Function.update_of_ne (fun e : r' = r => hnd'.1 (by rw [← e]; exact hr'))]; exact c)
      (by rw [Function.update_of_ne (Ne.symm hrA)]; exact hA)
    have hz : zeroL rs (Function.update u r 0) = zeroL (r :: rs) u := by
      funext r'
      by_cases h1 : r' ∈ rs
      · rw [zeroL_mem _ _ _ h1, zeroL_mem _ _ _ (List.mem_cons_of_mem _ h1)]
      · rw [zeroL_other _ _ _ h1]
        simp only [zeroL, List.foldr_cons]
        by_cases h2 : r' = r
        · subst h2; simp
        · rw [Function.update_of_ne h2, Function.update_of_ne h2]; exact (zeroL_other rs u r' h1).symm
    rw [hz, Function.update_of_ne (Ne.symm hrA)] at ih
    have hcost : clearCost rs (Function.update u r 0) = clearCost rs u := by
      unfold clearCost; congr 1
      apply List.map_congr_left
      intro r' hr'; rw [Function.update_of_ne (fun e : r' = r => hnd'.1 (by rw [← e]; exact hr'))]
    rw [hcost] at ih
    refine WExec.mono (WExec.seq e1 ih) ?_
    simp [clearCost]; omega

/-- The gadget registers. -/
def gRegs : List (Fin nrW) := [48, 49, 50, 51, 52, 53, 54, 55, 66, 67, 68, 69, 70, 71]

theorem vC_other (i : ℕ) (r : Fin nrW) (h : r ∉ gRegs) : vC D x bits pad B jk i r = v0 D x bits pad B jk i r := by
  simp only [gRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  simp only [vC, vF]
  rw [Function.update_of_ne h14, Function.update_of_ne h13, Function.update_of_ne h12, Function.update_of_ne h11,
    Function.update_of_ne h10, Function.update_of_ne h9, Function.update_of_ne h8, Function.update_of_ne h7,
    Function.update_of_ne h6, Function.update_of_ne h5, Function.update_of_ne h4, Function.update_of_ne h3,
    Function.update_of_ne h2, Function.update_of_ne h1]

/-- The register file of `LoopIter (i + 1)`. -/
def vNext (i : ℕ) : Fin nrW → ℕ :=
  Function.update (Function.update (LoopEntry D N x bits pad B jk).val rA (i + 1)) rLC (gadgets s g N - (i + 1))

theorem finish_regs (i : ℕ) :
    Function.update (zeroL gRegs (vC D x bits pad B jk i)) rA (vC D x bits pad B jk i rA + 1) =
      vNext D x bits pad B jk i := by
  rw [vC_A]
  funext r
  by_cases hA : r = rA
  · subst hA; simp only [vNext, Function.update_self]
    rw [Function.update_of_ne (by decide : rA ≠ rLC), Function.update_self]
  · rw [Function.update_of_ne hA]
    by_cases hm : r ∈ gRegs
    · rw [zeroL_mem _ _ _ hm]
      have h48 : 48 ≤ r.val := by
        simp only [gRegs, List.mem_cons, List.not_mem_nil, or_false] at hm
        rcases hm with h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> decide
      have hL : r ≠ rLC := fin_ne (by rw [rLC_val]; omega)
      simp only [vNext]; rw [Function.update_of_ne hL, Function.update_of_ne hA]
      have := v0_lt D x bits pad B jk i r h48
      simp only [v0] at this; rw [Function.update_of_ne hL, Function.update_of_ne hA] at this
      exact this.symm
    · rw [zeroL_other _ _ _ hm, vC_other D x bits pad B jk i r hm]
      simp only [v0, vNext]
      by_cases hL : r = rLC
      · subst hL; simp; omega
      · rw [Function.update_of_ne hL, Function.update_of_ne hL, Function.update_of_ne hA, Function.update_of_ne hA]

theorem randomBits_le_word : (pcpp s P g x B).randomBits ≤ (pcpp s P g x B).word.length := by
  rw [ClauseAccess.word_eq]
  have h1 := ClauseFront.flat_len_ge (ClauseAccess.triples (pcpp s P g x B))
  have h2 : (ClauseAccess.triples (pcpp s P g x B)).length = 2 ^ (pcpp s P g x B).randomBits := by
    simp [ClauseAccess.triples]
  have h3 := Nat.lt_two_pow_self (n := (pcpp s P g x B).randomBits)
  simp only [List.length_append]
  omega

theorem clearCost_gRegs (u : Fin nrW → ℕ) (Z : ℕ) (h : ∀ r ∈ gRegs, u r ≤ Z) :
    clearCost gRegs u ≤ 14 * (3 * Z + 2) := by
  simp only [gRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at h
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14⟩ := h
  simp only [clearCost, gRegs, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  omega

theorem fin_cost (Z : ℕ) : 14 * (3 * Z + 2) + 3 ≤ 100 * (Z + 1) := by omega

theorem finish_shape (cap Z : ℕ) (i : ℕ) (vi : List Bool) (wh : ℕ)
    (hidx : sysCount s P g x B + auxN s P g x B ≤ Z) (hW : (pcpp s P g x B).word.length ≤ Z)
    (hi : i < gadgets s g N) (hcap : 2 * Z + 2 ≤ cap) :
    WExec cap (finishW D) (Shape D x bits pad B jk vi wh (vC D x bits pad B jk i))
      (Shape D x bits pad B jk vi wh (vNext D x bits pad B jk i)) (100 * (Z + 1)) := by
  obtain ⟨b1, b2, b3⟩ := lit_bounds (P := P) x B i 0
  obtain ⟨c1, c2, -⟩ := lit_bounds (P := P) x B i 1
  obtain ⟨d1, d2, -⟩ := lit_bounds (P := P) x B i 2
  have hrb := randomBits_le_word (P := P) x B
  have hM : i < auxN s P g x B := by unfold auxN; omega
  have hvals : ∀ r ∈ gRegs, r ≠ regE 9 ∧ r ≠ rA ∧ vC D x bits pad B jk i r ≤ Z := by
    intro r hr
    simp only [gRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;>
      refine ⟨by decide, by decide, ?_⟩
    · exact (le_of_eq (vC_V D x bits pad B jk i 0)).trans (by omega)
    · exact (le_of_eq (vC_V D x bits pad B jk i 1)).trans (by omega)
    · exact (le_of_eq (vC_V D x bits pad B jk i 2)).trans (by omega)
    · exact (le_of_eq (vC_S D x bits pad B jk i 0)).trans (by omega)
    · exact (le_of_eq (vC_S D x bits pad B jk i 1)).trans (by omega)
    · exact (le_of_eq (vC_S D x bits pad B jk i 2)).trans (by omega)
    · exact (le_of_eq (vC_PB D x bits pad B jk i)).trans (by unfold auxN at hidx; omega)
    · show (pcpp s P g x B).randomBits ≤ Z; omega
    · exact (le_of_eq (vC_D D x bits pad B jk i 0)).trans (by omega)
    · exact (le_of_eq (vC_F D x bits pad B jk i 0)).trans (by omega)
    · exact (le_of_eq (vC_D D x bits pad B jk i 1)).trans (by omega)
    · exact (le_of_eq (vC_F D x bits pad B jk i 1)).trans (by omega)
    · exact (le_of_eq (vC_D D x bits pad B jk i 2)).trans (by omega)
    · exact (le_of_eq (vC_F D x bits pad B jk i 2)).trans (by omega)
  have e := clearsInc_shape D x bits pad B jk cap vi wh gRegs (vC D x bits pad B jk i) (by decide)
    (fun r hr => let h := hvals r hr; ⟨h.1, h.2.1, h.2.2.trans (by omega)⟩)
    (by rw [vC_A]; omega)
  rw [finish_regs] at e
  rw [finishW_eq]
  refine WExec.mono e ?_
  exact le_trans (Nat.add_le_add_right (clearCost_gRegs _ Z (fun r hr => (hvals r hr).2.2)) 3) (fin_cost Z)

end

end NearCubicGates.Close.TermLoop
