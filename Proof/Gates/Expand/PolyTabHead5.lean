import Proof.Gates.Expand.PolyTabHead4

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

namespace NearCubicGates.Close.Expand.PolyTab

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicGates.Close.CounterMachine NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.TabMachine
open NearCubicWires.RepairRepresentation (natWord)
open StablePartition.Workspace (overlay)
open NearCubicWires.RepairRepresentation

variable (E : ExpandMachine) (a : WilliamsAlgorithm)

local notation "WSE" => WState (NSx (te E) (Qa a)) NRk

noncomputable def phC : WMX (NSx (te E) (Qa a)) NRk := .seq (initB2 (sS 2) sS2_ne') st9

theorem U2_eq_U0 (i : Fin 10) (hi : i.val ≠ 0) : U2 (te := te E) (qa := Qa a) i = U0 i := by
  rw [UB_succ _ _ i hi, UB_succ _ _ i hi]

theorem evv_U2 {Wb hd : ℕ} {inp inp' : List Bool} {v : Fin 10 → ℕ} {τ : WSE} (h : EvV U0 RB Wb inp hd 0 v τ)
    (h2 : τ.st (sS 2) = inp') (h2h : τ.sh (sS 2) = 0) : EvV U2 RB Wb inp' 0 0 v τ :=
  ⟨fun i hi => by rw [U2_eq_U0 E a i (fun e => hi (Fin.ext e))]; exact h.num i hi, by rw [UB_zero]; exact h2,
    by rw [UB_zero]; exact h2h, h.r1, h.zero⟩

theorem mem_SB (x : Fin (NSx (te E) (Qa a) + 1)) (hx : x ∈ SB E a) :
    x.val = 65 ∨ x.val = 68 ∨ x.val = 69 ∨ x.val = 58 ∨ (86 ≤ x.val ∧ x.val < 95) := by
  simp only [SB, List.mem_append, List.mem_cons, List.mem_ofFn, List.not_mem_nil, or_false] at hx
  rcases hx with (h | h | h | h) | ⟨j, h⟩
  all_goals first
    | (subst h; simp; done)
    | (subst h; simp; omega)
    | (subst h; have := j.isLt; simp; omega)

/-- The terms word's field bound. -/
def ℓk (r : TabReq) : ℕ := (termsWord (E.expand ⟨r.V, r.F⟩)).length

/-- The caps of phase C. -/
def capC (r : TabReq) : ℕ :=
  capMono (Wk E r + 1) (Wdk E r + 1) (ℓk E r) r.V r.V (r.k + r.s + 2) (VTn E r).length +
    ((ts9 E r).flatMap (blk46 (Wk E r + 1) (r.k + r.s + 2) (VTn E r))).length + 2 * (Wk E r + 1) + 2 +
    r.V * ((r.k + r.s + 2) * (2 * (Wk E r + 1) + 1)) + 1 + ((ts9 E r).flatMap (blk56 (Wdk E r + 1))).length +
    2 * (Wdk E r + 1) + 2 + (ts9 E r).length + 2 * (Wk E r + 1) + 2 + 2 * (Wdk E r + 1) + 1

noncomputable def phCCost (r : TabReq) : ℕ :=
  (9 * (initCost (Wdk E r + 1) + 1) + (41 * (Wdk E r + 1) + 7)) + 1 +
    st9Cost (Wk E r + 1) (Wdk E r + 1) (ℓk E r) r.V r.V (r.k + r.s + 2) (VTn E r).length (ts9 E r).length
      ((ts9 E r).flatMap (blk46 (Wk E r + 1) (r.k + r.s + 2) (VTn E r))).length
      ((ts9 E r).flatMap (blk56 (Wdk E r + 1))).length

theorem termsN_nbl (r : TabReq) : ∀ x ∈ termsN (E.expand ⟨r.V, r.F⟩), natBitLength x ≤ ℓk E r := by
  intro x hx
  have h1 := natBitLength_le_word x
  have h2 := flatMap_natWord_ge _ x hx
  rw [← termsWord_eq] at h2
  unfold ℓk; omega

theorem phC_spec (r : TabReq) (cap : ℕ) (hcap : capC E r ≤ cap) (g : Fin 64 → ℕ) (ρ τ : WSE) (hI : BIn E a r g ρ)
    (hB : BEnd E a r g ρ τ) :
    Runs cap (phC E a) τ (phCCost E r) (fun τ' => ∃ σA : WSE, SameExcept τ σA (List.ofFn ubw) [] ∧
      S9End (recStream ((VTn E r).map (binary (Wk E r + 1)))) σA
        ((ts9 E r).flatMap (blk46 (Wk E r + 1) (r.k + r.s + 2) (VTn E r))) ((ts9 E r).flatMap (blk56 (Wdk E r + 1)))
        (Function.update (fun j => τ.val (rX j)) 32 0) τ') := by
  unfold capC at hcap
  set Wb := Wk E r + 1 with hWb
  set Wc := Wdk E r + 1 with hWc
  have hWW := Wk_le_Wdk E r
  have hW10 := Wk_ge E r
  -- blank streams at τ
  have blk : ∀ x, x ∉ SB E a → x ∉ sS 1 :: SA1 E a → τ.st x = [] ∧ τ.sh x = 0 := fun x h1 h2 => by
    rw [hB.fr.st h1, hB.fr.sh h1]; exact hI.bl x h2
  have nSB : ∀ i : Fin 40, i.val ∉ [0, 3, 4] → (21 ≤ i.val → 30 ≤ i.val) → sS i ∉ SB E a := fun i hi h21 hm => by
    have hm' := mem_SB E a _ hm
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
    have := i.isLt
    simp at hm'; omega
  have nSBz : ∀ i : Fin 64, i.val ≠ 57 → sZ i ∉ SB E a := fun i hi hm => by
    have hm' := mem_SB E a _ hm
    have := i.isLt
    simp at hm'; omega
  -- the registers at τ
  have rg : ∀ j : Fin 64, j.val < 52 → j.val ∉ [9, 2, 19, 26, 43, 20, 5] → τ.val (rX j) = g j := hB.rx
  -- (1) the coefficient block
  obtain ⟨v, hv, hv8, hv9⟩ := hB.ev
  obtain ⟨τ1, e1, hw1, hS1⟩ := initB2_spec cap (sS 2) sS2_ne' Wc (by omega) τ
    (fun i => blk _ (by
        intro hm; have hm' := mem_SB E a _ hm; have := i.isLt; simp at hm'; omega)
      (by
        intro hm; have := mem_SA1 E a _ hm; simp at this; omega))
    (by rw [rg 44 (by decide) (by decide), hI.regs.h44])
    (by rw [rg 51 (by decide) (by decide), hI.regs.z 51 (by decide)])
    (fun j hj => by
      by_cases j1 : j = 1
      · subst j1; exact hv.r1
      · exact hv.zero j j1 hj) (by omega)
  -- the stage-9 start
  have h2 : τ1.st (sS 2) = frame (termsWord (E.expand ⟨r.V, r.F⟩)) := by
    have hn : sS 2 ∉ List.ofFn (ubw (te := te E) (qa := Qa a)) := fun hm => by
      obtain ⟨i, e⟩ := List.mem_ofFn.mp hm; have := congrArg Fin.val e; simp at this; omega
    rw [hS1.st hn, hB.fr.st (nSB 2 (by decide) (by omega)), hI.s2]
  have h2h : τ1.sh (sS 2) = 0 := by
    have hn : sS 2 ∉ List.ofFn (ubw (te := te E) (qa := Qa a)) := fun hm => by
      obtain ⟨i, e⟩ := List.mem_ofFn.mp hm; have := congrArg Fin.val e; simp at this; omega
    rw [hS1.sh hn, hB.fr.sh (nSB 2 (by decide) (by omega)), hI.s2h]
  have nW : ∀ x, (∀ i : Fin 9, ubw i ≠ x) → x ∉ List.ofFn (ubw (te := te E) (qa := Qa a)) := fun x h hm => by
    obtain ⟨i, e⟩ := List.mem_ofFn.mp hm; exact h i e
  have b1 : ∀ x, x ∉ SB E a → x ∉ sS 1 :: SA1 E a → (∀ i : Fin 9, ubw i ≠ x) → τ1.st x = [] ∧ τ1.sh x = 0 :=
    fun x h1 h2 h3 => by rw [hS1.st (nW x h3), hS1.sh (nW x h3)]; exact blk x h1 h2
  have ubwz : ∀ i : Fin 9, ∀ j : Fin 64, ubw (te := te E) (qa := Qa a) i ≠ sZ j := fun i j e => by
    have := congrArg Fin.val e; simp at this; omega
  have ubws : ∀ i : Fin 9, ∀ j : Fin 40, j.val < 30 → ubw (te := te E) (qa := Qa a) i ≠ sS j := fun i j hj e => by
    have := congrArg Fin.val e; simp at this; omega
  have hv2 : EvV U2 RB Wb (frame (termsWord (E.expand ⟨r.V, r.F⟩))) 0 0 v τ1 := by
    refine evv_U2 E a (evv_transfer hv (fun i => ?_) (fun j => hS1.val (by simp))) h2 h2h
    exact ⟨hS1.st (nW _ (fun k e => by
        by_cases hi : i.val = 0
        · have : i = 0 := Fin.ext hi
          subst this; rw [UB_zero] at e; have := congrArg Fin.val e; simp at this; omega
        · rw [UB_succ _ _ i hi] at e; have := congrArg Fin.val e; simp at this; omega)),
      hS1.sh (nW _ (fun k e => by
        by_cases hi : i.val = 0
        · have : i = 0 := Fin.ext hi
          subst this; rw [UB_zero] at e; have := congrArg Fin.val e; simp at this; omega
        · rw [UB_succ _ _ i hi] at e; have := congrArg Fin.val e; simp at this; omega))⟩
  set f : Fin 64 → ℕ := fun j => τ.val (rX j) with hf
  have hx1 : ∀ j : Fin 64, τ1.val (rX j) = f j := fun j => hS1.val (by simp)
  have fz : ∀ j : Fin 64, j.val ∈ [0, 1, 3, 4, 6, 7, 28, 29, 30, 31, 32, 34, 35, 36, 37, 38] → f j = 0 := fun j hj => by
    simp only [hf]; rw [rg j (by simp at hj; omega) (by simp at hj ⊢; omega)]
    exact hI.regs.z j (by simp at hj ⊢; omega)
  have hFZ : FZ f (r.k + r.s + 2) := ⟨fz 0 (by decide), fz 1 (by decide), hB.r0 9 (by decide), fz 29 (by decide),
    fz 28 (by decide), fz 30 (by decide), fz 35 (by decide), fz 3 (by decide), fz 4 (by decide), fz 6 (by decide),
    fz 7 (by decide), fz 31 (by decide), fz 36 (by decide), hB.r0 5 (by decide),
    by simp only [hf]; rw [rg 27 (by decide) (by decide), hI.regs.h27]⟩
  have bZ : ∀ i : Fin 64, i.val ≠ 57 → τ1.st (sZ i) = [] ∧ τ1.sh (sZ i) = 0 := fun i h57 =>
    b1 (sZ i) (nSBz i h57) (nSA1_sZ E a i) (fun k => ubwz k i)
  have bS : ∀ i : Fin 40, i.val ∈ [5, 6] → τ1.st (sS i) = [] ∧ τ1.sh (sS i) = 0 := fun i hi =>
    b1 (sS i) (nSB i (by simp at hi ⊢; omega) (by simp at hi; omega)) (nSA1_sS E a i (by simp at hi ⊢; omega))
      (fun k => ubws k i (by simp at hi; omega))
  have hs4 : sS 4 ∉ List.ofFn (ubw (te := te E) (qa := Qa a)) := fun hm => by
    obtain ⟨i, e⟩ := List.mem_ofFn.mp hm; have := congrArg Fin.val e; simp at this; omega
  have hw1' : EvV U3 RB Wc (frame (termsWord (E.expand ⟨r.V, r.F⟩))) 0 0 v0' τ1 := by
    have := hw1
    rw [hB.fr.st (nSB 2 (by decide) (by omega)), hB.fr.sh (nSB 2 (by decide) (by omega)), hI.s2, hI.s2h] at this
    exact this
  have hMS : MS Wb Wc (frame (termsWord (E.expand ⟨r.V, r.F⟩))) (recStream ((VTn E r).map (binary Wb))) τ1 0 [] [] []
      [] f (fun _ => True) (fun _ => True) τ1 :=
    ⟨⟨v, hv2, hv8, hv9, trivial⟩, ⟨v0', hw1', by simp [v0'], by simp [v0'], trivial⟩,
      ⟨by rw [(bZ 46 (by decide)).1]; simp [overlay], by rw [(bZ 46 (by decide)).2]; rfl,
        by rw [hx1, fz 37 (by decide)]; rfl⟩,
      ⟨by rw [(bZ 56 (by decide)).1]; simp [overlay], by rw [(bZ 56 (by decide)).2]; rfl,
        by rw [hx1, fz 38 (by decide)]; rfl⟩,
      ⟨by rw [(bS 5 (by decide)).1]; simp [overlay], by rw [(bS 5 (by decide)).2]; rfl,
        by rw [hx1, fz 34 (by decide)]; rfl⟩,
      by rw [hS1.st hs4, hB.s4], by rw [hS1.sh hs4, hB.s4h], (bS 6 (by decide)).2,
      by rw [(bS 6 (by decide)).1]; simp, fun j _ => hx1 j, SameExcept.refl _ _ _⟩
  have hV : r.V ≤ Wk E r := by
    have := Wk_ge0 E r
    have : r.V ≤ r.V * (r.s + 1) := Nat.le_mul_of_pos_right _ (by omega)
    unfold Dm at *; omega
  have hNW : (ts9 E r).length < 2 ^ Wb :=
    lt_of_le_of_lt (ts9_length E r) (Nat.pow_lt_pow_right (by norm_num) (by omega))
  have hℓN : natBitLength (ts9 E r).length ≤ ℓk E r := by
    have := termsN_nbl E r (E.expand ⟨r.V, r.F⟩).length (by simp [termsN])
    simpa [ts9] using this
  have c1 : capMono (Wk E r + 1) (Wdk E r + 1) (ℓk E r) r.V r.V (r.k + r.s + 2) (VTn E r).length ≤ cap := by
    simp only [← hWb, ← hWc]; omega
  have c2 : ((ts9 E r).flatMap (blk46 (Wk E r + 1) (r.k + r.s + 2) (VTn E r))).length + 2 * (Wk E r + 1) + 2 +
      r.V * ((r.k + r.s + 2) * (2 * (Wk E r + 1) + 1)) + 1 ≤ cap := by
    simp only [← hWb, ← hWc]; omega
  have c3 : ((ts9 E r).flatMap (blk56 (Wdk E r + 1))).length + 2 * (Wdk E r + 1) + 2 ≤ cap := by
    simp only [← hWb, ← hWc]; omega
  obtain ⟨τ2, e2, h9⟩ := st9_spec cap (by omega) (by omega) (VTn E r) (ℓk E r) r.V r.V (r.k + r.s + 2) (ts9 E r)
    (monoOKs_all E r (ℓk E r) (termsN_nbl E r)) _ (frame_terms E r) f hFZ (fz 32 (by decide)) (fun _ => True)
    (fun _ => True) [] τ1 hMS hNW hℓN c1 c2 c3 (by omega)
  exact ⟨τ2, WXExec.seq e1 e2, τ1, hS1, h9⟩

end NearCubicGates.Close.Expand.PolyTab
