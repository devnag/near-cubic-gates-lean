import Proof.Gates.TabMachine.Source

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.TabMachine
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicGates.Close.Tabulator

variable {ns nr : ℕ}

section CutM
variable (Z : Fin 64 ↪ Fin (ns + 1)) (Y : Fin 112 ↪ Fin nr)

/-- The streams the cut machine may change. -/
def cutIdx : List (Fin 64) := monoIdx ++ [43, 54, 34]

/-- Every stream `GRest` keeps rewound. -/
theorem grest_heads {cap W s k : ℕ} {σ : WState ns nr} (h : GRest Z Y cap W s k σ) :
    ∀ i ∈ monoIdx, i ≠ 34 → σ.sh (Z i) = 0 := by
  intro i hi h34
  have hc : i ∈ w1List ∨ i ∈ wcList ∨ i ∈ ([3, 47] : List (Fin 64)) ∨ i ∈ ([24, 33] : List (Fin 64)) ∨
      i ∈ ([0, 2, 30, 31, 32] : List (Fin 64)) := by revert i; decide
  rcases hc with hc | hc | hc | hc | hc
  · obtain ⟨v, hv⟩ := h.w1 i hc; exact hv.2
  · obtain ⟨v, hv⟩ := h.wc i hc; exact hv.2
  · exact (h.work1 i hc).1
  · exact (h.workc i hc).1
  · exact h.closed i hc

/-- `grest_out` with extra streams outside the layout. -/
theorem grest_out' {cap W s k : ℕ} {σ τ : WState ns nr} (h : GRest Z Y cap W s k σ) (ex : List (Fin (ns + 1)))
    (hex : ∀ x ∈ ex, ∀ i, x ≠ Z i) (l : List (Fin 64)) (lr : List (Fin 112))
    (hfr : SameExcept σ τ (ex ++ l.map Z) (lr.map Y)) (hl : ∀ i ∈ l, i ∉ restIdx)
    (hlr : ∀ r ∈ lr, r ∉ zList ∧ r ∉ [(13 : Fin 112), 32, 41, 66, 84, 89]) : GRest Z Y cap W s k τ := by
  have hmem : ∀ i : Fin 64, Z i ∈ ex ++ l.map Z → i ∈ l := by
    intro i hm
    rcases List.mem_append.mp hm with hm | hm
    · exact absurd rfl (hex _ hm i)
    · exact (mem_map_emb Z l i).mp hm
  have hR : ∀ i : Fin 64, (i ∈ w1List ∨ i ∈ wcList ∨ i ∈ ([20, 21, 53, 26, 44, 45, 55] : List (Fin 64)) ∨
      i ∈ ([3, 47] : List (Fin 64)) ∨ i ∈ ([24, 33] : List (Fin 64)) ∨ i ∈ ([0, 2, 30, 31, 32] : List (Fin 64))) →
      i ∈ restIdx := by
    intro i hi; unfold restIdx; simp only [List.mem_append]; tauto
  refine grest_frame Z Y h hfr ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro i hi hm; exact absurd (hR i (Or.inl hi)) (hl i (hmem i hm))
  · intro i hi hm; exact absurd (hR i (Or.inr (Or.inl hi))) (hl i (hmem i hm))
  · intro i hi hm; exact hl i (hmem i hm) (hR i (Or.inr (Or.inr (Or.inl hi))))
  · intro i hi hm; exact absurd (hR i (Or.inr (Or.inr (Or.inr (Or.inl hi))))) (hl i (hmem i hm))
  · intro i hi hm; exact absurd (hR i (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hi)))))) (hl i (hmem i hm))
  · intro i hi hm; exact absurd (hR i (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hi)))))) (hl i (hmem i hm))
  · intro r hr hm; rw [mem_map_emb] at hm; exact absurd hr (hlr r hm).1
  · intro r hr hm; rw [mem_map_emb] at hm; exact (hlr r hm).2 hr

/-- The cut machine: all points, then the source assembly onto `O`. -/
def cutM (O : Fin (ns + 1)) : WMX ns nr := .seq (cutsP Z Y) (srcP Z Y O)

def cutMCost (W s : ℕ) (H N X CM n d p g : ℕ) : ℕ :=
  H * (pointCost W s N X CM + (50 * (W + 1) + 30)) + 3 + 1 +
    (srcHeadCost n d p g + 1 + srcTailCost n ((marks (srcHdr d p g (decide (s % 2 = 1)))).length + 2 * n + 1))

theorem cutM_spec {n k s G V : ℕ} (T : Tabulation n k s G V) (cap W Wd CS B CM : ℕ) (hs1 : 1 ≤ s)
    (hWd : Wd + 1 = (s + 1) * (W + 1)) (hWd1 : 1 ≤ Wd) (O : Fin (ns + 1)) (hO : ∀ i, O ≠ Z i) (L0 : List Bool)
    (hfits : ∀ c ∈ T.exactCuts, EquationRow.Fits Wd c) (hs67 : 67 ≤ s) (hcapT : T.exactCuts.length ^ 100 ≤ 2 ^ s)
    (σ : WState ns nr) (h : CutRest Z Y cap W s k (codeRecs (code T).terms) [] L0 0 0 σ)
    (hC : σ.st (Z 56) = recStream (coefRecs s W (code T).terms)) (hCh : σ.sh (Z 56) = 0)
    (hH : σ.st (Z 57) = recStream ((hList (code T)).map (binary (W + 1)))) (hHh : σ.sh (Z 57) = 0)
    (h100 : σ.val (Y 100) = 0) (h101 : σ.val (Y 101) = 0) (h102 : σ.val (Y 102) = 0) (h103 : σ.val (Y 103) = 0)
    (hOs : σ.st O = []) (hOh : σ.sh O = 0) (h104 : σ.val (Y 104) = 0) (h108 : σ.val (Y 108) = 0)
    (h109 : σ.val (Y 109) = 0) (h105 : σ.val (Y 105) = (s + 1) / 2) (h106 : σ.val (Y 106) = Wd)
    (h107 : σ.val (Y 107) = (decide (s % 2 = 1)).toNat)
    (hok : ∀ j, PointOK cap W s k Wd CS B CM (hList (code T)) (code T).terms [] 0 j)
    (hcap : (code T).terms.length * (2 * ((s + 1) * (W + 1)) + 1) + 2 * ((s + 1) * (W + 1)) + 2 ≤ cap)
    (hcapX : (codeRecs (code T).terms).length ≤ cap)
    (hcapH : (hList (code T)).length * (2 * (W + 1) + 1) + 2 * (W + 1) + 2 ≤ cap)
    (hcapS : 2 * (EquationRowCuts.stream Wd T.exactCuts).length + 10 * ((s + 1) / 2 + Wd + T.exactCuts.length) +
      2 * (marks (srcHdr ((s + 1) / 2) Wd T.exactCuts.length (decide (s % 2 = 1)))).length + 40 ≤ cap) :
    Runs cap (cutM Z Y O) σ (cutMCost W s (hList (code T)).length (code T).terms.length
        (codeRecs (code T).terms).length CM (EquationRowCuts.stream Wd T.exactCuts).length ((s + 1) / 2) Wd
        T.exactCuts.length) (fun τ =>
      τ.st O = frame (EquationRowRaw.source (T.input Wd hfits hs67 hcapT)) ∧ τ.sh O = 0 ∧
      GRest Z Y cap W s k τ ∧ τ.val (Y 74) = T.exactCuts.length ∧
      (∀ i ∈ cutIdx, τ.sh (Z i) = 0) ∧
      SameExcept σ τ (O :: cutIdx.map Z) [Y 74]) := by
  have h1 := cutsP_spec Z Y cap W s k Wd CS B CM hs1 hWd hWd1 (hList (code T)) (code T).terms [] L0 0 σ h hC hCh hH hHh
    h100 h101 h102 h103 hok hcap hcapX hcapH
  refine Runs.seq h1 fun τ1 ⟨r1, a56, a56h, a57, a57h, a100, a101, a102, a103, f1⟩ => ?_
  rw [List.nil_append, Nat.zero_add, ← stream_allCuts, ← count_allCount] at r1
  have nO : O ∉ (monoIdx ++ [43, 54]).map Z := fun hm => by
    obtain ⟨i, _, e⟩ := List.mem_map.mp hm; exact hO i e.symm
  have v1 : ∀ r : Fin 112, r ∉ ([74, 56] : List (Fin 112)) → τ1.val (Y r) = σ.val (Y r) := fun r hr => fr_val Y f1 r hr
  have h2 := srcP_spec Z Y cap W s k O hO (codeRecs (code T).terms) (EquationRowCuts.stream Wd T.exactCuts) L0
    T.exactCuts.length ((s + 1) / 2) Wd (decide (s % 2 = 1)) τ1 r1 (by rw [f1.st nO]; exact hOs)
    (by rw [f1.sh nO]; exact hOh) (by rw [v1 104 (by decide)]; exact h104) (by rw [v1 108 (by decide)]; exact h108)
    (by rw [v1 109 (by decide)]; exact h109) (by rw [v1 105 (by decide)]; exact h105)
    (by rw [v1 106 (by decide)]; exact h106) (by rw [v1 107 (by decide)]; exact h107) hcapS
  refine h2.post fun τ ⟨b1, b2, b3, b4, f2⟩ => ?_
  have hsrc := srcHdr_source (T.input Wd hfits hs67 hcapT)
  have st2 : ∀ i : Fin 64, i ≠ 34 → τ.st (Z i) = τ1.st (Z i) ∧ τ.sh (Z i) = τ1.sh (Z i) := by
    intro i hi
    have hn : Z i ∉ [O, Z 34] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨fun e => hO i e.symm, Z.injective.ne hi⟩
    exact ⟨f2.st hn, f2.sh hn⟩
  have v2 : ∀ r : Fin 112, r ≠ 56 → τ.val (Y r) = τ1.val (Y r) := fun r hr =>
    f2.val (by simp only [List.mem_singleton]; exact Y.injective.ne hr)
  have hex : ∀ x ∈ [O], ∀ i, x ≠ Z i := by intro x hx i; simp at hx; subst hx; exact hO i
  have hGR : GRest Z Y cap W s k τ := grest_out' Z Y r1.rest [O] hex [34] [56] f2 (by decide) (by decide)
  refine ⟨by rw [b1]; exact congrArg frame hsrc, b2, hGR, by rw [v2 74 (by decide)]; exact r1.gc, ?_, ?_⟩
  · intro i hi
    unfold cutIdx at hi
    rcases List.mem_append.mp hi with hi | hi
    · by_cases h34 : i = 34
      · subst h34; exact b3
      · exact grest_heads Z Y hGR i hi h34
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl
      · rw [(st2 43 (by decide)).2]; exact r1.w43h
      · rw [(st2 54 (by decide)).2]; exact r1.w54h
      · exact b3
  · refine ⟨fun x hx => ?_, fun r hr => ?_, by rw [f2.2.2, f1.2.2]⟩
    · have n1 : x ∉ [O, Z 34] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx ⊢
        refine ⟨hx.1, fun e => hx.2 ?_⟩
        rw [e]; unfold cutIdx; exact List.mem_map.mpr ⟨34, by simp, rfl⟩
      have n2 : x ∉ (monoIdx ++ [43, 54]).map Z := by
        intro hm; apply hx
        obtain ⟨i, hi, e⟩ := List.mem_map.mp hm
        refine List.mem_cons_of_mem _ (List.mem_map.mpr ⟨i, ?_, e⟩)
        unfold cutIdx
        rcases List.mem_append.mp hi with hi | hi
        · exact List.mem_append_left _ hi
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl <;> simp
      rw [f2.st n1, f2.sh n1]; exact f1.1 x n2
    · by_cases e56 : r = Y 56
      · subst e56; rw [b4]; exact h.cut.2.2.symm
      · have hn : r ∉ ([74, 56] : List (Fin 112)).map Y := by
          simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr ⊢
          exact ⟨hr, e56⟩
        rw [f2.val (by simpa using e56)]; exact f1.2.1 r hn
end CutM

end NearCubicGates.Close.TabMachine
