import Proof.Gates.Expand.Fam2

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.Expand

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicGates.Close.WordPrograms.BinW (numOn_sets_ne numOn_sets_self numOn_setv)
open StablePartition.Workspace (overlay)

variable {ns nr : ℕ}

/-- The family's records, level by level. -/
def famRecs (V D : ℕ) : List ℕ := (List.range (D + 1)).flatMap (lvlRecs V)

theorem famRecs_length (V D : ℕ) : (famRecs V D).length = (fam V D).length := by
  simp [famRecs, fam, lvlRecs, List.length_flatMap]

theorem famUpTo_eq (Wb V j : ℕ) : famUpTo Wb V j = (famRecs V j).flatMap fun x => frame (binary Wb x) := rfl

theorem level_le_fam (V D j : ℕ) (hj : j ≤ D) : (level V j).length ≤ (fam V D).length := by
  unfold fam
  rw [List.length_flatMap]
  have hmem : j ∈ List.range (D + 1) := List.mem_range.mpr (by omega)
  exact List.le_sum_of_mem (List.mem_map.mpr ⟨j, hmem, rfl⟩)

theorem fam_succ (V n : ℕ) : fam V (n + 1) = fam V n ++ level V (n + 1) := by
  unfold fam; rw [List.range_succ, List.flatMap_append]; simp

theorem fam_mono (V j D : ℕ) (hj : j ≤ D) : (fam V j).length ≤ (fam V D).length := by
  have hm : Monotone fun n => (fam V n).length :=
    monotone_nat_of_le_succ (fun n => by simp only [fam_succ, List.length_append]; omega)
  exact hm hj

theorem level2_le_fam (V D j : ℕ) (hj : j + 1 ≤ D) :
    (level V j).length + (level V (j + 1)).length ≤ (fam V D).length := by
  have h1 : (level V j).length ≤ (fam V j).length := level_le_fam V j j le_rfl
  have h2 := fam_mono V (j + 1) D hj
  rw [fam_succ, List.length_append] at h2
  omega

section Phase
variable (UF : Fin 12 ↪ Fin (ns + 1)) (RF : Fin 14 ↪ Fin nr)

/-- The start of the family phase: `DT := 0`, `E := 0`, the empty set into FAM and CUR. -/
def famInit : WMX ns nr :=
  .seq (BinW.zero (UF 9) (UF 7) (RF 0) (RF 1)) (.seq (BinW.zero (UF 6) (UF 7) (RF 0) (RF 1))
    (.seq (appendRecX (UF 6) (UF 2) (RF 4) (RF 6)) (.seq (appendRecX (UF 6) (UF 0) (RF 4) (RF 7))
      (closeOutX (UF 0) (RF 7)))))

/-- **The family phase** (`RD` holds `D`). -/
def famPhase : WMX ns nr :=
  .seq (famInit UF RF) (.seq (repK (RF 8) (RF 9) (famLevel UF RF)) (closeOutX (UF 2) (RF 6)))

end Phase

section PhaseSpec
variable {UF : Fin 12 ↪ Fin (ns + 1)} {RF : Fin 14 ↪ Fin nr}

theorem FLS.self {Wb V j : ℕ} {outF L0F : List Bool} {σ0 σ : WState ns nr} (h : FLS UF RF Wb V j outF L0F σ0 σ) :
    FLS UF RF Wb V j outF L0F σ σ :=
  { h with fr := SameExcept.refl σ _ _ }

theorem FLS.setv {Wb V j : ℕ} {outF L0F : List Bool} {σ : WState ns nr} (h : FLS UF RF Wb V j outF L0F σ σ)
    (k : Fin 14) (hk : k = 8 ∨ k = 9) (x : ℕ) : FLS UF RF Wb V j outF L0F (σ.setv (RF k) x) (σ.setv (RF k) x) := by
  have ne : ∀ i : Fin 14, i ≠ 8 → i ≠ 9 → RF i ≠ RF k := by
    intro i h8 h9 e; have := RF.injective e; subst this; rcases hk with rfl | rfl <;> simp_all
  obtain ⟨cur, curh, nxth, fam, wkh, wkl, ⟨x4, h4⟩, ⟨x5, h5⟩, ⟨x6, h6⟩, one, T, dtn, mask, regs, rv, _⟩ := h
  refine ⟨by simpa using cur, by simpa using curh, by simpa using nxth,
    ⟨by simpa using fam.1, by simpa using fam.2.1, by simp [Function.update_of_ne (ne 6 (by decide) (by decide)), fam.2.2]⟩,
    by simpa using wkh, by simpa using wkl, ⟨x4, numOn_setv h4 _ _⟩, ⟨x5, numOn_setv h5 _ _⟩, ⟨x6, numOn_setv h6 _ _⟩,
    numOn_setv one _ _, numOn_setv T _ _, numOn_setv dtn _ _, numOn_setv mask _ _, fun i hi => ?_, ?_,
    SameExcept.refl _ _ _⟩
  · have h8 : i ≠ 8 := by intro e; subst e; simp at hi
    have h9 : i ≠ 9 := by intro e; subst e; simp at hi
    simp [Function.update_of_ne (ne i h8 h9), regs i hi]
  · simp [Function.update_of_ne (ne 10 (by decide) (by decide)), rv]

/-- The family phase's start. -/
structure FS0 (UF : Fin 12 ↪ Fin (ns + 1)) (RF : Fin 14 ↪ Fin nr) (Wb V : ℕ) (σ : WState ns nr) : Prop where
  curh : σ.sh (UF 0) = 0
  nxth : σ.sh (UF 1) = 0
  famh : σ.sh (UF 2) = 0
  wkh : σ.sh (UF 3) = 0
  wkl : (σ.st (UF 3)).length ≤ 2 * Wb + 1
  S : ∃ x, NumOn σ (UF 4) Wb x
  P : ∃ x, NumOn σ (UF 5) Wb x
  E : ∃ x, NumOn σ (UF 6) Wb x
  one : NumOn σ (UF 7) Wb 1
  T : NumOn σ (UF 8) Wb (2 ^ V)
  DT : ∃ x, NumOn σ (UF 9) Wb x
  mask : NumOn σ (UF 10) Wb (2 ^ V - 1)
  regs : ∀ k : Fin 14, k ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 11, 12, 13] : List (Fin 14)) → σ.val (RF k) = 0
  rv : σ.val (RF 10) = V

/-- Append a width-`W` number (stream `Src`, head `0`) as a record to an open output stream: frame form. -/
theorem appendNum (cap W : ℕ) {Src O : Fin (ns + 1)} {CS CO : Fin nr} (hSO : Src ≠ O) (hC : CS ≠ CO)
    (σ : WState ns nr) (x : ℕ) (out L0 : List Bool) (hS : NumOn σ Src W x) (hCS : σ.val CS = 0)
    (hO : OutOn σ O CO out L0) (hcap : out.length + 2 * W + 2 ≤ cap) :
    Runs cap (appendRecX Src O CS CO) σ (40 * W + 11)
      (fun τ => OutOn τ O CO (out ++ frame (binary W x)) L0 ∧ SameExcept σ τ [O] [CO]) := by
  have a := appendRec_spec cap hSO hC σ (binary W x) [] out L0 (by rw [hS.1, BinW.frame_frameP]) hS.2 hCS hO
    (by rw [binary_length]; exact hcap)
  rw [binary_length] at a
  refine ⟨_, WXExec.wm a, appendRec_out σ O CO out L0 _, ?_⟩
  exact SameExcept.trans (SameExcept.trans (sameExcept_sets _ (by simp) _) (sameExcept_seth _ (by simp) _))
    (sameExcept_setv _ (by simp) _)

/-- Close an output stream: frame form. -/
theorem closeNum (cap : ℕ) {O : Fin (ns + 1)} {CO : Fin nr} (σ : WState ns nr) (out L0 : List Bool)
    (hO : OutOn σ O CO out L0) (hcap : out.length ≤ cap) :
    Runs cap (closeOutX O CO) σ (5 * out.length + 3)
      (fun τ => τ.st O = overlay (out ++ [false]) L0 ∧ τ.sh O = 0 ∧ τ.val CO = 0 ∧ SameExcept σ τ [O] [CO]) := by
  have c := closeOut_spec cap σ out L0 hO hcap
  refine ⟨_, WXExec.wm c, by simp, by simp, by simp, ?_⟩
  exact SameExcept.trans (SameExcept.trans (sameExcept_sets _ (by simp) _) (sameExcept_seth _ (by simp) _))
    (sameExcept_setv _ (by simp) _)

def famInitCost (Wb : ℕ) : ℕ :=
  (41 * Wb + 3) + 1 + ((41 * Wb + 3) + 1 + ((40 * Wb + 11) + 1 + ((40 * Wb + 11) + 1 + (5 * (2 * Wb + 1) + 3))))

theorem famInit_spec (cap Wb V : ℕ) (σ : WState ns nr) (h : FS0 UF RF Wb V σ) (hcap : 2 * Wb + 1 ≤ cap)
    (hcapR : 4 * Wb + 4 ≤ cap) :
    Runs cap (famInit UF RF) σ (famInitCost Wb) (FLS UF RF Wb V 0 [] (σ.st (UF 2)) σ) := by
  obtain ⟨x9, h9⟩ := h.DT
  obtain ⟨x6, h6⟩ := h.E
  have z1 := BinW.zero_spec cap Wb (ufN (by decide : (9 : Fin 12) ≠ 7)) (rfN (by decide : (0 : Fin 14) ≠ 1)) σ x9 1 h9
    h.one (h.regs 0 (by decide)) (h.regs 1 (by decide)) hcap
  have f1 : SameExcept σ (σ.sets (UF 9) (frame (binary Wb 0))) [UF 9] [] := sameExcept_sets σ (by simp) _
  have nin9 : ∀ k : Fin 12, k ≠ 9 → UF k ∉ [UF 9] := by
    intro k hk hm; simp only [List.mem_singleton] at hm; exact hk (UF.injective hm)
  refine Runs.seqE z1 ?_
  set σ1 := σ.sets (UF 9) (frame (binary Wb 0)) with hσ1
  have z2 := BinW.zero_spec cap Wb (ufN (by decide : (6 : Fin 12) ≠ 7)) (rfN (by decide : (0 : Fin 14) ≠ 1)) σ1 x6 1
    (f1.numOn (nin9 6 (by decide)) h6) (f1.numOn (nin9 7 (by decide)) h.one) (by rw [f1.val (by simp)]; exact h.regs 0 (by decide))
    (by rw [f1.val (by simp)]; exact h.regs 1 (by decide)) hcap
  refine Runs.seqE z2 ?_
  set σ2 := σ1.sets (UF 6) (frame (binary Wb 0)) with hσ2
  have f2 : SameExcept σ σ2 [UF 9, UF 6] [] :=
    SameExcept.trans (f1.weaken (fun x hx => by simp at hx ⊢; tauto) (fun r hr => by simp at hr))
      (sameExcept_sets σ1 (by simp) _)
  have nin96 : ∀ k : Fin 12, k ≠ 9 → k ≠ 6 → UF k ∉ [UF 9, UF 6] := by
    intro k hk hk' hm; simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hm | hm <;> have := UF.injective hm <;> simp_all
  have hE2 : NumOn σ2 (UF 6) Wb 0 := numOn_sets_self σ1 _ Wb 0 (by rw [f1.sh (nin9 6 (by decide))]; exact h6.2)
  have hD2 : NumOn σ2 (UF 9) Wb 0 := numOn_sets_ne (numOn_sets_self σ _ Wb 0 h9.2) (ufN (by decide : (9 : Fin 12) ≠ 6)) _
  have hFAM2 : OutOn σ2 (UF 2) (RF 6) [] (σ.st (UF 2)) :=
    ⟨by rw [f2.st (nin96 2 (by decide) (by decide))]; simp [overlay],
      by rw [f2.sh (nin96 2 (by decide) (by decide))]; simpa using h.famh,
      by rw [f2.val (by simp)]; simpa using h.regs 6 (by decide)⟩
  refine Runs.seq (appendNum cap Wb (ufN (by decide : (6 : Fin 12) ≠ 2)) (rfN (by decide : (4 : Fin 14) ≠ 6)) σ2 0 []
    (σ.st (UF 2)) hE2 (by rw [f2.val (by simp)]; exact h.regs 4 (by decide)) hFAM2 (by simp; omega))
    (fun σ3 ⟨hF3, f3⟩ => ?_)
  have hCUR3 : OutOn σ3 (UF 0) (RF 7) [] (σ.st (UF 0)) :=
    ⟨by rw [f3.st (by simp [ufN]), f2.st (nin96 0 (by decide) (by decide))]; simp [overlay],
      by rw [f3.sh (by simp [ufN]), f2.sh (nin96 0 (by decide) (by decide))]; simpa using h.curh,
      by rw [f3.val (by simp [rfN]), f2.val (by simp)]; simpa using h.regs 7 (by decide)⟩
  refine Runs.seq (appendNum cap Wb (ufN (by decide : (6 : Fin 12) ≠ 0)) (rfN (by decide : (4 : Fin 14) ≠ 7)) σ3 0 []
    (σ.st (UF 0)) (f3.numOn (by simp [ufN]) hE2) (by rw [f3.val (by simp [rfN]), f2.val (by simp)]; exact h.regs 4 (by decide))
    hCUR3 (by simp; omega)) (fun σ4 ⟨hC4, f4⟩ => ?_)
  refine (closeNum cap σ4 _ _ hC4 (by simp [frame_length]; omega)).mono
    (by simp only [List.nil_append, frame_length, binary_length]; omega)
    (fun σ5 ⟨hst5, hsh5, hcc5, f5⟩ => ?_)
  have f35 : SameExcept σ3 σ5 [UF 0] [RF 7] := SameExcept.trans f4 f5
  have fall : SameExcept σ σ5 [UF 0, UF 2, UF 6, UF 9] [RF 6, RF 7] :=
    SameExcept.trans (SameExcept.trans
      (f2.weaken (fun x hx => by simp at hx ⊢; tauto) (fun r hr => by simp at hr))
      (f3.weaken (fun x hx => by simp at hx ⊢; tauto) (fun r hr => by simp at hr ⊢; tauto)))
      (f35.weaken (fun x hx => by simp at hx ⊢; tauto) (fun r hr => by simp at hr ⊢; tauto))
  have ninA : ∀ k : Fin 12, k ∈ ([1, 3, 4, 5, 7, 8, 10] : List (Fin 12)) → UF k ∉ [UF 0, UF 2, UF 6, UF 9] := by
    intro k hk hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hm | hm | hm | hm <;> have := UF.injective hm <;> subst this <;> simp at hk
  have rinA : ∀ k : Fin 14, k ∈ ([0, 1, 2, 3, 4, 5, 10, 11, 12, 13] : List (Fin 14)) → RF k ∉ [RF 6, RF 7] := by
    intro k hk hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hm | hm <;> have := RF.injective hm <;> subst this <;> simp at hk
  have hlv0 : lvlRecs V 0 = [0] := by simp [lvlRecs, level]
  have hfu0 : famUpTo Wb V 0 = frame (binary Wb 0) := by simp [famUpTo, lvlRecs, level]
  refine ⟨?_, hsh5, ?_, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨junk, hj⟩ := overlay_rec ([] ++ frame (binary Wb 0)) (σ.st (UF 0))
    refine ⟨junk, ?_⟩
    rw [hst5, hj, hlv0]; simp [recStream]
  · rw [fall.sh (ninA 1 (by decide))]; exact h.nxth
  · rw [f35.st (by simp [ufN]), hfu0]; simpa using hF3.1
  · rw [f35.sh (by simp [ufN]), hfu0]; simpa using hF3.2.1
  · rw [f35.val (by simp [rfN]), hfu0]; simpa using hF3.2.2
  · rw [fall.sh (ninA 3 (by decide))]; exact h.wkh
  · rw [fall.st (ninA 3 (by decide))]; exact h.wkl
  · obtain ⟨x, hx⟩ := h.S; exact ⟨x, fall.numOn (ninA 4 (by decide)) hx⟩
  · obtain ⟨x, hx⟩ := h.P; exact ⟨x, fall.numOn (ninA 5 (by decide)) hx⟩
  · exact ⟨0, f35.numOn (by simp [ufN]) (f3.numOn (by simp [ufN]) hE2)⟩
  · exact fall.numOn (ninA 7 (by decide)) h.one
  · exact fall.numOn (ninA 8 (by decide)) h.T
  · rw [zero_mul]; exact f35.numOn (by simp [ufN]) (f3.numOn (by simp [ufN]) hD2)
  · exact fall.numOn (ninA 10 (by decide)) h.mask
  · intro k hk
    have hk' : k ∈ ([0, 1, 2, 3, 4, 5, 11, 12, 13] : List (Fin 14)) ∨ k = 7 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk ⊢; tauto
    rcases hk' with hk' | rfl
    · rw [fall.val (rinA k (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hk' ⊢; tauto))]
      exact h.regs k (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hk' ⊢; tauto)
    · exact hcc5
  · rw [fall.val (rinA 10 (by decide))]; exact h.rv
  · exact fall.weaken (fun x hx => by simp at hx ⊢; tauto) (fun r hr => by simp at hr ⊢; tauto)

end PhaseSpec

end NearCubicGates.Close.Expand
