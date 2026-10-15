import Proof.CaseAnalysis.FinalDecidesBridgeUniform
import Proof.CaseAnalysis.FinalStageSeamBlock

namespace NearCubicWires.RepairSource.CloseoutFinal.C10BodyWidths

open LocalBitMultitape ExtDecompositionBatch
open NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDock
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerChain
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.CloseoutFinal.C10LengthGate
open NearCubicWires.RepairSource.CloseoutFinal.C10CompareDockLit
open C10TailCompose
open CloseoutRowsOriginalSchedule (Phase)

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (e : ℕ) (he : 58 ≤ e)

def retained (j : Fin 2) : Fin (218+e) := ⟨274+j.val, by omega⟩
@[simp] theorem retained_val (j : Fin 2) : (retained e he j).val = 274+j.val := rfl

def widthWord (b : ℕ) (j : Fin 2) : List Bool :=
  List.replicate (if j.val = 0 then b else CompetitorRationalDecision.width b) true

def BlockRunsWidths {bs : ℕ} (body : LocalBitMultitape.Machine (218+e) bs) (F : ℕ)
    (input witness rec : List Bool) (b : ℕ) : Prop :=
  ∃ (heads : Fin (218+e) → ℕ) (exit : Fin (218+e) → List Bool),
    Step body F (fun _ => 0) (entryOf (wflag e) input witness) heads exit ∧
    exit (wport e) = rec ∧ exit (winput e) = frame input ∧ exit (wwit e) = frame witness ∧
    ∀ j, exit (retained e he j) = widthWord b j

def FreePrefix (i : Fin (bigOf e)) : Prop :=
  2 ≤ i.val ∧ i.val < 475 ∧ (i.val < 218 ∨ 221 ≤ i.val)

theorem rslot_free (ph : Phase) (j : Fin (218+e+1)) (i : Fin (bigOf e))
    (hi : FreePrefix e i) : rslot e ph j ≠ i := by
  intro h
  have hv := congrArg Fin.val h
  rw [rslot_val] at hv
  obtain ⟨hlo, hhi, hrec⟩ := hi
  have hj := j.isLt
  cases ph <;> simp only [scrVal, baseOf, cntVal] at hv <;> split_ifs at hv <;> omega

theorem body_dock_widths {bs : ℕ} (ph : Phase) (body : LocalBitMultitape.Machine (218+e) bs) (F : ℕ)
    (input witness : List Bool) (rec : List Bool) (b : ℕ)
    (h : BlockRunsWidths e he body F input witness rec b)
    (A : Fin (bigOf e) → List Bool)
    (hblk : ∀ i : Fin (218+e), A (bslot e ph i) = entryOf (wflag e) input witness i)
    (hcnt : A (cnt e ph) = []) :
    ∃ A' : Fin (bigOf e) → List Bool,
      Step (rbody e ph body) (2*F+2) (fun _ => 0) A (fun _ => 0) A' ∧
      A' (scr e ph) = rec ∧
      A' (gInput e) = frame input ∧ A' (gWit e) = frame witness ∧
      (∀ s : Fin (bigOf e), (∀ j, rslot e ph j ≠ s) → A' s = A s) ∧
      (∀ j, A' (bslot e ph (retained e he j)) = widthWord b j) := by
  obtain ⟨heads, exit, hstep, hrec, hin, hwit, hwidth⟩ := h
  obtain ⟨c, hr⟩ := step_reset hstep
  have hA : ∀ j : Fin (218+e+1), A (rslot e ph j)
      = Fin.addCases (motive := fun _ => List Bool) (entryOf (wflag e) input witness)
        (fun _ : Fin 1 => ([] : List Bool)) j := by
    intro j
    refine Fin.addCases (m := 218+e) (n := 1) (fun i => ?_) (fun i => ?_) j
    · rw [rslot_castAdd, Fin.addCases_left]
      exact hblk i
    · have hi : i = 0 := Fin.eq_zero i
      subst hi
      rw [rslot_last, Fin.addCases_right]
      exact hcnt
  have hdock := hr.dock (rslot e ph) (rslot_injective e ph) (fun _ => 0) A (fun _ => rfl) hA
  rw [dockH_existing (rslot e ph) (fun _ => 0) (fun _ => 0) (fun _ => rfl)] at hdock
  refine ⟨install (rslot e ph) A
    (Fin.addCases (motive := fun _ => List Bool) exit (fun _ : Fin 1 => c)), hdock, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← bslot_port e ph, ← rslot_castAdd e ph (wport e),
      install_slot (rslot e ph) (rslot_injective e ph) A _ ((wport e).castAdd 1),
      Fin.addCases_left]
    exact hrec
  · rw [← bslot_input e ph, ← rslot_castAdd e ph (winput e),
      install_slot (rslot e ph) (rslot_injective e ph) A _ ((winput e).castAdd 1),
      Fin.addCases_left]
    exact hin
  · rw [← bslot_wit e ph, ← rslot_castAdd e ph (wwit e),
      install_slot (rslot e ph) (rslot_injective e ph) A _ ((wwit e).castAdd 1),
      Fin.addCases_left]
    exact hwit
  · intro s hs
    exact install_other (rslot e ph) A _ s hs

  · intro j
    rw [← rslot_castAdd e ph (retained e he j),
      install_slot (rslot e ph) (rslot_injective e ph) A _ ((retained e he j).castAdd 1),
      Fin.addCases_left]
    exact hwidth j

theorem bodyThree_widths {bs : Phase → ℕ} (body : (ph : Phase) → LocalBitMultitape.Machine (218+e) (bs ph))
    (F : Phase → ℕ) (input witness : List Bool) (rec : Phase → List Bool) (width : Phase → ℕ)
    (hbody : ∀ ph, BlockRunsWidths e he (body ph) (F ph) input witness (rec ph) (width ph)) :
    ∃ A : Fin (bigOf e) → List Bool,
      Step (bodyThree e body) (bodyThreeFuel F) (fun _ => 0)
        (entryOf (gFlag e) input witness) (fun _ => 0) A ∧
      (∀ ph, A (scr e ph) = rec ph) ∧
      (∀ s : Fin (bigOf e), FreePrefix e s → A s = []) ∧
      A (tailCnt e) = [] ∧
      (∀ ph j, A (bslot e ph (retained e he j)) = widthWord (width ph) j) := by
  classical
  have hMF := momentFlag_val e
  have hCF := clauseFlag_val e
  have hML := momentLit_val e
  have hCL := clauseLit_val e
  set A0 : Fin (bigOf e) → List Bool := entryOf (gFlag e) input witness with hA0
  have hA0blank : ∀ s : Fin (bigOf e), s.val ≠ 691 → s.val ≠ 0 → s.val ≠ 1 → A0 s = [] := by
    intro s h691 h0 h1
    exact entryOf_blank (gFlag e) _ _ s (Fin.ne_of_val_ne (by rw [gFlag_val]; exact h691)) h0 h1
  -- §9.1 the two literal flag writes
  have hne1 : bslot e .moment (wflag e) ≠ litOf e .moment :=
    Fin.ne_of_val_ne (by rw [hMF, hML]; omega)
  have hne2 : bslot e .clause (wflag e) ≠ litOf e .clause :=
    Fin.ne_of_val_ne (by rw [hCF, hCL]; omega)
  have hL1 := lit_dock e (bslot e .moment (wflag e)) (litOf e .moment) hne1 A0
    (hA0blank _ (by omega) (by omega) (by omega)) (hA0blank _ (by omega) (by omega) (by omega))
  set A1 := install (pair2 e (bslot e .moment (wflag e)) (litOf e .moment)) A0 ![[true], [false]]
    with hA1
  have hA1other : ∀ s : Fin (bigOf e), s.val ≠ 909 + e → s.val ≠ 1129 + 3*e → A1 s = A0 s := by
    intro s h1 h2
    exact install_other _ A0 _ s
      (pair2_ne e _ _ s (Fin.ne_of_val_ne (by omega)) (Fin.ne_of_val_ne (by omega)))
  have hL2 := lit_dock e (bslot e .clause (wflag e)) (litOf e .clause) hne2 A1
    ((hA1other _ (by omega) (by omega)).trans (hA0blank _ (by omega) (by omega) (by omega)))
    ((hA1other _ (by omega) (by omega)).trans (hA0blank _ (by omega) (by omega) (by omega)))
  set A2 := install (pair2 e (bslot e .clause (wflag e)) (litOf e .clause)) A1 ![[true], [false]]
    with hA2
  have hA2other : ∀ s : Fin (bigOf e), s.val ≠ 1127 + 2*e → s.val ≠ 1130 + 3*e →
      A2 s = A1 s := by
    intro s h1 h2
    exact install_other _ A1 _ s
      (pair2_ne e _ _ s (Fin.ne_of_val_ne (by omega)) (Fin.ne_of_val_ne (by omega)))
  have hA2base : ∀ s : Fin (bigOf e), s.val ≠ 909 + e → s.val ≠ 1129 + 3*e →
      s.val ≠ 1127 + 2*e → s.val ≠ 1130 + 3*e → A2 s = A0 s :=
    fun s a b c d => (hA2other s c d).trans (hA1other s a b)
  have hMFtrue : A2 (bslot e .moment (wflag e)) = [true] := by
    have hslot := install_slot (pair2 e (bslot e .moment (wflag e)) (litOf e .moment))
      (pair2_injective e _ _ hne1) A0 ![[true], [false]] (0 : Fin 2)
    rw [pair2_zero] at hslot
    rw [hA2other _ (by omega) (by omega), hA1]
    exact hslot
  have hCFtrue : A2 (bslot e .clause (wflag e)) = [true] := by
    have hslot := install_slot (pair2 e (bslot e .clause (wflag e)) (litOf e .clause))
      (pair2_injective e _ _ hne2) A1 ![[true], [false]] (0 : Fin 2)
    rw [pair2_zero] at hslot
    rw [hA2]
    exact hslot
  have hPFtrue : A2 (bslot e .penalty (wflag e)) = [true] := by
    have hv : (bslot e .penalty (wflag e)).val = 691 := by
      rw [bslot_flag_val]; simp only [baseOf]
    have heq : bslot e .penalty (wflag e) = gFlag e := Fin.ext (by rw [hv, gFlag_val])
    rw [heq, hA2base _ (by rw [gFlag_val]; omega) (by rw [gFlag_val]; omega)
      (by rw [gFlag_val]; omega) (by rw [gFlag_val]; omega), hA0]
    exact entryOf_flag (gFlag e) input witness
  -- shared tapes, on any bank that agrees with `A0` off the literal slots
  have hgIn : ∀ A : Fin (bigOf e) → List Bool, A (gInput e) = A0 (gInput e) →
      A (gInput e) = frame input := by
    intro A hA
    rw [hA, hA0]
    exact entryOf_zero (gFlag e) _ _ (gInput e) (Fin.ne_of_val_ne (by simp)) (gInput_val e)
  have hgWit : ∀ A : Fin (bigOf e) → List Bool, A (gWit e) = A0 (gWit e) →
      A (gWit e) = frame witness := by
    intro A hA
    rw [hA, hA0]
    exact entryOf_one (gFlag e) _ _ (gWit e) (Fin.ne_of_val_ne (by simp)) (gWit_val e)
  have hin2 : A2 (gInput e) = frame input :=
    hgIn A2 (hA2base _ (by simp; omega) (by simp; omega) (by simp; omega) (by simp; omega))
  have hwit2 : A2 (gWit e) = frame witness :=
    hgWit A2 (hA2base _ (by simp; omega) (by simp; omega) (by simp; omega) (by simp; omega))
  -- §9.2 the blank slots of a block, on `A2`
  have hA2blk : ∀ (ph : Phase) (i : Fin (218+e)), i.val ≠ 0 → i.val ≠ 1 → i.val ≠ 216 →
      A2 (bslot e ph i) = [] := by
    intro ph i h0 h1 h216
    obtain ⟨n0, n1, n691, nMF, nCF, nML, nCL⟩ := block_slot_free e ph i h0 h1 h216
    rw [hA2base _ nMF nML nCF nCL]
    exact hA0blank _ n691 n0 n1
  have hcntA2 : ∀ ph : Phase, A2 (cnt e ph) = [] := by
    intro ph
    have hg := cntVal_gt e ph
    rw [hA2base _ (by omega) (by omega) (by omega) (by omega)]
    exact hA0blank _ (by omega) (by omega) (by omega)
  -- §9.3 the penalty block
  have hblk0 : ∀ i, A2 (bslot e .penalty i) = entryOf (wflag e) input witness i :=
    blk_of e .penalty input witness A2 hPFtrue hin2 hwit2 (hA2blk .penalty)
  obtain ⟨A3, hB0, hrec0, hin3, hwit3, hoth0, hwidth0⟩ :=
    body_dock_widths e he .penalty (body .penalty) (F .penalty) input witness (rec .penalty) (width .penalty)
      (hbody .penalty) A2 hblk0 (hcntA2 .penalty)
  -- §9.4 the moment block: disjoint from the penalty block except on `0`, `1`
  have hcross : ∀ (ph ph' : Phase), ph ≠ ph' → ∀ (i : Fin (218+e)), 2 ≤ i.val →
      ∀ j, rslot e ph' j ≠ bslot e ph i := by
    intro ph ph' hne i hi j hj
    have := rslot_cross e ph ph' hne j i hj
    omega
  have hnePM : (Phase.moment : Phase) ≠ Phase.penalty := by intro hc; exact Phase.noConfusion hc
  have hnePC : (Phase.clause : Phase) ≠ Phase.penalty := by intro hc; exact Phase.noConfusion hc
  have hneCM : (Phase.clause : Phase) ≠ Phase.moment := by intro hc; exact Phase.noConfusion hc
  have hblk1 : ∀ i, A3 (bslot e .moment i) = entryOf (wflag e) input witness i := by
    refine blk_of e .moment input witness A3 ?_ hin3 hwit3 ?_
    · rw [hoth0 _ (hcross .moment .penalty hnePM (wflag e) (by simp))]
      exact hMFtrue
    · intro i h0 h1 h216
      rw [hoth0 _ (hcross .moment .penalty hnePM i (by omega))]
      exact hA2blk .moment i h0 h1 h216
  have hcnt3 : A3 (cnt e .moment) = [] := by
    rw [hoth0 _ (fun j => ?_)]
    · exact hcntA2 .moment
    · intro hj
      have h1 := congrArg Fin.val hj
      rw [rslot_val] at h1
      have := j.isLt
      simp only [scrVal, baseOf, cntVal, cnt_val] at h1
      split_ifs at h1 <;> omega
  obtain ⟨A4, hB1, hrec1, hin4, hwit4, hoth1, hwidth1⟩ :=
    body_dock_widths e he .moment (body .moment) (F .moment) input witness (rec .moment) (width .moment)
      (hbody .moment) A3 hblk1 hcnt3
  -- §9.5 the clause block
  have hblk2 : ∀ i, A4 (bslot e .clause i) = entryOf (wflag e) input witness i := by
    refine blk_of e .clause input witness A4 ?_ hin4 hwit4 ?_
    · rw [hoth1 _ (hcross .clause .moment hneCM (wflag e) (by simp)),
        hoth0 _ (hcross .clause .penalty hnePC (wflag e) (by simp))]
      exact hCFtrue
    · intro i h0 h1 h216
      rw [hoth1 _ (hcross .clause .moment hneCM i (by omega)),
        hoth0 _ (hcross .clause .penalty hnePC i (by omega))]
      exact hA2blk .clause i h0 h1 h216
  have hcnt4 : A4 (cnt e .clause) = [] := by
    have hstep : ∀ (ph : Phase) (j : Fin (218+e+1)), rslot e ph j ≠ cnt e .clause ∨
        ph = Phase.clause := by
      intro ph j
      cases ph
      · left
        intro hj
        have h1 := congrArg Fin.val hj
        rw [rslot_val] at h1
        have := j.isLt
        simp only [scrVal, baseOf, cntVal, cnt_val] at h1
        split_ifs at h1 <;> omega
      · left
        intro hj
        have h1 := congrArg Fin.val hj
        rw [rslot_val] at h1
        have := j.isLt
        simp only [scrVal, baseOf, cntVal, cnt_val] at h1
        split_ifs at h1 <;> omega
      · right; rfl
    rw [hoth1 _ (fun j => (hstep .moment j).resolve_right (by intro hc; exact Phase.noConfusion hc)),
      hoth0 _ (fun j => (hstep .penalty j).resolve_right (by intro hc; exact Phase.noConfusion hc))]
    exact hcntA2 .clause
  obtain ⟨A5, hB2, hrec2, _hin5, _hwit5, hoth2, hwidth2⟩ :=
    body_dock_widths e he .clause (body .clause) (F .clause) input witness (rec .clause) (width .clause)
      (hbody .clause) A4 hblk2 hcnt4
  -- §9.6 the conclusion
  have hkeep : ∀ (ph ph' : Phase), ph ≠ ph' → ∀ j, rslot e ph' j ≠ scr e ph := by
    intro ph ph' hne j
    rw [← bslot_port e ph]
    exact hcross ph ph' hne (wport e) (by simp) j
  refine ⟨A5, ((hL1.seq hL2).seq (hB0.seq hB1)).seq hB2, ?_, ?_, ?_, ?_⟩
  · intro ph
    cases ph
    · rw [hoth2 _ (hkeep .penalty .clause (fun hc => Phase.noConfusion hc)),
        hoth1 _ (hkeep .penalty .moment (fun hc => Phase.noConfusion hc))]
      exact hrec0
    · rw [hoth2 _ (hkeep .moment .clause (fun hc => Phase.noConfusion hc))]
      exact hrec1
    · exact hrec2
  · intro s hs
    obtain ⟨h1, h2, h3⟩ := hs
    rw [hoth2 _ (fun j => rslot_free e _ j s ⟨h1, h2, h3⟩), hoth1 _ (fun j => rslot_free e _ j s ⟨h1, h2, h3⟩),
      hoth0 _ (fun j => rslot_free e _ j s ⟨h1, h2, h3⟩),
      hA2base s (by omega) (by omega) (by omega) (by omega)]
    exact hA0blank s (by omega) (by omega) (by omega)
  · rw [hoth2 _ (rslot_ne_tailCnt e .clause), hoth1 _ (rslot_ne_tailCnt e .moment),
      hoth0 _ (rslot_ne_tailCnt e .penalty),
      hA2base _ (by rw [tailCnt_val]; omega) (by rw [tailCnt_val]; omega)
        (by rw [tailCnt_val]; omega) (by rw [tailCnt_val]; omega)]
    exact hA0blank _ (by rw [tailCnt_val]; omega) (by rw [tailCnt_val]; omega)
      (by rw [tailCnt_val]; omega)

  · intro ph j
    have hj : 2 ≤ (retained e he j).val := by rw [retained_val]; omega
    cases ph
    · rw [hoth2 _ (hcross .penalty .clause (by intro h; cases h) _ hj),
        hoth1 _ (hcross .penalty .moment (by intro h; cases h) _ hj)]
      exact hwidth0 j
    · rw [hoth2 _ (hcross .moment .clause (by intro h; cases h) _ hj)]
      exact hwidth1 j
    · exact hwidth2 j

end
end NearCubicWires.RepairSource.CloseoutFinal.C10BodyWidths
