import Proof.CaseAnalysis.FinalWidthCopies
import Proof.CaseAnalysis.FinalTailComposeVerdict

/-! Paper C.10/C.10.1: one run computes the three estimates and their verdict.
The body below extends the existing three-block body by the six paid physical
width copies. The unchanged length gate then runs that body and the fixed tail.
Every width is the width of its own record, read from a retained block output. -/
namespace NearCubicWires.RepairSource.CloseoutFinal.C10ComposeWidths

open LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairOrdinary.CloseoutRowsOriginalSchedule
open RepairOrdinary.CloseoutFinalC10WorkerChain
open RepairRepresentation CompetitorRationalGap
open C10TailCompose C10BodyWidths C10TailSlotsUniform
open C10TailVerdict (tailBank tailFlag tailSpare scratchT)
open C10TailUniformSlots (phaseIndex widthSlot privateSlot)
open C10TailFeedDockUniform (PhaseParked)
open C10TailVerdictUniform (ParkedThree' TailWidths' tbud)

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def index (ph : Phase) (j : Fin 2) : Fin 6 :=
  ⟨2*(phaseIndex ph).val+j.val, by have := (phaseIndex ph).isLt; have := j.isLt; omega⟩

def lengths (W : Phase → ℕ) (k : Fin 6) : ℕ :=
  if (C10WidthCopies.partOf k).val = 0 then W (C10WidthCopies.phaseOf k)
  else CompetitorRationalDecision.width (W (C10WidthCopies.phaseOf k))

theorem lengths_index (W : Phase → ℕ) (ph : Phase) (j : Fin 2) :
    List.replicate (lengths W (index ph j)) true = widthWord (W ph) j := by
  cases ph <;> fin_cases j <;> rfl

variable (e : ℕ) (he : 58 ≤ e)

theorem dest_index (ph : Phase) (j : Fin 2) :
    C10WidthCopies.dest e (index ph j) = tslot e (widthSlotT ph j) := by
  apply Fin.ext
  change 2+(2*(phaseIndex ph).val+j.val) = 2+2*(phaseIndex ph).val+j.val
  omega

def bodyThree' {bs : Phase → ℕ} (body : (ph : Phase) → LocalBitMultitape.Machine (218+e) (bs ph)) :=
  Composition.machine (bodyThree e body) (C10WidthCopies.copies e he)

def bodyFuel (F W : Phase → ℕ) : ℕ := bodyThreeFuel F+1+C10WidthCopies.budget (lengths W)

def TailBlank (A : Fin (bigOf e) → List Bool) : Prop :=
  ∀ i, 15 ≤ i.val → i.val < 475 → (i.val < 218 ∨ 221 ≤ i.val) → A i = []

theorem body_step {bs : Phase → ℕ} (body : (ph : Phase) → LocalBitMultitape.Machine (218+e) (bs ph))
    (F W : Phase → ℕ) (input witness : List Bool) (rec : Phase → List Bool)
    (hbody : ∀ ph, BlockRunsWidths e he (body ph) (F ph) input witness (rec ph) (W ph)) :
    ∃ A, Step (bodyThree' e he body) (bodyFuel F W) (fun _ => 0)
      (entryOf (gFlag e) input witness) (fun _ => 0) A ∧
      (∀ ph, A (scr e ph) = rec ph) ∧ TailBlank e A ∧ A (tailCnt e) = [] ∧
      (∀ ph j, A (tslot e (widthSlotT ph j)) = widthWord (W ph) j) := by
  obtain ⟨A, hs, hr, hb, hc, hw⟩ := bodyThree_widths e he body F input witness rec W hbody
  have hready : C10WidthCopies.Ready e he (lengths W) 0 A := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro k
      exact hw (C10WidthCopies.phaseOf k) (C10WidthCopies.partOf k)
    · intro k
      rw [if_neg (by omega)]
      exact hb _ ⟨by show 2 ≤ 2+k.val; omega, by have := k.isLt; show 2+k.val < 475; omega,
        Or.inl (by have := k.isLt; show 2+k.val < 218; omega)⟩
    · exact hb _ ⟨by show 2 ≤ 8; omega, by show 8 < 475; omega, Or.inl (by show 8 < 218; omega)⟩
    · intro k _
      exact hb _ ⟨by show 2 ≤ 9+k.val; omega, by have := k.isLt; show 9+k.val < 475; omega,
        Or.inl (by have := k.isLt; show 9+k.val < 218; omega)⟩
  obtain ⟨A', hs', hd, hf⟩ := C10WidthCopies.copies_step e he (lengths W) A hready
  refine ⟨A', hs.seq hs', ?_, ?_, ?_, ?_⟩
  · intro ph
    rw [hf _ (by cases ph <;> norm_num [C10TailCompose.scr, scrVal])]
    exact hr ph
  · intro i hlo hhi hrec
    rw [hf i hlo]
    exact hb i ⟨by omega, hhi, hrec⟩
  · rw [hf _ (by rw [tailCnt_val]; omega)]
    exact hc
  · intro ph j
    rw [← dest_index, hd, lengths_index]

theorem phaseParked_of (W : Phase → ℕ) (est : Phase → CompetitorValidity.Estimate)
    (A : Fin (bigOf e) → List Bool)
    (hrec : ∀ ph, A (scr e ph) = CloseoutRowsEstimatorCoefficients.Stream.recordWord (W ph) (est ph) 1 1)
    (hblank : TailBlank e A)
    (hwidth : ∀ ph j, A (tslot e (widthSlotT ph j)) = widthWord (W ph) j)
    (ph : Phase) :
    PhaseParked ph (W ph) (est ph) (fun _ => 0) (fun i => A (tslot e i)) := by
  have hb (i : Fin tailBank) (hi : 221 ≤ i.val) : A (tslot e i) = [] :=
    hblank _ (by rw [tslot_val]; omega) (by rw [tslot_val]; exact i.isLt) (Or.inr hi)
  have hfw (j : Fin 2) : C10TailVerdict.feedSlots (phaseIndex ph) (widthSlot ph j) = widthSlotT ph j :=
    feedSlots_width _ _ j
  have hfp (j : Fin 29) : C10TailVerdict.feedSlots (phaseIndex ph) (privateSlot ph j) = privateSlotT ph j :=
    feedSlots_private _ _ j
  refine ⟨?_, rfl, fun _ => rfl, ?_, fun _ => rfl, ?_, fun _ => rfl, ?_,
    fun _ => rfl, ?_, fun _ => rfl, ?_, ?_, fun _ => rfl, ?_⟩
  · rw [C10TailVerdict.feedSlots_scratch]
    exact (congrArg A (tslot_scratch e ph)).trans (hrec ph)
  · intro j; exact hb _ (feedSlots_ge _ _ (C10TailVerdict.cmp_ge j))
  · intro j; exact hb _ (feedSlots_ge _ _ (C10TailVerdict.normA_ge j))
  · intro j; exact hb _ (feedSlots_ge _ _ (C10TailVerdict.normB_ge j))
  · intro j; exact hb _ (feedSlots_ge _ _ (C10TailVerdict.word_ge j))
  · rw [hfw]; exact hwidth ph 0
  · rw [hfw]; exact hwidth ph 1
  · intro j
    rw [hfp]
    have hr := privateSlotT_range ph j
    exact hblank _ hr.1 (by rw [tslot_val]; omega) (Or.inl (by rw [tslot_val]; omega))

theorem parkedThree_of' (W : Phase → ℕ) (est : Phase → CompetitorValidity.Estimate)
    (A : Fin (bigOf e) → List Bool)
    (hrec : ∀ ph, A (scr e ph) = CloseoutRowsEstimatorCoefficients.Stream.recordWord (W ph) (est ph) 1 1)
    (hblank : TailBlank e A)
    (hwidth : ∀ ph j, A (tslot e (widthSlotT ph j)) = widthWord (W ph) j) :
    ParkedThree' (W .penalty) (W .moment) (W .clause) (est .penalty) (est .moment) (est .clause)
      (fun _ => 0) (fun i => A (tslot e i)) :=
  ⟨phaseParked_of e W est A hrec hblank hwidth .penalty,
   phaseParked_of e W est A hrec hblank hwidth .moment,
   phaseParked_of e W est A hrec hblank hwidth .clause,
   hblank _ (by show 15 ≤ 473; omega) (by show 473 < 475; omega) (Or.inr (by show 221 ≤ 473; omega)), rfl,
   hblank _ (by show 15 ≤ 474; omega) (by show 474 < 475; omega) (Or.inr (by show 221 ≤ 474; omega)), rfl⟩

def UniformTail' {ts : ℕ} (m : LocalBitMultitape.Machine tailBank ts) (budget : ℕ → ℕ)
    {source : PointwisePCPPAlgorithm} (constants : Constants source) : Prop :=
  ∀ (bP bM bC : ℕ) (eP eM eC : CompetitorValidity.Estimate),
    eP.Valid bP → eM.Valid bM → eC.Valid bC → TailWidths' constants bP bM bC →
    ∀ (H : Fin tailBank → ℕ) (A : Fin tailBank → List Bool),
      ParkedThree' bP bM bC eP eM eC H A →
      ∃ H' A', Step m (budget (max bP (max bM bC))) H A H' A' ∧
        (readTapeBit (A' tailFlag) 0 = true ↔
          (CompetitorThresholdDecision.estimate eP.positive eP.negative eP.denominator ≤ 2*zeta constants ∧
           CompetitorThresholdDecision.estimate eM.positive eM.negative eM.denominator ≤ 1+zeta constants ∧
           midpoint constants ≤ CompetitorThresholdDecision.estimate eC.positive eC.negative eC.denominator)) ∧
        (∀ i, PublicPrefix i → A' i = A i)

def maxWidth (W : Phase → ℕ) : ℕ := max (W .penalty) (max (W .moment) (W .clause))

def innerOf' {bs : Phase → ℕ} {ts : ℕ}
    (body : (ph : Phase) → LocalBitMultitape.Machine (218+e) (bs ph))
    (m : LocalBitMultitape.Machine tailBank ts) :=
  Composition.machine (bodyThree' e he body) (RecoveryFocus.machine (rtslot e) (Rewind.machine m))

def composedWorker' {bs : Phase → ℕ} {ts : ℕ} (onset : ℕ)
    (body : (ph : Phase) → LocalBitMultitape.Machine (218+e) (bs ph))
    (m : LocalBitMultitape.Machine tailBank ts) :=
  worker onset (gInput e) (gFlag e) (gResult e) (innerOf' e he body m)

def innerFuel (F W : Phase → ℕ) (budget : ℕ → ℕ) : ℕ :=
  bodyFuel F W+1+(2*budget (maxWidth W)+2)

theorem verdict_run_uniform' {bs : Phase → ℕ} {ts : ℕ}
    (body : (ph : Phase) → LocalBitMultitape.Machine (218+e) (bs ph)) (F W : Phase → ℕ)
    (m : LocalBitMultitape.Machine tailBank ts) (budget : ℕ → ℕ)
    {source : PointwisePCPPAlgorithm} (constants : Constants source)
    (htail : UniformTail' m budget constants) (est : Phase → CompetitorValidity.Estimate)
    (hv : ∀ ph, (est ph).Valid (W ph))
    (hwidth : TailWidths' constants (W .penalty) (W .moment) (W .clause))
    (onset len : ℕ) (x : BitInput len) (bits : List Bool) (honset : onset ≤ len)
    (hbody : ∀ ph, BlockRunsWidths e he (body ph) (F ph) (List.ofFn x) bits
      (CloseoutRowsEstimatorCoefficients.Stream.recordWord (W ph) (est ph) 1 1) (W ph)) :
    ∃ A, Step (composedWorker' e he onset body m)
      (workerBudget onset (fun _ => innerFuel F W budget) len) (fun _ => 0)
      ((UAcceptanceCarrier.verifier (composedWorker' e he onset body m)
        (bigTwo e) (gResult e)).inputTapes (List.ofFn x) bits) (fun _ => 0) A ∧
      (readTapeBit (A (gResult e)) 0 = true ↔
        (CompetitorThresholdDecision.estimate (est .penalty).positive (est .penalty).negative
          (est .penalty).denominator ≤ 2*zeta constants ∧
         CompetitorThresholdDecision.estimate (est .moment).positive (est .moment).negative
          (est .moment).denominator ≤ 1+zeta constants ∧
         midpoint constants ≤ CompetitorThresholdDecision.estimate (est .clause).positive
          (est .clause).negative (est .clause).denominator)) ∧
      (∀ ph, A (scr e ph) = CloseoutRowsEstimatorCoefficients.Stream.recordWord (W ph) (est ph) 1 1) := by
  obtain ⟨Ab, hb, hr, hblank, hc, hw⟩ := body_step e he body F W (List.ofFn x) bits
    (fun ph => CloseoutRowsEstimatorCoefficients.Stream.recordWord (W ph) (est ph) 1 1) hbody
  have hp := parkedThree_of' e W est Ab hr hblank hw
  obtain ⟨H', A', ht, hiff, hpre⟩ := htail (W .penalty) (W .moment) (W .clause)
    (est .penalty) (est .moment) (est .clause) (hv .penalty) (hv .moment) (hv .clause)
    hwidth (fun _ => 0) (fun i => Ab (tslot e i)) hp
  obtain ⟨A2, hd, hval⟩ := tail_dock e m (budget (maxWidth W)) H' A' Ab ht hc
  refine ⟨A2, gate_of_inner e (innerOf' e he body m) _ onset len x bits honset A2 (hb.seq hd), ?_, ?_⟩
  · rw [← tslot_flag e, hval tailFlag]
    exact hiff
  · intro ph
    rw [← tslot_scratch e ph, hval (scratchT ph), hpre _ (scratch_public ph), tslot_scratch]
    exact hr ph

end
end NearCubicWires.RepairSource.CloseoutFinal.C10ComposeWidths
