import Proof.CaseAnalysis.FinalTailAnd
import Proof.CaseAnalysis.FinalTailFeedPrep

namespace NearCubicWires.RepairSource.CloseoutFinal.C10TailVerdict

open NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation
open LocalBitMultitape ExtDecompositionBatch
open CompetitorThresholdDecision
open NearCubicWires.RepairSource.CompetitorRationalGap
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.CloseoutFinal.C10CompareDockLit
open NearCubicWires.RepairSource.CloseoutFinal.C10LengthGate
open NearCubicWires.RepairSource.CloseoutFinal.C10TailSlots
open NearCubicWires.RepairSource.CloseoutFinal.C10TailFeedPrep
open NearCubicWires.RepairSource.CloseoutFinal.C10TailAnd

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ### The verdict bank -/

/-- The verdict bank: the feed bank's shared prefix `0 … 220` (worker `0 … 217`
and the three phase records `218/219/220`), three private copies of the feed's
84 tail tapes `221 … 304` (landing at `221 … 304`, `305 … 388`, `389 … 472`), the
AND flag `tailFlag = 473`, and one blank spare `tailSpare = 474` for its literal
word. -/
abbrev tailBank : ℕ := 475

/-- The AND flag: paper C.10's single "passes validity and accepts" bit. -/
def tailFlag : Fin tailBank := ⟨473, by show 473 < 475; omega⟩
/-- The blank second tape `HierarchyFixedWord.machine` needs to write `[false]`. -/
def tailSpare : Fin tailBank := ⟨474, by show 474 < 475; omega⟩

/-- Slot `i` of the feed bank inside private copy `k`. -/
def feedIdx (k : Fin 3) (i : Fin bank) : ℕ :=
  if i.val < 221 then i.val else 221 + 84*k.val + (i.val - 221)

theorem feedIdx_lt_flag (k : Fin 3) (i : Fin bank) : feedIdx k i < 473 := by
  have hi : i.val < 305 := i.isLt
  have hk : k.val < 3 := k.isLt
  unfold feedIdx
  split <;> omega

theorem feedIdx_lt (k : Fin 3) (i : Fin bank) : feedIdx k i < 475 := by
  have := feedIdx_lt_flag k i
  omega

/-- **The three docking maps.** Identity on `0 … 220`; `221 … 304` into copy `k`. -/
def feedSlots (k : Fin 3) (i : Fin bank) : Fin tailBank := ⟨feedIdx k i, feedIdx_lt k i⟩

theorem feedSlots_injective (k : Fin 3) : Function.Injective (feedSlots k) := by
  intro i j h
  have hv : feedIdx k i = feedIdx k j := congrArg Fin.val h
  apply Fin.ext
  unfold feedIdx at hv
  by_cases h1 : i.val < 221
  · rw [if_pos h1] at hv
    by_cases h2 : j.val < 221
    · rw [if_pos h2] at hv
      exact hv
    · rw [if_neg h2] at hv
      omega
  · rw [if_neg h1] at hv
    by_cases h2 : j.val < 221
    · rw [if_pos h2] at hv
      omega
    · rw [if_neg h2] at hv
      omega

/-- **Pairwise disjointness.** No slot of copy `k` hits a private tape of copy
`k'`. (The shared prefix `0 … 220` is deliberately NOT disjoint: all three copies
read the same three phase records.) -/
theorem feedSlots_disjoint {k k' : Fin 3} (hk : k ≠ k') (i : Fin bank) (hi : 221 ≤ i.val)
    (j : Fin bank) : feedSlots k j ≠ feedSlots k' i := by
  intro h
  have hv : feedIdx k j = feedIdx k' i := congrArg Fin.val h
  have hkne : k.val ≠ k'.val := fun hh => hk (Fin.ext hh)
  have hj : j.val < 305 := j.isLt
  have hi2 : i.val < 305 := i.isLt
  have hk3 : k.val < 3 := k.isLt
  have hk4 : k'.val < 3 := k'.isLt
  unfold feedIdx at hv
  rw [if_neg (by omega : ¬ i.val < 221)] at hv
  by_cases hjj : j.val < 221
  · rw [if_pos hjj] at hv
    omega
  · rw [if_neg hjj] at hv
    omega

theorem feedSlots_ne_flag (k : Fin 3) (i : Fin bank) : feedSlots k i ≠ tailFlag := by
  intro h
  have hv : feedIdx k i = 473 := congrArg Fin.val h
  have hlt := feedIdx_lt_flag k i
  omega

theorem feedSlots_ne_spare (k : Fin 3) (i : Fin bank) : feedSlots k i ≠ tailSpare := by
  intro h
  have hv : feedIdx k i = 474 := congrArg Fin.val h
  have hlt := feedIdx_lt_flag k i
  omega

theorem flag_ne_spare : tailFlag ≠ tailSpare := by
  intro h
  have hv : (473 : ℕ) = 474 := congrArg Fin.val h
  omega

/-- The shared-prefix slot of `i`, seen inside the feed bank. -/
def preIdx (i : Fin tailBank) (h : i.val < 221) : Fin bank :=
  ⟨i.val, by show i.val < 218 + 87; omega⟩

theorem feedSlots_pre (k : Fin 3) (i : Fin tailBank) (h : i.val < 221) :
    feedSlots k (preIdx i h) = i := by
  apply Fin.ext
  show (if i.val < 221 then i.val else 221 + 84*k.val + (i.val - 221)) = i.val
  rw [if_pos h]

/-- The three phase records, on the shared prefix. -/
def scratchT (ph : CloseoutRowsOriginalSchedule.Phase) : Fin tailBank :=
  match ph with
  | .penalty => ⟨218, by show 218 < 475; omega⟩
  | .moment => ⟨219, by show 219 < 475; omega⟩
  | .clause => ⟨220, by show 220 < 475; omega⟩

theorem scratchT_lt (ph : CloseoutRowsOriginalSchedule.Phase) : (scratchT ph).val < 221 := by
  cases ph <;> decide

theorem feedSlots_scratch (k : Fin 3) (ph : CloseoutRowsOriginalSchedule.Phase) :
    feedSlots k (scratch ph) = scratchT ph := by
  apply Fin.ext
  cases ph <;> rfl

theorem scratchT_ne_of_val {ph ph' : CloseoutRowsOriginalSchedule.Phase}
    (h : (scratchT ph).val ≠ (scratchT ph').val) : scratchT ph ≠ scratchT ph' :=
  fun hc => h (congrArg Fin.val hc)

/-! ### Every block slot lives above the shared prefix -/

theorem cmp_ge (j : Fin 67) : 221 ≤ (cmpSlots j).val := by
  show 221 ≤ 221 + j.val
  omega
theorem normA_ge (j : Fin 5) : 221 ≤ (normSlots j).val := by
  show 221 ≤ 288 + j.val
  omega
theorem normB_ge (j : Fin 5) : 221 ≤ (normSlotsB j).val := by
  show 221 ≤ 293 + j.val
  omega
theorem word_ge (j : Fin 6) : 221 ≤ (wordSlots j).val := by
  show 221 ≤ 298 + j.val
  omega

theorem cmp_ne_pre (j : Fin bank) (hj : j.val < 221) (i : Fin 67) : cmpSlots i ≠ j := by
  intro h
  have hv : (cmpSlots i).val = j.val := congrArg Fin.val h
  have hge := cmp_ge i
  omega
theorem normA_ne_pre (j : Fin bank) (hj : j.val < 221) (i : Fin 5) : normSlots i ≠ j := by
  intro h
  have hv : (normSlots i).val = j.val := congrArg Fin.val h
  have hge := normA_ge i
  omega
theorem normB_ne_pre (j : Fin bank) (hj : j.val < 221) (i : Fin 5) : normSlotsB i ≠ j := by
  intro h
  have hv : (normSlotsB i).val = j.val := congrArg Fin.val h
  have hge := normB_ge i
  omega
theorem word_ne_pre (j : Fin bank) (hj : j.val < 221) (i : Fin 6) : wordSlots i ≠ j := by
  intro h
  have hv : (wordSlots i).val = j.val := congrArg Fin.val h
  have hge := word_ge i
  omega

/-! ### A two-slot map on the verdict bank, for the flag's literal word -/

def pairT (src dst : Fin tailBank) (i : Fin 2) : Fin tailBank := if i.val = 0 then src else dst

theorem pairT_injective (src dst : Fin tailBank) (hne : src ≠ dst) :
    Function.Injective (pairT src dst) := by
  intro i j h
  fin_cases i <;> fin_cases j
  · rfl
  · have h' : src = dst := by simpa [pairT] using h
    exact absurd h' hne
  · have h' : dst = src := by simpa [pairT] using h
    exact absurd h'.symm hne
  · rfl

theorem pairT_ne {src dst i : Fin tailBank} (h1 : src ≠ i) (h2 : dst ≠ i) (j : Fin 2) :
    pairT src dst j ≠ i := by
  fin_cases j
  · simpa [pairT] using h1
  · simpa [pairT] using h2

/-- **Initialise the flag.** `and3` needs `A res = [false]`; a two-tape
`HierarchyFixedWord` literal writes it from blanks and returns both heads to `0`. -/
theorem flag_init (H : Fin tailBank → ℕ) (A : Fin tailBank → List Bool)
    (hfH : H tailFlag = 0) (hsH : H tailSpare = 0)
    (hfA : A tailFlag = []) (hsA : A tailSpare = []) :
    Step (RecoveryFocus.machine (pairT tailFlag tailSpare) (HierarchyFixedWord.machine [false]))
      4 H A H (install (pairT tailFlag tailSpare) A ![[false], List.replicate 1 false]) := by
  have hH : ∀ j, H (pairT tailFlag tailSpare j) = 0 := by
    intro j
    fin_cases j
    · simpa [pairT] using hfH
    · simpa [pairT] using hsH
  have hA : ∀ j, A (pairT tailFlag tailSpare j) = [] := by
    intro j
    fin_cases j
    · simpa [pairT] using hfA
    · simpa [pairT] using hsA
  have hstep := (word_step [false]).dock (pairT tailFlag tailSpare)
    (pairT_injective tailFlag tailSpare flag_ne_spare) H A hH hA
  rwa [dockH_existing (pairT tailFlag tailSpare) H (fun _ => 0) hH] at hstep

/-! ### The AND, with its frame -/

/-- `and3_step` with the extra "nothing but `res` moves" conjunct that the tail's
`A' i = A i` clause needs; same four-case proof. -/
theorem and3_step_frame {u : ℕ} (f1 f2 f3 res : Fin u)
    (H : Fin u → ℕ) (A : Fin u → List Bool)
    (hH1 : H f1 = 0) (hH2 : H f2 = 0) (hH3 : H f3 = 0) (hHr : H res = 0)
    (hAr : A res = [false]) :
    ∃ tout : Fin u → List Bool,
      Step (and3 f1 f2 f3 res) 4 H A H tout ∧
      (readTapeBit (tout res) 0 = true ↔
        (readTapeBit (A f1) 0 = true ∧ readTapeBit (A f2) 0 = true ∧
          readTapeBit (A f3) 0 = true)) ∧
      (∀ i, i ≠ res → tout i = A i) := by
  have hself := exitTapes_false_self res A hAr
  have hr0 : readTapeBit (A res) 0 = false := by simp [hAr, readTapeBit]
  cases hb1 : readTapeBit (A f1) 0
  · refine ⟨A, ?_, ?_, ?_⟩
    · have h := branch_reject f1 res (and2 f2 f3 res) H A (by rw [hH1]; exact hb1)
      rw [hHr, hself] at h
      exact Step.enlarge h (by norm_num)
    · simp [hr0]
    · intro i _
      rfl
  cases hb2 : readTapeBit (A f2) 0
  · refine ⟨A, ?_, ?_, ?_⟩
    · have inner := branch_reject f2 res (and1 f3 res) H A (by rw [hH2]; exact hb2)
      rw [hHr, hself] at inner
      have h := branch_pass f1 res (and2 f2 f3 res) H A (by rw [hH1]; exact hb1) 1 H A inner
      exact Step.enlarge h (by norm_num)
    · simp [hr0]
    · intro i _
      rfl
  cases hb3 : readTapeBit (A f3) 0
  · refine ⟨A, ?_, ?_, ?_⟩
    · have inner := branch_reject f3 res (setSlot res) H A (by rw [hH3]; exact hb3)
      rw [hHr, hself] at inner
      have mid := branch_pass f2 res (and1 f3 res) H A (by rw [hH2]; exact hb2) 1 H A inner
      have h := branch_pass f1 res (and2 f2 f3 res) H A (by rw [hH1]; exact hb1) 2 H A mid
      exact Step.enlarge h (by norm_num)
    · simp [hr0]
    · intro i _
      rfl
  · refine ⟨Function.update A res [true], ?_, ?_, ?_⟩
    · have inner := setSlot_step res H A hHr hAr
      have l3 := branch_pass f3 res (setSlot res) H A (by rw [hH3]; exact hb3) 1 H _ inner
      have l2 := branch_pass f2 res (and1 f3 res) H A (by rw [hH2]; exact hb2) 2 H _ l3
      exact branch_pass f1 res (and2 f2 f3 res) H A (by rw [hH1]; exact hb1) 3 H _ l2
    · simp [readTapeBit]
    · intro i hi
      exact Function.update_of_ne hi _ _

/-! ### The T1 → T2 interface -/

def FeedInterface : Prop :=
  ∀ (ph : CloseoutRowsOriginalSchedule.Phase) (lower : Bool) (q : ℚ) (W : ℕ)
    (est : CompetitorValidity.Estimate) (_hv : est.Valid W)
    (_hq : 0 ≤ q) (_hqnum : numerator q < 2^(w W)) (_hqden : q.den < 2^(w W))
    (H : Fin bank → ℕ) (A : Fin bank → List Bool) (_hp : Parked ph W est H A),
    ∃ (states : ℕ) (m : Machine bank states) (budget : ℕ) (H' : Fin bank → ℕ)
      (A' : Fin bank → List Bool),
      Step m budget H A H' A' ∧
      (readTapeBit (A' (cmpSlots 65)) 0 = true ↔
        passes lower est.positive est.negative est.denominator q) ∧
      (∀ i, (∀ j, cmpSlots j ≠ i) → (∀ j, normSlots j ≠ i) → (∀ j, normSlotsB j ≠ i) →
        (∀ j, wordSlots j ≠ i) → i ≠ scratch ph → A' i = A i) ∧
      (∀ i, (∀ j, cmpSlots j ≠ i) → (∀ j, normSlots j ≠ i) → (∀ j, normSlotsB j ≠ i) →
        (∀ j, wordSlots j ≠ i) → i ≠ scratch ph → H' i = H i) ∧
      H' (cmpSlots 65) = 0 ∧
      A' (scratch ph) = A (scratch ph)

/-! ### One feed, docked into the verdict bank -/

/-- **One phase's test, run on copy `k` of the verdict bank.** -/
theorem feed_dock (hfeed : FeedInterface) (k : Fin 3)
    (ph : CloseoutRowsOriginalSchedule.Phase) (lower : Bool) (q : ℚ) (W : ℕ)
    (est : CompetitorValidity.Estimate) (hv : est.Valid W)
    (hq : 0 ≤ q) (hqnum : numerator q < 2^(w W)) (hqden : q.den < 2^(w W))
    (H : Fin tailBank → ℕ) (A : Fin tailBank → List Bool)
    (hrecA : A (scratchT ph) =
      CloseoutRowsEstimatorCoefficients.Stream.recordWord (w W) est 1 1)
    (hrecH : H (scratchT ph) = 0)
    (hcA : ∀ j, A (feedSlots k (cmpSlots j)) = [])
    (hcH : ∀ j, H (feedSlots k (cmpSlots j)) = 0)
    (hnA : ∀ j, A (feedSlots k (normSlots j)) = [])
    (hnH : ∀ j, H (feedSlots k (normSlots j)) = 0)
    (hbA : ∀ j, A (feedSlots k (normSlotsB j)) = [])
    (hbH : ∀ j, H (feedSlots k (normSlotsB j)) = 0)
    (hwA : ∀ j, A (feedSlots k (wordSlots j)) = [])
    (hwH : ∀ j, H (feedSlots k (wordSlots j)) = 0) :
    ∃ (states : ℕ) (m : Machine tailBank states) (budget : ℕ) (H' : Fin tailBank → ℕ)
      (A' : Fin tailBank → List Bool),
      Step m budget H A H' A' ∧
      (readTapeBit (A' (feedSlots k (cmpSlots 65))) 0 = true ↔
        passes lower est.positive est.negative est.denominator q) ∧
      H' (feedSlots k (cmpSlots 65)) = 0 ∧
      (∀ i, i.val < 221 → A' i = A i) ∧
      (∀ i, i.val < 221 → i ≠ scratchT ph → H' i = H i) ∧
      (∀ i, (∀ j, feedSlots k j ≠ i) → A' i = A i) ∧
      (∀ i, (∀ j, feedSlots k j ≠ i) → H' i = H i) := by
  have hp : Parked ph W est (fun j => H (feedSlots k j)) (fun j => A (feedSlots k j)) := by
    refine ⟨?_, ?_, hcH, hcA, hnH, hnA, hbH, hbA, hwH, hwA⟩
    · show A (feedSlots k (scratch ph)) = _
      rw [feedSlots_scratch]
      exact hrecA
    · show H (feedSlots k (scratch ph)) = 0
      rw [feedSlots_scratch]
      exact hrecH
  obtain ⟨states, m, budget, Hf, Af, hstep, hiff, htapes, hheads, hcmp65, hscr⟩ :=
    hfeed ph lower q W est hv hq hqnum hqden _ _ hp
  have hinj := feedSlots_injective k
  have hdock := hstep.dock (feedSlots k) hinj H A (fun _ => rfl) (fun _ => rfl)
  have hchaseA : ∀ j : Fin bank, j.val < 221 → Af j = A (feedSlots k j) := by
    intro j hj
    by_cases hs : j = scratch ph
    · rw [hs]
      exact hscr
    · exact htapes j (cmp_ne_pre j hj) (normA_ne_pre j hj) (normB_ne_pre j hj)
        (word_ne_pre j hj) hs
  have hchaseH : ∀ j : Fin bank, j.val < 221 → j ≠ scratch ph → Hf j = H (feedSlots k j) := by
    intro j hj hs
    exact hheads j (cmp_ne_pre j hj) (normA_ne_pre j hj) (normB_ne_pre j hj)
      (word_ne_pre j hj) hs
  refine ⟨states, RecoveryFocus.machine (feedSlots k) m, budget,
    dockH (feedSlots k) H Hf, install (feedSlots k) A Af, hdock, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [install_slot (feedSlots k) hinj A Af (cmpSlots 65)]
    exact hiff
  · rw [dockH_slot (feedSlots k) hinj H Hf (cmpSlots 65)]
    exact hcmp65
  · intro i hi
    have he : feedSlots k (preIdx i hi) = i := feedSlots_pre k i hi
    calc install (feedSlots k) A Af i
        = install (feedSlots k) A Af (feedSlots k (preIdx i hi)) := by rw [he]
      _ = Af (preIdx i hi) := install_slot (feedSlots k) hinj A Af (preIdx i hi)
      _ = A (feedSlots k (preIdx i hi)) := hchaseA (preIdx i hi) hi
      _ = A i := by rw [he]
  · intro i hi hnei
    have he : feedSlots k (preIdx i hi) = i := feedSlots_pre k i hi
    have hne : preIdx i hi ≠ scratch ph := by
      intro hc
      apply hnei
      rw [← he, hc, feedSlots_scratch]
    calc dockH (feedSlots k) H Hf i
        = dockH (feedSlots k) H Hf (feedSlots k (preIdx i hi)) := by rw [he]
      _ = Hf (preIdx i hi) := dockH_slot (feedSlots k) hinj H Hf (preIdx i hi)
      _ = H (feedSlots k (preIdx i hi)) := hchaseH (preIdx i hi) hi hne
      _ = H i := by rw [he]
  · intro i hi
    exact install_other (feedSlots k) A Af i hi
  · intro i hi
    exact dockH_other (feedSlots k) H Hf i hi

/-! ### The parked verdict bank -/

/-- **The tail's entry state.** The three phase records sit on the shared prefix
at heads `0`; every private block copy is blank at head `0`; the AND flag and its
spare are blank at head `0`. -/
structure ParkedThree (W : ℕ) (estP estM estC : CompetitorValidity.Estimate)
    (H : Fin tailBank → ℕ) (A : Fin tailBank → List Bool) : Prop where
  recP : A (scratchT .penalty) =
    CloseoutRowsEstimatorCoefficients.Stream.recordWord (w W) estP 1 1
  recM : A (scratchT .moment) =
    CloseoutRowsEstimatorCoefficients.Stream.recordWord (w W) estM 1 1
  recC : A (scratchT .clause) =
    CloseoutRowsEstimatorCoefficients.Stream.recordWord (w W) estC 1 1
  recH : ∀ ph, H (scratchT ph) = 0
  cmpA : ∀ k j, A (feedSlots k (cmpSlots j)) = []
  cmpH : ∀ k j, H (feedSlots k (cmpSlots j)) = 0
  nAA : ∀ k j, A (feedSlots k (normSlots j)) = []
  nAH : ∀ k j, H (feedSlots k (normSlots j)) = 0
  nBA : ∀ k j, A (feedSlots k (normSlotsB j)) = []
  nBH : ∀ k j, H (feedSlots k (normSlotsB j)) = 0
  wdA : ∀ k j, A (feedSlots k (wordSlots j)) = []
  wdH : ∀ k j, H (feedSlots k (wordSlots j)) = 0
  flagA : A tailFlag = []
  flagH : H tailFlag = 0
  spareA : A tailSpare = []
  spareH : H tailSpare = 0

/-! ### The two directions of `passes` -/

theorem passes_false (p n d : ℕ) (q : ℚ) : passes false p n d q ↔ estimate p n d ≤ q := by
  simp [passes]

theorem passes_true (p n d : ℕ) (q : ℚ) : passes true p n d q ↔ q ≤ estimate p n d := by
  simp [passes]

/-! ### The theorem -/

/-- **Paper C.10 and C.10.1, physically.** From a parked verdict bank one machine
runs the mean test (`estimate ≤ 2*zeta`), the second-moment test
(`estimate ≤ 1+zeta`) and the acceptance test (`midpoint ≤ estimate`); `tailFlag`
reads `true` exactly when all three hold, and the worker bank together with the
three phase records is returned untouched. -/
theorem tail_step {source : PointwisePCPPAlgorithm} (constants : Constants source) (W : ℕ)
    (estP estM estC : CompetitorValidity.Estimate)
    (hvP : estP.Valid W) (hvM : estM.Valid W) (hvC : estC.Valid W)
    (hwidth : numerator (meanThreshold constants) < 2^(w W) ∧
      (meanThreshold constants).den < 2^(w W) ∧
      numerator (momentThreshold constants) < 2^(w W) ∧
      (momentThreshold constants).den < 2^(w W) ∧
      numerator (acceptanceThreshold constants) < 2^(w W) ∧
      (acceptanceThreshold constants).den < 2^(w W))
    (H : Fin tailBank → ℕ) (A : Fin tailBank → List Bool)
    (hparked : ParkedThree W estP estM estC H A)
    (hfeed : FeedInterface) :
    ∃ (states : ℕ) (m : Machine tailBank states) (budget : ℕ) (H' : Fin tailBank → ℕ)
      (A' : Fin tailBank → List Bool),
      Step m budget H A H' A' ∧
      (readTapeBit (A' tailFlag) 0 = true ↔
        (estimate estP.positive estP.negative estP.denominator ≤ 2*zeta constants ∧
         estimate estM.positive estM.negative estM.denominator ≤ 1+zeta constants ∧
         midpoint constants ≤ estimate estC.positive estC.negative estC.denominator)) ∧
      (∀ i, i.val < 221 → A' i = A i) := by
  obtain ⟨hmn, hmd, hMn, hMd, hcn, hcd⟩ := hwidth
  have hq0 : (0 : ℚ) ≤ meanThreshold constants := by
    unfold meanThreshold
    exact mul_nonneg (by norm_num) (zeta_positive constants).le
  have hq1 : (0 : ℚ) ≤ momentThreshold constants := by
    unfold momentThreshold
    linarith [zeta_positive constants]
  have hq2 : (0 : ℚ) ≤ acceptanceThreshold constants := (midpoint_positive constants).le
  -- feed 0 : the mean test, on copy 0
  obtain ⟨s0, m0, b0, H1, A1, hstep0, hiff0, hh0, hpreA0, hpreH0, houtA0, houtH0⟩ :=
    feed_dock hfeed 0 .penalty false (meanThreshold constants) W estP hvP hq0 hmn hmd H A
      hparked.recP (hparked.recH _)
      (fun j => hparked.cmpA 0 j) (fun j => hparked.cmpH 0 j)
      (fun j => hparked.nAA 0 j) (fun j => hparked.nAH 0 j)
      (fun j => hparked.nBA 0 j) (fun j => hparked.nBH 0 j)
      (fun j => hparked.wdA 0 j) (fun j => hparked.wdH 0 j)
  have hd01 : ∀ (i : Fin bank), 221 ≤ i.val → ∀ j, feedSlots 0 j ≠ feedSlots 1 i :=
    fun i hi j => feedSlots_disjoint (by decide) i hi j
  have hd02 : ∀ (i : Fin bank), 221 ≤ i.val → ∀ j, feedSlots 0 j ≠ feedSlots 2 i :=
    fun i hi j => feedSlots_disjoint (by decide) i hi j
  have hd12 : ∀ (i : Fin bank), 221 ≤ i.val → ∀ j, feedSlots 1 j ≠ feedSlots 2 i :=
    fun i hi j => feedSlots_disjoint (by decide) i hi j
  have hd10 : ∀ (i : Fin bank), 221 ≤ i.val → ∀ j, feedSlots 1 j ≠ feedSlots 0 i :=
    fun i hi j => feedSlots_disjoint (by decide) i hi j
  have hd20 : ∀ (i : Fin bank), 221 ≤ i.val → ∀ j, feedSlots 2 j ≠ feedSlots 0 i :=
    fun i hi j => feedSlots_disjoint (by decide) i hi j
  have hd21 : ∀ (i : Fin bank), 221 ≤ i.val → ∀ j, feedSlots 2 j ≠ feedSlots 1 i :=
    fun i hi j => feedSlots_disjoint (by decide) i hi j
  -- feed 1 : the second-moment test, on copy 1
  obtain ⟨s1, m1, b1, H2, A2, hstep1, hiff1, hh1, hpreA1, hpreH1, houtA1, houtH1⟩ :=
    feed_dock hfeed 1 .moment false (momentThreshold constants) W estM hvM hq1 hMn hMd H1 A1
      ((hpreA0 (scratchT .moment) (scratchT_lt _)).trans hparked.recM)
      ((hpreH0 (scratchT .moment) (scratchT_lt _)
        (scratchT_ne_of_val (by decide))).trans (hparked.recH _))
      (fun j => (houtA0 _ (hd01 (cmpSlots j) (cmp_ge j))).trans (hparked.cmpA 1 j))
      (fun j => (houtH0 _ (hd01 (cmpSlots j) (cmp_ge j))).trans (hparked.cmpH 1 j))
      (fun j => (houtA0 _ (hd01 (normSlots j) (normA_ge j))).trans (hparked.nAA 1 j))
      (fun j => (houtH0 _ (hd01 (normSlots j) (normA_ge j))).trans (hparked.nAH 1 j))
      (fun j => (houtA0 _ (hd01 (normSlotsB j) (normB_ge j))).trans (hparked.nBA 1 j))
      (fun j => (houtH0 _ (hd01 (normSlotsB j) (normB_ge j))).trans (hparked.nBH 1 j))
      (fun j => (houtA0 _ (hd01 (wordSlots j) (word_ge j))).trans (hparked.wdA 1 j))
      (fun j => (houtH0 _ (hd01 (wordSlots j) (word_ge j))).trans (hparked.wdH 1 j))
  -- feed 2 : the acceptance test, on copy 2
  obtain ⟨s2, m2, b2, H3, A3, hstep2, hiff2, hh2, hpreA2, _hpreH2, houtA2, houtH2⟩ :=
    feed_dock hfeed 2 .clause true (acceptanceThreshold constants) W estC hvC hq2 hcn hcd H2 A2
      ((hpreA1 (scratchT .clause) (scratchT_lt _)).trans
        ((hpreA0 (scratchT .clause) (scratchT_lt _)).trans hparked.recC))
      ((hpreH1 (scratchT .clause) (scratchT_lt _) (scratchT_ne_of_val (by decide))).trans
        ((hpreH0 (scratchT .clause) (scratchT_lt _)
          (scratchT_ne_of_val (by decide))).trans (hparked.recH _)))
      (fun j => (houtA1 _ (hd12 (cmpSlots j) (cmp_ge j))).trans
        ((houtA0 _ (hd02 (cmpSlots j) (cmp_ge j))).trans (hparked.cmpA 2 j)))
      (fun j => (houtH1 _ (hd12 (cmpSlots j) (cmp_ge j))).trans
        ((houtH0 _ (hd02 (cmpSlots j) (cmp_ge j))).trans (hparked.cmpH 2 j)))
      (fun j => (houtA1 _ (hd12 (normSlots j) (normA_ge j))).trans
        ((houtA0 _ (hd02 (normSlots j) (normA_ge j))).trans (hparked.nAA 2 j)))
      (fun j => (houtH1 _ (hd12 (normSlots j) (normA_ge j))).trans
        ((houtH0 _ (hd02 (normSlots j) (normA_ge j))).trans (hparked.nAH 2 j)))
      (fun j => (houtA1 _ (hd12 (normSlotsB j) (normB_ge j))).trans
        ((houtA0 _ (hd02 (normSlotsB j) (normB_ge j))).trans (hparked.nBA 2 j)))
      (fun j => (houtH1 _ (hd12 (normSlotsB j) (normB_ge j))).trans
        ((houtH0 _ (hd02 (normSlotsB j) (normB_ge j))).trans (hparked.nBH 2 j)))
      (fun j => (houtA1 _ (hd12 (wordSlots j) (word_ge j))).trans
        ((houtA0 _ (hd02 (wordSlots j) (word_ge j))).trans (hparked.wdA 2 j)))
      (fun j => (houtH1 _ (hd12 (wordSlots j) (word_ge j))).trans
        ((houtH0 _ (hd02 (wordSlots j) (word_ge j))).trans (hparked.wdH 2 j)))
  -- the flag and its spare survive all three feeds
  have hflagA : A3 tailFlag = [] :=
    (houtA2 _ (fun j => feedSlots_ne_flag 2 j)).trans
      ((houtA1 _ (fun j => feedSlots_ne_flag 1 j)).trans
        ((houtA0 _ (fun j => feedSlots_ne_flag 0 j)).trans hparked.flagA))
  have hflagH : H3 tailFlag = 0 :=
    (houtH2 _ (fun j => feedSlots_ne_flag 2 j)).trans
      ((houtH1 _ (fun j => feedSlots_ne_flag 1 j)).trans
        ((houtH0 _ (fun j => feedSlots_ne_flag 0 j)).trans hparked.flagH))
  have hspareA : A3 tailSpare = [] :=
    (houtA2 _ (fun j => feedSlots_ne_spare 2 j)).trans
      ((houtA1 _ (fun j => feedSlots_ne_spare 1 j)).trans
        ((houtA0 _ (fun j => feedSlots_ne_spare 0 j)).trans hparked.spareA))
  have hspareH : H3 tailSpare = 0 :=
    (houtH2 _ (fun j => feedSlots_ne_spare 2 j)).trans
      ((houtH1 _ (fun j => feedSlots_ne_spare 1 j)).trans
        ((houtH0 _ (fun j => feedSlots_ne_spare 0 j)).trans hparked.spareH))
  -- write `[false]` on the flag
  have hinit := flag_init H3 A3 hflagH hspareH hflagA hspareA
  obtain ⟨A4, hA4⟩ : ∃ X : Fin tailBank → List Bool,
      X = install (pairT tailFlag tailSpare) A3 ![[false], List.replicate 1 false] := ⟨_, rfl⟩
  rw [← hA4] at hinit
  have hpairNe : ∀ (k : Fin 3) (i : Fin bank), ∀ j, pairT tailFlag tailSpare j ≠ feedSlots k i :=
    fun k i j => pairT_ne (Ne.symm (feedSlots_ne_flag k i)) (Ne.symm (feedSlots_ne_spare k i)) j
  have hA4f1 : A4 (feedSlots 0 (cmpSlots 65)) = A1 (feedSlots 0 (cmpSlots 65)) := by
    rw [hA4]
    exact (install_other (pairT tailFlag tailSpare) A3 _ _ (hpairNe 0 (cmpSlots 65))).trans
      ((houtA2 _ (hd20 (cmpSlots 65) (cmp_ge 65))).trans
        (houtA1 _ (hd10 (cmpSlots 65) (cmp_ge 65))))
  have hA4f2 : A4 (feedSlots 1 (cmpSlots 65)) = A2 (feedSlots 1 (cmpSlots 65)) := by
    rw [hA4]
    exact (install_other (pairT tailFlag tailSpare) A3 _ _ (hpairNe 1 (cmpSlots 65))).trans
      (houtA2 _ (hd21 (cmpSlots 65) (cmp_ge 65)))
  have hA4f3 : A4 (feedSlots 2 (cmpSlots 65)) = A3 (feedSlots 2 (cmpSlots 65)) := by
    rw [hA4]
    exact install_other (pairT tailFlag tailSpare) A3 _ _ (hpairNe 2 (cmpSlots 65))
  have hH3f1 : H3 (feedSlots 0 (cmpSlots 65)) = 0 :=
    (houtH2 _ (hd20 (cmpSlots 65) (cmp_ge 65))).trans
      ((houtH1 _ (hd10 (cmpSlots 65) (cmp_ge 65))).trans hh0)
  have hH3f2 : H3 (feedSlots 1 (cmpSlots 65)) = 0 :=
    (houtH2 _ (hd21 (cmpSlots 65) (cmp_ge 65))).trans hh1
  have hA4flag : A4 tailFlag = [false] := by
    rw [hA4]
    exact install_slot (pairT tailFlag tailSpare) (pairT_injective _ _ flag_ne_spare) A3
      (![[false], List.replicate 1 false] : Fin 2 → List Bool) 0
  -- the AND
  obtain ⟨tout, hand, handIff, handFrame⟩ :=
    and3_step_frame (feedSlots 0 (cmpSlots 65)) (feedSlots 1 (cmpSlots 65))
      (feedSlots 2 (cmpSlots 65)) tailFlag H3 A4 hH3f1 hH3f2 hh2 hflagH hA4flag
  have e1 : readTapeBit (A4 (feedSlots 0 (cmpSlots 65))) 0 = true ↔
      estimate estP.positive estP.negative estP.denominator ≤ 2*zeta constants := by
    rw [hA4f1, hiff0]
    exact passes_false _ _ _ _
  have e2 : readTapeBit (A4 (feedSlots 1 (cmpSlots 65))) 0 = true ↔
      estimate estM.positive estM.negative estM.denominator ≤ 1+zeta constants := by
    rw [hA4f2, hiff1]
    exact passes_false _ _ _ _
  have e3 : readTapeBit (A4 (feedSlots 2 (cmpSlots 65))) 0 = true ↔
      midpoint constants ≤ estimate estC.positive estC.negative estC.denominator := by
    rw [hA4f3, hiff2]
    exact passes_true _ _ _ _
  refine ⟨_, _, _, H3, tout, ((((hstep0.seq hstep1).seq hstep2).seq hinit).seq hand), ?_, ?_⟩
  · exact handIff.trans (and_congr e1 (and_congr e2 e3))
  · intro i hi
    have hif : i ≠ tailFlag := by
      intro hc
      have h473 : i.val = 473 := congrArg Fin.val hc
      omega
    have his : i ≠ tailSpare := by
      intro hc
      have h474 : i.val = 474 := congrArg Fin.val hc
      omega
    calc tout i = A4 i := handFrame i hif
      _ = A3 i := by
            rw [hA4]
            exact install_other (pairT tailFlag tailSpare) A3 _ i
              (fun j => pairT_ne (Ne.symm hif) (Ne.symm his) j)
      _ = A2 i := hpreA2 i hi
      _ = A1 i := hpreA1 i hi
      _ = A i := hpreA0 i hi

end NearCubicWires.RepairSource.CloseoutFinal.C10TailVerdict
