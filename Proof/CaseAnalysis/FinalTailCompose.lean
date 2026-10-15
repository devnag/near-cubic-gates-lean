import Proof.CaseAnalysis.FinalWorkerDockSeam
import Proof.CaseAnalysis.FinalTailSlots
import Proof.CaseAnalysis.FinalTailVerdict
import Proof.CaseAnalysis.FinalTailFeed
import Proof.Foundations.OrdinaryRewind

namespace NearCubicWires.RepairSource.CloseoutFinal.C10TailCompose

open LocalBitMultitape ExtDecompositionBatch
open NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDock
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerChain
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.CloseoutFinal.C10LengthGate
open NearCubicWires.RepairSource.CloseoutFinal.C10CompareDockLit
open CloseoutRowsOriginalSchedule (Phase)

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## §1 A stage, with every head parked

`Rewind.machine p` logs one mark per transition of `p` on a fresh tape and then
consumes the marks, moving every head of `p` left once per mark.  Nothing here
is new: it is `Rewind.reset_run`, restated as a `Step`. -/

theorem step_reset {t s : ℕ} {p : Machine t s} {n : ℕ} {tin : Fin t → List Bool}
    {hout : Fin t → ℕ} {tout : Fin t → List Bool}
    (h : Step p n (fun _ => 0) tin hout tout) :
    ∃ counter : List Bool,
      Step (Rewind.machine p) (2*n+2) (fun _ => 0)
        (Fin.addCases tin (fun _ : Fin 1 => []))
        (fun _ => 0) (Fin.addCases tout (fun _ : Fin 1 => counter)) := by
  obtain ⟨r, hr, hh, ht, hs⟩ := h
  have hrun : run p n tin = some r := hr
  obtain ⟨r', hr', htapes, hheads, hsteps, _⟩ := Rewind.reset_run p n tin r hrun
  refine ⟨r'.final.tapes ((0 : Fin 1).natAdd t), ?_⟩
  have hfuel : 2*r.steps+2 ≤ 2*n+2 := by omega
  refine (Step.of_run (r := r') ?_ ?_ ?_).enlarge hfuel
  · exact hr'
  · funext i; exact hheads i
  · funext i
    refine Fin.addCases (m := t) (n := 1) (fun j => ?_) (fun j => ?_) i
    · rw [Fin.addCases_left]
      exact (htapes j).trans (congrFun ht j)
    · have hj : j = 0 := Fin.eq_zero j
      subst hj
      rw [Fin.addCases_right]

/-! ## §2 The gate's exit tapes, named -/

/-- The bank a gated worker hands its body: the verifier's framed input on tape
`0`, its framed witness on tape `1`, `[true]` on the gate's scratch slot, blank
everywhere else. -/
def entryOf {t : ℕ} (fl : Fin t) (input witness : List Bool) : Fin t → List Bool :=
  fun i => if i = fl then [true]
    else if i.val = 0 then frame input else if i.val = 1 then frame witness else []

theorem entry_eq {t s : ℕ} (p : Machine t s) (ht : 2 ≤ t) (res fl : Fin t)
    (h0 : fl.val ≠ 0) (h1 : fl.val ≠ 1) (input witness : List Bool) :
    exitTapes fl ((UAcceptanceCarrier.verifier p ht res).inputTapes input witness) 0 true
      = entryOf fl input witness := by
  have hblank : (UAcceptanceCarrier.verifier p ht res).inputTapes input witness fl = [] := by
    rw [UAcceptanceCarrier.inputTapes_eq]
    simp [h0, h1]
  funext i
  rw [exitTapes_blank fl _ true hblank i, UAcceptanceCarrier.inputTapes_eq]
  unfold entryOf
  by_cases hi : i = fl
  · simp [hi]
  · simp [hi]

theorem entryOf_flag {t : ℕ} (fl : Fin t) (input witness : List Bool) :
    entryOf fl input witness fl = [true] := by simp [entryOf]

theorem entryOf_zero {t : ℕ} (fl : Fin t) (input witness : List Bool) (s : Fin t)
    (hne : s ≠ fl) (h0 : s.val = 0) : entryOf fl input witness s = frame input := by
  simp [entryOf, hne, h0]

theorem entryOf_one {t : ℕ} (fl : Fin t) (input witness : List Bool) (s : Fin t)
    (hne : s ≠ fl) (h1 : s.val = 1) : entryOf fl input witness s = frame witness := by
  simp [entryOf, hne, h1]

theorem entryOf_blank {t : ℕ} (fl : Fin t) (input witness : List Bool) (s : Fin t)
    (hne : s ≠ fl) (h0 : s.val ≠ 0) (h1 : s.val ≠ 1) : entryOf fl input witness s = [] := by
  simp [entryOf, hne, h0, h1]

/-! ## §3 The body block's four named local slots

W1 freezes the dock's layout at `input = 0`, `port = 215`, `flag = 216`,
`result = 217`; S2's stage widens the bank to `218+e` with those ports at
`Fin.castAdd e`. -/

variable (e : ℕ)

def wport : Fin (218+e) := Fin.castAdd e port
def wflag : Fin (218+e) := Fin.castAdd e flag
def winput : Fin (218+e) := Fin.castAdd e inputTape
def wwit : Fin (218+e) := Fin.castAdd e ⟨1, by omega⟩

@[simp] theorem wport_val : (wport e).val = 215 := rfl
@[simp] theorem wflag_val : (wflag e).val = 216 := rfl
@[simp] theorem winput_val : (winput e).val = 0 := rfl
@[simp] theorem wwit_val : (wwit e).val = 1 := rfl

def BlockRuns {bs : ℕ} (body : Machine (218+e) bs) (F : ℕ)
    (input witness : List Bool) (rec : List Bool) : Prop :=
  ∃ (heads : Fin (218+e) → ℕ) (exit : Fin (218+e) → List Bool),
    Step body F (fun _ => 0) (entryOf (wflag e) input witness) heads exit ∧
    exit (wport e) = rec ∧
    exit (winput e) = frame input ∧ exit (wwit e) = frame witness

/-! ## §5 The composed bank

T2 froze its tail bank at `tailBank = 475`: identity on `0 … 220`, its three feed
copies at `221 … 472`, `tailFlag = 473`, `tailSpare = 474`.  The composition adds
its blocks ABOVE that, so every slot the tail names keeps its index.

| tapes | contents |
|---|---|
| `0`, `1` | the verifier's framed input and framed witness, SHARED by the three blocks |
| `218`, `219`, `220` | the three record slots (T2's `scratchT`) |
| `221 … 474` | T2's feed copies, `tailFlag = 473`, `tailSpare = 474` — never touched here |
| `475 + k*(218+e) + j` | block `k`'s local tape `j` (`k = 0,1,2`; `j ∉ {0,1,215}`) |
| `L`, `L+1` (`L := 475+3*(218+e)`) | the two literal scratch tapes |
| `L+2`, `L+3`, `L+4` | the three rewind counters |
| `L+5` | reserved for the tail's own rewind counter |
-/

/-- The composed bank. -/
def bigOf : ℕ := 475 + 3*(218+e) + 6

def scrVal : Phase → ℕ
  | .penalty => 218
  | .moment => 219
  | .clause => 220

def baseOf : Phase → ℕ
  | .penalty => 475
  | .moment => 475 + (218+e)
  | .clause => 475 + 2*(218+e)

def litVal : Phase → ℕ
  | .penalty => 475 + 3*(218+e)
  | .moment => 475 + 3*(218+e)
  | .clause => 475 + 3*(218+e) + 1

def cntVal : Phase → ℕ
  | .penalty => 475 + 3*(218+e) + 2
  | .moment => 475 + 3*(218+e) + 3
  | .clause => 475 + 3*(218+e) + 4

theorem scrVal_le (ph : Phase) : 218 ≤ scrVal ph ∧ scrVal ph ≤ 220 := by
  cases ph <;> simp only [scrVal] <;> omega
theorem baseOf_le (ph : Phase) : 475 ≤ baseOf e ph ∧ baseOf e ph ≤ 475 + 2*(218+e) := by
  cases ph <;> simp only [baseOf] <;> omega
theorem litVal_le (ph : Phase) :
    475 + 3*(218+e) ≤ litVal e ph ∧ litVal e ph ≤ 475 + 3*(218+e) + 1 := by
  cases ph <;> simp only [litVal] <;> omega
theorem cntVal_le (ph : Phase) :
    475 + 3*(218+e) + 2 ≤ cntVal e ph ∧ cntVal e ph ≤ 475 + 3*(218+e) + 4 := by
  cases ph <;> simp only [cntVal] <;> omega

def scr (ph : Phase) : Fin (bigOf e) :=
  ⟨scrVal ph, by have := scrVal_le ph; show scrVal ph < 475 + 3*(218+e) + 6; omega⟩
def cnt (ph : Phase) : Fin (bigOf e) :=
  ⟨cntVal e ph, by have := cntVal_le e ph; show cntVal e ph < 475 + 3*(218+e) + 6; omega⟩
def litOf (ph : Phase) : Fin (bigOf e) :=
  ⟨litVal e ph, by have := litVal_le e ph; show litVal e ph < 475 + 3*(218+e) + 6; omega⟩

@[simp] theorem scr_val (ph : Phase) : (scr e ph).val = scrVal ph := rfl
@[simp] theorem cnt_val (ph : Phase) : (cnt e ph).val = cntVal e ph := rfl
@[simp] theorem litOf_val (ph : Phase) : (litOf e ph).val = litVal e ph := rfl

/-- **The phase's block.**  Tapes `0` and `1` are shared; local `215` (the
emitter's output port) lands on the phase's record slot; everything else is
private to the phase. -/
def bslot (ph : Phase) (j : Fin (218+e)) : Fin (bigOf e) :=
  if j.val ≤ 1 then ⟨j.val, by
      have := j.isLt; show j.val < 475 + 3*(218+e) + 6; omega⟩
  else if j.val = 215 then scr e ph
  else ⟨baseOf e ph + j.val, by
      have := j.isLt; have := baseOf_le e ph
      show baseOf e ph + j.val < 475 + 3*(218+e) + 6; omega⟩

theorem bslot_val (ph : Phase) (j : Fin (218+e)) :
    (bslot e ph j).val =
      if j.val ≤ 1 then j.val
      else if j.val = 215 then scrVal ph else baseOf e ph + j.val := by
  unfold bslot
  split_ifs <;> rfl

/-- The block, extended by the phase's rewind counter: the slot map of the whole
`Rewind.machine`-wrapped body. -/
def rslot (ph : Phase) (j : Fin (218+e+1)) : Fin (bigOf e) :=
  if h : j.val < 218+e then bslot e ph ⟨j.val, h⟩ else cnt e ph

theorem rslot_val (ph : Phase) (j : Fin (218+e+1)) :
    (rslot e ph j).val =
      if j.val < 218+e then
        (if j.val ≤ 1 then j.val
          else if j.val = 215 then scrVal ph else baseOf e ph + j.val)
      else cntVal e ph := by
  unfold rslot
  by_cases h : j.val < 218+e
  · rw [dif_pos h, if_pos h, bslot_val]
  · rw [dif_neg h, if_neg h]
    rfl

theorem rslot_castAdd (ph : Phase) (i : Fin (218+e)) :
    rslot e ph (i.castAdd 1) = bslot e ph i := by
  have h : ((i.castAdd 1 : Fin (218+e+1))).val < 218+e := i.isLt
  simp only [rslot, dif_pos h]
  exact congrArg (bslot e ph) (Fin.ext rfl)

theorem rslot_last (ph : Phase) : rslot e ph ((0 : Fin 1).natAdd (218+e)) = cnt e ph := by
  have h : ¬ (((0 : Fin 1).natAdd (218+e) : Fin (218+e+1))).val < 218+e := by simp
  simp only [rslot, dif_neg h]

theorem rslot_injective (ph : Phase) : Function.Injective (rslot e ph) := by
  intro i j h
  have hv := congrArg Fin.val h
  rw [rslot_val, rslot_val] at hv
  have hi := i.isLt
  have hj := j.isLt
  refine Fin.ext ?_
  cases ph <;>
    · simp only [scrVal, baseOf, cntVal] at hv
      split_ifs at hv <;> omega

/-- Nothing the composition touches lies in `221 … 474` — T2's own region. -/
theorem rslot_out (ph : Phase) (j : Fin (218+e+1)) (s : Fin (bigOf e))
    (h1 : 221 ≤ s.val) (h2 : s.val < 475) : rslot e ph j ≠ s := by
  intro h
  have hv := congrArg Fin.val h
  rw [rslot_val] at hv
  have hj := j.isLt
  cases ph <;>
    · simp only [scrVal, baseOf, cntVal] at hv
      split_ifs at hv <;> omega

theorem litOf_out (ph : Phase) (s : Fin (bigOf e)) (h1 : 221 ≤ s.val) (h2 : s.val < 475) :
    litOf e ph ≠ s := by
  intro h
  have hv := congrArg Fin.val h
  have hb := litVal_le e ph
  simp only [litOf_val] at hv
  omega

/-- Slots of DIFFERENT phases meet only on the shared tapes `0` and `1`. -/
theorem rslot_cross (ph ph' : Phase) (hne : ph ≠ ph') (j : Fin (218+e+1)) (i : Fin (218+e))
    (h : rslot e ph' j = bslot e ph i) : i.val ≤ 1 := by
  have hv := congrArg Fin.val h
  rw [rslot_val, bslot_val] at hv
  have hi := i.isLt
  have hj := j.isLt
  cases ph <;> cases ph' <;> simp only [scrVal, baseOf, cntVal] at hv <;>
    split_ifs at hv <;> first | omega | exact absurd rfl hne

theorem rslot_le (ph : Phase) (j : Fin (218+e+1)) :
    (rslot e ph j).val ≤ 475 + 3*(218+e) + 4 := by
  rw [rslot_val]
  have := j.isLt
  cases ph <;>
    · simp only [scrVal, baseOf, cntVal]
      split_ifs <;> omega

/-- The tape reserved for the TAIL's own rewind counter. -/
def tailCnt : Fin (bigOf e) := ⟨475 + 3*(218+e) + 5, by
  show 475 + 3*(218+e) + 5 < 475 + 3*(218+e) + 6; omega⟩

@[simp] theorem tailCnt_val : (tailCnt e).val = 475 + 3*(218+e) + 5 := rfl

theorem rslot_ne_tailCnt (ph : Phase) (j : Fin (218+e+1)) : rslot e ph j ≠ tailCnt e := by
  have := rslot_le e ph j
  exact Fin.ne_of_val_ne (by rw [tailCnt_val]; omega)

/-! ### The gate's three slots -/

/-- The gate's input slot. -/
def gInput : Fin (bigOf e) := ⟨0, by show (0:ℕ) < 475 + 3*(218+e) + 6; omega⟩
/-- Bank tape `1`, the framed witness. -/
def gWit : Fin (bigOf e) := ⟨1, by show (1:ℕ) < 475 + 3*(218+e) + 6; omega⟩
/-- The gate's scratch slot: the penalty block's own `flag`. -/
def gFlag : Fin (bigOf e) := bslot e .penalty (wflag e)
/-- The gate's verdict slot: T2's `tailFlag`, at the same index. -/
def gResult : Fin (bigOf e) := ⟨473, by show (473:ℕ) < 475 + 3*(218+e) + 6; omega⟩

@[simp] theorem gInput_val : (gInput e).val = 0 := rfl
@[simp] theorem gWit_val : (gWit e).val = 1 := rfl
@[simp] theorem gResult_val : (gResult e).val = 473 := rfl

theorem bslot_flag_val (ph : Phase) : (bslot e ph (wflag e)).val = baseOf e ph + 216 := by
  rw [bslot_val, wflag_val]
  norm_num

@[simp] theorem gFlag_val : (gFlag e).val = 691 := by
  rw [gFlag, bslot_flag_val]
  simp [baseOf]

theorem bslot_port (ph : Phase) : bslot e ph (wport e) = scr e ph := by
  unfold bslot
  rw [if_neg (by rw [wport_val]; omega), if_pos (by rw [wport_val])]

theorem bslot_input (ph : Phase) : bslot e ph (winput e) = gInput e := by
  unfold bslot
  rw [if_pos (by rw [winput_val]; omega)]
  rfl

theorem bslot_wit (ph : Phase) : bslot e ph (wwit e) = gWit e := by
  unfold bslot
  rw [if_pos (by rw [wwit_val])]
  rfl

/-! ### A block is parked, read off the ambient bank -/

theorem blk_of (ph : Phase) (input witness : List Bool) (A : Fin (bigOf e) → List Bool)
    (hflag : A (bslot e ph (wflag e)) = [true])
    (hzero : A (gInput e) = frame input) (hone : A (gWit e) = frame witness)
    (hblank : ∀ i : Fin (218+e), i.val ≠ 0 → i.val ≠ 1 → i.val ≠ 216 →
      A (bslot e ph i) = []) :
    ∀ i : Fin (218+e), A (bslot e ph i) = entryOf (wflag e) input witness i := by
  intro i
  by_cases h216 : i.val = 216
  · have hi : i = wflag e := Fin.ext (by rw [h216, wflag_val])
    subst hi
    rw [hflag, entryOf_flag]
  · by_cases h0 : i.val = 0
    · have hi : i = winput e := Fin.ext (by rw [h0, winput_val])
      subst hi
      rw [bslot_input, hzero,
        entryOf_zero (wflag e) input witness (winput e)
          (Fin.ne_of_val_ne (by simp)) (winput_val e)]
    · by_cases h1 : i.val = 1
      · have hi : i = wwit e := Fin.ext (by rw [h1, wwit_val])
        subst hi
        rw [bslot_wit, hone,
          entryOf_one (wflag e) input witness (wwit e)
            (Fin.ne_of_val_ne (by simp)) (wwit_val e)]
      · rw [hblank i h0 h1 h216,
          entryOf_blank (wflag e) input witness i
            (Fin.ne_of_val_ne (by rw [wflag_val]; exact h216)) h0 h1]

/-! ## §6 One phase's body, docked and head-parked -/

noncomputable def rbody {bs : ℕ} (ph : Phase) (body : Machine (218+e) bs) :=
  RecoveryFocus.machine (rslot e ph) (Rewind.machine body)

/-- **One phase, docked.**  From a bank whose block `ph` is parked as the body's
run premise demands, the phase's record lands on `scr ph`, the verifier's input
and witness tapes come back unchanged, every head is back at `0`, and no slot
outside the block is touched. -/
theorem body_dock {bs : ℕ} (ph : Phase) (body : Machine (218+e) bs) (F : ℕ)
    (input witness : List Bool) (rec : List Bool)
    (h : BlockRuns e body F input witness rec)
    (A : Fin (bigOf e) → List Bool)
    (hblk : ∀ i : Fin (218+e), A (bslot e ph i) = entryOf (wflag e) input witness i)
    (hcnt : A (cnt e ph) = []) :
    ∃ A' : Fin (bigOf e) → List Bool,
      Step (rbody e ph body) (2*F+2) (fun _ => 0) A (fun _ => 0) A' ∧
      A' (scr e ph) = rec ∧
      A' (gInput e) = frame input ∧ A' (gWit e) = frame witness ∧
      (∀ s : Fin (bigOf e), (∀ j, rslot e ph j ≠ s) → A' s = A s) := by
  obtain ⟨heads, exit, hstep, hrec, hin, hwit⟩ := h
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
    (Fin.addCases (motive := fun _ => List Bool) exit (fun _ : Fin 1 => c)), hdock, ?_, ?_, ?_, ?_⟩
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

/-! ## §7 The two literal flag writes -/

def pair2 (a b : Fin (bigOf e)) (i : Fin 2) : Fin (bigOf e) := if i.val = 0 then a else b

theorem pair2_zero (a b : Fin (bigOf e)) : pair2 e a b 0 = a := rfl
theorem pair2_one (a b : Fin (bigOf e)) : pair2 e a b 1 = b := rfl

theorem pair2_injective (a b : Fin (bigOf e)) (hne : a ≠ b) :
    Function.Injective (pair2 e a b) := by
  intro i j h
  fin_cases i <;> fin_cases j
  · rfl
  · exact absurd (show a = b by simpa [pair2] using h) hne
  · exact absurd (show a = b by simpa [pair2] using h.symm) hne
  · rfl

theorem pair2_ne (a b s : Fin (bigOf e)) (ha : a ≠ s) (hb : b ≠ s) (j : Fin 2) :
    pair2 e a b j ≠ s := by
  fin_cases j
  · simpa [pair2] using ha
  · simpa [pair2] using hb

/-- P4's gate writes `[true]` once, at the penalty block's own `flag`; the other
two blocks get theirs from `HierarchyFixedWord`, which needs one blank second
tape apiece. -/
noncomputable def litStage (a b : Fin (bigOf e)) :=
  RecoveryFocus.machine (pair2 e a b) (HierarchyFixedWord.machine [true])

theorem lit_dock (a b : Fin (bigOf e)) (hne : a ≠ b) (A : Fin (bigOf e) → List Bool)
    (ha : A a = []) (hb : A b = []) :
    Step (litStage e a b) 4 (fun _ => 0) A (fun _ => 0)
      (install (pair2 e a b) A ![[true], [false]]) := by
  have h := (word_step [true]).dock (pair2 e a b) (pair2_injective e a b hne) (fun _ => 0) A
    (fun _ => rfl) (by intro j; fin_cases j <;> simp [pair2, ha, hb])
  rw [dockH_existing (pair2 e a b) (fun _ => 0) (fun _ => 0) (fun _ => rfl)] at h
  have hfuel : 2*([true] : List Bool).length+2 = 4 := by norm_num
  have hrep : (![([true] : List Bool), List.replicate ([true] : List Bool).length false]
      : Fin 2 → List Bool) = ![[true], [false]] := by
    funext i; fin_cases i <;> rfl
  rw [hfuel, hrep] at h
  exact h

/-! ## §8 The four literal slots, by index -/

theorem momentFlag_val : (bslot e .moment (wflag e)).val = 909 + e := by
  rw [bslot_flag_val]; simp only [baseOf]; omega
theorem clauseFlag_val : (bslot e .clause (wflag e)).val = 1127 + 2*e := by
  rw [bslot_flag_val]; simp only [baseOf]; omega
theorem momentLit_val : (litOf e .moment).val = 1129 + 3*e := by
  simp only [litOf_val, litVal]; omega
theorem clauseLit_val : (litOf e .clause).val = 1130 + 3*e := by
  simp only [litOf_val, litVal]; omega
theorem cntVal_gt (ph : Phase) : 1131 + 3*e ≤ (cnt e ph).val := by
  simp only [cnt_val]; cases ph <;> simp only [cntVal] <;> omega

/-- Every non-shared, non-flag slot of every block avoids the four literal slots
and the three shared tapes. -/
theorem block_slot_free (ph : Phase) (i : Fin (218+e))
    (h0 : i.val ≠ 0) (h1 : i.val ≠ 1) (h216 : i.val ≠ 216) :
    (bslot e ph i).val ≠ 0 ∧ (bslot e ph i).val ≠ 1 ∧ (bslot e ph i).val ≠ 691 ∧
      (bslot e ph i).val ≠ 909 + e ∧ (bslot e ph i).val ≠ 1127 + 2*e ∧
      (bslot e ph i).val ≠ 1129 + 3*e ∧ (bslot e ph i).val ≠ 1130 + 3*e := by
  have hlt := i.isLt
  rw [bslot_val]
  cases ph <;>
    · simp only [scrVal, baseOf]
      split_ifs <;> refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-! ## §9 The three phase bodies, composed inside one bank -/

/-- **The composed body.**  Two literal flag writes, then the three phase
bodies, each head-parked by `Rewind`.  ONE machine, fixed once the three block
bodies are: nothing in it depends on the input, the witness or the length. -/
noncomputable def bodyThree {bs : Phase → ℕ} (body : (ph : Phase) → Machine (218+e) (bs ph)) :=
  Composition.machine
    (Composition.machine
      (Composition.machine (litStage e (bslot e .moment (wflag e)) (litOf e .moment))
        (litStage e (bslot e .clause (wflag e)) (litOf e .clause)))
      (Composition.machine (rbody e .penalty (body .penalty)) (rbody e .moment (body .moment))))
    (rbody e .clause (body .clause))

/-- The composed budget: two four-step literal writes, three DOUBLED block
budgets (the `Rewind` head-reset factor), and the four paid bridge steps of
`Composition.machine`.  Every summand is `len`-determined exactly when the block
budgets are. -/
def bodyThreeFuel (F : Phase → ℕ) : ℕ :=
  ((4+1+4) + 1 + ((2*F .penalty+2) + 1 + (2*F .moment+2))) + 1 + (2*F .clause+2)

/-- **T3(i): the three phase bodies, at ONE run, on ONE bank.**  From the gate's
exit tapes, the composed body leaves the three phase records on T2's three
`scratchT` slots `218/219/220`, every head back at `0`, and T2's whole region
`221 … 474` untouched — which is exactly the parked bank `tail_step` consumes. -/
theorem bodyThree_step {bs : Phase → ℕ} (body : (ph : Phase) → Machine (218+e) (bs ph))
    (F : Phase → ℕ) (input witness : List Bool) (rec : Phase → List Bool)
    (hbody : ∀ ph, BlockRuns e (body ph) (F ph) input witness (rec ph)) :
    ∃ A : Fin (bigOf e) → List Bool,
      Step (bodyThree e body) (bodyThreeFuel F) (fun _ => 0)
        (entryOf (gFlag e) input witness) (fun _ => 0) A ∧
      (∀ ph, A (scr e ph) = rec ph) ∧
      (∀ s : Fin (bigOf e), 221 ≤ s.val → s.val < 475 → A s = []) ∧
      A (tailCnt e) = [] := by
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
  obtain ⟨A3, hB0, hrec0, hin3, hwit3, hoth0⟩ :=
    body_dock e .penalty (body .penalty) (F .penalty) input witness (rec .penalty)
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
  obtain ⟨A4, hB1, hrec1, hin4, hwit4, hoth1⟩ :=
    body_dock e .moment (body .moment) (F .moment) input witness (rec .moment)
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
  obtain ⟨A5, hB2, hrec2, _hin5, _hwit5, hoth2⟩ :=
    body_dock e .clause (body .clause) (F .clause) input witness (rec .clause)
      (hbody .clause) A4 hblk2 hcnt4
  -- §9.6 the conclusion
  have hkeep : ∀ (ph ph' : Phase), ph ≠ ph' → ∀ j, rslot e ph' j ≠ scr e ph := by
    intro ph ph' hne j
    rw [← bslot_port e ph]
    exact hcross ph ph' hne (wport e) (by simp) j
  refine ⟨A5, ((hL1.seq hL2).seq (hB0.seq hB1)).seq hB2, ?_, ?_, ?_⟩
  · intro ph
    cases ph
    · rw [hoth2 _ (hkeep .penalty .clause (fun hc => Phase.noConfusion hc)),
        hoth1 _ (hkeep .penalty .moment (fun hc => Phase.noConfusion hc))]
      exact hrec0
    · rw [hoth2 _ (hkeep .moment .clause (fun hc => Phase.noConfusion hc))]
      exact hrec1
    · exact hrec2
  · intro s h1 h2
    rw [hoth2 _ (fun j => rslot_out e _ j s h1 h2), hoth1 _ (fun j => rslot_out e _ j s h1 h2),
      hoth0 _ (fun j => rslot_out e _ j s h1 h2),
      hA2base s (by omega) (by omega) (by omega) (by omega)]
    exact hA0blank s (by omega) (by omega) (by omega)
  · rw [hoth2 _ (rslot_ne_tailCnt e .clause), hoth1 _ (rslot_ne_tailCnt e .moment),
      hoth0 _ (rslot_ne_tailCnt e .penalty),
      hA2base _ (by rw [tailCnt_val]; omega) (by rw [tailCnt_val]; omega)
        (by rw [tailCnt_val]; omega) (by rw [tailCnt_val]; omega)]
    exact hA0blank _ (by rw [tailCnt_val]; omega) (by rw [tailCnt_val]; omega)
      (by rw [tailCnt_val]; omega)

/-! ## §10 Inside P4's gate

W1's `worker onset input flag result body` IS `C10LengthGate.gated`, and
`gated_verifier_pass` hands the body the verifier's own tapes with every head at
`0` and the single scratch slot `flag` carrying `[true]` — which is precisely
`entryOf (gFlag e)`.  So the composed body plugs into the gate with no glue. -/

theorem bigTwo : 2 ≤ bigOf e := by show 2 ≤ 475 + 3*(218+e) + 6; omega

theorem gFlag_ne_gInput : gFlag e ≠ gInput e := Fin.ne_of_val_ne (by simp)

/-- **The gate seam, once and for all.**  Any inner machine that runs from
`entryOf (gFlag e)` and parks its heads becomes a run of the gated worker at the
verifier's own input tapes, at a budget that mentions only `len`. -/
theorem gate_of_inner {S : ℕ} (P : Machine (bigOf e) S) (fuel onset len : ℕ)
    (x : BitInput len) (bits : List Bool) (honset : onset ≤ len)
    (A : Fin (bigOf e) → List Bool)
    (hinner : Step P fuel (fun _ => 0) (entryOf (gFlag e) (List.ofFn x) bits) (fun _ => 0) A) :
    Step (worker onset (gInput e) (gFlag e) (gResult e) P)
      (workerBudget onset (fun _ => fuel) len) (fun _ => 0)
      ((UAcceptanceCarrier.verifier (worker onset (gInput e) (gFlag e) (gResult e) P)
          (bigTwo e) (gResult e)).inputTapes (List.ofFn x) bits) (fun _ => 0) A := by
  have hentry := entry_eq (worker onset (gInput e) (gFlag e) (gResult e) P) (bigTwo e)
    (gResult e) (gFlag e) (by simp) (by simp) (List.ofFn x) bits
  rw [← hentry] at hinner
  exact gated_verifier_pass onset (gInput e) (gFlag e) (gResult e) P
    (bigTwo e) (by simp) len x bits honset fuel (fun _ => 0) A hinner

/-- **T3(i), gated.**  ABOVE the cutoff: one `Step` of the whole gated machine,
from the verifier's own input tapes, leaving the three phase records on T2's
`scratchT` slots with every head at `0` and T2's region `221 … 474` untouched. -/
theorem gatedThree_step {bs : Phase → ℕ} (body : (ph : Phase) → Machine (218+e) (bs ph))
    (F : Phase → ℕ) (onset len : ℕ) (x : BitInput len) (bits : List Bool)
    (rec : Phase → List Bool) (honset : onset ≤ len)
    (hbody : ∀ ph, BlockRuns e (body ph) (F ph) (List.ofFn x) bits (rec ph)) :
    ∃ A : Fin (bigOf e) → List Bool,
      Step (worker onset (gInput e) (gFlag e) (gResult e) (bodyThree e body))
        (workerBudget onset (fun _ => bodyThreeFuel F) len) (fun _ => 0)
        ((UAcceptanceCarrier.verifier
            (worker onset (gInput e) (gFlag e) (gResult e) (bodyThree e body))
            (bigTwo e) (gResult e)).inputTapes (List.ofFn x) bits)
        (fun _ => 0) A ∧
      (∀ ph, A (scr e ph) = rec ph) ∧
      (∀ s : Fin (bigOf e), 221 ≤ s.val → s.val < 475 → A s = []) := by
  obtain ⟨A, hstep, hrec, hblank, _⟩ := bodyThree_step e body F (List.ofFn x) bits rec hbody
  exact ⟨A, gate_of_inner e (bodyThree e body) (bodyThreeFuel F) onset len x bits honset A hstep,
    hrec, hblank⟩

/-- **`Verdict.gate` for the composed machine.**  P4's realizer, instantiated at
the composed worker: the onset is spent as finite control, so the machine
rejects every length below `Soundness.cutoff constants`. -/
theorem gate_of_compose {source : RepairRepresentation.PointwisePCPPAlgorithm}
    (constants : RepairSource.CompetitorRationalGap.Constants source)
    {S : ℕ} (P : Machine (bigOf e) S) (budget : ℕ → ℕ) :
    LengthGate constants
      (worker (CloseoutWitness.Soundness.cutoff constants) (gInput e) (gFlag e) (gResult e) P)
      (bigTwo e) (gResult e) budget :=
  lengthGate_of_stateCounter constants (gInput e) (gFlag e) (gResult e) P
    (bigTwo e) (by simp) (gFlag_ne_gInput e) budget

/-- **BELOW the cutoff: the gate's own run.**  `Verdict.run` is unconditional,
so the composed machine must halt at every length; below the cutoff it halts on
the gate's reject path, in `2*len+3` steps, with the verdict slot reading
`false`.  This is `accepts_iff`'s reject direction, physically. -/
theorem gated_below {bsq : ℕ} (C : ℕ) (q : Machine (bigOf e) bsq)
    (len : ℕ) (x : BitInput len) (bits : List Bool) (hlt : len < C) :
    ∃ (H : Fin (bigOf e) → ℕ) (A : Fin (bigOf e) → List Bool),
      Step (worker C (gInput e) (gFlag e) (gResult e) q) (2*len+3) (fun _ => 0)
        ((UAcceptanceCarrier.verifier (worker C (gInput e) (gFlag e) (gResult e) q)
            (bigTwo e) (gResult e)).inputTapes (List.ofFn x) bits) H A ∧
      readTapeBit (A (gResult e)) (H (gResult e)) = false := by
  have hT0 : (UAcceptanceCarrier.verifier (worker C (gInput e) (gFlag e) (gResult e) q)
      (bigTwo e) (gResult e)).inputTapes (List.ofFn x) bits (gInput e)
      = frame (List.ofFn x) := by
    rw [UAcceptanceCarrier.inputTapes_eq]
    simp
  have hread : ∀ j, j < 2*len → j % 2 = 0 →
      readTapeBit ((UAcceptanceCarrier.verifier
        (worker C (gInput e) (gFlag e) (gResult e) q) (bigTwo e) (gResult e)).inputTapes
        (List.ofFn x) bits (gInput e)) ((fun _ : Fin (bigOf e) => 0) (gInput e) + j) = true := by
    intro j hj he
    rw [hT0]
    simpa using frame_short (List.ofFn x) j (by simpa using hj) he
  have hstop : readTapeBit ((UAcceptanceCarrier.verifier
      (worker C (gInput e) (gFlag e) (gResult e) q) (bigTwo e) (gResult e)).inputTapes
      (List.ofFn x) bits (gInput e))
      ((fun _ : Fin (bigOf e) => 0) (gInput e) + 2*len) = false := by
    rw [hT0]
    simpa using frame_stop (List.ofFn x)
  obtain ⟨u, hu, hfalse⟩ := gated_reject C (gInput e) (gFlag e) (gResult e) q
    (gFlag_ne_gInput e) (fun _ => 0) _ len (by omega) hread hstop
  refine ⟨u.final.heads, u.final.tapes, ?_, hfalse⟩
  have hfuel : (2*len+1)+1+1 = 2*len+3 := by omega
  rw [hfuel] at hu
  exact Step.of_run hu rfl rfl

/-! ## §11 T2's decision tail, docked

T2's bank (`tailBank = 475`) is the identity on `0 … 220` and never touches
`i.val < 221`, so it embeds into the composed bank index for index; only its own
rewind counter needs a fresh tape, and that is `tailCnt`. -/

/-- T2's bank sits at the bottom of the composed bank, index for index. -/
def tslot (i : Fin C10TailVerdict.tailBank) : Fin (bigOf e) :=
  ⟨i.val, by
    have hi : i.val < 475 := i.isLt
    show i.val < 475 + 3*(218+e) + 6
    omega⟩

@[simp] theorem tslot_val (i : Fin C10TailVerdict.tailBank) : (tslot e i).val = i.val := rfl

/-- The tail's slot map, extended by its own rewind counter. -/
def rtslot (i : Fin (C10TailVerdict.tailBank + 1)) : Fin (bigOf e) :=
  if h : i.val < C10TailVerdict.tailBank then tslot e ⟨i.val, h⟩ else tailCnt e

theorem rtslot_val (i : Fin (C10TailVerdict.tailBank + 1)) :
    (rtslot e i).val =
      if i.val < C10TailVerdict.tailBank then i.val else 475 + 3*(218+e) + 5 := by
  unfold rtslot
  by_cases h : i.val < C10TailVerdict.tailBank
  · rw [dif_pos h, if_pos h]; rfl
  · rw [dif_neg h, if_neg h]; rfl

theorem rtslot_castAdd (i : Fin C10TailVerdict.tailBank) :
    rtslot e (i.castAdd 1) = tslot e i := by
  have h : ((i.castAdd 1 : Fin (C10TailVerdict.tailBank+1))).val
      < C10TailVerdict.tailBank := i.isLt
  simp only [rtslot, dif_pos h]
  exact congrArg (tslot e) (Fin.ext rfl)

theorem rtslot_last :
    rtslot e ((0 : Fin 1).natAdd C10TailVerdict.tailBank) = tailCnt e := by
  have h : ¬ (((0 : Fin 1).natAdd C10TailVerdict.tailBank :
      Fin (C10TailVerdict.tailBank+1))).val < C10TailVerdict.tailBank := by simp
  simp only [rtslot, dif_neg h]

theorem rtslot_injective : Function.Injective (rtslot e) := by
  intro i j h
  have hv := congrArg Fin.val h
  rw [rtslot_val, rtslot_val] at hv
  have hi : i.val < 476 := i.isLt
  have hj : j.val < 476 := j.isLt
  refine Fin.ext ?_
  by_cases ha : i.val < C10TailVerdict.tailBank <;>
    by_cases hb : j.val < C10TailVerdict.tailBank
  · rw [if_pos ha, if_pos hb] at hv
    exact hv
  · rw [if_pos ha, if_neg hb] at hv
    have ha' : i.val < 475 := ha
    omega
  · rw [if_neg ha, if_pos hb] at hv
    have hb' : j.val < 475 := hb
    omega
  · have ha' : ¬ (i.val < 475) := ha
    have hb' : ¬ (j.val < 475) := hb
    omega

theorem tslot_scratch (ph : Phase) : tslot e (C10TailVerdict.scratchT ph) = scr e ph :=
  Fin.ext (by cases ph <;> rfl)

theorem tslot_flag : tslot e C10TailVerdict.tailFlag = gResult e := Fin.ext rfl

theorem feedSlots_ge (k : Fin 3) (i : Fin C10TailSlots.bank) (hi : 221 ≤ i.val) :
    221 ≤ (C10TailVerdict.feedSlots k i).val := by
  show 221 ≤ C10TailVerdict.feedIdx k i
  unfold C10TailVerdict.feedIdx
  split <;> omega

/-- **The parked bank `tail_step` consumes**, read straight off `bodyThree_step`. -/
theorem parkedThree_of {W : ℕ} (est : Phase → CompetitorValidity.Estimate)
    (A : Fin (bigOf e) → List Bool)
    (hrec : ∀ ph, A (scr e ph) =
      CloseoutRowsEstimatorCoefficients.Stream.recordWord (C10TailFeedPrep.w W) (est ph) 1 1)
    (hblank : ∀ s : Fin (bigOf e), 221 ≤ s.val → s.val < 475 → A s = []) :
    C10TailVerdict.ParkedThree W (est .penalty) (est .moment) (est .clause)
      (fun _ => 0) (fun i => A (tslot e i)) := by
  have hb : ∀ (i : Fin C10TailVerdict.tailBank), 221 ≤ i.val → A (tslot e i) = [] := by
    intro i hi
    exact hblank _ (by rw [tslot_val]; exact hi) (by rw [tslot_val]; exact i.isLt)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [tslot_scratch]; exact hrec .penalty
  · rw [tslot_scratch]; exact hrec .moment
  · rw [tslot_scratch]; exact hrec .clause
  · intro _; rfl
  · intro k j
    exact hb _ (feedSlots_ge k _ (C10TailVerdict.cmp_ge j))
  · intro _ _; rfl
  · intro k j
    exact hb _ (feedSlots_ge k _ (C10TailVerdict.normA_ge j))
  · intro _ _; rfl
  · intro k j
    exact hb _ (feedSlots_ge k _ (C10TailVerdict.normB_ge j))
  · intro _ _; rfl
  · intro k j
    exact hb _ (feedSlots_ge k _ (C10TailVerdict.word_ge j))
  · intro _ _; rfl
  · exact hb _ (by show (221:ℕ) ≤ 473; omega)
  · rfl
  · exact hb _ (by show (221:ℕ) ≤ 474; omega)
  · rfl

/-- **The tail, docked and head-parked.** -/
theorem tail_dock {states : ℕ} (m : Machine C10TailVerdict.tailBank states) (budget : ℕ)
    (H' : Fin C10TailVerdict.tailBank → ℕ) (A' : Fin C10TailVerdict.tailBank → List Bool)
    (A : Fin (bigOf e) → List Bool)
    (hstep : Step m budget (fun _ => 0) (fun i => A (tslot e i)) H' A')
    (hcnt : A (tailCnt e) = []) :
    ∃ A'' : Fin (bigOf e) → List Bool,
      Step (RecoveryFocus.machine (rtslot e) (Rewind.machine m)) (2*budget+2)
        (fun _ => 0) A (fun _ => 0) A'' ∧
      (∀ i, A'' (tslot e i) = A' i) := by
  obtain ⟨c, hr⟩ := step_reset hstep
  have hA : ∀ j, A (rtslot e j)
      = Fin.addCases (motive := fun _ => List Bool) (fun i => A (tslot e i))
        (fun _ : Fin 1 => ([] : List Bool)) j := by
    intro j
    refine Fin.addCases (m := C10TailVerdict.tailBank) (n := 1) (fun i => ?_) (fun i => ?_) j
    · rw [rtslot_castAdd, Fin.addCases_left]
    · have hi : i = 0 := Fin.eq_zero i
      subst hi
      rw [rtslot_last, Fin.addCases_right]
      exact hcnt
  have hdock := hr.dock (rtslot e) (rtslot_injective e) (fun _ => 0) A (fun _ => rfl) hA
  rw [dockH_existing (rtslot e) (fun _ => 0) (fun _ => 0) (fun _ => rfl)] at hdock
  refine ⟨install (rtslot e) A
    (Fin.addCases (motive := fun _ => List Bool) A' (fun _ : Fin 1 => c)), hdock, ?_⟩
  intro i
  rw [← rtslot_castAdd e i, install_slot (rtslot e) (rtslot_injective e) A _ (i.castAdd 1),
    Fin.addCases_left]

/-! ## §12 The whole C.10 machine, above the cutoff

Three phase bodies, T2's three-comparator decision tail, all inside P4's gate,
at ONE run: `Verdict.run` and `Verdict.accepts_iff` for the composed machine. -/

theorem verdict_run_of_records {bs : Phase → ℕ}
    (body : (ph : Phase) → Machine (218+e) (bs ph)) (F : Phase → ℕ)
    {source : RepairRepresentation.PointwisePCPPAlgorithm}
    (constants : RepairSource.CompetitorRationalGap.Constants source)
    (W : ℕ) (est : Phase → CompetitorValidity.Estimate)
    (hvP : (est .penalty).Valid W) (hvM : (est .moment).Valid W)
    (hvC : (est .clause).Valid W)
    (hwidth : CompetitorThresholdDecision.numerator
          (RepairSource.CompetitorRationalGap.meanThreshold constants) < 2^(C10TailFeedPrep.w W) ∧
      (RepairSource.CompetitorRationalGap.meanThreshold constants).den < 2^(C10TailFeedPrep.w W) ∧
      CompetitorThresholdDecision.numerator
          (RepairSource.CompetitorRationalGap.momentThreshold constants) < 2^(C10TailFeedPrep.w W) ∧
      (RepairSource.CompetitorRationalGap.momentThreshold constants).den
          < 2^(C10TailFeedPrep.w W) ∧
      CompetitorThresholdDecision.numerator
          (CompetitorThresholdDecision.acceptanceThreshold constants) < 2^(C10TailFeedPrep.w W) ∧
      (CompetitorThresholdDecision.acceptanceThreshold constants).den
          < 2^(C10TailFeedPrep.w W))
    (onset len : ℕ) (x : BitInput len) (bits : List Bool) (honset : onset ≤ len)
    (hbody : ∀ ph, BlockRuns e (body ph) (F ph) (List.ofFn x) bits
      (CloseoutRowsEstimatorCoefficients.Stream.recordWord (C10TailFeedPrep.w W) (est ph) 1 1)) :
    ∃ (S : ℕ) (P : Machine (bigOf e) S) (bud : ℕ) (A : Fin (bigOf e) → List Bool),
      Step (worker onset (gInput e) (gFlag e) (gResult e) P)
        (workerBudget onset (fun _ => bud) len) (fun _ => 0)
        ((UAcceptanceCarrier.verifier (worker onset (gInput e) (gFlag e) (gResult e) P)
            (bigTwo e) (gResult e)).inputTapes (List.ofFn x) bits) (fun _ => 0) A ∧
      (readTapeBit (A (gResult e)) 0 = true ↔
        (CompetitorThresholdDecision.estimate (est .penalty).positive (est .penalty).negative
            (est .penalty).denominator ≤ 2*RepairSource.CompetitorRationalGap.zeta constants ∧
          CompetitorThresholdDecision.estimate (est .moment).positive (est .moment).negative
            (est .moment).denominator ≤ 1+RepairSource.CompetitorRationalGap.zeta constants ∧
          RepairSource.CompetitorRationalGap.midpoint constants ≤
            CompetitorThresholdDecision.estimate (est .clause).positive (est .clause).negative
              (est .clause).denominator)) ∧
      (∀ ph, A (scr e ph) =
        CloseoutRowsEstimatorCoefficients.Stream.recordWord (C10TailFeedPrep.w W) (est ph) 1 1) := by
  obtain ⟨Ab, hstepB, hrecB, hblankB, hcntB⟩ :=
    bodyThree_step e body F (List.ofFn x) bits
      (fun ph => CloseoutRowsEstimatorCoefficients.Stream.recordWord
        (C10TailFeedPrep.w W) (est ph) 1 1) hbody
  have hpark := parkedThree_of e est Ab hrecB hblankB
  obtain ⟨states, m, bud, H', A', hstepT, hiff, hpre⟩ :=
    C10TailVerdict.tail_step constants W (est .penalty) (est .moment) (est .clause)
      hvP hvM hvC hwidth (fun _ => 0) (fun i => Ab (tslot e i)) hpark
      (fun ph lower q W' est' hv hq hqnum hqden H A hp =>
        C10TailFeed.feed_exists ph lower q W' est' hv hq hqnum hqden H A hp)
  obtain ⟨A2, hstepD, hval⟩ := tail_dock e m bud H' A' Ab hstepT hcntB
  refine ⟨_, Composition.machine (bodyThree e body)
      (RecoveryFocus.machine (rtslot e) (Rewind.machine m)),
    bodyThreeFuel F + 1 + (2*bud+2), A2, ?_, ?_, ?_⟩
  · exact gate_of_inner e _ _ onset len x bits honset A2 (hstepB.seq hstepD)
  · rw [← tslot_flag e, hval C10TailVerdict.tailFlag]
    exact hiff
  · intro ph
    rw [← tslot_scratch e ph, hval (C10TailVerdict.scratchT ph),
      hpre _ (C10TailVerdict.scratchT_lt ph), tslot_scratch]
    exact hrecB ph

/-! ## §13 The uniform tail, and the FIXED composed machine

`C10Verdict.Verdict` fixes one machine `p` per input, which `verdict_run_of_records`
supplies; `C10Fusion.Pipeline` fixes ONE machine for every `n`, `x` and `bits`,
and that is strictly more.  `tail_step` as frozen quantifies `states` and `m`
INSIDE the `∀ W …`, so the composed machine varies with the record width — the
literal threshold words are written by `HierarchyFixedWord`, whose state count is
the word's length, i.e. `w W`.

`UniformTail` is the same theorem with `states`, `m` and the budget FUNCTION
hoisted out.  Against it the composed machine `composedWorker` is fixed once the
three block bodies and the tail machine are, and `Pipeline`'s single `p` exists. -/

/-- The six threshold-width bounds `tail_step` takes, named. -/
def TailWidths {source : RepairRepresentation.PointwisePCPPAlgorithm}
    (constants : RepairSource.CompetitorRationalGap.Constants source) (W : ℕ) : Prop :=
  CompetitorThresholdDecision.numerator
      (RepairSource.CompetitorRationalGap.meanThreshold constants) < 2^(C10TailFeedPrep.w W) ∧
    (RepairSource.CompetitorRationalGap.meanThreshold constants).den < 2^(C10TailFeedPrep.w W) ∧
    CompetitorThresholdDecision.numerator
      (RepairSource.CompetitorRationalGap.momentThreshold constants) < 2^(C10TailFeedPrep.w W) ∧
    (RepairSource.CompetitorRationalGap.momentThreshold constants).den
      < 2^(C10TailFeedPrep.w W) ∧
    CompetitorThresholdDecision.numerator
      (CompetitorThresholdDecision.acceptanceThreshold constants) < 2^(C10TailFeedPrep.w W) ∧
    (CompetitorThresholdDecision.acceptanceThreshold constants).den < 2^(C10TailFeedPrep.w W)

/-- **The interface `Pipeline` needs from T2**: `tail_step` with `states`, `m`
and the budget hoisted out of the `∀`. -/
def UniformTail {ts : ℕ} (m : Machine C10TailVerdict.tailBank ts) (tbud : ℕ → ℕ)
    {source : RepairRepresentation.PointwisePCPPAlgorithm}
    (constants : RepairSource.CompetitorRationalGap.Constants source) : Prop :=
  ∀ (W : ℕ) (eP eM eC : CompetitorValidity.Estimate),
    eP.Valid W → eM.Valid W → eC.Valid W → TailWidths constants W →
    ∀ (H : Fin C10TailVerdict.tailBank → ℕ) (A : Fin C10TailVerdict.tailBank → List Bool),
      C10TailVerdict.ParkedThree W eP eM eC H A →
      ∃ (H' : Fin C10TailVerdict.tailBank → ℕ) (A' : Fin C10TailVerdict.tailBank → List Bool),
        Step m (tbud W) H A H' A' ∧
        (readTapeBit (A' C10TailVerdict.tailFlag) 0 = true ↔
          (CompetitorThresholdDecision.estimate eP.positive eP.negative eP.denominator ≤
              2*RepairSource.CompetitorRationalGap.zeta constants ∧
            CompetitorThresholdDecision.estimate eM.positive eM.negative eM.denominator ≤
              1+RepairSource.CompetitorRationalGap.zeta constants ∧
            RepairSource.CompetitorRationalGap.midpoint constants ≤
              CompetitorThresholdDecision.estimate eC.positive eC.negative eC.denominator)) ∧
        (∀ i, i.val < 221 → A' i = A i)

/-- The whole inner machine: three phase bodies, then the docked tail. -/
noncomputable def innerOf {bs : Phase → ℕ} {ts : ℕ}
    (body : (ph : Phase) → Machine (218+e) (bs ph))
    (m : Machine C10TailVerdict.tailBank ts) :=
  Composition.machine (bodyThree e body)
    (RecoveryFocus.machine (rtslot e) (Rewind.machine m))

/-- **The composed C.10 weak machine.**  Fixed once the three block bodies and
the tail machine are: nothing in it mentions `n`, `x` or `bits`. -/
noncomputable def composedWorker {bs : Phase → ℕ} {ts : ℕ} (onset : ℕ)
    (body : (ph : Phase) → Machine (218+e) (bs ph))
    (m : Machine C10TailVerdict.tailBank ts) :=
  worker onset (gInput e) (gFlag e) (gResult e) (innerOf e body m)

/-- **T3, at a FIXED machine.**  Above the cutoff, one `Step` of `composedWorker`
from the verifier's own input tapes, with the C.10 verdict on `gResult` and the
three phase records still on their slots. -/
theorem verdict_run_uniform {bs : Phase → ℕ} {ts : ℕ}
    (body : (ph : Phase) → Machine (218+e) (bs ph)) (F : Phase → ℕ)
    (m : Machine C10TailVerdict.tailBank ts) (tbud : ℕ → ℕ)
    {source : RepairRepresentation.PointwisePCPPAlgorithm}
    (constants : RepairSource.CompetitorRationalGap.Constants source)
    (htail : UniformTail m tbud constants)
    (W : ℕ) (est : Phase → CompetitorValidity.Estimate)
    (hvP : (est .penalty).Valid W) (hvM : (est .moment).Valid W)
    (hvC : (est .clause).Valid W) (hwidth : TailWidths constants W)
    (onset len : ℕ) (x : BitInput len) (bits : List Bool) (honset : onset ≤ len)
    (hbody : ∀ ph, BlockRuns e (body ph) (F ph) (List.ofFn x) bits
      (CloseoutRowsEstimatorCoefficients.Stream.recordWord (C10TailFeedPrep.w W) (est ph) 1 1)) :
    ∃ A : Fin (bigOf e) → List Bool,
      Step (composedWorker e onset body m)
        (workerBudget onset (fun _ => bodyThreeFuel F + 1 + (2*tbud W+2)) len) (fun _ => 0)
        ((UAcceptanceCarrier.verifier (composedWorker e onset body m)
            (bigTwo e) (gResult e)).inputTapes (List.ofFn x) bits) (fun _ => 0) A ∧
      (readTapeBit (A (gResult e)) 0 = true ↔
        (CompetitorThresholdDecision.estimate (est .penalty).positive (est .penalty).negative
            (est .penalty).denominator ≤ 2*RepairSource.CompetitorRationalGap.zeta constants ∧
          CompetitorThresholdDecision.estimate (est .moment).positive (est .moment).negative
            (est .moment).denominator ≤ 1+RepairSource.CompetitorRationalGap.zeta constants ∧
          RepairSource.CompetitorRationalGap.midpoint constants ≤
            CompetitorThresholdDecision.estimate (est .clause).positive (est .clause).negative
              (est .clause).denominator)) ∧
      (∀ ph, A (scr e ph) =
        CloseoutRowsEstimatorCoefficients.Stream.recordWord (C10TailFeedPrep.w W) (est ph) 1 1) := by
  obtain ⟨Ab, hstepB, hrecB, hblankB, hcntB⟩ :=
    bodyThree_step e body F (List.ofFn x) bits
      (fun ph => CloseoutRowsEstimatorCoefficients.Stream.recordWord
        (C10TailFeedPrep.w W) (est ph) 1 1) hbody
  have hpark := parkedThree_of e est Ab hrecB hblankB
  obtain ⟨H', A', hstepT, hiff, hpre⟩ :=
    htail W (est .penalty) (est .moment) (est .clause) hvP hvM hvC hwidth
      (fun _ => 0) (fun i => Ab (tslot e i)) hpark
  obtain ⟨A2, hstepD, hval⟩ := tail_dock e m (tbud W) H' A' Ab hstepT hcntB
  refine ⟨A2, ?_, ?_, ?_⟩
  · exact gate_of_inner e (innerOf e body m) _ onset len x bits honset A2 (hstepB.seq hstepD)
  · rw [← tslot_flag e, hval C10TailVerdict.tailFlag]
    exact hiff
  · intro ph
    rw [← tslot_scratch e ph, hval (C10TailVerdict.scratchT ph),
      hpre _ (C10TailVerdict.scratchT_lt ph), tslot_scratch]
    exact hrecB ph

/-- **`Verdict.gate` at the fixed composed machine.** -/
theorem gate_uniform {bs : Phase → ℕ} {ts : ℕ}
    {source : RepairRepresentation.PointwisePCPPAlgorithm}
    (constants : RepairSource.CompetitorRationalGap.Constants source)
    (body : (ph : Phase) → Machine (218+e) (bs ph))
    (m : Machine C10TailVerdict.tailBank ts) (budget : ℕ → ℕ) :
    LengthGate constants
      (composedWorker e (CloseoutWitness.Soundness.cutoff constants) body m)
      (bigTwo e) (gResult e) budget :=
  gate_of_compose e constants (innerOf e body m) budget

end NearCubicWires.RepairSource.CloseoutFinal.C10TailCompose
