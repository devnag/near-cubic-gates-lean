import Proof.CaseAnalysis.FinalSupplierCountStage
import Proof.CaseAnalysis.FinalSeedEngine

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10PrologueBlankBand

open NearCubicWires
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDockSeam (phaseRecords)
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream (Entry)
open NearCubicWires.RepairSource.CloseoutFinal.C10PrologueUniform
  (Prologue bank_apply bankAt_scratch)
open NearCubicWires.RepairSource.CloseoutFinal.C10SupplierCall
open NearCubicWires.RepairSource.CloseoutFinal.C10SupplierCountStage
  (BlankFrom Rounds callsReady_of_rounds bank_scratch_apply)
open NearCubicWires.RepairSource.CloseoutLanguage (clauseWidth)
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPipeline

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## §1 The prologue's exit, read by tape number

`Prologue` (`Proof/CaseAnalysis/FinalPrologueUniform.lean`) states its exit as
`Fin.addCases` over the bank and the one extra counter tape.  Both halves are read
here by tape number, which is the only form the docking of §4 can use. -/

/-- The prologue's exit HEADS by tape number: parked everywhere but the counter. -/
theorem addCases_heads_apply (t : ℕ) (i : Fin (t + 1)) :
    Fin.addCases (motive := fun _ => ℕ) (fun _ => 0) (fun _ : Fin 1 => 1) i
      = if i.val = t then 1 else 0 := by
  refine Fin.addCases (m := t) (n := 1) (fun j => ?_) (fun j => ?_) i
  · rw [Fin.addCases_left]
    show (0 : ℕ) = if j.val = t then 1 else 0
    rw [if_neg (Nat.ne_of_lt j.isLt)]
  · rw [Fin.addCases_right]
    have hv : (Fin.natAdd t j : Fin (t + 1)).val = t := by
      have hj : j.val = 0 := Nat.lt_one_iff.mp j.isLt
      show t + j.val = t
      omega
    rw [hv, if_pos rfl]

/-- The prologue's exit TAPES by tape number. -/
theorem addCases_bank_apply {t : ℕ} (stream count driver input witness top : List Bool)
    (sc : ℕ → List Bool) (i : Fin (t + 1)) :
    Fin.addCases (motive := fun _ => List Bool)
        (bank stream count driver input witness sc : Fin t → List Bool)
        (fun _ : Fin 1 => top) i
      = if i.val = t then top
        else bankAt stream count driver input witness sc i.val := by
  refine Fin.addCases (m := t) (n := 1) (fun j => ?_) (fun j => ?_) i
  · rw [Fin.addCases_left]
    show bank stream count driver input witness sc j
        = if j.val = t then top else bankAt stream count driver input witness sc j.val
    rw [if_neg (Nat.ne_of_lt j.isLt)]
    rfl
  · rw [Fin.addCases_right]
    have hv : (Fin.natAdd t j : Fin (t + 1)).val = t := by
      have hj : j.val = 0 := Nat.lt_one_iff.mp j.isLt
      show t + j.val = t
      omega
    rw [hv, if_pos rfl]

/-- Two scratch functions that agree at ONE tape number give the same bank cell
there.  The band form of `bank_scratch_congr`
(`Proof/CaseAnalysis/FinalSupplierCall.lean`). -/
theorem bankAt_congr (stream count driver input witness : List Bool)
    (sc1 sc2 : ℕ → List Bool) (v : ℕ) (h : sc1 v = sc2 v) :
    bankAt stream count driver input witness sc1 v
      = bankAt stream count driver input witness sc2 v := by
  unfold bankAt
  split_ifs <;> first | rfl | exact h

/-! ## §2 The free invariant, and why it is worth nothing

`BlankFrom L` for `L` at or above the bank's width is deliverable from ANY
prologue, because `bank` (`Proof/CaseAnalysis/FinalSupplierCall.lean`) reads its
scratch only at tape numbers below the width.  The same fact is exactly why such
an invariant hands a round no blank tape. -/

/-- The scratch cut off at the bank's width. -/
def capScratch (t : ℕ) (s : ℕ → List Bool) : ℕ → List Bool :=
  fun v => if v < t then s v else []

theorem blankFrom_capScratch (t L : ℕ) (hL : t ≤ L) (s : ℕ → List Bool) :
    BlankFrom L (capScratch t s) := by
  intro v hv
  unfold capScratch
  rw [if_neg (by omega)]

theorem capScratch_low (t : ℕ) (s : ℕ → List Bool) (v : ℕ) (hv : v < t) :
    capScratch t s v = s v := by
  unfold capScratch
  rw [if_pos hv]

theorem capScratch_high (t : ℕ) (s : ℕ → List Bool) (v : ℕ) (hv : t ≤ v) :
    capScratch t s v = [] := by
  unfold capScratch
  rw [if_neg (by omega)]

/-- Cutting the scratch at the bank's width changes no bank tape. -/
theorem bank_capScratch {t : ℕ} (stream count driver input witness : List Bool)
    (s : ℕ → List Bool) :
    (bank stream count driver input witness (capScratch t s) : Fin t → List Bool)
      = bank stream count driver input witness s :=
  bank_scratch_congr stream count driver input witness _ _
    (fun j hj => capScratch_low t s j hj)

/-- **`hpre` at a line above the bank is FREE, for every prologue.**  This is
`callsReady_of_rounds`'s `hpre` binder
(`Proof/CaseAnalysis/FinalSupplierCountStage.lean`) at
`Inv := fun k s => BlankFrom (line + k * block) s`, discharged from nothing but
`Prologue` itself.  Read it together with
`blankFrom_above_bank_certifies_nothing` below: the reason it is free is the
reason it is useless. -/
theorem hpre_blankFrom_free (extra ps : ℕ) (pre : Machine (218 + (60 + extra) + 1) ps)
    (entryWidth q : ℕ → ℕ) (clauseDegree : ℕ) (preFuel : ℕ → ℕ)
    (hpro : Prologue extra entryWidth q clauseDegree preFuel pre)
    (line block : ℕ) (hline : 218 + (60 + extra) ≤ line)
    (len : ℕ) (x : BitInput len) (bits : List Bool) :
    ∃ w : ℕ → List Bool, BlankFrom (line + 0 * block) w ∧
      Step pre (preFuel len) (fun _ => 0)
        (bank [] [] [] (List.ofFn x) bits (fun _ => []))
        (Fin.addCases (motive := fun _ => ℕ) (fun _ => 0) (fun _ : Fin 1 => 1))
        (Fin.addCases (motive := fun _ => List Bool)
          (bank [] (CompareMachine.word 0) (List.replicate (entryWidth len) true)
            (List.ofFn x) bits w)
          (fun _ : Fin 1 => CompareMachine.word (2 ^ clauseWidth clauseDegree (q len)))) := by
  obtain ⟨w, hstep⟩ := hpro len x bits
  refine ⟨capScratch (218 + (60 + extra)) w, ?_, ?_⟩
  · have := blankFrom_capScratch (218 + (60 + extra)) line hline w
    intro v hv
    exact this v (by omega)
  · rw [bank_capScratch]
    exact hstep

/-- **An invariant at or above the bank's width certifies NO bank tape blank.**
Every bank is realized by a scratch that satisfies it, including one that is
nonempty at the very tape a docked engine wants empty.  So the `hpre` of
`hpre_blankFrom_free` hands a round nothing: `sum_dock`, `copy_dock`,
`product_dock`, `fixedWord_dock` (`Proof/CaseAnalysis/FinalWordEngines.lean`,
`:90`, `:120`, `:161`), `divide_dock`, `answer_dock`
(`Proof/CaseAnalysis/FinalDividerDock.lean`, `:141`) and `dock`, `clause_dock`,
`support_dock` (`Proof/CaseAnalysis/FinalWordFunctionDock.lean`, `:267`, `:286`)
each demand `A (slots j) = []`, and this invariant refutes none of the banks that
break it. -/
theorem blankFrom_above_bank_certifies_nothing {t : ℕ} (L : ℕ) (hL : t ≤ L)
    (stream count driver input witness : List Bool) (i : Fin t) (hi : 278 ≤ i.val) :
    ∃ s : ℕ → List Bool, BlankFrom L s ∧
      (bank stream count driver input witness s : Fin t → List Bool) i ≠ [] := by
  refine ⟨capScratch t (fun _ => [true]), blankFrom_capScratch t L hL _, ?_⟩
  rw [bank_scratch_apply stream count driver input witness _ i hi,
    capScratch_low t _ i.val i.isLt]
  simp

/-- **The band is exhausted after finitely many rounds.**  Once
`line + k * block` reaches the bank's width the round invariant is the vacuous one
of `blankFrom_above_bank_certifies_nothing`.  A bank of FIXED width therefore
supports a fresh blank block for finitely many `k`, while `Rounds`
(`Proof/CaseAnalysis/FinalSupplierCountStage.lean`) quantifies `k` over all of
`ℕ`: choosing how many rounds get a band is a real decision, not a detail. -/
theorem band_exhausted {t : ℕ} (line block k : ℕ) (hk : t ≤ line + k * block)
    (stream count driver input witness : List Bool) (i : Fin t) (hi : 278 ≤ i.val) :
    ∃ s : ℕ → List Bool, BlankFrom (line + k * block) s ∧
      (bank stream count driver input witness s : Fin t → List Bool) i ≠ [] :=
  blankFrom_above_bank_certifies_nothing (line + k * block) hk stream count driver input
    witness i hi

/-- **The arithmetic of the collision.**  At `extra = tapesOf tw r D + 23` — the
value `bankSlots` (`Proof/CaseAnalysis/FinalSeedEngine.lean`) is built for — the
round body's bank `Fin (218 + (60 + extra))` has exactly the tape numbers
`0 .. 300 + tapesOf tw r D`, and `bankSlots_private`
(`Proof/CaseAnalysis/FinalSeedEngine.lean`) puts the engine's private tapes in
`[301, 301 + tapesOf tw r D)`.  The private band IS the top of the body bank. -/
theorem engine_band_is_the_whole_bank (tw r D : ℕ) :
    218 + (60 + (CloseoutFinalC10SeedEngine.tapesOf tw r D + 23))
      = 301 + CloseoutFinalC10SeedEngine.tapesOf tw r D := by
  omega

/-- The exact slot each private engine tape lands on: `301 + j.val`. -/
theorem engine_private_slot {tw : ℕ} (r D : ℕ) (inW : Fin tw)
    (j : Fin (CloseoutFinalC10SeedEngine.tapesOf tw r D))
    (h1 : j.val ≠ inW.val) (h2 : j.val ≠ tw) (h3 : j.val ≠ tw + 1) :
    (CloseoutFinalC10SeedEngine.bankSlots tw r D inW j).val = 301 + j.val := by
  show (if j.val = inW.val then 0 else if j.val = tw then 218
      else if j.val = tw + 1 then 278 else 301 + j.val) = 301 + j.val
  rw [if_neg h1, if_neg h2, if_neg h3]

/-- **`Seed` says nothing about the engine's private band.**  Its two blankness
clauses — `279 .. 300`, and the loop counter tape `301 + e` — are consistent with a
DIRTY tape at every `v` of `[301, 300 + e]`, which by
`engine_band_is_the_whole_bank` is the whole of the round body's scratch band above
`300`.  So no strengthening of `BlankFrom line` with `line ≤ 300 + e` is derivable
from `Prologue` (`Proof/CaseAnalysis/FinalPrologueUniform.lean`) as it stands,
and `blank_not_restorable`
(`Proof/CaseAnalysis/FinalSupplierCountStage.lean`) forbids clearing it later. -/
theorem seed_allows_dirt_above_300 (e v : ℕ) (h1 : 301 ≤ v) (h2 : v ≤ 300 + e) :
    ∃ junk : ℕ → List Bool,
      (∀ u, 279 ≤ u → u ≤ 300 → junk u = []) ∧ junk (301 + e) = [] ∧ junk v ≠ [] := by
  refine ⟨fun u => if u ≤ 300 ∨ u = 301 + e then [] else [true], ?_, ?_, ?_⟩
  · intro u _ hu
    show (if u ≤ 300 ∨ u = 301 + e then [] else [true]) = []
    rw [if_pos (Or.inl hu)]
  · show (if 301 + e ≤ 300 ∨ 301 + e = 301 + e then [] else [true]) = []
    rw [if_pos (Or.inr rfl)]
  · show (if v ≤ 300 ∨ v = 301 + e then [] else [true]) ≠ []
    rw [if_neg (by omega)]
    simp

/-- The old bank inside the widened one: the loop counter tape goes to the new
top, every other tape to its own number. -/
def widen (extra m : ℕ) (i : Fin (218 + (60 + extra) + 1)) :
    Fin (218 + (60 + (extra + m)) + 1) :=
  ⟨if i.val = 218 + (60 + extra) then 218 + (60 + (extra + m)) else i.val, by
    have := i.isLt; split_ifs <;> omega⟩

theorem widen_val_last (extra m : ℕ) (i : Fin (218 + (60 + extra) + 1))
    (h : i.val = 218 + (60 + extra)) :
    (widen extra m i).val = 218 + (60 + (extra + m)) := by
  show (if i.val = 218 + (60 + extra) then 218 + (60 + (extra + m)) else i.val)
      = 218 + (60 + (extra + m))
  rw [if_pos h]

theorem widen_val_low (extra m : ℕ) (i : Fin (218 + (60 + extra) + 1))
    (h : i.val ≠ 218 + (60 + extra)) : (widen extra m i).val = i.val := by
  show (if i.val = 218 + (60 + extra) then 218 + (60 + (extra + m)) else i.val) = i.val
  rw [if_neg h]

theorem widen_injective (extra m : ℕ) : Function.Injective (widen extra m) := by
  intro a b h
  have ha := a.isLt
  have hb := b.isLt
  have hv : (widen extra m a).val = (widen extra m b).val :=
    congrArg (fun z : Fin (218 + (60 + (extra + m)) + 1) => z.val) h
  apply Fin.ext
  by_cases hA : a.val = 218 + (60 + extra) <;> by_cases hB : b.val = 218 + (60 + extra)
  · omega
  · rw [widen_val_last extra m a hA, widen_val_low extra m b hB] at hv; omega
  · rw [widen_val_low extra m a hA, widen_val_last extra m b hB] at hv; omega
  · rw [widen_val_low extra m a hA, widen_val_low extra m b hB] at hv; omega

/-- Every tape of the widened bank that the old bank does not reach. -/
theorem widen_other (extra m : ℕ) (i : Fin (218 + (60 + (extra + m)) + 1))
    (h1 : 218 + (60 + extra) ≤ i.val) (h2 : i.val ≠ 218 + (60 + (extra + m))) :
    ∀ j, widen extra m j ≠ i := by
  intro j hj
  have hjl := j.isLt
  have hv : (widen extra m j).val = i.val :=
    congrArg (fun z : Fin (218 + (60 + (extra + m)) + 1) => z.val) hj
  by_cases hA : j.val = 218 + (60 + extra)
  · rw [widen_val_last extra m j hA] at hv; omega
  · rw [widen_val_low extra m j hA] at hv; omega

theorem widen_hits_low (extra m : ℕ) (i : Fin (218 + (60 + (extra + m)) + 1))
    (h : i.val < 218 + (60 + extra)) :
    widen extra m ⟨i.val, by omega⟩ = i := by
  apply Fin.ext
  rw [widen_val_low extra m ⟨i.val, by omega⟩ (by simp only []; omega)]

theorem widen_hits_top (extra m : ℕ) (i : Fin (218 + (60 + (extra + m)) + 1))
    (h : i.val = 218 + (60 + (extra + m))) :
    widen extra m ⟨218 + (60 + extra), by omega⟩ = i := by
  apply Fin.ext
  rw [widen_val_last extra m ⟨218 + (60 + extra), by omega⟩ rfl, h]

/-- The entry bank is the same on both sides of the relabelling. -/
theorem bank_widen_entry (extra m : ℕ) (input witness : List Bool)
    (j : Fin (218 + (60 + extra) + 1)) :
    (bank [] [] [] input witness (fun _ => [])
        : Fin (218 + (60 + (extra + m)) + 1) → List Bool) (widen extra m j)
      = (bank [] [] [] input witness (fun _ => [])
        : Fin (218 + (60 + extra) + 1) → List Bool) j := by
  show bankAt [] [] [] input witness (fun _ => []) (widen extra m j).val
      = bankAt [] [] [] input witness (fun _ => []) j.val
  by_cases h : j.val = 218 + (60 + extra)
  · rw [widen_val_last extra m j h, bankAt_scratch _ _ _ _ _ _ _ (by omega),
      bankAt_scratch _ _ _ _ _ _ _ (by omega)]
  · rw [widen_val_low extra m j h]

/-- **`Prologue` fused with the blank band it must hand the first round.**  The
type names `line`, so a widening that produced no blank band cannot inhabit it;
`prologueBlank_prologue` shows nothing of `Prologue` is lost. -/
def PrologueBlank (extra line : ℕ) (entryWidth q : ℕ → ℕ) (clauseDegree : ℕ)
    (preFuel : ℕ → ℕ) {ps : ℕ} (pre : Machine (218 + (60 + extra) + 1) ps) : Prop :=
  ∀ (len : ℕ) (x : BitInput len) (bits : List Bool),
    ∃ w : ℕ → List Bool,
      BlankFrom line w ∧
      Step pre (preFuel len) (fun _ => 0)
        (bank [] [] [] (List.ofFn x) bits (fun _ => []))
        (Fin.addCases (motive := fun _ => ℕ) (fun _ => 0) (fun _ : Fin 1 => 1))
        (Fin.addCases (motive := fun _ => List Bool)
          (bank [] (CompareMachine.word 0) (List.replicate (entryWidth len) true)
            (List.ofFn x) bits w)
          (fun _ : Fin 1 => CompareMachine.word (2 ^ clauseWidth clauseDegree (q len))))

theorem prologueBlank_prologue (extra line ps : ℕ)
    (pre : Machine (218 + (60 + extra) + 1) ps)
    (entryWidth q : ℕ → ℕ) (clauseDegree : ℕ) (preFuel : ℕ → ℕ)
    (h : PrologueBlank extra line entryWidth q clauseDegree preFuel pre) :
    Prologue extra entryWidth q clauseDegree preFuel pre := by
  intro len x bits
  obtain ⟨w, _, hstep⟩ := h len x bits
  exact ⟨w, hstep⟩

/-- The relabelled exit heads. -/
theorem dockH_widen (extra m : ℕ) :
    dockH (widen extra m) (fun _ => (0 : ℕ))
        (Fin.addCases (motive := fun _ => ℕ) (fun _ => 0) (fun _ : Fin 1 => 1))
      = Fin.addCases (motive := fun _ => ℕ) (fun _ => 0) (fun _ : Fin 1 => 1) := by
  funext i
  have hi := i.isLt
  by_cases hT : i.val = 218 + (60 + (extra + m))
  · rw [← widen_hits_top extra m i hT,
      dockH_slot (widen extra m) (widen_injective extra m),
      addCases_heads_apply, addCases_heads_apply,
      widen_val_last extra m ⟨218 + (60 + extra), by omega⟩ rfl]
    rw [if_pos rfl, if_pos rfl]
  · by_cases hlow : i.val < 218 + (60 + extra)
    · rw [← widen_hits_low extra m i hlow,
        dockH_slot (widen extra m) (widen_injective extra m),
        addCases_heads_apply, addCases_heads_apply,
        widen_val_low extra m ⟨i.val, by omega⟩ (by simp only []; omega)]
      rw [if_neg (by simp only []; omega), if_neg (by omega)]
    · rw [dockH_other (widen extra m) _ _ i (widen_other extra m i (by omega) hT),
        addCases_heads_apply, if_neg hT]

/-- The relabelled exit tapes: the old bank's cells where they were, the fresh
tapes blank, the counter word on the new top. -/
theorem install_widen (extra m : ℕ) (driver input witness top : List Bool)
    (w : ℕ → List Bool) :
    install (widen extra m)
        (bank [] [] [] input witness (fun _ => [])
          : Fin (218 + (60 + (extra + m)) + 1) → List Bool)
        (Fin.addCases (motive := fun _ => List Bool)
          (bank [] (CompareMachine.word 0) driver input witness w
            : Fin (218 + (60 + extra)) → List Bool)
          (fun _ : Fin 1 => top))
      = Fin.addCases (motive := fun _ => List Bool)
          (bank [] (CompareMachine.word 0) driver input witness
              (capScratch (218 + (60 + extra)) w)
            : Fin (218 + (60 + (extra + m))) → List Bool)
          (fun _ : Fin 1 => top) := by
  funext i
  have hi := i.isLt
  by_cases hT : i.val = 218 + (60 + (extra + m))
  · rw [← widen_hits_top extra m i hT,
      install_slot (widen extra m) (widen_injective extra m),
      addCases_bank_apply, addCases_bank_apply,
      widen_val_last extra m ⟨218 + (60 + extra), by omega⟩ rfl]
    rw [if_pos rfl, if_pos rfl]
  · by_cases hlow : i.val < 218 + (60 + extra)
    · rw [← widen_hits_low extra m i hlow,
        install_slot (widen extra m) (widen_injective extra m),
        addCases_bank_apply, addCases_bank_apply,
        widen_val_low extra m ⟨i.val, by omega⟩ (by simp only []; omega)]
      rw [if_neg (by simp only []; omega), if_neg (by omega)]
      exact bankAt_congr [] (CompareMachine.word 0) driver input witness w _ i.val
        (capScratch_low (218 + (60 + extra)) w i.val hlow).symm
    · rw [install_other (widen extra m) _ _ i (widen_other extra m i (by omega) hT),
        addCases_bank_apply, if_neg hT,
        bankAt_scratch _ _ _ _ _ _ _ (by omega),
        capScratch_high (218 + (60 + extra)) w i.val (by omega)]
      show bankAt [] [] [] input witness (fun _ => []) i.val = []
      rw [bankAt_scratch _ _ _ _ _ _ _ (by omega)]

theorem prologue_widen (extra m ps : ℕ) (pre : Machine (218 + (60 + extra) + 1) ps)
    (entryWidth q : ℕ → ℕ) (clauseDegree : ℕ) (preFuel : ℕ → ℕ)
    (hpro : Prologue extra entryWidth q clauseDegree preFuel pre) :
    PrologueBlank (extra + m) (218 + (60 + extra)) entryWidth q clauseDegree preFuel
      (RecoveryFocus.machine (widen extra m) pre) := by
  intro len x bits
  obtain ⟨w, hstep⟩ := hpro len x bits
  refine ⟨capScratch (218 + (60 + extra)) w,
    blankFrom_capScratch (218 + (60 + extra)) (218 + (60 + extra)) (le_refl _) w, ?_⟩
  have hdock := hstep.dock (widen extra m) (widen_injective extra m)
    (fun _ => 0)
    (bank [] [] [] (List.ofFn x) bits (fun _ => [])
      : Fin (218 + (60 + (extra + m)) + 1) → List Bool)
    (fun j => rfl) (fun j => bank_widen_entry extra m (List.ofFn x) bits j)
  rw [dockH_widen extra m, install_widen extra m] at hdock
  exact hdock

/-- The band `[line, line + m)` is above `278` and inside the widened bank. -/
theorem widened_band_fits (extra m : ℕ) :
    278 ≤ 218 + (60 + extra) ∧
      218 + (60 + extra) + m = 218 + (60 + (extra + m)) := by
  omega

/-- **The payoff, in the form the docked-engine library asks for.**  `dock`
(`Proof/CaseAnalysis/FinalWordFunctionDock.lean`) and its eight siblings demand
`A (slots j) = []`; a band slot at or above `line` is exactly that. -/
theorem bank_blank_of_blankFrom {t : ℕ} (line : ℕ) (hline : 278 ≤ line)
    (s : ℕ → List Bool) (hs : BlankFrom line s)
    (stream count driver input witness : List Bool) (i : Fin t) (hi : line ≤ i.val) :
    (bank stream count driver input witness s : Fin t → List Bool) i = [] := by
  rw [bank_scratch_apply stream count driver input witness s i
    (by omega)]
  exact hs i.val hi

/-- **`callsReady_of_rounds`'s `hpre` binder, at the blank-band invariant.** -/
theorem hpre_of_prologueBlank (extra line ps : ℕ)
    (pre : Machine (218 + (60 + extra) + 1) ps)
    (entryWidth q : ℕ → ℕ) (clauseDegree : ℕ) (preFuel : ℕ → ℕ) (block : ℕ)
    (hpb : PrologueBlank extra line entryWidth q clauseDegree preFuel pre)
    (len : ℕ) (x : BitInput len) (bits : List Bool) :
    ∃ w : ℕ → List Bool, BlankFrom (line + 0 * block) w ∧
      Step pre (preFuel len) (fun _ => 0)
        (bank [] [] [] (List.ofFn x) bits (fun _ => []))
        (Fin.addCases (motive := fun _ => ℕ) (fun _ => 0) (fun _ : Fin 1 => 1))
        (Fin.addCases (motive := fun _ => List Bool)
          (bank [] (CompareMachine.word 0) (List.replicate (entryWidth len) true)
            (List.ofFn x) bits w)
          (fun _ : Fin 1 => CompareMachine.word (2 ^ clauseWidth clauseDegree (q len)))) := by
  obtain ⟨w, hw, hstep⟩ := hpb len x bits
  refine ⟨w, ?_, hstep⟩
  intro v hv
  exact hw v (by omega)

variable {Atom : Type} {arity : ℕ} {circuit : BooleanCircuit arity}

theorem callsReady_of_rounds_blankBand (extra m : ℕ) {ps bs : ℕ}
    (pre : Machine (218 + (60 + extra) + 1) ps)
    (body : Machine (218 + (60 + (extra + m))) bs)
    (answer : List Atom → ℕ) (denominator : ℕ)
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (entryWidth q preFuel : ℕ → ℕ) (clauseDegree callCount cost block : ℕ)
    (len : ℕ) (x : BitInput len) (bits : List Bool)
    (hlen : (phaseRecords answer denominator phase pcpp coordinate systematicAtom).length
      = callCount)
    (hfit : pcpp.clauseBits ≤ clauseWidth clauseDegree (q len))
    (hpro : Prologue extra entryWidth q clauseDegree preFuel pre)
    (hrounds : Rounds (extra + m) body cost (entryWidth len) answer denominator phase pcpp
      coordinate systematicAtom (List.ofFn x) bits
      (fun k s => BlankFrom (218 + (60 + extra) + k * block) s)) :
    RepairSource.CloseoutFinal.C10SupplierStage.CallsReady (extra + m + 2)
      (callMachine (extra + m) (RecoveryFocus.machine (widen extra m) pre) body)
      (callFuel (preFuel len) (clauseWidth clauseDegree (q len)) cost) (entryWidth len)
      callCount
      (CloseoutRowsEstimatorCoefficients.Stream.words (entryWidth len)
        (phaseRecords answer denominator phase pcpp coordinate systematicAtom))
      (List.ofFn x) bits :=
  callsReady_of_rounds (extra + m) (RecoveryFocus.machine (widen extra m) pre) body answer
    denominator phase pcpp coordinate systematicAtom (entryWidth len) callCount (preFuel len)
    cost clauseDegree (q len) (List.ofFn x) bits
    (fun k s => BlankFrom (218 + (60 + extra) + k * block) s) hlen hfit hrounds
    (hpre_of_prologueBlank (extra + m) (218 + (60 + extra)) ps
      (RecoveryFocus.machine (widen extra m) pre) entryWidth q clauseDegree preFuel block
      (prologue_widen extra m ps pre entryWidth q clauseDegree preFuel hpro) len x bits)

theorem prologue_blank_at_schedule_closed (sources : RepairSource.EightSources)
    (k r D m : ℕ) (hD : 1 ≤ D) :
    ∃ (extra ps line : ℕ) (preFuel : ℕ → ℕ) (pre : Machine (218 + (60 + extra) + 1) ps),
      278 ≤ line ∧ line + m = 218 + (60 + extra) ∧
      PrologueBlank extra line
        (RepairSource.CloseoutFinal.C10PartsSchedule.entryWidthSchedule sources k r)
        (RepairSource.CloseoutFinal.C10PartsSchedule.widthAt sources k) D preFuel pre := by
  obtain ⟨extra, ps, preFuel, pre, hpro⟩ :=
    CloseoutFinalC10SeedEngine.prologue_at_schedule_closed sources k r D hD
  exact ⟨extra + m, ps, 218 + (60 + extra), preFuel,
    RecoveryFocus.machine (widen extra m) pre, by omega, by omega,
    prologue_widen extra m ps pre _ _ D preFuel hpro⟩

end NearCubicWires.RepairOrdinary.CloseoutFinalC10PrologueBlankBand
