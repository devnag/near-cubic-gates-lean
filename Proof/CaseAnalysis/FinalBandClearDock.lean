import Proof.CaseAnalysis.FinalBandRecycle

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10BandClearDock

open NearCubicWires
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.RepairSource.CloseoutFinal.C10SupplierCall (bank)
open NearCubicWires.RepairSource.CloseoutFinal.C10SupplierCountStage
  (scratchOf scratchOf_apply bank_scratch_apply round_step_of_dock)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10BandRecycle (ZeroBand)

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## §1  The band slot map: three fixed tape numbers, and nothing that moves -/

/-- Tape number of the eraser's slot `j`: the `t` scratch tapes at
`line+2 .. line+2+t`, the unary driver at `line`, the reset log at `line+1`. -/
def bandSlot (line t : ℕ) (j : Fin (t + 1 + 1)) : ℕ :=
  if j.val < t then line + 2 + j.val else if j.val = t then line else line + 1

/-- The same, landed in the C.10 bank's index type.  **Nothing here depends on
the round index**; that is the whole content of band REUSE. -/
def bandSlots (extra line t : ℕ) (hfit : line + 2 + t ≤ 218 + (60 + extra))
    (j : Fin (t + 1 + 1)) : Fin (218 + (60 + extra)) :=
  ⟨bandSlot line t j, by
    have hj := j.isLt
    unfold bandSlot
    split_ifs <;> omega⟩

theorem bandSlots_val_work (extra line t : ℕ) (hfit : line + 2 + t ≤ 218 + (60 + extra))
    (i : Fin t) :
    (bandSlots extra line t hfit ((i.castAdd 1).castAdd 1)).val = line + 2 + i.val := by
  show bandSlot line t ((i.castAdd 1).castAdd 1) = line + 2 + i.val
  have hv : ((i.castAdd 1).castAdd 1 : Fin (t + 1 + 1)).val = i.val := rfl
  have hlt := i.isLt
  unfold bandSlot
  rw [hv, if_pos hlt]

theorem bandSlots_val_driver (extra line t : ℕ) (hfit : line + 2 + t ≤ 218 + (60 + extra)) :
    (bandSlots extra line t hfit (((0 : Fin 1).natAdd t).castAdd 1)).val = line := by
  show bandSlot line t (((0 : Fin 1).natAdd t).castAdd 1) = line
  have hv : ((((0 : Fin 1).natAdd t).castAdd 1) : Fin (t + 1 + 1)).val = t := rfl
  unfold bandSlot
  rw [hv]
  split_ifs <;> omega

theorem bandSlots_val_log (extra line t : ℕ) (hfit : line + 2 + t ≤ 218 + (60 + extra)) :
    (bandSlots extra line t hfit ((0 : Fin 1).natAdd (t + 1))).val = line + 1 := by
  show bandSlot line t ((0 : Fin 1).natAdd (t + 1)) = line + 1
  have hv : (((0 : Fin 1).natAdd (t + 1)) : Fin (t + 1 + 1)).val = t + 1 := rfl
  unfold bandSlot
  rw [hv]
  split_ifs <;> omega

/-- **The band is a bounded window.**  Every slot is below `line + 2 + t`, which
is what lets everything above the window be framed out. -/
theorem bandSlots_val_lt (extra line t : ℕ) (hfit : line + 2 + t ≤ 218 + (60 + extra))
    (j : Fin (t + 1 + 1)) : (bandSlots extra line t hfit j).val < line + 2 + t := by
  show bandSlot line t j < line + 2 + t
  have hj := j.isLt
  unfold bandSlot
  split_ifs <;> omega

/-- The band sits on the bank's scratch region, so `bank_scratch_apply`
(`Proof/CaseAnalysis/FinalSupplierCountStage.lean`) applies at every slot. -/
theorem bandSlots_band (extra line t : ℕ) (hfit : line + 2 + t ≤ 218 + (60 + extra))
    (hline : 278 ≤ line) (j : Fin (t + 1 + 1)) :
    278 ≤ (bandSlots extra line t hfit j).val := by
  show 278 ≤ bandSlot line t j
  unfold bandSlot
  split_ifs <;> omega

theorem bandSlots_injective (extra line t : ℕ) (hfit : line + 2 + t ≤ 218 + (60 + extra)) :
    Function.Injective (bandSlots extra line t hfit) := by
  intro a b hab
  have h : bandSlot line t a = bandSlot line t b := congrArg Fin.val hab
  have ha := a.isLt
  have hb := b.isLt
  refine Fin.ext ?_
  unfold bandSlot at h
  split_ifs at h <;> omega

/-! ## §2  The eraser's own entry and exit layouts, named -/

/-- The eraser's entry tapes at capacity `total + 1`: dirt, driver, log. -/
def clearIn (total t : ℕ) (backing : Fin t → List Bool) : Fin (t + 1 + 1) → List Bool :=
  Fin.addCases (Fin.addCases backing (fun _ : Fin 1 => List.replicate total true))
    (fun _ : Fin 1 => List.replicate (total + 1) false)

/-- The eraser's exit tapes at capacity `total + 1`.  **The log entry and the log
exit are the same list** -- that is `clear_capacity_fixed`
(`Proof/CaseAnalysis/FinalBandRecycle.lean`) spent, and it is why the band is
reusable rather than merely erasable once. -/
def clearOut (total t : ℕ) : Fin (t + 1 + 1) → List Bool :=
  Fin.addCases (Fin.addCases (fun _ : Fin t => List.replicate total false)
    (fun _ : Fin 1 => List.replicate total true))
    (fun _ : Fin 1 => List.replicate (total + 1) false)

theorem clearIn_work (total t : ℕ) (backing : Fin t → List Bool) (i : Fin t) :
    clearIn total t backing ((i.castAdd 1).castAdd 1) = backing i := by
  unfold clearIn; simp only [Fin.addCases_left]

theorem clearIn_driver (total t : ℕ) (backing : Fin t → List Bool) :
    clearIn total t backing (((0 : Fin 1).natAdd t).castAdd 1) = List.replicate total true := by
  unfold clearIn; simp only [Fin.addCases_left, Fin.addCases_right]

theorem clearIn_log (total t : ℕ) (backing : Fin t → List Bool) :
    clearIn total t backing ((0 : Fin 1).natAdd (t + 1)) = List.replicate (total + 1) false := by
  unfold clearIn; simp only [Fin.addCases_right]

theorem clearOut_work (total t : ℕ) (i : Fin t) :
    clearOut total t ((i.castAdd 1).castAdd 1) = List.replicate total false := by
  unfold clearOut; simp only [Fin.addCases_left]

theorem clearOut_driver (total t : ℕ) :
    clearOut total t (((0 : Fin 1).natAdd t).castAdd 1) = List.replicate total true := by
  unfold clearOut; simp only [Fin.addCases_left, Fin.addCases_right]

theorem clearOut_log (total t : ℕ) :
    clearOut total t ((0 : Fin 1).natAdd (t + 1)) = List.replicate (total + 1) false := by
  unfold clearOut; simp only [Fin.addCases_right]

/-- **`clear_step` at the capacity that is a fixed point.**  Instantiating
`BandRecycle.clear_step` (`Proof/CaseAnalysis/FinalBandRecycle.lean`) at
`capacity := total + 1` collapses `max capacity (total+1)` to `total + 1`. -/
theorem clear_step_fixed (total t : ℕ) (backing : Fin t → List Bool)
    (hb : ∀ i, (backing i).length ≤ total) :
    Step (RecoveryScratchErase.resetMachine t) (2 * total + 4) (fun _ => 0)
      (clearIn total t backing) (fun _ => 0) (clearOut total t) := by
  have h := CloseoutFinalC10BandRecycle.clear_step (t := t) total (total + 1) backing hb
  rw [max_self] at h
  exact h

/-! ## §3  The dock -/

theorem clear_bank_dock (extra total line t : ℕ) (hline : 278 ≤ line)
    (hfit : line + 2 + t ≤ 218 + (60 + extra))
    (stream count driver input witness : List Bool) (s : ℕ → List Bool)
    (hb : ∀ i : Fin t, (s (line + 2 + i.val)).length ≤ total)
    (hdriver : s line = List.replicate total true)
    (hlog : s (line + 1) = List.replicate (total + 1) false) :
    Step (RecoveryFocus.machine (bandSlots extra line t hfit)
        (RecoveryScratchErase.resetMachine t)) (2 * total + 4) (fun _ => 0)
      (bank stream count driver input witness s) (fun _ => 0)
      (bank stream count driver input witness
        (scratchOf extra
          (install (bandSlots extra line t hfit)
            (bank stream count driver input witness s) (clearOut total t)) s)) := by
  have hinj := bandSlots_injective extra line t hfit
  have hband := bandSlots_band extra line t hfit hline
  have hA : ∀ j, bank stream count driver input witness s (bandSlots extra line t hfit j)
      = clearIn total t (fun i : Fin t => s (line + 2 + i.val)) j := by
    intro j
    refine Fin.addCases (m := t + 1) (n := 1) (fun k => ?_) (fun k => ?_) j
    · refine Fin.addCases (m := t) (n := 1) (fun i => ?_) (fun i => ?_) k
      · rw [bank_scratch_apply stream count driver input witness s _ (hband _),
          bandSlots_val_work, clearIn_work]
      · rw [Subsingleton.elim i (0 : Fin 1),
          bank_scratch_apply stream count driver input witness s _ (hband _),
          bandSlots_val_driver, clearIn_driver, hdriver]
    · rw [Subsingleton.elim k (0 : Fin 1),
        bank_scratch_apply stream count driver input witness s _ (hband _),
        bandSlots_val_log, clearIn_log, hlog]
  have hdock := (clear_step_fixed total t (fun i : Fin t => s (line + 2 + i.val))
    (fun i => hb i)).dock (bandSlots extra line t hfit) hinj (fun _ => 0)
      (bank stream count driver input witness s) (fun _ => rfl) hA
  rw [dockH_existing (bandSlots extra line t hfit) (fun _ => 0) (fun _ => 0)
    (fun _ => rfl)] at hdock
  refine round_step_of_dock extra (2 * total + 4) stream count driver input witness s
    (bandSlots extra line t hfit) hband (fun _ => 0) _ hdock (fun _ => rfl) ?_
  intro i hi
  exact install_other _ _ _ i hi

/-! ## §4  The fixed point -/

/-- **The band's entry layout, at fixed tape numbers.**  The third conjunct is
`BandRecycle.ZeroBand` (`Proof/CaseAnalysis/FinalBandRecycle.lean`) verbatim,
so `round_step_of_zeroBand` (`:277`) consumes this invariant directly at
`line := line + 2`. -/
def BandReady (total line : ℕ) (s : ℕ → List Bool) : Prop :=
  s line = List.replicate total true ∧
    s (line + 1) = List.replicate (total + 1) false ∧ ZeroBand total (line + 2) s

/-- **What a round must not do.**  It may dirty the band window, and must leave
the eraser's own driver and log, and everything above the window, alone.  Every
docked engine's frame clause (`∀ i, (∀ j, slots j ≠ i) → B i = A i`) delivers
this whenever the round's slots lie inside `[line+2, line+2+t)`. -/
def Confined (line t : ℕ) (s s' : ℕ → List Bool) : Prop :=
  s' line = s line ∧ s' (line + 1) = s (line + 1) ∧ ∀ v, line + 2 + t ≤ v → s' v = s v

theorem scratchOf_high (extra : ℕ) (A : Fin (218 + (60 + extra)) → List Bool)
    (s : ℕ → List Bool) (v : ℕ) (hv : ¬ v < 218 + (60 + extra)) :
    scratchOf extra A s v = s v := by
  unfold NearCubicWires.RepairSource.CloseoutFinal.C10SupplierCountStage.scratchOf
  rw [dif_neg hv]

/-- **The clear RESTORES the entry layout.**  Driver and log come back because
the exit is `install` and `install_slot` reads them; the band comes back because
every tape of the window is a slot, and every tape above the window was never a
slot and so is framed through unchanged. -/
theorem bandReady_of_clear (extra total line t : ℕ) (hline : 278 ≤ line)
    (hfit : line + 2 + t ≤ 218 + (60 + extra))
    (stream count driver input witness : List Bool) (s : ℕ → List Bool)
    (houter : ∀ v, line + 2 + t ≤ v → s v = List.replicate total false) :
    BandReady total line
      (scratchOf extra
        (install (bandSlots extra line t hfit)
          (bank stream count driver input witness s) (clearOut total t)) s) := by
  have hinj := bandSlots_injective extra line t hfit
  set A := install (bandSlots extra line t hfit)
    (bank stream count driver input witness s) (clearOut total t) with hAdef
  have hslot : ∀ j : Fin (t + 1 + 1),
      scratchOf extra A s (bandSlots extra line t hfit j).val = clearOut total t j := by
    intro j
    rw [scratchOf_apply extra A s (bandSlots extra line t hfit j), hAdef,
      install_slot _ hinj]
  refine ⟨?_, ?_, ?_⟩
  · have h := hslot (((0 : Fin 1).natAdd t).castAdd 1)
    rw [bandSlots_val_driver, clearOut_driver] at h
    exact h
  · have h := hslot ((0 : Fin 1).natAdd (t + 1))
    rw [bandSlots_val_log, clearOut_log] at h
    exact h
  · intro v hv
    by_cases hin : v < line + 2 + t
    · have h := hslot ((((⟨v - (line + 2), by omega⟩ : Fin t)).castAdd 1).castAdd 1)
      rw [bandSlots_val_work, clearOut_work] at h
      have he : line + 2 + (⟨v - (line + 2), by omega⟩ : Fin t).val = v := by
        show line + 2 + (v - (line + 2)) = v
        omega
      rw [he] at h
      exact h
    · have hge : line + 2 + t ≤ v := by omega
      by_cases hw : v < 218 + (60 + extra)
      · have hne : ∀ j, bandSlots extra line t hfit j ≠ (⟨v, hw⟩ : Fin (218 + (60 + extra))) := by
          intro j hj
          have hlt := bandSlots_val_lt extra line t hfit j
          rw [hj] at hlt
          exact absurd (show v < line + 2 + t from hlt) (by omega)
        have h := scratchOf_apply extra A s (⟨v, hw⟩ : Fin (218 + (60 + extra)))
        rw [hAdef, install_other _ _ _ _ hne,
          bank_scratch_apply stream count driver input witness s _
            (by show (278 : ℕ) ≤ v; omega)] at h
        rw [h]
        exact houter v hge
      · rw [scratchOf_high extra A s v hw]
        exact houter v hge

theorem scratchOf_low (extra : ℕ) (A : Fin (218 + (60 + extra)) → List Bool)
    (s : ℕ → List Bool) (v : ℕ) (hv : v < 218 + (60 + extra)) :
    scratchOf extra A s v = A ⟨v, hv⟩ := by
  unfold NearCubicWires.RepairSource.CloseoutFinal.C10SupplierCountStage.scratchOf
  rw [dif_pos hv]

theorem round_exit_off_band (extra total line t : ℕ) {r : ℕ}
    (slots : Fin r → Fin (218 + (60 + extra)))
    (hlow : ∀ j, line + 2 ≤ (slots j).val) (hhigh : ∀ j, (slots j).val < line + 2 + t)
    (stream count driver input witness : List Bool) (s : ℕ → List Bool)
    (B : Fin (218 + (60 + extra)) → List Bool)
    (hframe : ∀ i : Fin (218 + (60 + extra)), (∀ j, slots j ≠ i) →
      B i = install slots (bank stream count driver input witness s) (fun _ : Fin r => []) i)
    (v : ℕ) (hv : 278 ≤ v) (hout : v < line + 2 ∨ line + 2 + t ≤ v) :
    scratchOf extra (fun i => ZeroPadding.pad
      (CloseoutFinalC10BandRecycle.bandCap slots total i) (B i)) s v = s v := by
  by_cases hw : v < 218 + (60 + extra)
  · have hne : ∀ j, slots j ≠ (⟨v, hw⟩ : Fin (218 + (60 + extra))) := by
      intro j hj
      have h1 := hlow j
      have h2 := hhigh j
      rw [hj] at h1 h2
      have hv1 : line + 2 ≤ v := h1
      have hv2 : v < line + 2 + t := h2
      omega
    rw [scratchOf_low extra _ s v hw]
    show ZeroPadding.pad (CloseoutFinalC10BandRecycle.bandCap slots total ⟨v, hw⟩)
      (B ⟨v, hw⟩) = s v
    rw [CloseoutFinalC10BandRecycle.exit_off_slots slots total B _ hne, hframe _ hne,
      CloseoutFinalC10BandRecycle.blank_off_slots slots _ _ hne,
      bank_scratch_apply stream count driver input witness s _ (show (278 : ℕ) ≤ v from hv)]
  · rw [scratchOf_high extra _ s v hw]

/-! ## §5  Round then clear, at the budget that makes it a constant factor -/

theorem clear_budget (cost : ℕ) : cost + 1 + (2 * (cost + 1) + 4) = 3 * cost + 7 := by omega

/-- **ONE ROUND, THEN THE CLEAR, AND THE INVARIANT IS BACK.**

The hypothesis is any round step between two real banks -- the six record ports
may change, which is what `Rounds`
(`Proof/CaseAnalysis/FinalSupplierCountStage.lean`) needs of the body.  The
conclusion is a single `Step` of a single machine at a single fuel, with the
entry invariant re-established at the exit.  `hb` is not assumed: it is derived
from the round's own fuel through `band_length_after_round`
(`Proof/CaseAnalysis/FinalBandRecycle.lean`). -/
theorem round_clear_seq (extra total line t cost : ℕ) (hline : 278 ≤ line)
    (hfit : line + 2 + t ≤ 218 + (60 + extra)) (hcost : cost + 1 ≤ total)
    {bs : ℕ} (body : Machine (218 + (60 + extra)) bs)
    (stream count driver stream' count' driver' input witness : List Bool)
    (s s' : ℕ → List Bool) (hs : BandReady total line s) (hconf : Confined line t s s')
    (hround : Step body cost (fun _ => 0) (bank stream count driver input witness s)
      (fun _ => 0) (bank stream' count' driver' input witness s')) :
    ∃ s'' : ℕ → List Bool, BandReady total line s'' ∧
      Step (Composition.machine body
          (RecoveryFocus.machine (bandSlots extra line t hfit)
            (RecoveryScratchErase.resetMachine t)))
        (cost + 1 + (2 * total + 4)) (fun _ => 0)
        (bank stream count driver input witness s) (fun _ => 0)
        (bank stream' count' driver' input witness s'') := by
  obtain ⟨hd, hl, hz⟩ := hs
  obtain ⟨cd, cl, co⟩ := hconf
  have hout : ∀ v, line + 2 + t ≤ v → s' v = List.replicate total false := by
    intro v hv
    rw [co v hv]
    exact hz v (by omega)
  have hb : ∀ i : Fin t, (s' (line + 2 + i.val)).length ≤ total := by
    intro i
    have hidx : line + 2 + i.val < 218 + (60 + extra) := by have := i.isLt; omega
    have hentry : (bank stream count driver input witness s
        (⟨line + 2 + i.val, hidx⟩ : Fin (218 + (60 + extra)))).length ≤ total := by
      rw [bank_scratch_apply stream count driver input witness s _
          (by show (278 : ℕ) ≤ line + 2 + i.val; omega),
        hz (line + 2 + i.val) (by omega), List.length_replicate]
    have hstep := CloseoutFinalC10BandRecycle.band_length_after_round body cost total hround
      hcost (⟨line + 2 + i.val, hidx⟩ : Fin (218 + (60 + extra))) rfl hentry
    rwa [bank_scratch_apply stream' count' driver' input witness s' _
      (by show (278 : ℕ) ≤ line + 2 + i.val; omega)] at hstep
  have hclear := clear_bank_dock extra total line t hline hfit stream' count' driver' input
    witness s' hb (by rw [cd]; exact hd) (by rw [cl]; exact hl)
  exact ⟨_, bandReady_of_clear extra total line t hline hfit stream' count' driver' input
    witness s' hout, hround.seq hclear⟩

theorem round_clear_at_cost (extra line t cost : ℕ) (hline : 278 ≤ line)
    (hfit : line + 2 + t ≤ 218 + (60 + extra))
    {bs : ℕ} (body : Machine (218 + (60 + extra)) bs)
    (stream count driver stream' count' driver' input witness : List Bool)
    (s s' : ℕ → List Bool) (hs : BandReady (cost + 1) line s)
    (hconf : Confined line t s s')
    (hround : Step body cost (fun _ => 0) (bank stream count driver input witness s)
      (fun _ => 0) (bank stream' count' driver' input witness s')) :
    ∃ s'' : ℕ → List Bool, BandReady (cost + 1) line s'' ∧
      Step (Composition.machine body
          (RecoveryFocus.machine (bandSlots extra line t hfit)
            (RecoveryScratchErase.resetMachine t)))
        (3 * cost + 7) (fun _ => 0)
        (bank stream count driver input witness s) (fun _ => 0)
        (bank stream' count' driver' input witness s'') := by
  obtain ⟨s'', hready, hstep⟩ := round_clear_seq extra (cost + 1) line t cost hline hfit
    (Nat.le_refl _) body stream count driver stream' count' driver' input witness s s'
    hs hconf hround
  exact ⟨s'', hready, by rwa [clear_budget cost] at hstep⟩

/-- **BANDSIZE'S ROUND STEP AND THIS CLEAR, COMPOSED.**

`hstep` is what the docked-engine library hands a builder: a `Step` out of the
FICTIONAL bank whose round slots are literally `[]`, which `blank_at_slots`
(`Proof/CaseAnalysis/FinalBandRecycle.lean`) supplies with no hypothesis on the
bank.  `round_step_of_zeroBand` (`:277`) turns that into a real round step over
the recycled band; this module's clear then puts the band back.  The result is
ONE `Step` of ONE machine at ONE fuel between two real banks, with the entry
invariant re-established -- the shape `Rounds`
(`Proof/CaseAnalysis/FinalSupplierCountStage.lean`) asks of a round body.

The only demand on the round is geometric: its slots lie inside the clear's
window `[line+2, line+2+t)`.  Nothing here depends on the round index. -/
theorem zeroBand_round_then_clear (extra total line t cost : ℕ) (hline : 278 ≤ line)
    (hfit : line + 2 + t ≤ 218 + (60 + extra)) (hcost : cost + 1 ≤ total)
    {bs r : ℕ} (body : Machine (218 + (60 + extra)) bs)
    (slots : Fin r → Fin (218 + (60 + extra))) (hinj : Function.Injective slots)
    (hlow : ∀ j, line + 2 ≤ (slots j).val) (hhigh : ∀ j, (slots j).val < line + 2 + t)
    (stream count driver input witness : List Bool) (s : ℕ → List Bool)
    (hs : BandReady total line s)
    (H' : Fin (218 + (60 + extra)) → ℕ) (B : Fin (218 + (60 + extra)) → List Bool)
    (hstep : Step body cost (fun _ => 0)
      (install slots (bank stream count driver input witness s) (fun _ : Fin r => [])) H' B)
    (hzero : ∀ i, H' i = 0)
    (hframe : ∀ i : Fin (218 + (60 + extra)), (∀ j, slots j ≠ i) →
      B i = install slots (bank stream count driver input witness s)
        (fun _ : Fin r => []) i) :
    ∃ s'' : ℕ → List Bool, BandReady total line s'' ∧
      Step (Composition.machine body
          (RecoveryFocus.machine (bandSlots extra line t hfit)
            (RecoveryScratchErase.resetMachine t)))
        (cost + 1 + (2 * total + 4)) (fun _ => 0)
        (bank stream count driver input witness s) (fun _ => 0)
        (bank stream count driver input witness s'') := by
  have hround := CloseoutFinalC10BandRecycle.round_step_of_zeroBand extra total (line + 2) cost
    (by omega) body slots hinj hlow stream count driver input witness s hs.2.2 H' B hstep hzero
    hframe
  refine round_clear_seq extra total line t cost hline hfit hcost body stream count driver
    stream count driver input witness s _ hs ⟨?_, ?_, ?_⟩ hround
  · exact round_exit_off_band extra total line t slots hlow hhigh stream count driver input
      witness s B hframe line (by omega) (Or.inl (by omega))
  · exact round_exit_off_band extra total line t slots hlow hhigh stream count driver input
      witness s B hframe (line + 1) (by omega) (Or.inl (by omega))
  · intro v hv
    exact round_exit_off_band extra total line t slots hlow hhigh stream count driver input
      witness s B hframe v (by omega) (Or.inr hv)

end NearCubicWires.RepairOrdinary.CloseoutFinalC10BandClearDock
