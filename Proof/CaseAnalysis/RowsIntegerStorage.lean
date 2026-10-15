import Proof.CaseAnalysis.CloseoutRowsIntegerReady

/-! The exact reusable integer bank has one framed input and one live
output. Every other cell is the same paid local zero workspace. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsIntegerReady
open LocalBitMultitape RadixSemantics CloseoutWitness
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem raw_tape (bits out : List Bool) (i : Fin 214) :
    (CloseoutRowsCheckedInteger.entry bits [] out).tapes i=
      if i=213 then out else if i=0 then frame bits else []:=by
  fin_cases i <;> rfl

theorem entry_old (w : ℕ) (bits out : List Bool) (i : Fin 214) :
    (entry w bits out).tapes (i.castAdd 1)=
      ZeroPadding.pad (PaddedReset.pads selected (capacity w) i)
        ((CloseoutRowsCheckedInteger.entry bits [] out).tapes i):=by
  simp only [entry,PaddedReset.entry,ZeroPadding.config,Rewind.recording,Rewind.config,
    Rewind.Workspace.capacities,Fin.addCases_left,ZeroPadding.pad_zero]

theorem padded_clock {t s : ℕ} (chosen : Fin t→Bool) (cap : ℕ) (c : Configuration t s) :
    (PaddedReset.entry chosen cap c).tapes ((0 : Fin 1).natAdd t)=List.replicate cap false:=by
  simp only [PaddedReset.entry,ZeroPadding.config,Rewind.recording,Rewind.config,
    Rewind.Workspace.capacities,Fin.addCases_right,List.replicate_zero]
  simp [ZeroPadding.pad]
theorem entry_clock (w : ℕ) (bits out : List Bool) :
    (entry w bits out).tapes 214=List.replicate (capacity w) false:=by
  have h:=padded_clock selected (capacity w) (CloseoutRowsCheckedInteger.entry bits [] out)
  simpa only [entry,show (0 : Fin 1).natAdd 214=(214 : Fin 215) by decide] using h
theorem entry_source (w : ℕ) (bits out : List Bool) :
    (entry w bits out).tapes 0=ZeroPadding.pad (capacity w) (frame bits):=by
  change (entry w bits out).tapes ((0 : Fin 214).castAdd 1)=_
  rw [entry_old,raw_tape]
  rfl
theorem entry_output (w : ℕ) (bits out : List Bool) :
    (entry w bits out).tapes 213=out:=by
  change (entry w bits out).tapes ((213 : Fin 214).castAdd 1)=_
  rw [entry_old,raw_tape]
  exact ZeroPadding.pad_zero out

theorem entry_heads (w : ℕ) (bits out : List Bool) (i : Fin 215) :
    (entry w bits out).heads i=if i=213 then out.length else 0:=by
  refine Fin.addCases (m:=214) (n:=1) ?_ ?_ i
  · intro j
    simp only [entry,PaddedReset.entry,ZeroPadding.config,Rewind.recording,Rewind.config,Fin.addCases_left]
    by_cases hj:j=213
    · subst j
      rfl
    · rw [raw_heads bits out j hj,if_neg (by
        intro he
        exact hj (Fin.ext (congrArg (fun i : Fin 215=>i.val) he)))]
  · intro j
    have hj:j=0:=Fin.eq_zero j
    subst j
    rfl

theorem entry_bits_other (w : ℕ) (bits next out : List Bool) (i : Fin 215) (hi : i≠0) :
    (entry w bits out).tapes i=(entry w next out).tapes i:=by
  revert hi
  refine Fin.addCases (m:=214) (n:=1) ?_ ?_ i
  · intro j hj
    rw [entry_old,entry_old,raw_tape,raw_tape]
    have h0:j≠0:=by intro he;subst j;exact hj rfl
    simp only [if_neg h0]
  · intro j _
    have hj:j=0:=Fin.eq_zero j
    subst j
    rw [show (0 : Fin 1).natAdd 214=(214 : Fin 215) by decide,entry_clock,entry_clock]

theorem capacity_positive (w : ℕ) : 1 ≤ capacity w:=by
  have hp:1 ≤ (w+1)^24:=Nat.one_le_pow _ _ (by omega)
  unfold capacity
  omega

theorem pad_empty_frame (cap : ℕ) (hcap : 1 ≤ cap) :
    ZeroPadding.pad cap (frame [])=List.replicate cap false:=by
  change ZeroPadding.pad cap (List.replicate 1 false)=_
  rw [Rewind.Workspace.pad_zeros,Nat.max_eq_left hcap]

theorem padded_blank_old {t s : ℕ} (chosen : Fin t→Bool) (cap : ℕ) (c : Configuration t s)
    (i : Fin t) (hi : chosen i=true) (hcap : 1 ≤ cap)
    (ht : c.tapes i=[] ∨ c.tapes i=frame []) :
    (PaddedReset.entry chosen cap c).tapes (i.castAdd 1)=List.replicate cap false:=by
  simp only [PaddedReset.entry,ZeroPadding.config,Rewind.recording,Rewind.config,
    Rewind.Workspace.capacities,Fin.addCases_left,ZeroPadding.pad_zero,PaddedReset.pads,hi,if_true]
  rcases ht with h|h
  · rw [h]
    simp [ZeroPadding.pad]
  · rw [h]
    exact pad_empty_frame cap hcap

theorem entry_blank_old (w : ℕ) (out : List Bool) (j : Fin 214) (h : j≠213) :
    (entry w [] out).tapes (j.castAdd 1)=List.replicate (capacity w) false:=by
  apply padded_blank_old selected (capacity w) (CloseoutRowsCheckedInteger.entry [] [] out) j
    (decide_eq_true h) (capacity_positive w)
  rw [raw_tape,if_neg h]
  split_ifs <;> simp

theorem entry_blank (w : ℕ) (out : List Bool) (i : Fin 215) (hi : i≠213) :
    (entry w [] out).tapes i=List.replicate (capacity w) false:=by
  revert hi
  refine Fin.addCases (m:=214) (n:=1) ?_ ?_ i
  · intro j hj
    have h:j≠213:=by intro he;subst j;exact hj rfl
    exact entry_blank_old w out j h
  · intro j _
    have hj:j=0:=Fin.eq_zero j
    subst j
    rw [show (0 : Fin 1).natAdd 214=(214 : Fin 215) by decide]
    exact entry_clock w [] out

end NearCubicWires.RepairOrdinary.CloseoutRowsIntegerReady
