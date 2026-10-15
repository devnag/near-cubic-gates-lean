import Proof.CaseAnalysis.WitnessTermChoice

/-! The counted term invariant uses the already-agreed circuit ports.
Private tapes have one common paid allocation; the actual source-domain,
mode caps and native logical output are the only retained circuit data. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.TermEnvironment
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def heads (native : List Bool) (i : Fin 1705) : ℕ :=
  if i.val=1674 then 1 else if i.val=1688 then native.length else 0
def tapes (H core W L : ℕ) (native : List Bool) (i : Fin 1705) : List Bool :=
  if i.val=1674 then UnaryTemplate.tape core else if i.val=1688 then native
  else if i.val=1698 then List.replicate W true else if i.val=1699 then List.replicate L true
  else if i.val=1703 then List.replicate H true else if i.val=1704 then List.replicate (H+1) false
  else List.replicate H false

theorem private_covers (j : Fin 1703) (hj : ¬TermCircuitReset.retained j) :
    ∃ i : Fin 1697,TermCircuitReset.privateSlot i=j := by
  let n := if j.val<1 then j.val else if j.val<1674 then j.val-1 else
    if j.val<1688 then j.val-2 else if j.val<1694 then j.val-3 else
    if j.val<1698 then j.val-4 else j.val-6
  have hnot := hj
  dsimp only [TermCircuitReset.retained] at hnot
  have hn : n<1697 := by dsimp only [n];split_ifs <;> omega
  refine ⟨⟨n,hn⟩,?_⟩
  apply Fin.ext
  dsimp only [TermCircuitReset.privateSlot,n]
  split_ifs <;> omega

theorem private_tapes (H core W L : ℕ) (native : List Bool) (i : Fin 1697) :
    tapes H core W L native ((TermCircuitReset.privateSlot i).castAdd 2)=List.replicate H false := by
  have h:=TermCircuitReset.private_not_retained i
  have hb:=(TermCircuitReset.privateSlot i).isLt
  dsimp only [TermCircuitReset.retained] at h
  simp only [tapes,Fin.val_castAdd,if_neg (show (TermCircuitReset.privateSlot i).val≠1674 by omega),
    if_neg (show (TermCircuitReset.privateSlot i).val≠1688 by omega),
    if_neg (show (TermCircuitReset.privateSlot i).val≠1698 by omega),
    if_neg (show (TermCircuitReset.privateSlot i).val≠1699 by omega),
    if_neg (show (TermCircuitReset.privateSlot i).val≠1703 by omega),
    if_neg (show (TermCircuitReset.privateSlot i).val≠1704 by omega)]

theorem reset_heads (position : ℕ) (out native : List Bool) (i : Fin 1699) :
    TermRound.heads position out (heads native) (TermCircuitReset.slots i)=0 := by
  refine Fin.addCases (m:=1697) (n:=2) ?_ ?_ i
  · intro j
    rw [TermCircuitReset.slots_old]
    have he : TermCircuitReset.scratch j=((TermCircuitReset.privateSlot j).castAdd 2).natAdd 827 := Fin.ext rfl
    rw [he]
    have h:=TermCircuitReset.private_not_retained j
    dsimp only [TermCircuitReset.retained] at h
    simp only [TermRound.heads,Fin.addCases_right,heads,Fin.val_castAdd,
      if_neg (show (TermCircuitReset.privateSlot j).val≠1674 by omega),
      if_neg (show (TermCircuitReset.privateSlot j).val≠1688 by omega)]
  · intro j
    rw [TermCircuitReset.slots_new]
    fin_cases j <;> rfl

theorem restored (H core W L : ℕ) (native : List Bool) (saved final : Fin 1705 → List Bool)
    (hpublic : ∀ i : Fin 1703,TermCircuitReset.retained i →
      saved (i.castAdd 2)=tapes H core W L native (i.castAdd 2))
    (hprivate : ∀ i,final ((TermCircuitReset.privateSlot i).castAdd 2)=List.replicate H false)
    (hdriver : final 1703=List.replicate H true) (hlog : final 1704=List.replicate (H+1) false)
    (hkeep : ∀ i,(∀ j,TermCircuitReset.slots j≠i.natAdd 827) → final i=saved i) :
    final=tapes H core W L native := by
  funext i
  refine Fin.addCases (m:=1703) (n:=2) ?_ ?_ i
  · intro j
    by_cases hj : TermCircuitReset.retained j
    · exact (hkeep (j.castAdd 2) (TermCircuitReset.retained_outside j hj)).trans (hpublic j hj)
    · obtain ⟨k,hk⟩ := private_covers j hj
      rw [←hk,hprivate]
      exact (private_tapes H core W L native k).symm
  · intro j
    fin_cases j
    · exact hdriver
    · exact hlog

end NearCubicWires.RepairOrdinary.CloseoutWitness.TermEnvironment
