import Proof.CaseAnalysis.WitnessNodeReset
import Proof.PCP.PCPSerializerReuseReset

/-! The reusable node workspace has one load target, four retained bounds,
and one live descriptor. All its other cells start in charged zero padding. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.NodeReady
open LocalBitMultitape RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem entry_old (cap w : ℕ) (left right bits out : List Bool) (i : Fin 748) :
    (entry cap w left right bits out).tapes (i.castAdd 1)=
      ZeroPadding.pad (pads cap i) ((NodeBody.entry w left right bits [] out).tapes i):=by
  simp only [entry,ZeroPadding.config,Rewind.recording,Rewind.config,
    Rewind.Workspace.capacities,Fin.addCases_left,ZeroPadding.pad_zero]

theorem entry_clock (cap w : ℕ) (left right bits out : List Bool) :
    (entry cap w left right bits out).tapes 748=List.replicate cap false:=by
  change ZeroPadding.pad cap ([] : List Bool)=_
  simp [ZeroPadding.pad]

theorem entry_source (cap w : ℕ) (left right bits out : List Bool) :
    (entry cap w left right bits out).tapes 1=ZeroPadding.pad cap (frame bits):=by
  change (entry cap w left right bits out).tapes ((1 : Fin 748).castAdd 1)=_
  rw [entry_old]
  rfl

theorem entry_output (cap w : ℕ) (left right bits out : List Bool) :
    (entry cap w left right bits out).tapes 747=out:=by
  change (entry cap w left right bits out).tapes ((747 : Fin 748).castAdd 1)=_
  rw [entry_old]
  change ZeroPadding.pad 0 out=out
  exact ZeroPadding.pad_zero out

theorem entry_common (cap w : ℕ) (left right bits out : List Bool) (i : Fin 4) :
    (entry cap w left right bits out).tapes ((NodeGuard.common i).castAdd 3)=
      ZeroPadding.pad cap (NodeGuard.shared w left right i):=by
  change (entry cap w left right bits out).tapes (((NodeGuard.common i).castAdd 2).castAdd 1)=_
  rw [entry_old,pads,if_neg (by fin_cases i <;> decide)]
  simp only [NodeBody.entry,Composition.leftConfig,TapeEmbedding.config,Fin.addCases_left,
    initialConfiguration,NodeGuard.input,NodeGuard.base_common]

theorem entry_heads (cap w : ℕ) (left right bits out : List Bool) (i : Fin 749) :
    (entry cap w left right bits out).heads i=if i=747 then out.length else 0:=by
  refine Fin.addCases (m:=748) (n:=1) ?_ ?_ i
  · intro j
    simp only [entry,ZeroPadding.config,Rewind.recording,Rewind.config,Fin.addCases_left]
    by_cases hj:j=747
    · subst j
      rfl
    · rw [NodeBody.entry_heads _ _ _ _ _ _ j hj,if_neg (by
        intro he
        apply hj
        exact Fin.ext (congrArg (fun i : Fin 749=>i.val) he))]
  · intro j
    have hj:j=0:=Fin.eq_zero j
    subst j
    rfl

theorem entry_bits_other (cap w : ℕ) (left right bits nextBits out : List Bool)
    (i : Fin 749) (hi : i≠1) :
    (entry cap w left right bits out).tapes i=(entry cap w left right nextBits out).tapes i:=by
  revert hi
  refine Fin.addCases (m:=748) (n:=1) ?_ ?_ i
  · intro j hi
    rw [entry_old,entry_old]
    apply congrArg
    revert hi
    refine Fin.addCases (m:=746) (n:=2) ?_ ?_ j
    · intro k hi
      simp only [NodeBody.entry,Composition.leftConfig,TapeEmbedding.config,Fin.addCases_left,initialConfiguration,
        NodeGuard.input,NodeGuard.base]
      revert hi
      refine Fin.addCases (m:=668) (n:=78) ?_ ?_ k
      · intro a hi
        simp only [Fin.addCases_left,NodeFields.input]
        revert hi
        refine Fin.addCases (m:=122) (n:=546) ?_ ?_ a
        · intro b hi
          have h1:b.val≠1:=by intro h;apply hi;exact Fin.ext h
          simp only [Fin.addCases_left,CompetitorWitnessTriple.input,h1,if_false]
        · intro b _
          simp only [Fin.addCases_right]
      · intro a _
        simp only [Fin.addCases_right]
    · intro k _
      simp only [NodeBody.entry,Composition.leftConfig,TapeEmbedding.config,Fin.addCases_right]
  · intro j _
    have hj:j=0:=Fin.eq_zero j
    subst j
    rw [show (0 : Fin 1).natAdd 748=(748 : Fin 749) by decide]
    rw [entry_clock,entry_clock]

theorem empty_raw (w : ℕ) (left right out : List Bool) (i : Fin 748)
    (hi : i≠747) (hc : ∀ j : Fin 4,(NodeGuard.common j).castAdd 2≠i) :
    (NodeBody.entry w left right [] [] out).tapes i=[] ∨
      (NodeBody.entry w left right [] [] out).tapes i=[false]:=by
  revert hi hc
  refine Fin.addCases (m:=746) (n:=2) ?_ ?_ i
  · intro j hi hc
    simp only [NodeBody.entry,Composition.leftConfig,TapeEmbedding.config,Fin.addCases_left,
      initialConfiguration,NodeGuard.input,NodeGuard.base]
    revert hi hc
    refine Fin.addCases (m:=668) (n:=78) ?_ ?_ j
    · intro k _ _
      simp only [Fin.addCases_left,NodeFields.input]
      refine Fin.addCases (m:=122) (n:=546) ?_ ?_ k
      · intro a
        simp only [Fin.addCases_left,CompetitorWitnessTriple.input]
        split_ifs <;> first | exact Or.inl rfl | exact Or.inr rfl
      · intro a
        simp only [Fin.addCases_right,true_or]
    · intro k hi hc
      simp only [Fin.addCases_right]
      revert hi hc
      refine Fin.addCases (m:=4) (n:=74) ?_ ?_ k
      · intro a _ hc
        exact False.elim (hc a (Fin.ext rfl))
      · intro a _ _
        simp only [Fin.addCases_right,true_or]
  · intro j hi _
    fin_cases j
    · exact Or.inl rfl
    · exact False.elim (hi rfl)

theorem entry_blank (cap w : ℕ) (left right out : List Bool) (hcap : 1 ≤ cap) (i : Fin 749)
    (hi : i≠747) (hc : ∀ j : Fin 4,(NodeGuard.common j).castAdd 3≠i) :
    (entry cap w left right [] out).tapes i=List.replicate cap false:=by
  revert hi hc
  refine Fin.addCases (m:=748) (n:=1) ?_ ?_ i
  · intro j hi hc
    have hj:j≠747:=by intro h;subst j;exact hi rfl
    have hcommon:∀ a : Fin 4,(NodeGuard.common a).castAdd 2≠j:=by
      intro a he
      apply hc a
      exact Fin.ext (congrArg (fun i : Fin 748=>i.val) he)
    rw [entry_old,pads,if_neg hj]
    rcases empty_raw w left right out j hj hcommon with h|h
    · rw [h]
      simp [ZeroPadding.pad]
    · rw [h]
      exact PCPSerializerReuse.pad_zeros cap 1 hcap
  · intro j _ _
    have hj:j=0:=Fin.eq_zero j
    subst j
    rw [show (0 : Fin 1).natAdd 748=(748 : Fin 749) by decide]
    exact entry_clock cap w left right [] out

end NearCubicWires.RepairOrdinary.CloseoutWitness.NodeReady
