import Proof.Circuits.DecompositionSignedPair

/-! Positive signed-atom tail: the physically parsed magnitude/count enter
the shared serializer, then the retained sign and actual framed result enter
the paid canonical pair adapter. No source constructor is called here. -/
namespace NearCubicWires.RepairOrdinary.DecompositionSignedTail
open LocalBitMultitape RepairRepresentation RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def pairSlots (j : Fin 41) : Fin 175 :=
  if j=0 then 6 else if j=1 then 85 else ⟨j.val+134,by omega⟩
theorem pair_injective : Function.Injective pairSlots := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [pairSlots] at hv
  split_ifs at hv <;> simp_all only [Fin.ext_iff,Fin.val_zero,Fin.val_one]
  all_goals omega
theorem pair_fresh (j : Fin 41) (h0 : j≠0) (h1 : j≠1) : 136 ≤ (pairSlots j).val := by
  have hj0 : j.val≠0 := fun h => h0 (Fin.ext h)
  have hj1 : j.val≠1 := fun h => h1 (Fin.ext h)
  simp only [pairSlots,h0,h1,ite_false]
  change 136 ≤ j.val+134
  omega
noncomputable def first := TapeEmbedding.machine 39 DecompositionMagnitudeSerializer.machine
noncomputable def last := RecoveryFocus.machine pairSlots DecompositionSignedPair.machine
noncomputable def machine := Composition.machine first last
noncomputable def entry (pre tail : List Bool) (z : ℤ) :=
  let c := TapeEmbedding.config (fun _ : Fin 39 => 0) (fun _ => [])
    (DecompositionMagnitudeSerializer.entry pre tail z)
  (⟨machine.start,c.heads,c.tapes⟩ : Configuration 175 _)
def budget (z : ℤ) := PCPTraversal.budget (3*natBitLength z.natAbs)+1+
  DecompositionSignedPair.budget (decide (z<0)) (CanonicalBinary.encodeNat z.natAbs).bits

theorem tail_run (pre tail : List Bool) (z : ℤ) (hz : 0<z.natAbs) :
    ∃ r,runFrom machine (budget z) (entry pre tail z)=some r ∧
      r.final.tapes 162=ZeroPadding.pad
        (2*PCPPair.width [decide (z<0)] (CanonicalBinary.encodeNat z.natAbs).bits+1)
        (frame (CanonicalBinary.encodeInt z).bits) ∧
      r.final.heads 162=0 ∧
      r.final.tapes 0=pre++intWord z++tail ∧
      r.final.heads 0=pre.length+(intWord z).length ∧ r.steps ≤ budget z := by
  let b := decide (z<0)
  let bits := (CanonicalBinary.encodeNat z.natAbs).bits
  let cap := PCPPairReusable.capacity (3*natBitLength z.natAbs)
  let suffix := List.replicate (cap-(frame bits).length) false
  obtain ⟨base,hb,b85,_,bh85,b0,bh0,b6,bh6,bs⟩ :=
    DecompositionMagnitudeSerializer.serialized_run pre tail z hz
  let prepared := TapeEmbedding.receipt (fun _ : Fin 39 => 0) (fun _ => []) base
  have hp := TapeEmbedding.run_embed DecompositionMagnitudeSerializer.machine
    (fun _ : Fin 39 => 0) (fun _ => []) _ _ base hb
  have oldT (j : Fin 136) : prepared.final.tapes (j.castAdd 39)=base.final.tapes j := by
    simp only [prepared,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases_left]
  have oldH (j : Fin 136) : prepared.final.heads (j.castAdd 39)=base.final.heads j := by
    simp only [prepared,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases_left]
  have freshT (j : Fin 175) (hj : 136 ≤ j.val) : prepared.final.tapes j=[] := by
    simp [prepared,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases,show ¬j.val<136 by omega]
  have freshH (j : Fin 175) (hj : 136 ≤ j.val) : prepared.final.heads j=0 := by
    simp [prepared,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases,show ¬j.val<136 by omega]
  have hpos : 0<Nat.pair (value [b]) (value bits) := by
    rw [DecompositionSignedPair.int_pair]
    have hn : CanonicalBinary.encodeInt z≠0 := by
      intro he
      have hz0 := (CanonicalBinary.encodeInt_eq_zero_iff z).mp he
      subst z
      contradiction
    omega
  obtain ⟨out,⟨pair,hpair,pt,ph,ps⟩,po⟩ := DecompositionSignedPair.pair_run b bits suffix hpos
  have ht (j : Fin 41) : prepared.final.tapes (pairSlots j)=DecompositionSignedPair.input b bits suffix j := by
    by_cases h0 : j=0
    · subst j
      exact (oldT 6).trans b6
    by_cases h1 : j=1
    · subst j
      exact (oldT 85).trans b85
    rw [freshT _ (pair_fresh j h0 h1)]
    simp only [DecompositionSignedPair.input,h0,h1,ite_false]
  have hh (j : Fin 41) : prepared.final.heads (pairSlots j)=0 := by
    by_cases h0 : j=0
    · subst j; exact (oldH 6).trans bh6
    by_cases h1 : j=1
    · subst j; exact (oldH 85).trans bh85
    exact freshH _ (pair_fresh j h0 h1)
  obtain ⟨focused,hf,ff,fs⟩ := RecoveryFocus.run_config pairSlots pair_injective
    DecompositionSignedPair.machine prepared.final.heads prepared.final.tapes _ _ pair hpair
  have hi : RecoveryFocus.config pairSlots prepared.final.heads prepared.final.tapes
      (initialConfiguration DecompositionSignedPair.machine (DecompositionSignedPair.input b bits suffix))=
      Composition.restart prepared.final last.start :=
    WilliamsSourceCrop.focus_same pairSlots prepared.final _ hh ht
  rw [hi] at hf
  have whole := Composition.run_join first last _ _ _ prepared focused hp hf
  have hn : RecoveryFocus.pick pairSlots (0 : Fin 175)=none := by
    have he : ¬∃ j,pairSlots j=(0 : Fin 175) := by
      rintro ⟨j,hj⟩
      have hv := congrArg Fin.val hj
      simp only [pairSlots] at hv
      split_ifs at hv <;> dsimp at hv <;> omega
    simp [RecoveryFocus.pick,he]
  refine ⟨Composition.joinedReceipt prepared focused,whole,?_,?_,?_,?_,?_⟩
  · change focused.final.tapes (pairSlots 28)=_
    rw [ff]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot pairSlots pair_injective,pt]
    rw [po,DecompositionSignedPair.int_pair]
  · change focused.final.heads (pairSlots 28)=0
    rw [ff]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot pairSlots pair_injective]
    exact ph 28
  · change focused.final.tapes 0=_
    rw [ff]
    simp only [RecoveryFocus.config,hn]
    exact (oldT 0).trans b0
  · change focused.final.heads 0=_
    rw [ff]
    simp only [RecoveryFocus.config,hn]
    exact (oldH 0).trans bh0
  · change base.steps+1+focused.steps ≤ _
    rw [fs]
    change base.steps+1+pair.steps ≤ PCPTraversal.budget (3*natBitLength z.natAbs)+1+
      DecompositionSignedPair.budget b bits
    omega

end NearCubicWires.RepairOrdinary.DecompositionSignedTail
