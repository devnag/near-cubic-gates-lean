import Proof.CaseAnalysis.RowsCircuitEntry

/-! One complete cold preparation run at the final circuit ABI. The
existing native prefix/cursor survives allocation and canonical framing;
the same top field is copied into the reusable checked-gate workspace. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitColdEntry
open LocalBitMultitape RecoveryRootRound RecoveryExecution CloseoutRowsGatePairHeads CloseoutRowsCircuit
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem untouched (i : Fin 1703) (hi : i.val<639 ∨ i.val=1674 ∨
    (1688 ≤ i.val ∧ i.val ≤ 1690) ∨ i.val=1693 ∨ i.val=1698 ∨ i.val=1699) :
    ∀ j,CloseoutRowsCircuitAllocate.slots j≠i:=by
  intro j h
  have hv:=congrArg (fun k : Fin 1703=>k.val) h
  revert hv
  refine Fin.addCases (m:=1054) (n:=2) ?_ ?_ j
  · intro a hv;rw [CloseoutRowsCircuitAllocate.slots_old] at hv
    revert hv
    refine Fin.addCases (m:=1048) (n:=6) ?_ ?_ a
    · intro b hv;rw [CloseoutRowsCircuitAllocate.scratch_old] at hv
      have hb:=CloseoutRowsCircuitAllocate.gate_range b;omega
    · intro b hv;rw [CloseoutRowsCircuitAllocate.scratch_new] at hv
      fin_cases b <;> simp [CloseoutRowsCircuitAllocate.extra] at hv <;> omega
  · intro a hv;rw [CloseoutRowsCircuitAllocate.slots_new] at hv
    fin_cases a
    · change 1694=i.val at hv;omega
    · change 1695=i.val at hv;omega

theorem allocated_other (cap core W L : ℕ) (bits out : List Bool) (i : Fin 1703)
    (hi : ∀ j,CloseoutRowsCircuitAllocate.slots j≠i) :
    allocated cap core W L bits out i=input cap core W L bits out i:=install_other _ _ _ _ hi
theorem seeded_other (cap core W L : ℕ) (bits out : List Bool) (i : Fin 1703)
    (hi : ∀ j,seedSlots j≠i) : seeded cap core W L bits out i=allocated cap core W L bits out i:=
  install_other _ _ _ _ hi
theorem framed_other (cap core W L : ℕ) (bits out : List Bool) (bank : Fin 639→List Bool)
    (i : Fin 1703) (hi : 639 ≤ i.val) : framed cap core W L bits out bank i=seeded cap core W L bits out i:=
  install_other _ _ _ _ (by
    intro j h;have hv:=congrArg (fun k : Fin 1703=>k.val) h
    change j.val=i.val at hv;omega)

theorem seed_run (cap core W L : ℕ) (bits out : List Bool) :
    ReadyAt seed 1 (heads out) (allocated cap core W L bits out) (seeded cap core W L bits out):=by
  have hi:∀ i,allocated cap core W L bits out (seedSlots i)=seedInput cap i:=by
    intro i;fin_cases i
    · exact (allocated_other _ _ _ _ _ _ 0 (untouched 0 (by decide))).trans rfl
    · exact (allocated_other _ _ _ _ _ _ 1693 (untouched 1693 (by decide))).trans rfl
    · have h:=allocated_scratch cap core W L bits out ((3 : Fin 6).natAdd 1048)
      rw [CloseoutRowsCircuitAllocate.scratch_new] at h
      exact h
  obtain ⟨r,hr,rh,rt,rs⟩:=(seed_ready cap).focus_at seedSlots (by decide) (heads out)
    (allocated cap core W L bits out) hi (by intro i;fin_cases i <;> rfl)
  exact ⟨r,hr,rt,rh,rs⟩

theorem seeded_prefix (cap core W L : ℕ) (bits out : List Bool) (i : Fin 639) :
    seeded cap core W L bits out (prefixSlots i)=CloseoutRowsCircuitPrefix.input bits i:=by
  rw [prefix_input]
  by_cases hi:i.val=0
  · have he:i=0:=Fin.ext hi;subst i
    exact install_slot seedSlots (by decide) _ _ 0
  · rw [if_neg hi,seeded_other _ _ _ _ _ _ _ (by
      intro j h;have hv:=congrArg (fun k : Fin 1703=>k.val) h
      fin_cases j
      · change 0=i.val at hv;omega
      · change 1693=i.val at hv;omega
      · change 1697=i.val at hv;omega),allocated_old]
    change (if i.val=1 then frame bits else if i.val=1674 then UnaryTemplate.tape core else
      if i.val=1694 then List.replicate cap true else if i.val=1698 then List.replicate W true else
        if i.val=1699 then List.replicate L true else [])=_
    simp only [if_neg (show i.val≠1674 by omega),if_neg (show i.val≠1694 by omega),
      if_neg (show i.val≠1698 by omega),if_neg (show i.val≠1699 by omega)]

private theorem compose {t a b : ℕ} (p : Machine t a) (q : Machine t b) (fp fq : ℕ)
    (H : Fin t→ℕ) (A B C : Fin t→List Bool) (hp : ReadyAt p fp H A B) (hq : ReadyAt q fq H B C) :
    ReadyAt (Composition.machine p q) (fp+1+fq) H A C:=by
  obtain ⟨r,hr,rt,rh,rs⟩:=hp
  obtain ⟨s,hs,st,sh,ss⟩:=hq
  have he:Composition.restart r.final q.start=RecoveryCalls.restarted q H B:=by
    apply configuration_ext
    · rfl
    · exact rh
    · exact rt
  rw [←he] at hs
  refine ⟨Composition.joinedReceipt r s,Composition.run_join p q _ _ _ r s hr hs,st,sh,?_⟩
  change r.steps+1+s.steps ≤ fp+1+fq
  omega

theorem load_run (cap core W L : ℕ) (bits out : List Bool) (bank : Fin 639→List Bool)
    (hbank : bank 158=frame (CloseoutRowsCircuitHeader.codeWord bits 3))
    (hin : 2*bits.length+1 ≤ cap) :
    ReadyAt load (2*cap+4) (heads out) (framed cap core W L bits out bank) (output cap core W L bits out bank):=by
  have hlen:(frame (CloseoutRowsCircuitHeader.codeWord bits 3)).length ≤ cap:=by
    rw [frame_length]
    have hl:(CloseoutRowsCircuitHeader.codeWord bits 3).length=bits.length:=
      (RecoveryFixedUnpair.word_lengths _).1.trans (CompetitorWitnessTriple.word_length bits _)
    rw [hl];exact hin
  have hh:∀ i,heads out (topLoadSlots i)=0:=by intro i;fin_cases i <;> rfl
  have ht:∀ i,framed cap core W L bits out bank (topLoadSlots i)=
      CloseoutRowsMetadataCopy.input (frame (CloseoutRowsCircuitHeader.codeWord bits 3)) cap i:=by
    intro i;fin_cases i
    · exact (install_slot prefixSlots prefix_injective _ _ 158).trans hbank
    · rw [framed_other _ _ _ _ _ _ _ _ (by decide),seeded_other _ _ _ _ _ _ _ (by decide)]
      have h:=allocated_scratch cap core W L bits out ((1 : Fin 1048).castAdd 6)
      rw [CloseoutRowsCircuitAllocate.scratch_old] at h
      exact h
    · rw [framed_other _ _ _ _ _ _ _ _ (by decide),seeded_other _ _ _ _ _ _ _ (by decide)]
      exact install_slot CloseoutRowsCircuitAllocate.slots CloseoutRowsCircuitAllocate.slots_injective _ _ 1054
    · rw [framed_other _ _ _ _ _ _ _ _ (by decide),seeded_other _ _ _ _ _ _ _ (by decide)]
      have h:=install_slot CloseoutRowsCircuitAllocate.slots CloseoutRowsCircuitAllocate.slots_injective
        (input cap core W L bits out) (PCPTraversal.clearedLocal 1054 cap 0) 1055
      change allocated cap core W L bits out 1695=
        PCPTraversal.clearedLocal 1054 cap 0 ((0 : Fin 1).natAdd 1055) at h
      change allocated cap core W L bits out 1695=List.replicate (cap+1) false
      simpa only [PCPTraversal.clearedLocal,Fin.addCases_right,Nat.max_eq_right (Nat.zero_le _)] using h
  obtain ⟨r,hr,rh,rt,rs⟩:=CloseoutRowsCircuitCopy.copy_focus topLoadSlots (by decide) cap
    (frame (CloseoutRowsCircuitHeader.codeWord bits 3)) hlen (heads out) (framed cap core W L bits out bank) hh ht
  exact ⟨r,hr,rt,rh,rs.le⟩

theorem cold_run (threshold : Bool) (cap core W L : ℕ) (bits out : List Bool)
    (hin : 2*bits.length+1 ≤ cap) : ∃ bank,
    ReadyAt (machine threshold) (budget cap bits) (heads out) (input cap core W L bits out)
      (output cap core W L bits out bank) ∧
      bank 158=frame (CloseoutRowsCircuitHeader.codeWord bits 3) ∧
      bank 297=PCPPNativeCanonicalWalk.atomStream (CloseoutRowsCircuitHeader.codeWord bits 2).length
        (PCPPNativeCanonicalTree.tree (RadixSemantics.value (CloseoutRowsCircuitHeader.codeWord bits 2))).atoms ∧
      bank 622=List.replicate (CloseoutRowsCircuitCount.count (CloseoutRowsCircuitHeader.codeWord bits 2)) true ∧
      bank 624=UnaryTemplate.tape (CloseoutRowsCircuitCount.count (CloseoutRowsCircuitHeader.codeWord bits 2)) ∧
      (readTapeBit (bank 638) 0=true ↔ CloseoutRowsCircuitPrefix.valid threshold bits):=by
  have initial:=compose CloseoutRowsCircuitAllocate.machine seed _ _ (heads out) _ _ _
    (allocated_run cap core W L bits out) (seed_run cap core W L bits out)
  obtain ⟨bank,run,top,stream,count,template,flag⟩:=CloseoutRowsCircuitPrefix.prefix_run threshold bits
  obtain ⟨r,hr,rh,rt,rs⟩:=run.focus_at prefixSlots prefix_injective (heads out)
    (seeded cap core W L bits out) (seeded_prefix cap core W L bits out) (by
      intro i
      change (if (prefixSlots i)=1688 then out.length else if (prefixSlots i).val=1674 then 1 else 0)=0
      have hi:i.val<639:=i.isLt
      simp only [prefixSlots,Fin.val_castAdd]
      split_ifs <;> first | rfl | (rename_i he;have hv:=congrArg (fun k : Fin 1703=>k.val) he;change i.val=1688 at hv;omega) | omega)
  have prefixReady:ReadyAt (prefixMachine threshold) (CloseoutRowsCircuitPrefix.budget bits) (heads out)
      (seeded cap core W L bits out) (framed cap core W L bits out bank):=⟨r,hr,rt,rh,rs⟩
  have joined:=compose first (prefixMachine threshold) _ _ (heads out) _ _ _ initial prefixReady
  have all:=compose (second threshold) load _ _ (heads out) _ _ _ joined
    (load_run cap core W L bits out bank top hin)
  have hf:((2*cap+4+1+1)+1+CloseoutRowsCircuitPrefix.budget bits)+1+(2*cap+4)=budget cap bits:=by
    unfold budget;omega
  rw [hf] at all
  exact ⟨bank,all,top,stream,count,template,flag⟩

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitColdEntry
