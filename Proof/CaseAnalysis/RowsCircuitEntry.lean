import Proof.CaseAnalysis.RowsCircuitAllocate

/-! Cold circuit entry with an existing native output prefix. Allocation,
literal seeds, the original canonical prefix and the top-field copy all
execute once while the append cursor and policy fields remain outside. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitColdEntry
open LocalBitMultitape RecoveryRootRound RecoveryExecution CloseoutRowsGatePairHeads CloseoutRowsCircuit
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def seedSlots : Fin 3→Fin 1703:=![0,1693,1697]
def seedInput (cap : ℕ) : Fin 3→List Bool:=![[],[],List.replicate cap false]
def seedOutput (cap : ℕ) : Fin 3→List Bool:=![[false],[true],ZeroPadding.pad cap [true]]
def seedWorker : Machine 3 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==1
  rule:=fun q _=>if q.val=0 then some ⟨1,![some false,some true,some true],fun _=>.stay⟩ else none
noncomputable def seed:=RecoveryFocus.machine seedSlots seedWorker
def heads (out : List Bool) (i : Fin 1703):=if i=1688 then out.length else CloseoutRowsCircuit.heads i
def input (cap core W L : ℕ) (bits out : List Bool) (i : Fin 1703):=
  if i=1688 then out else CloseoutRowsCircuit.input cap core W L bits i
noncomputable def allocated (cap core W L : ℕ) (bits out : List Bool):=
  install CloseoutRowsCircuitAllocate.slots (input cap core W L bits out) (PCPTraversal.clearedLocal 1054 cap 0)
noncomputable def seeded (cap core W L : ℕ) (bits out : List Bool):=
  install seedSlots (allocated cap core W L bits out) (seedOutput cap)
noncomputable def framed (cap core W L : ℕ) (bits out : List Bool) (bank : Fin 639→List Bool):=
  install prefixSlots (seeded cap core W L bits out) bank
noncomputable def output (cap core W L : ℕ) (bits out : List Bool) (bank : Fin 639→List Bool):=
  Function.update (framed cap core W L bits out bank) 640
    (ZeroPadding.pad cap (frame (CloseoutRowsCircuitHeader.codeWord bits 3)))
noncomputable def prefixMachine (threshold : Bool):=RecoveryFocus.machine prefixSlots (CloseoutRowsCircuitPrefix.machine threshold)
noncomputable def load:=RecoveryFocus.machine topLoadSlots RecoveryBoundedTapeCopy.machine
noncomputable def first:=Composition.machine CloseoutRowsCircuitAllocate.machine seed
noncomputable def second (threshold : Bool):=Composition.machine first (prefixMachine threshold)
noncomputable def machine (threshold : Bool):=Composition.machine (second threshold) load
def budget (cap : ℕ) (bits : List Bool):=4*cap+CloseoutRowsCircuitPrefix.budget bits+12

private theorem join {t a b : ℕ} (p : Machine t a) (q : Machine t b) (fp fq : ℕ)
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

theorem seed_ready (cap : ℕ) : ClockJoin.ReadyRun seedWorker 1 (seedInput cap) (seedOutput cap):=by
  let last : Configuration 3 2:=⟨1,fun _=>0,seedOutput cap⟩
  have hs:step seedWorker (initialConfiguration seedWorker (seedInput cap))=some last:=by
    apply congrArg some
    apply configuration_ext
    · rfl
    · rfl
    · funext i;fin_cases i
      · rfl
      · rfl
      · change writeTapeBit (List.replicate cap false) 0 true=ZeroPadding.pad cap [true]
        rw [show List.replicate cap false=ZeroPadding.pad cap [] by simp [ZeroPadding.pad],ZeroPadding.write_pad]
        rfl
  obtain ⟨r,hr,rf,rs⟩:=(Timed.single (by rfl) hs).run (by rfl)
  exact ⟨r,hr,by rw [rf],by intro i;rw [rf],rs.le⟩

theorem allocate_outside : ∀ j,CloseoutRowsCircuitAllocate.slots j≠(1688 : Fin 1703):=by
  intro j h
  revert h
  refine Fin.addCases (m:=1054) (n:=2) ?_ ?_ j
  · intro i h;rw [CloseoutRowsCircuitAllocate.slots_old] at h
    revert h
    refine Fin.addCases (m:=1048) (n:=6) ?_ ?_ i
    · intro k h;rw [CloseoutRowsCircuitAllocate.scratch_old] at h
      have hr:=CloseoutRowsCircuitAllocate.gate_range k
      have hv:=congrArg (fun z : Fin 1703=>z.val) h
      change _=1688 at hv;omega
    · intro k h;rw [CloseoutRowsCircuitAllocate.scratch_new] at h
      have hr:=CloseoutRowsCircuitAllocate.extra_range k
      have hv:=congrArg (fun z : Fin 1703=>z.val) h
      change _=1688 at hv;omega
  · intro i h;rw [CloseoutRowsCircuitAllocate.slots_new] at h
    fin_cases i <;> cases h

theorem allocated_run (cap core W L : ℕ) (bits out : List Bool) :
    ReadyAt CloseoutRowsCircuitAllocate.machine (2*cap+4) (heads out)
      (input cap core W L bits out) (allocated cap core W L bits out):=by
  have run:=RecoveryScratchErase.erase_ready cap 0 (fun _ : Fin 1054=>[]) (by intro i;exact Nat.zero_le _)
  have ht:∀ i : Fin 1056,CloseoutRowsCircuit.input cap core W L bits (CloseoutRowsCircuitAllocate.slots i)=
      (Fin.addCases (m:=1055) (n:=1) (motive:=fun _=>List Bool)
        (Fin.addCases (m:=1054) (n:=1) (motive:=fun _=>List Bool)
          (fun _=>[]) (fun _=>List.replicate cap true)) (fun _=>List.replicate 0 false)) i:=by
    intro i
    refine Fin.addCases (m:=1055) (n:=1) ?_ ?_ i
    · intro j
      refine Fin.addCases (m:=1054) (n:=1) ?_ ?_ j
      · intro k
        have hs:=CloseoutRowsCircuitAllocate.scratch_range k
        rw [show (k.castAdd 1).castAdd 1=k.castAdd 2 from Fin.ext rfl,CloseoutRowsCircuitAllocate.slots_old]
        rw [show k.castAdd 2=(k.castAdd 1).castAdd 1 from Fin.ext rfl]
        simp only [Fin.addCases_left,CloseoutRowsCircuit.input]
        split_ifs <;> first | rfl | omega
      · intro k;have hk:k=0:=Fin.eq_zero k;subst k;rfl
    · intro k;have hk:k=0:=Fin.eq_zero k;subst k;rfl
  obtain ⟨r,hr,rh,rt,rs⟩:=run.focus_at CloseoutRowsCircuitAllocate.slots CloseoutRowsCircuitAllocate.slots_injective
    (heads out) (input cap core W L bits out)
    (by intro i;rw [input,if_neg (allocate_outside i)];exact ht i) (by
      intro i;rw [heads,if_neg (allocate_outside i)]
      refine Fin.addCases (m:=1054) (n:=2) ?_ ?_ i
      · intro j
        rw [CloseoutRowsCircuitAllocate.slots_old]
        change (if (CloseoutRowsCircuitAllocate.scratch j).val=1674 then 1 else 0)=0
        rw [if_neg (CloseoutRowsCircuitAllocate.scratch_range j).2.1]
      · intro j;fin_cases j <;> rfl)
  exact ⟨r,hr,rt,rh,rs.le⟩

theorem allocated_old (cap core W L : ℕ) (bits out : List Bool) (i : Fin 639) :
    allocated cap core W L bits out (prefixSlots i)=CloseoutRowsCircuit.input cap core W L bits (prefixSlots i):=by
  rw [allocated,install_other _ _ _ _ (CloseoutRowsCircuitAllocate.prefix_outside i)]
  rw [input,if_neg (by intro h;have hv:=congrArg (fun k : Fin 1703=>k.val) h;change i.val=1688 at hv;omega)]
theorem allocated_scratch (cap core W L : ℕ) (bits out : List Bool) (i : Fin 1054) :
    allocated cap core W L bits out (CloseoutRowsCircuitAllocate.scratch i)=List.replicate cap false:=by
  have h:=install_slot CloseoutRowsCircuitAllocate.slots CloseoutRowsCircuitAllocate.slots_injective
    (input cap core W L bits out) (PCPTraversal.clearedLocal 1054 cap 0) (i.castAdd 2)
  rw [CloseoutRowsCircuitAllocate.slots_old] at h
  rw [show i.castAdd 2=(i.castAdd 1).castAdd 1 from Fin.ext rfl] at h
  simpa only [allocated,PCPTraversal.clearedLocal,Fin.addCases_left] using h

theorem prefix_input (bits : List Bool) (i : Fin 639) : CloseoutRowsCircuitPrefix.input bits i=
    if i.val=0 then [false] else if i.val=1 then frame bits else []:=by
  refine Fin.addCases (m:=268) (n:=371) ?_ ?_ i
  · intro j
    simp only [CloseoutRowsCircuitPrefix.input,Fin.addCases_left,Fin.val_castAdd]
    refine Fin.addCases (m:=242) (n:=26) ?_ ?_ j
    · intro k
      simp only [CloseoutRowsCircuitTagged.input,Fin.addCases_left,Fin.val_castAdd]
      refine Fin.addCases (m:=122) (n:=120) ?_ ?_ k
      · intro z
        simp only [CloseoutRowsCircuitHeader.input,Fin.addCases_left,Fin.val_castAdd,CompetitorWitnessTriple.input]
        rfl
      · intro z
        simp only [CloseoutRowsCircuitHeader.input,Fin.addCases_right,Fin.val_natAdd,
          if_neg (show 122+z.val≠0 by omega),if_neg (show 122+z.val≠1 by omega)]
    · intro k
      simp only [CloseoutRowsCircuitTagged.input,Fin.addCases_right,Fin.val_natAdd,
        if_neg (show 242+k.val≠0 by omega),if_neg (show 242+k.val≠1 by omega)]
  · intro j
    simp only [CloseoutRowsCircuitPrefix.input,Fin.addCases_right,Fin.val_natAdd,
      if_neg (show 268+j.val≠0 by omega),if_neg (show 268+j.val≠1 by omega)]

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitColdEntry
