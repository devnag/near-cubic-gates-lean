import Proof.Amplification.RecoveryTseitinNativeCarrier

/-! Join the physical drivers and tautology stream over abstract controller
carriers; retain only the exact ambient data required by the cold erase. -/
namespace NearCubicWires.RepairSource.RecoveryTseitinNative.Cold
open LocalBitMultitape RepairOrdinary ProjectionNormalization RecoveryExecution RecoveryRootRound VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem prefix_core {s u : Nat} (p : Machine 1370 s) (q : Machine 263 u)
    (f g cap bound n count output : Nat) (word : List Bool) (hcap : bound ≤ cap)
    (hd : ∃ drivers,ClockJoin.ReadyRun p f (input n count output word) drivers ∧
      drivers 1336=List.replicate (cap) true ∧
      drivers 1338=CompareMachine.word count ∧ drivers 1342=List.replicate count true ∧
      (∀ i : Fin 1342,i≠1336 → i≠1338 → drivers (i.castAdd 28)=input n count output word (i.castAdd 28)))
    (ht : ∃ base,run q g (tautInput n)=some base ∧
      base.final.tapes 239=RecoveryFormulaPayload.input (CircuitInputCNF.circuitInputTautologies n) ∧
      base.final.heads 239=(RecoveryFormulaPayload.input (CircuitInputCNF.circuitInputTautologies n)).length ∧
      base.final.tapes 242=List.replicate n true ∧
      (∀ i : Fin 263,i≠239 → base.final.heads i=0) ∧
      (∀ i : Fin 263,i≠242 → (base.final.tapes i).length ≤ bound) ∧
      base.steps ≤ g) : ∃ r,
    run (Composition.machine p (RecoveryFocus.machine tautSlots q)) (f+1+g) (input n count output word)=some r ∧
      r.final.tapes 1333=RecoveryFormulaPayload.input (CircuitInputCNF.circuitInputTautologies n) ∧
      r.final.heads 1333=(RecoveryFormulaPayload.input (CircuitInputCNF.circuitInputTautologies n)).length ∧
      (∀ i,i≠1333 → r.final.heads i=0) ∧
      (∀ i,retained i → r.final.tapes i=workspaceData cap n count output word i) ∧
      (∀ j,(r.final.tapes ((Reuse.scratch j).castAdd 34)).length ≤ cap) ∧
      r.steps ≤ f+1+g := by
  obtain ⟨drivers,hdrivers,dc,dword,_draw,dk⟩:=hd
  obtain ⟨a,ha,atapes,aheads,asteps⟩:=hdrivers
  have view (j : Fin 263) : a.final.tapes (tautSlots j)=tautInput n j := by
    rw [atapes,←taut_old_cast j,dk (tautOld j) (taut_old_work j).1 (taut_old_work j).2,
      taut_old_cast,taut_input]
  have driver_retained (i : Fin 1370) (hi : retained i) : drivers i=workspaceData cap n count output word i := by
    by_cases hc : i=1336
    · subst i; exact dc
    by_cases hw : i=1338
    · subst i; exact dword
    let j : Fin 1342:=⟨i.val,retained_bound i hi⟩
    have he : j.castAdd 28=i := Fin.ext rfl
    have h:=dk j
      (by intro heq; apply hc; have hv:=congrArg Fin.val heq; exact Fin.ext hv)
      (by intro heq; apply hw; have hv:=congrArg Fin.val heq; exact Fin.ext hv)
    rw [he] at h
    simpa only [workspaceData,if_neg hc,if_neg hw] using h
  obtain ⟨base,hbase,bo,bh,br,bheads,bb,bsteps⟩:=ht
  obtain ⟨b,hb,_bc,bstep,bhh,btt,bkeep⟩:=RecoveryFocus.dock tautSlots taut_injective q _
    a.final.heads a.final.tapes _ (by intro j; exact aheads _) view base hbase
  have bhall (i : Fin 1370) (hi : i≠1333) : b.final.heads i=0 := by
    by_cases hs : ∃ j,tautSlots j=i
    · obtain ⟨j,rfl⟩:=hs
      exact (bhh j).trans (bheads j (by intro he; subst j; exact hi rfl))
    · exact ((bkeep i (by intro j he; exact hs ⟨j,he⟩)).1).trans (aheads i)
  have btall (i : Fin 1370) (hi : retained i) : b.final.tapes i=workspaceData cap n count output word i := by
    by_cases h0 : i=0
    · subst i
      exact (btt 242).trans br
    · exact ((bkeep i (retained_away i hi h0)).2).trans
        ((congrFun atapes i).trans (driver_retained i hi))
  have bbound (j : Fin 1332) :
      (b.final.tapes ((Reuse.scratch j).castAdd 34)).length ≤ cap := by
    by_cases hs : ∃ k,tautSlots k=(Reuse.scratch j).castAdd 34
    · obtain ⟨k,hk⟩:=hs
      have h242 : k≠242 := by
        intro he
        subst k
        have hv:=congrArg Fin.val hk
        change 0=(Reuse.scratch j).val at hv
        exact (Reuse.scratch_range j).1 hv.symm
      rw [←hk,btt]
      exact (bb k h242).trans hcap
    · rw [(bkeep _ (by intro k hk; exact hs ⟨k,hk⟩)).2,atapes]
      let k : Fin 1342:=(Reuse.scratch j).castAdd 6
      have hi:=(Reuse.scratch j).isLt
      have hk6 : k≠1336 := by intro he; have hv:=congrArg Fin.val he; change (Reuse.scratch j).val=1336 at hv; omega
      have hk8 : k≠1338 := by intro he; have hv:=congrArg Fin.val he; change (Reuse.scratch j).val=1338 at hv; omega
      have he : (Reuse.scratch j).castAdd 34=k.castAdd 28 := rfl
      rw [he,dk k hk6 hk8,←he,native_blank,List.length_nil]
      omega
  obtain ⟨r,hr,rh,rt,rs⟩:=join_two p (RecoveryFocus.machine tautSlots q) _ _ _ a b ha hb
  refine ⟨r,hr,(congrFun rt 1333).trans ((btt 239).trans bo),
    (congrFun rh 1333).trans ((bhh 239).trans bh),?_,?_,?_,?_⟩
  · intro i hi
    exact (congrFun rh i).trans (bhall i hi)
  · intro i hi
    exact (congrFun rt i).trans (btall i hi)
  · intro j
    rw [rt]
    exact bbound j
  · rw [rs,bstep]
    omega

end NearCubicWires.RepairSource.RecoveryTseitinNative.Cold
