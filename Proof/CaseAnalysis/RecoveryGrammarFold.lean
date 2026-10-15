import Proof.CaseAnalysis.RecoveryGrammarSchedule

/-! One physical terminal-constant and reverse fold serves the original
grammar's all and any lists, from their already emitted child references. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarFold
open LocalBitMultitape SourceInterfaces RepairRepresentation Composition
open RecoveryBoundedNative RecoveryBoundedAddress
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def bits (conjunction : Bool) :=
  PCPPRequestNodeSchema.native (.const conjunction : BooleanNode 0)
def heads (out pre : List Bool) (refs : List ℕ) : Fin 35→ℕ :=
  Fin.addCases (m:=29) (n:=6) (motive:=fun _=>ℕ) (PCPPNativeClauseBank.heads out)
    (![0,0,(pre++RecoveryBoundedNativeUnaryLoop.stackWords refs).length,0,0,1] : Fin 6→ℕ)
def data (base C : ℕ) (out pre : List Bool) (refs : List ℕ) : Fin 35→List Bool :=
  Fin.addCases (m:=29) (n:=6) (motive:=fun _=>List Bool) (RecoveryBoundedNativeFold.oldData 0 base C out)
    (![[false],List.replicate C false,pre++RecoveryBoundedNativeUnaryLoop.stackWords refs,
      List.replicate C false,List.replicate C false,CompareMachine.word refs.length] : Fin 6→List Bool)
def slot : Fin 1→Fin 35:=fun _=>20
noncomputable def seed (conjunction : Bool):=RecoveryFocus.machine slot (HierarchyFixedWord.raw (bits conjunction))
noncomputable def machine (conjunction : Bool):=Composition.machine (seed conjunction)
  (RecoveryBoundedNativeFoldLoop.machine conjunction)
noncomputable def entry (conjunction : Bool) (base C : ℕ) (out pre : List Bool) (refs : List ℕ) :=
  (⟨(machine conjunction).start,heads out pre refs,data base C out pre refs⟩ : Configuration 35 _)
def budget (conjunction : Bool) (count C : ℕ):=
  (bits conjunction).length+1+(count*(24*C+66)+count+3)

theorem seed_run (conjunction : Bool) (base C : ℕ) (out pre : List Bool) (refs : List ℕ) :
    ∃ r,runFrom (seed conjunction) (bits conjunction).length
      ⟨(seed conjunction).start,heads out pre refs,data base C out pre refs⟩=some r ∧
      r.steps=(bits conjunction).length ∧ r.final.heads=heads (out++bits conjunction) pre refs ∧
      r.final.tapes=data base C (out++bits conjunction) pre refs := by
  obtain ⟨p,pr,pf,ps⟩:=RepairSource.ProjectionNormalization.Constants.write_run (bits conjunction) out
  obtain ⟨r,rr,_,rs,rh,rt,rkeep⟩:=RecoveryFocus.dock slot (by decide)
    (HierarchyFixedWord.raw (bits conjunction)) _ (heads out pre refs) (data base C out pre refs)
    (RepairSource.ProjectionNormalization.Constants.cfg (bits conjunction) out 0 (by omega))
    (by intro j;fin_cases j;rfl)
    (by intro j;fin_cases j;change out=out++(bits conjunction).take 0;simp) p pr
  refine ⟨r,rr,rs.trans ps,?_,?_⟩
  · funext i
    by_cases hi : i=20
    · subst i
      have hh:=rh 0
      change r.final.heads 20=p.final.heads 0 at hh
      rw [hh,pf]
      change out.length+(bits conjunction).length=(out++bits conjunction).length
      simp only [List.length_append]
    · rw [(rkeep i (by intro j;fin_cases j;exact fun h=>hi h.symm)).1]
      fin_cases i <;> first | rfl | exact False.elim (hi rfl)
  · have he:=HierarchyWidth.install_eq slot (by decide) (data base C out pre refs) r.final.tapes
      (fun _=>out++bits conjunction)
      (by intro j;rw [rt j,pf];simp only [RepairSource.ProjectionNormalization.Constants.cfg,List.take_length]) (by intro i hi;exact (rkeep i hi).2)
    rw [←he]
    apply HierarchyWidth.install_eq slot (by decide)
    · intro j;fin_cases j;rfl
    · intro i hi
      have h:=hi 0
      fin_cases i <;> first | rfl | exact False.elim (h rfl)

theorem loop_heads (conjunction : Bool) (base C : ℕ) (out pre : List Bool) (refs : List ℕ) :
    (RecoveryBoundedNativeFoldLoop.configuration 0 conjunction C false pre refs.reverse
      ⟨base,0,0,out⟩ refs.length 1).heads=heads out pre refs := by
  simp only [RecoveryBoundedNativeFoldLoop.configuration,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,
    RecoveryBoundedNativeFoldLoop.State.entry,RecoveryBoundedNativeFold.entry,
    RecoveryBoundedNativeFoldLoop.stack,List.reverse_reverse,RecoveryBoundedNativeFold.heads]
  funext i
  fin_cases i <;> rfl

theorem loop_tapes (conjunction : Bool) (base C : ℕ) (out pre : List Bool) (refs : List ℕ) :
    (RecoveryBoundedNativeFoldLoop.configuration 0 conjunction C false pre refs.reverse
      ⟨base,0,0,out⟩ refs.length 1).tapes=data base C out pre refs := by
  simp only [RecoveryBoundedNativeFoldLoop.configuration,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,
    RecoveryBoundedNativeFoldLoop.State.entry,RecoveryBoundedNativeFold.entry,
    RecoveryBoundedNativeFoldLoop.stack,List.reverse_reverse,RecoveryBoundedNativeFold.data,
    List.replicate_zero,List.append_nil]
  funext i
  fin_cases i <;> rfl

noncomputable def finalConfiguration (conjunction : Bool) (base C : ℕ) (out pre : List Bool) (refs : List ℕ):=
  RecoveryBoundedNativeFoldLoop.configuration 3 conjunction C false pre []
    (RecoveryBoundedNativeFoldLoop.State.iterate conjunction refs.reverse ⟨base,0,0,out++bits conjunction⟩)
    refs.length 1

theorem fold_run (conjunction : Bool) (base W C : ℕ) (out pre : List Bool) (refs : List ℕ)
    (href : ∀ ref∈refs,ref ≤ W) (ha : base+refs.length ≤ W)
    (hC : 16384*(W+1)^2 ≤ C) :
    ∃ r,runFrom (machine conjunction) (budget conjunction refs.length C)
      (entry conjunction base C out pre refs)=some r ∧
      r.steps ≤ budget conjunction refs.length C ∧
      r.final.heads=(finalConfiguration conjunction base C out pre refs).heads ∧
      r.final.tapes=(finalConfiguration conjunction base C out pre refs).tapes := by
  obtain ⟨p,pr,ps,ph,pt⟩:=seed_run conjunction base C out pre refs
  obtain ⟨q,qr,qf,qs⟩:=RecoveryBoundedNativeFoldLoop.loop_run conjunction W C refs.length false pre refs.reverse
    ⟨base,0,0,out++bits conjunction⟩
    (by simp only [List.length_reverse,Nat.zero_add])
    (by intro ref hr;exact href ref (List.mem_reverse.mp hr))
    (by simpa only [List.length_reverse] using ha) hC
  rw [List.length_reverse] at qr qs
  have qr' : runFrom (RecoveryBoundedNativeFoldLoop.machine conjunction)
      (refs.length*(24*C+66)+refs.length+3)
      (restart p.final (RecoveryBoundedNativeFoldLoop.machine conjunction).start)=some q := by
    have he : restart p.final (RecoveryBoundedNativeFoldLoop.machine conjunction).start=
        RecoveryBoundedNativeFoldLoop.configuration 0 conjunction C false pre refs.reverse
          ⟨base,0,0,out++bits conjunction⟩ refs.length 1 := by
      apply configuration_ext
      · rfl
      · change p.final.heads=_
        rw [ph,loop_heads]
      · change p.final.tapes=_
        rw [pt,loop_tapes]
    rw [he]
    exact qr
  have full:=Composition.run_join (seed conjunction) (RecoveryBoundedNativeFoldLoop.machine conjunction)
    _ _ _ p q pr qr'
  refine ⟨joinedReceipt p q,full,?_,?_,?_⟩
  · change p.steps+1+q.steps ≤ budget conjunction refs.length C
    unfold budget
    omega
  · change q.final.heads=_
    rw [qf]
    rfl
  · change q.final.tapes=_
    rw [qf]
    rfl

theorem output_graph (n : ℕ) (conjunction : Bool) (base C : ℕ)
    (out pre : List Bool) (refs : List ℕ) :
    (finalConfiguration conjunction base C out pre refs).tapes 20=
      out++([BooleanNode.const conjunction]++foldNodes (n:=n) conjunction base refs.reverse).flatMap
        PCPPRequestNodeSchema.native := by
  have h:=RecoveryBoundedNativeFoldLoop.iterate_meaning (n:=n) conjunction refs.reverse
    ⟨base,0,0,out++bits conjunction⟩
  change (RecoveryBoundedNativeFoldLoop.State.iterate conjunction refs.reverse ⟨base,0,0,out++bits conjunction⟩).out=_
  rw [h.2]
  simp only [List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc]
  rfl

theorem output_counter (conjunction : Bool) (base C : ℕ) (out pre : List Bool) (refs : List ℕ) :
    (finalConfiguration conjunction base C out pre refs).tapes 25=List.replicate (base+refs.length) true := by
  have h:=RecoveryBoundedNativeFoldLoop.iterate_meaning (n:=0) conjunction refs.reverse
    ⟨base,0,0,out++bits conjunction⟩
  change List.replicate (RecoveryBoundedNativeFoldLoop.State.iterate conjunction refs.reverse
    ⟨base,0,0,out++bits conjunction⟩).acc true=_
  rw [h.1,List.length_reverse]

end NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarFold
