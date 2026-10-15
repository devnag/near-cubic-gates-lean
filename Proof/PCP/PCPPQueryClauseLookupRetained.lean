import Proof.PCP.PCPPQueryClauseLookup

/-! Retain the literal cached clause source and index through the actual
list-count parser, fixed header print and selected native-pair reader. -/
namespace NearCubicWires.RepairOrdinary.PCPPQueryClauseLookup
open LocalBitMultitape RepairRepresentation PCPPQueryField RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem lookup_retained_run (pre : List Bool) (count : ℕ) (rows : List (ℕ×ℕ))
    (a b : ℕ) (tail backing : List Bool) :
    let source := pre++natWord count++PCPPQueryClauseRows.stream rows++pairBits a b++tail
    ∃ r,runFrom machine (budget count rows a b) (entry source pre.length backing rows.length)=some r ∧
      r.steps=budget count rows a b ∧ r.final.tapes 2=natListWord [a,b] ∧
      r.final.tapes 0=source ∧ r.final.tapes 3=UnaryTemplate.tape rows.length ∧
      r.final.heads 3=1 := by
  dsimp only
  let source := pre++natWord count++PCPPQueryClauseRows.stream rows++pairBits a b++tail
  let start : Configuration 5 4 := ⟨header.start,![pre.length,0,0,1,0],![source,backing,[],UnaryTemplate.tape rows.length,[]]⟩
  obtain ⟨raw,hr,hrf,hrs⟩ := nat_run false pre (PCPPQueryClauseRows.stream rows++pairBits a b++tail) backing [] count
  have hsource : pre++natWord count++(PCPPQueryClauseRows.stream rows++pairBits a b++tail)=source := by
    simp [source,List.append_assoc]
  rw [hsource] at hr hrf
  simp only [selected,Bool.false_eq_true,↓reduceIte,List.append_nil] at hrf
  obtain ⟨x,hx,hxf,hxs⟩ := RecoveryFocus.run_config headerSlots (by decide)
    (PCPPQueryField.machine false) start.heads start.tapes _ _ raw hr
  have hxentry : RecoveryFocus.config headerSlots start.heads start.tapes (cfg 0 source pre.length backing 0 [])=start := by
    apply WilliamsSourceCrop.focus_same
    · intro i; fin_cases i <;> rfl
    · intro i; fin_cases i <;> rfl
  rw [hxentry] at hx
  obtain ⟨printed,hp,hpf,hps⟩ := (HierarchyFixedWord.write_prefix prefixBits 0 prefixBits.length (by omega)).run
    (by simp [HierarchyFixedWord.raw,HierarchyFixedWord.cfg])
  obtain ⟨y,hy,hyf,hys⟩ := RecoveryFocus.run_config printSlots (by intro i j _; exact Subsingleton.elim i j)
    (HierarchyFixedWord.raw prefixBits) x.final.heads x.final.tapes _ _ printed hp
  have printNone : RecoveryFocus.pick headerSlots (2 : Fin 5)=none := by decide
  have hyentry : RecoveryFocus.config printSlots x.final.heads x.final.tapes
      (HierarchyFixedWord.cfg prefixBits 0 (by omega))=Composition.restart x.final print.start := by
    apply WilliamsSourceCrop.focus_same
    · intro i
      rw [hxf]
      simp only [printSlots,RecoveryFocus.config,printNone]
      rfl
    · intro i
      rw [hxf]
      simp only [printSlots,RecoveryFocus.config,printNone]
      rfl
  rw [hyentry] at hy
  have hXY := Composition.run_join header print _ _ _ x y hx hy
  let xy := Composition.joinedReceipt x y
  let pre2 := pre++natWord count
  obtain ⟨base,hb,hsourceB,hposB,houtB,houtHeadB,hindexB,hindexHeadB,hbs⟩ := PCPPQueryClauseRows.pair_lookup_run
    pre2 rows tail (saved count backing) prefixBits a b
  obtain ⟨padded,hpad,hpadf,hpads,_⟩ := ZeroPadding.run_config PCPPQueryClauseRows.machine (capacity rows.length) _ _ base hb
  let paddedEntry := ZeroPadding.config (capacity rows.length)
    (Composition.leftConfig 8 (PCPPQueryClauseRows.cfg 0 source pre2.length (saved count backing) prefixBits rows.length 1))
  have hpad' : runFrom PCPPQueryClauseRows.machine (PCPPQueryClauseRows.budget rows a b) paddedEntry=some padded := hpad
  obtain ⟨z,hz,hzf,hzs⟩ := RecoveryFocus.run_config pairSlots
    (by intro i j h; apply Fin.ext; exact congrArg (fun k : Fin 5 => k.val) h)
    PCPPQueryClauseRows.machine xy.final.heads xy.final.tapes _ paddedEntry padded hpad'
  have hpickHeader (i : Fin 5) : RecoveryFocus.pick headerSlots i=
      (![some 0,some 1,none,none,some 2] : Fin 5→Option (Fin 3)) i := by
    fin_cases i
    · exact RecoveryFocus.pick_slot headerSlots (by decide) 0
    · exact RecoveryFocus.pick_slot headerSlots (by decide) 1
    · decide
    · decide
    · exact RecoveryFocus.pick_slot headerSlots (by decide) 2
  have hpickPrint (i : Fin 5) : RecoveryFocus.pick printSlots i=if i=2 then some 0 else none := by
    by_cases hi : i=2
    · subst i; exact RecoveryFocus.pick_slot printSlots (by intro i j _; exact Subsingleton.elim i j) 0
    · have hn : ¬∃ j,printSlots j=i := by simpa [printSlots] using Ne.symm hi
      simp [RecoveryFocus.pick,hn,hi]
  have hzentry : RecoveryFocus.config pairSlots xy.final.heads xy.final.tapes paddedEntry=
      Composition.restart xy.final pairs.start := by
    apply WilliamsSourceCrop.focus_same
    · intro i
      change y.final.heads (pairSlots i)=_
      rw [hyf,hpf,hxf,hrf]
      fin_cases i <;> simp [RecoveryFocus.config,hpickPrint,hpickHeader,pairSlots,HierarchyFixedWord.cfg,
        payload,cfg,start,paddedEntry,ZeroPadding.config,Composition.leftConfig,PCPPQueryClauseRows.cfg,
        RepeatMachine.cfg,controlConfig,TapeEmbedding.config,store,Fin.addCases,pre2,
        WilliamsInputHeader.natWord_eq,SignedSortKey.binary_length,Nat.add_assoc]
      omega
    · intro i
      change y.final.tapes (pairSlots i)=_
      rw [hyf,hpf,hxf,hrf]
      fin_cases i <;> simp [RecoveryFocus.config,hpickPrint,hpickHeader,pairSlots,HierarchyFixedWord.cfg,
        payload,cfg,start,paddedEntry,ZeroPadding.config,capacity,Composition.leftConfig,PCPPQueryClauseRows.cfg,
        RepeatMachine.cfg,controlConfig,TapeEmbedding.config,store,Fin.addCases,saved,PCPPQuerySupport.template_pad]
  rw [hzentry] at hz
  have hXYZ := Composition.run_join prefixMachine pairs _ _ _ xy z hXY hz
  have ht : (2*natBitLength count+3+1+prefixBits.length)+1+PCPPQueryClauseRows.budget rows a b=budget count rows a b := by
    unfold budget fieldCost; omega
  rw [ht] at hXYZ
  have he : Composition.leftConfig (Fintype.card (RepeatMachine.Control 8)+8)
      (Composition.leftConfig (prefixBits.length+1) start)=entry source pre.length backing rows.length := rfl
  rw [he] at hXYZ
  refine ⟨Composition.joinedReceipt xy z,hXYZ,?_,?_,?_,?_,?_⟩
  · change (x.steps+1+y.steps)+1+z.steps=_
    rw [hxs,hrs,hys,hps,hzs,hpads,hbs]
    exact ht
  · change z.final.tapes (pairSlots 2)=_
    simp only [hzf,RecoveryFocus.config,RecoveryFocus.pick_slot pairSlots
      (by intro i j h; apply Fin.ext; exact congrArg (fun k : Fin 5 => k.val) h)]
    rw [hpadf]
    simp only [ZeroPadding.config,capacity,show (2 : Fin 4)≠3 by decide,if_false,ZeroPadding.pad_zero]
    rw [houtB]
    simp [prefixBits,pairBits,fieldBits,natListWord]

  · change z.final.tapes (pairSlots 0)=_
    simp only [hzf,RecoveryFocus.config,RecoveryFocus.pick_slot pairSlots
      (by intro i j h; apply Fin.ext; exact congrArg (fun k : Fin 5 => k.val) h)]
    rw [hpadf]
    change ZeroPadding.pad 0 (base.final.tapes 0)=source
    rw [ZeroPadding.pad_zero,hsourceB]
  · change z.final.tapes (pairSlots 3)=_
    simp only [hzf,RecoveryFocus.config,RecoveryFocus.pick_slot pairSlots
      (by intro i j h; apply Fin.ext; exact congrArg (fun k : Fin 5 => k.val) h)]
    rw [hpadf]
    change ZeroPadding.pad (rows.length+2) (base.final.tapes 3)=UnaryTemplate.tape rows.length
    rw [hindexB,PCPPQuerySupport.template_pad]
  · change z.final.heads (pairSlots 3)=_
    simp only [hzf,RecoveryFocus.config,RecoveryFocus.pick_slot pairSlots
      (by intro i j h; apply Fin.ext; exact congrArg (fun k : Fin 5 => k.val) h)]
    rw [hpadf]
    exact hindexHeadB

end NearCubicWires.RepairOrdinary.PCPPQueryClauseLookup
