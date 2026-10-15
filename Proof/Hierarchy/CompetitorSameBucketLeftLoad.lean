import Proof.Hierarchy.CompetitorSameBucketInnerRow

/-! The outer-row loader clears only the cached left record and its local
copy log, then takes the next fixed-width record from the original packet.
The right-bucket cursor, templates, and output cursor stay in place. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketLeftLoad
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def heads (sourcePos outPos : ℕ) : Fin 45 → ℕ := fun i =>
  if i=34 then outPos else if i=38 ∨ i=41 then 1 else if i=43 then sourcePos else 0
def tapes (ambient : Fin 41 → List Bool) (h b : ℕ) (source log : List Bool) : Fin 45 → List Bool :=
  Fin.addCases (m := 41) (n := 4) (motive := fun _ => List Bool) ambient
    ![UnaryTemplate.tape b,UnaryTemplate.tape h,source,log]
def cfg {s : ℕ} (q : Fin s) (sourcePos outPos : ℕ) (ambient : Fin 41 → List Bool)
    (h b : ℕ) (source log : List Bool) : Configuration 45 s :=
  ⟨q,heads sourcePos outPos,tapes ambient h b source log⟩
def eraseSlots : Fin 4 → Fin 45 := ![0,44,36,37]
def loadSlots : Fin 4 → Fin 45 := ![38,43,0,44]
theorem erase_injective : Function.Injective eraseSlots := by decide
theorem load_injective : Function.Injective loadSlots := by decide
noncomputable def first := RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 2)
noncomputable def last := RecoveryFocus.machine loadSlots CompetitorSameBucketRecordCopy.machine
noncomputable def machine := Composition.machine first last

theorem erase_pick (i : Fin 45) : RecoveryFocus.pick eraseSlots i=
    (if i=0 then some 0 else if i=44 then some 1 else if i=36 then some 2 else if i=37 then some 3 else none) := by
  classical
  by_cases h0 : i=0
  · subst i; exact RecoveryFocus.pick_slot eraseSlots erase_injective 0
  by_cases h44 : i=44
  · subst i; exact RecoveryFocus.pick_slot eraseSlots erase_injective 1
  by_cases h36 : i=36
  · subst i; exact RecoveryFocus.pick_slot eraseSlots erase_injective 2
  by_cases h37 : i=37
  · subst i; exact RecoveryFocus.pick_slot eraseSlots erase_injective 3
  simp only [h0,h44,h36,h37,ite_false]
  unfold RecoveryFocus.pick
  apply dif_neg
  rintro ⟨j,hj⟩
  fin_cases j <;> simp_all [eraseSlots]

theorem load_pick (i : Fin 45) : RecoveryFocus.pick loadSlots i=
    (if i=38 then some 0 else if i=43 then some 1 else if i=0 then some 2 else if i=44 then some 3 else none) := by
  classical
  by_cases h38 : i=38
  · subst i; exact RecoveryFocus.pick_slot loadSlots load_injective 0
  by_cases h43 : i=43
  · subst i; exact RecoveryFocus.pick_slot loadSlots load_injective 1
  by_cases h0 : i=0
  · subst i; exact RecoveryFocus.pick_slot loadSlots load_injective 2
  by_cases h44 : i=44
  · subst i; exact RecoveryFocus.pick_slot loadSlots load_injective 3
  simp only [h38,h43,h0,h44,ite_false]
  unfold RecoveryFocus.pick
  apply dif_neg
  rintro ⟨j,hj⟩
  fin_cases j <;> simp_all [loadSlots]

theorem clear_run (cap h b pos outPos : ℕ) (ambient : Fin 41 → List Bool) (source log : List Bool)
    (driver : ambient 36=List.replicate cap true) (reset : ambient 37=List.replicate (cap+1) false)
    (leftFit : (ambient 0).length≤cap) (logFit : log.length≤cap) :
    ∃ r,runFrom first (2*cap+4) (cfg first.start pos outPos ambient h b source log)=some r ∧
      r.final.heads=heads pos outPos ∧
      r.final.tapes=tapes (Function.update ambient 0 (List.replicate cap false)) h b source (List.replicate cap false) ∧
      r.steps=2*cap+4 := by
  have ready : ReadyRun (RecoveryScratchErase.resetMachine 2) (2*cap+4)
      (CompetitorPlaneWorkspace.eraseInput cap (![ambient 0,log] : Fin 2 → List Bool))
      (CompetitorPlaneWorkspace.eraseInput cap (fun _ : Fin 2 => List.replicate cap false)) := by
    simpa only [CompetitorPlaneWorkspace.eraseInput,max_self] using
      RecoveryScratchErase.erase_ready cap (cap+1) (![ambient 0,log] : Fin 2 → List Bool)
        (by intro i; fin_cases i; exact leftFit; exact logFit)
  obtain ⟨base,hb,bt,bh,bs⟩ := ready
  let entry := cfg first.start pos outPos ambient h b source log
  have hi : RecoveryFocus.config eraseSlots entry.heads entry.tapes
      (initialConfiguration (RecoveryScratchErase.resetMachine 2)
        (CompetitorPlaneWorkspace.eraseInput cap (![ambient 0,log] : Fin 2 → List Bool)))=entry := by
    apply WilliamsSourceCrop.focus_same
    · intro i; fin_cases i <;> rfl
    · intro i; fin_cases i <;> first | exact driver | exact reset | rfl
  obtain ⟨actual,hr,hf,hs⟩ := RecoveryFocus.run_config eraseSlots erase_injective (RecoveryScratchErase.resetMachine 2)
    entry.heads entry.tapes _ _ base hb
  rw [hi] at hr
  refine ⟨actual,hr,?_,?_,hs.trans bs⟩
  · rw [hf]
    funext i
    simp only [RecoveryFocus.config,erase_pick]
    fin_cases i <;> simp [entry,cfg,heads,bh]
  · rw [hf]
    funext i
    simp only [RecoveryFocus.config,erase_pick,bt]
    fin_cases i <;> simp [entry,cfg,tapes,CompetitorPlaneWorkspace.eraseInput,Fin.addCases,driver,reset]

theorem load_run (cap h b outPos : ℕ) (ambient : Fin 41 → List Bool) (pre bits suffix : List Bool)
    (width : ambient 38=UnaryTemplate.tape bits.length) (hc : 2*bits.length+4≤cap) :
    ∃ r,runFrom last (CompetitorSameBucketRecordCopy.budget bits.length)
        (cfg last.start pre.length outPos (Function.update ambient 0 (List.replicate cap false)) h b
          (pre++bits++suffix) (List.replicate cap false))=some r ∧
      r.final.heads=heads (pre.length+bits.length) outPos ∧
      r.final.tapes=tapes (Function.update ambient 0 (ZeroPadding.pad cap bits)) h b (pre++bits++suffix) (List.replicate cap false) ∧
      r.steps=CompetitorSameBucketRecordCopy.budget bits.length := by
  obtain ⟨base,hb,bh,bt,bs⟩ := CompetitorSameBucketRecordCopy.padded_run cap pre bits suffix hc
  let entry := cfg last.start pre.length outPos (Function.update ambient 0 (List.replicate cap false)) h b
    (pre++bits++suffix) (List.replicate cap false)
  have hi : RecoveryFocus.config loadSlots entry.heads entry.tapes
      (CompetitorSameBucketRecordCopy.paddedInput cap pre bits suffix)=entry := by
    apply WilliamsSourceCrop.focus_same
    · intro i
      rw [CompetitorSameBucketRecordCopy.padded_heads]
      fin_cases i <;> rfl
    · intro i
      rw [CompetitorSameBucketRecordCopy.padded_tapes]
      fin_cases i
      · exact width
      · rfl
      · simp [entry,cfg,tapes,loadSlots,Fin.addCases]
      · rfl
  obtain ⟨actual,hr,hf,hs⟩ := RecoveryFocus.run_config loadSlots load_injective CompetitorSameBucketRecordCopy.machine
    entry.heads entry.tapes _ _ base hb
  rw [hi] at hr
  refine ⟨actual,hr,?_,?_,hs.trans bs⟩
  · rw [hf]
    funext i
    simp only [RecoveryFocus.config,load_pick,bh]
    fin_cases i <;> simp [entry,cfg,heads]
  · rw [hf]
    funext i
    simp only [RecoveryFocus.config,load_pick,bt]
    fin_cases i <;> simp [entry,cfg,tapes,Fin.addCases,width]

theorem prepare_run (cap h b outPos : ℕ) (ambient : Fin 41 → List Bool) (pre bits suffix log : List Bool)
    (driver : ambient 36=List.replicate cap true) (reset : ambient 37=List.replicate (cap+1) false)
    (leftFit : (ambient 0).length≤cap) (logFit : log.length≤cap)
    (width : ambient 38=UnaryTemplate.tape bits.length) (hc : 2*bits.length+4≤cap) :
    ∃ r,runFrom machine (2*cap+4*bits.length+15)
        (cfg machine.start pre.length outPos ambient h b (pre++bits++suffix) log)=some r ∧
      r.final.heads=heads (pre.length+bits.length) outPos ∧
      r.final.tapes=tapes (Function.update ambient 0 (ZeroPadding.pad cap bits)) h b (pre++bits++suffix) (List.replicate cap false) ∧
      r.steps=2*cap+4*bits.length+15 := by
  obtain ⟨clear,hclear,ch,ct,cs⟩ := clear_run cap h b pre.length outPos ambient (pre++bits++suffix) log driver reset leftFit logFit
  obtain ⟨copy,hcopy,ph,pt,ps⟩ := load_run cap h b outPos ambient pre bits suffix width hc
  have hi : Composition.restart clear.final last.start=
      cfg last.start pre.length outPos (Function.update ambient 0 (List.replicate cap false)) h b (pre++bits++suffix) (List.replicate cap false) :=
    configuration_ext rfl ch ct
  rw [←hi] at hcopy
  have hall := Composition.run_join first last _ _ _ clear copy hclear hcopy
  have he : (2*cap+4)+1+CompetitorSameBucketRecordCopy.budget bits.length=2*cap+4*bits.length+15 := by
    unfold CompetitorSameBucketRecordCopy.budget; omega
  rw [he] at hall
  refine ⟨Composition.joinedReceipt clear copy,hall,ph,pt,?_⟩
  change clear.steps+1+copy.steps=_
  omega

end NearCubicWires.RepairOrdinary.CompetitorSameBucketLeftLoad
