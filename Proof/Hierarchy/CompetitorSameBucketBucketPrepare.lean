import Proof.Hierarchy.CompetitorSameBucketSquare

/-! Once-per-bucket D erasure and the existing fixed-block copy/return.
The candidate square will reuse this bank; no D-sized erasure occurs inside
its pair loops. Physical H/B/BL and D fields are retained throughout. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketBucketPrepare
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def heads (sourcePos outPos : ℕ) : Fin 50 → ℕ := fun i =>
  if i=34 then outPos else if i=38 ∨ i=41 ∨ i=45 ∨ i=48 then 1 else if i=43 then sourcePos else 0
def tapes (ambient : Fin 46 → List Bool) (cap h b : ℕ) (log : List Bool) : Fin 50 → List Bool :=
  Fin.addCases (m := 46) (n := 4) (motive := fun _ => List Bool) ambient
    ![List.replicate cap true,List.replicate (cap+1) false,UnaryTemplate.tape ((4*h+1)*b),log]
def cfg {s : ℕ} (q : Fin s) (sourcePos outPos : ℕ) (ambient : Fin 46 → List Bool)
    (cap h b : ℕ) (log : List Bool) : Configuration 50 s :=
  ⟨q,heads sourcePos outPos,tapes ambient cap h b log⟩
def eraseSlots : Fin 4 → Fin 50 := ![39,49,46,47]
def loadSlots : Fin 6 → Fin 50 := ![48,43,39,49,42,45]
theorem erase_injective : Function.Injective eraseSlots := by decide
theorem load_injective : Function.Injective loadSlots := by decide
noncomputable def first := RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 2)
noncomputable def last := RecoveryFocus.machine loadSlots CompetitorSameBucketBlockLoad.machine
noncomputable def machine := Composition.machine first last

theorem erase_pick (i : Fin 50) : RecoveryFocus.pick eraseSlots i=
    (if i=39 then some 0 else if i=49 then some 1 else if i=46 then some 2 else if i=47 then some 3 else none) := by
  classical
  by_cases h39 : i=39
  · subst i; exact RecoveryFocus.pick_slot eraseSlots erase_injective 0
  by_cases h49 : i=49
  · subst i; exact RecoveryFocus.pick_slot eraseSlots erase_injective 1
  by_cases h46 : i=46
  · subst i; exact RecoveryFocus.pick_slot eraseSlots erase_injective 2
  by_cases h47 : i=47
  · subst i; exact RecoveryFocus.pick_slot eraseSlots erase_injective 3
  simp only [h39,h49,h46,h47,ite_false]
  unfold RecoveryFocus.pick
  apply dif_neg
  rintro ⟨j,hj⟩
  fin_cases j <;> simp_all [eraseSlots]

theorem clear_run (cap h b pos outPos : ℕ) (ambient : Fin 46 → List Bool) (log : List Bool)
    (leftFit : (ambient 39).length≤cap) (logFit : log.length≤cap) :
    ∃ r,runFrom first (2*cap+4) (cfg first.start pos outPos ambient cap h b log)=some r ∧
      r.final.heads=heads pos outPos ∧
      r.final.tapes=tapes (Function.update ambient 39 (List.replicate cap false)) cap h b (List.replicate cap false) ∧
      r.steps=2*cap+4 := by
  have ready : ReadyRun (RecoveryScratchErase.resetMachine 2) (2*cap+4)
      (CompetitorPlaneWorkspace.eraseInput cap (![ambient 39,log] : Fin 2 → List Bool))
      (CompetitorPlaneWorkspace.eraseInput cap (fun _ : Fin 2 => List.replicate cap false)) := by
    simpa only [CompetitorPlaneWorkspace.eraseInput,max_self] using
      RecoveryScratchErase.erase_ready cap (cap+1) (![ambient 39,log] : Fin 2 → List Bool)
        (by intro i; fin_cases i; exact leftFit; exact logFit)
  obtain ⟨base,hb,bt,bh,bs⟩ := ready
  let entry := cfg first.start pos outPos ambient cap h b log
  have hi : RecoveryFocus.config eraseSlots entry.heads entry.tapes
      (initialConfiguration (RecoveryScratchErase.resetMachine 2)
        (CompetitorPlaneWorkspace.eraseInput cap (![ambient 39,log] : Fin 2 → List Bool)))=entry := by
    apply WilliamsSourceCrop.focus_same
    · intro i; fin_cases i <;> rfl
    · intro i; fin_cases i <;> rfl
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
    fin_cases i <;> simp [entry,cfg,tapes,CompetitorPlaneWorkspace.eraseInput,Fin.addCases]

theorem load_pick (i : Fin 50) : RecoveryFocus.pick loadSlots i=
    (if i=48 then some 0 else if i=43 then some 1 else if i=39 then some 2 else if i=49 then some 3
      else if i=42 then some 4 else if i=45 then some 5 else none) := by
  classical
  by_cases h48 : i=48
  · subst i; exact RecoveryFocus.pick_slot loadSlots load_injective 0
  by_cases h43 : i=43
  · subst i; exact RecoveryFocus.pick_slot loadSlots load_injective 1
  by_cases h39 : i=39
  · subst i; exact RecoveryFocus.pick_slot loadSlots load_injective 2
  by_cases h49 : i=49
  · subst i; exact RecoveryFocus.pick_slot loadSlots load_injective 3
  by_cases h42 : i=42
  · subst i; exact RecoveryFocus.pick_slot loadSlots load_injective 4
  by_cases h45 : i=45
  · subst i; exact RecoveryFocus.pick_slot loadSlots load_injective 5
  simp only [h48,h43,h39,h49,h42,h45,ite_false]
  unfold RecoveryFocus.pick
  apply dif_neg
  rintro ⟨j,hj⟩
  fin_cases j <;> simp_all [loadSlots]

theorem load_run (cap h b outPos : ℕ) (ambient : Fin 46 → List Bool) (pre bits suffix : List Bool)
    (hsource : ambient 43=pre++bits++suffix) (hH : ambient 42=UnaryTemplate.tape h) (hB : ambient 45=UnaryTemplate.tape b)
    (hlen : bits.length=(4*h+1)*b) (hc : 2*bits.length+4≤cap) :
    ∃ r,runFrom last (CompetitorSameBucketBlockLoad.budget h b)
        (cfg last.start pre.length outPos (Function.update ambient 39 (List.replicate cap false)) cap h b (List.replicate cap false))=some r ∧
      r.final.heads=heads pre.length outPos ∧
      r.final.tapes=tapes (Function.update ambient 39 (ZeroPadding.pad cap bits)) cap h b (List.replicate cap false) ∧
      r.steps≤CompetitorSameBucketBlockLoad.budget h b := by
  obtain ⟨base,hb,bh,bt,bs⟩ := CompetitorSameBucketBlockLoad.block_run h b cap pre bits suffix hlen hc
  let entry := cfg last.start pre.length outPos (Function.update ambient 39 (List.replicate cap false)) cap h b (List.replicate cap false)
  have hi : RecoveryFocus.config loadSlots entry.heads entry.tapes
      (CompetitorSameBucketBlockLoad.cfg CompetitorSameBucketBlockLoad.machine.start (pre++bits++suffix) h b cap pre.length
        (List.replicate cap false))=entry := by
    apply WilliamsSourceCrop.focus_same
    · intro i; fin_cases i <;> rfl
    · intro i
      fin_cases i <;> first | exact hsource | exact hH | exact hB | simp [entry,cfg,tapes,loadSlots,CompetitorSameBucketBlockLoad.cfg,Fin.addCases]
  obtain ⟨actual,hr,hf,hs⟩ := RecoveryFocus.run_config loadSlots load_injective CompetitorSameBucketBlockLoad.machine
    entry.heads entry.tapes _ _ base hb
  rw [hi] at hr
  refine ⟨actual,hr,?_,?_,hs.trans_le bs⟩
  · rw [hf]
    funext i
    simp only [RecoveryFocus.config,load_pick,bh]
    fin_cases i <;> simp [entry,cfg,heads,CompetitorSameBucketBlockLoad.cfg]
  · rw [hf]
    funext i
    simp only [RecoveryFocus.config,load_pick,bt]
    fin_cases i <;> simp [entry,cfg,tapes,Fin.addCases,CompetitorSameBucketBlockLoad.cfg,hsource,hH,hB]

def budget (cap h b : ℕ) := 2*cap+5+CompetitorSameBucketBlockLoad.budget h b
theorem prepare_run (cap h b outPos : ℕ) (ambient : Fin 46 → List Bool) (pre bits suffix log : List Bool)
    (hsource : ambient 43=pre++bits++suffix) (hH : ambient 42=UnaryTemplate.tape h) (hB : ambient 45=UnaryTemplate.tape b)
    (targetFit : (ambient 39).length≤cap) (logFit : log.length≤cap)
    (hlen : bits.length=(4*h+1)*b) (hc : 2*bits.length+4≤cap) :
    ∃ r,runFrom machine (budget cap h b) (cfg machine.start pre.length outPos ambient cap h b log)=some r ∧
      r.final.heads=heads pre.length outPos ∧
      r.final.tapes=tapes (Function.update ambient 39 (ZeroPadding.pad cap bits)) cap h b (List.replicate cap false) ∧
      r.steps≤budget cap h b := by
  obtain ⟨clear,hclear,ch,ct,cs⟩ := clear_run cap h b pre.length outPos ambient log targetFit logFit
  obtain ⟨copy,hcopy,ph,pt,ps⟩ := load_run cap h b outPos ambient pre bits suffix hsource hH hB hlen hc
  have hi : Composition.restart clear.final last.start=
      cfg last.start pre.length outPos (Function.update ambient 39 (List.replicate cap false)) cap h b (List.replicate cap false) :=
    configuration_ext rfl ch ct
  rw [←hi] at hcopy
  have hall := Composition.run_join first last _ _ _ clear copy hclear hcopy
  have he : (2*cap+4)+1+CompetitorSameBucketBlockLoad.budget h b=budget cap h b := by unfold budget; omega
  rw [he] at hall
  refine ⟨Composition.joinedReceipt clear copy,hall,ph,pt,?_⟩
  change clear.steps+1+copy.steps≤budget cap h b
  rw [←he]
  omega

end NearCubicWires.RepairOrdinary.CompetitorSameBucketBucketPrepare
