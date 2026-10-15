import Proof.Hierarchy.CompetitorUnaryWidthCopy

/-! Actual coefficient/count loading for the monomial stream loop. The
coefficient cursor advances while the scalar-output cursor is preserved;
every local field call and handoff is paid. -/
namespace NearCubicWires.RepairOrdinary.CompetitorMonomialStream
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorReusableDecision
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def heads (outPos pos : ℕ) : Fin 88 → ℕ := fun i => if i.val=79 then pos else if i.val=74 then outPos else 0
def cfg {s : ℕ} (outPos : ℕ) (q : Fin s) (pos : ℕ) (ambient : Fin 88 → List Bool) : Configuration 88 s :=
  ⟨q,heads outPos pos,ambient⟩

def target (j : Fin 6) : Fin 88 := j.castAdd 82
def loadSlots (j : Fin 6) : Fin 3 → Fin 88 := ![79,target j,80]
noncomputable def fieldProgram (j : Fin 6) := RecoveryFocus.machine (loadSlots j) FrameLoad.machine
def loaded (b : ℕ) (j : Fin 6) (bits : List Bool) (ambient : Fin 88 → List Bool) :=
  Function.update ambient (target j) (ZeroPadding.pad (capacity b) (frame bits))
theorem load_injective (j : Fin 6) : Function.Injective (loadSlots j) := by fin_cases j <;> decide
theorem target_ne_source (j : Fin 6) : target j≠79 := by
  intro h
  have hv := congrArg Fin.val h
  change j.val=79 at hv
  omega
theorem target_ne_counter (j : Fin 6) : target j≠80 := by
  intro h
  have hv := congrArg Fin.val h
  change j.val=80 at hv
  omega

theorem focus_heads (outPos : ℕ) (j : Fin 6) (q : Fin 4) (pos oldPos cap : ℕ) (source out : List Bool)
    (ambient : Fin 88 → List Bool) :
    (RecoveryFocus.config (loadSlots j) (heads outPos oldPos) ambient (loadCfg q source pos cap out)).heads=heads outPos pos := by
  funext i
  by_cases h0 : i=79
  · subst i
    have hp : RecoveryFocus.pick (loadSlots j) 79=some 0 :=
      RecoveryFocus.pick_slot (loadSlots j) (load_injective j) 0
    simp [RecoveryFocus.config,hp,loadCfg,heads]
  · by_cases h1 : i=target j
    · subst i
      have hj : (target j).val≠79 := fun h => target_ne_source j (Fin.ext h)
      have hjOut : (target j).val≠74 := by change j.val≠74; omega
      have hp : RecoveryFocus.pick (loadSlots j) (target j)=some 1 :=
        RecoveryFocus.pick_slot (loadSlots j) (load_injective j) 1
      simp [RecoveryFocus.config,hp,loadCfg,heads,hj,hjOut]
    · by_cases h2 : i=80
      · subst i
        have hp : RecoveryFocus.pick (loadSlots j) 80=some 2 :=
          RecoveryFocus.pick_slot (loadSlots j) (load_injective j) 2
        simp [RecoveryFocus.config,hp,loadCfg,heads]
      · have hn : ¬∃ k,loadSlots j k=i := by
          rintro ⟨k,hk⟩
          fin_cases k
          · exact h0 hk.symm
          · exact h1 hk.symm
          · exact h2 hk.symm
        have hv : i.val≠79 := fun h => h0 (Fin.ext h)
        simp [RecoveryFocus.config,RecoveryFocus.pick,hn,heads,hv]

theorem field_run (b outPos : ℕ) (j : Fin 6) (pre bits suffix : List Bool) (ambient : Fin 88 → List Bool)
    (hsource : ambient 79=pre++frame bits++suffix)
    (htarget : ambient (target j)=List.replicate (capacity b) false)
    (hcounter : ambient 80=List.replicate (capacity b) false)
    (hc : 2*bits.length+1≤capacity b) :
    ∃ r : ExecutionReceipt 88 4,
      runFrom (fieldProgram j) (4*bits.length+3) (cfg outPos (fieldProgram j).start pre.length ambient)=some r ∧
      r.final.heads=heads outPos (pre.length+2*bits.length+1) ∧
      r.final.tapes=loaded b j bits ambient ∧ r.steps=4*bits.length+3 := by
  obtain ⟨base,hr,hf,hs⟩ := padded_load_run pre bits suffix (capacity b) hc
  obtain ⟨r,hrun,hfinal,hsteps⟩ := RecoveryFocus.run_config (loadSlots j) (load_injective j)
    FrameLoad.machine (heads outPos pre.length) ambient _ _ base hr
  have hi : RecoveryFocus.config (loadSlots j) (heads outPos pre.length) ambient
      (loadCfg 0 (pre++frame bits++suffix) pre.length (capacity b) (List.replicate (capacity b) false))=
      cfg outPos (fieldProgram j).start pre.length ambient := by
    apply configuration_ext
    · rfl
    · exact focus_heads outPos j 0 _ _ _ _ _ _
    · apply install_existing
      intro k
      fin_cases k
      · exact hsource
      · exact htarget
      · exact hcounter
  rw [hi] at hrun
  refine ⟨r,hrun,?_,?_,hsteps.trans hs⟩
  · rw [hfinal,hf]
    exact focus_heads outPos j 3 _ _ _ _ _ _
  · rw [hfinal,hf]
    change install (loadSlots j) ambient
      (loadCfg 3 (pre++frame bits++suffix) (pre.length+2*bits.length+1) (capacity b)
        (ZeroPadding.pad (capacity b) (frame bits))).tapes=loaded b j bits ambient
    funext i
    by_cases h1 : i=target j
    · subst i
      rw [loaded,Function.update_self]
      exact install_slot (loadSlots j) (load_injective j) ambient
        (loadCfg 3 (pre++frame bits++suffix) (pre.length+2*bits.length+1) (capacity b)
          (ZeroPadding.pad (capacity b) (frame bits))).tapes 1
    · rw [loaded,Function.update_of_ne h1]
      by_cases h0 : i=79
      · subst i
        exact (install_slot (loadSlots j) (load_injective j) _ _ 0).trans hsource.symm
      · by_cases h2 : i=80
        · subst i
          exact (install_slot (loadSlots j) (load_injective j) _ _ 2).trans hcounter.symm
        · apply install_other
          intro k hk
          fin_cases k
          · exact h0 hk.symm
          · exact h1 hk.symm
          · exact h2 hk.symm

def fieldStates : List (Fin 6) → ℕ
  | [] => 1
  | _::js => 4+fieldStates js
def fieldHalt : Machine 88 1 where
  descriptionBits := 0
  start := 0
  halted := fun _ => true
  rule := fun _ _ => none
noncomputable def fieldsProgram : (js : List (Fin 6)) → Machine 88 (fieldStates js)
  | [] => fieldHalt
  | j::js => Composition.machine (fieldProgram j) (fieldsProgram js)
def fieldStream (fields : Fin 6 → List Bool) (js : List (Fin 6)) := js.flatMap (fun j => frame (fields j))
def fieldCost (fields : Fin 6 → List Bool) : List (Fin 6) → ℕ
  | [] => 0
  | j::js => 4*(fields j).length+4+fieldCost fields js
def placed (b : ℕ) (fields : Fin 6 → List Bool) : List (Fin 6) → (Fin 88 → List Bool) → (Fin 88 → List Bool)
  | [],ambient => ambient
  | j::js,ambient => placed b fields js (loaded b j (fields j) ambient)

theorem fields_run (b outPos : ℕ) (fields : Fin 6 → List Bool) (js : List (Fin 6))
    (hn : js.Nodup) (pre suffix : List Bool) (ambient : Fin 88 → List Bool)
    (hsource : ambient 79=pre++fieldStream fields js++suffix)
    (hblank : ∀ j∈js,ambient (target j)=List.replicate (capacity b) false)
    (hcounter : ambient 80=List.replicate (capacity b) false)
    (hcap : ∀ j∈js,2*(fields j).length+1≤capacity b) :
    ∃ r : ExecutionReceipt 88 (fieldStates js),
      runFrom (fieldsProgram js) (fieldCost fields js) (cfg outPos (fieldsProgram js).start pre.length ambient)=some r ∧
      r.final.heads=heads outPos (pre.length+(fieldStream fields js).length) ∧
      r.final.tapes=placed b fields js ambient ∧ r.steps=fieldCost fields js := by
  induction js generalizing pre ambient with
  | nil =>
    let r : ExecutionReceipt 88 1 := ⟨cfg outPos 0 pre.length ambient,0,(cfg outPos (0 : Fin 1) pre.length ambient).tapeCells⟩
    refine ⟨r,rfl,?_,rfl,rfl⟩
    simp [r,fieldStream,cfg]
  | cons j js ih =>
    obtain ⟨hj,hjs⟩ := List.nodup_cons.mp hn
    obtain ⟨first,hfirst,hfh,hft,hfs⟩ := field_run b outPos j pre (fields j) (fieldStream fields js++suffix)
      ambient (by simpa [fieldStream,List.append_assoc] using hsource)
      (hblank j (by simp)) hcounter (hcap j (by simp))
    have hs : loaded b j (fields j) ambient 79=
        (pre++frame (fields j))++fieldStream fields js++suffix := by
      rw [loaded,Function.update_of_ne (target_ne_source j).symm]
      simpa [fieldStream,List.append_assoc] using hsource
    have hb : ∀ k∈js,loaded b j (fields j) ambient (target k)=List.replicate (capacity b) false := by
      intro k hk
      have hkj : target k≠target j := by
        intro he
        have hval := congrArg Fin.val he
        have hkj : k=j := Fin.ext hval
        exact hj (hkj ▸ hk)
      rw [loaded,Function.update_of_ne hkj]
      exact hblank k (by simp [hk])
    have hc : loaded b j (fields j) ambient 80=List.replicate (capacity b) false := by
      rw [loaded,Function.update_of_ne (target_ne_counter j).symm]
      exact hcounter
    obtain ⟨last,hlast,hlh,hlt,hls⟩ := ih hjs (pre++frame (fields j)) (loaded b j (fields j) ambient)
      hs hb hc (fun k hk => hcap k (by simp [hk]))
    have he : Composition.restart first.final (fieldsProgram js).start=
        cfg outPos (fieldsProgram js).start (pre++frame (fields j)).length (loaded b j (fields j) ambient) := by
      apply configuration_ext
      · rfl
      · simpa [Composition.restart,cfg,List.length_append,frame_length,Nat.add_assoc] using hfh
      · exact hft
    have hlast' : runFrom (fieldsProgram js) (fieldCost fields js)
        (Composition.restart first.final (fieldsProgram js).start)=some last := by
      rw [he]
      exact hlast
    have hall := Composition.run_join (fieldProgram j) (fieldsProgram js)
      (4*(fields j).length+3) (fieldCost fields js) _ first last hfirst hlast'
    have htime : (4*(fields j).length+3)+1+fieldCost fields js=fieldCost fields (j::js) := by
      simp only [fieldCost]
    rw [htime] at hall
    refine ⟨Composition.joinedReceipt first last,hall,?_,hlt,?_⟩
    · change last.final.heads=heads outPos (pre.length+(fieldStream fields (j::js)).length)
      simpa [fieldStream,List.length_append,Nat.add_assoc] using hlh
    · change first.steps+1+last.steps=fieldCost fields (j::js)
      rw [hfs,hls]
      exact htime

end NearCubicWires.RepairOrdinary.CompetitorMonomialStream
