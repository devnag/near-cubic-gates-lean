import Proof.Hierarchy.CompetitorValidityField

/-! Six actual field loads for one rational-comparison record. The finite
target list is static program wiring; its fields are read sequentially from
the physical stream, with each call return included. -/
namespace NearCubicWires.RepairOrdinary.CompetitorValidity
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorReusableDecision
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def fieldStates : List (Fin 6) → ℕ
  | [] => 1
  | _::js => 4+fieldStates js
def fieldHalt : Machine 71 1 where
  descriptionBits := 0
  start := 0
  halted := fun _ => true
  rule := fun _ _ => none
noncomputable def fieldsProgram : (js : List (Fin 6)) → Machine 71 (fieldStates js)
  | [] => fieldHalt
  | j::js => Composition.machine (fieldProgram j) (fieldsProgram js)
def fieldStream (fields : Fin 6 → List Bool) (js : List (Fin 6)) := js.flatMap (fun j => frame (fields j))
def fieldCost (fields : Fin 6 → List Bool) : List (Fin 6) → ℕ
  | [] => 0
  | j::js => 4*(fields j).length+4+fieldCost fields js
def placed (b : ℕ) (fields : Fin 6 → List Bool) : List (Fin 6) → (Fin 71 → List Bool) → (Fin 71 → List Bool)
  | [],ambient => ambient
  | j::js,ambient => placed b fields js (loaded b j (fields j) ambient)

theorem fields_run (b : ℕ) (fields : Fin 6 → List Bool) (js : List (Fin 6))
    (hn : js.Nodup) (pre suffix : List Bool) (ambient : Fin 71 → List Bool)
    (hsource : ambient 67=pre++fieldStream fields js++suffix)
    (hblank : ∀ j∈js,ambient (target j)=List.replicate (capacity b) false)
    (hcounter : ambient 68=List.replicate (capacity b) false)
    (hcap : ∀ j∈js,2*(fields j).length+1≤capacity b) :
    ∃ r : ExecutionReceipt 71 (fieldStates js),
      runFrom (fieldsProgram js) (fieldCost fields js) (cfg (fieldsProgram js).start pre.length ambient)=some r ∧
      r.final.heads=heads (pre.length+(fieldStream fields js).length) ∧
      r.final.tapes=placed b fields js ambient ∧ r.steps=fieldCost fields js := by
  induction js generalizing pre ambient with
  | nil =>
    let r : ExecutionReceipt 71 1 := ⟨cfg 0 pre.length ambient,0,(cfg (0 : Fin 1) pre.length ambient).tapeCells⟩
    refine ⟨r,rfl,?_,rfl,rfl⟩
    simp [r,fieldStream,cfg]
  | cons j js ih =>
    obtain ⟨hj,hjs⟩ := List.nodup_cons.mp hn
    obtain ⟨first,hfirst,hfh,hft,hfs⟩ := field_run b j pre (fields j) (fieldStream fields js++suffix)
      ambient (by simpa [fieldStream,List.append_assoc] using hsource)
      (hblank j (by simp)) hcounter (hcap j (by simp))
    have hs : loaded b j (fields j) ambient 67=
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
    have hc : loaded b j (fields j) ambient 68=List.replicate (capacity b) false := by
      rw [loaded,Function.update_of_ne (target_ne_counter j).symm]
      exact hcounter
    obtain ⟨last,hlast,hlh,hlt,hls⟩ := ih hjs (pre++frame (fields j)) (loaded b j (fields j) ambient)
      hs hb hc (fun k hk => hcap k (by simp [hk]))
    have he : Composition.restart first.final (fieldsProgram js).start=
        cfg (fieldsProgram js).start (pre++frame (fields j)).length (loaded b j (fields j) ambient) := by
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
    · change last.final.heads=heads (pre.length+(fieldStream fields (j::js)).length)
      simpa [fieldStream,List.length_append,Nat.add_assoc] using hlh
    · change first.steps+1+last.steps=fieldCost fields (j::js)
      rw [hfs,hls]
      exact htime

end NearCubicWires.RepairOrdinary.CompetitorValidity
