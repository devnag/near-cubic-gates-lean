import Proof.Assembly.ClosureHardwireCacheBody
import Proof.Assembly.ClosureHardwireBudget
import Proof.CaseAnalysis.RowsDegreeLoop

/-! A sequential native-cache loop for one A.12 live assignment. Every
iteration calls the actual copy/reload/hardwire body; there is no assumed
supplier callback. The original cache is retained, its cursor advances, and
the entire reusable bank is specified at both ends. Header parsing and the
outer live-assignment loop are separate physical steps.
-/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.HardwireCacheLoop
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch RecoveryRootRound
open RepairRepresentation RepairSource CloseoutFinal SupplierPipeline SupplierEstimator
open VerifierDecoding
open scoped BigOperators

def bodyBudget (B q w : Nat) := 16384*(B+q+w+1)^2
private theorem absorbed_range_flatMap {α β : Type} (l : List α) (f : α→List β) :
    (List.range l.length).flatMap (fun j=>(l[j]?).elim [] f)=l.flatMap f:=by
  have h:(List.range l.length).map (fun j=>(l[j]?).elim [] f)=l.map f:=by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp only [List.getElem_map,List.getElem_range]
      rw [List.getElem?_eq_getElem (by simpa using hj)]
      rfl
  simp only [List.flatMap_def,h]

variable {q : Nat} (live : Finset (Fin q)) (y : BitInput live.card)

noncomputable def state (source cache copyBacking out : List Bool) (B w : Nat) : Fin 103 → List Bool :=
  HardwireCacheBody.state live y [] w (HardwireBudget.C w) (HardwireBudget.D q w) (HardwireBudget.E B q)
    source source cache copyBacking out B (HardwireBudget.R B q w)

theorem masters_fit (g : ExactThresholdGate q) (source : List Bool) (B w : Nat)
    (hsource : source.length≤B) (hg : (exactWord g).length≤B) :
    ∀ j,(HardwireCacheBody.masters live y [] w (HardwireBudget.C w) (HardwireBudget.D q w)
      (HardwireBudget.E B q) source j).length≤HardwireBudget.R B q w := by
  have hnew := HardwireBudget.masters_fit live g y [] [] B w
    (by simpa only [List.append_nil] using hg) (by simp)
  have hB : B≤HardwireBudget.R B q w := by
    have square := Nat.le_self_pow (by decide : 2≠0) (B+q+w+1)
    unfold HardwireBudget.R
    omega
  intro j
  by_cases hj : j=0
  · subst j
    exact hsource.trans hB
  · rw [HardwireCacheBody.masters_other live y [] w (HardwireBudget.C w) (HardwireBudget.D q w)
      (HardwireBudget.E B q) source (exactWord g++[]) j hj]
    exact hnew j

theorem body_run (g : ExactThresholdGate q) (pre tail copyBacking oldSource out : List Bool)
    (B w : Nat) (hb : copyBacking.length≤B) (ho : oldSource.length≤B)
    (hg : (exactWord g).length+2≤B) (hw : 0<w)
    (hm : g.target.natAbs+(∑ i,(g.weight i).natAbs)<2^w) :
    Step HardwireCacheBody.machine (bodyBudget B q w) (HardwireCacheBody.heads out pre.length)
      (state live y oldSource (pre++exactWord g++tail) copyBacking out B w)
      (HardwireCacheBody.heads (out++exactWord (C10SupplierRowInput.hardwire live g y))
        (pre.length+(exactWord g).length))
      (state live y (ZeroPadding.pad B (exactWord g)) (pre++exactWord g++tail)
        (ZeroPadding.pad B (DecompositionSource.Records.childSaved g []))
        (out++exactWord (C10SupplierRowInput.hardwire live g y)) B w) := by
  have hword : (exactWord g).length≤B := by omega
  have hpad : (ZeroPadding.pad B (exactWord g)).length≤B := by
    rw [ZeroPadding.pad_length,Nat.max_eq_left hword]
  have htail : (exactWord g++List.replicate (B-(exactWord g).length) false).length≤B := hpad
  have actual := HardwireCacheBody.run live y [] w (HardwireBudget.C w) (HardwireBudget.D q w)
    (HardwireBudget.E B q) g pre tail copyBacking oldSource out B (HardwireBudget.R B q w)
    hb ho hword hw hm le_rfl (HardwireBudget.score_loop live g y w).le
    (HardwireBudget.weight_loop live g _ B htail)
    (masters_fit live y g oldSource B w ho hword)
    (masters_fit live y g (ZeroPadding.pad B (exactWord g)) B w hpad hword)
    (HardwireBudget.reserve live g y _ B w htail hw hm)
  apply actual.enlarge
  have hrun := HardwireBudget.reusable_bound live g y _ B w htail hw hm
  have square := Nat.le_self_pow (by decide : 2≠0) (B+q+w+1)
  unfold HardwireCacheBody.budget C10ThresholdSelectedChild.budget
    HardwireBudget.R HardwireBudget.budget bodyBudget at *
  omega

variable (gs : List (ExactThresholdGate q)) (B w : Nat)

noncomputable def heldSource (j : Nat) :=
  if j=0 then [] else ZeroPadding.pad B (exactWord (gs.getD (j-1) C10SupplierRowInput.falseChild))
noncomputable def heldBacking (j : Nat) :=
  if j=0 then [] else ZeroPadding.pad B
    (DecompositionSource.Records.childSaved (gs.getD (j-1) C10SupplierRowInput.falseChild) [])
def sourcePrefix (j : Nat) := natWord gs.length++(gs.take j).flatMap exactWord
noncomputable def emit (j : Nat) :=
  (gs[j]?).elim [] (fun g=>exactWord (C10SupplierRowInput.hardwire live g y))
noncomputable def entry (j : Nat) (out : List Bool) :=
  Configuration.mk HardwireCacheBody.machine.start (HardwireCacheBody.heads out (sourcePrefix gs j).length)
    (state live y (heldSource gs B j) (exactListWord gs) (heldBacking gs B j) out B w)
noncomputable def machine := CloseoutRowsDegreeLoop.machine HardwireCacheBody.machine
def budget := gs.length*(bodyBudget B q w+3)+3

theorem held_fit (hbytes : ∀ g∈gs,(exactWord g).length+2≤B) (j : Nat) (hj : j≤gs.length) :
    (heldSource gs B j).length≤B ∧ (heldBacking gs B j).length≤B := by
  by_cases hzero : j=0
  · subst j
    exact ⟨Nat.zero_le B,Nat.zero_le B⟩
  · have hprev : j-1<gs.length := by omega
    have hg := hbytes gs[j-1] (List.getElem_mem hprev)
    simp only [heldSource,heldBacking,if_neg hzero,List.getD_eq_getElem _ _ hprev,ZeroPadding.pad_length]
    exact ⟨max_le (Nat.le_refl B) (by omega),max_le (Nat.le_refl B)
      (C10ThresholdSelectedChild.child_saved_fit gs[j-1] B hg)⟩

theorem step (hbytes : ∀ g∈gs,(exactWord g).length+2≤B) (hw : 0<w)
    (hm : ∀ g∈gs,g.target.natAbs+(∑ i,(g.weight i).natAbs)<2^w)
    (j : Nat) (hj : j<gs.length) (out : List Bool) :
    Step HardwireCacheBody.machine (bodyBudget B q w) (entry live y gs B w j out).heads
      (entry live y gs B w j out).tapes
      (entry live y gs B w (j+1) (out++emit live y gs j)).heads
      (entry live y gs B w (j+1) (out++emit live y gs j)).tapes := by
  have hg := hbytes gs[j] (List.getElem_mem hj)
  have mag := hm gs[j] (List.getElem_mem hj)
  obtain ⟨ho,hb⟩ := held_fit gs B hbytes j hj.le
  have hword : exactListWord gs=sourcePrefix gs j++exactWord gs[j]++(gs.drop (j+1)).flatMap exactWord :=
    DecompositionCachedChild.selected_word gs j hj
  have actual := body_run live y gs[j] (sourcePrefix gs j) ((gs.drop (j+1)).flatMap exactWord)
    (heldBacking gs B j) (heldSource gs B j) out B w hb ho hg hw mag
  have hs : heldSource gs B (j+1)=ZeroPadding.pad B (exactWord gs[j]) := by
    simp only [heldSource,show ¬j+1=0 by omega,if_false,Nat.add_sub_cancel,
      List.getD_eq_getElem _ _ hj]
  have hb : heldBacking gs B (j+1)=
      ZeroPadding.pad B (DecompositionSource.Records.childSaved gs[j] []) := by
    simp only [heldBacking,show ¬j+1=0 by omega,if_false,Nat.add_sub_cancel,
      List.getD_eq_getElem _ _ hj]
  have he : emit live y gs j=exactWord (C10SupplierRowInput.hardwire live gs[j] y) := by
    simp only [emit,List.getElem?_eq_getElem hj,Option.elim_some]
  have hp : (sourcePrefix gs (j+1)).length=(sourcePrefix gs j).length+(exactWord gs[j]).length := by
    simp only [sourcePrefix,List.take_succ_eq_append_getElem hj,List.flatMap_append,List.flatMap_singleton,
      List.length_append]
    omega
  simpa only [entry,he,hs,hb,hp,←hword] using actual

theorem run (hbytes : ∀ g∈gs,(exactWord g).length+2≤B) (hw : 0<w)
    (hm : ∀ g∈gs,g.target.natAbs+(∑ i,(g.weight i).natAbs)<2^w) (out : List Bool) :
    ∃ actual,runFrom machine (budget gs B w)
      (RepeatMachine.cfg 0 (entry live y gs B w 0 out) gs.length 1)=some actual ∧
      actual.final=RepeatMachine.cfg 3
        (entry live y gs B w gs.length
          (out++gs.flatMap (fun g=>exactWord (C10SupplierRowInput.hardwire live g y)))) gs.length 1 ∧
      actual.steps≤budget gs B w := by
  have all := CloseoutRowsDegreeLoop.loop_run HardwireCacheBody.machine
    (entry live y gs B w) (emit live y gs) (bodyBudget B q w) gs.length
    (by intro j hj output;rfl) (fun j hj output=>step live y gs B w hbytes hw hm j hj output) out
  have he : (List.range gs.length).flatMap (emit live y gs)=
      gs.flatMap (fun g=>exactWord (C10SupplierRowInput.hardwire live g y)) :=
    absorbed_range_flatMap gs _
  simpa only [machine,budget,he] using all

end NearCubicWires.P1Closure.HardwireCacheLoop
