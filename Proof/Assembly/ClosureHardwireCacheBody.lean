import Proof.Assembly.ClosureHardwireReusable
import Proof.Assembly.FinalThresholdSelectedChild

/-! One physical A.12 child-cache step: copy the next native child into the
source master, restore the working bank, append its hardwired word, restore
the bank again. The input cache cursor advances once; all state is explicit.
-/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.HardwireCacheBody
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch RecoveryRootRound
open RepairRepresentation RepairSource CloseoutFinal SupplierPipeline SupplierEstimator
open scoped BigOperators

variable {q : Nat} (live : Finset (Fin q)) (y : BitInput live.card)
  (backing : List Bool) (w C D E : Nat)

noncomputable def native (source out : List Bool) : Fin 48 → List Bool :=
  Fin.addCases (motive:=fun _=>List Bool)
    (C10NaturalHardwireScoreInputs.data source
      (List.ofFn (C10NaturalHardwireScore.frozenMask live y)) out w C D q 0 0)
    (HardwireChild.extra backing (CloseoutRowsGateSupport.gateMembers live) q E)
noncomputable def masters (source : List Bool) : Fin 47 → List Bool :=
  fun j=>native live y backing w C D E source [] (HardwireReusable.work j)
noncomputable def padded (source out : List Bool) (R : Nat) : Fin 48 → List Bool :=
  fun i=>ZeroPadding.pad (HardwireReusable.caps R i) (native live y backing w C D E source out i)
noncomputable def localState (source masterSource out : List Bool) (R : Nat) : Fin 98 → List Bool :=
  HardwireReusable.state (padded live y backing w C D E source out R)
    (masters live y backing w C D E masterSource) R

def extra (cache copyBacking : List Bool) (q B : Nat) : Fin 5 → List Bool :=
  ![cache,copyBacking,UnaryTemplate.tape q,List.replicate B true,List.replicate (B+1) false]
def heads (out : List Bool) (pos : Nat) : Fin 103 → Nat :=
  Fin.addCases (motive:=fun _=>Nat) (HardwireReusable.heads out 1) (![pos,0,1,0,0] : Fin 5 → Nat)
noncomputable def state (source masterSource cache copyBacking out : List Bool) (B R : Nat) :
    Fin 103 → List Bool :=
  Fin.addCases (motive:=fun _=>List Bool) (localState live y backing w C D E source masterSource out R)
    (extra cache copyBacking q B)

def copySlots : Fin 6 → Fin 103 := ![98,99,48,100,101,102]
theorem copySlots_injective : Function.Injective copySlots := by decide
noncomputable def copy := RecoveryFocus.machine copySlots C10ThresholdSelectedChild.machine
noncomputable def reload := Composition.machine
  (Composition.machine (HardwireReusable.move false) HardwireReusable.restore) (HardwireReusable.move true)
noncomputable def worker := Composition.machine reload HardwireReusable.machine
noncomputable def machine := Composition.machine copy (TapeEmbedding.machine 5 worker)
noncomputable def budget (g : ExactThresholdGate q) (B R : Nat) :=
  C10ThresholdSelectedChild.budget g B+1+(4*R+14+HardwireReusable.budget live g y w C R)

theorem copy_heads (out : List Bool) (pos next : Nat) :
    dockH copySlots (heads out pos) (C10ThresholdSelectedChild.heads next 0)=heads out next := by
  funext i
  fin_cases i <;> first
    | exact dockH_slot copySlots copySlots_injective _ _ 0
    | exact dockH_slot copySlots copySlots_injective _ _ 1
    | exact dockH_slot copySlots copySlots_injective _ _ 2
    | exact dockH_slot copySlots copySlots_injective _ _ 3
    | exact dockH_slot copySlots copySlots_injective _ _ 4
    | exact dockH_slot copySlots copySlots_injective _ _ 5
    | exact dockH_other copySlots _ _ _ (by decide)

theorem padded_work (source out : List Bool) (R : Nat) (j : Fin 47) :
    padded live y backing w C D E source out R (HardwireReusable.work j)=
      ZeroPadding.pad R (masters live y backing w C D E source j) := by
  fin_cases j <;> rfl

theorem masters_other (source other : List Bool) (j : Fin 47) (hj : j≠0) :
    masters live y backing w C D E source j=masters live y backing w C D E other j := by
  fin_cases j <;> first | rfl | exact False.elim (hj rfl)

theorem state_other (source oldMaster newMaster cache oldBacking newBacking out : List Bool)
    (B R : Nat) (i : Fin 103) (h48 : i≠48) (h99 : i≠99) :
    state live y backing w C D E source oldMaster cache oldBacking out B R i=
      state live y backing w C D E source newMaster cache newBacking out B R i := by
  revert h48 h99
  refine Fin.addCases (m:=98) (n:=5) (fun j=>?_) (fun j=>?_) i
  · refine Fin.addCases (m:=48) (n:=50) (fun j=>?_) (fun j=>?_) j
    · intro _ _
      simp only [state,localState,HardwireReusable.state,Fin.addCases_left]
    · refine Fin.addCases (m:=47) (n:=3) (fun j=>?_) (fun j=>?_) j
      · intro h48 _
        simp only [state,localState,HardwireReusable.state,Fin.addCases_left,Fin.addCases_right]
        exact masters_other live y backing w C D E oldMaster newMaster j (by
          intro hj
          subst j
          exact h48 rfl)
      · intro _ _
        simp only [state,localState,HardwireReusable.state,Fin.addCases_left,Fin.addCases_right]
  · intro _ h99
    simp only [state,Fin.addCases_right]
    fin_cases j <;> first | rfl | exact False.elim (h99 rfl)

theorem reload_run (oldSource newSource out : List Bool) (R : Nat)
    (hold : ∀ j,(masters live y backing w C D E oldSource j).length≤R)
    (hnew : ∀ j,(masters live y backing w C D E newSource j).length≤R) :
    Step reload (4*R+13) (HardwireReusable.heads out 1)
      (localState live y backing w C D E oldSource newSource out R)
      (HardwireReusable.heads out 1) (localState live y backing w C D E newSource newSource out R) := by
  have restore := HardwireReusable.restore_run
    (padded live y backing w C D E oldSource out R)
    (padded live y backing w C D E newSource out R)
    (masters live y backing w C D E newSource) out R hnew
    (by intro j;rw [padded_work,ZeroPadding.pad_length,Nat.max_eq_left (hold j)])
    (padded_work live y backing w C D E newSource out R) rfl
  have joined := ((HardwireReusable.move_run false out _).seq restore).seq
    (HardwireReusable.move_run true out _)
  convert joined using 1 <;> first | rfl | omega

theorem copy_run (g : ExactThresholdGate q) (pre tail copyBacking oldSource out : List Bool)
    (B R : Nat) (hb : copyBacking.length≤B) (ho : oldSource.length≤B)
    (hg : (exactWord g).length≤B) :
    Step copy (C10ThresholdSelectedChild.budget g B) (heads out pre.length)
      (state live y backing w C D E oldSource oldSource (pre++exactWord g++tail) copyBacking out B R)
      (heads out (pre.length+(exactWord g).length))
      (state live y backing w C D E oldSource (ZeroPadding.pad B (exactWord g))
        (pre++exactWord g++tail) (ZeroPadding.pad B (DecompositionSource.Records.childSaved g [])) out B R) := by
  have actual := (C10ThresholdSelectedChild.run g pre tail copyBacking oldSource B 0 hb ho (Nat.zero_le B) hg).focus
    copySlots copySlots_injective (heads out pre.length)
    (state live y backing w C D E oldSource oldSource (pre++exactWord g++tail) copyBacking out B R)
  refine (actual.congr_in
    (dockH_existing copySlots _ _ (by intro j;fin_cases j <;> rfl))
    (install_existing copySlots _ _ (by intro j;fin_cases j <;> rfl))).congr ?_ ?_
  · exact copy_heads _ _ _
  · apply HierarchyAllocation.install_eq copySlots copySlots_injective
    · intro j;fin_cases j <;> rfl
    · intro i hi
      exact (state_other live y backing w C D E oldSource oldSource (ZeroPadding.pad B (exactWord g))
        (pre++exactWord g++tail) copyBacking (ZeroPadding.pad B (DecompositionSource.Records.childSaved g []))
        out B R i (Ne.symm (hi 2)) (Ne.symm (hi 1))).symm

theorem run (g : ExactThresholdGate q) (pre tail copyBacking oldSource out : List Bool)
    (B R : Nat) (hb : copyBacking.length≤B) (ho : oldSource.length≤B)
    (hg : (exactWord g).length≤B) (hw : 0<w)
    (hm : g.target.natAbs+(∑ i,(g.weight i).natAbs)<2^w) (hc : 8*w+12≤C)
    (hD : C10NaturalHardwireScore.loopBudget (C10NaturalHardwireScore.items live g y) w C≤D)
    (hE : C10NaturalHardwireWeights.loopBudget (C10NaturalHardwireWeights.gateItems g live)≤E)
    (hold : ∀ j,(masters live y backing w C D E oldSource j).length≤R)
    (hnew : ∀ j,(masters live y backing w C D E (ZeroPadding.pad B (exactWord g)) j).length≤R)
    (hR : HardwireChild.budget live g y w C+2≤R) :
    Step machine (budget live y w C g B R) (heads out pre.length)
      (state live y backing w C D E oldSource oldSource (pre++exactWord g++tail) copyBacking out B R)
      (heads (out++exactWord (C10SupplierRowInput.hardwire live g y)) (pre.length+(exactWord g).length))
      (state live y backing w C D E (ZeroPadding.pad B (exactWord g)) (ZeroPadding.pad B (exactWord g))
        (pre++exactWord g++tail) (ZeroPadding.pad B (DecompositionSource.Records.childSaved g []))
        (out++exactWord (C10SupplierRowInput.hardwire live g y)) B R) := by
  have first := copy_run live y backing w C D E g pre tail copyBacking oldSource out B R hb ho hg
  have reset := reload_run live y backing w C D E oldSource (ZeroPadding.pad B (exactWord g)) out R hold hnew
  have child := HardwireReusable.run live g y (List.replicate (B-(exactWord g).length) false)
    backing w C D E out R hw hm hc hD hE hnew hR
  have joined := (reset.seq child).embed (![pre.length+(exactWord g).length,0,1,0,0] : Fin 5 → Nat)
    (extra (pre++exactWord g++tail) (ZeroPadding.pad B (DecompositionSource.Records.childSaved g [])) q B)
  exact first.seq joined

end NearCubicWires.P1Closure.HardwireCacheBody
