import Proof.Hierarchy.CompetitorPlaneColdClear

/-! Complete cold signed-plane pass from native counts, old raw P/N pairs,
one physical factor/width/capacity/count set and blank work tapes. The final
global rewind is paid once for the complete plane. -/
namespace NearCubicWires.RepairOrdinary.CompetitorPlaneEntry
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open RepairSource.VerifierDecoding CompetitorPlaneStream CompetitorPlaneWorkspace
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def outerSlots (j : Fin 27) : Fin 28 := j.castAdd 1
def extendTapes (tapes : Fin 27 → List Bool) (n : ℕ) : Fin 28 → List Bool :=
  Fin.addCases (m := 27) (n := 1) (motive := fun _ => List Bool) tapes (fun _ => CompareMachine.word n)
def input (b w : ℕ) (bits : List Bool) (xs : List Cell) :=
  extendTapes (coldInput b w bits (countWords b xs) (oldWords w xs)) xs.length
noncomputable def bootProgram := RecoveryFocus.machine outerSlots (clearProgram workSlot)
def loopHeads : Fin 28 → ℕ := fun i => if i.val=27 then 1 else 0
def enter : Machine 28 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun q _ => if q.val=0 then
    some ⟨1,fun _ => none,fun i => if i.val=27 then .right else .stay⟩ else none
noncomputable def tailProgram (sign : Bool) := Composition.machine enter (planeProgram sign)
noncomputable def program (sign : Bool) := Composition.machine bootProgram (tailProgram sign)
def budget (w n : ℕ) := planeBudget w n+2*CompetitorPlane.capacity w+7

theorem outer_injective : Function.Injective outerSlots := by
  intro i j h
  exact Fin.ext (congrArg (fun a : Fin 28 => a.val) h)

theorem boot_run (b w : ℕ) (bits : List Bool) (xs : List Cell) :
    ClockJoin.ReadyRun bootProgram (2*CompetitorPlane.capacity w+4) (input b w bits xs)
      (extendTapes (zeroed b w bits (countWords b xs) (oldWords w xs)) xs.length) := by
  have hin : ∀ j,input b w bits xs (outerSlots j)=coldInput b w bits (countWords b xs) (oldWords w xs) j := by
    simp [input,extendTapes,outerSlots]
  have hf := CompetitorRationalProducts.bounded_focus outerSlots outer_injective _ _ _
    (cold_clear_run b w bits (countWords b xs) (oldWords w xs)) (input b w bits xs) hin
  have he : install outerSlots (input b w bits xs) (zeroed b w bits (countWords b xs) (oldWords w xs))=
      extendTapes (zeroed b w bits (countWords b xs) (oldWords w xs)) xs.length := by
    funext i
    refine Fin.addCases (m := 27) (n := 1) ?_ ?_ i
    · intro j
      simp only [extendTapes,Fin.addCases_left]
      change install outerSlots _ _ (outerSlots j)=_
      exact install_slot outerSlots outer_injective _ _ j
    · intro j
      fin_cases j
      apply install_other
      intro k hk
      have hv := congrArg (fun a : Fin 28 => a.val) hk
      change k.val=27 at hv
      omega
  rw [he] at hf
  exact hf

theorem enter_run (tapes : Fin 28 → List Bool) :
    ∃ r : ExecutionReceipt 28 2,run enter 1 tapes=some r ∧ r.final=⟨1,loopHeads,tapes⟩ ∧ r.steps=1 := by
  have hstep : step enter (initialConfiguration enter tapes)=some (⟨1,loopHeads,tapes⟩ : Configuration 28 2) := by
    simp [step,enter,initialConfiguration]
    apply configuration_ext
    · rfl
    · funext i
      by_cases hi : i.val=27 <;> simp [applyAction,loopHeads,hi,HeadMove.apply]
    · rfl
  exact (Timed.single (by rfl) hstep).run (by rfl)

theorem cold_plane_run (sign : Bool) (b w : ℕ) (bits : List Bool) (xs : List Cell)
    (hb : b≤w) (hbits : bits.length≤w) (hv : ∀ a∈xs,a.Valid sign b w bits) :
    ∃ r out,run (program sign) (budget w xs.length) (input b w bits xs)=some r ∧
      r.steps≤budget w xs.length ∧ r.final.tapes=extendTapes out xs.length ∧
      Store b w bits (countWords b xs) (oldWords w xs) (newWords sign w bits xs) out := by
  obtain ⟨boot,hboot,hbt,hbh,hbs⟩ := boot_run b w bits xs
  let startTapes := zeroed b w bits (countWords b xs) (oldWords w xs)
  obtain ⟨start,hstart,hstartf,hstarts⟩ := enter_run (extendTapes startTapes xs.length)
  obtain ⟨loop,out,hloop,hloops,hloopf,hout⟩ := plane_run sign b w bits xs startTapes hb hbits hv
    (zeroed_store b w bits (countWords b xs) (oldWords w xs))
  have heLoop : Composition.restart start.final (planeProgram sign).start=
      RepeatMachine.cfg 0 (cfg (bodyProgram sign).start 0 0 0 startTapes) xs.length 1 := by
    rw [hstartf]
    apply configuration_ext
    · rfl
    · funext i
      refine Fin.addCases (m := 27) (n := 1) ?_ ?_ i
      · intro j
        have hj : j.val≠27 := by omega
        simp [Composition.restart,loopHeads,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,cfg,heads,hj]
      · intro j
        fin_cases j
        rfl
    · rfl
  have hl' : runFrom (planeProgram sign) (planeBudget w xs.length)
      (Composition.restart start.final (planeProgram sign).start)=some loop := by rw [heLoop]; exact hloop
  have htail := Composition.run_join enter (planeProgram sign) _ _ _ start loop hstart hl'
  let tail := Composition.joinedReceipt start loop
  have heStart : Composition.restart boot.final (tailProgram sign).start=
      Composition.leftConfig _ (initialConfiguration enter (extendTapes startTapes xs.length)) := by
    apply configuration_ext
    · rfl
    · funext i
      exact hbh i
    · exact hbt
  have ht' : runFrom (tailProgram sign) (1+1+planeBudget w xs.length)
      (Composition.restart boot.final (tailProgram sign).start)=some tail := by rw [heStart]; exact htail
  have hall := Composition.run_join bootProgram (tailProgram sign) _ _ _ boot tail hboot ht'
  have hcost : (2*CompetitorPlane.capacity w+4)+1+(1+1+planeBudget w xs.length)=budget w xs.length := by unfold budget; omega
  rw [hcost] at hall
  refine ⟨Composition.joinedReceipt boot tail,out,hall,?_,?_,hout⟩
  · change boot.steps+1+(start.steps+1+loop.steps)≤budget w xs.length
    omega
  · change loop.final.tapes=extendTapes out xs.length
    rw [hloopf]
    rfl

noncomputable def machine (sign : Bool) := Rewind.machine (program sign)
def readyInput (b w : ℕ) (bits : List Bool) (xs : List Cell) : Fin 29 → List Bool :=
  Fin.addCases (m := 28) (n := 1) (motive := fun _ => List Bool) (input b w bits xs) (fun _ => [])
def readyBudget (w n : ℕ) := 2*budget w n+2

theorem ready_plane_run (sign : Bool) (b w : ℕ) (bits : List Bool) (xs : List Cell)
    (hb : b≤w) (hbits : bits.length≤w) (hv : ∀ a∈xs,a.Valid sign b w bits) :
    ∃ out,ClockJoin.ReadyRun (machine sign) (readyBudget w xs.length) (readyInput b w bits xs) out ∧
      out 17=newWords sign w bits xs ∧ out 18=countWords b xs ∧ out 19=oldWords w xs ∧
      out 0=frame bits ∧ out 9=List.replicate w true ∧ out 20=List.replicate b true ∧
      out 27=CompareMachine.word xs.length := by
  obtain ⟨base,store,hr,hs,ht,hstore⟩ := cold_plane_run sign b w bits xs hb hbits hv
  obtain ⟨r,hrun,hrt,hrh,hrs,_⟩ := Rewind.reset_run (program sign) _ _ base hr
  have hc : 2*base.steps+2≤readyBudget w xs.length := by unfold readyBudget; omega
  have hmore := runFrom_moreFuel (machine sign) _ (readyBudget w xs.length-(2*base.steps+2)) _ r hrun
  rw [Nat.add_sub_of_le hc] at hmore
  refine ⟨r.final.tapes,⟨r,hmore,rfl,hrh,by omega⟩,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (hrt 17).trans (congrFun ht 17) |>.trans hstore.output
  · exact (hrt 18).trans (congrFun ht 18) |>.trans hstore.counts
  · exact (hrt 19).trans (congrFun ht 19) |>.trans hstore.old
  · exact (hrt 0).trans (congrFun ht 0) |>.trans hstore.factor
  · exact (hrt 9).trans (congrFun ht 9) |>.trans hstore.width
  · exact (hrt 20).trans (congrFun ht 20) |>.trans hstore.nativeWidth
  · exact (hrt 27).trans (congrFun ht 27)

end NearCubicWires.RepairOrdinary.CompetitorPlaneEntry
