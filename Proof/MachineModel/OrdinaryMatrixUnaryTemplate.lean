import Proof.MachineModel.OrdinaryMatrixUnaryLoop

/-! A binary scalar and its physical width are enough to generate a unary
dimension template. Zero initialization, reset capacity, the branch flag,
the initial sentinel and the whole counting loop are actual calls. -/
namespace NearCubicWires.RepairOrdinary.MatrixUnaryTemplate
open LocalBitMultitape RecoveryExecution SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def zero : Machine 7 6 := TapeEmbedding.machine 2 ClockNormalize.machine
def boot : Machine 7 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun q _ => if q.val=0 then some ⟨1,
    fun i => if i=3 ∨ i=6 then some false else none,
    fun i => if i=6 then .right else .stay⟩ else none
def bootOutput (tapes : Fin 7 → List Bool) : Configuration 7 2 :=
  ⟨1,fun i => if i=6 then 1 else 0,
    fun i => if i=3 ∨ i=6 then [false] else tapes i⟩
def prepare : Machine 7 8 := Composition.machine zero boot
def slots : Fin 5 → Fin 7 := ![5,2,3,4,6]
noncomputable def loop := RecoveryFocus.machine slots MatrixUnary.machine
noncomputable def machine := Composition.machine prepare loop
def budget (w n : ℕ) := n*(8*w+10)+8*w+n+17
def input (w n : ℕ) : Fin 7 → List Bool :=
  ![List.replicate w true,[],[],[],[],frame (binary w n),[]]

theorem boot_run (tapes : Fin 7 → List Bool) (h3 : tapes 3=[true]) (h6 : tapes 6=[]) :
    ∃ r : ExecutionReceipt 7 2, run boot 1 tapes=some r ∧
      r.final=bootOutput tapes ∧ r.steps=1 := by
  have hs : step boot (initialConfiguration boot tapes)=some (bootOutput tapes) := by
    simp [step,boot,initialConfiguration]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply,bootOutput]
    · funext i; fin_cases i <;> simp [applyAction,bootOutput,h3,h6,writeTapeBit]
  exact (Timed.single (by rfl) hs).run (by rfl)

theorem template_run (w n : ℕ) (hn : n<2^w) :
    ∃ r : ExecutionReceipt 7 (8+Fintype.card (RecoveryCalls.Control MatrixUnary.sizes)),
      run machine (budget w n) (input w n)=some r ∧
      r.final.tapes 0=List.replicate w true ∧
      r.final.tapes 5=frame (binary w n) ∧
      r.final.tapes 6=UnaryTemplate.tape n ∧ r.final.heads 6=1 ∧
      (∀ i, i≠6 → r.final.heads i=0) ∧ r.steps≤budget w n := by
  obtain ⟨base,hr,h0,_,h2,h3,h4,hh,hs⟩ := ClockScalarFields.zero_run w
  let extras : Fin 2 → List Bool := ![frame (binary w n),[]]
  let z := TapeEmbedding.receipt (fun _ : Fin 2 => 0) extras base
  have hz := TapeEmbedding.run_embed ClockNormalize.machine (fun _ : Fin 2 => 0) extras _ _ base hr
  have hzhead : ∀ i, z.final.heads i=0 := by
    intro i; fin_cases i <;> simp [z,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases,hh]
  have hz0 : z.final.tapes 0=List.replicate w true := h0
  have hz2 : z.final.tapes 2=frame (binary w 0) := h2
  have hz3 : z.final.tapes 3=[true] := h3
  have hz4 : z.final.tapes 4=List.replicate (2*w+1) false := h4
  have hz5 : z.final.tapes 5=frame (binary w n) := rfl
  have hz6 : z.final.tapes 6=[] := rfl
  obtain ⟨b,hb,hbf,hbs⟩ := boot_run z.final.tapes hz3 hz6
  have hbridge : Composition.restart z.final boot.start=initialConfiguration boot z.final.tapes := by
    apply configuration_ext
    · rfl
    · exact funext hzhead
    · rfl
  have hb' : runFrom boot 1 (Composition.restart z.final boot.start)=some b := by rw [hbridge]; exact hb
  have hp := Composition.run_join zero boot (4*w+4) 1 _ z b hz hb'
  let p := Composition.joinedReceipt z b
  have hphead : p.final.heads=fun i => if i=6 then 1 else 0 := by change b.final.heads=_; rw [hbf]; rfl
  have hptape : p.final.tapes=fun i => if i=3 ∨ i=6 then [false] else z.final.tapes i := by
    change b.final.tapes=_; rw [hbf]; rfl
  obtain ⟨localRun,hl,hlf,hls⟩ := MatrixUnary.loop_run w n hn
  let entry := MatrixUnary.boundary 0 w n 0 0 false
  have hi : RecoveryFocus.config slots p.final.heads p.final.tapes entry =
      Composition.restart p.final loop.start := by
    apply WilliamsSourceCrop.focus_same
    · intro i
      rw [hphead]
      fin_cases i <;> simp [slots,entry,MatrixUnary.boundary,controlConfig,MatrixUnary.config]
    · intro i
      rw [hptape]
      fin_cases i <;> simp [slots,entry,MatrixUnary.boundary,controlConfig,MatrixUnary.config,hz2,hz4,hz5]
  obtain ⟨focused,hfocus,hff,hfs⟩ := RecoveryFocus.run_config slots (by decide) MatrixUnary.machine
    p.final.heads p.final.tapes _ entry localRun hl
  rw [hi] at hfocus
  have hj := Composition.run_join prepare loop (4*w+4+1+1)
    (n*(8*w+10)+4*w+n+10) _ p focused hp hfocus
  have htime : 4*w+4+1+1+1+(n*(8*w+10)+4*w+n+10)=budget w n := by unfold budget; omega
  rw [htime] at hj
  have hinput : Composition.leftConfig _
      (Composition.leftConfig 2 (TapeEmbedding.config (fun _ : Fin 2 => 0) extras
        (initialConfiguration ClockNormalize.machine (ClockScalarFields.zeroInput w)))) =
      initialConfiguration machine (input w n) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [hinput] at hj
  have hpick : ∀ i : Fin 7, RecoveryFocus.pick slots i =
      (![none,none,some 1,some 2,some 3,some 0,some 4] : Fin 7 → Option (Fin 5)) i := by
    intro i; fin_cases i
    · decide
    · decide
    · exact RecoveryFocus.pick_slot slots (by decide) 1
    · exact RecoveryFocus.pick_slot slots (by decide) 2
    · exact RecoveryFocus.pick_slot slots (by decide) 3
    · exact RecoveryFocus.pick_slot slots (by decide) 0
    · exact RecoveryFocus.pick_slot slots (by decide) 4
  refine ⟨Composition.joinedReceipt p focused,hj,?_,?_,?_,?_,?_,?_⟩
  · change focused.final.tapes 0=_
    rw [hff,hlf]
    simp [RecoveryFocus.config,hpick,hptape,hz0]
  · change focused.final.tapes 5=_
    rw [hff,hlf]
    simp [RecoveryFocus.config,hpick,MatrixUnary.result,RecoveryCalls.stopped,MatrixUnary.finished]
  · change focused.final.tapes 6=_
    rw [hff,hlf]
    simp [RecoveryFocus.config,hpick,MatrixUnary.result,RecoveryCalls.stopped,MatrixUnary.finished]
  · change focused.final.heads 6=1
    rw [hff,hlf]
    simp [RecoveryFocus.config,hpick,MatrixUnary.result,RecoveryCalls.stopped,MatrixUnary.finished]
  · intro i hi6
    change focused.final.heads i=0
    rw [hff,hlf]
    fin_cases i <;> simp [RecoveryFocus.config,hpick,hphead,MatrixUnary.result,RecoveryCalls.stopped,MatrixUnary.finished] at *
  · change z.steps+1+b.steps+1+focused.steps≤_
    rw [hbs,hfs]
    have hzsteps : z.steps=4*w+4 := hs
    rw [hzsteps]
    unfold budget
    omega

end NearCubicWires.RepairOrdinary.MatrixUnaryTemplate
