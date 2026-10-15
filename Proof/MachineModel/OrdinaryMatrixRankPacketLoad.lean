import Proof.MachineModel.OrdinaryMatrixBatchRankReverse

/-! Copy one complete ranked gate packet from a streaming global source,
then restore only the local target. The extra false terminator is physically
copied and consumed, so the source is positioned at the next gate packet. -/
namespace NearCubicWires.RepairOrdinary.MatrixRankPacketLoad
open LocalBitMultitape RecoveryExecution MatrixBatchRankAppend
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def terminate : Machine 2 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun _ _ => some ⟨1,![none,some false],![.right,.right]⟩
def packetMachine := Composition.machine copyMachine terminate
def packetInput (words : List (List Bool)) (pre suffix : List Bool) :=
  Composition.leftConfig 2 (MatrixBatchRankAppend.cfg (RecordController.test 3)
    (pre++stream words++suffix) pre.length [])

theorem packet_run (words : List (List Bool)) (pre suffix : List Bool)
    (hn : ∀ w∈words,w≠[]) :
    ∃ actual,runFrom packetMachine (packetBudget words) (packetInput words pre suffix)=some actual ∧
      actual.final.heads=![pre.length+(stream words).length,(stream words).length] ∧
      actual.final.tapes=![pre++stream words++suffix,stream words] ∧ actual.steps=packetBudget words := by
  obtain ⟨base,hb,bf,bs⟩ := (copy_prefix words pre suffix [] hn).run (by rfl)
  simp only [List.nil_append] at bf
  let source := pre++stream words++suffix
  let entry : Configuration 2 2 :=
    ⟨0,![pre.length+(fields words).length,(fields words).length],![source,fields words]⟩
  let final : Configuration 2 2 :=
    ⟨1,![pre.length+(stream words).length,(stream words).length],![source,stream words]⟩
  have hs : step terminate entry=some final := by
    simp [step,terminate,entry]
    apply configuration_ext
    · rfl
    · funext i
      fin_cases i <;> simp [applyAction,HeadMove.apply,final,stream,List.length_append,Nat.add_assoc]
    · funext i
      fin_cases i
      · rfl
      · change writeTapeBit (fields words) (fields words).length false=stream words
        exact Streaming.write_append _ _
  obtain ⟨last,hl,lf,ls⟩ := (Timed.single (by rfl) hs).run (by rfl)
  have he : Composition.restart base.final terminate.start=entry := by rw [bf]; rfl
  rw [←he] at hl
  have joined := Composition.run_join copyMachine terminate _ _ _ base last hb hl
  refine ⟨Composition.joinedReceipt base last,joined,?_,?_,?_⟩
  · change last.final.heads=_
    rw [lf]
  · change last.final.tapes=_
    rw [lf]
  · change base.steps+1+last.steps=_
    rw [bs,ls]
    unfold packetBudget
    omega

def selected (i : Fin 2) : Bool := decide (i=1)
def machine := MaskedReset.machine packetMachine selected
def input (words : List (List Bool)) (pre suffix : List Bool) :=
  Rewind.recording (packetInput words pre suffix) 0
def budget (words : List (List Bool)) := 2*packetBudget words+2

theorem load_run (words : List (List Bool)) (pre suffix : List Bool) (hn : ∀ w∈words,w≠[]) :
    ∃ actual,runFrom machine (budget words) (input words pre suffix)=some actual ∧
      actual.final.heads=![pre.length+(stream words).length,0,0] ∧
      actual.final.tapes=![pre++stream words++suffix,stream words,List.replicate (packetBudget words) false] ∧
      actual.steps=budget words := by
  obtain ⟨base,hb,bh,bt,bs⟩ := packet_run words pre suffix hn
  have hh : ∀ i,selected i=true → base.final.heads i ≤ base.steps := by
    intro i hi
    have he : i=1 := by simpa [selected] using hi
    subst i
    rw [bh,bs]
    change (stream words).length ≤ packetBudget words
    simp only [stream,List.length_append,List.length_singleton,packetBudget]
    omega
  obtain ⟨actual,ha,haf,has,_⟩ := MaskedReset.reset_run packetMachine selected _ _ base hb hh
  rw [bs] at ha has
  refine ⟨actual,ha,?_,?_,has⟩
  · rw [haf,bh]
    funext i
    fin_cases i <;> rfl
  · rw [haf,bt,bs]
    funext i
    fin_cases i <;> rfl

def paddedInput (cap : ℕ) (words : List (List Bool)) (pre suffix : List Bool) :=
  ZeroPadding.config (![0,cap,cap] : Fin 3 → ℕ) (input words pre suffix)

theorem padded_heads (cap : ℕ) (words : List (List Bool)) (pre suffix : List Bool) :
    (paddedInput cap words pre suffix).heads=![pre.length,0,0] := by
  funext i
  fin_cases i <;> rfl

theorem padded_tapes (cap : ℕ) (words : List (List Bool)) (pre suffix : List Bool) :
    (paddedInput cap words pre suffix).tapes=
      ![pre++stream words++suffix,List.replicate cap false,List.replicate cap false] := by
  funext i
  fin_cases i <;> simp [paddedInput,ZeroPadding.config,ZeroPadding.pad,input,Rewind.recording,Rewind.config,
    packetInput,Composition.leftConfig,MatrixBatchRankAppend.cfg,Fin.addCases]

theorem padded_run (cap : ℕ) (words : List (List Bool)) (pre suffix : List Bool)
    (hn : ∀ w∈words,w≠[]) (hc : packetBudget words ≤ cap) :
    ∃ actual,runFrom machine (budget words) (paddedInput cap words pre suffix)=some actual ∧
      actual.final.heads=![pre.length+(stream words).length,0,0] ∧
      actual.final.tapes=![pre++stream words++suffix,ZeroPadding.pad cap (stream words),List.replicate cap false] ∧
      actual.steps=budget words := by
  obtain ⟨base,hb,bh,bt,bs⟩ := load_run words pre suffix hn
  obtain ⟨actual,ha,haf,has,_⟩ := ZeroPadding.run_config machine (![0,cap,cap] : Fin 3 → ℕ) _ _ base hb
  refine ⟨actual,ha,?_,?_,has.trans bs⟩
  · rw [haf]
    exact bh
  · rw [haf]
    simp only [ZeroPadding.config,bt]
    funext i
    fin_cases i
    · exact ZeroPadding.pad_zero _
    · rfl
    · change ZeroPadding.pad cap (List.replicate (packetBudget words) false)=List.replicate cap false
      simp [ZeroPadding.pad,Nat.add_sub_of_le hc]

end NearCubicWires.RepairOrdinary.MatrixRankPacketLoad
