import Proof.Assembly.RowsPoolWeightChoice

/-! One original coordinate consumes exactly one live-mask bit. Its native
width scratch is retained for the next actual integer. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsPoolWeight
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def advance : Machine 4 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>decide (q=1)
  rule:=fun _ _=>some ⟨1,fun _=>none,fun i=>if i=3 then .right else .stay⟩
noncomputable def body:=Composition.machine choice advance
def bodyBudget (z : ℤ):=DecompositionSource.Fields.cost z+9

theorem advance_run (source backing out mask : List Bool) (pos mpos : ℕ) :
    Step advance 1 (heads pos mpos out) (data source backing out mask)
      (heads pos (mpos+1) out) (data source backing out mask):=by
  have h:step advance ⟨0,heads pos mpos out,data source backing out mask⟩=
      some ⟨1,heads pos (mpos+1) out,data source backing out mask⟩:=by
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;> rfl
    · rfl
  obtain ⟨r,hr,hf,_⟩:=(Timed.single (by rfl) h).run (by rfl)
  exact Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)

theorem body_run (pre tail backing out mpre mtail : List Bool) (z : ℤ) (live : Bool) :
    Step body (bodyBudget z) (heads pre.length mpre.length out)
      (data (pre++intWord z++tail) backing out (mpre++live::mtail))
      (heads (pre.length+(intWord z).length) (mpre.length+1) (out++intWord (transformed live z)))
      (data (pre++intWord z++tail) (DecompositionSource.Fields.saved z backing)
        (out++intWord (transformed live z)) (mpre++live::mtail)):=by
  have selected:=choice_run pre tail backing out (mpre++live::mtail) mpre.length z live
    (Streaming.read_append mpre mtail live)
  have h:=selected.seq (advance_run (pre++intWord z++tail) (DecompositionSource.Fields.saved z backing)
    (out++intWord (transformed live z)) (mpre++live::mtail)
    (pre.length+(intWord z).length) mpre.length)
  have ht:choiceBudget z+1+1=bodyBudget z:=by unfold choiceBudget bodyBudget;omega
  rw [ht] at h
  exact h

theorem body_budget (z : ℤ) : bodyBudget z=(intWord z).length+12:=by
  simp [bodyBudget,DecompositionSource.Fields.cost,DecompositionSource.intWord_length,
    natBitLength,intBitLength]

end NearCubicWires.RepairOrdinary.CloseoutRowsPoolWeight
