import Proof.PCP.PCPPNativeClauseDriverEntry

/-! Raw shared C/M counters feed the whole original compact clause loop.
The same emitted nodes and live cursors are returned by one fixed machine. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeClauseRawRun
open LocalBitMultitape SourceInterfaces RepairSource PCPPNativeClauseLoop
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots (i : Fin 52) : Fin 58 := i.castAdd 6
theorem slots_injective : Function.Injective slots := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 58=>k.val) h)
noncomputable def last := RecoveryFocus.machine slots PCPPNativeClauseLoop.machine
noncomputable def machine := Composition.machine PCPPNativeClauseDriverEntry.machine last
def budget (C M : ℕ) := PCPPNativeClauseDrivers.budget C M+1+(M*(48*C+131)+3)
noncomputable def entry (source : List Bool) (pos stride p n C base accumulator : ℕ) (out : List Bool) (M : ℕ) :=
  (⟨machine.start,PCPPNativeClauseDriverEntry.heads source pos stride p n C base accumulator out M,
    PCPPNativeClauseDriverEntry.input source pos stride p n C base accumulator out M⟩ : Configuration 58 _)

theorem original_run {n q : ℕ} (r W C : ℕ) (oracle : BooleanCircuit n)
    (clauses : List (Fin 3→Literal q)) (pre suffix out : List Bool)
    (hstride : 2*oracle.size+1≤W) (hsize : q*(2*oracle.size+1)+3*clauses.length+1≤W)
    (hbytes : (sourceFields clauses).length≤W) (hC : 16384*(W+1)^2≤C) :
    ∃ result,runFrom machine (budget C clauses.length)
      (entry (pre++sourceFields clauses++suffix) pre.length (2*oracle.size+1) (2*oracle.output.val+1)
        (2*oracle.size) C (q*(2*oracle.size+1)+1) (q*(2*oracle.size+1)) out clauses.length)=some result ∧
      result.final.tapes 47=out++(PCPPNative.clauseStreamNodes (r:=r)
        (q*(2*oracle.size+1)+1) (q*(2*oracle.size+1)) (PCPPNative.literalAddress oracle) clauses).flatMap PCPPRequestNodeSchema.native ∧
      result.final.heads 47=(out++(PCPPNative.clauseStreamNodes (r:=r)
        (q*(2*oracle.size+1)+1) (q*(2*oracle.size+1)) (PCPPNative.literalAddress oracle) clauses).flatMap PCPPRequestNodeSchema.native).length ∧
      result.final.heads 13=(pre++sourceFields clauses).length ∧
      result.steps≤budget C clauses.length := by
  obtain ⟨a,ar,as,af⟩:=PCPPNativeClauseDriverEntry.prepare_run (pre++sourceFields clauses++suffix)
    pre.length (2*oracle.size+1) (2*oracle.output.val+1) (2*oracle.size) C
    (q*(2*oracle.size+1)+1) (q*(2*oracle.size+1)) out clauses.length
  obtain ⟨b,br,bh,bt,bs⟩:=PCPPNativeClauseCold.template_run r W C oracle clauses pre suffix out hstride hsize hbytes hC
  obtain ⟨c,cr,_,cs,ch,ct,_⟩:=RecoveryFocus.dock slots slots_injective PCPPNativeClauseLoop.machine _
    a.final.heads a.final.tapes _ (fun i=>(af i).1) (fun i=>(af i).2) b br
  have joined:=Composition.run_join PCPPNativeClauseDriverEntry.machine last _ _ _ a c ar cr
  refine ⟨Composition.joinedReceipt a c,joined,?_,?_,?_,?_⟩
  · change c.final.tapes 47=_
    exact (ct 47).trans bt
  · change c.final.heads 47=_
    exact (ch 47).trans (congrFun bh 47)
  · change c.final.heads 13=_
    exact (ch 13).trans (congrFun bh 13)
  · change a.steps+1+c.steps≤budget C clauses.length
    rw [cs,as]
    exact Nat.add_le_add_left bs _

end NearCubicWires.RepairOrdinary.PCPPNativeClauseRawRun
