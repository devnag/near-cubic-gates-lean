import Proof.CaseAnalysis.WitnessDAGFields

/-! Reuse the accepted scalar test on the retained padded arity and final
node counter. Zero padding changes no transition or cost. The original
output payload is compared as a binary value, including malformed guesses. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.DAGOutput
open LocalBitMultitape RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def caps (cap : ℕ) (i : Fin 21) : ℕ:=if i.val<4 then cap else 0
def input (cap w : ℕ) (left right bits : List Bool) (i : Fin 21) : List Bool:=
  ZeroPadding.pad (caps cap i) (NodeScalar.input w left right bits i)

theorem compare_run (cap w : ℕ) (left right bits : List Bool)
    (hl : left.length=w) (hr : right.length=w) (hb : bits.length≤w) : ∃ out,
    ClockJoin.ReadyRun NodeScalar.machine (NodeScalar.budget w) (input cap w left right bits) out ∧
      out 19=[decide (value right≤value bits)] ∧
      (∀ i : Fin 5,out (i.castAdd 16)=input cap w left right bits (i.castAdd 16)):=by
  obtain ⟨base,⟨r,hrun,rt,rh,rs⟩,h0,h1,h2,h3,h4,_,_,_,h19⟩:=NodeScalar.scalar_run w left right bits hl hr hb
  obtain ⟨a,ha,af,ast,_⟩:=ZeroPadding.run_config NodeScalar.machine (caps cap) _ _ r hrun
  have hi:ZeroPadding.config (caps cap) (initialConfiguration NodeScalar.machine (NodeScalar.input w left right bits))=
      initialConfiguration NodeScalar.machine (input cap w left right bits):=by rfl
  rw [hi] at ha
  refine ⟨a.final.tapes,⟨a,ha,rfl,?_,ast.trans_le rs⟩,?_,?_⟩
  · intro i
    rw [af]
    exact rh i
  · rw [af]
    change ZeroPadding.pad (caps cap 19) (r.final.tapes 19)=_
    rw [rt,h19]
    simp [caps]
  · intro i
    rw [af]
    change ZeroPadding.pad (caps cap (i.castAdd 16)) (r.final.tapes (i.castAdd 16))=_
    rw [rt]
    fin_cases i
    · exact congrArg (ZeroPadding.pad _) h0
    · exact congrArg (ZeroPadding.pad _) h1
    · exact congrArg (ZeroPadding.pad _) h2
    · exact congrArg (ZeroPadding.pad _) h3
    · exact congrArg (ZeroPadding.pad _) h4

end NearCubicWires.RepairOrdinary.CloseoutWitness.DAGOutput
