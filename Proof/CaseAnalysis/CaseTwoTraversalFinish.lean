import Proof.CaseAnalysis.CaseTwoTraversalController

/-! The original output sentinel dispatches to exactly one output-reference
field and then halts. Its unused second field and every padding row remain
unvisited in the retained original flat description. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.Traversal
open LocalBitMultitape RepairRepresentation OuterPCPRecovery RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem finish_trace (C F S M count value : ℕ) (pre tail out : List Bool)
    (h : Fits C F S M) (hv : value≤F)
    (hsource : (pre++orderedNatBits 6 5++orderedNatBits F value++tail).length≤S) :
    let source:=pre++orderedNatBits 6 5++orderedNatBits F value++tail
    ∃ steps,steps≤64*(C+1) ∧
      Timed machine steps (cfg 0 (heads out) (data C F count source pre.length [] out false))
        (RecoveryCalls.stopped sizes (heads (out++natWord value))
          (data C F count source (pre.length+6+F) (natWord 5) (out++natWord value) true)) := by
  let source:=pre++orderedNatBits 6 5++orderedNatBits F value++tail
  have hpre : pre.length+6+F≤S:=by
    simp only [List.length_append,orderedNatBits_length] at hsource
    omega
  have hword : 2*source.length+1≤C:=(Nat.add_le_add_right (Nat.mul_le_mul_left 2 hsource) 1).trans h.source
  have hsrc : pre++orderedNatBits 6 5++(orderedNatBits F value++tail)=source:=by
    dsimp [source];simp only [List.append_assoc]
  obtain ⟨r0,hr0,hs0,hh0,ht0⟩:=tag_run C F count pre (orderedNatBits F value++tail) out (5 : Fin 6)
    (by change 2*(pre++orderedNatBits 6 5++(orderedNatBits F value++tail)).length+1≤C
        rw [hsrc];exact hword) (by have ho:=h.offset;omega)
    (h.field pre.length 6 5 (by omega) (by omega) (by decide))
  change runFrom tag (TagReady.budget C)
    ⟨tag.start,heads out,data C F count (pre++orderedNatBits 6 5++(orderedNatBits F value++tail)) pre.length [] out false⟩=some r0 at hr0
  change r0.final.tapes=data C F count (pre++orderedNatBits 6 5++(orderedNatBits F value++tail))
    (pre.length+6) (natWord 5) out true at ht0
  rw [hsrc] at hr0 ht0
  have t0:=call 0 2 (TagReady.budget C) (heads out) (heads out)
    (data C F count source pre.length [] out false)
    (data C F count source (pre.length+6) (natWord 5) out true) r0 hr0 hh0 ht0
    (by intro q;change some (if readTapeBit (data C F count source (pre.length+6) (natWord 5) out true 25)
          (heads out 25) then 2 else 1)=some 2
        rw [flag_scan];rfl)
  have hp : (pre++orderedNatBits 6 5).length=pre.length+6:=by simp
  obtain ⟨r1,hr1,hs1,hh1,ht1⟩:=field_run C F count value (pre++orderedNatBits 6 5) tail (natWord 5) out true hv
    hword (by rw [hp];have ho:=h.offset;omega)
    (by rw [hp];exact h.field (pre.length+6) F value (by omega) (by omega) hv)
  rw [hp] at hr1 hs1 ht1
  have t1:=stop (FieldStep.budget (pre.length+6) F value C) (heads out) (heads (out++natWord value))
    (data C F count source (pre.length+6) (natWord 5) out true)
    (data C F count source (pre.length+6+F) (natWord 5) (out++natWord value) true) r1 hr1 hh1 ht1
  refine ⟨(r0.steps+1)+(r1.steps+1),?_,t0.trans t1⟩
  have hb0:=tag_budget C
  have hb1:=field_budget C F S M (pre.length+6) value h (by omega) hv
  omega

end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.Traversal
