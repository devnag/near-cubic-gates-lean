import Proof.CaseAnalysis.CaseTwoTraversalField
import Proof.CaseAnalysis.CaseTwoTraversalTag

/-! A complete original node row publishes its saved tag, appends the two
original ordered-rank arguments, and increments the physical node count.
All repeated work cells and source offsets are carried through the run. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.Traversal
open LocalBitMultitape RepairRepresentation OuterPCPRecovery RecoveryRootRound Composition
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def arguments:=Composition.machine (Composition.machine field field) increment
noncomputable def node:=Composition.machine publish arguments
def argumentsBudget (C F count offset a b : ℕ):=
  FieldStep.budget offset F a C+FieldStep.budget (offset+F) F b C+2*count+6
def nodeBudget (C F count offset tag a b : ℕ):=
  TagPublish.budget tag C+1+argumentsBudget C F count offset a b

theorem arguments_run (C F count a b : ℕ) (pre tail out : List Bool)
    (ha : a≤F) (hb : b≤F)
    (hsource : 2*(pre++orderedNatBits F a++orderedNatBits F b++tail).length+1≤C)
    (hoffset : pre.length+2*F+2≤C) (hcount : count+1≤C)
    (hba : FieldNative.budget pre.length F a+1≤C)
    (hbb : FieldNative.budget (pre.length+F) F b+1≤C) :
    let source:=pre++orderedNatBits F a++orderedNatBits F b++tail
    ∃ r,runFrom arguments (argumentsBudget C F count pre.length a b)
      ⟨arguments.start,heads out,data C F count source pre.length [] out false⟩=some r ∧
      r.steps≤argumentsBudget C F count pre.length a b ∧
      r.final.heads=heads (out++natWord a++natWord b) ∧
      r.final.tapes=data C F (count+1) source (pre.length+2*F) [] (out++natWord a++natWord b) false := by
  let source:=pre++orderedNatBits F a++orderedNatBits F b++tail
  have haRun:=field_run C F count a pre (orderedNatBits F b++tail) [] out false ha
    (by simpa only [List.append_assoc] using hsource) (by omega) hba
  obtain ⟨r1,h1,s1,h1h,h1t⟩:=haRun
  have hsourceEq : pre++orderedNatBits F a++(orderedNatBits F b++tail)=source:=by
    simp only [source,List.append_assoc]
  rw [hsourceEq] at h1 h1t
  have hpre : (pre++orderedNatBits F a).length=pre.length+F:=by simp
  obtain ⟨r2,h2,s2,h2h,h2t⟩:=field_run C F count b (pre++orderedNatBits F a) tail [] (out++natWord a) false hb
    hsource (by rw [hpre];omega) (by rw [hpre];exact hbb)
  rw [hpre] at h2 s2 h2t
  have h2' : runFrom field (FieldStep.budget (pre.length+F) F b C) (restart r1.final field.start)=some r2:=by
    change runFrom field _ ⟨field.start,r1.final.heads,r1.final.tapes⟩=some r2
    rw [h1h,h1t]
    exact h2
  have h12:=Composition.run_join field field _ _ _ r1 r2 h1 h2'
  obtain ⟨r3,h3,s3,h3h,h3t⟩:=increment_run C F count (pre.length+F+F) source []
    (out++natWord a++natWord b) false hcount
  have h3' : runFrom increment (2*count+4) (restart (joinedReceipt r1 r2).final increment.start)=some r3:=by
    change runFrom increment _ ⟨increment.start,r2.final.heads,r2.final.tapes⟩=some r3
    rw [h2h,h2t]
    exact h3
  have whole:=Composition.run_join (Composition.machine field field) increment _ _ _
    (joinedReceipt r1 r2) r3 h12 h3'
  have ht : FieldStep.budget pre.length F a C+1+FieldStep.budget (pre.length+F) F b C+1+(2*count+4)=
      argumentsBudget C F count pre.length a b:=by unfold argumentsBudget;omega
  rw [ht] at whole
  refine ⟨joinedReceipt (joinedReceipt r1 r2) r3,whole,?_,h3h,?_⟩
  · change r1.steps+1+r2.steps+1+r3.steps≤argumentsBudget C F count pre.length a b
    unfold argumentsBudget;omega
  · change r3.final.tapes=_
    have hoff : pre.length+F+F=pre.length+2*F:=by omega
    simpa only [hoff] using h3t

theorem node_run (C F count tag a b : ℕ) (pre tail out : List Bool)
    (ha : a≤F) (hb : b≤F)
    (hsource : 2*(pre++orderedNatBits F a++orderedNatBits F b++tail).length+1≤C)
    (hoffset : pre.length+2*F+2≤C) (hcount : count+1≤C)
    (hba : FieldNative.budget pre.length F a+1≤C)
    (hbb : FieldNative.budget (pre.length+F) F b+1≤C)
    (htag : 2*natBitLength tag+3≤C) :
    let source:=pre++orderedNatBits F a++orderedNatBits F b++tail
    ∃ r,runFrom node (nodeBudget C F count pre.length tag a b)
      ⟨node.start,heads out,data C F count source pre.length (natWord tag) out false⟩=some r ∧
      r.steps≤nodeBudget C F count pre.length tag a b ∧
      r.final.heads=heads (out++natWord tag++natWord a++natWord b) ∧
      r.final.tapes=data C F (count+1) source (pre.length+2*F) []
        (out++natWord tag++natWord a++natWord b) false := by
  let source:=pre++orderedNatBits F a++orderedNatBits F b++tail
  obtain ⟨r1,h1,s1,h1h,h1t⟩:=publish_run C F count pre.length tag source out htag
  obtain ⟨r2,h2,s2,h2h,h2t⟩:=arguments_run C F count a b pre tail (out++natWord tag)
    ha hb hsource hoffset hcount hba hbb
  have h2' : runFrom arguments (argumentsBudget C F count pre.length a b)
      (restart r1.final arguments.start)=some r2:=by
    change runFrom arguments _ ⟨arguments.start,r1.final.heads,r1.final.tapes⟩=some r2
    rw [h1h,h1t]
    exact h2
  have whole:=Composition.run_join publish arguments _ _ _ r1 r2 h1 h2'
  refine ⟨joinedReceipt r1 r2,whole,?_,h2h,h2t⟩
  change r1.steps+1+r2.steps≤nodeBudget C F count pre.length tag a b
  unfold nodeBudget
  omega

end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.Traversal
