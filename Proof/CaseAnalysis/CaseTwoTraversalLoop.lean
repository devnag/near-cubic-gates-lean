import Proof.CaseAnalysis.CaseTwoTraversalCalls

/-! Execute the original node rows and stop at their original output row.
The single append buffer and the physical counter are produced together;
the full retained description is never replaced by a second encoding. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.Traversal
open LocalBitMultitape RepairRepresentation OuterPCPRecovery RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem loop_trace {n : ℕ} (C F S M : ℕ) (nodes : List (BooleanNode n)) (count output : ℕ)
    (pre tail out : List Bool) (h : Fits C F S M)
    (hsource : (pre++word F nodes output tail).length≤S)
    (hcount : count+nodes.length≤M)
    (hvalues : ∀ x∈nodes,PCPPRequestNodeSchema.fields x 1≤F ∧ PCPPRequestNodeSchema.fields x 2≤F)
    (houtput : output≤F) :
    let source:=pre++word F nodes output tail
    let result:=out++nodes.flatMap PCPPRequestNodeSchema.native++natWord output
    ∃ steps,steps≤256*(nodes.length+1)*(C+1) ∧
      Timed machine steps (cfg 0 (heads out) (data C F count source pre.length [] out false))
        (RecoveryCalls.stopped sizes (heads result)
          (data C F (count+nodes.length) source (pre.length+nodes.length*(6+2*F)+6+F)
            (natWord 5) result true)) := by
  induction nodes generalizing count pre out with
  | nil=>
    have hsrc : (pre++orderedNatBits 6 5++orderedNatBits F output++tail).length≤S:=by
      simpa only [word,List.flatMap_nil,List.nil_append,List.append_assoc] using hsource
    obtain ⟨steps,hs,ht⟩:=finish_trace C F S M count output pre tail out h houtput hsrc
    refine ⟨steps,by simp only [List.length_nil];omega,?_⟩
    simpa only [word,List.flatMap_nil,List.nil_append,List.append_nil,List.length_nil,
      Nat.add_zero,Nat.zero_mul,List.append_assoc] using ht
  | cons x xs ih=>
    let a:=PCPPRequestNodeSchema.fields x 1
    let b:=PCPPRequestNodeSchema.fields x 2
    let v : Fin 6:=⟨PCPPRequestNodeSchema.fields x 0,by
      rw [PCPPRequestNodeSchema.first_tag]
      have ht:=(PCPPRequestNodeSchema.tag x).isLt
      omega⟩
    let source:=pre++word F (x::xs) output tail
    let prefixTag:=pre++orderedNatBits 6 v.val
    let prefixNext:=pre++rowBits F x
    let nativeNext:=out++PCPPRequestNodeSchema.native x
    let afterTag:=orderedNatBits F a++orderedNatBits F b++word F xs output tail
    have ha : a≤F:=(hvalues x (by simp)).1
    have hb : b≤F:=(hvalues x (by simp)).2
    have hv : v.val<5:=by
      change PCPPRequestNodeSchema.fields x 0<5
      rw [PCPPRequestNodeSchema.first_tag]
      exact (PCPPRequestNodeSchema.tag x).isLt
    have hfalse : decide (v.val=5)=false:=by simp only [decide_eq_false_iff_not];omega
    have hsrc0 : pre++orderedNatBits 6 v.val++afterTag=source:=by
      simp only [source,afterTag,word,rowBits,v,a,b,List.flatMap_cons,List.append_assoc]
    have hsrc1 : prefixTag++orderedNatBits F a++orderedNatBits F b++word F xs output tail=source:=by
      simp only [prefixTag,source,word,rowBits,v,a,b,List.flatMap_cons,List.append_assoc]
    have hsrc2 : prefixNext++word F xs output tail=source:=by
      simp only [prefixNext,source,word,List.flatMap_cons,List.append_assoc]
    have hpt : prefixTag.length=pre.length+6:=by simp [prefixTag]
    have hpn : prefixNext.length=pre.length+6+2*F:=by simp [prefixNext];omega
    have hrest : (prefixNext++word F xs output tail).length≤S:=by rw [hsrc2];exact hsource
    have hpre : pre.length+6+2*F≤S:=by
      rw [List.length_append,hpn] at hrest
      omega
    have hword : 2*source.length+1≤C:=(Nat.add_le_add_right (Nat.mul_le_mul_left 2 hsource) 1).trans h.source
    obtain ⟨r0,hr0,hs0,hh0,ht0⟩:=tag_run C F count pre afterTag out v
      (by rw [hsrc0];exact hword) (by have ho:=h.offset;omega)
      (h.field pre.length 6 v.val (by omega) (by omega) (by omega))
    rw [hsrc0] at hr0 ht0
    rw [hfalse] at ht0
    have t0:=call 0 1 (TagReady.budget C) (heads out) (heads out)
      (data C F count source pre.length [] out false)
      (data C F count source (pre.length+6) (natWord v.val) out false) r0 hr0 hh0 ht0
      (by intro q;change some (if readTapeBit (data C F count source (pre.length+6) (natWord v.val) out false 25)
            (heads out 25) then 2 else 1)=some 1
          rw [flag_scan];rfl)
    obtain ⟨r1,hr1,hs1,hh1,ht1⟩:=node_run C F count v.val a b prefixTag (word F xs output tail) out ha hb
      (by rw [hsrc1];exact hword)
      (by rw [hpt];have ho:=h.offset;omega)
      (by have hc:=h.count;simp only [List.length_cons] at hcount;omega)
      (h.field prefixTag.length F a (by rw [hpt];omega) (by omega) ha)
      (h.field (prefixTag.length+F) F b (by rw [hpt];omega) (by omega) hb)
      (by have hw:=tag_width v;have hn:=h.nine;omega)
    rw [hsrc1] at hr1 ht1
    have hoff : prefixTag.length+2*F=prefixNext.length:=by rw [hpt,hpn]
    have hout : out++natWord v.val++natWord a++natWord b=nativeNext:=by
      simp only [nativeNext,PCPPRequestNodeSchema.native,v,a,b,List.append_assoc]
    rw [hoff,hout] at ht1
    rw [hout] at hh1
    rw [hpt] at hr1
    have t1:=node_call (nodeBudget C F count (pre.length+6) v.val a b) (heads out) (heads nativeNext)
      (data C F count source (pre.length+6) (natWord v.val) out false)
      (data C F (count+1) source prefixNext.length [] nativeNext false) r1
      hr1 hh1 ht1
    obtain ⟨steps,hs,t2⟩:=ih (count:=count+1) (pre:=prefixNext) (out:=nativeNext) hrest
      (by simp only [List.length_cons] at hcount;omega)
      (fun y hy=>hvalues y (List.mem_cons_of_mem x hy))
    have hcounts : count+1+xs.length=count+(x::xs).length:=by simp;omega
    have hoffsets : prefixNext.length+xs.length*(6+2*F)+6+F=
        pre.length+(x::xs).length*(6+2*F)+6+F:=by
      rw [hpn]
      simp only [List.length_cons]
      ring
    have houts : nativeNext++xs.flatMap PCPPRequestNodeSchema.native++natWord output=
        out++(x::xs).flatMap PCPPRequestNodeSchema.native++natWord output:=by
      simp only [nativeNext,List.flatMap_cons,List.append_assoc]
    rw [hsrc2,hcounts,hoffsets,houts] at t2
    refine ⟨(r0.steps+1)+(r1.steps+1)+steps,?_,(t0.trans t1).trans t2⟩
    have h0b:=tag_budget C
    have h1b:=node_budget C F S M count prefixTag.length a b v h
      (by rw [hpt];omega) (by simp only [List.length_cons] at hcount;omega) ha hb
    have ht : 256*((x::xs).length+1)*(C+1)=256*(xs.length+1)*(C+1)+256*(C+1):=by
      simp only [List.length_cons]
      ring
    rw [ht]
    omega

theorem loop_run {n : ℕ} (C F S M : ℕ) (nodes : List (BooleanNode n)) (count output : ℕ)
    (pre tail out : List Bool) (h : Fits C F S M)
    (hsource : (pre++word F nodes output tail).length≤S)
    (hcount : count+nodes.length≤M)
    (hvalues : ∀ x∈nodes,PCPPRequestNodeSchema.fields x 1≤F ∧ PCPPRequestNodeSchema.fields x 2≤F)
    (houtput : output≤F) :
    let source:=pre++word F nodes output tail
    let result:=out++nodes.flatMap PCPPRequestNodeSchema.native++natWord output
    ∃ r,runFrom machine (256*(nodes.length+1)*(C+1))
      (cfg 0 (heads out) (data C F count source pre.length [] out false))=some r ∧
      r.steps≤256*(nodes.length+1)*(C+1) ∧ r.final.heads=heads result ∧
      r.final.tapes=data C F (count+nodes.length) source (pre.length+nodes.length*(6+2*F)+6+F)
        (natWord 5) result true := by
  obtain ⟨steps,hs,ht⟩:=loop_trace C F S M nodes count output pre tail out h hsource hcount hvalues houtput
  obtain ⟨r,hr,rf,rs⟩:=ht.run (by simp [machine,RecoveryCalls.machine,RecoveryCalls.stopped])
  have more:=runFrom_moreFuel machine steps (256*(nodes.length+1)*(C+1)-steps) _ r hr
  rw [Nat.add_sub_of_le hs] at more
  exact ⟨r,more,rs.le.trans hs,by rw [rf];rfl,by rw [rf];rfl⟩

end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.Traversal
