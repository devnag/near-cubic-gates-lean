import Proof.CaseAnalysis.RecoveryAddressOutput

/-! The same original address machine runs with an allocated reusable outer
stack. Every returned scalar and scratch field has its next-call form. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedAddressReuse
open LocalBitMultitape SourceInterfaces RepairRepresentation
open BoundedOracleStructuralCircuit FinitePredicateCircuit RecoveryBoundedNative RecoveryBoundedAddress
open RecoveryBoundedAddressFinish
open RecoveryBoundedSelectorLoop (capacity)
open RecoveryBoundedSelectorFinish (folded falseBits)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def caps (C : ℕ) (i : Fin 41):=if i=38 then C else 0
def selected (i : Fin 41):=decide (i=37)
def paddedData (index base C D value limit total : ℕ) (out source : List Bool) (i : Fin 41):=
  ZeroPadding.pad (caps C i) (RecoveryBoundedAddressFinish.data index base C D value limit total out source [] i)
def finalHeads (out : List Bool) : Fin 42→ℕ:=
  Fin.addCases (m:=41) (n:=1) (motive:=fun _=>ℕ) (RecoveryBoundedAddressFinish.heads out [] 0) (fun _=>0)
def finalData (index base C D value limit total L : ℕ) (out source : List Bool) : Fin 42→List Bool:=
  Fin.addCases (m:=41) (n:=1) (motive:=fun _=>List Bool)
    (paddedData index base C D value limit total out source) (fun _=>List.replicate L false)

theorem padded_after (index base C D value limit total z : ℕ) (out source : List Bool) (hz : z ≤ C) :
    (fun i=>ZeroPadding.pad (caps C i) (afterData index base C D value limit total z out source [] i))=
      paddedData index base C D value limit total out source := by
  funext i
  by_cases hi : i=38
  · subst i
    change ZeroPadding.pad C (List.replicate z false)=ZeroPadding.pad C []
    rw [RecoveryBoundedSelectorLoop.pad_erased C z hz]
    rfl
  · simp only [afterData,if_neg hi,paddedData]

theorem reset_heads (out : List Bool) (pos : ℕ) :
    (fun i=>if selected i then 0 else RecoveryBoundedAddressFinish.heads out [] pos i)=
      RecoveryBoundedAddressFinish.heads out [] 0 := by
  funext i
  fin_cases i <;> rfl

theorem padded_run {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (row : Fin (bound+1)) (start limit W D : ℕ) (hblock : start+limit ≤ rowWidth n bound)
    (bits out tail : List Bool)
    (hi : RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start+limit ≤ W)
    (hp : b.nodes.length+bits.length*(3*limit+1)+3*limit ≤ W)
    (hg : (compileExpr b (BoolExpr.any (items row start limit hblock 0 bits))).final.nodes.length ≤ W)
    (hc : bits.length ≤ W)
    (hD : RecoveryBoundedNativeUnaryJoin.budget limit (capacity W) ≤ D) :
    let compiled:=compileExpr b (BoolExpr.any (items row start limit hblock 0 bits))
    let result:=out++compiled.extension.suffix.flatMap PCPPRequestNodeSchema.native
    ∃ r,runFrom RecoveryBoundedAddressFinish.machine (RecoveryBoundedAddressFinish.budget bits.length W)
      (ZeroPadding.config (caps (capacity W))
        (RecoveryBoundedAddressFinish.entry (n:=n) row start limit W D b.nodes.length bits.length out [] (bits++tail) []))=some r ∧
      r.steps ≤ RecoveryBoundedAddressFinish.budget bits.length W ∧
      r.final.heads=RecoveryBoundedAddressFinish.heads result [] bits.length ∧
      r.final.tapes=paddedData (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start)
        compiled.output.val (capacity W) D bits.length limit bits.length result (bits++tail) := by
  let xs:=items row start limit hblock 0 bits
  let compiled:=compileExpr b (BoolExpr.any xs)
  let a:=(initial b.nodes.length out [] []).iterate row start limit hblock bits
  let refs:=references b.nodes.length xs
  let f:=folded a.position (a.out++falseBits) refs
  have hs:=iterate_schedule row start limit hblock bits (initial b.nodes.length out [] [])
  have haPos : a.position=b.nodes.length+prefixSize xs:=hs.1
  have haSkipped : a.skipped=bits := by
    have h:=hs.2.2.2.1
    change a.skipped=[]++bits at h
    exact h.trans (List.nil_append bits)
  have hrlen : refs.length=bits.length := by rw [RecoveryBoundedAddress.references_length,items_length]
  have hf : a.position+bits.length ≤ W := by
    rw [compileExpr_length,any_count,items_length] at hg
    rw [haPos]
    dsimp only [xs]
    omega
  have href : ∀ ref∈refs,ref ≤ W := by
    intro ref hr
    have h:=saved_bound b.nodes.length xs ref hr
    rw [←haPos] at h
    omega
  have hz:=RecoveryBoundedSelectorReuse.erased_small a.position W (a.out++falseBits) refs
    (by rw [hrlen];exact hc) href
  obtain ⟨old,hr0,rs0,oldGraph,oldOutput,rh0,rt0⟩:=
    original_run b row start limit W D hblock bits out [] tail [] hi hp hg hc hD
  have hd : old.final.tapes=(reverseOutput (RecoveryBoundedNativeUnaryLoop.firstIndex (n:=n) row start)
      a.position (capacity W) D bits.length limit bits.length a.skipped.length
      (a.out++falseBits) (bits++tail) [] refs).tapes := by
    simpa only [List.nil_append] using rt0
  rw [hd,output_tapes] at oldGraph oldOutput
  change f.out=out++compiled.extension.suffix.flatMap PCPPRequestNodeSchema.native at oldGraph
  change List.replicate f.acc true=List.replicate compiled.output.val true at oldOutput
  have hacc : f.acc=compiled.output.val := by
    have h:=congrArg List.length oldOutput
    simpa only [List.length_replicate] using h
  obtain ⟨r,hr,rf,rs,_⟩:=ZeroPadding.run_config RecoveryBoundedAddressFinish.machine (caps (capacity W)) _ _ old hr0
  refine ⟨r,hr,rs.le.trans rs0,?_,?_⟩
  · rw [rf]
    change old.final.heads=_
    rw [rh0,output_heads]
    change RecoveryBoundedAddressFinish.heads f.out [] a.skipped.length=_
    rw [haSkipped,oldGraph]
  · rw [rf]
    change (fun i=>ZeroPadding.pad (caps (capacity W) i) (old.final.tapes i))=_
    rw [hd,output_tapes,padded_after _ _ _ _ _ _ _ _ _ _ hz,hacc,oldGraph]

end NearCubicWires.RepairOrdinary.RecoveryBoundedAddressReuse
