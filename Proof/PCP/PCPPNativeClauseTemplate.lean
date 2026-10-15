import Proof.PCP.PCPPNativeClause

/-! The actual raw-count reader returns a sentinel with one terminal zero.
The unchanged original clause loop consumes that physical sentinel directly. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeClauseCold
open LocalBitMultitape SourceInterfaces RepairSource PCPPNativeClauseLoop
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def countPadding (M : ℕ) (i : Fin 52) : ℕ := if i=51 then M+2 else 0
noncomputable def templateInput (source : List Bool) (pos stride p n C base accumulator : ℕ)
    (out : List Bool) (M : ℕ) :=
  ZeroPadding.config (countPadding M) (input source pos stride p n C base accumulator out M)

theorem template_count (source : List Bool) (pos stride p n C base accumulator : ℕ)
    (out : List Bool) (M : ℕ) :
    (templateInput source pos stride p n C base accumulator out M).tapes 51=UnaryTemplate.tape M := by
  change ZeroPadding.pad (M+2) (VerifierDecoding.CompareMachine.word M)=UnaryTemplate.tape M
  simp [VerifierDecoding.CompareMachine.word,UnaryTemplate.tape,ZeroPadding.pad]

theorem template_other (source : List Bool) (pos stride p n C base accumulator : ℕ)
    (out : List Bool) (M : ℕ) (i : Fin 52) (hi : i≠51) :
    (templateInput source pos stride p n C base accumulator out M).tapes i=
      (input source pos stride p n C base accumulator out M).tapes i := by
  simp only [templateInput,ZeroPadding.config,countPadding,hi,ite_false,ZeroPadding.pad_zero]

theorem template_run {n q : ℕ} (r W C : ℕ) (oracle : BooleanCircuit n)
    (clauses : List (Fin 3→Literal q)) (pre suffix out : List Bool)
    (hstride : 2*oracle.size+1≤W) (hsize : q*(2*oracle.size+1)+3*clauses.length+1≤W)
    (hbytes : (sourceFields clauses).length≤W) (hC : 16384*(W+1)^2≤C) :
    ∃ result,runFrom machine (clauses.length*(48*C+131)+3)
      (templateInput (pre++sourceFields clauses++suffix) pre.length (2*oracle.size+1)
        (2*oracle.output.val+1) (2*oracle.size) C (q*(2*oracle.size+1)+1)
        (q*(2*oracle.size+1)) out clauses.length)=some result ∧
      result.final.heads=(cfg 3 (pre++sourceFields clauses++suffix) (pre++sourceFields clauses).length
        (2*oracle.size+1) (2*oracle.output.val+1) (2*oracle.size) C
        (q*(2*oracle.size+1)+3*clauses.length+1) (q*(2*oracle.size+1)+3*clauses.length)
        (out++(PCPPNative.clauseStreamNodes (r:=r) (q*(2*oracle.size+1)+1) (q*(2*oracle.size+1))
          (PCPPNative.literalAddress oracle) clauses).flatMap PCPPRequestNodeSchema.native) clauses.length 1).heads ∧
      result.final.tapes 47=out++(PCPPNative.clauseStreamNodes (r:=r)
        (q*(2*oracle.size+1)+1) (q*(2*oracle.size+1)) (PCPPNative.literalAddress oracle) clauses).flatMap PCPPRequestNodeSchema.native ∧
      result.steps≤clauses.length*(48*C+131)+3 := by
  obtain ⟨a,ar,af,as⟩:=original_run r W C oracle clauses pre suffix out hstride hsize hbytes hC
  obtain ⟨b,br,bf,bs,_⟩:=ZeroPadding.run_config machine (countPadding clauses.length) _ _ a ar
  refine ⟨b,br,?_,?_,bs.le.trans as⟩
  · exact (congrArg (fun c=>c.heads) bf).trans (congrArg (fun c=>c.heads) af)
  · have ht:=congrArg (fun c=>c.tapes 47) bf
    simp only [ZeroPadding.config,countPadding,show (47:Fin 52)≠51 by decide,ite_false,ZeroPadding.pad_zero] at ht
    exact ht.trans ((retained_tape C _ _ af 47 (by decide)).trans (ZeroPadding.pad_zero _))

end NearCubicWires.RepairOrdinary.PCPPNativeClauseCold
