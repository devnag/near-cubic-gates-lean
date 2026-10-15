import Proof.PCP.PCPPNativeClauseOriginal

/-! The complete original M-loop starts with genuinely blank scratch.
The existing reverse padding simulation proves the same physical run; only
the actual source, true scalar drivers and output prefix are supplied. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeClauseCold
open LocalBitMultitape SourceInterfaces RepairSource PCPPNativeClauseLoop
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev retained (i : Fin 52) : Prop :=
  i=4 ∨ i=5 ∨ i=6 ∨ i=13 ∨ i=21 ∨ i=26 ∨ i=27 ∨ i=28 ∨ i=47 ∨ i=49 ∨ i=51
def padding (C : ℕ) (i : Fin 52) : ℕ :=
  if retained i then 0 else if i=20 ∨ i=22 ∨ i=50 then C+1 else C
noncomputable def input (source : List Bool) (pos stride p n C base accumulator : ℕ) (out : List Bool) (M : ℕ) :=
  { cfg 0 source pos stride p n C base accumulator out M 1 with
    tapes := fun i=>if retained i then (cfg 0 source pos stride p n C base accumulator out M 1).tapes i else [] }

theorem blank_tape (source : List Bool) (pos stride p n C base accumulator : ℕ) (out : List Bool) (M : ℕ)
    (i : Fin 52) (hi : ¬retained i) :
    (cfg 0 source pos stride p n C base accumulator out M 1).tapes i=List.replicate (padding C i) false := by
  fin_cases i
  all_goals first | exact False.elim (hi (by decide)) | rfl | exact ZeroPadding.pad_zero _

theorem padded_input (source : List Bool) (pos stride p n C base accumulator : ℕ) (out : List Bool) (M : ℕ) :
    ZeroPadding.config (padding C) (input source pos stride p n C base accumulator out M)=
      cfg 0 source pos stride p n C base accumulator out M 1 := by
  apply configuration_ext
  · rfl
  · rfl
  · funext i
    by_cases hi : retained i
    · change ZeroPadding.pad (padding C i) (if retained i then _ else [])=_
      simp only [padding,hi,ite_true,ZeroPadding.pad_zero]
    · change ZeroPadding.pad (padding C i) (if retained i then _ else [])=_
      rw [if_neg hi,blank_tape source pos stride p n C base accumulator out M i hi]
      simp only [ZeroPadding.pad,List.length_nil,Nat.sub_zero,List.nil_append]

theorem retained_tape {s : ℕ} (C : ℕ) (a b : Configuration 52 s)
    (h : ZeroPadding.config (padding C) a=b) (i : Fin 52) (hi : retained i) : a.tapes i=b.tapes i := by
  have he:=congrArg (fun c=>c.tapes i) h
  simpa only [ZeroPadding.config,padding,hi,ite_true,ZeroPadding.pad_zero] using he

theorem original_run {n q : ℕ} (r W C : ℕ) (oracle : BooleanCircuit n)
    (clauses : List (Fin 3→Literal q)) (pre suffix out : List Bool)
    (hstride : 2*oracle.size+1≤W) (hsize : q*(2*oracle.size+1)+3*clauses.length+1≤W)
    (hbytes : (sourceFields clauses).length≤W) (hC : 16384*(W+1)^2≤C) :
    ∃ result,runFrom machine (clauses.length*(48*C+131)+3)
      (input (pre++sourceFields clauses++suffix) pre.length (2*oracle.size+1) (2*oracle.output.val+1) (2*oracle.size) C
        (q*(2*oracle.size+1)+1) (q*(2*oracle.size+1)) out clauses.length)=some result ∧
      ZeroPadding.config (padding C) result.final=
        cfg 3 (pre++sourceFields clauses++suffix) (pre++sourceFields clauses).length
          (2*oracle.size+1) (2*oracle.output.val+1) (2*oracle.size) C
          (q*(2*oracle.size+1)+3*clauses.length+1) (q*(2*oracle.size+1)+3*clauses.length)
          (out++(PCPPNative.clauseStreamNodes (r:=r) (q*(2*oracle.size+1)+1) (q*(2*oracle.size+1))
            (PCPPNative.literalAddress oracle) clauses).flatMap PCPPRequestNodeSchema.native) clauses.length 1 ∧
      result.steps≤clauses.length*(48*C+131)+3 := by
  obtain ⟨a,ar,af,as⟩:=PCPPNativeClauseOriginal.original_run r W C oracle clauses pre suffix out hstride hsize hbytes hC
  rw [←padded_input] at ar
  obtain ⟨b,br,bf,bs,_⟩:=ZeroPadding.run_unpad machine (padding C) _ _ a ar
  exact ⟨b,br,bf.trans af,bs.le.trans as⟩

end NearCubicWires.RepairOrdinary.PCPPNativeClauseCold
