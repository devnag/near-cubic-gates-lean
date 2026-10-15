import Proof.Amplification.RecoveryPCPFormulaResumeFramed

/-! Execute the exact original outer-proof recovery formula through the
accepted balanced-CNF serializer. The serializer receives the bytes physically
emitted by the cold tautologies and all original PCP rows. -/
namespace NearCubicWires.RepairSource.RecoveryPCPFormulaResumeSerialize
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound SourceInterfaces ProjectionNormalization VerifierDecoding
open CanonicalRecoveryLanguage BalancedCNFSATEncoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots (i : Fin 133) : Fin 716 := if i=0 then 582 else ⟨583+i.val,by have hi:=i.isLt; omega⟩
theorem slots_injective : Function.Injective slots := by
  intro i j h
  have hv:=congrArg (fun i : Fin 716=>i.val) h
  dsimp [slots] at hv
  apply Fin.ext
  split_ifs at hv <;> dsimp at hv <;> omega
noncomputable def first := TapeEmbedding.machine 132 RecoveryPCPFormulaResumePrefix.framedMachine
noncomputable def last := RecoveryFocus.machine slots RecoveryFormulaFrame.machine
noncomputable def machine := Composition.machine first last
noncomputable def input (p : RawProjectionPCP) (R Q cap logCap resetCap : Nat) : Fin 716→List Bool :=
  Fin.addCases (m:=584) (n:=132) (motive:=fun _=>List Bool)
    (RecoveryPCPFormulaResumePrefix.framedInput p R Q cap logCap resetCap) (fun _=>[])
def budget (cap R Q count : Nat) (words : List (List Bool)) :=
  RecoveryPCPFormulaResumePrefix.framedBudget cap R Q count (FieldList.stream words).length+1+
    RecoveryFormulaFrame.rawBudget words

private theorem embedded_initial {t e s : Nat} (p : Machine t s) (data : Fin t→List Bool) :
    TapeEmbedding.config (fun _ : Fin e=>0) (fun _ : Fin e=>[]) (initialConfiguration p data)=
      initialConfiguration (TapeEmbedding.machine e p) (Fin.addCases data (fun _ : Fin e=>[])) := by
  apply configuration_ext
  · rfl
  · funext i
    refine Fin.addCases (m:=t) (n:=e) (fun i=>?_) (fun i=>?_) i
    all_goals simp only [TapeEmbedding.config,initialConfiguration,Fin.addCases_left,Fin.addCases_right]
  · rfl

theorem serialize_run (p : RawProjectionPCP) (R Q : Nat) (hr : p.width≤R) (hq : p.queries≤Q)
    {n : Nat} (x : BitInput n) (cap logCap resetCap : Nat)
    (hc : RecoverySourceClauseLoad.uniformBudget Q R≤cap)
    (hl : RecoveryProjectionRowsRewind.batchBudget R Q+2≤logCap)
    (hz : RecoveryPCPFormulaResumeRow.budget cap R Q (Codec.clauses p).length≤resetCap) : ∃ r,
    run machine (budget cap R Q (Codec.clauses p).length
        (RecoveryPCPFormulaResume.words (compactProjectionPCP (p.normalized R Q hr hq)) x))
      (input p R Q cap logCap resetCap)=some r ∧
      r.final.tapes 714=frame (balancedCNFPayload
        (outerProofRecoveryFormula (compactProjectionPCP (p.normalized R Q hr hq)) x)).bits ∧
      r.steps≤budget cap R Q (Codec.clauses p).length
        (RecoveryPCPFormulaResume.words (compactProjectionPCP (p.normalized R Q hr hq)) x) := by
  let words := RecoveryPCPFormulaResume.words (compactProjectionPCP (p.normalized R Q hr hq)) x
  obtain ⟨base,hbase,bt,bh,bs⟩ := RecoveryPCPFormulaResumePrefix.framed_run p R Q hr hq x cap logCap resetCap hc hl hz
  let a := TapeEmbedding.receipt (fun _ : Fin 132=>0) (fun _ : Fin 132=>[]) base
  have ha:=TapeEmbedding.run_embed RecoveryPCPFormulaResumePrefix.framedMachine
    (fun _ : Fin 132=>0) (fun _ : Fin 132=>[]) _ _ base hbase
  rw [embedded_initial] at ha
  obtain ⟨code,hcode,ct,cs⟩ := RecoveryFormulaFrame.raw_run words
  have hheads : ∀ j,a.final.heads (slots j)=0 := by
    intro j
    by_cases hj : j=0
    · subst j
      exact (TapeEmbedding.receipt_heads_old _ _ _ (582 : Fin 584)).trans (bh 582)
    · let k : Fin 132 := ⟨j.val-1,by have hi:=j.isLt; omega⟩
      have he : slots j=k.natAdd 584 := by
        apply Fin.ext
        have hn : j.val≠0 := fun h=>hj (Fin.ext h)
        simp only [slots,hj,ite_false,Fin.val_natAdd]
        dsimp [k]; omega
      rw [he]
      exact TapeEmbedding.receipt_heads_new _ _ _ k
  have htapes : ∀ j,a.final.tapes (slots j)=RecoveryFormulaFrame.input words j := by
    intro j
    by_cases hj : j=0
    · subst j
      exact (TapeEmbedding.receipt_tapes_old _ _ _ (582 : Fin 584)).trans bt
    · let k : Fin 132 := ⟨j.val-1,by have hi:=j.isLt; omega⟩
      have he : slots j=k.natAdd 584 := by
        apply Fin.ext
        have hn : j.val≠0 := fun h=>hj (Fin.ext h)
        simp only [slots,hj,ite_false,Fin.val_natAdd]
        dsimp [k]; omega
      rw [he,TapeEmbedding.receipt_tapes_new]
      rw [RecoveryFormulaPayload.input_tapes]
      change []=(if j.val=0 then frame (FieldList.stream words) else [])
      rw [if_neg (show j.val≠0 from fun h=>hj (Fin.ext h))]
  obtain ⟨b,hb,_bc,bsteps,_bheads,btapes,_bkeep⟩ := RecoveryFocus.dock slots slots_injective
    RecoveryFormulaFrame.machine _ a.final.heads a.final.tapes _ hheads htapes code hcode
  have hall:=Composition.run_join first last _ _ _ a b ha hb
  refine ⟨_,hall,?_,?_⟩
  · change b.final.tapes (slots 131)=_
    rw [btapes,ct,RecoveryFormulaPayload.value_code _ words (RecoveryPCPFormulaResume.values _ x)]
  · change a.steps+1+b.steps≤_
    rw [bsteps]
    change base.steps+1+code.steps≤_
    unfold budget
    change code.steps≤RecoveryFormulaFrame.rawBudget
      (RecoveryPCPFormulaResume.words (compactProjectionPCP (p.normalized R Q hr hq)) x) at cs
    omega

end NearCubicWires.RepairSource.RecoveryPCPFormulaResumeSerialize
