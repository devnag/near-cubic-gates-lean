import Proof.Amplification.RecoveryPCPFormulaResumeRowReset

/-! Execute a complete original PCP row, reset its source, and physically
erase the address result. The exact entry bank is restored for repetition. -/
namespace NearCubicWires.RepairSource.RecoveryPCPFormulaResumeRowReusable
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound SourceInterfaces ProjectionNormalization
open RecoveryPCPFormulaResumeRow RecoveryPCPFormulaResumeRowReset
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 3→Fin 318 := ![159,278,279]
theorem slots_injective : Function.Injective slots := by decide
noncomputable def clearMachine := RecoveryFocus.machine slots (RecoveryScratchErase.resetMachine 1)
noncomputable def machine := Composition.machine RecoveryPCPFormulaResumeRowReset.machine clearMachine

theorem input_address (cap : Nat) (source out : List Bool) (count : Nat)
    (p : RawProjectionPCP) (R Q : Nat) (randomness : BitInput R) (logCap resetCap : Nat) :
    input cap source out count p R Q randomness logCap resetCap 159=List.replicate cap false := by
  change ZeroPadding.pad cap (initialTapes cap source out 0 count p R Q randomness logCap (addressSlots 31))=_
  rw [initialTapes,install_slot addressSlots address_injective]
  rfl

theorem input_driver (cap : Nat) (source out : List Bool) (count : Nat)
    (p : RawProjectionPCP) (R Q : Nat) (randomness : BitInput R) (logCap resetCap : Nat) :
    input cap source out count p R Q randomness logCap resetCap 278=List.replicate cap true := by
  change ZeroPadding.pad 0 (initialTapes cap source out 0 count p R Q randomness logCap (clauseSlots 278))=_
  rw [ZeroPadding.pad_zero,initial_other _ _ _ _ _ _ _ _ _ _ 278 (by decide)]
  rfl

theorem input_log (cap : Nat) (source out : List Bool) (count : Nat)
    (p : RawProjectionPCP) (R Q : Nat) (randomness : BitInput R) (logCap resetCap : Nat) :
    input cap source out count p R Q randomness logCap resetCap 279=List.replicate (cap+1) false := by
  change ZeroPadding.pad 0 (initialTapes cap source out 0 count p R Q randomness logCap (clauseSlots 279))=_
  rw [ZeroPadding.pad_zero,initial_other _ _ _ _ _ _ _ _ _ _ 279 (by decide)]
  rfl

theorem stream_length (words : List (List Bool)) (R : Nat) (hw : ∀ word∈words,word.length=R) :
    (FieldList.stream words).length=words.length*(2*R+1) := by
  induction words with
  | nil => simp only [FieldList.stream_nil,List.length_nil,Nat.zero_mul]
  | cons word words ih =>
    have hword:=hw word (by simp)
    have htail:=ih (fun x hx=>hw x (by simp [hx]))
    rw [FieldList.stream_cons,List.length_append,frame_length,hword,htail,List.length_cons]
    ring

theorem address_fits (p : RawProjectionPCP) (R Q : Nat) (hr : p.width≤R) (hq : p.queries≤Q)
    {n : Nat} (x : BitInput n) (randomness : BitInput R) (cap : Nat)
    (hc : RecoverySourceClauseLoad.uniformBudget Q R≤cap) :
    (FieldList.stream (RecoveryProjectionRows.addressFields p R Q hr hq x randomness)).length≤cap := by
  have h:=stream_length (RecoveryProjectionRows.addressFields p R Q hr hq x randomness) R (by
    intro word hw
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hw
    exact List.length_ofFn)
  have hlen : (RecoveryProjectionRows.addressFields p R Q hr hq x randomness).length=Q := by
    simp only [RecoveryProjectionRows.addressFields,List.length_ofFn]
  rw [hlen] at h
  rw [h]
  unfold RecoverySourceClauseLoad.uniformBudget at hc
  nlinarith

def rowBudget (cap R Q count : Nat) := 2*budget cap R Q count+2*cap+7

theorem row_run (p : RawProjectionPCP) (R Q : Nat) (hr : p.width≤R) (hq : p.queries≤Q)
    {n : Nat} (x : BitInput n) (randomness : BitInput R) (cap logCap resetCap : Nat) (out : List Bool)
    (hc : RecoverySourceClauseLoad.uniformBudget Q R≤cap)
    (hl : RecoveryProjectionRowsRewind.batchBudget R Q+2≤logCap)
    (hz : budget cap R Q (Codec.clauses p).length≤resetCap) : ∃ r,
    runFrom machine (rowBudget cap R Q (Codec.clauses p).length)
      ⟨machine.start,heads cap (DedupBytes.fields p) out (Codec.clauses p).length,
        input cap (DedupBytes.fields p) out (Codec.clauses p).length p R Q randomness logCap resetCap⟩=some r ∧
      r.final.heads=heads cap (DedupBytes.fields p)
        (out++FieldList.stream (RecoveryPCPFormulaResume.rowWords
          (compactProjectionPCP (p.normalized R Q hr hq)) x randomness)) (Codec.clauses p).length ∧
      r.final.tapes=input cap (DedupBytes.fields p)
        (out++FieldList.stream (RecoveryPCPFormulaResume.rowWords
          (compactProjectionPCP (p.normalized R Q hr hq)) x randomness))
        (Codec.clauses p).length p R Q randomness logCap resetCap ∧
      r.steps≤rowBudget cap R Q (Codec.clauses p).length := by
  obtain ⟨a,ha,ah,atapes,asteps⟩ := reset_run p R Q hr hq x randomness cap logCap resetCap out hc hl hz
  let address:=FieldList.stream (RecoveryProjectionRows.addressFields p R Q hr hq x randomness)
  let nextOut:=out++FieldList.stream (RecoveryPCPFormulaResume.rowWords
    (compactProjectionPCP (p.normalized R Q hr hq)) x randomness)
  let backing : Fin 1→List Bool := fun _=>ZeroPadding.pad cap address
  have ready:=RecoveryScratchErase.erase_ready cap (cap+1) backing (by
    intro i
    rw [ZeroPadding.pad_length]
    exact max_le le_rfl (address_fits p R Q hr hq x randomness cap hc))
  obtain ⟨b,hb,bh,bt,bs⟩ := ready.focus_at slots slots_injective a.final.heads a.final.tapes
    (by intro i; rw [atapes]; fin_cases i
        · rfl
        · change input cap (DedupBytes.fields p) nextOut (Codec.clauses p).length p R Q randomness logCap resetCap 278=List.replicate cap true
          exact input_driver _ _ _ _ _ _ _ _ _ _
        · change input cap (DedupBytes.fields p) nextOut (Codec.clauses p).length p R Q randomness logCap resetCap 279=List.replicate (cap+1) false
          exact input_log _ _ _ _ _ _ _ _ _ _)
    (by intro i; rw [ah]; fin_cases i <;> rfl)
  have hall:=Composition.run_join RecoveryPCPFormulaResumeRowReset.machine clearMachine _ _ _ a b ha hb
  have ht : (2*budget cap R Q (Codec.clauses p).length+2)+1+(2*cap+4)=
      rowBudget cap R Q (Codec.clauses p).length := by unfold rowBudget; omega
  rw [ht] at hall
  refine ⟨_,hall,bh.trans ah,?_,?_⟩
  · change b.final.tapes=input cap (DedupBytes.fields p) nextOut (Codec.clauses p).length p R Q randomness logCap resetCap
    rw [bt,atapes]
    funext i
    by_cases h159 : i=159
    · subst i
      change install slots _ _ (slots 0)=_
      rw [install_slot slots slots_injective,input_address]
      rfl
    by_cases h278 : i=278
    · subst i
      change install slots _ _ (slots 1)=_
      rw [install_slot slots slots_injective,input_driver]
      rfl
    by_cases h279 : i=279
    · subst i
      change install slots _ _ (slots 2)=_
      rw [install_slot slots slots_injective,input_log]
      simp only [max_self]; rfl
    rw [install_other _ _ _ _ (by
      intro j; fin_cases j
      · exact Ne.symm h159
      · exact Ne.symm h278
      · exact Ne.symm h279),Function.update_of_ne h159]
  · change a.steps+1+b.steps≤_
    unfold rowBudget
    omega

end NearCubicWires.RepairSource.RecoveryPCPFormulaResumeRowReusable
