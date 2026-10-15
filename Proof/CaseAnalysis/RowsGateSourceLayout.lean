import Proof.CaseAnalysis.RowsGateSourceCalls

/-! Alias the already validated native request to the original CW source
input. All source scratch is fresh; the source's exact child word and its
two produced templates are retained at their actual final cursors. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsGateSource
open LocalBitMultitape RepairRepresentation ExecutableInterfaces RecoveryRootRound
open CloseoutRowsGatePairHeads DecompositionSource
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

variable (a : DecompositionAlgorithm)
abbrev tapes := 1038+Counted.tapes a
def old (i : Fin 1038) : Fin (tapes a) := i.castAdd (Counted.tapes a)
def slots (i : Fin (Counted.tapes a)) : Fin (tapes a) :=
  if i.val=0 then old a 1033 else i.natAdd 1038
def heads : Fin (tapes a) → ℕ :=
  Fin.addCases (m := 1038) (n := Counted.tapes a) (motive := fun _ => ℕ)
    CloseoutRowsGateGuard.heads (fun _ => 0)
def extend (bank : Fin 1038 → List Bool) : Fin (tapes a) → List Bool :=
  Fin.addCases (m := 1038) (n := Counted.tapes a) (motive := fun _ => List Bool) bank (fun _ => [])
def input (core : ℕ) (bits : List Bool) := extend a (CloseoutRowsGateGuard.input core bits)
noncomputable def first (compressed : Bool) :=
  TapeEmbedding.machine (Counted.tapes a) (CloseoutRowsGateGuard.machine compressed)
noncomputable def second := RecoveryFocus.machine (slots a) (Entry.machine a)
noncomputable def machine (compressed : Bool) :=
  CloseoutRowsGateColdPair.machine (first a compressed) (second a) (fun scanned => scanned (old a 1037))
def budget (bits : List Bool) (request : ExactDecompositionRequest) :=
  CloseoutRowsGateGuard.budget bits+1+Entry.budget a request+1

theorem slots_injective : Function.Injective (slots a) := by
  intro i j h
  by_cases hi : i.val=0 <;> by_cases hj : j.val=0
  · exact Fin.ext (hi.trans hj.symm)
  · have hv := congrArg Fin.val h
    simp only [slots,if_pos hi,if_neg hj,old,Fin.val_castAdd,Fin.val_natAdd] at hv
    omega
  · have hv := congrArg Fin.val h
    simp only [slots,if_neg hi,if_pos hj,old,Fin.val_castAdd,Fin.val_natAdd] at hv
    omega
  · have hv := congrArg Fin.val h
    simp only [slots,if_neg hi,if_neg hj,Fin.val_natAdd] at hv
    exact Fin.ext (by omega)

theorem source_heads (i : Fin (Counted.tapes a)) : heads a (slots a i)=0 := by
  by_cases hi : i.val=0
  · simp only [slots,if_pos hi,heads,old,Fin.addCases_left]
    rfl
  · simp only [slots,if_neg hi,heads,Fin.addCases_right]

theorem source_input (request : ExactDecompositionRequest) (bank : Fin 1038 → List Bool)
    (hr : bank 1033=frame (thresholdWord request.gate)) (i : Fin (Counted.tapes a)) :
    extend a bank (slots a i)=Counted.input a request i := by
  rw [← DecompositionSource.input_eq a request]
  change extend a bank (slots a i)=(if i.val=0 then frame (thresholdWord request.gate) else [])
  by_cases hi : i.val=0
  · simp only [slots,if_pos hi,extend,old,Fin.addCases_left]
    exact hr
  · simp only [slots,if_neg hi,extend,Fin.addCases_right]

theorem first_run (compressed : Bool) (core : ℕ) (bits : List Bool) (out : Fin 1038 → List Bool)
    (h : ReadyAt (CloseoutRowsGateGuard.machine compressed) (CloseoutRowsGateGuard.budget bits)
      CloseoutRowsGateGuard.heads (CloseoutRowsGateGuard.input core bits) out) :
    ReadyAt (first a compressed) (CloseoutRowsGateGuard.budget bits) (heads a) (input a core bits) (extend a out) := by
  obtain ⟨r,hr,rt,rh,rs⟩ := h
  have run := TapeEmbedding.run_embed (CloseoutRowsGateGuard.machine compressed)
    (fun _ : Fin (Counted.tapes a) => 0) (fun _ => []) _ _ r hr
  refine ⟨TapeEmbedding.receipt (fun _ : Fin (Counted.tapes a) => 0) (fun _ => []) r,run,?_,?_,rs⟩
  · change (TapeEmbedding.config (fun _ : Fin (Counted.tapes a) => 0) (fun _ => []) r.final).tapes=_
    simp only [TapeEmbedding.config,rt]
    rfl
  · change (TapeEmbedding.config (fun _ : Fin (Counted.tapes a) => 0) (fun _ => []) r.final).heads=_
    simp only [TapeEmbedding.config,rh]
    rfl

def Output {s : ℕ} (request : ExactDecompositionRequest) (out : Configuration (tapes a) s) : Prop :=
  out.tapes (slots a (Counted.localTape a 15))=Entry.output a request ∧
    out.heads (slots a (Counted.localTape a 15))=(Entry.output a request).length ∧
    out.tapes (slots a (Counted.localTape a 12))=UnaryTemplate.tape request.arity ∧
    out.heads (slots a (Counted.localTape a 12))=1 ∧
    out.tapes (slots a (Counted.fresh a 9))=UnaryTemplate.tape (a.output request).children.length ∧
    out.heads (slots a (Counted.fresh a 9))=1

theorem source_run (request : ExactDecompositionRequest) (bank : Fin 1038 → List Bool)
    (ht : bank 1033=frame (thresholdWord request.gate)) : ∃ r,
    runFrom (second a) (Entry.budget a request) (RecoveryCalls.restarted (second a) (heads a) (extend a bank))=some r ∧
      r.steps≤Entry.budget a request ∧ Output a request r.final := by
  obtain ⟨base,hbase,bs,bt,bh,arity,arityHead,count,countHead⟩ := Entry.entry_run a request
  obtain ⟨r,hr,_rc,rs,hheads,htapes,_other⟩ := RecoveryFocus.dock (slots a) (slots_injective a)
    (Entry.machine a) _ (heads a) (extend a bank) _ (source_heads a) (source_input a request bank ht) base hbase
  exact ⟨r,hr,rs ▸ bs,(htapes _).trans bt,(hheads _).trans bh,(htapes _).trans arity,
    (hheads _).trans arityHead,(htapes _).trans count,(hheads _).trans countHead⟩

end NearCubicWires.RepairOrdinary.CloseoutRowsGateSource
