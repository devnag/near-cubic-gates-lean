import Proof.CaseAnalysis.RowsRawAtomLoop
import Proof.MachineModel.OrdinaryMatrixDimensionPrepare

/-! A SAME-source native child-count header is physically read and supplies
the absolute-index loop. The retained offset is advanced by that actual
count. No supplied unary child count or monomial driver remains. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsRawAtomNative
open LocalBitMultitape RepairRepresentation SignedSortKey RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def extraHeads (count : ℕ) (out : List Bool) : Fin 3→ℕ:=![1,out.length,count+1]
def extraTapes (offset count : ℕ) (out : List Bool) : Fin 3→List Bool:=
  ![UnaryTemplate.tape (offset+1),out,CompareMachine.word count]
noncomputable def first:=TapeEmbedding.machine 3 MatrixDimensionPrepare.machine
def slots : Fin 4→Fin 14:=![10,11,12,13]
theorem injective : Function.Injective slots:=by decide
noncomputable def last:=RecoveryFocus.machine slots CloseoutRowsRawAtomLoop.machine
noncomputable def machine:=Composition.machine first last
def budget (offset n : ℕ):=MatrixDimensionPrepare.budget (natBitLength n) n+1+
  CloseoutRowsRawAtomLoop.budget offset n
noncomputable def input (source : List Bool) (pos offset count : ℕ) (out : List Bool) :
    Configuration 14 ((8+(8+Fintype.card (RecoveryCalls.Control MatrixUnary.sizes)))+
      Fintype.card (RecoveryCalls.Control CloseoutRowsRawAtomLoop.sizes)) :=
  Composition.leftConfig _ (TapeEmbedding.config (extraHeads count out) (extraTapes offset count out)
    (Composition.leftConfig _ (MatrixDimensionPrepare.input source pos)))

theorem native_run (pre tail out : List Bool) (offset n count : ℕ) :
    ∃ r,runFrom machine (budget offset n)
      (input (pre++natWord n++tail) pre.length offset count out)=some r ∧
      r.final.tapes 0=pre++natWord n++tail ∧
      r.final.heads 0=pre.length+(natWord n).length ∧
      r.final.tapes 10=UnaryTemplate.tape n ∧ r.final.heads 10=n+1 ∧
      r.final.tapes 11=UnaryTemplate.tape (offset+n+1) ∧ r.final.heads 11=1 ∧
      r.final.tapes 12=out++ExtIncidence.stream (CloseoutRowsRawAtomLoop.indices offset n) ∧
      r.final.heads 12=(out++ExtIncidence.stream (CloseoutRowsRawAtomLoop.indices offset n)).length ∧
      r.final.tapes 13=CompareMachine.word (count+n) ∧ r.final.heads 13=count+n+1 ∧
      r.steps≤budget offset n := by
  let source:=pre++natWord n++tail
  obtain ⟨a,ha,at0,ah0,_at1,_ah1,_at3,_ah3,_at4,_ah4,at10,ah10,as⟩:=
    MatrixDimensionPrepare.prepare_run pre tail (natBitLength n) n
      (by simpa only [natBitLength] using Nat.lt_pow_succ_log_self (b:=2) (by decide) n)
  have hsource : pre++List.replicate (natBitLength n) true++false::(binary (natBitLength n) n++tail)=source := by
    simp [source,WilliamsInputHeader.natWord_eq,List.append_assoc]
  rw [hsource] at ha at0
  let a':=TapeEmbedding.receipt (extraHeads count out) (extraTapes offset count out) a
  have firstRun:=TapeEmbedding.run_embed MatrixDimensionPrepare.machine (extraHeads count out)
    (extraTapes offset count out) _ _ a ha
  obtain ⟨b,hb,bf,_bs⟩:=CloseoutRowsRawAtomLoop.range_run offset n count out
  have hheads : ∀ i,a'.final.heads (slots i)=
      (CloseoutRowsRawAtomLoop.entry 0 (UnaryTemplate.tape n) 1 offset count out).heads i := by
    intro i;fin_cases i
    · exact ah10
    all_goals rfl
  have htapes : ∀ i,a'.final.tapes (slots i)=
      (CloseoutRowsRawAtomLoop.entry 0 (UnaryTemplate.tape n) 1 offset count out).tapes i := by
    intro i;fin_cases i
    · exact at10
    all_goals rfl
  obtain ⟨focused,hf,_fc,fs,fh,ft,keep⟩:=RecoveryFocus.dock slots injective CloseoutRowsRawAtomLoop.machine
    _ a'.final.heads a'.final.tapes _ hheads htapes b hb
  change runFrom last (CloseoutRowsRawAtomLoop.budget offset n)
    (Composition.restart a'.final last.start)=some focused at hf
  have whole:=Composition.run_join first last _ _ _ a' focused firstRun hf
  have keep0:=keep 0 (by intro i;fin_cases i <;> decide)
  refine ⟨Composition.joinedReceipt a' focused,whole,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact keep0.2.trans at0
  · have hn:(natWord n).length=2*natBitLength n+1:=by
      simp only [WilliamsInputHeader.natWord_eq,List.length_append,List.length_replicate,
        List.length_cons,binary_length];omega
    exact keep0.1.trans (ah0.trans (by rw [hn];omega))
  · change focused.final.tapes (slots 0)=_
    rw [ft,bf];rfl
  · change focused.final.heads (slots 0)=_
    rw [fh,bf];rfl
  · change focused.final.tapes (slots 1)=_
    rw [ft,bf];rfl
  · change focused.final.heads (slots 1)=_
    rw [fh,bf];rfl
  · change focused.final.tapes (slots 2)=_
    rw [ft,bf];rfl
  · change focused.final.heads (slots 2)=_
    rw [fh,bf];rfl
  · change focused.final.tapes (slots 3)=_
    rw [ft,bf];rfl
  · change focused.final.heads (slots 3)=_
    rw [fh,bf];rfl
  · change a.steps+1+focused.steps≤_
    rw [fs]
    unfold budget
    omega

end NearCubicWires.RepairOrdinary.CloseoutRowsRawAtomNative
