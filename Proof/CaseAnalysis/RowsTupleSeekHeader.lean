import Proof.CaseAnalysis.RowsTupleSeekPairs
import Proof.PCP.PCPPQueryNatural
import Proof.MachineModel.OrdinaryMatrixNaturalHeader
import Proof.PCP.PCPPQueryField

/-! The gate count is read from the same native record being selected.
Its actual width and binary fields reconstruct that identical native header;
the family source is read once and its cursor is retained. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsTupleSeek
open LocalBitMultitape RecoveryRootRound ExtDecompositionBatch RepairRepresentation SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def headerExtraHeads (out : List Bool) : Fin 4→ℕ := ![0,0,0,out.length]
def headerExtraData (out : List Bool) : Fin 4→List Bool := ![[],[],[],out]
def headerSlots : Fin 4→Fin 15 := ![4,1,11,12]
def headerCopySlots : Fin 3→Fin 15 := ![11,13,14]
noncomputable def headerFirst := TapeEmbedding.machine 4 PCPPQueryNatural.machine
noncomputable def headerWrite := RecoveryFocus.machine headerSlots MatrixNaturalHeader.resetMachine
noncomputable def headerCopy (keep : Bool) := RecoveryFocus.machine headerCopySlots (PCPPQueryField.machine keep)
noncomputable def headerMachine (keep : Bool) :=
  Composition.machine (Composition.machine headerFirst headerWrite) (headerCopy keep)
noncomputable def headerInput (source : List Bool) (pos : ℕ) (out : List Bool) :=
  TapeEmbedding.config (headerExtraHeads out) (headerExtraData out) (PCPPQueryNatural.entry source pos)
noncomputable def headerEntry (keep : Bool) (source : List Bool) (pos : ℕ) (out : List Bool) :=
  (⟨(headerMachine keep).start,(headerInput source pos out).heads,
    (headerInput source pos out).tapes⟩ : Configuration 15 _)
def headerCost (n : ℕ) := PCPPQueryNatural.budget n+8*natBitLength n+11

theorem header_run (keep : Bool) (pre tail out : List Bool) (n : ℕ) :
    ∃ r,runFrom (headerMachine keep) (headerCost n)
      (headerEntry keep (pre++natWord n++tail) pre.length out)=some r ∧
      r.final.tapes 0=pre++natWord n++tail ∧ r.final.heads 0=pre.length+(natWord n).length ∧
      r.final.tapes 10=UnaryTemplate.tape n ∧ r.final.heads 10=1 ∧
      r.final.tapes 14=out++selected keep (natWord n) ∧
      r.final.heads 14=(out++selected keep (natWord n)).length ∧ r.steps ≤ headerCost n := by
  let source := pre++natWord n++tail
  obtain ⟨a,ha,at0,ah0,at1,ah1,_at3,_ah3,at4,ah4,at10,ah10,as⟩ :=
    MatrixDimensionPrepare.prepare_run pre tail (natBitLength n) n
      (by simpa only [natBitLength] using Nat.lt_pow_succ_log_self (b:=2) (by decide) n)
  have hs : pre++List.replicate (natBitLength n) true++false::(binary (natBitLength n) n++tail)=source := by
    simp [source,WilliamsInputHeader.natWord_eq,List.append_assoc]
  rw [hs] at ha at0
  have hi : Composition.leftConfig _ (MatrixDimensionPrepare.input source pre.length)=
      PCPPQueryNatural.entry source pre.length := by
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;> simp [MatrixDimensionPrepare.input,MatrixDimensionField.input,MatrixDimensionHeader.input,
        TapeEmbedding.config,PCPPQueryNatural.entry,Fin.addCases,Composition.leftConfig]
    · funext i;fin_cases i <;> simp [MatrixDimensionPrepare.input,MatrixDimensionField.input,MatrixDimensionHeader.input,
        TapeEmbedding.config,PCPPQueryNatural.entry,Fin.addCases,Composition.leftConfig]
  rw [hi] at ha
  let a' := TapeEmbedding.receipt (headerExtraHeads out) (headerExtraData out) a
  have first := TapeEmbedding.run_embed PCPPQueryNatural.machine (headerExtraHeads out)
    (headerExtraData out) _ _ a ha
  obtain ⟨b,hb,bt0,bt1,bt2,bh,bs⟩ := MatrixNaturalHeader.natural_run n
  obtain ⟨w,hw,_wc,ws,wh,wt,wkeep⟩ := RecoveryFocus.dock headerSlots (by decide)
    MatrixNaturalHeader.resetMachine _ a'.final.heads a'.final.tapes
    (initialConfiguration MatrixNaturalHeader.resetMachine
      (MatrixNaturalHeader.resetInput (binary (natBitLength n) n)))
    (by intro i;fin_cases i
        · exact ah4
        · exact ah1
        all_goals rfl)
    (by intro i;fin_cases i
        · exact at4
        · change a.final.tapes 1=List.replicate (binary (natBitLength n) n).length true
          rw [binary_length];exact at1
        all_goals rfl) b hb
  have joined := Composition.run_join headerFirst headerWrite _ _ _ a' w first hw
  obtain ⟨c,hc,cf,cs⟩ := PCPPQueryField.nat_run keep [] [] [] out n
  obtain ⟨z,hz,_zc,zs,zh,zt,zkeep⟩ := RecoveryFocus.dock headerCopySlots (by decide)
    (PCPPQueryField.machine keep) _ w.final.heads w.final.tapes
    (PCPPQueryField.cfg 0 ([]++natWord n++[]) 0 [] 0 out)
    (by intro i;fin_cases i
        · exact (wh 2).trans (bh 2)
        · exact (wkeep 13 (by decide)).1
        · exact (wkeep 14 (by decide)).1)
    (by intro i;fin_cases i
        · change w.final.tapes 11=[]++natWord n++[]
          simpa only [show headerSlots 2=11 by rfl,List.nil_append,List.append_nil] using (wt 2).trans bt2
        · exact (wkeep 13 (by decide)).2
        · exact (wkeep 14 (by decide)).2) c hc
  have whole := Composition.run_join (Composition.machine headerFirst headerWrite) (headerCopy keep)
    _ _ _ (Composition.joinedReceipt a' w) z joined hz
  have time : MatrixDimensionPrepare.budget (natBitLength n) n+1+(6*natBitLength n+6)+1+(2*natBitLength n+3)=headerCost n := by
    unfold headerCost PCPPQueryNatural.budget;omega
  rw [time] at whole
  have keep (i : Fin 15) (h0 : i=0 ∨ i=10) :
      z.final.heads i=a'.final.heads i ∧ z.final.tapes i=a'.final.tapes i := by
    have hw' : ∀ j,headerSlots j≠i := by rcases h0 with rfl|rfl <;> decide
    have hz' : ∀ j,headerCopySlots j≠i := by rcases h0 with rfl|rfl <;> decide
    exact ⟨(zkeep i hz').1.trans (wkeep i hw').1,(zkeep i hz').2.trans (wkeep i hw').2⟩
  refine ⟨Composition.joinedReceipt (Composition.joinedReceipt a' w) z,whole,
    (keep 0 (by simp)).2.trans at0,?_,(keep 10 (by simp)).2.trans at10,
    (keep 10 (by simp)).1.trans ah10,?_,?_,?_⟩
  · exact (keep 0 (by simp)).1.trans (ah0.trans (by
      simp only [WilliamsInputHeader.natWord_eq,List.length_append,List.length_replicate,
        List.length_cons,binary_length];omega))
  · exact (zt 2).trans (by rw [cf];rfl)
  · exact (zh 2).trans (by rw [cf];rfl)
  · change a.steps+1+w.steps+1+z.steps ≤ _
    rw [ws,zs,bs,cs]
    unfold headerCost PCPPQueryNatural.budget
    omega

end NearCubicWires.RepairOrdinary.CloseoutRowsTupleSeek
