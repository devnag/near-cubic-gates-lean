import Proof.PCP.PCPPQueryClauseHeader
import Proof.PCP.PCPPQuerySupportSemantics

/-! The physically decoded systematic-bit count drives the complete skip
of the explicit support matrix. The source stops at the literal-list count
header, retaining the query index and reusable natural-field scratch. -/
namespace NearCubicWires.RepairOrdinary.PCPPQueryClauseMatrix
open LocalBitMultitape RepairSource.VerifierDecoding PCPPQueryField
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def skipEntry (source : List Bool) (pos arity count : ℕ) :
    Configuration 4 (Fintype.card (RepeatMachine.Control 5)) :=
  ⟨PCPPQueryRows.skip.start,![1,pos,0,1],![UnaryTemplate.tape arity,source,[],UnaryTemplate.tape count]⟩
def skipCapacity (count : ℕ) : Fin 4→ℕ := fun i => if i=3 then count+2 else 0

theorem skip_run (pre : List Bool) (rows : List (List Bool)) (tail : List Bool) (arity : ℕ)
    (hw : ∀ r∈rows,r.length=arity) :
    ∃ r,runFrom PCPPQueryRows.skip (rows.length*(2*arity+7)+3)
      (skipEntry (pre++rows.flatten++tail) pre.length arity rows.length)=some r ∧
      r.final.tapes=![UnaryTemplate.tape arity,pre++rows.flatten++tail,[],UnaryTemplate.tape rows.length] ∧
      r.final.heads=![1,pre.length+rows.flatten.length,0,1] ∧
      r.steps=rows.length*(2*arity+7)+3 := by
  obtain ⟨base,hb,hbf,hbs⟩ := PCPPQueryRows.skip_run arity pre rows tail [] hw
  obtain ⟨r,hr,hf,hs,_⟩ := ZeroPadding.run_config PCPPQueryRows.skip (skipCapacity rows.length) _ _ base hb
  have he : ZeroPadding.config (skipCapacity rows.length)
      (PCPPQueryRows.cfg 0 arity (pre++rows.flatten++tail) pre.length [] rows.length 1)=
      skipEntry (pre++rows.flatten++tail) pre.length arity rows.length := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> simp [ZeroPadding.config,skipCapacity,PCPPQueryRows.cfg,
        RepeatMachine.cfg,controlConfig,TapeEmbedding.config,MatrixRawBlock.config,Fin.addCases,
        skipEntry,PCPPQuerySupport.template_pad]
  rw [he] at hr
  refine ⟨r,hr,?_,?_,hs.trans hbs⟩
  · rw [hf,hbf]
    funext i; fin_cases i <;> simp [ZeroPadding.config,skipCapacity,PCPPQueryRows.cfg,
      RepeatMachine.cfg,controlConfig,TapeEmbedding.config,MatrixRawBlock.config,Fin.addCases,PCPPQuerySupport.template_pad]
  · rw [hf,hbf]
    funext i; fin_cases i <;> rfl

def slots : Fin 4→Fin 16 := ![13,0,12,10]
noncomputable def scan := RecoveryFocus.machine slots PCPPQueryRows.skip
noncomputable def machine := Composition.machine PCPPQueryClauseHeader.machine scan
def budget (a b c arity : ℕ) := PCPPQueryClauseHeader.budget a b c+a*(2*arity+7)+4

theorem matrix_run (a b c arity index : ℕ) (rows : List (List Bool)) (tail : List Bool)
    (hc : rows.length=a) (hw : ∀ r∈rows,r.length=arity) :
    let source := fourBits 3 a b c++rows.flatten++tail
    ∃ r,runFrom machine (budget a b c arity)
      (Composition.leftConfig (Fintype.card (RepeatMachine.Control 5))
        (PCPPQueryClauseHeader.entry source arity index))=some r ∧
      r.steps≤budget a b c arity ∧
      r.final.tapes 0=source ∧ r.final.heads 0=(fourBits 3 a b c).length+rows.flatten.length ∧
      r.final.tapes 11=saved c (saved b (saved 3 [])) ∧ r.final.heads 11=0 ∧
      r.final.tapes 12=[] ∧ r.final.heads 12=0 ∧
      r.final.tapes 14=UnaryTemplate.tape index ∧ r.final.heads 14=1 ∧
      r.final.tapes 15=[] ∧ r.final.heads 15=0 := by
  dsimp only
  let fields := fourBits 3 a b c
  let source := fields++rows.flatten++tail
  obtain ⟨first,hfirst,hfs,hsource,hsourceHead,hsys,hsysHead,hscratch,hscratchHead,
    hdiscard,hdiscardHead,harity,harityHead,hindex,hindexHead,hout,houtHead⟩ :=
    PCPPQueryClauseHeader.header_run a b c arity index (rows.flatten++tail)
  have hword : fourBits 3 a b c++(rows.flatten++tail)=source := by simp [source,fields,List.append_assoc]
  rw [hword] at hfirst hsource
  obtain ⟨base,hb,hbt,hbh,hbs⟩ := skip_run fields rows tail arity hw
  rw [hc] at hb hbt hbs
  obtain ⟨focused,hf,hff,hfsteps⟩ := RecoveryFocus.run_config slots (by decide) PCPPQueryRows.skip
    first.final.heads first.final.tapes _ _ base hb
  have he : RecoveryFocus.config slots first.final.heads first.final.tapes
      (skipEntry source fields.length arity a)=Composition.restart first.final scan.start := by
    apply WilliamsSourceCrop.focus_same
    · intro i
      fin_cases i
      · exact harityHead
      · exact hsourceHead
      · exact hdiscardHead
      · exact hsysHead
    · intro i
      fin_cases i
      · exact harity
      · exact hsource
      · exact hdiscard
      · exact hsys
  rw [he] at hf
  have hj := Composition.run_join PCPPQueryClauseHeader.machine scan _ _ _ first focused hfirst hf
  have ht : PCPPQueryClauseHeader.budget a b c+1+(a*(2*arity+7)+3)=budget a b c arity := by unfold budget; omega
  rw [ht] at hj
  have ft (i : Fin 4) : focused.final.tapes (slots i)=base.final.tapes i := by
    simp only [hff,RecoveryFocus.config,RecoveryFocus.pick_slot slots (by decide)]
  have fh (i : Fin 4) : focused.final.heads (slots i)=base.final.heads i := by
    simp only [hff,RecoveryFocus.config,RecoveryFocus.pick_slot slots (by decide)]
  have other (i : Fin 16) (hi : RecoveryFocus.pick slots i=none) :
      focused.final.tapes i=first.final.tapes i ∧ focused.final.heads i=first.final.heads i := by
    simp [hff,RecoveryFocus.config,hi]
  refine ⟨Composition.joinedReceipt first focused,hj,?_,(ft 1).trans (by rw [hbt]; rfl),
    (fh 1).trans (by rw [hbh]; rfl),(other 11 (by decide)).1.trans hscratch,(other 11 (by decide)).2.trans hscratchHead,
    (ft 2).trans (by rw [hbt]; rfl),(fh 2).trans (by rw [hbh]; rfl),
    (other 14 (by decide)).1.trans hindex,(other 14 (by decide)).2.trans hindexHead,
    (other 15 (by decide)).1.trans hout,(other 15 (by decide)).2.trans houtHead⟩
  change first.steps+1+focused.steps≤_
  rw [hfsteps,hbs]
  unfold budget
  omega

end NearCubicWires.RepairOrdinary.PCPPQueryClauseMatrix
