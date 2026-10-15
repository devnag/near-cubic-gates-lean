import Proof.CaseAnalysis.RowsEstimatorReuseAppend
import Proof.CaseAnalysis.RowsEstimatorReuseErase

/-! The exact post-estimator append and sweep. Every private tape is erased
after the six-field record has reached the retained growing scalar stream. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Reuse
open LocalBitMultitape RecoveryRootRound CloseoutRowsEstimatorCoefficients
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def after (p : Program):=Composition.machine (append p) (erase p)
def afterBudget (b D : ℕ):=2*D+40*b+61

theorem after_run (p : Program) (b : ℕ) (q : CompetitorValidity.Estimate) (count denominator D : ℕ)
    (out : List Bool) (H : Fin (tapes p)→ℕ) (A : Fin (tapes p)→List Bool)
    (hD:20*b+27≤D+1)
    (hrecord:A (old p (Whole.recordSlot p))=ZeroPadding.pad D (Stream.recordWord b q count denominator))
    (hout:A (output p)=out) (hlog:A (log p)=List.replicate (D+1) false)
    (hdriver:A (driver p)=List.replicate D true)
    (hh:∀ i,i≠output p→ H i=0) (hohead:H (output p)=out.length)
    (hs:∀ i,(A (work p i)).length≤D) :
    ∃ r,runFrom (after p) (afterBudget b D) ⟨(after p).start,H,A⟩=some r ∧
      r.steps≤afterBudget b D ∧
      r.final.heads=Function.update H (output p) (out++Stream.recordWord b q count denominator).length ∧
      r.final.tapes=install (eraseSlots p) (Function.update A (output p) (out++Stream.recordWord b q count denominator)) (erased p D):=by
  have old_ne:old p (Whole.recordSlot p)≠output p:=by
    intro he
    have hv:=congrArg Fin.val he
    have hi:=(Whole.recordSlot p).isLt
    simp only [old,output,Fin.val_castAdd,Fin.val_natAdd] at hv
    omega
  have log_ne:log p≠output p:=by
    intro he
    have hv:=congrArg Fin.val he
    simp only [log,output,Fin.val_castAdd,Fin.val_natAdd] at hv
    omega
  have driver_ne:driver p≠output p:=by
    intro he
    have hv:=congrArg Fin.val he
    simp only [driver,output,Fin.val_natAdd] at hv
    omega
  obtain ⟨first,hf,fs,fh,ft⟩:=append_run p b q count denominator D out H A hD hrecord hout hlog
    (hh _ old_ne) hohead (hh _ log_ne)
  let H':=Function.update H (output p) (out++Stream.recordWord b q count denominator).length
  let A':=Function.update A (output p) (out++Stream.recordWord b q count denominator)
  have hhe:∀ j,H' (eraseSlots p j)=0:=by
    intro j
    have hn:=erase_avoids p (output p) (Or.inr (Or.inr rfl)) j
    exact (Function.update_of_ne hn _ _).trans (hh _ hn)
  have hse:∀ i,(A' (work p i)).length≤D:=by
    intro i
    have hn:=erase_avoids p (output p) (Or.inr (Or.inr rfl)) ((i.castAdd 1).castAdd 1)
    have hn':work p i≠output p:=by simpa only [erase_work] using hn
    have he:A' (work p i)=A (work p i):=Function.update_of_ne hn' _ _
    exact (congrArg List.length he).le.trans (hs i)
  obtain ⟨last,hl,ls,lh,lt,_lw,_ld,_ll,_lk⟩:=erase_run p D H' A' hhe hse
    ((Function.update_of_ne driver_ne _ _).trans hdriver)
    ((Function.update_of_ne log_ne _ _).trans hlog)
  have hi:Composition.restart first.final (erase p).start=⟨(erase p).start,H',A'⟩:=by
    apply configuration_ext
    · rfl
    · exact fh
    · exact ft
  have hl':runFrom (erase p) (2*D+4) (Composition.restart first.final (erase p).start)=some last:=by
    rw [hi]
    exact hl
  have whole:=Composition.run_join (append p) (erase p) _ _ _ first last hf hl'
  have ht:(40*b+56)+1+(2*D+4)=afterBudget b D:=by unfold afterBudget;omega
  rw [ht] at whole
  refine ⟨Composition.joinedReceipt first last,whole,?_,lh,lt⟩
  change first.steps+1+last.steps≤_
  unfold afterBudget
  omega

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Reuse
