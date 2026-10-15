import Proof.CaseAnalysis.RowsRawPairCopy
import Proof.CaseAnalysis.RowsRawPairSeek

/-! One occurrence block reads the actual adjacent X/C entries from the
source-produced cache and emits their raw sum. Both cache entries are used
without column-dependent syntax or an additional cache representation. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsRawPairRead
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch
open CloseoutRowsRawPolynomialAdd
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def seekSlots : Fin 2→Fin 5:=![0,1]
noncomputable def seek:=RecoveryFocus.machine seekSlots CloseoutRowsRawPairSeek.machine
noncomputable def machine:=Composition.machine seek CloseoutRowsRawPairCopy.machine
def budget (ps : List CloseoutRowsRawPairSeek.Pair) (p : CloseoutRowsRawPairSeek.Pair):=
  CloseoutRowsRawPairSeek.budget ps+5+CloseoutRowsRawPairCopy.budget p

theorem seek_run (C : ℕ) (ps : List CloseoutRowsRawPairSeek.Pair) (ip it cp ct out : List Bool) :
    Step seek (CloseoutRowsRawPairSeek.budget ps+4) (heads ip.length cp.length out)
      (data C (ip++ExtIncidence.block ps.length++it) (cp++CloseoutRowsRawPairSeek.cacheWord ps++ct) out)
      (heads (ip.length+(ExtIncidence.block ps.length).length)
        (cp.length+(CloseoutRowsRawPairSeek.cacheWord ps).length) out)
      (data C (ip++ExtIncidence.block ps.length++it) (cp++CloseoutRowsRawPairSeek.cacheWord ps++ct) out) := by
  obtain ⟨raw,hr,rh,rt,_⟩:=CloseoutRowsRawPairSeek.seek_run ps ip it cp ct
  obtain ⟨r,rr,_rc,_rs,h,t,keep⟩:=RecoveryFocus.dock seekSlots (by decide)
    CloseoutRowsRawPairSeek.machine _ (heads ip.length cp.length out)
    (data C (ip++ExtIncidence.block ps.length++it) (cp++CloseoutRowsRawPairSeek.cacheWord ps++ct) out) _
    (by intro i;fin_cases i <;> rfl) (by intro i;fin_cases i <;> rfl) raw hr
  refine Step.of_run rr ?_ ?_
  · funext i;fin_cases i
    · exact (h 0).trans (congrArg (fun H=>H 0) rh)
    · exact (h 1).trans (congrArg (fun H=>H 1) rh)
    all_goals exact (keep _ (by intro j;fin_cases j <;> decide)).1
  · funext i;fin_cases i
    · exact (t 0).trans (congrArg (fun T=>T 0) rt)
    · exact (t 1).trans (congrArg (fun T=>T 1) rt)
    all_goals exact (keep _ (by intro j;fin_cases j <;> decide)).2

theorem read_run (C : ℕ) (ps : List CloseoutRowsRawPairSeek.Pair) (p : CloseoutRowsRawPairSeek.Pair)
    (ip it tail out : List Bool) (hc : 1≤C) :
    Step machine (budget ps p) (heads ip.length 0 out)
      (data C (ip++ExtIncidence.block ps.length++it)
        (CloseoutRowsRawPairSeek.cacheWord ps++CloseoutRowsRawPairSeek.word p++tail) out)
      (heads (ip.length+(ExtIncidence.block ps.length).length)
        ((CloseoutRowsRawPairSeek.cacheWord ps).length+(CloseoutRowsRawPairSeek.word p).length)
        (out++ExtIncidence.stream (p.1++p.2)))
      (data C (ip++ExtIncidence.block ps.length++it)
        (CloseoutRowsRawPairSeek.cacheWord ps++CloseoutRowsRawPairSeek.word p++tail)
        (out++ExtIncidence.stream (p.1++p.2))) := by
  have first:=seek_run C ps ip it [] (CloseoutRowsRawPairSeek.word p++tail) out
  simp only [List.nil_append,List.length_nil,Nat.zero_add] at first
  have last:=CloseoutRowsRawPairCopy.copy_run C (ip.length+(ExtIncidence.block ps.length).length)
    (ip++ExtIncidence.block ps.length++it) (CloseoutRowsRawPairSeek.cacheWord ps) tail out p hc
  simp only [List.append_assoc] at first last
  have all:=first.seq last
  have cost:CloseoutRowsRawPairSeek.budget ps+4+1+CloseoutRowsRawPairCopy.budget p=budget ps p:=by
    unfold budget;omega
  rw [cost] at all
  simpa only [machine,List.append_assoc] using all

theorem budget_bound (ps : List CloseoutRowsRawPairSeek.Pair) (p : CloseoutRowsRawPairSeek.Pair) :
    budget ps p≤64*((CloseoutRowsRawPairSeek.cacheWord ps).length+
      (CloseoutRowsRawPairSeek.word p).length+ps.length+2) := by
  have copied:=CloseoutRowsRawPairCopy.budget_bound p
  unfold budget CloseoutRowsRawPairSeek.budget
  omega

end NearCubicWires.RepairOrdinary.CloseoutRowsRawPairRead
