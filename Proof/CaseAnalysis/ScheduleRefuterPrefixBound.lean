import Proof.CaseAnalysis.ScheduleRefuterPrefixRun
import Proof.CaseAnalysis.ScheduleRefuter

/-! One fixed all-length schedule/refuter prefix for the paper's common
language. The actual selected source supplies its own onset and polynomial
refuter budget; every short length follows the canonical false branch. -/
namespace NearCubicWires.RepairSource.CloseoutSchedule.RefuterPrefix
open LocalBitMultitape RepairOrdinary OrdinaryOracleCompose
open CloseoutRetainedRefuter
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def sourcePort (w : Nat):=Guarded.fresh w 8
def flagPort (w : Nat):=Guarded.fresh w 4
def addressPort (w : Nat):=Guarded.old w (Cold.extra w 0)
def selectedProgram (sources : EightSources) (k D copies : Nat)
    (clock : OrdinaryClock (fun n=>n^(k+2))) (A B onset : Nat) (r : OrdinaryOracleProgram):=
  program (Guarded.machine (Cold.machine sources k D copies clock A B) onset) r
    (sourcePort (Step.workTapes sources k D)) (flagPort (Step.workTapes sources k D))

theorem budget_bound (a d b e n N : Nat) (hN : N≤2^n) :
    a*(2^n+1)^d+16*(b*(N+2)^e+1)+4≤
      32*(a+b*2^e+1)*(2^n+1)^(d+e+1):=by
  have h:=Nat.mul_le_mul_left 2 (Refuter.compose_bound a d b e n N hN)
  calc
    _≤2*(16*(a*(2^n+1)^d+b*(N+2)^e+1)):=by omega
    _≤2*(16*(a+b*2^e+1)*(2^n+1)^(d+e+1)):=h
    _=_:=by ring

theorem exists_selected (sources : EightSources) (k D copies cutoff : Nat)
    (clock : OrdinaryClock (fun n=>n^(k+2))) (hD : 1≤D)
    (M : OrdinaryWeakMachine) (hM : OrdinaryLittleO M (fun n=>n^(k+2))) :
    ∃ onset : Nat,1≤onset ∧ cutoff≤onset ∧ ∃ (r : OrdinaryOracleProgram) (A B C E : Nat),
      ∀ bits : List Bool,
        let w:=Step.workTapes sources k D
        let width:=CloseoutLanguage.widthAt sources k clock copies D
        let N:=Framed.selectedLength width bits.length
        let answer:=List.ofFn ((sources.hierarchy (fun n=>n^(k+2)) clock).output M N)
        ∃ cost≤C*(2^bits.length+1)^E,∃ out,
          Ready RecoveryOracle.correctedSat (selectedProgram sources k D copies clock A B onset r)
            cost (input r (Guarded.input w bits)) out ∧
          out (old r (addressPort w))=frame bits ∧
          out (old r (flagPort w))=[decide (onset≤N)] ∧
          out (fresh (Guarded.tapes w) r 0)=frame (if onset≤N then answer else []) ∧
          (onset≤N →
            (M.accepts N ((sources.hierarchy (fun n=>n^(k+2)) clock).output M N) ↔
              (sources.hierarchy (fun n=>n^(k+2)) clock).hierarchy.timedView.accepts N
                ((sources.hierarchy (fun n=>n^(k+2)) clock).output M N)=false) ∧
            ∃ qlen≤C*(2^bits.length+1)^E,
              out (bank r (sourcePort w) (clocked r).queryTape)=List.replicate qlen false):=by
  obtain ⟨b,e,start,r,_hb,_he,hrefuter⟩:=RecoveryRefuterReplay.polynomial_runs
    (sources.hierarchy (fun n=>n^(k+2)) clock) clock M hM
  let onset:=max (max 1 cutoff) start
  have ho:1≤onset:=(Nat.le_max_left 1 cutoff).trans (Nat.le_max_left _ _)
  have hcut:cutoff≤onset:=(Nat.le_max_right 1 cutoff).trans (Nat.le_max_left _ _)
  obtain ⟨A,B,hschedule⟩:=Guarded.exists_guarded sources k D copies onset clock hD ho
  let a:=Guarded.coefficient A B onset
  refine ⟨onset,ho,hcut,r,A,B,32*(a+b*2^e+1),(A+1)+e+1,?_⟩
  intro bits
  let w:=Step.workTapes sources k D
  let width:=CloseoutLanguage.widthAt sources k clock copies D
  let N:=Framed.selectedLength width bits.length
  let answer:=List.ofFn ((sources.hierarchy (fun n=>n^(k+2)) clock).output M N)
  obtain ⟨mid,hm,haddress,hflag,hword⟩:=hschedule bits
  have hf : mid (flagPort w)=[decide (onset≤N)]:=by
    simpa only [flagPort,N,width,Guarded.selected_guard _ _ _ ho] using hflag
  have hrun : decide (onset≤N)=true →
      OrdinaryOracleRuns RecoveryOracle.correctedSat r (List.replicate N true) answer (b*(N+2)^e):=by
    intro h
    have hn:onset≤N:=of_decide_eq_true h
    exact (hrefuter N ((Nat.le_max_right (max 1 cutoff) start).trans hn)).1
  obtain ⟨cost,hcost,out,hr,hret,hout,hquery⟩:=prefix_run
    (Guarded.machine (Cold.machine sources k D copies clock A B) onset) r
    (sourcePort w) (flagPort w) (Guarded.input w bits) mid (List.replicate N true) answer
    (decide (onset≤N)) hm hf hword hrun
  have hbnd:=budget_bound a (A+1) b e bits.length N (Framed.selectedLength_bound width bits.length)
  have ha : addressPort w≠sourcePort w:=Guarded.old_fresh w (Cold.extra w 0) 8
  have hfl : flagPort w≠sourcePort w:=by
    intro h
    have hv:=congrArg Fin.val h
    change Cold.tapes w+4=Cold.tapes w+8 at hv
    omega
  refine ⟨cost,hcost.trans hbnd,out,hr,(hret _ ha).trans haddress,(hret _ hfl).trans hf,?_,?_⟩
  · simpa using hout
  · intro hn
    have hs:start≤N:=(Nat.le_max_right (max 1 cutoff) start).trans hn
    obtain ⟨qlen,hqlen,hqt⟩:=hquery (decide_eq_true hn)
    refine ⟨(hrefuter N hs).2,qlen,?_,hqt⟩
    exact (hqlen.trans (by omega : b*(N+2)^e≤a*(2^bits.length+1)^(A+1)+16*(b*(N+2)^e+1)+4)).trans hbnd

end
end NearCubicWires.RepairSource.CloseoutSchedule.RefuterPrefix
