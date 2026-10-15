import Proof.CaseAnalysis.RowsRawPolynomialSkip

/-! A raw variable block drives selection in the already-produced atom
cache. The actual prefix polynomials are scanned once, with no numeric
index conversion, count prepass, or discarded output. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsRawAtomSeek
open LocalBitMultitape RecoveryExecution RecoveryRootRound ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def heads (ip cp : ℕ) : Fin 2→ℕ:=![ip,cp]
def data (index cache : List Bool) : Fin 2→List Bool:=![index,cache]
def slots : Fin 1→Fin 2:=fun _=>1
noncomputable def skip:=RecoveryFocus.machine slots CloseoutRowsRawPolynomialSkip.machine
def advance : Machine 2 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>decide (q=1)
  rule:=fun q _=>if q=0 then some ⟨1,fun _=>none,![.right,.stay]⟩ else none
noncomputable def body:=Composition.machine skip advance
def idle : Machine 2 1 where
  descriptionBits:=0
  start:=0
  halted:=fun _=>true
  rule:=fun _ _=>none
def sizes : Fin 2→ℕ:=![1,6]
noncomputable def programs : (i : Fin 2)→Machine 2 (sizes i)
  | ⟨0,_⟩=>idle
  | ⟨1,_⟩=>body
  | ⟨n+2,h⟩=>False.elim (by omega)
def next (i : Fin 2) (_ : Fin (sizes i)) (bits : Fin 2→Bool) : Option (Fin 2):=
  if i=0 then if bits 0 then some 1 else none else some 0
noncomputable def loop:=RecoveryCalls.machine sizes programs 0 next
noncomputable def entry (i : Fin 2) (ip cp : ℕ) (index cache : List Bool):=
  controlConfig (RecoveryCalls.code sizes i)
    (⟨(programs i).start,heads ip cp,data index cache⟩ : Configuration 2 (sizes i))
noncomputable def final (ip cp : ℕ) (index cache : List Bool):=
  RecoveryCalls.stopped sizes (heads ip cp) (data index cache)
def cacheWord (ps : List (List (List ℕ))):=ps.flatMap ExtIncidence.stream
def budget (ps : List (List (List ℕ))):=(cacheWord ps).length+4*ps.length+1
noncomputable def machine:=Composition.machine (Composition.machine advance loop) advance

theorem advance_run (ip cp : ℕ) (index cache : List Bool) :
    Step advance 1 (heads ip cp) (data index cache) (heads (ip+1) cp) (data index cache) := by
  have hs:step advance ⟨0,heads ip cp,data index cache⟩=
      some ⟨1,heads (ip+1) cp,data index cache⟩:=by
    simp only [step,advance,↓reduceIte,Option.map_some]
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;> rfl
    · rfl
  obtain ⟨r,hr,rf,_⟩:=(Timed.single (by rfl) hs).run (by rfl)
  exact Step.of_run hr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)

theorem skip_run (ip : ℕ) (index pre tail : List Bool) (p : List (List ℕ)) :
    Step skip (ExtIncidence.stream p).length (heads ip pre.length)
      (data index (pre++ExtIncidence.stream p++tail))
      (heads ip (pre.length+(ExtIncidence.stream p).length))
      (data index (pre++ExtIncidence.stream p++tail)) := by
  obtain ⟨raw,hr,rh,rt,_⟩:=CloseoutRowsRawPolynomialSkip.skip_run p pre tail
  obtain ⟨r,rr,_rc,_rs,h,t,keep⟩:=RecoveryFocus.dock slots (by decide)
    CloseoutRowsRawPolynomialSkip.machine _ (heads ip pre.length)
    (data index (pre++ExtIncidence.stream p++tail)) _
    (by intro i;fin_cases i;rfl) (by intro i;fin_cases i;rfl) raw hr
  have other:=keep 0 (by intro i;fin_cases i;decide)
  refine Step.of_run rr ?_ ?_
  · funext i;fin_cases i
    · exact other.1
    · exact (h 0).trans (congrArg (fun H=>H 0) rh)
  · funext i;fin_cases i
    · exact other.2
    · exact (t 0).trans (congrArg (fun T=>T 0) rt)

theorem body_run (ip : ℕ) (index pre tail : List Bool) (p : List (List ℕ)) :
    Step body ((ExtIncidence.stream p).length+2) (heads ip pre.length)
      (data index (pre++ExtIncidence.stream p++tail))
      (heads (ip+1) (pre.length+(ExtIncidence.stream p).length))
      (data index (pre++ExtIncidence.stream p++tail)) := by
  have first:=skip_run ip index pre tail p
  have last:=advance_run ip (pre.length+(ExtIncidence.stream p).length)
    index (pre++ExtIncidence.stream p++tail)
  simpa only [body,Nat.add_assoc] using first.seq last

theorem probe (pre tail cache : List Bool) (cp : ℕ) :
    Timed loop 1 (entry 0 pre.length cp (pre++true::tail) cache)
      (entry 1 pre.length cp (pre++true::tail) cache) := by
  have hn:next 0 (programs 0).start
      (⟨(programs 0).start,heads pre.length cp,data (pre++true::tail) cache⟩ :
        Configuration 2 (sizes 0)).scanned=some 1:=by
    simp [next,Configuration.scanned,heads,data,Streaming.read_append]
  exact Timed.single (by simp [loop,entry,RecoveryCalls.machine,controlConfig,RecoveryCalls.code])
    (RecoveryCalls.return_step sizes programs 0 next 0 1 _ (by rfl) hn)

theorem stop (pre tail cache : List Bool) (cp : ℕ) :
    Timed loop 1 (entry 0 pre.length cp (pre++false::tail) cache)
      (final pre.length cp (pre++false::tail) cache) := by
  have hn:next 0 (programs 0).start
      (⟨(programs 0).start,heads pre.length cp,data (pre++false::tail) cache⟩ :
        Configuration 2 (sizes 0)).scanned=none:=by
    simp [next,Configuration.scanned,heads,data,Streaming.read_append]
  exact Timed.single (by simp [loop,entry,RecoveryCalls.machine,controlConfig,RecoveryCalls.code])
    (RecoveryCalls.stop_step sizes programs 0 next 0 _ (by rfl) hn)

theorem round (ip : ℕ) (index pre tail : List Bool) (p : List (List ℕ)) :
    ∃ time≤(ExtIncidence.stream p).length+3,Timed loop time
      (entry 1 ip pre.length index (pre++ExtIncidence.stream p++tail))
      (entry 0 (ip+1) (pre.length+(ExtIncidence.stream p).length)
        index (pre++ExtIncidence.stream p++tail)) := by
  obtain ⟨r,hr,rh,rt,_⟩:=body_run ip index pre tail p
  obtain ⟨time,ht,tr⟩:=call_receipt sizes programs 0 next 1 0 _ _ r hr (by rfl)
  have same:RecoveryCalls.restarted (programs 0) r.final.heads r.final.tapes=
      ⟨(programs 0).start,heads (ip+1) (pre.length+(ExtIncidence.stream p).length),
        data index (pre++ExtIncidence.stream p++tail)⟩:=by
    apply configuration_ext
    · rfl
    · exact rh
    · exact rt
  rw [same] at tr
  exact ⟨time,by omega,tr⟩

theorem remaining (ps : List (List (List ℕ))) (ip it cp ct : List Bool) :
    ∃ time≤budget ps,Timed loop time
      (entry 0 ip.length cp.length (ip++List.replicate ps.length true++false::it)
        (cp++cacheWord ps++ct))
      (final (ip.length+ps.length) (cp.length+(cacheWord ps).length)
        (ip++List.replicate ps.length true++false::it) (cp++cacheWord ps++ct)) := by
  induction ps generalizing ip cp with
  | nil=>simpa [budget,cacheWord] using
      (show ∃ time≤1,Timed loop time (entry 0 ip.length cp.length (ip++false::it) (cp++ct))
        (final ip.length cp.length (ip++false::it) (cp++ct)) from ⟨1,by omega,stop ip it (cp++ct) cp.length⟩)
  | cons p ps ih=>
    let index:=ip++true::(List.replicate ps.length true++false::it)
    obtain ⟨first,hfirst,tr⟩:=round ip.length index cp (cacheWord ps++ct) p
    obtain ⟨rest,hrest,tailTrace⟩:=ih (ip++[true]) (cp++ExtIncidence.stream p)
    have start:=probe ip (List.replicate ps.length true++false::it)
      (cp++ExtIncidence.stream p++cacheWord ps++ct) cp.length
    have isource:(ip++[true])++List.replicate ps.length true++false::it=index:=by
      simp [index,List.append_assoc]
    rw [isource] at tailTrace
    simp only [List.length_append,List.length_singleton,List.append_assoc] at tr tailTrace
    simp only [List.append_assoc] at start
    have all:=start.trans (tr.trans tailTrace)
    refine ⟨1+(first+rest),?_,?_⟩
    · simp only [budget,cacheWord,List.flatMap_cons,List.length_append,List.length_cons] at *
      omega
    · simpa only [index,List.length_cons,List.replicate_succ,List.cons_append,
        cacheWord,List.flatMap_cons,List.length_append,List.append_assoc,Nat.add_assoc,
        Nat.add_comm,Nat.add_left_comm] using all

theorem loop_run (ps : List (List (List ℕ))) (ip it cp ct : List Bool) :
    Step loop (budget ps) (heads ip.length cp.length)
      (data (ip++List.replicate ps.length true++false::it) (cp++cacheWord ps++ct))
      (heads (ip.length+ps.length) (cp.length+(cacheWord ps).length))
      (data (ip++List.replicate ps.length true++false::it) (cp++cacheWord ps++ct)) := by
  obtain ⟨time,ht,tr⟩:=remaining ps ip it cp ct
  obtain ⟨r,hr,rf,_⟩:=tr.run (by simp [loop,final,RecoveryCalls.machine,RecoveryCalls.stopped])
  have more:=runFrom_moreFuel loop time (budget ps-time) _ r hr
  rw [Nat.add_sub_of_le ht] at more
  exact Step.of_run more (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)

theorem seek_run (ps : List (List (List ℕ))) (ip it cp ct : List Bool) :
    Step machine (budget ps+4) (heads ip.length cp.length)
      (data (ip++ExtIncidence.block ps.length++it) (cp++cacheWord ps++ct))
      (heads (ip.length+(ExtIncidence.block ps.length).length) (cp.length+(cacheWord ps).length))
      (data (ip++ExtIncidence.block ps.length++it) (cp++cacheWord ps++ct)) := by
  let index:=ip++ExtIncidence.block ps.length++it
  let cache:=cp++cacheWord ps++ct
  have first:=advance_run ip.length cp.length index cache
  have middle:=loop_run ps (ip++[true]) it cp ct
  have source:(ip++[true])++List.replicate ps.length true++false::it=index:=by
    simp [index,ExtIncidence.block,List.replicate_succ,List.append_assoc]
  rw [source] at middle
  simp only [List.length_append,List.length_singleton] at middle
  have last:=advance_run (ip.length+1+ps.length) (cp.length+(cacheWord ps).length) index cache
  have all:=(first.seq middle).seq last
  have time:1+1+budget ps+1+1=budget ps+4:=by omega
  rw [time] at all
  have pos:ip.length+1+ps.length+1=ip.length+(ExtIncidence.block ps.length).length:=by
    rw [ExtIncidence.block_length];omega
  simpa only [machine,pos,index,cache] using all

end NearCubicWires.RepairOrdinary.CloseoutRowsRawAtomSeek
