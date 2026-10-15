import Proof.CaseAnalysis.RowsRawProductPair

/-! A raw left monomial is multiplied by every original right monomial.
The actual right stream controls the loop; duplicates and empty polynomials
are retained with no separately supplied enumeration count. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsRawProductRow
open LocalBitMultitape RecoveryExecution RecoveryRootRound ExtDecompositionBatch
open CloseoutRowsRawProductFields
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def idle : Machine 4 1 where
  descriptionBits:=0
  start:=0
  halted:=fun _=>true
  rule:=fun _ _=>none
def sizes : Fin 2→ℕ:=![1,12]
noncomputable def programs : (i : Fin 2)→Machine 4 (sizes i)
  | ⟨0,_⟩=>idle
  | ⟨1,_⟩=>CloseoutRowsRawProductPair.machine
  | ⟨n+2,h⟩=>False.elim (by omega)
def next (i : Fin 2) (_ : Fin (sizes i)) (bits : Fin 4→Bool) : Option (Fin 2):=
  if i=0 then if bits 1 then some 1 else none else some 0
noncomputable def machine:=RecoveryCalls.machine sizes programs 0 next
noncomputable def entry (i : Fin 2) (C lp rp : ℕ) (left right out : List Bool):=
  controlConfig (RecoveryCalls.code sizes i)
    (⟨(programs i).start,heads lp rp out,data C left right out⟩ : Configuration 4 (sizes i))
noncomputable def final (C lp rp : ℕ) (left right out : List Bool):=
  RecoveryCalls.stopped sizes (heads lp rp out) (data C left right out)
def budget (left : List ℕ) (right : List (List ℕ)):=
  (right.map (fun r=>CloseoutRowsRawProductPair.budget left r+2)).sum+1
def word (left : List ℕ) (right : List (List ℕ)):=
  (right.map (fun r=>left++r)).flatMap ExtIncidence.monomialWord

theorem probe (C lp : ℕ) (pre tail left out : List Bool) :
    Timed machine 1 (entry 0 C lp pre.length left (pre++true::tail) out)
      (entry 1 C lp pre.length left (pre++true::tail) out) := by
  have hn:next 0 (programs 0).start
      (⟨(programs 0).start,heads lp pre.length out,data C left (pre++true::tail) out⟩ :
        Configuration 4 (sizes 0)).scanned=some 1:=by
    simp [next,Configuration.scanned,heads,data,Streaming.read_append]
  exact Timed.single (by simp [machine,entry,RecoveryCalls.machine,controlConfig,RecoveryCalls.code])
    (RecoveryCalls.return_step sizes programs 0 next 0 1 _ (by rfl) hn)

theorem pair (C : ℕ) (left right : List ℕ) (lp lt rp rt out : List Bool)
    (hc : (left.flatMap ExtIncidence.block).length+1≤C) :
    ∃ time≤CloseoutRowsRawProductPair.budget left right+1,Timed machine time
      (entry 1 C lp.length rp.length (lp++left.flatMap ExtIncidence.block++false::lt)
        (rp++ExtIncidence.monomialWord right++rt) out)
      (entry 0 C lp.length (rp.length+(ExtIncidence.monomialWord right).length)
        (lp++left.flatMap ExtIncidence.block++false::lt) (rp++ExtIncidence.monomialWord right++rt)
        (out++ExtIncidence.monomialWord (left++right))) := by
  obtain ⟨r,hr,rh,rtapes,_⟩:=CloseoutRowsRawProductPair.pair_run C left right lp lt rp rt out hc
  obtain ⟨time,ht,trace⟩:=call_receipt sizes programs 0 next 1 0 _ _ r hr (by rfl)
  have same:RecoveryCalls.restarted (programs 0) r.final.heads r.final.tapes=
      ⟨(programs 0).start,heads lp.length (rp.length+(ExtIncidence.monomialWord right).length)
        (out++ExtIncidence.monomialWord (left++right)),
        data C (lp++left.flatMap ExtIncidence.block++false::lt) (rp++ExtIncidence.monomialWord right++rt)
          (out++ExtIncidence.monomialWord (left++right))⟩:=by
    apply configuration_ext
    · rfl
    · exact rh
    · exact rtapes
  rw [same] at trace
  exact ⟨time,ht,trace⟩

theorem stop (C lp : ℕ) (pre tail left out : List Bool) :
    Timed machine 1 (entry 0 C lp pre.length left (pre++false::tail) out)
      (final C lp pre.length left (pre++false::tail) out) := by
  have hn:next 0 (programs 0).start
      (⟨(programs 0).start,heads lp pre.length out,data C left (pre++false::tail) out⟩ :
        Configuration 4 (sizes 0)).scanned=none:=by
    simp [next,Configuration.scanned,heads,data,Streaming.read_append]
  exact Timed.single (by simp [machine,entry,RecoveryCalls.machine,controlConfig,RecoveryCalls.code])
    (RecoveryCalls.stop_step sizes programs 0 next 0 _ (by rfl) hn)

theorem remaining (C : ℕ) (left : List ℕ) (right : List (List ℕ))
    (lp lt rp rt out : List Bool) (hc : (left.flatMap ExtIncidence.block).length+1≤C) :
    ∃ time≤budget left right,Timed machine time
      (entry 0 C lp.length rp.length (lp++left.flatMap ExtIncidence.block++false::lt)
        (rp++ExtIncidence.stream right++rt) out)
      (final C lp.length (rp.length+(right.flatMap ExtIncidence.monomialWord).length)
        (lp++left.flatMap ExtIncidence.block++false::lt) (rp++ExtIncidence.stream right++rt)
        (out++word left right)) := by
  induction right generalizing rp out with
  | nil=>
    exact ⟨1,by simp [budget],by simpa [ExtIncidence.stream,word] using
      (stop C lp.length rp rt (lp++left.flatMap ExtIncidence.block++false::lt) out)⟩
  | cons r right ih=>
    obtain ⟨first,hfirst,firstTrace⟩:=pair C left r lp lt rp (ExtIncidence.stream right++rt) out hc
    obtain ⟨rest,hrest,restTrace⟩:=ih (rp++ExtIncidence.monomialWord r)
      (out++ExtIncidence.monomialWord (left++r))
    simp only [List.length_append,List.append_assoc] at firstTrace restTrace
    have start:=probe C lp.length rp
      (r.flatMap ExtIncidence.block++false::(ExtIncidence.stream right++rt))
      (lp++left.flatMap ExtIncidence.block++false::lt) out
    have st:rp++true::(r.flatMap ExtIncidence.block++false::(ExtIncidence.stream right++rt))=
        rp++ExtIncidence.monomialWord r++(ExtIncidence.stream right++rt):=by
      simp [ExtIncidence.monomialWord,List.append_assoc]
    rw [st] at start
    simp only [List.append_assoc] at start
    have all:=start.trans (firstTrace.trans restTrace)
    refine ⟨1+(first+rest),?_,?_⟩
    · simp only [budget,List.map_cons,List.sum_cons] at *
      omega
    · simpa only [ExtIncidence.stream_cons,List.flatMap_cons,List.length_append,word,
        List.map_cons,List.append_assoc,Nat.add_assoc] using all

theorem row_run (C : ℕ) (left : List ℕ) (right : List (List ℕ)) (lp lt out : List Bool)
    (hc : (left.flatMap ExtIncidence.block).length+1≤C) :
    Step machine (budget left right) (heads lp.length 0 out)
      (data C (lp++left.flatMap ExtIncidence.block++false::lt) (ExtIncidence.stream right) out)
      (heads lp.length (right.flatMap ExtIncidence.monomialWord).length (out++word left right))
      (data C (lp++left.flatMap ExtIncidence.block++false::lt) (ExtIncidence.stream right) (out++word left right)) := by
  obtain ⟨time,ht,trace⟩:=remaining C left right lp lt [] [] out hc
  simp only [List.nil_append,List.append_nil,List.length_nil,Nat.zero_add] at trace
  obtain ⟨r,hr,rf,_⟩:=trace.run (by simp [machine,final,RecoveryCalls.machine,RecoveryCalls.stopped])
  have more:=runFrom_moreFuel machine time (budget left right-time) _ r hr
  rw [Nat.add_sub_of_le ht] at more
  exact Step.of_run more (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)

end NearCubicWires.RepairOrdinary.CloseoutRowsRawProductRow
