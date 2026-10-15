import Proof.CaseAnalysis.RowsRawAtomReuse

/-! The actual sequence of native source counts drives the complete atom
batch. Each zero count is still read; no separate occurrence or monomial
driver is assumed, and all private returns/erases are paid per occurrence. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsRawAtomBatch
open LocalBitMultitape RepairRepresentation RecoveryExecution RecoveryRootRound
open CloseoutRowsRawAtomReuse
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def idle : Machine 17 1 where
  descriptionBits:=0
  start:=0
  halted:=fun _=>true
  rule:=fun _ _=>none
noncomputable def sizes : Fin 2→ℕ:=![1,
  8+(8+Fintype.card (RecoveryCalls.Control MatrixUnary.sizes))+
    Fintype.card (RecoveryCalls.Control CloseoutRowsRawAtomLoop.sizes)+2+4]
noncomputable def programs : (i : Fin 2)→Machine 17 (sizes i)
  | ⟨0,_⟩=>idle
  | ⟨1,_⟩=>CloseoutRowsRawAtomReuse.machine
  | ⟨n+2,h⟩=>False.elim (by omega)
def next (i : Fin 2) (_ : Fin (sizes i)) (bits : Fin 17→Bool) : Option (Fin 2):=
  if i=0 then if bits 0 then some 1 else none else some 0
noncomputable def machine:=RecoveryCalls.machine sizes programs 0 next
noncomputable def entry (i : Fin 2) (C : ℕ) (source : List Bool)
    (pos offset count : ℕ) (out : List Bool):=
  controlConfig (RecoveryCalls.code sizes i)
    (⟨(programs i).start,heads pos count out,data C source offset count out⟩ : Configuration 17 (sizes i))
noncomputable def final (C : ℕ) (source : List Bool) (pos offset count : ℕ) (out : List Bool):=
  RecoveryCalls.stopped sizes (heads pos count out) (data C source offset count out)
def countWord (ns : List ℕ):=ns.flatMap natWord
def atoms : ℕ→List ℕ→List Bool
  | _,[]=>[]
  | offset,n::ns=>ExtIncidence.stream (CloseoutRowsRawAtomLoop.indices offset n)++atoms (offset+n) ns
def budget (C n : ℕ):=n*(4*C+7)+1

theorem probe (C : ℕ) (pre tail out : List Bool) (offset n count : ℕ) :
    Timed machine 1 (entry 0 C (pre++natWord n++tail) pre.length offset count out)
      (entry 1 C (pre++natWord n++tail) pre.length offset count out) := by
  have hread:readTapeBit (pre++natWord n++tail) pre.length=true:=by
    rw [WilliamsInputHeader.natWord_eq]
    simp only [natBitLength,List.replicate_succ,List.cons_append,List.append_assoc]
    simp [Streaming.read_append]
  have hn:next 0 (programs 0).start
      (⟨(programs 0).start,heads pre.length count out,
        data C (pre++natWord n++tail) offset count out⟩ : Configuration 17 (sizes 0)).scanned=some 1:=by
    simp only [next,Configuration.scanned,heads,data,↓reduceIte,hread]
  exact Timed.single (by simp [machine,entry,RecoveryCalls.machine,controlConfig,RecoveryCalls.code])
    (RecoveryCalls.return_step sizes programs 0 next 0 1 _ (by rfl) hn)

theorem round (C : ℕ) (pre tail out : List Bool) (offset n count : ℕ)
    (hc : CloseoutRowsRawAtomNative.budget offset n+1≤C) :
    ∃ time≤4*C+6,Timed machine time
      (entry 1 C (pre++natWord n++tail) pre.length offset count out)
      (entry 0 C (pre++natWord n++tail) (pre.length+(natWord n).length)
        (offset+n) (count+n) (out++ExtIncidence.stream (CloseoutRowsRawAtomLoop.indices offset n))) := by
  obtain ⟨r,hr,rh,rt,_⟩:=reuse_run C pre tail out offset n count hc
  rw [entry_fields] at hr
  obtain ⟨time,ht,trace⟩:=call_receipt sizes programs 0 next 1 0 _ _ r hr (by rfl)
  have same:RecoveryCalls.restarted (programs 0) r.final.heads r.final.tapes=
      ⟨(programs 0).start,heads (pre.length+(natWord n).length) (count+n)
        (out++ExtIncidence.stream (CloseoutRowsRawAtomLoop.indices offset n)),
        data C (pre++natWord n++tail) (offset+n) (count+n)
          (out++ExtIncidence.stream (CloseoutRowsRawAtomLoop.indices offset n))⟩:=by
    apply configuration_ext
    · rfl
    · exact rh
    · exact rt
  rw [same] at trace
  refine ⟨time,?_,trace⟩
  unfold CloseoutRowsRawAtomReuse.budget CloseoutRowsRawAtomReset.budget at ht
  omega

theorem stop (C : ℕ) (pre out : List Bool) (offset count : ℕ) :
    Timed machine 1 (entry 0 C pre pre.length offset count out)
      (final C pre pre.length offset count out) := by
  have hread:readTapeBit pre pre.length=false:=by simp [readTapeBit,List.getD]
  have hn:next 0 (programs 0).start
      (⟨(programs 0).start,heads pre.length count out,data C pre offset count out⟩ :
        Configuration 17 (sizes 0)).scanned=none:=by
    simp only [next,Configuration.scanned,heads,data,↓reduceIte,hread,Bool.false_eq_true]
  exact Timed.single (by simp [machine,entry,RecoveryCalls.machine,controlConfig,RecoveryCalls.code])
    (RecoveryCalls.stop_step sizes programs 0 next 0 _ (by rfl) hn)

theorem remaining (C B : ℕ) (ns : List ℕ) (offset count : ℕ) (pre out : List Bool)
    (hB : offset+ns.sum≤B) (hc : 64*(B+2)^2≤C) :
    ∃ time≤budget C ns.length,Timed machine time
      (entry 0 C (pre++countWord ns) pre.length offset count out)
      (final C (pre++countWord ns) (pre++countWord ns).length
        (offset+ns.sum) (count+ns.sum) (out++atoms offset ns)) := by
  induction ns generalizing offset count pre out with
  | nil=>
    exact ⟨1,by simp [budget],by simpa [countWord,atoms] using stop C pre out offset count⟩
  | cons n ns ih=>
    have hn:offset+n≤B:=by simp only [List.sum_cons] at hB;omega
    have cap:CloseoutRowsRawAtomNative.budget offset n+1≤C:=
      (CloseoutRowsRawAtomBounds.native_bound offset n B hn).trans hc
    obtain ⟨first,hfirst,tr⟩:=round C pre (countWord ns) out offset n count cap
    obtain ⟨rest,hrest,tail⟩:=ih (offset+n) (count+n) (pre++natWord n)
      (out++ExtIncidence.stream (CloseoutRowsRawAtomLoop.indices offset n)) (by
        simpa only [List.sum_cons,Nat.add_assoc] using hB)
    have full:pre++countWord (n::ns)=pre++natWord n++countWord ns:=by
      simp only [countWord,List.flatMap_cons,List.append_assoc]
    simp only [List.length_append] at tail
    have all:=(probe C pre (countWord ns) out offset n count).trans (tr.trans tail)
    refine ⟨1+(first+rest),?_,?_⟩
    · unfold budget at *
      simp only [List.length_cons]
      nlinarith
    · simpa only [full,atoms,List.length_append,List.sum_cons,List.append_assoc,Nat.add_assoc] using all

theorem batch_run (C B : ℕ) (ns : List ℕ) (out : List Bool)
    (hB : ns.sum≤B) (hc : 64*(B+2)^2≤C) :
    ∃ r,runFrom machine (budget C ns.length) (entry 0 C (countWord ns) 0 0 0 out)=some r ∧
      r.final=final C (countWord ns) (countWord ns).length ns.sum ns.sum (out++atoms 0 ns) ∧
      r.steps≤budget C ns.length := by
  obtain ⟨time,ht,trace⟩:=remaining C B ns 0 0 [] out (by simpa using hB) hc
  simp only [List.nil_append,List.length_nil,Nat.zero_add] at trace
  obtain ⟨r,hr,rf,rs⟩:=trace.run (by simp [machine,final,RecoveryCalls.machine,RecoveryCalls.stopped])
  have more:=runFrom_moreFuel machine time (budget C ns.length-time) _ r hr
  rw [Nat.add_sub_of_le ht] at more
  exact ⟨r,more,rf,rs.le.trans ht⟩

end NearCubicWires.RepairOrdinary.CloseoutRowsRawAtomBatch
