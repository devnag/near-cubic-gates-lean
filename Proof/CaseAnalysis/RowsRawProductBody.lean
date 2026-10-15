import Proof.CaseAnalysis.RowsRawMonomialSkip

/-! One original left monomial emits its complete product row, returns
the right stream by the existing paid rewind, and advances the left stream.
Both rewind logs are retained for the next actual left monomial. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsRawProductBody
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def heads (pos : ℕ) (out : List Bool) : Fin 5→ℕ:=![pos,0,out.length,0,0]
def data (C : ℕ) (left right out : List Bool) : Fin 5→List Bool:=
  ![left,right,out,List.replicate C false,List.replicate C false]
def advance : Machine 5 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>decide (q=1)
  rule:=fun q _=>if q=0 then some ⟨1,fun _=>none,![.right,.stay,.stay,.stay,.stay]⟩ else none
noncomputable def row:=MaskedReset.machine CloseoutRowsRawProductRow.machine (fun i=>decide (i=1))
def skipSlots : Fin 1→Fin 5:=fun _=>0
noncomputable def skip:=RecoveryFocus.machine skipSlots CloseoutRowsRawMonomialSkip.machine
noncomputable def machine:=Composition.machine (Composition.machine advance row) skip
def budget (left : List ℕ) (right : List (List ℕ)):=
  2*CloseoutRowsRawProductRow.budget left right+(left.flatMap ExtIncidence.block).length+6

theorem advance_run (C pos : ℕ) (left right out : List Bool) :
    Step advance 1 (heads pos out) (data C left right out) (heads (pos+1) out) (data C left right out) := by
  have hs:step advance ⟨0,heads pos out,data C left right out⟩=
      some ⟨1,heads (pos+1) out,data C left right out⟩:=by
    simp only [step,advance,↓reduceIte,Option.map_some]
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;> rfl
    · rfl
  obtain ⟨r,hr,rf,_⟩:=(Timed.single (by rfl) hs).run (by rfl)
  exact Step.of_run hr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)

theorem row_run (C : ℕ) (left : List ℕ) (right : List (List ℕ)) (pre tail out : List Bool)
    (hl : (left.flatMap ExtIncidence.block).length+1≤C)
    (hc : CloseoutRowsRawProductRow.budget left right≤C) :
    Step row (2*CloseoutRowsRawProductRow.budget left right+2) (heads pre.length out)
      (data C (pre++left.flatMap ExtIncidence.block++false::tail) (ExtIncidence.stream right) out)
      (heads pre.length (out++CloseoutRowsRawProductRow.word left right))
      (data C (pre++left.flatMap ExtIncidence.block++false::tail) (ExtIncidence.stream right)
        (out++CloseoutRowsRawProductRow.word left right)) := by
  have raw:=CloseoutRowsRawProductRow.row_run C left right pre tail out hl
  have reset:=raw.mask (cap:=C) (fun i=>decide (i=1)) (by
    intro i hi
    have he:i=1:=of_decide_eq_true hi
    subst i;rfl) hc
  apply (reset.congr_in ?_ ?_).congr ?_ ?_
  all_goals funext i;fin_cases i <;> rfl

theorem skip_run (C : ℕ) (left : List ℕ) (right pre tail out : List Bool) :
    Step skip ((left.flatMap ExtIncidence.block).length+1) (heads pre.length out)
      (data C (pre++left.flatMap ExtIncidence.block++false::tail) right out)
      (heads (pre.length+(left.flatMap ExtIncidence.block).length+1) out)
      (data C (pre++left.flatMap ExtIncidence.block++false::tail) right out) := by
  obtain ⟨raw,hr,rh,rt,_⟩:=CloseoutRowsRawMonomialSkip.skip_run left pre tail
  obtain ⟨r,rr,_rc,_rs,h,t,keep⟩:=RecoveryFocus.dock skipSlots (by decide)
    CloseoutRowsRawMonomialSkip.machine _ (heads pre.length out)
    (data C (pre++left.flatMap ExtIncidence.block++false::tail) right out) _
    (by intro i;fin_cases i;rfl) (by intro i;fin_cases i;rfl) raw hr
  have hh:r.final.heads=heads (pre.length+(left.flatMap ExtIncidence.block).length+1) out:=by
    funext i
    by_cases hi:i=0
    · subst i;exact (h 0).trans (congrArg (fun H=>H 0) rh)
    · have kept:=keep i (by intro j;exact Ne.symm hi)
      rw [kept.1]
      fin_cases i <;> simp_all [heads]
  have ht:r.final.tapes=data C (pre++left.flatMap ExtIncidence.block++false::tail) right out:=by
    funext i
    by_cases hi:i=0
    · subst i;exact (t 0).trans (congrArg (fun A=>A 0) rt)
    · exact (keep i (by intro j;exact Ne.symm hi)).2
  exact Step.of_run rr hh ht

theorem body_run (C : ℕ) (left : List ℕ) (right : List (List ℕ)) (pre tail out : List Bool)
    (hl : (left.flatMap ExtIncidence.block).length+1≤C)
    (hc : CloseoutRowsRawProductRow.budget left right≤C) :
    Step machine (budget left right) (heads pre.length out)
      (data C (pre++ExtIncidence.monomialWord left++tail) (ExtIncidence.stream right) out)
      (heads (pre.length+(ExtIncidence.monomialWord left).length)
        (out++CloseoutRowsRawProductRow.word left right))
      (data C (pre++ExtIncidence.monomialWord left++tail) (ExtIncidence.stream right)
        (out++CloseoutRowsRawProductRow.word left right)) := by
  have first:=advance_run C pre.length (pre++ExtIncidence.monomialWord left++tail)
    (ExtIncidence.stream right) out
  have second:=row_run C left right (pre++[true]) tail out hl hc
  have third:=skip_run C left (ExtIncidence.stream right) (pre++[true]) tail
    (out++CloseoutRowsRawProductRow.word left right)
  have source:(pre++[true])++left.flatMap ExtIncidence.block++false::tail=
      pre++ExtIncidence.monomialWord left++tail:=by
    simp [ExtIncidence.monomialWord,List.append_assoc]
  rw [source] at second third
  simp only [List.length_append,List.length_singleton] at second third
  have joined:=(first.seq second).seq third
  have time:1+1+(2*CloseoutRowsRawProductRow.budget left right+2)+1+
      ((left.flatMap ExtIncidence.block).length+1)=budget left right:=by unfold budget;omega
  rw [time] at joined
  apply joined.congr
  · funext i;fin_cases i
    · change pre.length+1+(left.flatMap ExtIncidence.block).length+1=
        pre.length+(ExtIncidence.monomialWord left).length
      rw [ExtIncidence.monomialWord_length];omega
    all_goals rfl
  · rfl

end NearCubicWires.RepairOrdinary.CloseoutRowsRawProductBody
