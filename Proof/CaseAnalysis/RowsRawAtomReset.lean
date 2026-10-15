import Proof.CaseAnalysis.RowsRawAtomMeaning
import Proof.CaseAnalysis.RowsProjectionReset

/-! The actual native count/absolute-index writer returns only its private
heads. Source, offset, monomial count and append cursors remain live. The
paid zero backing and rewind log are explicit preprocessing inputs. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsRawAtomReset
open LocalBitMultitape RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def selected (i : Fin 14) : Bool := decide (0 < i.val ∧ i.val ≤ 10)
def caps (C : ℕ) (i : Fin 14) : ℕ := if selected i then C else 0
noncomputable def machine := MaskedReset.machine CloseoutRowsRawAtomNative.machine selected
noncomputable def input (C : ℕ) (source : List Bool) (pos offset count : ℕ) (out : List Bool) :=
  ZeroPadding.config (Rewind.Workspace.capacities 14 C)
    (Rewind.recording (ZeroPadding.config (caps C)
      (CloseoutRowsRawAtomNative.input source pos offset count out)) 0)
def budget (offset n : ℕ) := 2*CloseoutRowsRawAtomNative.budget offset n+2

theorem input_private (source : List Bool) (pos offset count : ℕ) (out : List Bool)
    (i : Fin 14) (hi : selected i=true) :
    (CloseoutRowsRawAtomNative.input source pos offset count out).heads i=0 ∧
    (CloseoutRowsRawAtomNative.input source pos offset count out).tapes i=[] := by
  fin_cases i <;> simp_all [selected]
  all_goals constructor <;> rfl

theorem reset_run (C : ℕ) (pre tail out : List Bool) (offset n count : ℕ)
    (hc : CloseoutRowsRawAtomNative.budget offset n+1≤C) :
    ∃ r,runFrom machine (budget offset n)
      (input C (pre++natWord n++tail) pre.length offset count out)=some r ∧
      r.final.tapes 0=pre++natWord n++tail ∧
      r.final.heads 0=pre.length+(natWord n).length ∧
      r.final.tapes 11=UnaryTemplate.tape (offset+n+1) ∧ r.final.heads 11=1 ∧
      r.final.tapes 12=out++ExtIncidence.stream (CloseoutRowsRawAtomLoop.indices offset n) ∧
      r.final.heads 12=(out++ExtIncidence.stream (CloseoutRowsRawAtomLoop.indices offset n)).length ∧
      r.final.tapes 13=RepairSource.VerifierDecoding.CompareMachine.word (count+n) ∧
      r.final.heads 13=count+n+1 ∧
      (∀ i : Fin 14,selected i=true → r.final.heads (i.castAdd 1)=0 ∧
        (r.final.tapes (i.castAdd 1)).length=C) ∧
      r.final.heads 14=0 ∧ r.final.tapes 14=List.replicate C false ∧
      r.steps≤budget offset n := by
  obtain ⟨raw,hr,t0,h0,_t10,_h10,t11,h11,t12,h12,t13,h13,hs⟩:=
    CloseoutRowsRawAtomNative.native_run pre tail out offset n count
  obtain ⟨padded,hp,pf,ps,_⟩:=ZeroPadding.run_config CloseoutRowsRawAtomNative.machine
    (caps C) _ _ raw hr
  obtain ⟨r,rr,rf,rs,_⟩:=MaskedReset.workspace_run CloseoutRowsRawAtomNative.machine selected
    _ C _ padded hp (by
      intro i hi
      exact (input_private (pre++natWord n++tail) pre.length offset count out i hi).1) (by omega)
  have hb:2*padded.steps+2≤budget offset n:=by unfold budget; omega
  have run:=runFrom_moreFuel machine _ (budget offset n-(2*padded.steps+2)) _ r rr
  rw [Nat.add_sub_of_le hb] at run
  have rh (i : Fin 14) : r.final.heads (i.castAdd 1)=
      if selected i then 0 else raw.final.heads i := by
    rw [rf,pf]
    simp only [SelectiveReset.finished,Rewind.config,ZeroPadding.config,Fin.addCases_left]
  have rt (i : Fin 14) : r.final.tapes (i.castAdd 1)=
      ZeroPadding.pad (caps C i) (raw.final.tapes i) := by
    rw [rf,pf]
    simp only [SelectiveReset.finished,Rewind.config,ZeroPadding.config,Fin.addCases_left]
  have retained (i : Fin 14) (hi : selected i=false) :
      r.final.heads (i.castAdd 1)=raw.final.heads i ∧
      r.final.tapes (i.castAdd 1)=raw.final.tapes i := by
    rw [rh,rt]
    simp only [caps,hi,Bool.false_eq_true,↓reduceIte,ZeroPadding.pad_zero]
    trivial
  have p0:=retained 0 rfl
  have p11:=retained 11 rfl
  have p12:=retained 12 rfl
  have p13:=retained 13 rfl
  refine ⟨r,run,p0.2.trans t0,p0.1.trans h0,p11.2.trans t11,p11.1.trans h11,
    p12.2.trans t12,p12.1.trans h12,p13.2.trans t13,p13.1.trans h13,?_,?_,?_,by omega⟩
  · intro i hi
    have init:=input_private (pre++natWord n++tail) pre.length offset count out i hi
    have supp:=CloseoutRowsProjectionReset.scratch_support CloseoutRowsRawAtomNative.machine
      _ C _ raw hr i init.1 (by rw [init.2]; simp) (by omega)
    rw [rh,rt]
    simp only [hi,↓reduceIte,caps,ZeroPadding.pad_length,max_eq_left supp]
    trivial
  · rw [rf];rfl
  · rw [rf];rfl

end NearCubicWires.RepairOrdinary.CloseoutRowsRawAtomReset
