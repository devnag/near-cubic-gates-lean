import Proof.CaseAnalysis.WitnessMass
import Proof.CaseAnalysis.WitnessTermMass
import Proof.Hierarchy.CompetitorFieldEmit
import Proof.MachineModel.OrdinarySourceSATLiftRequestMoves

/-! Retain one checked coefficient before clearing its parser. The record
uses one sign bit and the same two guarded b-bit fields. Only the logical
output cursor advances; neither allocated padding nor old prefixes are scanned. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.CoefficientRecord
open LocalBitMultitape RecoveryRootRound RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def heads (out : List Bool) : Fin 5→ℕ:=![0,0,0,out.length,0]
def tapes (P : ℕ) (source nb db out : List Bool) : Fin 5→List Bool:=
  ![source,ZeroPadding.pad P (frame nb),ZeroPadding.pad P (frame db),out,List.replicate P false]
def Run {s : ℕ} (p : Machine 5 s) (cost P : ℕ) (source nb db out after : List Bool) : Prop:=
  ∃ r,runFrom p cost ⟨p.start,heads out,tapes P source nb db out⟩=some r ∧
    r.steps=cost ∧ r.final.heads=heads after ∧ r.final.tapes=tapes P source nb db after

theorem join {a b : ℕ} (p : Machine 5 a) (q : Machine 5 b) (fp fq P : ℕ)
    (source nb db out middle after : List Bool)
    (hp : Run p fp P source nb db out middle) (hq : Run q fq P source nb db middle after) :
    Run (Composition.machine p q) (fp+1+fq) P source nb db out after:=by
  obtain ⟨r,hr,rs,rh,rt⟩:=hp
  obtain ⟨s,hs,ss,sh,st⟩:=hq
  have he:Composition.restart r.final q.start=⟨q.start,heads middle,tapes P source nb db middle⟩:=
    configuration_ext rfl rh rt
  have hsq:runFrom q fq (Composition.restart r.final q.start)=some s:=by rw [he];exact hs
  exact ⟨Composition.joinedReceipt r s,Composition.run_join p q fp fq _ r s hr hsq,
    by change r.steps+1+s.steps=fp+1+fq;rw [rs,ss],sh,st⟩

noncomputable def literal (bits : List Bool):=
  RecoveryFocus.machine (fun _ : Fin 1=>(3 : Fin 5)) (HierarchyFixedWord.raw bits)
noncomputable def sign:=TapeEmbedding.machine 1 CloseoutRowsSignedAppend.sign
noncomputable def field (i : Fin 2):=CompetitorFieldEmit.program (if i.val=0 then 1 else 2) (3 : Fin 5) 4
def word (i : Fin 2) (nb db : List Bool):=if i.val=0 then nb else db
noncomputable def first:=Composition.machine (literal [true]) sign
noncomputable def signed:=Composition.machine first (literal [false])
noncomputable def numerator:=Composition.machine signed (field 0)
noncomputable def machine:=Composition.machine numerator (field 1)
def produced (source nb db : List Bool):=frame [readTapeBit source 1]++frame nb++frame db
def budget (nb db : List Bool):=4*nb.length+4*db.length+14

theorem literal_run (bits : List Bool) (P : ℕ) (source nb db out : List Bool) :
    Run (literal bits) bits.length P source nb db out (out++bits):=by
  obtain ⟨r,hr,rs,rh,rt,keep⟩:=RepairSource.OrdinarySourceSATLift.RequestMoves.print_run
    (3 : Fin 5) bits out (heads out) (tapes P source nb db out) rfl rfl
  refine ⟨r,hr,rs,?_,?_⟩
  · funext i;fin_cases i
    · exact (keep 0 (by decide)).1
    · exact (keep 1 (by decide)).1
    · exact (keep 2 (by decide)).1
    · exact rh
    · exact (keep 4 (by decide)).1
  · funext i;fin_cases i
    · exact (keep 0 (by decide)).2
    · exact (keep 1 (by decide)).2
    · exact (keep 2 (by decide)).2
    · exact rt
    · exact (keep 4 (by decide)).2

theorem sign_run (P : ℕ) (source nb db out : List Bool) :
    Run sign 2 P source nb db out (out++[readTapeBit source 1]):=by
  obtain ⟨r,hr,rf,rs⟩:=CloseoutRowsSignedAppend.sign_run source
    (ZeroPadding.pad P (frame nb)) (ZeroPadding.pad P (frame db)) out
  have he:=TapeEmbedding.run_embed CloseoutRowsSignedAppend.sign (fun _ : Fin 1=>0)
    (fun _=>List.replicate P false) _ _ r hr
  refine ⟨TapeEmbedding.receipt (fun _ : Fin 1=>0) (fun _=>List.replicate P false) r,?_,rs,?_,?_⟩
  · have hc:(⟨sign.start,heads out,tapes P source nb db out⟩ : Configuration 5 3)=
        TapeEmbedding.config (fun _ : Fin 1=>0) (fun _=>List.replicate P false)
          (CloseoutRowsSignedAppend.signInput source (ZeroPadding.pad P (frame nb))
            (ZeroPadding.pad P (frame db)) out):=by
      apply configuration_ext
      · rfl
      · funext i;fin_cases i <;> rfl
      · funext i;fin_cases i <;> rfl
    rw [hc]
    exact he
  · change (TapeEmbedding.config (fun _ : Fin 1=>0) (fun _=>List.replicate P false) r.final).heads=_
    rw [rf]
    funext i;fin_cases i <;> rfl
  · change (TapeEmbedding.config (fun _ : Fin 1=>0) (fun _=>List.replicate P false) r.final).tapes=_
    rw [rf]
    funext i;fin_cases i <;> rfl

theorem field_run (i : Fin 2) (P : ℕ) (source nb db out : List Bool)
    (hcap : 2*(word i nb db).length+1 ≤ P) :
    Run (field i) (4*(word i nb db).length+3) P source nb db out (out++frame (word i nb db)):=by
  obtain ⟨r,hr,rh,rt,rs⟩:=CompetitorFieldEmit.field_run
    (if i.val=0 then 1 else 2) (3 : Fin 5) 4
    (by fin_cases i <;> decide) (by fin_cases i <;> decide) (by decide)
    (word i nb db) out P (heads out) (tapes P source nb db out)
    (by fin_cases i <;> rfl) rfl rfl (by fin_cases i <;> rfl) rfl rfl hcap
  refine ⟨r,hr,rs,?_,?_⟩
  · rw [rh]
    funext j;fin_cases j <;> rfl
  · rw [rt]
    funext j;fin_cases j <;> rfl

theorem record_run (P : ℕ) (source nb db out : List Bool)
    (hn : 2*nb.length+1 ≤ P) (hd : 2*db.length+1 ≤ P) :
    Run machine (budget nb db) P source nb db out (out++produced source nb db):=by
  have a:=join (literal [true]) sign 1 2 P source nb db out (out++[true])
    ((out++[true])++[readTapeBit source 1])
    (literal_run [true] P source nb db out) (sign_run P source nb db (out++[true]))
  have b:=join first (literal [false]) (1+1+2) 1 P source nb db out
    ((out++[true])++[readTapeBit source 1])
    (((out++[true])++[readTapeBit source 1])++[false]) a
    (literal_run [false] P source nb db ((out++[true])++[readTapeBit source 1]))
  have c:=join signed (field 0) ((1+1+2)+1+1) (4*nb.length+3) P source nb db out
    (((out++[true])++[readTapeBit source 1])++[false])
    ((((out++[true])++[readTapeBit source 1])++[false])++frame nb) b
    (field_run 0 P source nb db (((out++[true])++[readTapeBit source 1])++[false]) hn)
  have d:=join numerator (field 1) (((1+1+2)+1+1)+1+(4*nb.length+3)) (4*db.length+3) P source nb db out
    ((((out++[true])++[readTapeBit source 1])++[false])++frame nb)
    (((((out++[true])++[readTapeBit source 1])++[false])++frame nb)++frame db) c
    (field_run 1 P source nb db ((((out++[true])++[readTapeBit source 1])++[false])++frame nb) hd)
  have ht:((((1+1+2)+1+1)+1+(4*nb.length+3))+1+(4*db.length+3))=budget nb db:=by unfold budget;omega
  have ho:(((((out++[true])++[readTapeBit source 1])++[false])++frame nb)++frame db)=
      out++produced source nb db:=by simp [produced,frame,RepairOrdinary.frame,List.append_assoc]
  rw [ht,ho] at d
  exact d

theorem sign_meaning (P : ℕ) (bits : List Bool) (q : ℚ)
    (hd : CanonicalWitnessCodec.decodeCanonicalRational (value bits)=some q) :
    readTapeBit (ZeroPadding.pad P (frame (RecoveryFixedUnpair.leftWord (RationalCold.numeratorWord bits)))) 1=
      decide (q.num<0):=by
  rw [ZeroPadding.read_pad]
  exact CloseoutRowsSignedAppend.sign_of_decode (RationalCold.numeratorWord bits) q.num
    (RationalCold.decoded_words bits q hd).2.1
theorem produced_length (source : List Bool) (b n d : ℕ) :
    (produced source (SignedSortKey.binary b n) (SignedSortKey.binary b d)).length=4*b+5:=by
  simp only [produced,List.length_append,frame_length,List.length_singleton,SignedSortKey.binary_length]
  omega

end NearCubicWires.RepairOrdinary.CloseoutWitness.CoefficientRecord
