import Proof.CaseAnalysis.CaseTwoShape
import Proof.PCP.PCPPNativeLiteralSplit
import Proof.PCP.PCPPNativeClauseOffsetSelect

/-! Decode the actual two-literal native query packet. The original native
reader supplies the two compact literal templates; the existing literal
splitter computes variable indices by the original 2*j+sign convention. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.LiteralFields
open LocalBitMultitape RepairRepresentation SourceInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine:=Rewind.machine PCPPNativeNodeRead.machine
def input (C left right : ℕ) : Fin 32→List Bool:=
  SourceHandoff.sourceTapes (ZeroPadding.pad C (natListWord [left,right]))
def budget (left right : ℕ):=2*PCPPNativeNodeRead.budget 2 left right+2

theorem fields_run (C left right : ℕ) : ∃ out,
    ClockJoin.ReadyRun machine (budget left right) (input C left right) out ∧
      out 20=UnaryTemplate.tape left ∧ out 30=UnaryTemplate.tape right ∧
      out 0=ZeroPadding.pad C (natListWord [left,right]):=by
  let tail:=List.replicate (C-(natListWord [left,right]).length) false
  obtain ⟨base,hb,bs,b0,_,bt,_⟩:=PCPPNativeNodeRead.cold_run [] tail 2 left right
  have hw:PCPPNativeNodeRead.source [] tail 2 left right=ZeroPadding.pad C (natListWord [left,right]):=by
    simp [PCPPNativeNodeRead.source,tail,ZeroPadding.pad,natListWord,List.append_assoc]
  rw [hw] at hb b0
  have hi:PCPPNativeNodeRead.entry (ZeroPadding.pad C (natListWord [left,right])) 0=
      initialConfiguration PCPPNativeNodeRead.machine
        (SourceHandoff.sourceTapes (t:=31) (ZeroPadding.pad C (natListWord [left,right]))):=by
    apply configuration_ext
    · rfl
    · funext i
      change (if i=0 then 0 else 0)=0
      split_ifs <;>rfl
    · funext i
      change (if i=0 then ZeroPadding.pad C (natListWord [left,right]) else [])=
        (if i.val=0 then ZeroPadding.pad C (natListWord [left,right]) else [])
      by_cases hz : i=0
      · subst i;rfl
      · have hv : i.val≠0:=fun he=>hz (Fin.ext he)
        simp only [hz,hv,if_false]
  simp only [List.length_nil] at hb
  rw [hi] at hb
  obtain ⟨r,hr,rt,rh,rs,_⟩:=Rewind.reset_run PCPPNativeNodeRead.machine _ _ base hb
  have hin:Fin.addCases (m:=31) (n:=1) (motive:=fun _=>List Bool)
      (SourceHandoff.sourceTapes (ZeroPadding.pad C (natListWord [left,right]))) (fun _=>[])=input C left right:=
    PCPPRequestSource.single_input_from (by decide) _ _ rfl
  rw [hin] at hr
  have ready:ClockJoin.ReadyRun machine (2*base.steps+2) (input C left right) r.final.tapes:=
    ⟨r,hr,rfl,rh,rs.le⟩
  refine ⟨_,ClockJoin.enlarge _ _ _ _ _ ready (by unfold budget;omega),?_,?_,?_⟩
  · exact (rt 20).trans (bt 1)
  · exact (rt 30).trans (bt 2)
  · exact (rt 0).trans b0

def split:=Rewind.machine PCPPNativeLiteralSplit.raw
def splitInput (index : ℕ) (negative : Bool) : Fin 4→List Bool:=
  ![UnaryTemplate.tape (2*index+negative.toNat),[],[],[]]
def splitBudget (index : ℕ) (negative : Bool):=2*(2*index+negative.toNat+2)+2
theorem split_run (index : ℕ) (negative : Bool) : ∃ out,
    ClockJoin.ReadyRun split (splitBudget index negative) (splitInput index negative) out ∧
      out 1=List.replicate index true:=by
  obtain ⟨base,hb,bf,bs⟩:=PCPPNativeLiteralSplit.raw_run index negative
  obtain ⟨r,hr,rt,rh,rs,_⟩:=Rewind.reset_run PCPPNativeLiteralSplit.raw _ _ base hb
  have hi:Fin.addCases (m:=3) (n:=1) (motive:=fun _=>List Bool)
      ![UnaryTemplate.tape (2*index+negative.toNat),[],[]] (fun _=>[])=splitInput index negative:=by
    funext i;fin_cases i <;>rfl
  rw [hi,bs] at hr
  rw [bs] at rs
  exact ⟨_,⟨r,hr,rfl,rh,rs.le⟩,(rt 1).trans (by rw [bf];rfl)⟩

def index {n : ℕ} (l : Literal n):=match l with | .positive j=>j.val | .negative j=>j.val
def negative {n : ℕ} (l : Literal n):=match l with | .positive _=>false | .negative _=>true
theorem code {n : ℕ} (l : Literal n) : literalIndex l=2*index l+(negative l).toNat:=by
  cases l <;>rfl
theorem literal_run {n : ℕ} (l : Literal n) : ∃ out,
    ClockJoin.ReadyRun split (splitBudget (index l) (negative l))
      ![UnaryTemplate.tape (literalIndex l),[],[],[]] out ∧ out 1=List.replicate (index l) true:=by
  rw [code]
  exact split_run (index l) (negative l)

end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.LiteralFields
