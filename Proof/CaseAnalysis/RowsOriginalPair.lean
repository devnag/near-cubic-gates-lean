import Proof.CaseAnalysis.RowsOriginalLiteral
import Proof.PCP.PCPPQueryClauseReusable

/-! The actual clause result is a native two-element list. Its fixed header
is skipped by paid moves, then both signed fields feed the original decoder. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsOriginalPair
open LocalBitMultitape ExtDecompositionBatch RecoveryRootRound RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def heads (pos : ℕ) (i : Fin 25) := if i=0 then pos else 0
def data (source : List Bool) (i : Fin 25) := if i=0 then source else []
def dirs (i : Fin 25) : HeadMove := if i=0 then .right else .stay
def move := DecompositionCountPosition.move dirs
def skip := Composition.machine (Composition.machine (Composition.machine (Composition.machine move move) move) move) move
noncomputable def first := TapeEmbedding.machine 12 CloseoutRowsOriginalLiteral.machine
def slots (i : Fin 13) : Fin 25 := if i=0 then 0 else ⟨i.val+12,by omega⟩
theorem injective : Function.Injective slots := by
  intro i j h
  have hv:=congrArg Fin.val h
  simp only [slots] at hv
  split_ifs at hv <;> apply Fin.ext <;> simp_all only [Fin.ext_iff] <;> omega
noncomputable def last := RecoveryFocus.machine slots CloseoutRowsOriginalLiteral.machine
noncomputable def machine := Composition.machine (Composition.machine skip first) last
def word (a b : ℕ) (sa sb : Bool) := natListWord [2*a+sa.toNat,2*b+sb.toNat]
def budget (a b : ℕ) (sa sb : Bool) :=
  CloseoutRowsOriginalLiteral.budget a sa+CloseoutRowsOriginalLiteral.budget b sb+11

theorem move_run (source : List Bool) (pos : ℕ) : Step move 1 (heads pos) (data source) (heads (pos+1)) (data source) := by
  obtain ⟨r,hr,rf,_⟩:=DecompositionCountPosition.move_run dirs (heads pos) (data source)
  apply Step.of_run hr _ (congrArg Configuration.tapes rf)
  rw [rf]
  funext i;fin_cases i <;> rfl

theorem skip_run (source : List Bool) : Step skip 9 (heads 0) (data source) (heads 5) (data source) :=
  ((((move_run source 0).seq (move_run source 1)).seq (move_run source 2)).seq (move_run source 3)).seq (move_run source 4)

theorem raw_run (a b : ℕ) (sa sb : Bool) :
    ∃ r,runFrom machine (budget a b sa sb) ⟨machine.start,heads 0,data (word a b sa sb)⟩=some r ∧
      r.final.tapes 0=word a b sa sb ∧ r.final.heads 0=(word a b sa sb).length ∧
      r.final.tapes 11=List.replicate a true ∧ r.final.tapes 12=[sa] ∧
      r.final.tapes 23=List.replicate b true ∧ r.final.tapes 24=[sb] ∧
      r.steps ≤ budget a b sa sb := by
  let left:=natWord (2*a+sa.toNat)
  let right:=natWord (2*b+sb.toNat)
  have wn : word a b sa sb=natWord 2++left++right := by simp [word,natListWord,left,right,List.append_assoc]
  have hlen : (natWord 2).length=5 := by decide
  obtain ⟨l,hl,lt0,lh0,lt11,lt12,_⟩:=CloseoutRowsOriginalLiteral.raw_run a sa (natWord 2) right
  have leftStep:=(Step.of_run hl rfl rfl).embed (fun _ : Fin 12=>0) (fun _ : Fin 12=>[])
  have leH : Fin.addCases (m:=13) (n:=12) (motive:=fun _=>ℕ)
      (CloseoutRowsOriginalLiteral.heads (natWord 2).length) (fun _=>0)=heads 5 := by
    rw [hlen];funext i;fin_cases i <;> rfl
  have leA : Fin.addCases (m:=13) (n:=12) (motive:=fun _=>List Bool)
      (CloseoutRowsOriginalLiteral.data (natWord 2++left++right)) (fun _=>[])=data (word a b sa sb) := by
    rw [wn];funext i;fin_cases i <;> rfl
  have initial:=(skip_run (word a b sa sb)).seq (leftStep.congr_in leH leA)
  let H : Fin 25 → ℕ:=Fin.addCases (m:=13) (n:=12) (motive:=fun _=>ℕ) l.final.heads (fun _=>0)
  let A : Fin 25 → List Bool:=Fin.addCases (m:=13) (n:=12) (motive:=fun _=>List Bool) l.final.tapes (fun _=>[])
  obtain ⟨q,hq,qt0,qh0,qt11,qt12,_⟩:=CloseoutRowsOriginalLiteral.raw_run b sb (natWord 2++left) []
  have hH : ∀ j,H (slots j)=CloseoutRowsOriginalLiteral.heads (natWord 2++left).length j := by
    intro j;fin_cases j
    · change l.final.heads 0=_
      rw [lh0,List.length_append]
      simp [CloseoutRowsOriginalLiteral.heads,left,WilliamsInputHeader.natWord_eq,two_mul,Nat.add_assoc]
    all_goals rfl
  have hA : ∀ j,A (slots j)=CloseoutRowsOriginalLiteral.data ((natWord 2++left)++natWord (2*b+sb.toNat)++[]) j := by
    intro j;fin_cases j
    · change l.final.tapes 0=_
      simpa [CloseoutRowsOriginalLiteral.data,left,right] using lt0
    all_goals rfl
  have lastStep:=(Step.of_run hq rfl rfl).dock slots injective H A hH hA
  have all:=initial.seq lastStep
  have time : 9+1+CloseoutRowsOriginalLiteral.budget a sa+1+CloseoutRowsOriginalLiteral.budget b sb=budget a b sa sb := by
    unfold budget;omega
  rw [time] at all
  obtain ⟨r,hr,rh,rt,rs⟩:=all
  have port (i : Fin 13) : r.final.tapes (slots i)=q.final.tapes i := by rw [rt,install_slot _ injective]
  refine ⟨r,hr,?_,?_,?_,?_,port 11 |>.trans qt11,port 12 |>.trans qt12,rs⟩
  · simpa [slots,word,natListWord,left,right,List.append_assoc] using (port 0).trans qt0
  · have h : r.final.heads (slots 0)=q.final.heads 0 := by rw [rh,dockH_slot _ injective]
    rw [qh0] at h
    simp [slots,word,natListWord,left,WilliamsInputHeader.natWord_eq] at h ⊢
    omega
  · rw [rt,install_other _ _ _ 11 (by intro j;fin_cases j <;> decide)]
    exact lt11
  · rw [rt,install_other _ _ _ 12 (by intro j;fin_cases j <;> decide)]
    exact lt12

end NearCubicWires.RepairOrdinary.CloseoutRowsOriginalPair
