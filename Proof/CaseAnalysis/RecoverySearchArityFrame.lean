import Proof.CaseAnalysis.RecoveryGraphRun
import Proof.Amplification.RecoveryPCPFormulaResumeSearchCountFrame

/-! Frame the retained actual description arity using the existing unary
template printer and count framer. All three scratch tapes start empty. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedSearchArityFrame
open LocalBitMultitape RecoveryRootRound
open RepairSource.ProjectionNormalization RepairSource.VerifierDecoding
open RepairSource.RecoveryPCPFormulaResumeSearchCount
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

private theorem padded_ready {t s fuel : ℕ} {p : Machine t s}
    {input output : Fin t→List Bool} (h : ClockJoin.ReadyRun p fuel input output) (caps : Fin t→ℕ) :
    ClockJoin.ReadyRun p fuel (fun i=>ZeroPadding.pad (caps i) (input i))
      (fun i=>ZeroPadding.pad (caps i) (output i)) := by
  obtain ⟨a,ar,atapes,ah,as⟩:=h
  obtain ⟨b,br,bf,bs,_⟩:=ZeroPadding.run_config p caps _ _ a ar
  refine ⟨b,br,?_,?_,bs.trans_le as⟩
  · rw [bf]
    exact congrArg (fun A i=>ZeroPadding.pad (caps i) (A i)) atapes
  · intro i
    rw [bf]
    exact ah i

theorem template_ready (n B : ℕ) :
    ClockJoin.ReadyRun (DimensionTemplate.machine false) (2*n+8)
      ![ZeroPadding.pad B (List.replicate n true),[],[]]
      ![ZeroPadding.pad B (List.replicate n true),UnaryTemplate.tape n,List.replicate (n+3) false] := by
  have h:=padded_ready (DimensionTemplate.ready false n) ![B,0,0]
  convert h using 1 <;>
    (funext i;fin_cases i <;> simp [DimensionTemplate.input,DimensionTemplate.output])

theorem framed_template (n : ℕ) :
    ClockJoin.ReadyRun frameMachine (4*n+6)
      ![UnaryTemplate.tape n,[]] ![UnaryTemplate.tape n,frame (List.replicate n true)] := by
  have h:=padded_ready (frame_ready n) ![n+2,0]
  convert h using 1 <;>
    (funext i;fin_cases i <;>
      simp [frameInput,frameOutput,UnaryTemplate.tape,CompareMachine.word,ZeroPadding.pad])

def firstSlots (i : Fin 3) : Fin 4:=i.castAdd 1
def lastSlots : Fin 2→Fin 4:=![1,3]
theorem first_injective : Function.Injective firstSlots := by
  intro i j he
  exact Fin.ext (congrArg (fun k : Fin 4=>k.val) he)
noncomputable def first:=RecoveryFocus.machine firstSlots (DimensionTemplate.machine false)
noncomputable def last:=RecoveryFocus.machine lastSlots frameMachine
noncomputable def machine:=Composition.machine first last
def input (n B : ℕ) : Fin 4→List Bool:=![ZeroPadding.pad B (List.replicate n true),[],[],[]]
def middle (n B : ℕ) : Fin 4→List Bool:=
  ![ZeroPadding.pad B (List.replicate n true),UnaryTemplate.tape n,List.replicate (n+3) false,[]]
def output (n B : ℕ) : Fin 4→List Bool:=
  ![ZeroPadding.pad B (List.replicate n true),UnaryTemplate.tape n,List.replicate (n+3) false,
    frame (List.replicate n true)]

theorem ready (n B : ℕ) : ClockJoin.ReadyRun machine (6*n+15) (input n B) (output n B) := by
  have a:=(template_ready n B).focus firstSlots first_injective (input n B) (by intro i;fin_cases i <;> rfl)
  have atapes : install firstSlots (input n B)
      ![ZeroPadding.pad B (List.replicate n true),UnaryTemplate.tape n,List.replicate (n+3) false]=middle n B := by
    apply HierarchyWidth.install_eq firstSlots first_injective
    · intro i;fin_cases i <;> rfl
    · intro i hi
      fin_cases i
      · exact False.elim (hi 0 rfl)
      · exact False.elim (hi 1 rfl)
      · exact False.elim (hi 2 rfl)
      · rfl
  rw [atapes] at a
  have b:=(framed_template n).focus lastSlots (by decide) (middle n B) (by intro i;fin_cases i <;> rfl)
  have btapes : install lastSlots (middle n B)
      ![UnaryTemplate.tape n,frame (List.replicate n true)]=output n B := by
    apply HierarchyWidth.install_eq lastSlots (by decide)
    · intro i;fin_cases i <;> rfl
    · intro i hi
      fin_cases i
      · rfl
      · exact False.elim (hi 0 rfl)
      · rfl
      · exact False.elim (hi 1 rfl)
  rw [btapes] at b
  have h:=ClockJoin.join first last (2*n+8) (4*n+6) _ _ _ a b
  have he : (2*n+8)+1+(4*n+6)=6*n+15 := by omega
  rw [he] at h
  exact h

end NearCubicWires.RepairOrdinary.RecoveryBoundedSearchArityFrame
