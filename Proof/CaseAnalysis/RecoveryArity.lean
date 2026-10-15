import Proof.MachineModel.ClockUnaryProduct
import Proof.CaseAnalysis.RecoveryScalarMetadata

/-! The retained row width and bound driver physically produce the original
description arity. The same paid backing absorbs the product's rewind log. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedColdArity
open LocalBitMultitape RecoveryRootRound RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def rawInput (d e : ℕ) : Fin 4→List Bool:=
  ![List.replicate d true,CompareMachine.word e,[],[]]
def rawOutput (d e : ℕ) : Fin 4→List Bool:=
  ![List.replicate d true,CompareMachine.word e,List.replicate (d*e) true,
    List.replicate (d*(2*e+3)+2) false]
def input (d e B : ℕ) : Fin 4→List Bool:=fun i=>ZeroPadding.pad B (rawInput d e i)
def output (d e B : ℕ) : Fin 4→List Bool:=
  ![ZeroPadding.pad B (List.replicate d true),ZeroPadding.pad B (CompareMachine.word e),
    ZeroPadding.pad B (List.replicate (d*e) true),List.replicate B false]
def budget (d e : ℕ):=2*(d*(2*e+3)+2)+2
def slots : Fin 4→Fin 158:=![138,150,144,116]
noncomputable def machine:=RecoveryFocus.machine slots ClockUnaryProduct.machine

theorem raw_ready (d e : ℕ) :
    ClockJoin.ReadyRun ClockUnaryProduct.machine (budget d e) (rawInput d e) (rawOutput d e) := by
  obtain ⟨r,hr,h0,h1,h2,h3,hh,hs⟩:=ClockUnaryProduct.product_run d e
  have hi : (Fin.addCases (m:=3) (n:=1) (motive:=fun _ : Fin (3+1)=>List Bool)
      ![List.replicate d true,false::List.replicate e true,[]] (fun _=>[]))=rawInput d e := by
    funext i;fin_cases i <;> rfl
  rw [hi] at hr
  exact ⟨r,hr,by funext i;fin_cases i;exact h0;exact h1;exact h2;exact h3,hh,hs.le⟩

theorem ready (d e B : ℕ) (hB : d*(2*e+3)+2≤B) :
    ClockJoin.ReadyRun ClockUnaryProduct.machine (budget d e) (input d e B) (output d e B) := by
  obtain ⟨a,ha,atapes,ah,as⟩:=raw_ready d e
  obtain ⟨r,hr,rf,rs,_⟩:=ZeroPadding.run_config ClockUnaryProduct.machine (fun _=>B) _ _ a ha
  change runFrom _ _ (ZeroPadding.config _ (initialConfiguration _ _))=_ at hr
  have hi : ZeroPadding.config (fun _ : Fin 4=>B)
      (initialConfiguration ClockUnaryProduct.machine (rawInput d e))=
      initialConfiguration ClockUnaryProduct.machine (input d e B) := by rfl
  rw [hi] at hr
  refine ⟨r,hr,?_,?_,rs.le.trans as⟩
  · rw [rf]
    change (fun i=>ZeroPadding.pad B (a.final.tapes i))=output d e B
    rw [atapes]
    funext i;fin_cases i
    · rfl
    · rfl
    · rfl
    · change ZeroPadding.pad B (List.replicate (d*(2*e+3)+2) false)=List.replicate B false
      simp only [ZeroPadding.pad,List.length_replicate,←List.replicate_add,Nat.add_sub_of_le hB]
  · intro i
    rw [rf]
    exact ah i

theorem arity_run (d e B : ℕ) (A : Fin 158→List Bool) (H : Fin 158→ℕ)
    (hB : d*(2*e+3)+2≤B) (hin : ∀ j,A (slots j)=input d e B j)
    (hh : ∀ j,H (slots j)=0) :
    ∃ r,runFrom machine (budget d e) ⟨machine.start,H,A⟩=some r ∧
      r.final.heads=H ∧ r.final.tapes=install slots A (output d e B) ∧ r.steps≤budget d e :=
  (ready d e B hB).focus_at slots (by decide) H A hin hh

end NearCubicWires.RepairOrdinary.RecoveryBoundedColdArity
