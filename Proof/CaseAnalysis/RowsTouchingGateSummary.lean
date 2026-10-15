import Proof.CaseAnalysis.RowsTouchingSupportReady
import Proof.Amplification.RecoveryScratchErase

/-! Reuse the three summary fields across the original retained gates.
The same paid P driver clears old count/flags together, then one support
pass returns the exact Compare count and both physical flag bits. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsTouching.GateSummary
open LocalBitMultitape ExtDecompositionBatch RecoveryRootRound SupportScan
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def eraseSlots : Fin 5→Fin 9:=![4,5,6,8,7]
def scanSlots (i : Fin 8):Fin 9:=i.castAdd 1
noncomputable def erase:=RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 3)
noncomputable def scan:=RecoveryFocus.machine scanSlots SupportReady.machine
noncomputable def machine:=Composition.machine erase scan
def heads (pos : ℕ) : Fin 9→ℕ:=![pos,0,0,0,0,0,0,0,0]
def data (P C : ℕ) (source : List Bool) (xs : List Cell) (backing : Fin 3→List Bool):Fin 9→List Bool:=
  ![source,(masks xs) 0,(masks xs) 1,(masks xs) 2,backing 0,backing 1,backing 2,
    List.replicate C false,List.replicate P true]
def result (P : ℕ) (xs : List Cell):Fin 3→List Bool:=
  ![ZeroPadding.pad P (RepairSource.VerifierDecoding.CompareMachine.word (count xs)),
    ZeroPadding.pad P [xs.any touched],ZeroPadding.pad P [xs.any current]]

theorem summary_run (P C : ℕ) (pre tail : List Bool) (xs : List Cell) (backing : Fin 3→List Bool)
    (hP:1≤P) (hb:∀ i,(backing i).length≤P) (hC:P+1≤C) (hScan:2*xs.length+3≤C):
    Step machine (2*P+4*xs.length+13) (heads pre.length)
      (data P C (pre++frame (xs.map Prod.fst)++tail) xs backing)
      (heads (pre.length+2*xs.length+1))
      (data P C (pre++frame (xs.map Prod.fst)++tail) xs (result P xs)):=by
  let source:=pre++frame (xs.map Prod.fst)++tail
  let cleared : Fin 3→List Bool:=fun _=>List.replicate P false
  have er:=RecoveryScratchErase.erase_ready P C backing hb
  rw [Nat.max_eq_left hC] at er
  have first:Step erase (2*P+4) (heads pre.length) (data P C source xs backing)
      (heads pre.length) (data P C source xs cleared):=by
    have focused:=(Step.of_ready er).focus eraseSlots (by decide) (heads pre.length) (data P C source xs backing)
    refine focused.congr_in ?_ ?_ |>.congr ?_ ?_
    · apply dockH_existing;intro i;fin_cases i <;> rfl
    · apply install_existing;intro i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> first | rfl | exact install_slot eraseSlots (by decide) _ _ 0 | exact install_slot eraseSlots (by decide) _ _ 1 | exact install_slot eraseSlots (by decide) _ _ 2 | exact install_slot eraseSlots (by decide) _ _ 3 | exact install_slot eraseSlots (by decide) _ _ 4
  have second:Step scan (4*xs.length+8) (heads pre.length) (data P C source xs cleared)
      (heads (pre.length+2*xs.length+1)) (data P C source xs (result P xs)):=by
    have focused:=(SupportReady.ready_run P C pre tail xs hScan).focus scanSlots (by decide)
      (heads pre.length) (data P C source xs cleared)
    refine focused.congr_in ?_ ?_ |>.congr ?_ ?_
    · apply dockH_existing;intro i;fin_cases i <;> rfl
    · apply install_existing
      intro i
      fin_cases i
      · rfl
      · rfl
      · rfl
      · rfl
      · exact (pad_replicate_false P 1 hP).symm
      · exact (pad_replicate_false P 1 hP).symm
      · exact (pad_replicate_false P 1 hP).symm
      · rfl
    · funext i;fin_cases i <;> first | rfl | exact dockH_slot scanSlots (by decide) _ _ 0 | exact dockH_slot scanSlots (by decide) _ _ 1 | exact dockH_slot scanSlots (by decide) _ _ 2 | exact dockH_slot scanSlots (by decide) _ _ 3 | exact dockH_slot scanSlots (by decide) _ _ 4 | exact dockH_slot scanSlots (by decide) _ _ 5 | exact dockH_slot scanSlots (by decide) _ _ 6 | exact dockH_slot scanSlots (by decide) _ _ 7
    · funext i;fin_cases i <;> first | rfl | exact install_slot scanSlots (by decide) _ _ 0 | exact install_slot scanSlots (by decide) _ _ 1 | exact install_slot scanSlots (by decide) _ _ 2 | exact install_slot scanSlots (by decide) _ _ 3 | exact install_slot scanSlots (by decide) _ _ 4 | exact install_slot scanSlots (by decide) _ _ 5 | exact install_slot scanSlots (by decide) _ _ 6 | exact install_slot scanSlots (by decide) _ _ 7
  exact (first.seq second).enlarge (by omega)

theorem count_le (xs : List Cell):count xs≤xs.length:=by
  induction xs with
  | nil=>rfl
  | cons e xs ih=>
    simp only [count,List.length_cons]
    have hk:(kept e).toNat≤1:=by cases kept e <;> decide
    omega

theorem result_length (P : ℕ) (xs : List Cell) (h:xs.length+1≤P) (i : Fin 3):
    (result P xs i).length=P:=by
  have countBound:=count_le xs
  fin_cases i <;> simp [result,ZeroPadding.pad,RepairSource.VerifierDecoding.CompareMachine.word] <;> omega

end NearCubicWires.RepairOrdinary.CloseoutRowsTouching.GateSummary
