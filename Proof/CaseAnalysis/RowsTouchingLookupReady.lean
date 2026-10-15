import Proof.CaseAnalysis.RowsTouchingTableLookup
import Proof.Circuits.DecompositionCountPosition

/-! The complete lookup returns the table and all query driver heads to
zero. Its scalar backing is overwritten directly, and its byte workspace
uses the already produced Pascal row capacity. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsTouching.LookupReady
open LocalBitMultitape ExtDecompositionBatch RecoveryRootRound SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def directions : Fin 7→HeadMove:=![.stay,.right,.right,.right,.stay,.stay,.stay]
def move:=DecompositionCountPosition.move directions
noncomputable def core:=Composition.machine move Lookup.machine
noncomputable def machine:=MaskedReset.machine core (fun _=>true)
def data (q m k : ℕ) (backing : List Bool) : Fin 7→List Bool:=
  Function.update (Lookup.data (PascalReady.width q) (q+1) m k (PascalTable.table q) backing)
    6 (List.replicate (PascalReady.width q) false)
def input (q m k C : ℕ) (backing : List Bool):Fin 8→List Bool:=
  fun i=>Fin.addCases (data q m k backing) (fun _ : Fin 1=>List.replicate C false) i
def budget (q m k : ℕ):=2*(Lookup.budget (PascalReady.width q) (q+1) m k+2)+2

theorem ready_run (q m k C : ℕ) (backing : List Bool) (hm:m≤q) (hk:k≤q)
    (hb:backing.length≤2*(q+1)+1) (hC:Lookup.budget (PascalReady.width q) (q+1) m k+2≤C):
    Step machine (budget q m k) (fun _=>0) (input q m k C backing) (fun _=>0)
      (input q m k C (frame (binary (q+1) (Nat.choose m k)))):=by
  have actual:=TableLookup.lookup_run q m k backing hm hk hb
  let caps : Fin 7→ℕ:=![0,0,0,0,0,0,PascalReady.width q]
  have width:2*(q+1)+1≤PascalReady.width q:=by
    unfold PascalReady.width
    have h:1≤q+1:=by omega
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right (2*(q+1)+1) h
  have padded:Step Lookup.machine (Lookup.budget (PascalReady.width q) (q+1) m k) (Lookup.heads 0)
      (data q m k backing) (Lookup.heads (m*PascalReady.width q+k*(2*(q+1)+1)+2*(q+1)+1))
      (data q m k (frame (binary (q+1) (Nat.choose m k)))):=by
    refine (actual.pad caps).congr_in rfl ?_ |>.congr rfl ?_
    all_goals funext i;fin_cases i <;> first | exact ZeroPadding.pad_zero _ | exact pad_replicate_false _ _ width
  obtain ⟨r,run,rf,_⟩:=DecompositionCountPosition.move_run directions (fun _=>0) (data q m k backing)
  have positioned:Step move 1 (fun _=>0) (data q m k backing) (Lookup.heads 0) (data q m k backing):=by
    refine Step.of_run run ?_ ?_
    · rw [rf];funext i;fin_cases i <;> rfl
    · rw [rf]
  have both:=positioned.seq padded
  have time:1+1+Lookup.budget (PascalReady.width q) (q+1) m k=
      Lookup.budget (PascalReady.width q) (q+1) m k+2:=by omega
  rw [time] at both
  have reset:=both.mask (fun _=>true) (by intro i hi;rfl) hC
  exact reset.congr_in (by funext i;fin_cases i <;> rfl)
    (by funext i;fin_cases i <;> rfl) |>.congr
    (by funext i;fin_cases i <;> rfl) (by funext i;fin_cases i <;> rfl)

end NearCubicWires.RepairOrdinary.CloseoutRowsTouching.LookupReady
