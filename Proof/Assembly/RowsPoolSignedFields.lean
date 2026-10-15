import Proof.Assembly.RowsPoolMinimumLoop
import Proof.Supplier.RowCoefficientNormalize
import Proof.CaseAnalysis.RowsStrictMagnitude

/-! Existing signed normalization and one reverse comparison supply the
exact magnitude/sign and zero test needed to serialize the transformed
threshold. The reverse comparison avoids a second magnitude traversal. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsPoolSigned
open LocalBitMultitape RecoveryExecution RecoveryRootRound ExtDecompositionBatch SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def normalSlots (i : Fin 5) : Fin 15:=i.castAdd 10
def compareSlots : Fin 4→Fin 15:=![0,1,5,4]
theorem normal_injective : Function.Injective normalSlots:=by
  intro i j h
  exact Fin.ext (congrArg (fun i : Fin 15=>i.val) h)
theorem compare_injective : Function.Injective compareSlots:=by decide
noncomputable def normalizer:=RecoveryFocus.machine normalSlots RowCoefficientNormalize.machine
noncomputable def comparator:=RecoveryFocus.machine compareSlots compareMachine
noncomputable def prefixMachine:=Composition.machine normalizer comparator
def input (w p n cap : ℕ) : Fin 15→List Bool:=
  ![frame (binary w p),frame (binary w n),[false],[],List.replicate cap false,
    [false],[],[],[],[],[],[],[],[],[]]
def normalized (w p n cap : ℕ) : Fin 15→List Bool:=
  ![frame (binary w p),frame (binary w n),[decide (n≤p)],
    frame (binary w (RowCoefficientNormalize.magnitude p n)),List.replicate (max cap (2*w+1)) false,
    [false],[],[],[],[],[],[],[],[],[]]
def compared (w p n cap : ℕ) : Fin 15→List Bool:=
  ![frame (binary w p),frame (binary w n),[decide (n≤p)],
    frame (binary w (RowCoefficientNormalize.magnitude p n)),List.replicate (max cap (2*w+1)) false,
    [decide (p≤n)],[],[],[],[],[],[],[],[],[]]

theorem normalized_run (w p n cap : ℕ) (hp : p<2^w) (hn : n<2^w) :
    ReadyRun normalizer (8*w+10) (input w p n cap) (normalized w p n cap):=by
  have h:=(RowCoefficientNormalize.normalize_run w p n cap hp hn).focus
    normalSlots normal_injective (input w p n cap) (by intro j;fin_cases j <;> rfl)
  have he:install normalSlots (input w p n cap) (RowCoefficientNormalize.output w p n cap)=
      normalized w p n cap:=by
    funext i
    fin_cases i
    all_goals first
      | exact install_slot normalSlots normal_injective _ _ 0
      | exact install_slot normalSlots normal_injective _ _ 1
      | exact install_slot normalSlots normal_injective _ _ 2
      | exact install_slot normalSlots normal_injective _ _ 3
      | exact install_slot normalSlots normal_injective _ _ 4
      | exact install_other normalSlots _ _ _ (by decide)
  exact he ▸ h

theorem comparison_run (w p n cap : ℕ) (hp : p<2^w) (hn : n<2^w) :
    ReadyRun comparator (4*w+4) (normalized w p n cap) (compared w p n cap):=by
  have h:=compare_ready (binary w p) (binary w n) (max cap (2*w+1)) (by simp)
  simp only [binary_length,binary_value w p hp,binary_value w n hn,
    max_eq_left (Nat.le_max_right cap (2*w+1))] at h
  have focused:=h.focus compareSlots compare_injective (normalized w p n cap)
    (by intro j;fin_cases j <;> rfl)
  have he:install compareSlots (normalized w p n cap)
      ![frame (binary w p),frame (binary w n),[decide (p≤n)],List.replicate (max cap (2*w+1)) false]=
      compared w p n cap:=by
    funext i
    fin_cases i
    all_goals first
      | exact install_slot compareSlots compare_injective _ _ 0
      | exact install_slot compareSlots compare_injective _ _ 1
      | exact install_slot compareSlots compare_injective _ _ 2
      | exact install_slot compareSlots compare_injective _ _ 3
      | exact install_other compareSlots _ _ _ (by decide)
  exact he ▸ focused

theorem prefix_run (w p n cap : ℕ) (hp : p<2^w) (hn : n<2^w) :
    ClockJoin.ReadyRun prefixMachine (12*w+15) (input w p n cap) (compared w p n cap):=by
  have h:=(Step.of_ready (normalized_run w p n cap hp hn)).seq
    (Step.of_ready (comparison_run w p n cap hp hn))
  have ht:(8*w+10)+1+(4*w+4)=12*w+15:=by omega
  rw [ht] at h
  obtain ⟨r,hr,rh,rt,rs⟩:=h
  exact ⟨r,hr,rt,fun i=>congrFun rh i,rs⟩

theorem compared_zero (w p n cap : ℕ) :
    (readTapeBit (compared w p n cap 2) 0 && readTapeBit (compared w p n cap 5) 0)=decide (p=n):=by
  change (decide (n≤p) && decide (p≤n))=decide (p=n)
  by_cases h:p=n
  · subst n;simp
  · by_cases hn:n≤p
    · have hp:¬p≤n:=by omega
      simp [hn,hp,h]
    · simp [hn,h]

theorem magnitude_fit (w p n : ℕ) (hp : p<2^w) (hn : n<2^w) :
    RowCoefficientNormalize.magnitude p n<2^w:=by
  unfold RowCoefficientNormalize.magnitude
  split <;> omega

theorem magnitude_positive (p n : ℕ) (h:p≠n) : 0<RowCoefficientNormalize.magnitude p n:=by
  unfold RowCoefficientNormalize.magnitude
  split <;> omega

end NearCubicWires.RepairOrdinary.CloseoutRowsPoolSigned
