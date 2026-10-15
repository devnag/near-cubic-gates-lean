import Proof.Hierarchy.CompetitorSameBucketGroupArithmeticMap
import Proof.Hierarchy.HierarchyBinaryMultiplyEntry

/-! One complete reusable natural accumulator update for either sign bank:
widen the actual magnitude, execute binary add/copyback, then erase only
temporary workspace with its physical unary capacity. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketGroupArithmetic
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def normalSlots : Fin 5 → Fin 11 := ![0,1,2,3,4]
abbrev addSlots := CompetitorSameBucketGroupArithmeticMap.addSlots
abbrev eraseSlots := CompetitorSameBucketGroupArithmeticMap.eraseSlots
noncomputable def normalProgram := RecoveryFocus.machine normalSlots ClockNormalize.machine
noncomputable def addProgram := RecoveryFocus.machine addSlots MatrixScoreAccumulate.machine
noncomputable def eraseProgram := RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 6)
noncomputable def machine := Composition.machine normalProgram (Composition.machine addProgram eraseProgram)

def data (cap w : ℕ) (bits : List Bool) (a : ℕ) (scratch : Fin 6 → List Bool) : Fin 11 → List Bool :=
  ![List.replicate w true,field cap bits,scratch 0,scratch 1,scratch 2,scalar cap w a,
    scratch 3,scratch 4,scratch 5,List.replicate cap true,zeros (cap+1)]
def clean (cap : ℕ) : Fin 6 → List Bool := fun _ => zeros cap
def widened (cap w : ℕ) (bits : List Bool) : Fin 6 → List Bool :=
  ![scalar cap w (value bits),ZeroPadding.pad cap [true],zeros cap,zeros cap,zeros cap,zeros cap]
def added (cap w : ℕ) (bits : List Bool) (a : ℕ) : Fin 6 → List Bool :=
  ![scalar cap w (value bits),ZeroPadding.pad cap [true],zeros cap,
    scalar cap w (value bits+a),zeros cap,zeros cap]
def budget (cap w : ℕ) := 2*cap+16*w+23

theorem normal_stage (cap w : ℕ) (bits : List Bool) (a : ℕ) (hw : bits.length≤w) (hc : 2*w+1≤cap) :
    ReadyRun normalProgram (4*w+4) (data cap w bits a (clean cap))
      (data cap w bits a (widened cap w bits)) := by
  have h := (normal_ready cap w bits hw hc).focus normalSlots (by decide)
    (data cap w bits a (clean cap)) (by intro i; fin_cases i <;> rfl)
  have he : install normalSlots (data cap w bits a (clean cap)) (normalOutput cap w bits)=
      data cap w bits a (widened cap w bits) := by
    funext i
    fin_cases i
    all_goals first
      | exact install_slot normalSlots (by decide) _ _ 0
      | exact install_slot normalSlots (by decide) _ _ 1
      | exact install_slot normalSlots (by decide) _ _ 2
      | exact install_slot normalSlots (by decide) _ _ 3
      | exact install_slot normalSlots (by decide) _ _ 4
      | exact install_other normalSlots _ _ _ (by decide)
  rw [he] at h
  exact h

theorem focused_stage {t u s n : ℕ} (p : Machine t s) (slot : Fin t → Fin u)
    (hi : Function.Injective slot) (input output : Fin t → List Bool)
    (ambient final : Fin u → List Bool)
    (hin : ∀ j,ambient (slot j)=input j)
    (hout : install slot ambient output=final)
    (h : ReadyRun p n input output) :
    ReadyRun (RecoveryFocus.machine slot p) n ambient final := by
  have hf := h.focus slot hi ambient hin
  rw [hout] at hf
  exact hf

theorem add_stage (cap w : ℕ) (bits : List Bool) (a : ℕ) (hc : 4*w+3≤cap)
    (hfit : value bits+a<2^w) :
    ReadyRun addProgram (12*w+13) (data cap w bits a (widened cap w bits))
      (data cap w bits (value bits+a) (added cap w bits a)) := by
  apply focused_stage MatrixScoreAccumulate.machine addSlots CompetitorSameBucketGroupArithmeticMap.add_injective
    ![MatrixScoreWeight.scalar cap w (value bits),MatrixScoreWeight.scalar cap w a,
      MatrixScoreWeight.zeros cap,MatrixScoreWeight.zeros cap,MatrixScoreWeight.zeros cap]
    ![MatrixScoreWeight.scalar cap w (value bits),MatrixScoreWeight.scalar cap w (value bits+a),
      MatrixScoreWeight.scalar cap w (value bits+a),MatrixScoreWeight.zeros cap,MatrixScoreWeight.zeros cap]
  · intro i
    fin_cases i <;> rfl
  · exact CompetitorSameBucketGroupArithmeticMap.install_add _ _ _ _ _ _ _ _ _
  · exact MatrixScoreWeight.padded_accumulate cap w (value bits) a hc hfit

theorem clear_stage (cap w : ℕ) (bits : List Bool) (a : ℕ) (scratch : Fin 6 → List Bool)
    (hs : ∀ i,(scratch i).length≤cap) :
    ReadyRun eraseProgram (2*cap+4) (data cap w bits a scratch) (data cap w bits a (clean cap)) := by
  have h := (RecoveryScratchErase.erase_ready cap (cap+1) scratch hs).focus eraseSlots CompetitorSameBucketGroupArithmeticMap.erase_injective
    (data cap w bits a scratch) (by intro i; fin_cases i <;> rfl)
  simp only [max_self] at h
  let out : Fin 8 → List Bool :=
    Fin.addCases (m:=7) (n:=1) (motive:=fun _=>List Bool)
      (Fin.addCases (m:=6) (n:=1) (motive:=fun _=>List Bool)
        (fun _=>zeros cap) (fun _=>List.replicate cap true)) (fun _=>zeros (cap+1))
  change ReadyRun eraseProgram (2*cap+4) (data cap w bits a scratch)
    (install eraseSlots (data cap w bits a scratch) out) at h
  have he : install eraseSlots (data cap w bits a scratch) out=data cap w bits a (clean cap) :=
    CompetitorSameBucketGroupArithmeticMap.install_clear _ _ _ _ _ _ scratch
  rw [he] at h
  exact h

theorem accumulate_ready (cap w : ℕ) (bits : List Bool) (a : ℕ)
    (hw : bits.length≤w) (hc : 4*w+3≤cap) (hfit : value bits+a<2^w) :
    ReadyRun machine (budget cap w) (data cap w bits a (clean cap))
      (data cap w bits (value bits+a) (clean cap)) := by
  have hs : ∀ i,(added cap w bits a i).length≤cap := by
    intro i
    fin_cases i
    · exact scalar_support cap w _ (by omega)
    · simp [added,ZeroPadding.pad_length]; omega
    · simp [added,zeros]
    · exact scalar_support cap w _ (by omega)
    · simp [added,zeros]
    · simp [added,zeros]
  have htail := HierarchyMultiplyEntry.join_exact addProgram eraseProgram _ _ _ _ _
    (add_stage cap w bits a hc hfit) (clear_stage cap w bits (value bits+a) (added cap w bits a) hs)
  have h := HierarchyMultiplyEntry.join_exact normalProgram (Composition.machine addProgram eraseProgram)
    _ _ _ _ _ (normal_stage cap w bits a hw (by omega)) htail
  have he : (4*w+4)+1+((12*w+13)+1+(2*cap+4))=budget cap w := by unfold budget; omega
  simpa only [machine,he] using h

end NearCubicWires.RepairOrdinary.CompetitorSameBucketGroupArithmetic
