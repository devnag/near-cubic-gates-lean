import Proof.CaseAnalysis.RowsTouchingSelectorOutput
import Proof.Assembly.RowsPoolMinimumLoop
import Proof.CaseAnalysis.RowsGateSupportMeaning

/-! A.4 mask dock.  The deterministic touching selector already leaves the
live-set mask on one physical tape.  The X/C pool loops read their live bit
from a mask tape of their own port chart; this file shows the two are the
SAME list, and fixes the injective slot maps that let the pool loops be
docked onto the selector's bank without copying the mask. -/
namespace NearCubicWires.RepairOrdinary.CloseoutFinalPool
open LocalBitMultitape ExtDecompositionBatch RecoveryRootRound
open CloseoutRowsGateSupport CloseoutRowsPoolWeight
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-- The pool item list of one gate under one live set. -/
def items {n : ℕ} (g : NormalizedThresholdGate n) (live : Finset (Fin n)) : List Item :=
  List.ofFn (fun i : Fin n => (g.weight i,decide (i∈live)))

@[simp] theorem items_length {n : ℕ} (g : NormalizedThresholdGate n) (live : Finset (Fin n)) :
    (items g live).length=n:=List.length_ofFn

/-- The pool mask port is literally the selector's gate-member word. -/
theorem items_mask {n : ℕ} (g : NormalizedThresholdGate n) (live : Finset (Fin n)) :
    mask (items g live)=gateMembers live:=by
  simp only [mask,items,gateMembers,List.map_ofFn,Function.comp_def]

theorem items_word {n : ℕ} (g : NormalizedThresholdGate n) (live : Finset (Fin n)) :
    word (items g live)=(List.ofFn g.weight).flatMap RepairRepresentation.intWord:=by
  simp only [word,items,List.ofFn_eq_map,List.flatMap_map]

theorem items_bits {n : ℕ} (g : NormalizedThresholdGate n) (live : Finset (Fin n)) (b : ℕ)
    (hb:∀ i,natBitLength (g.weight i).natAbs≤b) :
    ∀ x∈items g live,natBitLength x.1.natAbs≤b:=by
  intro x hx
  rcases List.mem_ofFn.mp hx with ⟨i,rfl⟩
  exact hb i

/-- A `RepeatMachine` loop receipt, restated as this project's `Step`. -/
theorem step_of_repeat {t s : ℕ} (body : Machine t s) (acc : Fin s→(Fin t→Bool)→Bool) (n : ℕ)
    (c d : Configuration t s) (total h1 h2 : ℕ)
    (r : ExecutionReceipt (t+1) (Fintype.card (RepeatMachine.Control s)))
    (hr:runFrom (RepeatMachine.machine body acc) n (RepeatMachine.cfg 0 c total h1)=some r)
    (hf:r.final=RepeatMachine.cfg 3 d total h2) :
    Step (RepeatMachine.machine body acc) n
      (Fin.addCases c.heads (fun _ : Fin 1=>h1))
      (Fin.addCases c.tapes (fun _ : Fin 1=>CompareMachine.word total))
      (Fin.addCases d.heads (fun _ : Fin 1=>h2))
      (Fin.addCases d.tapes (fun _ : Fin 1=>CompareMachine.word total)):=by
  have entry:RepeatMachine.cfg 0 c total h1=
      (⟨(RepeatMachine.machine body acc).start,Fin.addCases c.heads (fun _ : Fin 1=>h1),
        Fin.addCases c.tapes (fun _ : Fin 1=>CompareMachine.word total)⟩ :
          Configuration (t+1) (Fintype.card (RepeatMachine.Control s))):=by
    apply configuration_ext
    · rfl
    · rfl
    · rfl
  rw [entry] at hr
  exact Step.of_run hr (by rw [hf];rfl) (by rw [hf];rfl)

/-! ### The shared bank.

`Fin 64` holds the selector's 36 tapes at 0-35, the weight loop's private
tapes at 36-39 and the minimum loop's private tapes at 41-61.  BOTH pool
loops take their mask port to slot 1 - the very tape the selector wrote. -/

def selSlots : Fin 36→Fin 64:=Fin.castLE (by omega)
def weightSlots : Fin 5→Fin 64:=fun i=>if i.val=3 then 1 else Fin.castLE (by omega) (Fin.natAdd 36 i)
def minSlots : Fin 21→Fin 64:=fun i=>if i.val=13 then 1 else Fin.castLE (by omega) (Fin.natAdd 41 i)

theorem sel_injective : Function.Injective selSlots:=Fin.castLE_injective _
theorem weight_injective : Function.Injective weightSlots:=by decide
theorem min_injective : Function.Injective minSlots:=by decide

/-- The selector's live-mask output port. -/
def maskPort : Fin 64:=selSlots ((1 : Fin 35).castAdd 1)

/-- No copy: the weight loop's mask port IS the selector's mask port. -/
theorem weight_mask_port : weightSlots 3=maskPort:=by decide
/-- No copy: the minimum loop's mask port IS the selector's mask port. -/
theorem min_mask_port : minSlots 13=maskPort:=by decide
theorem mask_port_val : maskPort=(1 : Fin 64):=by decide

theorem sel_val (k : Fin 36):(selSlots k).val=k.val:=rfl
theorem weight_val (j : Fin 5) (hj:j.val≠3):(weightSlots j).val=36+j.val:=by
  simp only [weightSlots,if_neg hj]
  rfl
theorem min_val (j : Fin 21) (hj:j.val≠13):(minSlots j).val=41+j.val:=by
  simp only [minSlots,if_neg hj]
  rfl

theorem sel_ne_weight (j : Fin 5) (hj:j.val≠3) (k : Fin 36):selSlots k≠weightSlots j:=by
  intro he
  have hv:=congrArg Fin.val he
  rw [sel_val,weight_val j hj] at hv
  have hk:=k.isLt
  omega

theorem sel_ne_min (j : Fin 21) (hj:j.val≠13) (k : Fin 36):selSlots k≠minSlots j:=by
  intro he
  have hv:=congrArg Fin.val he
  rw [sel_val,min_val j hj] at hv
  have hk:=k.isLt
  omega

theorem weight_ne_min (i : Fin 5) (j : Fin 21) (hj:j.val≠13):weightSlots i≠minSlots j:=by
  intro he
  have hv:=congrArg Fin.val he
  rw [min_val j hj] at hv
  by_cases hi:i.val=3
  · have h1:(weightSlots i).val=1:=by simp [weightSlots,hi]
    omega
  · rw [weight_val i hi] at hv
    have hk:=i.isLt
    omega

end NearCubicWires.RepairOrdinary.CloseoutFinalPool
