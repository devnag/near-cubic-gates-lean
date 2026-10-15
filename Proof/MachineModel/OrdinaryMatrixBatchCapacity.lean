import Proof.MachineModel.OrdinaryMatrixBatchNativeFields
import Proof.Hierarchy.CompetitorDimensions
import Proof.Hierarchy.HierarchyFixedWord

/-! Paid shared storage for the raw gate scheduler. Its two runtime inputs
are the scalar capacity and the already constructed assignment template. -/
namespace NearCubicWires.RepairOrdinary.MatrixBatchCapacity
open LocalBitMultitape RecoveryExecution RecoveryRootRound MatrixScoreBatch
open CompetitorRationalProducts
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def capacity (C U : ℕ) := 65536*U*(C+1)^2
def native (i : Fin 19) : Fin 26 := i.castAdd 7
def constantSlots : Fin 2 → Fin 26 := ![20,21]
def scaleSlots : Fin 4 → Fin 26 := ![17,20,22,23]
def productSlots : Fin 4 → Fin 26 := ![22,19,24,25]
def input (C U : ℕ) : Fin 26 → List Bool := fun i =>
  if i=0 then List.replicate C true else if i=19 then UnaryTemplate.tape U else []
noncomputable def first := RecoveryFocus.machine native CompetitorDimensions.machine
noncomputable def constant := RecoveryFocus.machine constantSlots (HierarchyFixedWord.machine (UnaryTemplate.tape 16))
noncomputable def scale := RecoveryFocus.machine scaleSlots ClockUnaryProduct.machine
noncomputable def product := RecoveryFocus.machine productSlots ClockUnaryProduct.machine
noncomputable def tail := Composition.machine constant (Composition.machine scale product)
noncomputable def machine := Composition.machine first tail
def budget (C U : ℕ) := CompetitorDimensions.budget C+1+(38+1+
  (WilliamsUnaryProduct.budget (CompetitorReusableDecision.capacity C) 16+1+
    WilliamsUnaryProduct.budget (CompetitorReusableDecision.capacity C*16) U))

theorem native_injective : Function.Injective native := by
  intro i j h
  exact Fin.ext (congrArg (fun a : Fin 26 => a.val) h)

theorem capacity_run (C U : ℕ) : ∃ out,ClockJoin.ReadyRun machine (budget C U) (input C U) out ∧
    out 0=List.replicate C true ∧ out 19=UnaryTemplate.tape U ∧
    out 24=List.replicate (capacity C U) true := by
  obtain ⟨base,hb,b0,_,b17⟩ := CompetitorDimensions.dimensions_run C
  have hi : ∀ i,input C U (native i)=CompetitorDimensions.input C i := by
    intro i
    fin_cases i <;> rfl
  let prepared := install native (input C U) base
  have hp := bounded_focus native native_injective _ _ _ hb (input C U) hi
  obtain ⟨fixed,hfixed,ft,fh,fs⟩ := HierarchyFixedWord.word_ready (UnaryTemplate.tape 16)
  have fixedReady : ClockJoin.ReadyRun (HierarchyFixedWord.machine (UnaryTemplate.tape 16)) 38
      (fun _ => []) ![UnaryTemplate.tape 16,List.replicate 18 false] := by
    exact ⟨fixed,hfixed,ft,fh,fs.le⟩
  have hiFixed : ∀ i,prepared (constantSlots i)=[] := by
    intro i
    fin_cases i
    all_goals exact install_other native _ _ _ (by intro j h; have hv := congrArg (fun a : Fin 26 => a.val) h; dsimp [native,constantSlots,scaleSlots,productSlots] at hv; omega)
  let printed := install constantSlots prepared ![UnaryTemplate.tape 16,List.replicate 18 false]
  have hf := bounded_focus constantSlots (by decide) _ _ _ fixedReady prepared hiFixed
  have hiScale : ∀ i,printed (scaleSlots i)=WilliamsUnaryProduct.input (CompetitorReusableDecision.capacity C) 16 i := by
    intro i
    fin_cases i
    · exact (install_other constantSlots _ _ 17 (by decide)).trans
        ((install_slot native native_injective _ base 17).trans b17)
    · exact install_slot constantSlots (by decide) _ _ 0
    all_goals
      exact (install_other constantSlots _ _ _ (by decide)).trans
        (install_other native _ _ _ (by intro j h; have hv := congrArg (fun a : Fin 26 => a.val) h; dsimp [native,constantSlots,scaleSlots,productSlots] at hv; omega))
  let scaled := install scaleSlots printed (WilliamsUnaryProduct.output (CompetitorReusableDecision.capacity C) 16)
  have hs := bounded_focus scaleSlots (by decide) _ _ _
    (CompetitorDimensions.unary_ready (CompetitorReusableDecision.capacity C) 16) printed hiScale
  have hiProduct : ∀ i,scaled (productSlots i)=WilliamsUnaryProduct.input (CompetitorReusableDecision.capacity C*16) U i := by
    intro i
    fin_cases i
    · exact install_slot scaleSlots (by decide) _ _ 2
    · exact (install_other scaleSlots _ _ 19 (by decide)).trans
        ((install_other constantSlots _ _ 19 (by decide)).trans
          (install_other native _ _ 19 (by intro j h; have hv := congrArg (fun a : Fin 26 => a.val) h; dsimp [native,constantSlots,scaleSlots,productSlots] at hv; omega)))
    all_goals
      exact (install_other scaleSlots _ _ _ (by decide)).trans
        ((install_other constantSlots _ _ _ (by decide)).trans
          (install_other native _ _ _ (by intro j h; have hv := congrArg (fun a : Fin 26 => a.val) h; dsimp [native,constantSlots,scaleSlots,productSlots] at hv; omega)))
  let out := install productSlots scaled (WilliamsUnaryProduct.output (CompetitorReusableDecision.capacity C*16) U)
  have hl := bounded_focus productSlots (by decide) _ _ _
    (CompetitorDimensions.unary_ready (CompetitorReusableDecision.capacity C*16) U) scaled hiProduct
  have hsl := ClockJoin.join scale product _ _ _ _ _ hs hl
  have htail := ClockJoin.join constant (Composition.machine scale product) _ _ _ _ _ hf hsl
  have hall := ClockJoin.join first tail _ _ _ _ _ hp htail
  refine ⟨out,hall,?_,?_,?_⟩
  · exact (install_other productSlots _ _ 0 (by decide)).trans
      ((install_other scaleSlots _ _ 0 (by decide)).trans
        ((install_other constantSlots _ _ 0 (by decide)).trans
          ((install_slot native native_injective _ base 0).trans b0)))
  · exact install_slot productSlots (by decide) _ _ 1
  · have ht := install_slot productSlots (by decide) scaled
      (WilliamsUnaryProduct.output (CompetitorReusableDecision.capacity C*16) U) 2
    apply ht.trans
    change List.replicate (CompetitorReusableDecision.capacity C*16*U) true=_
    congr 1
    unfold CompetitorReusableDecision.capacity capacity
    ring

theorem budget_bound (C U : ℕ) (hU : 1≤U) : budget C U≤20*capacity C U := by
  have hb := CompetitorDimensions.budget_bound C
  have hsq : 1≤(C+1)^2 := by
    have hp : 0<(C+1)^2 := by positivity
    omega
  unfold budget WilliamsUnaryProduct.budget capacity CompetitorReusableDecision.capacity at *
  nlinarith [Nat.mul_le_mul_left ((C+1)^2) hU]

theorem request_capacity (r : Request) :
    MatrixScoreRawRanksBounds.capacity r≤capacity (MatrixScoreLeftLoop.C r) r.U ∧
    104000*(r.U+1)≤capacity (MatrixScoreLeftLoop.C r) r.U := by
  have hu : 1≤r.U := Nat.one_le_two_pow
  have hc : 4*(r.d+r.p+1)≤MatrixScoreLeftLoop.C r+1 := by
    unfold MatrixScoreLeftLoop.C Request.S
    rw [common_width]
    omega
  have hq : 1≤r.d+r.p+1 := by omega
  have hs := Nat.pow_le_pow_left hc 2
  have hm := Nat.mul_le_mul_left r.U hs
  have hpos : 1≤(r.d+r.p+1)^2 := by nlinarith
  unfold MatrixScoreRawRanksBounds.capacity capacity
  constructor <;> nlinarith [Nat.mul_le_mul_left ((r.d+r.p+1)^2) hu]

end NearCubicWires.RepairOrdinary.MatrixBatchCapacity
