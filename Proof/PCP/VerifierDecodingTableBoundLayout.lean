import Proof.PCP.VerifierDecodingRangeReject

/-! The table-size guard computes 2^t and then s*2^t with the existing capped
ordinary arithmetic. The power-to-product handoff includes a paid cap-cursor
return, and the two initial unit marks are written by the finite controller. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.TableBoundMachine
open LocalBitMultitape RepairOrdinary RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def store (c a b t result s : ℕ) (flag : Bool) : Fin 7 → List Bool :=
  ![CapMachine.counter c a,CapMachine.counter c b,CapMachine.counter c c,
    CapMachine.counter c t,CapMachine.counter c result,CapMachine.counter c s,[flag]]
def initProgram : Machine 7 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val = 1
  rule := fun q _ => if q.val = 0 then
    some ⟨1,![some true,some true,none,none,none,none,none],![.stay,.right,.right,.stay,.stay,.stay,.stay]⟩
    else none

def resetLayout : Fin 7 ≃ Fin 7 where
  toFun := ![2,0,1,3,4,5,6]
  invFun := ![1,2,0,3,4,5,6]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def productLayout : Fin 7 ≃ Fin 7 where
  toFun := ![0,4,2,5,1,3,6]
  invFun := ![0,4,2,5,1,3,6]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def powerProgram : Machine 7 11 := TapeEmbedding.machine 3 PowerMachine.machine
def resetProgram : Machine 7 3 := TapeRenaming.machine resetLayout (TapeEmbedding.machine 6 UnaryTemplate.machine)
def productProgram : Machine 7 6 := TapeRenaming.machine productLayout (TapeEmbedding.machine 3 ProductMachine.machine)

def initial (c t s : ℕ) : Configuration 7 2 := ⟨0,![1,1,1,1,1,1,0],store c 0 0 t 0 s false⟩
def powerInput (c t s : ℕ) : Configuration 7 11 := ⟨0,![1,2,2,1,1,1,0],store c 1 1 t 0 s false⟩
def powerOutput (c t s p : ℕ) : Configuration 7 11 :=
  ⟨9,![1,p+1,p+1,t+1,1,1,0],store c p p t 0 s false⟩
def resetInput (c t s p : ℕ) : Configuration 7 3 :=
  ⟨resetProgram.start,(powerOutput c t s p).heads,(powerOutput c t s p).tapes⟩
def productInput (c t s p : ℕ) : Configuration 7 6 :=
  ⟨0,![1,p+1,1,t+1,1,1,0],store c p p t 0 s false⟩
def productOutput (c t s p result : ℕ) : Configuration 7 6 :=
  ⟨4,![1,p+1,result+1,t+1,result+1,s+1,0],store c p p t result s false⟩

theorem init_step (c t s : ℕ) :
    step initProgram (initial c t s) = some (⟨1,(powerInput c t s).heads,(powerInput c t s).tapes⟩ : Configuration 7 2) := by
  simp [step,initProgram,initial]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply,powerInput]
  · funext i; fin_cases i <;> simp [applyAction,powerInput,store,CapMachine.counter_write]

theorem power_layout (c t s : ℕ) (hc : 1 ≤ c) (ht : t ≤ c) :
    ∃ receipt : ExecutionReceipt 7 11,
      runFrom powerProgram (t*(8*c+9)+1) (powerInput c t s) = some receipt ∧
      receipt.steps ≤ t*(8*c+9)+1 ∧
      (if 2^t ≤ c then receipt.final = powerOutput c t s (2^t)
       else receipt.final.control = 10 ∧ receipt.final.tapes 6 = [false]) := by
  obtain ⟨r,hr,hf,hs,_⟩ := PowerMachine.capped_power_run c t hc ht
  let eh : Fin 3 → ℕ := ![1,1,0]
  let et : Fin 3 → List Bool := ![CapMachine.counter c 0,CapMachine.counter c s,[false]]
  have hp := TapeEmbedding.run_embed PowerMachine.machine eh et _ _ r hr
  let result := TapeEmbedding.receipt eh et r
  have hi : TapeEmbedding.config eh et (PowerMachine.boundary c t 0 1) = powerInput c t s := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [hi] at hp
  refine ⟨result,hp,hs,?_⟩
  by_cases hfit : 2^t ≤ c
  · simp only [PowerMachine.Result,if_pos hfit] at hf
    simp only [if_pos hfit]
    apply configuration_ext
    · change r.final.control = 9
      simp [hf]
    · funext i; fin_cases i <;> simp [result,TapeEmbedding.receipt,TapeEmbedding.config,hf,
        PowerMachine.boundary,powerOutput,eh,Fin.addCases]
    · funext i; fin_cases i <;> simp [result,TapeEmbedding.receipt,TapeEmbedding.config,hf,
        PowerMachine.boundary,powerOutput,store,et,Fin.addCases]
  · simp only [PowerMachine.Result,if_neg hfit] at hf
    simp only [if_neg hfit]
    exact ⟨hf.1,rfl⟩

theorem reset_layout (c t s p : ℕ) (hp : p ≤ c) :
    ∃ receipt : ExecutionReceipt 7 3,
      runFrom resetProgram (p+2) (resetInput c t s p) = some receipt ∧
      receipt.final = ⟨2,(productInput c t s p).heads,(productInput c t s p).tapes⟩ ∧
      receipt.steps = p+2 := by
  obtain ⟨r,hr,hf,hs,_⟩ := CapMachine.reset_run c c p (Nat.le_refl _) hp
  let eh : Fin 6 → ℕ := ![1,p+1,t+1,1,1,0]
  let et : Fin 6 → List Bool := ![CapMachine.counter c p,CapMachine.counter c p,
    CapMachine.counter c t,CapMachine.counter c 0,CapMachine.counter c s,[false]]
  have he := TapeEmbedding.run_embed UnaryTemplate.machine eh et _ _ r hr
  have hren := TapeRenaming.run_rename resetLayout (TapeEmbedding.machine 6 UnaryTemplate.machine) _ _ _ he
  let result := TapeRenaming.receipt resetLayout (TapeEmbedding.receipt eh et r)
  have hi : TapeRenaming.config resetLayout (TapeEmbedding.config eh et
      (UnaryTemplate.config 0 (CapMachine.counter c c) (p+1))) = resetInput c t s p := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [TapeRenaming.config,TapeEmbedding.config,UnaryTemplate.config,
        resetInput,powerOutput,eh,resetLayout,Fin.addCases]
    · funext i; fin_cases i <;> simp [TapeRenaming.config,TapeEmbedding.config,UnaryTemplate.config,
        resetInput,powerOutput,store,et,resetLayout,Fin.addCases]
  rw [hi] at hren
  refine ⟨result,hren,?_,hs⟩
  apply configuration_ext
  · change r.final.control = 2
    simp [hf,UnaryTemplate.config]
  · funext i; fin_cases i <;> simp [result,TapeRenaming.receipt,TapeEmbedding.receipt,
      TapeRenaming.config,TapeEmbedding.config,hf,UnaryTemplate.config,productInput,eh,resetLayout,Fin.addCases]
  · funext i; fin_cases i <;> simp [result,TapeRenaming.receipt,TapeEmbedding.receipt,
      TapeRenaming.config,TapeEmbedding.config,hf,UnaryTemplate.config,productInput,store,et,resetLayout,Fin.addCases]

theorem product_layout (c t s p : ℕ) (hp : p ≤ c) (hs : s ≤ c) :
    ∃ receipt : ExecutionReceipt 7 6,
      runFrom productProgram (s*(2*p+4)+1) (productInput c t s p) = some receipt ∧
      receipt.steps ≤ s*(2*p+4)+1 ∧
      (if p*s ≤ c then receipt.final = productOutput c t s p (p*s)
       else receipt.final.control = 5 ∧ receipt.final.tapes 6 = [false]) := by
  obtain ⟨r,hr,hf,hsteps,_⟩ := ProductMachine.capped_product_run c p s hp hs
  let eh : Fin 3 → ℕ := ![p+1,t+1,0]
  let et : Fin 3 → List Bool := ![CapMachine.counter c p,CapMachine.counter c t,[false]]
  have he := TapeEmbedding.run_embed ProductMachine.machine eh et _ _ r hr
  have hren := TapeRenaming.run_rename productLayout (TapeEmbedding.machine 3 ProductMachine.machine) _ _ _ he
  let result := TapeRenaming.receipt productLayout (TapeEmbedding.receipt eh et r)
  have hi : TapeRenaming.config productLayout (TapeEmbedding.config eh et
      (ProductMachine.boundary c p s 0 0)) = productInput c t s p := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [TapeRenaming.config,TapeEmbedding.config,ProductMachine.boundary,
        productInput,eh,productLayout,Fin.addCases]
    · funext i; fin_cases i <;> simp [TapeRenaming.config,TapeEmbedding.config,ProductMachine.boundary,
        productInput,store,et,productLayout,Fin.addCases]
  rw [hi] at hren
  refine ⟨result,hren,hsteps,?_⟩
  by_cases hfit : p*s ≤ c
  · simp only [ProductMachine.Result,if_pos hfit] at hf
    simp only [if_pos hfit]
    apply configuration_ext
    · change r.final.control = 4
      simp [hf]
    · funext i; fin_cases i <;> simp [result,TapeRenaming.receipt,TapeEmbedding.receipt,
        TapeRenaming.config,TapeEmbedding.config,hf,ProductMachine.boundary,
        productOutput,eh,productLayout,Fin.addCases]
    · funext i; fin_cases i <;> simp [result,TapeRenaming.receipt,TapeEmbedding.receipt,
        TapeRenaming.config,TapeEmbedding.config,hf,ProductMachine.boundary,
        productOutput,store,et,productLayout,Fin.addCases]
  · simp only [ProductMachine.Result,if_neg hfit] at hf
    simp only [if_neg hfit]
    exact ⟨hf.1,rfl⟩

end NearCubicWires.RepairSource.VerifierDecoding.TableBoundMachine
