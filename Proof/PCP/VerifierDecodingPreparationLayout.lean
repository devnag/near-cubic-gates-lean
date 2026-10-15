import Proof.PCP.VerifierDecodingCompare
import Proof.Amplification.RecoveryCallController

/-! Concrete tape layouts at the enclosing decoder preparation boundary. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.Preparation
open LocalBitMultitape RepairOrdinary RepairOrdinary.RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def lengthLayout : Fin 4 ≃ Fin 4 where
  toFun := ![0,3,1,2]
  invFun := ![0,2,3,1]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def tLayout : Fin 4 ≃ Fin 4 where
  toFun := ![1,3,0,2]
  invFun := ![2,0,3,1]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def sLayout : Fin 4 ≃ Fin 4 where
  toFun := ![2,3,0,1]
  invFun := ![2,3,0,1]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def lengthProgram : Machine 4 6 := TapeRenaming.machine lengthLayout (TapeEmbedding.machine 2 LengthMachine.machine)
def headerProgram : Machine 4 8 := TapeEmbedding.machine 1 HeaderMachine.machine
def tProgram : Machine 4 4 := TapeRenaming.machine tLayout (TapeEmbedding.machine 2 SentinelMachine.machine)
def sProgram : Machine 4 4 := TapeRenaming.machine sLayout (TapeEmbedding.machine 2 SentinelMachine.machine)

def zeros (c : ℕ) := ZeroPadding.pad (c+2) []
def cap (word : List Bool) := CapMachine.counter word.length word.length

def initial (word : List Bool) : Configuration 4 6 :=
  ⟨lengthProgram.start,fun _ => 0,![frame word,zeros word.length,zeros word.length,zeros word.length]⟩
def headerInput (word : List Bool) : Configuration 4 8 :=
  ⟨headerProgram.start,![0,0,0,1],![frame word,zeros word.length,zeros word.length,cap word]⟩
def tInput (word : List Bool) (t s : ℕ) : Configuration 4 4 :=
  ⟨tProgram.start,![2*t+2*s+4,t,s,1],
    ![frame word,SentinelMachine.raw word.length t,SentinelMachine.raw word.length s,cap word]⟩
def sInput (word : List Bool) (t s : ℕ) : Configuration 4 4 :=
  ⟨sProgram.start,![2*t+2*s+4,1,s,1],
    ![frame word,CapMachine.counter word.length t,SentinelMachine.raw word.length s,cap word]⟩
def finished (word : List Bool) (t s : ℕ) : Configuration 4 4 :=
  ⟨3,![2*t+2*s+4,1,1,1],
    ![frame word,CapMachine.counter word.length t,CapMachine.counter word.length s,cap word]⟩

theorem length_layout (word : List Bool) :
    ∃ receipt : ExecutionReceipt 4 6,
      runFrom lengthProgram (4*word.length+3) (initial word) = some receipt ∧
      receipt.final = ⟨5,(headerInput word).heads,(headerInput word).tapes⟩ ∧
      receipt.steps = 4*word.length+3 := by
  obtain ⟨r,hr,hf,hs,_⟩ := LengthMachine.length_run word
  obtain ⟨p,hrp,hfp,hsp,_⟩ := ZeroPadding.run_config LengthMachine.machine
    ![0,word.length+2] _ _ r hr
  let eh : Fin 2 → ℕ := fun _ => 0
  let et : Fin 2 → List Bool := fun _ => zeros word.length
  have he := TapeEmbedding.run_embed LengthMachine.machine eh et _ _ p hrp
  have hren := TapeRenaming.run_rename lengthLayout (TapeEmbedding.machine 2 LengthMachine.machine) _ _ _ he
  let result := TapeRenaming.receipt lengthLayout (TapeEmbedding.receipt eh et p)
  have hi : TapeRenaming.config lengthLayout (TapeEmbedding.config eh et
      (ZeroPadding.config ![0,word.length+2] (initialConfiguration LengthMachine.machine ![frame word,[]]))) =
      initial word := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> simp [TapeRenaming.config,TapeEmbedding.config,
        ZeroPadding.config,initialConfiguration,initial,eh,et,lengthLayout,zeros,Fin.addCases]
  rw [hi] at hren
  refine ⟨result,hren,?_,hsp.trans hs⟩
  apply configuration_ext
  · change p.final.control = 5
    simp [hfp,hf,ZeroPadding.config,LengthMachine.cfg]
  · funext i; fin_cases i <;> simp [result,TapeRenaming.receipt,TapeEmbedding.receipt,
      TapeRenaming.config,TapeEmbedding.config,hfp,hf,ZeroPadding.config,LengthMachine.cfg,
      headerInput,eh,lengthLayout,Fin.addCases]
  · funext i; fin_cases i <;> simp [result,TapeRenaming.receipt,TapeEmbedding.receipt,
      TapeRenaming.config,TapeEmbedding.config,hfp,hf,ZeroPadding.config,LengthMachine.cfg,
      headerInput,et,lengthLayout,Fin.addCases,cap,CapMachine.counter]

theorem header_layout (t s : ℕ) (fields : List Bool) :
    let word := HeaderMachine.word t s fields
    ∃ receipt : ExecutionReceipt 4 8,
      runFrom headerProgram (2*t+2*s+5) (headerInput word) = some receipt ∧
      receipt.final = ⟨6,(tInput word t s).heads,(tInput word t s).tapes⟩ ∧
      receipt.steps = 2*t+2*s+5 := by
  dsimp only
  let word := HeaderMachine.word t s fields
  obtain ⟨r,hr,hf,hs,_⟩ := HeaderMachine.header_run t s fields
  obtain ⟨p,hrp,hfp,hsp,_⟩ := ZeroPadding.run_config HeaderMachine.machine
    ![0,word.length+2,word.length+2] _ _ r hr
  let eh : Fin 1 → ℕ := fun _ => 1
  let et : Fin 1 → List Bool := fun _ => cap word
  have he := TapeEmbedding.run_embed HeaderMachine.machine eh et _ _ p hrp
  let result := TapeEmbedding.receipt eh et p
  have hi : TapeEmbedding.config eh et (ZeroPadding.config ![0,word.length+2,word.length+2]
      (initialConfiguration HeaderMachine.machine ![frame word,[],[]])) = headerInput word := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> simp [TapeEmbedding.config,ZeroPadding.config,initialConfiguration,
        headerInput,eh,et,zeros,Fin.addCases]
  rw [hi] at he
  refine ⟨result,he,?_,hsp.trans hs⟩
  apply configuration_ext
  · change p.final.control = 6
    simp [hfp,hf,ZeroPadding.config,HeaderMachine.finished]
  · funext i; fin_cases i <;> simp [result,TapeEmbedding.receipt,TapeEmbedding.config,hfp,hf,
      ZeroPadding.config,HeaderMachine.finished,tInput,eh,Fin.addCases]
  · funext i; fin_cases i <;> simp [result,TapeEmbedding.receipt,TapeEmbedding.config,hfp,hf,
      ZeroPadding.config,HeaderMachine.finished,tInput,et,Fin.addCases,SentinelMachine.raw,word]

theorem t_layout (word : List Bool) (t s : ℕ) (ht : t ≤ word.length) :
    ∃ receipt : ExecutionReceipt 4 4,
      runFrom tProgram (2*word.length+3) (tInput word t s) = some receipt ∧
      receipt.final = ⟨3,(sInput word t s).heads,(sInput word t s).tapes⟩ ∧
      receipt.steps = 2*word.length+3 := by
  obtain ⟨r,hr,hf,hs,_⟩ := SentinelMachine.sentinel_run word.length t ht
  let eh : Fin 2 → ℕ := ![2*t+2*s+4,s]
  let et : Fin 2 → List Bool := ![frame word,SentinelMachine.raw word.length s]
  have he := TapeEmbedding.run_embed SentinelMachine.machine eh et _ _ r hr
  have hren := TapeRenaming.run_rename tLayout (TapeEmbedding.machine 2 SentinelMachine.machine) _ _ _ he
  let result := TapeRenaming.receipt tLayout (TapeEmbedding.receipt eh et r)
  have hi : TapeRenaming.config tLayout (TapeEmbedding.config eh et
      (SentinelMachine.cfg 0 (SentinelMachine.raw word.length t) (cap word) t 1)) = tInput word t s := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [TapeRenaming.config,TapeEmbedding.config,SentinelMachine.cfg,
        tLayout,tInput,eh,Fin.addCases]
    · funext i; fin_cases i <;> simp [TapeRenaming.config,TapeEmbedding.config,SentinelMachine.cfg,
        tLayout,tInput,et,Fin.addCases]
  dsimp only [cap] at hi
  rw [hi] at hren
  refine ⟨result,hren,?_,hs⟩
  apply configuration_ext
  · change r.final.control = 3
    simp [hf,SentinelMachine.cfg]
  · funext i; fin_cases i <;> simp [result,TapeRenaming.receipt,TapeEmbedding.receipt,
      TapeRenaming.config,TapeEmbedding.config,hf,SentinelMachine.cfg,sInput,eh,tLayout,Fin.addCases]
  · funext i; fin_cases i <;> simp [result,TapeRenaming.receipt,TapeEmbedding.receipt,
      TapeRenaming.config,TapeEmbedding.config,hf,SentinelMachine.cfg,sInput,et,tLayout,Fin.addCases,cap]

theorem s_layout (word : List Bool) (t s : ℕ) (hs : s ≤ word.length) :
    ∃ receipt : ExecutionReceipt 4 4,
      runFrom sProgram (2*word.length+3) (sInput word t s) = some receipt ∧
      receipt.final = finished word t s ∧ receipt.steps = 2*word.length+3 := by
  obtain ⟨r,hr,hf,hsteps,_⟩ := SentinelMachine.sentinel_run word.length s hs
  let eh : Fin 2 → ℕ := ![2*t+2*s+4,1]
  let et : Fin 2 → List Bool := ![frame word,CapMachine.counter word.length t]
  have he := TapeEmbedding.run_embed SentinelMachine.machine eh et _ _ r hr
  have hren := TapeRenaming.run_rename sLayout (TapeEmbedding.machine 2 SentinelMachine.machine) _ _ _ he
  let result := TapeRenaming.receipt sLayout (TapeEmbedding.receipt eh et r)
  have hi : TapeRenaming.config sLayout (TapeEmbedding.config eh et
      (SentinelMachine.cfg 0 (SentinelMachine.raw word.length s) (cap word) s 1)) = sInput word t s := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [TapeRenaming.config,TapeEmbedding.config,SentinelMachine.cfg,
        sLayout,sInput,eh,Fin.addCases]
    · funext i; fin_cases i <;> simp [TapeRenaming.config,TapeEmbedding.config,SentinelMachine.cfg,
        sLayout,sInput,et,Fin.addCases]
  dsimp only [cap] at hi
  rw [hi] at hren
  refine ⟨result,hren,?_,hsteps⟩
  apply configuration_ext
  · change r.final.control = 3
    simp [hf,SentinelMachine.cfg]
  · funext i; fin_cases i <;> simp [result,TapeRenaming.receipt,TapeEmbedding.receipt,
      TapeRenaming.config,TapeEmbedding.config,hf,SentinelMachine.cfg,finished,eh,sLayout,Fin.addCases]
  · funext i; fin_cases i <;> simp [result,TapeRenaming.receipt,TapeEmbedding.receipt,
      TapeRenaming.config,TapeEmbedding.config,hf,SentinelMachine.cfg,finished,et,sLayout,Fin.addCases,cap]

end NearCubicWires.RepairSource.VerifierDecoding.Preparation
