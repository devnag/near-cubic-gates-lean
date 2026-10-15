import Proof.Amplification.RecoveryHeaderCopies

/-! Cold header entry: the five-tape dimension computation is physically
embedded into the twenty-tape bank, then one paid transition restores the
width head and writes the framed empty seed used by the zero-field copy. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdHeader
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def input (bits : List Bool) (i : Fin 20) := if i.val=0 then frame bits else []
def before (bits : List Bool) (cap scratch : Nat) :=
  Function.update (base bits cap scratch fields0) 11 []
def beforeHeads (i : Fin 20) : Nat := if i.val=1 then 1 else 0
noncomputable def dimensionsMachine := TapeEmbedding.machine 15 RecoveryColdDimensions.machine

def setupMachine : Machine 20 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==1
  rule := fun q _=>if q.val=0 then
    some ⟨1,(fun i=>if i.val=11 then some false else none),
      (fun i=>if i.val=1 then .left else .stay)⟩ else none

theorem setup_step (bits : List Bool) (cap scratch : Nat) :
    step setupMachine ⟨0,beforeHeads,before bits cap scratch⟩=
      some ⟨1,fun _=>0,base bits cap scratch fields0⟩ := by
  simp only [step,setupMachine]
  apply congrArg some
  apply configuration_ext
  · rfl
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i <;> simp [applyAction,before,beforeHeads,base,fields0,writeTapeBit]

theorem setup_run (bits : List Bool) (cap scratch : Nat) :
    ∃ r,runFrom setupMachine 1 ⟨setupMachine.start,beforeHeads,before bits cap scratch⟩=some r ∧
      r.final.heads=(fun _=>0) ∧ r.final.tapes=base bits cap scratch fields0 := by
  obtain ⟨r,hr,hf,_⟩ := (Timed.single (by rfl) (setup_step bits cap scratch)).run (by rfl)
  exact ⟨r,hr,by rw [hf],by rw [hf]⟩

theorem dimensions_entry (bits : List Bool) :
    ∃ cap scratch,cap ≤ 2*PCPResourceLedger.ell bits.length+3 ∧ scratch ≤ HierarchyInputLength.rawBudget bits ∧
      ∃ r,run dimensionsMachine (RecoveryColdDimensions.budget bits) (input bits)=some r ∧
        r.final.heads=beforeHeads ∧ r.final.tapes=before bits cap scratch := by
  obtain ⟨cap,scratch,hcap,hscratch,b,hb,hbh,hbt,_⟩ := RecoveryColdDimensions.dimensions_run bits
  obtain ⟨r,hr,_,hf⟩ := RecoveryBankPair.left_run RecoveryColdDimensions.machine
    (RecoveryColdDimensions.budget bits) (initialConfiguration RecoveryColdDimensions.machine (RecoveryColdDimensions.input bits)) b hb
    (fun _ : Fin 15=>0) (fun _=>[])
  have hi : RecoveryBankPair.cfg
      (initialConfiguration RecoveryColdDimensions.machine (RecoveryColdDimensions.input bits)).heads
      (initialConfiguration RecoveryColdDimensions.machine (RecoveryColdDimensions.input bits)).tapes
      (fun _ : Fin 15=>0) (fun _=>[])
      (initialConfiguration RecoveryColdDimensions.machine (RecoveryColdDimensions.input bits)).control=
      initialConfiguration dimensionsMachine (input bits) := by
    apply configuration_ext
    · rfl
    · funext i
      fin_cases i <;> rfl
    · funext i
      fin_cases i <;> rfl
  rw [hi] at hr
  refine ⟨cap,scratch,hcap,hscratch,r,hr,?_,?_⟩
  · rw [hf,hbh]
    funext i
    fin_cases i <;> rfl
  · rw [hf,hbt]
    funext i
    fin_cases i <;> rfl

noncomputable def frontMachine := Composition.machine dimensionsMachine setupMachine

theorem front_run (bits : List Bool) :
    ∃ cap scratch,cap ≤ 2*PCPResourceLedger.ell bits.length+3 ∧ scratch ≤ HierarchyInputLength.rawBudget bits ∧
      ∃ r,run frontMachine (RecoveryColdDimensions.budget bits+2) (input bits)=some r ∧
        r.final.heads=(fun _=>0) ∧ r.final.tapes=base bits cap scratch fields0 := by
  obtain ⟨cap,scratch,hcap,hscratch,b,hb,hbh,hbt⟩ := dimensions_entry bits
  obtain ⟨last,hl,hlh,hlt⟩ := setup_run bits cap scratch
  have hi : Composition.restart b.final setupMachine.start=
      (⟨setupMachine.start,beforeHeads,before bits cap scratch⟩ : Configuration 20 2) := by
    apply configuration_ext
    · rfl
    · exact hbh
    · exact hbt
  rw [←hi] at hl
  have h := Composition.run_join dimensionsMachine setupMachine
    (RecoveryColdDimensions.budget bits) 1 _ b last hb hl
  have he : RecoveryColdDimensions.budget bits+1+1=RecoveryColdDimensions.budget bits+2 := by omega
  rw [he] at h
  exact ⟨cap,scratch,hcap,hscratch,Composition.joinedReceipt b last,h,hlh,hlt⟩

end NearCubicWires.RepairOrdinary.RecoveryColdHeader
