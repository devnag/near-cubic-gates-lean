import Proof.MachineModel.OrdinaryMatrixComplementValue

/-! A right-plane bucket executes the paid complement and then the SAME
accepted keyed scan. Only rank-labelled records and ordinary scalar/key
workspace are its entry data; no complement word is supplied by the caller. -/
namespace NearCubicWires.RepairOrdinary.MatrixRightScan
open LocalBitMultitape SignedSortKey RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure Request where
  S : ℕ
  K : ℕ
  I : ℕ
  inner : ℕ
  keyCap : ℕ
  resetCap : ℕ
  a : ℕ
  initialRank : ℕ
  records : List KeyLoop.Record
  upper : List Bool
  recordBack : List Bool
  cloneBack : List Bool
  out : List Bool
  backing : List Bool
  aFit : a<2^(K+S+1)
  rankFit : ∀ r ∈ records,r.2.2<2^(K+S+1)-1
  upperFit : upper.length ≤ 2*(K+S+1)+1
  recordFit : recordBack.length ≤ 4*(K+S+1)+1
  cloneFit : cloneBack.length ≤ 4*(K+S+1)+1
  backingFit : backing.length ≤ 2*(K+S+1)+1
  keyI : 2*I ≤ keyCap
  keyK : 2*K ≤ keyCap
  resetFit : records.length*(68*(K+S+1)+4*(I+K)+63)+1 ≤ resetCap

def width (r : Request) := r.K+r.S+1
def fuel (r : Request) := r.records.length*(68*width r+4*(r.I+r.K)+63)+1

def core (r : Request) : Configuration 21 57 :=
  KeyReset.config KeyReset.machine.start (width r) r.a (MatrixComplement.difference (width r) r.a) r.initialRank
    r.upper r.recordBack r.cloneBack true (KeyLoop.stream r.S r.K r.records) r.out r.K r.I r.inner r.keyCap r.resetCap

def extended (r : Request) : Configuration 22 57 :=
  TapeEmbedding.config (fun _ : Fin 1 => 0) (fun _ : Fin 1 => List.replicate (2*width r+1) false) (core r)
def slots : Fin 3 → Fin 22 := ![0,1,21]
noncomputable def first : Machine 22 5 := RecoveryFocus.machine slots MatrixComplement.resetMachine
def scan : Machine 22 57 := TapeEmbedding.machine 1 KeyReset.machine
noncomputable def machine : Machine 22 62 := Composition.machine first scan

noncomputable def entry (r : Request) : Configuration 22 5 :=
  ⟨first.start,(extended r).heads,Function.update (extended r).tapes 1 r.backing⟩
def output (r : Request) : List Bool :=
  r.records.flatMap (fun e => frame (decide (r.a≤e.2.2)::(binary r.I r.inner++binary r.K e.2.1)))

theorem output_eq (r : Request) :
    KeyLoop.output r.K r.I r.inner r.a (MatrixComplement.difference (width r) r.a) true r.records=output r := by
  unfold KeyLoop.output output
  apply List.flatMap_congr
  intro e he
  rw [MatrixComplement.selected_right (width r) r.a e.2.2 r.aFit (r.rankFit e he)]

theorem complement_run (r : Request) :
    ∃ actual : ExecutionReceipt 22 5,runFrom first (4*width r+4) (entry r)=some actual ∧
      actual.final=Composition.restart (extended r) actual.final.control ∧ actual.steps=4*width r+4 := by
  obtain ⟨base,hb,h0,h1,h2,hh,hs⟩ := MatrixComplement.workspace_run (width r) r.a r.backing r.aFit r.backingFit
  let part := initialConfiguration MatrixComplement.resetMachine (MatrixComplement.workspaceInput (width r) r.a r.backing)
  have hi : RecoveryFocus.config slots (entry r).heads (entry r).tapes part=entry r := by
    apply WilliamsSourceCrop.focus_same
    · intro i; fin_cases i <;> rfl
    · intro i; fin_cases i <;> simp [entry,slots,part,initialConfiguration,MatrixComplement.workspaceInput]
      all_goals rfl
  obtain ⟨actual,ha,hf,hsteps⟩ := RecoveryFocus.run_config slots (by decide) MatrixComplement.resetMachine
    (entry r).heads (entry r).tapes _ part base hb
  rw [hi] at ha
  have hp (i : Fin 3) : RecoveryFocus.pick slots (slots i)=some i := RecoveryFocus.pick_slot slots (by decide) i
  have hp1 : RecoveryFocus.pick slots 1=some 1 := hp 1
  refine ⟨actual,ha,?_,hsteps.trans hs⟩
  rw [hf]
  apply configuration_ext
  · rfl
  · funext i
    cases hi : RecoveryFocus.pick slots i with
    | none => simp only [RecoveryFocus.config,hi]; rfl
    | some j =>
      have hij := RecoveryFocus.slot_of_pick slots hi
      simp only [RecoveryFocus.config,hi,Composition.restart]
      rw [hh]
      rw [←hij]
      fin_cases j <;> rfl
  · funext i
    cases hi : RecoveryFocus.pick slots i with
    | none =>
      have hn : i≠1 := by intro he; subst i; rw [hp1] at hi; contradiction
      simp only [RecoveryFocus.config,hi,Composition.restart,entry,Function.update_of_ne hn]
    | some j =>
      have hij := RecoveryFocus.slot_of_pick slots hi
      simp only [RecoveryFocus.config,hi,Composition.restart]
      rw [←hij]
      fin_cases j
      · exact h0
      · exact h1
      · exact h2

theorem scan_run (r : Request) :
    ∃ finalRank finalUpper finalRecord finalClone,
      finalUpper.length ≤ 2*width r+1 ∧ finalRecord.length ≤ 4*width r+1 ∧ finalClone.length ≤ 4*width r+1 ∧
      ∃ actual : ExecutionReceipt 22 62,
        runFrom machine (2*fuel r+4*width r+7) (Composition.leftConfig 57 (entry r))=some actual ∧
        actual.final=Composition.rightConfig 5
          (TapeEmbedding.config (fun _ : Fin 1 => 0) (fun _ : Fin 1 => List.replicate (2*width r+1) false)
            (KeyReset.config (56 : Fin 57) (width r) r.a (MatrixComplement.difference (width r) r.a) finalRank
              finalUpper finalRecord finalClone true (KeyLoop.stream r.S r.K r.records) (r.out++output r)
              r.K r.I r.inner r.keyCap r.resetCap)) ∧ actual.steps ≤ 2*fuel r+4*width r+7 := by
  have hfit : r.a+MatrixComplement.difference (width r) r.a<2^(r.K+r.S+1) := by
    rw [MatrixComplement.sum_difference (width r) r.a r.aFit]
    have hp : 0<2^width r := pow_pos (by decide) _
    change 2^width r-1<2^width r
    omega
  obtain ⟨fr,fu,fre,fc,hfu,hfre,hfc,last,hl,hlf,hls,_⟩ := KeyReset.scan_run r.S r.K r.I r.inner r.keyCap r.resetCap
    r.a (MatrixComplement.difference (width r) r.a) r.initialRank r.records r.upper r.recordBack r.cloneBack r.out true
    hfit (fun e he => (r.rankFit e he).trans_le (Nat.sub_le _ _)) r.upperFit r.recordFit r.cloneFit r.keyI r.keyK r.resetFit
  obtain ⟨firstRun,hfirst,hff,hfs⟩ := complement_run r
  have he := TapeEmbedding.run_embed KeyReset.machine (fun _ : Fin 1 => 0)
    (fun _ : Fin 1 => List.replicate (2*width r+1) false) _ _ last hl
  have hi : Composition.restart firstRun.final scan.start=extended r := by
    rw [hff]
    rfl
  have he' : runFrom scan (2*fuel r+2) (Composition.restart firstRun.final scan.start)=
      some (TapeEmbedding.receipt (fun _ : Fin 1 => 0) (fun _ : Fin 1 => List.replicate (2*width r+1) false) last) := by
    rw [hi]
    exact he
  have hj := Composition.run_join first scan (4*width r+4) (2*fuel r+2) (entry r) firstRun
    (TapeEmbedding.receipt (fun _ : Fin 1 => 0) (fun _ : Fin 1 => List.replicate (2*width r+1) false) last) hfirst he'
  have htime : (4*width r+4)+1+(2*fuel r+2)=2*fuel r+4*width r+7 := by omega
  rw [htime] at hj
  refine ⟨fr,fu,fre,fc,hfu,hfre,hfc,Composition.joinedReceipt firstRun
    (TapeEmbedding.receipt (fun _ : Fin 1 => 0) (fun _ : Fin 1 => List.replicate (2*width r+1) false) last),hj,?_,?_⟩
  · change Composition.rightConfig 5 (TapeEmbedding.config _ _ last.final)=_
    rw [hlf,output_eq]
    rfl
  · change firstRun.steps+1+last.steps ≤ _
    dsimp only [fuel,width] at hfs ⊢
    omega

end NearCubicWires.RepairOrdinary.MatrixRightScan
