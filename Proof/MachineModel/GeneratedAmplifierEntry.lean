import Proof.MachineModel.GeneratedAmplifierPrepared
import Proof.MachineModel.GeneratedAmplifierBackward
import Proof.PCP.PCPPQueryInput

/-! Actual external input to raw lookup entry. The address boundary is found
by paid backward motion from the retained complete-input cursor; table bits
are never treated as delimiters. The two scalar flags are physically written. -/
namespace NearCubicWires.RepairOrdinary.GeneratedAmplifier.Entry
open LocalBitMultitape RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def backSlots : Fin 2→Fin 18 := ![1,12]
def querySlots : Fin 3→Fin 18 := ![1,13,14]
noncomputable def prepare := TapeEmbedding.machine 5 Prepared.machine
noncomputable def back := RecoveryFocus.machine backSlots Backward.machine
noncomputable def first := Composition.machine prepare back
noncomputable def query := RecoveryFocus.machine querySlots PCPPQueryInput.isolate
noncomputable def second := Composition.machine first query
def boot : Machine 18 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun q _ => if q.val=0 then some ⟨1,
    fun i => if i=15 ∨ i=17 then some false else none,fun _ => .stay⟩ else none
noncomputable def machine := Composition.machine second boot
def input (word : List Bool) : Fin 18→List Bool := fun i => if i=0 then frame word else []
def budget (n : ℕ) (table address : List Bool) := Prepared.budget n (table++frame address)+7*n+13
def bootOutput (heads : Fin 18→ℕ) (tapes : Fin 18→List Bool) : Configuration 18 2 :=
  ⟨1,heads,fun i => if i=15 ∨ i=17 then [false] else tapes i⟩

theorem boot_run (heads : Fin 18→ℕ) (tapes : Fin 18→List Bool)
    (h15 : heads 15=0) (h17 : heads 17=0) (t15 : tapes 15=[]) (t17 : tapes 17=[]) :
    ∃ r,runFrom boot 1 ⟨0,heads,tapes⟩=some r ∧ r.final=bootOutput heads tapes ∧ r.steps=1 := by
  have hs : step boot ⟨0,heads,tapes⟩=some (bootOutput heads tapes) := by
    simp [step,boot,bootOutput]
    apply configuration_ext
    · rfl
    · funext i; simp [applyAction,HeadMove.apply]
    · funext i
      by_cases h : i=15 ∨ i=17
      · rcases h with h|h <;> subst i <;> simp [applyAction,h15,h17,t15,t17,writeTapeBit]
      · simp [applyAction,h]
  exact (Timed.single (by rfl) hs).run (by rfl)

structure Ready {s : ℕ} (c : Configuration 18 s) (n : ℕ) (table address : List Bool) : Prop where
  source : c.tapes 3=frame n.bits++table++frame address
  sourceHead : c.heads 3=2*n.bits.length+1
  query : c.tapes 13=frame address
  queryHead : c.heads 13=0
  flag : c.tapes 15=[false]
  flagHead : c.heads 15=0
  scratch : c.tapes 16=[]
  scratchHead : c.heads 16=0
  output : c.tapes 17=[false]
  outputHead : c.heads 17=0

theorem entry_run (n : ℕ) (table address : List Bool) (ha : address.length=n) :
    let word := frame n.bits++table++frame address
    ∃ r,run machine (budget n table address) (input word)=some r ∧
      r.steps≤budget n table address ∧ Ready r.final n table address := by
  dsimp only
  let word := frame n.bits++table++frame address
  let pre := frame n.bits++table
  obtain ⟨base,hb,hbs,hend,hendHead,hsource,hsourceHead,hcount,hcountHead⟩ :=
    Prepared.prepared_run n (table++frame address)
  have hword : frame n.bits++(table++frame address)=word := by simp [word,List.append_assoc]
  rw [hword] at hb hend hendHead hsource
  have he := TapeEmbedding.run_embed Prepared.machine (fun _ : Fin 5 => 0) (fun _ : Fin 5 => []) _ _ base hb
  let ambient := TapeEmbedding.config (fun _ : Fin 5 => 0) (fun _ : Fin 5 => []) base.final
  obtain ⟨br,hbr,hbrf,hbrs⟩ := Backward.backward_run word n pre.length
  obtain ⟨bf,hbf,hbff,hbfs⟩ := RecoveryFocus.run_config backSlots (by decide) Backward.machine
    ambient.heads ambient.tapes _ _ br hbr
  have bl : word.length=pre.length+2*n+1 := by simp [word,pre,ha]; omega
  have bhi : RecoveryFocus.config backSlots ambient.heads ambient.tapes
      (Backward.cfg 0 word n (pre.length+2*n+1) 1)=Composition.restart ambient back.start := by
    apply WilliamsSourceCrop.focus_same
    · intro i; fin_cases i
      · change base.final.heads 1=pre.length+2*n+1
        rw [hendHead,bl]
      · exact hcountHead
    · intro i; fin_cases i
      · exact hend
      · exact hcount
  rw [bhi] at hbf
  have hfirst := Composition.run_join prepare back _ _ _
    (TapeEmbedding.receipt (fun _ : Fin 5 => 0) (fun _ : Fin 5 => []) base) bf he hbf
  let firstRun := Composition.joinedReceipt
    (TapeEmbedding.receipt (fun _ : Fin 5 => 0) (fun _ : Fin 5 => []) base) bf
  have hbother (i : Fin 18) (hi : RecoveryFocus.pick backSlots i=none) :
      firstRun.final.tapes i=ambient.tapes i ∧ firstRun.final.heads i=ambient.heads i := by
    simp [firstRun,Composition.joinedReceipt,Composition.rightConfig,hbff,RecoveryFocus.config,hi]
  obtain ⟨qr,hqr,hqrf,hqrs⟩ := PCPPQueryInput.isolate_run pre address []
  simp only [List.append_nil] at hqr hqrf
  obtain ⟨qf,hqf,hqff,hqfs⟩ := RecoveryFocus.run_config querySlots (by decide) PCPPQueryInput.isolate
    firstRun.final.heads firstRun.final.tapes _ _ qr hqr
  have qhi : RecoveryFocus.config querySlots firstRun.final.heads firstRun.final.tapes
      (PCPPQueryInput.entry word pre.length)=Composition.restart firstRun.final query.start := by
    apply WilliamsSourceCrop.focus_same
    · intro i; fin_cases i
      · change bf.final.heads (backSlots 0)=pre.length
        simp only [hbff,RecoveryFocus.config,RecoveryFocus.pick_slot backSlots (by decide)]
        rw [hbrf]
        rfl
      · change firstRun.final.heads 13=0
        rw [(hbother 13 (by decide)).2]
        rfl
      · change firstRun.final.heads 14=0
        rw [(hbother 14 (by decide)).2]
        rfl
    · intro i; fin_cases i
      · change bf.final.tapes (backSlots 0)=word
        simp only [hbff,RecoveryFocus.config,RecoveryFocus.pick_slot backSlots (by decide)]
        rw [hbrf]
        rfl
      · change firstRun.final.tapes 13=[]
        rw [(hbother 13 (by decide)).1]
        rfl
      · change firstRun.final.tapes 14=[]
        rw [(hbother 14 (by decide)).1]
        rfl
  rw [qhi] at hqf
  have hsecond := Composition.run_join first query _ _ _ firstRun qf hfirst hqf
  let secondRun := Composition.joinedReceipt firstRun qf
  have hqother (i : Fin 18) (hi : RecoveryFocus.pick querySlots i=none) :
      secondRun.final.tapes i=firstRun.final.tapes i ∧ secondRun.final.heads i=firstRun.final.heads i := by
    simp [secondRun,Composition.joinedReceipt,Composition.rightConfig,hqff,RecoveryFocus.config,hi]
  have fresh (i : Fin 18) (hb : RecoveryFocus.pick backSlots i=none)
      (hq : RecoveryFocus.pick querySlots i=none) (hi : 13 ≤ i.val) :
      secondRun.final.tapes i=[] ∧ secondRun.final.heads i=0 := by
    rw [(hqother i hq).1,(hqother i hq).2,(hbother i hb).1,(hbother i hb).2]
    simp [ambient,TapeEmbedding.config,Fin.addCases,Nat.not_lt.mpr hi]
  have f15 := fresh 15 (by decide) (by decide) (by decide)
  have f16 := fresh 16 (by decide) (by decide) (by decide)
  have f17 := fresh 17 (by decide) (by decide) (by decide)
  obtain ⟨last,hl,hlf,hls⟩ := boot_run secondRun.final.heads secondRun.final.tapes f15.2 f17.2 f15.1 f17.1
  have hall := Composition.run_join second boot _ _ _ secondRun last hsecond hl
  have htime : ((Prepared.budget n (table++frame address)+1+(3*n+5))+1+(4*address.length+4))+1+1=
      budget n table address := by unfold budget; omega
  rw [htime] at hall
  have hcold : Composition.leftConfig 2 (Composition.leftConfig 5 (Composition.leftConfig 7
      (TapeEmbedding.config (fun _ : Fin 5 => 0) (fun _ : Fin 5 => [])
        (initialConfiguration Prepared.machine (Prepared.input word)))))=
      initialConfiguration machine (input word) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [hcold] at hall
  have hs3 : secondRun.final.tapes 3=word ∧ secondRun.final.heads 3=2*n.bits.length+1 := by
    rw [(hqother 3 (by decide)).1,(hqother 3 (by decide)).2,(hbother 3 (by decide)).1,(hbother 3 (by decide)).2]
    exact ⟨hsource,hsourceHead⟩
  have hq13 : secondRun.final.tapes 13=frame address ∧ secondRun.final.heads 13=0 := by
    change qf.final.tapes (querySlots 1)=_ ∧ qf.final.heads (querySlots 1)=_
    simp only [hqff,RecoveryFocus.config,RecoveryFocus.pick_slot querySlots (by decide)]
    rw [hqrf]
    exact ⟨rfl,rfl⟩
  refine ⟨Composition.joinedReceipt secondRun last,hall,?_,?_⟩
  · change base.steps+1+bf.steps+1+qf.steps+1+last.steps≤_
    rw [hbfs,hbrs,hqfs,hqrs,hls]
    unfold budget
    omega
  · change Ready (Composition.rightConfig _ last.final) n table address
    rw [hlf]
    exact ⟨hs3.1,hs3.2,hq13.1,hq13.2,rfl,f15.2,f16.1,f16.2,rfl,f17.2⟩

end NearCubicWires.RepairOrdinary.GeneratedAmplifier.Entry
