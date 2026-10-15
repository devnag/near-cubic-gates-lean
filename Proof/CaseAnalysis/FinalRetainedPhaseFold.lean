import Proof.CaseAnalysis.FinalWordsStage
import Proof.CaseAnalysis.FinalWorkerLoaderPorts
import Proof.CaseAnalysis.FinalStageSeam
import Proof.CaseAnalysis.FinalTailComposeUniform
import Proof.Amplification.RecoveryFocusRetained

/-!
The selected C10 phase consumer: prepare dimensions from the actual completed
stream, fold and emit its estimate, then rewind the same physical run. Fixed
per-phase fresh consumer banks retain one common cold/cache/pool. The two width
outputs and result word are written directly at their final tail ports.

Every source input, stream/count identity, validity premise and exact empty
consumer cell remains explicit. The theorem preserves ambient heads and all
other tapes; in particular the loop counter is outside this focused consumer.
The fuel is exactly the existing words budget, one composition bridge, and the
existing Rewind bound for the existing docked fold. No source/capacity/schedule
or whole-worker Runtime theorem is asserted here.
-/
namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10RetainedPhaseFold
open NearCubicWires.LocalBitMultitape NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairSource.CloseoutFinal
open RecoveryRootRound
open NearCubicWires.RepairSource.VerifierDecoding
open CloseoutFinalC10WorkerWidth CloseoutFinalC10WorkerFold
open CloseoutRowsOriginalSchedule
open CloseoutRowsEstimatorCoefficients.Stream
open CloseoutFinalC10WorkerDock CloseoutFinalC10WorkerEmitShape CloseoutFinalC10WorkerDockBody
open CloseoutFinalC10WorkerLoaderPorts CloseoutFinalC10WorkerEmitLoader
open CloseoutFinalC10WordsStage
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tailSlots (L B : Nat) (hL : 301 ≤ L) (hFresh : L+1154 < B) : Fin 475 → Fin B := fun i =>
  ⟨if i.val = 473 then 217 else L+124+i.val, by
    have := i.isLt
    split_ifs <;> omega⟩
def phaseBank (L B : Nat) (hL : 301 ≤ L) (hFresh : L+1154 < B) : NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule.Phase → Fin 278 → Fin B := fun ph i =>
    let index := (NearCubicWires.RepairSource.CloseoutFinal.C10TailUniformSlots.phaseIndex ph).val
    if i.val = 0 ∨ i.val = 1 ∨ i.val = 216 ∨ i.val = 217 ∨ index = 0 then
      ⟨i.val, by have := i.isLt; omega⟩
    else
      ⟨L+599+(index-1)*278+i.val, by
        have hi := i.isLt
        have hp := (NearCubicWires.RepairSource.CloseoutFinal.C10TailUniformSlots.phaseIndex ph).isLt
        dsimp only [index] at *
        omega⟩

def wordSlots (L B : Nat) (hL : 301 ≤ L) (hFresh : L+1154 < B) : NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule.Phase → Fin 278 → Fin B := fun ph i =>
  if i.val = 274 then tailSlots L B hL hFresh (NearCubicWires.RepairSource.CloseoutFinal.C10TailSlotsUniform.widthSlotT ph 0)
  else if i.val = 275 then tailSlots L B hL hFresh (NearCubicWires.RepairSource.CloseoutFinal.C10TailSlotsUniform.widthSlotT ph 1)
  else phaseBank L B hL hFresh ph i
def foldSlots (L B : Nat) (hL : 301 ≤ L) (hFresh : L+1154 < B) : NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule.Phase → Fin 219 → Fin B := fun ph i =>
  if i.val = 215 then tailSlots L B hL hFresh (NearCubicWires.RepairSource.CloseoutFinal.C10TailVerdict.scratchT ph)
  else if i.val = 218 then
    tailSlots L B hL hFresh ⟨8+(NearCubicWires.RepairSource.CloseoutFinal.C10TailUniformSlots.phaseIndex ph).val, by
      have := (NearCubicWires.RepairSource.CloseoutFinal.C10TailUniformSlots.phaseIndex ph).isLt
      omega⟩
  else phaseBank L B hL hFresh ph ⟨i.val, by have := i.isLt; omega⟩
private theorem overrides_injective {B n : Nat} (f : Fin n → Fin B)
    (hf : Function.Injective f) (p q : Nat) (a b : Fin B) (hab : a≠b)
    (ha : ∀ i,f i≠a) (hb : ∀ i,f i≠b) :
    Function.Injective (fun i : Fin n => if i.val=p then a else if i.val=q then b else f i) := by
  intro i j h
  dsimp only at h
  split_ifs at h <;> first
    | exact Fin.ext (by omega)
    | exact False.elim (hab h)
    | exact False.elim (hab h.symm)
    | exact False.elim (ha i h)
    | exact False.elim (ha j h.symm)
    | exact False.elim (hb i h)
    | exact False.elim (hb j h.symm)
    | exact hf h

private theorem bank_injective (L B : Nat) (hL : 301≤L) (hFresh : L+1154<B) (ph : Phase) :
    Function.Injective (phaseBank L B hL hFresh ph) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  have hi := i.isLt
  have hj := j.isLt
  simp only [phaseBank,apply_ite] at hv
  split_ifs at hv <;> omega

private theorem bank_range (L B : Nat) (hL : 301≤L) (hFresh : L+1154<B) (ph : Phase) (i : Fin 278) :
    (phaseBank L B hL hFresh ph i).val ≤277 ∨ L+599≤(phaseBank L B hL hFresh ph i).val := by
  have hi:=i.isLt
  simp only [phaseBank,apply_ite]
  split_ifs <;> omega

theorem maps_injective (L B : Nat) (hL : 301≤L) (hFresh : L+1154<B) (ph : Phase) :
    Function.Injective (wordSlots L B hL hFresh ph) ∧
    Function.Injective (foldSlots L B hL hFresh ph) := by
  have outside (i : Fin 278) (j : Fin 475) (hj : 2≤j.val ∧ j.val≤220) :
      phaseBank L B hL hFresh ph i ≠ tailSlots L B hL hFresh j := by
    intro he
    have hv := congrArg Fin.val he
    have hb:=bank_range L B hL hFresh ph i
    simp only [tailSlots,Fin.val_mk,if_neg (show j.val≠473 by omega)] at hv
    omega
  constructor
  · apply overrides_injective _ (bank_injective L B hL hFresh ph)
    · intro he
      have hv:=congrArg Fin.val he
      cases ph <;> norm_num [tailSlots,C10TailSlotsUniform.widthSlotT,C10TailSlotsUniform.prefixSlot,C10TailUniformSlots.widthSlot,C10TailUniformSlots.phaseIndex] at hv
    · intro i
      apply outside
      cases ph <;> norm_num [C10TailUniformSlots.phaseIndex,C10TailVerdict.scratchT,C10TailSlotsUniform.widthSlotT,C10TailSlotsUniform.prefixSlot,C10TailUniformSlots.widthSlot]
    · intro i
      apply outside
      cases ph <;> norm_num [C10TailUniformSlots.phaseIndex,C10TailVerdict.scratchT,C10TailSlotsUniform.widthSlotT,C10TailSlotsUniform.prefixSlot,C10TailUniformSlots.widthSlot]
  · apply overrides_injective (fun i : Fin 219=>phaseBank L B hL hFresh ph ⟨i.val,by have:=i.isLt;omega⟩)
      (fun i j h => Fin.ext (congrArg (@Fin.val 278) (bank_injective L B hL hFresh ph h)))
    · intro he
      have hv:=congrArg Fin.val he
      cases ph <;> norm_num [tailSlots,C10TailVerdict.scratchT,C10TailUniformSlots.phaseIndex] at hv
    · intro i
      apply outside
      cases ph <;> norm_num [C10TailUniformSlots.phaseIndex,C10TailVerdict.scratchT,C10TailSlotsUniform.widthSlotT,C10TailSlotsUniform.prefixSlot,C10TailUniformSlots.widthSlot]
    · intro i
      apply outside
      cases ph <;> norm_num [C10TailUniformSlots.phaseIndex,C10TailVerdict.scratchT,C10TailSlotsUniform.widthSlotT,C10TailSlotsUniform.prefixSlot,C10TailUniformSlots.widthSlot]
theorem fold_protected (n : Nat) (hin hout : Fin 218 → Nat) (tin tout : Fin 218 → List Bool)
    (i : Fin 218) (hi : i=0 ∨ i=1 ∨ i=216 ∨ i=217)
    (hrun : Step (CloseoutFinalC10StageSeam.dockedBody emitLoader) n hin tin hout tout) :
    tout i = tin i :=
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary in
by
  classical
  let Preserves := fun {t s : Nat} (p : Machine t s) (i : Fin t) =>
    ∀ state scanned action, p.rule state scanned = some action → action.write i = none
  have focused {t u s : Nat} (slots : Fin t → Fin u) (p : Machine t s)
      (i : Fin u) (hi : ∀ j, slots j ≠ i) : Preserves (RecoveryFocus.machine slots p) i := by
    have pick : RecoveryFocus.pick slots i = none := by
      simp [RecoveryFocus.pick,show ¬∃ j,slots j=i by simpa using hi]
    intro state scanned action hr
    change (p.rule state (scanned ∘ slots)).map (RecoveryFocus.action slots) = some action at hr
    obtain ⟨a,ha,rfl⟩ := Option.map_eq_some_iff.mp hr
    simp [RecoveryFocus.action,pick]
  have composed {t a b : Nat} (p : Machine t a) (q : Machine t b)
      (i : Fin t) (hp : Preserves p i) (hq : Preserves q i) :
      Preserves (Composition.machine p q) i := by
    intro state
    refine Fin.addCases ?_ ?_ state
    · intro state scanned action hr
      simp only [Composition.machine, Fin.addCases_left] at hr
      change (if p.halted state then some (Composition.bridge q.start)
        else (p.rule state scanned).map (Composition.leftAction b)) = some action at hr
      split_ifs at hr
      · cases hr
        rfl
      · obtain ⟨a,ha,rfl⟩ := Option.map_eq_some_iff.mp hr
        exact hp state scanned a ha
    · intro state scanned action hr
      simp only [Composition.machine, Fin.addCases_right] at hr
      change (q.rule state scanned).map (Composition.rightAction a) = some action at hr
      obtain ⟨a,ha,rfl⟩ := Option.map_eq_some_iff.mp hr
      exact hq state scanned a ha
  have actual : Preserves (NearCubicWires.RepairOrdinary.CloseoutFinalC10StageSeam.dockedBody
      NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerEmitLoader.emitLoader) i := by
    apply composed
    · apply composed
      · apply focused
        rcases hi with rfl | rfl | rfl | rfl <;> decide
      · apply focused
        rcases hi with rfl | rfl | rfl | rfl <;> decide
    · apply composed
      · apply composed
        · apply composed
          · apply focused
            rcases hi with rfl | rfl | rfl | rfl <;> decide
          · apply focused
            rcases hi with rfl | rfl | rfl | rfl <;> decide
        · apply focused
          rcases hi with rfl | rfl | rfl | rfl <;> decide
      · apply focused
        rcases hi with rfl | rfl | rfl | rfl <;> decide
  have eachStep {t s : Nat} (p : Machine t s) (j : Fin t) (h : Preserves p j)
      (c d : Configuration t s) (hs : step p c = some d) : d.tapes j = c.tapes j := by
    change (p.rule c.control c.scanned).map (applyAction c) = some d at hs
    obtain ⟨a,ha,rfl⟩ := Option.map_eq_some_iff.mp hs
    simp [applyAction,h c.control c.scanned a ha]
  have eachPrefix {t s space count : Nat} (p : Machine t s) (j : Fin t) (h : Preserves p j)
      {c d : Configuration t s} (hp : Prefix p space count c d) : d.tapes j=c.tapes j := by
    induction hp with
    | refl => rfl
    | step hc hn hs tail ih => exact ih.trans (eachStep p j h _ _ hs)
  obtain ⟨r,hr,_hh,ht,_hs⟩ := hrun
  obtain ⟨hp,_hhalt⟩ := prefix_of_run _ _ _ _ hr
  rw [← ht]
  exact eachPrefix _ i actual hp

noncomputable def machine (L B : Nat) (hL : 301 ≤ L) (hFresh : L+1154<B) (ph : Phase) :=
  Composition.machine (RecoveryFocus.machine (wordSlots L B hL hFresh ph) wordsMachine)
    (RecoveryFocus.machine (foldSlots L B hL hFresh ph)
      (Rewind.machine (CloseoutFinalC10StageSeam.dockedBody emitLoader)))

def fuel (b count : Nat) := wordsFuel b count + 1 +
  (2*CloseoutFinalC10StageSeam.dockedFuel (fun _ => emitFuel (joinScalarWidth b count)) b count 0+2)

/-- A phase folds the actual retained stream after physically preparing its
  dimensions. No later count, record, empty scratch or tape frame is assumed. -/
theorem run (L B : Nat) (hL : 301 ≤ L) (hFresh : L+1154<B) (ph : Phase)
    (b : Nat) (entries : List Entry) (H : Fin B → Nat) (A : Fin B → List Bool)
    (hvalid : ∀ entry∈entries,Entry.Valid b entry)
    (hHw : ∀ i,H (wordSlots L B hL hFresh ph i)=0)
    (hHf : ∀ i,H (foldSlots L B hL hFresh ph i)=0)
    (hdriver : A (wordSlots L B hL hFresh ph 218)=List.replicate b true)
    (hcount : A (wordSlots L B hL hFresh ph 90)=CompareMachine.word entries.length)
    (hstream : A (wordSlots L B hL hFresh ph 81)=words b entries)
    (hblank : ∀ i : Fin 278, 2 ≤ i.val → i.val < 215 → i.val ≠ 81 → i.val ≠ 90 →
      A (wordSlots L B hL hFresh ph i)=[])
    (hfresh : ∀ i : Fin 278, 219 ≤ i.val → A (wordSlots L B hL hFresh ph i)=[])
    (hrecord : A (foldSlots L B hL hFresh ph 215)=[])
    (hlog : A (foldSlots L B hL hFresh ph 218)=[]) :
    ∃ out : Fin B → List Bool,
      Step (machine L B hL hFresh ph) (fuel b entries.length) H A H out ∧
      out (foldSlots L B hL hFresh ph 215)=recordWord
        (foldWidth (CompetitorRationalDecision.width b) entries)
        (CompetitorSumFold.folded CompetitorSumWidth.zero (contributions entries)) 1 1 ∧
      out (wordSlots L B hL hFresh ph 274)=List.replicate (joinScalarWidth b entries.length) true ∧
      out (wordSlots L B hL hFresh ph 275)=List.replicate
        (CompetitorRationalDecision.width (joinScalarWidth b entries.length)) true ∧
      (∀ i : Fin 218,i=0 ∨ i=1 ∨ i=216 ∨ i=217 →
        out (foldSlots L B hL hFresh ph (i.castAdd 1))=A (foldSlots L B hL hFresh ph (i.castAdd 1))) ∧
      (∀ i : Fin B,(∀ j,wordSlots L B hL hFresh ph j ≠ i) →
        (∀ j,foldSlots L B hL hFresh ph j ≠ i) → out i=A i) := by
  classical
  let w:=wordSlots L B hL hFresh ph
  let f:=foldSlots L B hL hFresh ph
  obtain ⟨hw,hf⟩:=maps_injective L B hL hFresh ph
  have align (i : Fin 218) (hi : i.val ≠ 215) :
      f (i.castAdd 1)=w ⟨i.val,by have:=i.isLt;omega⟩ := by
    simp [f,w,foldSlots,wordSlots,hi,show i.val ≠ 218 by have:=i.isLt;omega,
      show i.val ≠ 274 by have:=i.isLt;omega,show i.val ≠ 275 by have:=i.isLt;omega]
  have wrange (i : Fin 278) :
      (w i).val ≤ 277 ∨ L+599 ≤ (w i).val ∨ (L+126 ≤ (w i).val ∧ (w i).val ≤ L+131) := by
    have hb:=bank_range L B hL hFresh ph i
    dsimp only [w,wordSlots]
    split_ifs
    · cases ph <;> norm_num [tailSlots,C10TailSlotsUniform.widthSlotT,C10TailSlotsUniform.prefixSlot,C10TailUniformSlots.widthSlot,C10TailUniformSlots.phaseIndex]
    · cases ph <;> norm_num [tailSlots,C10TailSlotsUniform.widthSlotT,C10TailSlotsUniform.prefixSlot,C10TailUniformSlots.widthSlot,C10TailUniformSlots.phaseIndex]
    · exact hb.elim Or.inl (fun h=>Or.inr (Or.inl h))
  have separate (i : Fin 219) (hi : i.val=215 ∨ i.val=218) : ∀ j,w j ≠ f i := by
    intro j he
    have hr:=wrange j
    have hv:=congrArg Fin.val he
    rcases hi with hi|hi
    all_goals
      have ieq : i=⟨i.val,i.isLt⟩:=rfl
      cases ph <;> simp [f,foldSlots,hi,tailSlots,C10TailVerdict.scratchT,C10TailUniformSlots.phaseIndex] at hv <;> omega
  have frange (i : Fin 219) :
      (f i).val ≤ 277 ∨ L+599 ≤ (f i).val ∨
      (L+132 ≤ (f i).val ∧ (f i).val ≤ L+134) ∨ (L+342 ≤ (f i).val ∧ (f i).val ≤ L+344) := by
    have hb:=bank_range L B hL hFresh ph ⟨i.val,by have:=i.isLt;omega⟩
    dsimp only [f,foldSlots]
    split_ifs
    · cases ph <;> norm_num [tailSlots,C10TailVerdict.scratchT,C10TailUniformSlots.phaseIndex]
    · cases ph <;> norm_num [tailSlots,C10TailUniformSlots.phaseIndex]
    · exact hb.elim Or.inl (fun h=>Or.inr (Or.inl h))
  have widthSeparate (j : Fin 278) (hj : j.val=274 ∨ j.val=275) : ∀ i,f i ≠ w j := by
    have bound : L+126 ≤ (w j).val ∧ (w j).val ≤ L+131 := by
      rcases hj with hj|hj
      · have he : j=274:=Fin.ext hj
        subst j
        cases ph <;> norm_num [w,wordSlots,tailSlots,C10TailSlotsUniform.widthSlotT,C10TailSlotsUniform.prefixSlot,C10TailUniformSlots.widthSlot,C10TailUniformSlots.phaseIndex]
      · have he : j=275:=Fin.ext hj
        subst j
        cases ph <;> norm_num [w,wordSlots,tailSlots,C10TailSlotsUniform.widthSlotT,C10TailSlotsUniform.prefixSlot,C10TailUniformSlots.widthSlot,C10TailUniformSlots.phaseIndex]
    intro i he
    have hv:=congrArg Fin.val he
    have hb:=frange i
    omega
  obtain ⟨WH,WA,ws,hWH,h83,h84,h85,h86,h90,h98,h176,h182,h186,h187,h213,h214,h274,h275,frame⟩ :=
    words_step b entries.length (H ∘ w) (A ∘ w) hHw hdriver hcount
      (by intro i hi;apply hblank i <;> simp only [Finset.mem_insert,Finset.mem_singleton] at hi <;> omega)
      hfresh
  let T:=install w A WA
  have stepWords : Step (RecoveryFocus.machine w wordsMachine) (wordsFuel b entries.length) H A H T :=
    (ws.dock w hw H A (by intro i;rfl) (by intro i;rfl)).congr
      (dockH_existing w H WH (fun i=>(hHw i).trans (hWH i).symm)) rfl
  let bank : Fin 218 → List Bool:=fun i=>T (f (i.castAdd 1))
  have get (i : Fin 218) (hi : i.val ≠ 215) :
      bank i=WA ⟨i.val,by have:=i.isLt;omega⟩ := by
    dsimp only [bank,T]
    rw [align i hi,install_slot w hw]
  have blank (i : Fin 218) (h2 : 2 ≤ i.val) (hlt : i.val < 215)
      (h81 : i.val ≠ 81) (h90 : i.val ≠ 90)
      (hp : i.val∉({83,84,85,86,90,98,176,182,186,187, 213, 214, 218}:Finset Nat)) : bank i=[] :=
    (get i (by omega)).trans ((frame ⟨i.val,by omega⟩ hp (by change i.val < 219;omega)).trans (hblank _ h2 hlt h81 h90))
  have recordBlank : bank 215=[] :=
    (install_other w A WA (f 215) (separate 215 (Or.inl rfl))).trans hrecord
  have ready : DockReady b entries bank :=
    dockReady_of_ports b entries bank
      ((get 81 (by decide)).trans ((frame 81 (by decide) (by decide)).trans hstream))
      ((get 83 (by decide)).trans h83) ((get 84 (by decide)).trans h84)
      ((get 85 (by decide)).trans h85) ((get 86 (by decide)).trans h86)
      ((get 90 (by decide)).trans h90) ((get 98 (by decide)).trans (h98.trans h84))
      ((get 176 (by decide)).trans (h176.trans h85)) ((get 182 (by decide)).trans (h182.trans h86))
      ((get 186 (by decide)).trans h186)
      (by intro i h2 hi h81 h83 h84 h85 h86 h90 h98 h176 h182 h186
          apply blank i h2 (by omega) h81 h90
          simp only [Finset.mem_insert,Finset.mem_singleton,not_or]
          omega)
  have entry : EmitEntry (joinScalarWidth b entries.length) bank :=
    emitEntry_of_ports _ bank ((get 187 (by decide)).trans h187)
      ((get 213 (by decide)).trans h213) ((get 214 (by decide)).trans (h214.trans h213))
      (by intro i hlo hhi h213 h214
          by_cases hi : i.val=215
          · have he : i=215:=Fin.ext hi
            subst i
            exact recordBlank
          · apply blank i (by omega) (by omega) (by omega) (by omega)
            simp only [Finset.mem_insert,Finset.mem_singleton,not_or]
            omega)
  obtain ⟨DH,DA,ds,record⟩:=CloseoutFinalC10StageSeam.docked_run b entries hvalid bank ready entry 0
  obtain ⟨log,rs⟩:=C10TailCompose.step_reset ds
  let out:=install f T (Fin.addCases (motive := fun _ => List Bool) DA (fun _ : Fin 1=>log))
  have stepFold : Step (RecoveryFocus.machine f (Rewind.machine (CloseoutFinalC10StageSeam.dockedBody emitLoader)))
      (2*CloseoutFinalC10StageSeam.dockedFuel (fun _=>emitFuel (joinScalarWidth b entries.length)) b entries.length 0+2)
      H T H out := by
    apply (rs.dock f hf H T hHf ?_).congr (dockH_existing f H (fun _=>0) hHf) rfl
    intro i
    refine Fin.addCases (m:=218) (n:=1) ?_ ?_ i
    · intro i
      rw [Fin.addCases_left]
    · intro i
      have hi : i=0:=Fin.eq_zero i
      subst i
      rw [Fin.addCases_right]
      exact (install_other w A WA (f 218) (separate 218 (Or.inr rfl))).trans hlog
  refine ⟨out,stepWords.seq stepFold,?_,?_,?_,?_,?_⟩
  · exact (install_slot f hf T _ (215 : Fin 219)).trans record
  · exact (install_other f T _ (w 274) (widthSeparate 274 (Or.inl rfl))).trans
      ((install_slot w hw A WA 274).trans (h274.trans h85))
  · exact (install_other f T _ (w 275) (widthSeparate 275 (Or.inr rfl))).trans
      ((install_slot w hw A WA 275).trans (h275.trans h84))
  · intro i hi
    have hip : i.val ≠ 215:=by rcases hi with rfl|rfl|rfl|rfl <;> decide
    have hp:=fold_protected _ _ _ _ _ i hi ds
    change install f T _ (f (i.castAdd 1))=_
    rw [install_slot f hf]
    simp only [Fin.addCases_left]
    rw [hp,get i hip]
    exact (frame ⟨i.val,by have:=i.isLt;omega⟩ (by rcases hi with rfl|rfl|rfl|rfl <;> norm_num)
      (by change i.val < 219;have:=i.isLt;omega)).trans (congrArg A (align i hip).symm)
  · intro i hwout hfout
    exact (install_other f T _ i hfout).trans (install_other w A WA i hwout)

end NearCubicWires.RepairOrdinary.CloseoutFinalC10RetainedPhaseFold
