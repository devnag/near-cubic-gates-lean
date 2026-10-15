import Proof.MachineModel.OccurrenceRun
import Proof.PCP.PCPPQueryNatural
import Proof.MachineModel.FrameSkip
import Proof.Hierarchy.HierarchyFixedWord
import Proof.MachineModel.FinalState
import Proof.MachineModel.SourceEnvelope

/-! Run the existing occurrence loop on the actual produced unary
template. Only the already produced driver gains its trailing false cell. -/
namespace NearCubicWires.ExtDecompositionBatch.OccurrenceTemplate
open LocalBitMultitape RepairOrdinary RepairRepresentation ExecutableInterfaces SupplierPipeline
open RepairOrdinary.CloseoutRowsCircuitBottom RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
variable (a : DecompositionAlgorithm)

def heads (pos : ℕ) (c1 c2 c3 : List Bool) (driver : ℕ) : Fin (CT a+1) → ℕ :=
  Fin.addCases (loopInH a pos c1 c2 c3) (fun _ => driver)
def tapes (C q : ℕ) (source c1 c2 c3 : List Bool) (count : ℕ) : Fin (CT a+1) → List Bool :=
  Fin.addCases (loopInA a C q source c1 c2 c3) (fun _ => UnaryTemplate.tape count)
def capacities (count : ℕ) : Fin (CT a+1) → ℕ :=
  Fin.addCases (fun _ : Fin (CT a) => 0) (fun _ => count+2)
noncomputable def cfg (phase : Fin 5) (C q pos : ℕ) (source c1 c2 c3 : List Bool) (count driver : ℕ) :=
  (⟨(loopCfg a phase C q pos source c1 c2 c3 count driver).control,
    heads a pos c1 c2 c3 driver,tapes a C q source c1 c2 c3 count⟩ :
      Configuration (CT a+1) _)

theorem padded_cfg (phase : Fin 5) (C q pos : ℕ) (source c1 c2 c3 : List Bool) (count driver : ℕ) :
    ZeroPadding.config (capacities a count) (loopCfg a phase C q pos source c1 c2 c3 count driver) =
      cfg a phase C q pos source c1 c2 c3 count driver := by
  apply configuration_ext
  · rfl
  · rfl
  · funext i
    refine Fin.addCases (m:=CT a) (n:=1) (fun j => ?_) (fun j => ?_) i
    · simp only [ZeroPadding.config,capacities,loopCfg,RepeatMachine.cfg,controlConfig,
        TapeEmbedding.config,loopStore,cfg,tapes,Fin.addCases_left,ZeroPadding.pad_zero]
    · simp only [ZeroPadding.config,capacities,loopCfg,RepeatMachine.cfg,controlConfig,
        TapeEmbedding.config,loopStore,cfg,tapes,Fin.addCases_right]
      rw [pad_template (count+2) count (Nat.le_refl _)]
      simp [ZeroPadding.pad,UnaryTemplate.tape]

theorem run (C q : ℕ) (occ : List (SupportedNormalizedGate q))
    (pre rest c1 c2 c3 : List Bool) (hC : ∀ g∈occ,bodyCost a q g<C) :
    ∃ r,runFrom (occurrenceLoop a) (loopCost a C occ)
      (cfg a 0 C q pre.length (pre++requestStream occ++rest) c1 c2 c3 occ.length 1)=some r ∧
      r.final=cfg a 3 C q (pre.length+(requestStream occ).length) (pre++requestStream occ++rest)
        (c1++(counts a occ).flatMap natWord) (c2++(GS a occ).flatMap exactWord)
        (c3++List.replicate (B a occ) true) occ.length 1 ∧ r.steps≤loopCost a C occ := by
  obtain ⟨r,hr,hf,hs⟩ := occurrence_run a C q occ pre rest c1 c2 c3 hC
  obtain ⟨p,hp,pf,ps,_⟩ := ZeroPadding.run_config (occurrenceLoop a) (capacities a occ.length) _ _ r hr
  rw [padded_cfg] at hp
  refine ⟨p,hp,?_,ps.le.trans hs⟩
  rw [pf,hf,padded_cfg]

end NearCubicWires.ExtDecompositionBatch.OccurrenceTemplate

/-! Parse the actual occurrence header in the existing natural reader.
Only its nine private tapes have C backing; source and produced template are exact. -/
namespace NearCubicWires.ExtDecompositionBatch.PreludeNatural
open LocalBitMultitape RepairOrdinary RepairRepresentation
open RepairOrdinary.RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def caps (C : ℕ) (i : Fin 11) := if i=0 ∨ i=10 then 0 else C
def input (C : ℕ) (source : List Bool) (i : Fin 11) : List Bool :=
  if i=0 then source else if i=10 then [] else List.replicate C false
def heads (n : ℕ) (i : Fin 11) := if i=0 then (natWord n).length else if i=10 then 1 else 0
def selected (i : Fin 11) : Bool := decide (i≠0 ∧ i≠10)
noncomputable def machine := MaskedReset.machine PCPPQueryNatural.machine selected

theorem padded_run (C n : ℕ) (tail : List Bool) (hC : PCPPQueryNatural.budget n<C) :
    ∃ (H : Fin 11 → ℕ) (A : Fin 11 → List Bool),
      Step PCPPQueryNatural.machine (PCPPQueryNatural.budget n) (fun _ => 0)
        (input C (natWord n++tail)) H A ∧
      H 0=(natWord n).length ∧ A 0=natWord n++tail ∧ H 10=1 ∧ A 10=UnaryTemplate.tape n ∧
      ∀ i,i≠0 → i≠10 → (A i).length=C := by
  obtain ⟨r,hr,hs,src,pos,drv,dh⟩ := PCPPQueryNatural.natural_run [] tail n
  simp only [List.nil_append,List.length_nil,Nat.zero_add] at hr src pos
  have hi : PCPPQueryNatural.entry (natWord n++tail) 0 =
      (⟨PCPPQueryNatural.machine.start,fun _ => 0,fun i => if i=0 then natWord n++tail else []⟩ :
        Configuration 11 PCPPQueryNatural.states) := by
    apply configuration_ext
    · rfl
    · funext i;simp [PCPPQueryNatural.entry]
    · rfl
  rw [hi] at hr
  have raw : Step PCPPQueryNatural.machine (PCPPQueryNatural.budget n) (fun _ => 0)
      (fun i => if i=0 then natWord n++tail else []) r.final.heads r.final.tapes :=
    ⟨r,hr,rfl,rfl,hs⟩
  let A := fun i => ZeroPadding.pad (caps C i) (r.final.tapes i)
  have run := raw.pad (caps C)
  have initial : (fun i => ZeroPadding.pad (caps C i) (if i=0 then natWord n++tail else [])) =
      input C (natWord n++tail) := by
    funext i
    by_cases h0 : i=0
    · subst i;simp [caps,input,ZeroPadding.pad_zero]
    by_cases h10 : i=10
    · subst i;simp [caps,input,ZeroPadding.pad_zero]
    · simp [caps,input,h0,h10,ZeroPadding.pad]
  rw [initial] at run
  refine ⟨r.final.heads,A,run,?_,?_,dh,?_,?_⟩
  · rw [DecompositionSource.natWord_length];exact pos
  · change ZeroPadding.pad 0 (r.final.tapes 0) = _
    rw [ZeroPadding.pad_zero,src]
  · change ZeroPadding.pad 0 (r.final.tapes 10) = _
    rw [ZeroPadding.pad_zero,drv]
  · intro i h0 h10
    obtain ⟨p,pr,_ph,pt,_ps⟩ := run
    have hfit : (⟨PCPPQueryNatural.machine.start,fun _ => 0,input C (natWord n++tail)⟩ :
        Configuration 11 PCPPQueryNatural.states).heads i+PCPPQueryNatural.budget n <
        (input C (natWord n++tail) i).length := by
      simpa only [input,if_neg h0,if_neg h10,List.length_replicate,Nat.zero_add] using hC
    have bound := length_preserved PCPPQueryNatural.machine _ _ p i pr hfit
    rw [pt] at bound
    change (A i).length=(input C (natWord n++tail) i).length at bound
    simpa only [input,if_neg h0,if_neg h10,List.length_replicate] using bound

theorem masked_run (C n : ℕ) (tail : List Bool) (hC : PCPPQueryNatural.budget n<C) :
    ∃ A : Fin 11 → List Bool,
      Step machine (2*PCPPQueryNatural.budget n+2)
        (Fin.addCases (fun _ : Fin 11 => 0) (fun _ : Fin 1 => 0))
        (Fin.addCases (input C (natWord n++tail)) (fun _ : Fin 1 => List.replicate C false))
        (Fin.addCases (heads n) (fun _ : Fin 1 => 0))
        (Fin.addCases A (fun _ : Fin 1 => List.replicate C false)) ∧
      A 0=natWord n++tail ∧ A 10=UnaryTemplate.tape n ∧
      ∀ i,i≠0 → i≠10 → (A i).length=C := by
  obtain ⟨H,A,run,h0,a0,h10,a10,hlen⟩ := padded_run C n tail hC
  have masked := run.mask selected (by intros;rfl) hC.le
  refine ⟨A,?_,a0,a10,hlen⟩
  apply masked.congr _ rfl
  have he : (fun i => if selected i then 0 else H i) = heads n := by
    funext i
    by_cases hi : i=0
    · subst i;simp [selected,heads,h0]
    by_cases hj : i=10
    · subst i;simp [selected,heads,h10]
    · simp [selected,heads,hi,hj]
  rw [he]

end NearCubicWires.ExtDecompositionBatch.PreludeNatural

/-! The header reader and its paid cleanup in a fixed fourteen-port bank.
The actual source cursor and occurrence driver remain live during cleanup. -/
namespace NearCubicWires.ExtDecompositionBatch.PreludeHeader
open LocalBitMultitape RepairOrdinary RepairRepresentation RepairOrdinary.RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def heads (H : Fin 11 → ℕ) : Fin 14 → ℕ :=
  Fin.addCases (m:=12) (n:=2) (motive:=fun _ => ℕ)
    (Fin.addCases (m:=11) (n:=1) (motive:=fun _ => ℕ) H (fun _ => 0)) (fun _ => 0)
def data (C : ℕ) (A : Fin 11 → List Bool) : Fin 14 → List Bool :=
  Fin.addCases (m:=12) (n:=2) (motive:=fun _ => List Bool)
    (Fin.addCases (m:=11) (n:=1) (motive:=fun _ => List Bool) A (fun _ => List.replicate C false))
    (![List.replicate C true,List.replicate (C+1) false] : Fin 2 → List Bool)
def values (C n : ℕ) (source : List Bool) (i : Fin 11) : List Bool :=
  if i=0 then source else if i=10 then UnaryTemplate.tape n else List.replicate C false
def eraseSlots : Fin 11 → Fin 14 := ![1,2,3,4,5,6,7,8,9,12,13]
def privateValues (A : Fin 11 → List Bool) (i : Fin 9) := A ⟨i.val+1,by omega⟩
def clean (C : ℕ) : Fin 11 → List Bool :=
  Fin.addCases (m:=10) (n:=1) (motive:=fun _ => List Bool)
    (Fin.addCases (m:=9) (n:=1) (motive:=fun _ => List Bool) (fun _ => List.replicate C false)
      (fun _ => List.replicate C true)) (fun _ => List.replicate (C+1) false)
noncomputable def first := TapeEmbedding.machine 2 PreludeNatural.machine
noncomputable def erase := RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 9)
noncomputable def machine := Composition.machine first erase
def budget (C n : ℕ) := 2*PCPPQueryNatural.budget n+2*C+7

theorem erase_run (C n : ℕ) (source : List Bool) (A : Fin 11 → List Bool)
    (h0 : A 0=source) (h10 : A 10=UnaryTemplate.tape n)
    (hlen : ∀ i,i≠0 → i≠10 → (A i).length=C) :
    Step erase (2*C+4) (heads (PreludeNatural.heads n)) (data C A)
      (heads (PreludeNatural.heads n)) (data C (values C n source)) := by
  have ready := Step.of_ready (RecoveryScratchErase.erase_ready C (C+1) (privateValues A) (by
    intro i
    exact (hlen ⟨i.val+1,by omega⟩
      (by intro h;have hv:=congrArg Fin.val h;change i.val+1=0 at hv;omega)
      (by intro h;have hv:=congrArg Fin.val h;change i.val+1=10 at hv;have hi:=i.isLt;omega)).le))
  have localRun : Step (RecoveryScratchErase.resetMachine 9) (2*C+4) (fun _ => 0)
      (Fin.addCases (m:=10) (n:=1) (motive:=fun _ => List Bool)
        (Fin.addCases (m:=9) (n:=1) (motive:=fun _ => List Bool)
          (privateValues A) (fun _ => List.replicate C true))
        (fun _ => List.replicate (C+1) false)) (fun _ => 0) (clean C) := by
    apply ready.congr rfl
    funext i;fin_cases i <;> simp only [clean,Nat.max_self]
  have hh : ∀ j,heads (PreludeNatural.heads n) (eraseSlots j)=0 := by
    intro j;fin_cases j <;> rfl
  have run := localRun.dock eraseSlots (by decide) (heads (PreludeNatural.heads n)) (data C A) hh (by
    intro j;fin_cases j <;> rfl)
  apply run.congr (dockH_existing eraseSlots _ _ hh)
  apply HierarchyWidth.install_eq eraseSlots (by decide)
  · intro j;fin_cases j <;> rfl
  · intro i hi
    have keep : i=0 ∨ i=10 ∨ i=11 := by
      have hfinite : ∀ k : Fin 14,(∀ j,eraseSlots j≠k) → k=0 ∨ k=10 ∨ k=11 := by decide
      exact hfinite i hi
    rcases keep with rfl|rfl|rfl
    · exact h0.symm
    · exact h10.symm
    · rfl

theorem run (C n : ℕ) (tail : List Bool) (hC : PCPPQueryNatural.budget n<C) :
    Step machine (budget C n) (fun _ => 0) (data C (PreludeNatural.input C (natWord n++tail)))
      (heads (PreludeNatural.heads n)) (data C (values C n (natWord n++tail))) := by
  obtain ⟨A,parsed,a0,a10,hlen⟩ := PreludeNatural.masked_run C n tail hC
  have head := parsed.embed (fun _ : Fin 2 => 0)
    (![List.replicate C true,List.replicate (C+1) false] : Fin 2 → List Bool)
  have initial : Fin.addCases (m:=12) (n:=2) (motive:=fun _ => ℕ)
      (Fin.addCases (m:=11) (n:=1) (motive:=fun _ => ℕ) (fun _ => 0) (fun _ => 0))
      (fun _ => 0) = (fun _ : Fin 14 => 0) := by funext i;fin_cases i <;> rfl
  have head' := head.congr_in initial rfl
  have whole := head'.seq (erase_run C n (natWord n++tail) A a0 a10 hlen)
  have time : (2*PCPPQueryNatural.budget n+2)+1+(2*C+4)=budget C n := by unfold budget;omega
  rw [time] at whole
  exact whole

end NearCubicWires.ExtDecompositionBatch.PreludeHeader

/-! The header's fourteen ports share the existing source bank, source
stream, paid mask log and occurrence driver. All other batch ports are retained. -/
namespace NearCubicWires.ExtDecompositionBatch.Prelude
open LocalBitMultitape RepairOrdinary RepairRepresentation ExecutableInterfaces
open RepairOrdinary.DecompositionSource RepairOrdinary.RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
variable (a : DecompositionAlgorithm)

def lift (i : Fin (T a)) : Fin (CT a+1) := (i.castAdd 1).castAdd 1
def sourceSlot := lift a (str a)
def totalSlot := lift a (tot a)
def driverSlot : Fin (CT a+1) := Fin.last (CT a)
def logSlot : Fin (CT a+1) := (Fin.last (T a)).castAdd 1
def headerSlots : Fin 14 → Fin (CT a+1) :=
  ![sourceSlot a,lift a (bk a (Counted.localTape a 0)),lift a (bk a (Counted.localTape a 1)),
    lift a (bk a (Counted.localTape a 2)),lift a (bk a (Counted.localTape a 3)),
    lift a (bk a (Counted.localTape a 4)),lift a (bk a (Counted.localTape a 5)),
    lift a (bk a (Counted.localTape a 6)),lift a (bk a (Counted.localTape a 7)),
    lift a (bk a (Counted.localTape a 8)),driverSlot a,logSlot a,lift a (drv a),lift a (wsp a)]
def inputHeads := OccurrenceTemplate.heads a 0 [] [] [] 0
def inputTapes (C q : ℕ) (source : List Bool) : Fin (CT a+1) → List Bool :=
  Fin.addCases (m:=CT a) (n:=1) (loopInA a C q source [] [] []) (fun _ => [])
noncomputable def header := RecoveryFocus.machine (headerSlots a) PreludeHeader.machine

theorem header_value (j : Fin 14) : (headerSlots a j).val =
    (![SB a,0,1,2,3,4,5,6,7,8,CT a,T a,SB a+8,SB a+9] : Fin 14 → ℕ) j := by
  fin_cases j <;> rfl

theorem header_injective : Function.Injective (headerSlots a) := by
  have hs : 27 ≤ SB a := by rw [sb_eq];omega
  intro i j he
  have hv := congrArg Fin.val he
  rw [header_value,header_value] at hv
  fin_cases i <;> fin_cases j
  all_goals first
    | rfl
    | (dsimp [CT,T] at hv
       exfalso
       omega)

theorem header_input_heads (j : Fin 14) : inputHeads a (headerSlots a j)=0 := by
  fin_cases j <;> simp [inputHeads,headerSlots,sourceSlot,driverSlot,logSlot,lift,
    OccurrenceTemplate.heads,loopInH,loopHeads,str,drv,wsp,bk,ex,Fin.addCases]
theorem header_input_tapes (C q : ℕ) (source : List Bool) (j : Fin 14) :
    inputTapes a C q source (headerSlots a j)=PreludeHeader.data C (PreludeNatural.input C source) j := by
  have hT : 27 ≤ T a := by change 27 ≤ SB a+12;rw [sb_eq];omega
  fin_cases j <;> simp [inputTapes,headerSlots,sourceSlot,driverSlot,logSlot,lift,
    loopInA,loggedTapes,loopTapes,str,drv,wsp,bk,ex,PreludeHeader.data,PreludeNatural.input,Fin.addCases,local_val]
theorem header_output_heads (n : ℕ) (j : Fin 14) :
    OccurrenceTemplate.heads a (natWord n).length [] [] [] 1 (headerSlots a j)=
      PreludeHeader.heads (PreludeNatural.heads n) j := by
  have hT : 27 ≤ T a := by change 27 ≤ SB a+12;rw [sb_eq];omega
  fin_cases j <;> simp [headerSlots,sourceSlot,driverSlot,logSlot,lift,OccurrenceTemplate.heads,
    loopInH,loopHeads,str,drv,wsp,bk,ex,PreludeHeader.heads,PreludeNatural.heads,Fin.addCases,local_val]
theorem header_output_tapes (C q n : ℕ) (source : List Bool) (j : Fin 14) :
    OccurrenceTemplate.tapes a C q source [] [] [] n (headerSlots a j)=
      PreludeHeader.data C (PreludeHeader.values C n source) j := by
  have hT : 27 ≤ T a := by change 27 ≤ SB a+12;rw [sb_eq];omega
  fin_cases j <;> simp [headerSlots,sourceSlot,driverSlot,logSlot,lift,OccurrenceTemplate.tapes,
    loopInA,loggedTapes,loopTapes,str,drv,wsp,bk,ex,PreludeHeader.data,PreludeHeader.values,Fin.addCases,local_val]

theorem header_outside_heads (n : ℕ) (i : Fin (CT a+1)) (hi : ∀ j,headerSlots a j≠i) :
    OccurrenceTemplate.heads a (natWord n).length [] [] [] 1 i=inputHeads a i := by
  revert hi
  refine Fin.addCases (m:=CT a) (n:=1) (fun j => ?_) (fun j => ?_) i
  · refine Fin.addCases (m:=T a) (n:=1) (fun k => ?_) (fun k => ?_) j
    · refine Fin.addCases (m:=SB a) (n:=12) (fun l => ?_) (fun l => ?_) k
      · intro _;simp only [OccurrenceTemplate.heads,inputHeads,loopInH,loopHeads,Fin.addCases_left]
      · intro hout
        fin_cases l
        · exact False.elim (hout 0 rfl)
        all_goals simp [OccurrenceTemplate.heads,inputHeads,loopInH,loopHeads,Fin.addCases]
    · intro _;simp only [OccurrenceTemplate.heads,inputHeads,loopInH,Fin.addCases_left,Fin.addCases_right]
  · intro hout
    have hj : j=0 := Fin.eq_zero j
    subst hj
    exact False.elim (hout 10 rfl)

theorem header_run (C q n : ℕ) (tail : List Bool) (hC : PCPPQueryNatural.budget n<C) :
    Step (header a) (PreludeHeader.budget C n) (inputHeads a) (inputTapes a C q (natWord n++tail))
      (OccurrenceTemplate.heads a (natWord n).length [] [] [] 1)
      (OccurrenceTemplate.tapes a C q (natWord n++tail) [] [] [] n) := by
  have run := (PreludeHeader.run C n tail hC).dock (headerSlots a) (header_injective a)
    (inputHeads a) (inputTapes a C q (natWord n++tail)) (header_input_heads a)
    (header_input_tapes a C q (natWord n++tail))
  apply run.congr
  · funext i
    cases hp : RecoveryFocus.pick (headerSlots a) i with
    | some j =>
      have he := RecoveryFocus.slot_of_pick (headerSlots a) hp
      rw [←he,dockH_slot _ (header_injective a)]
      exact (header_output_heads a n j).symm
    | none =>
      have hi : ∀ j,headerSlots a j≠i := by
        intro j he
        have hj := RecoveryFocus.pick_slot (headerSlots a) (header_injective a) j
        rw [he,hp] at hj
        contradiction
      rw [dockH_other _ _ _ i hi]
      exact (header_outside_heads a n i hi).symm
  · apply HierarchyWidth.install_eq (headerSlots a) (header_injective a)
    · exact header_output_tapes a C q n (natWord n++tail)
    · intro i hi
      revert hi
      refine Fin.addCases (m:=CT a) (n:=1) (fun j _ => ?_) (fun j hj => ?_) i
      · simp only [OccurrenceTemplate.tapes,inputTapes,Fin.addCases_left]
      · have he : j=0 := Fin.eq_zero j
        subst he
        exact False.elim (hj 10 rfl)

end NearCubicWires.ExtDecompositionBatch.Prelude

/-! Skip the actual framed top payload and write the running-total
sentinel. Neither operation inspects or changes an occurrence request. -/
namespace NearCubicWires.ExtDecompositionBatch.PreludeTail
open LocalBitMultitape RepairOrdinary RepairRepresentation RepairOrdinary.RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def sourceSlots : Fin 1 → Fin 2 := fun _ => 0
def totalSlots : Fin 1 → Fin 2 := fun _ => 1
noncomputable def skip := RecoveryFocus.machine sourceSlots FrameSkip.machine
noncomputable def sentinel := RecoveryFocus.machine totalSlots (HierarchyFixedWord.raw [false])
noncomputable def machine := Composition.machine skip sentinel

theorem skip_run (pre top rest : List Bool) :
    Step skip (2*top.length+1) ![pre.length,0] ![pre++frame top++rest,[]]
      ![pre.length+(frame top).length,0] ![pre++frame top++rest,[]] := by
  obtain ⟨r,hr,hf,hs⟩ := FrameSkip.skip_run pre top rest
  have base : Step FrameSkip.machine (2*top.length+1) (fun _ => pre.length)
      (fun _ => pre++frame top++rest) (fun _ => pre.length+(frame top).length)
      (fun _ => pre++frame top++rest) := ⟨r,hr,by rw [hf];rfl,by rw [hf];rfl,hs.le⟩
  have run := base.dock sourceSlots (by decide) ![pre.length,0] ![pre++frame top++rest,[]]
    (by intro i;fin_cases i;rfl) (by intro i;fin_cases i;rfl)
  apply run.congr
  · funext i;fin_cases i
    · exact dockH_slot sourceSlots (by decide) _ _ 0
    · exact dockH_other sourceSlots _ _ 1 (by decide)
  · exact install_existing sourceSlots _ _ (by intro i;fin_cases i;rfl)

theorem sentinel_run (pos : ℕ) (source : List Bool) :
    Step sentinel 1 ![pos,0] ![source,[]] ![pos,1] ![source,[false]] := by
  obtain ⟨r,hr,hf,hs⟩ := (HierarchyFixedWord.write_prefix [false] 0 1 rfl).run rfl
  have base : Step (HierarchyFixedWord.raw [false]) 1 (fun _ => 0) (fun _ => [])
      (fun _ => 1) (fun _ => [false]) := ⟨r,hr,by rw [hf];rfl,by rw [hf];rfl,hs.le⟩
  have run := base.dock totalSlots (by decide) ![pos,0] ![source,[]]
    (by intro i;fin_cases i;rfl) (by intro i;fin_cases i;rfl)
  apply run.congr
  · funext i;fin_cases i
    · exact dockH_other totalSlots _ _ 0 (by decide)
    · exact dockH_slot totalSlots (by decide) _ _ 0
  · funext i;fin_cases i
    · exact install_other totalSlots _ _ 0 (by decide)
    · exact install_slot totalSlots (by decide) _ _ 0

theorem run (pre top rest : List Bool) :
    Step machine (2*top.length+3) ![pre.length,0] ![pre++frame top++rest,[]]
      ![(pre++frame top).length,1] ![pre++frame top++rest,[false]] := by
  have whole := (skip_run pre top rest).seq
    (sentinel_run (pre.length+(frame top).length) (pre++frame top++rest))
  have hc : (2*top.length+1)+1+1=2*top.length+3 := by omega
  rw [hc,←List.length_append] at whole
  exact whole

end NearCubicWires.ExtDecompositionBatch.PreludeTail

/-! The top-frame skip and total sentinel share only the actual source and
total ports of the occurrence bank. Every other tape and head is retained. -/
namespace NearCubicWires.ExtDecompositionBatch.Prelude
open LocalBitMultitape RepairOrdinary RepairRepresentation ExecutableInterfaces
open RepairOrdinary.DecompositionSource RepairOrdinary.RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
variable (a : DecompositionAlgorithm)

def tailSlots : Fin 2 → Fin (CT a+1) := ![sourceSlot a,totalSlot a]
noncomputable def tail := RecoveryFocus.machine (tailSlots a) PreludeTail.machine

theorem tail_injective : Function.Injective (tailSlots a) := by
  intro i j he
  have hv := congrArg Fin.val he
  fin_cases i <;> fin_cases j
  all_goals first
    | rfl
    | (change SB a=SB a+3 at hv;omega)
    | (change SB a+3=SB a at hv;omega)

theorem tail_input_heads (pre : List Bool) (j : Fin 2) :
    OccurrenceTemplate.heads a pre.length [] [] [] 1 (tailSlots a j)=![pre.length,0] j := by
  fin_cases j <;> simp [tailSlots,sourceSlot,totalSlot,lift,OccurrenceTemplate.heads,
    loopInH,loopHeads,str,tot,ex,Fin.addCases]
theorem tail_input_tapes (C q n : ℕ) (source : List Bool) (j : Fin 2) :
    OccurrenceTemplate.tapes a C q source [] [] [] n (tailSlots a j)=![source,[]] j := by
  fin_cases j <;> simp [tailSlots,sourceSlot,totalSlot,lift,OccurrenceTemplate.tapes,
    loopInA,loggedTapes,loopTapes,str,tot,ex,Fin.addCases]
theorem tail_output_heads (pre top : List Bool) (j : Fin 2) :
    OccurrenceTemplate.heads a (pre++frame top).length [] [] [false] 1 (tailSlots a j)=
      ![(pre++frame top).length,1] j := by
  fin_cases j <;> simp [tailSlots,sourceSlot,totalSlot,lift,OccurrenceTemplate.heads,
    loopInH,loopHeads,str,tot,ex,Fin.addCases]
theorem tail_output_tapes (C q n : ℕ) (source : List Bool) (j : Fin 2) :
    OccurrenceTemplate.tapes a C q source [] [] [false] n (tailSlots a j)=![source,[false]] j := by
  fin_cases j <;> simp [tailSlots,sourceSlot,totalSlot,lift,OccurrenceTemplate.tapes,
    loopInA,loggedTapes,loopTapes,str,tot,ex,Fin.addCases]

theorem tail_outside_heads (pre top : List Bool) (i : Fin (CT a+1)) (hi : ∀ j,tailSlots a j≠i) :
    OccurrenceTemplate.heads a (pre++frame top).length [] [] [false] 1 i=
      OccurrenceTemplate.heads a pre.length [] [] [] 1 i := by
  revert hi
  refine Fin.addCases (m:=CT a) (n:=1) (fun j => ?_) (fun j => ?_) i
  · refine Fin.addCases (m:=T a) (n:=1) (fun k => ?_) (fun k => ?_) j
    · refine Fin.addCases (m:=SB a) (n:=12) (fun l => ?_) (fun l => ?_) k
      · intro _;simp only [OccurrenceTemplate.heads,loopInH,loopHeads,Fin.addCases_left]
      · intro hout
        fin_cases l
        · exact False.elim (hout 0 rfl)
        case «3» => exact False.elim (hout 1 rfl)
        all_goals simp [OccurrenceTemplate.heads,loopInH,loopHeads,Fin.addCases]
    · intro _;simp only [OccurrenceTemplate.heads,loopInH,Fin.addCases_left,Fin.addCases_right]
  · intro _;simp only [OccurrenceTemplate.heads,Fin.addCases_right]

theorem tail_outside_tapes (C q n : ℕ) (source : List Bool) (i : Fin (CT a+1))
    (hi : ∀ j,tailSlots a j≠i) :
    OccurrenceTemplate.tapes a C q source [] [] [false] n i=
      OccurrenceTemplate.tapes a C q source [] [] [] n i := by
  revert hi
  refine Fin.addCases (m:=CT a) (n:=1) (fun j => ?_) (fun j => ?_) i
  · refine Fin.addCases (m:=T a) (n:=1) (fun k => ?_) (fun k => ?_) j
    · refine Fin.addCases (m:=SB a) (n:=12) (fun l => ?_) (fun l => ?_) k
      · intro _;simp only [OccurrenceTemplate.tapes,loopInA,loggedTapes,loopTapes,Fin.addCases_left]
      · intro hout
        fin_cases l
        case «3» => exact False.elim (hout 1 rfl)
        all_goals simp [OccurrenceTemplate.tapes,loopInA,loggedTapes,loopTapes,Fin.addCases]
    · intro _;simp only [OccurrenceTemplate.tapes,loopInA,loggedTapes,Fin.addCases_left,Fin.addCases_right]
  · intro _;simp only [OccurrenceTemplate.tapes,Fin.addCases_right]

theorem tail_run (C q n : ℕ) (pre top rest : List Bool) :
    Step (tail a) (2*top.length+3)
      (OccurrenceTemplate.heads a pre.length [] [] [] 1)
      (OccurrenceTemplate.tapes a C q (pre++frame top++rest) [] [] [] n)
      (OccurrenceTemplate.heads a (pre++frame top).length [] [] [false] 1)
      (OccurrenceTemplate.tapes a C q (pre++frame top++rest) [] [] [false] n) := by
  have run := (PreludeTail.run pre top rest).dock (tailSlots a) (tail_injective a)
    (OccurrenceTemplate.heads a pre.length [] [] [] 1)
    (OccurrenceTemplate.tapes a C q (pre++frame top++rest) [] [] [] n)
    (tail_input_heads a pre) (tail_input_tapes a C q n (pre++frame top++rest))
  apply run.congr
  · funext i
    cases hp : RecoveryFocus.pick (tailSlots a) i with
    | some j =>
      have he := RecoveryFocus.slot_of_pick (tailSlots a) hp
      rw [←he,dockH_slot _ (tail_injective a)]
      exact (tail_output_heads a pre top j).symm
    | none =>
      have hi : ∀ j,tailSlots a j≠i := by
        intro j he
        have hj := RecoveryFocus.pick_slot (tailSlots a) (tail_injective a) j
        rw [he,hp] at hj
        contradiction
      rw [dockH_other _ _ _ i hi]
      exact (tail_outside_heads a pre top i hi).symm
  · apply HierarchyWidth.install_eq (tailSlots a) (tail_injective a)
    · exact tail_output_tapes a C q n (pre++frame top++rest)
    · exact tail_outside_tapes a C q n (pre++frame top++rest)

end NearCubicWires.ExtDecompositionBatch.Prelude

/-! The paid physical prelude parses the actual header, skips the actual
top frame, and initializes the accumulated total before the existing loop. -/
namespace NearCubicWires.ExtDecompositionBatch.Prelude
open LocalBitMultitape RepairOrdinary RepairRepresentation ExecutableInterfaces
open RepairOrdinary.DecompositionSource RepairOrdinary.RecoveryRootRound SupplierPipeline
open RepairOrdinary.CloseoutRowsCircuitBottom
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
variable (a : DecompositionAlgorithm)

noncomputable def machine := Composition.machine (header a) (tail a)
def budget (C n : ℕ) (top : List Bool) := PreludeHeader.budget C n+1+(2*top.length+3)

theorem run (C q n : ℕ) (top rest : List Bool) (hC : PCPPQueryNatural.budget n<C) :
    Step (machine a) (budget C n top)
      (inputHeads a) (inputTapes a C q (natWord n++frame top++rest))
      (OccurrenceTemplate.heads a (natWord n++frame top).length [] [] [false] 1)
      (OccurrenceTemplate.tapes a C q (natWord n++frame top++rest) [] [] [false] n) := by
  have first := header_run a C q n (frame top++rest) hC
  rw [←List.append_assoc] at first
  exact first.seq (tail_run a C q n (natWord n) top rest)

theorem budget_eq (C n : ℕ) (top : List Bool) :
    budget C n top=2*PCPPQueryNatural.budget n+2*C+2*top.length+11 := by
  unfold budget PreludeHeader.budget
  omega

/-- The exact existing loop, started with the actual generated template. -/
theorem loop_step (C q : ℕ) (occ : List (SupportedNormalizedGate q))
    (pre rest c1 c2 c3 : List Bool) (hC : ∀ g∈occ,bodyCost a q g<C) :
    Step (occurrenceLoop a) (loopCost a C occ)
      (OccurrenceTemplate.heads a pre.length c1 c2 c3 1)
      (OccurrenceTemplate.tapes a C q (pre++requestStream occ++rest) c1 c2 c3 occ.length)
      (OccurrenceTemplate.heads a (pre.length+(requestStream occ).length)
        (c1++(counts a occ).flatMap natWord) (c2++(GS a occ).flatMap exactWord)
        (c3++List.replicate (B a occ) true) 1)
      (OccurrenceTemplate.tapes a C q (pre++requestStream occ++rest)
        (c1++(counts a occ).flatMap natWord) (c2++(GS a occ).flatMap exactWord)
        (c3++List.replicate (B a occ) true) occ.length) := by
  obtain ⟨r,hr,hf,hs⟩ := OccurrenceTemplate.run a C q occ pre rest c1 c2 c3 hC
  have entry : OccurrenceTemplate.cfg a 0 C q pre.length (pre++requestStream occ++rest)
      c1 c2 c3 occ.length 1=
      (⟨(occurrenceLoop a).start,OccurrenceTemplate.heads a pre.length c1 c2 c3 1,
        OccurrenceTemplate.tapes a C q (pre++requestStream occ++rest) c1 c2 c3 occ.length⟩ :
          Configuration (CT a+1) _) := by
    apply configuration_ext
    · rfl
    · rfl
    · rfl
  rw [entry] at hr
  exact ⟨r,hr,by rw [hf];rfl,by rw [hf];rfl,hs⟩

noncomputable def occurrences := Composition.machine (machine a) (occurrenceLoop a)
def occurrenceBudget {q : ℕ} (C : ℕ) (occ : List (SupportedNormalizedGate q)) (top : List Bool) :=
  budget C occ.length top+1+loopCost a C occ

/-- Complete prelude and original occurrence loop, uniformly including no occurrences. -/
theorem occurrences_run (C q : ℕ) (occ : List (SupportedNormalizedGate q)) (top : List Bool)
    (hheader : PCPPQueryNatural.budget occ.length<C)
    (hbody : ∀ g∈occ,bodyCost a q g<C) :
    Step (occurrences a) (occurrenceBudget a C occ top)
      (inputHeads a) (inputTapes a C q (segment occ top))
      (OccurrenceTemplate.heads a (segment occ top).length
        ((counts a occ).flatMap natWord) ((GS a occ).flatMap exactWord)
        (false::List.replicate (B a occ) true) 1)
      (OccurrenceTemplate.tapes a C q (segment occ top)
        ((counts a occ).flatMap natWord) ((GS a occ).flatMap exactWord)
        (false::List.replicate (B a occ) true) occ.length) := by
  have first := run a C q occ.length top (requestStream occ) hheader
  have second := loop_step a C q occ (natWord occ.length++frame top) [] [] [] [false] hbody
  simp only [List.append_nil,List.nil_append,List.cons_append] at second
  have sourceEq : (natWord occ.length++frame top)++requestStream occ=segment occ top := by
    simp only [segment,requestStream,List.append_assoc]
  have sourceEq' : natWord occ.length++frame top++requestStream occ=segment occ top := rfl
  rw [sourceEq'] at first
  rw [sourceEq,←List.length_append,sourceEq] at second
  exact first.seq second

end NearCubicWires.ExtDecompositionBatch.Prelude

/-! The complete ordered source batch: actual header and top skip, every
original constructor occurrence, and one final native child cache. -/
namespace NearCubicWires.ExtDecompositionBatch
open LocalBitMultitape RepairOrdinary RepairRepresentation ExecutableInterfaces
open RepairOrdinary.DecompositionSource RepairOrdinary.RecoveryRootRound SupplierPipeline
open RepairOrdinary.CloseoutRowsCircuitBottom
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
variable (a : DecompositionAlgorithm)

noncomputable def finalMachine:=TapeEmbedding.machine 1 (TapeEmbedding.machine 1 (FinalLayout.machine a))
noncomputable def batchMachine:=Composition.machine (Prelude.occurrences a) (finalMachine a)
def batchBudget {q : ℕ} (C : ℕ) (occ : List (SupportedNormalizedGate q)) (top : List Bool):=
  Prelude.occurrenceBudget a C occ top+1+FinalLayout.finalCost C (GS a occ)
def live (i:Fin (T a)) : Fin (CT a+1):=(i.castAdd 1).castAdd 1

theorem finished_unmodified {q:ℕ} (gs:List (ExactThresholdGate q)) (H:Fin (T a) → ℕ)
    (e:Fin 12) (he:e.val=0 ∨ e.val=1):
    FinalLayout.finishedHeads a gs H (ex a e)=H (ex a e):=by
  unfold FinalLayout.finishedHeads
  rw [dockH_other (FinalLayout.tailSlots a) _ _ _
    (FinalLayout.tail_other a e (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))]
  exact dockH_other (FinalLayout.prefixSlots a) _ _ _
    (FinalLayout.prefix_other a e (by omega) (by omega) (by omega) (by omega) (by omega))

theorem batch_run {q : ℕ} (C : ℕ) (occ : List (SupportedNormalizedGate q)) (top : List Bool)
    (hheader : PCPPQueryNatural.budget occ.length<C)
    (hbody : ∀g∈occ,bodyCost a q g<C)
    (hn : B a occ+2≤C) (hh : PCPPNativeNaturalAppend.budget (B a occ)≤C)
    (hb : (bodyWord a occ).length≤C) (hc : (exactListWord (GS a occ)).length≤C) :
    ∃ H O,
      Step (batchMachine a) (batchBudget a C occ top)
        (Prelude.inputHeads a) (Prelude.inputTapes a C q (segment occ top)) H O ∧
      O (live a (cch a))=exactListWord (GS a occ) ∧ H (live a (cch a))=0 ∧
      O (live a (cnt a))=countWord a occ ∧ H (live a (cnt a))=(countWord a occ).length ∧
      O (live a (str a))=segment occ top ∧ H (live a (str a))=(segment occ top).length ∧
      O (live a (tot a))=UnaryTemplate.tape (B a occ) ∧ H (live a (tot a))=1 ∧
      O (live a (dom a))=UnaryTemplate.tape q ∧ H (live a (dom a))=1 ∧
      O (live a (scr a))=List.replicate (B a occ) false ∧ H (live a (scr a))=0 ∧
      O (live a (drv a))=List.replicate C true ∧ H (live a (drv a))=0 ∧
      O (live a (wsp a))=List.replicate (C+1) false ∧ H (live a (wsp a))=0 := by
  have first:=Prelude.occurrences_run a C q occ top hheader hbody
  obtain ⟨O,finish,cache,counts,source,total,domain,scratch,driver,log⟩:=
    final_state_run a C occ (segment occ top).length (segment occ top) hn hh hb hc
  have second:=(finish.embed (fun _ : Fin 1=>0) (fun _ : Fin 1=>List.replicate C false)).embed
    (fun _ : Fin 1=>1) (fun _ : Fin 1=>UnaryTemplate.tape occ.length)
  have joined:=first.seq second
  have ports:=FinalLayout.finished_cache a (GS a occ)
    (loopHeads a (segment occ top).length (countWord a occ) (bodyWord a occ) (totalWord a occ))
  refine ⟨_,_,joined,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals simp only [live,Fin.addCases_left]
  · exact cache
  · exact ports.1
  · exact counts
  · have h := finished_unmodified a (GS a occ)
      (loopHeads a (segment occ top).length (countWord a occ) (bodyWord a occ) (totalWord a occ))
      1 (Or.inr rfl)
    simpa [loopHeads, ex, cnt] using h
  · exact source
  · have h := finished_unmodified a (GS a occ)
      (loopHeads a (segment occ top).length (countWord a occ) (bodyWord a occ) (totalWord a occ))
      0 (Or.inl rfl)
    simpa [loopHeads, ex, str] using h
  · exact total
  · exact ports.2.1
  · exact domain
  · exact ports.2.2.2.1
  · exact scratch
  · exact ports.2.2.1
  · exact driver
  · exact ports.2.2.2.2.1
  · exact log
  · exact ports.2.2.2.2.2

end NearCubicWires.ExtDecompositionBatch

/-! The same already-produced source capacity pays the residual-atom worker.
No second capacity factory is needed before the ordered raw expansion. -/
namespace NearCubicWires.ExtDecompositionBatch.SourceEnvelope
open LocalBitMultitape RepairOrdinary RepairRepresentation ExecutableInterfaces SupplierPipeline
open RepairOrdinary.CloseoutRowsCircuitBottom
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem atom_capacity (a:DecompositionAlgorithm) {q:ℕ} (occ:List (SupportedNormalizedGate q))
    (top:List Bool) (P:ℕ) (hq:q≤P) (hi:(segment occ top).length≤1000*(P+2)^2):
    64*(B a occ+2)^2≤capacity a P:=by
  have bound:=(actual_bounds a occ top P hq hi).2.2.1
  have cap:=capacity_covers a P
  nlinarith

end NearCubicWires.ExtDecompositionBatch.SourceEnvelope

/-! Actual source-capacity production is upstream of the child cache. The
polynomial worker writes directly into the batch's retained capacity port. -/
namespace NearCubicWires.ExtDecompositionBatch.Cold
open LocalBitMultitape RepairOrdinary RepairRepresentation ExecutableInterfaces
open RepairOrdinary.DecompositionSource RepairOrdinary.RecoveryRootRound
open RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
variable (a : DecompositionAlgorithm)

abbrev Base:=CT a+1
abbrev Power:=DimensionPolynomial.tapes (SourceEnvelope.degree a)
abbrev tapes:=Base a+Power a
def old (i:Fin (Base a)) : Fin (tapes a):=i.castAdd (Power a)
def extra (i:Fin (Power a)) : Fin (tapes a):=i.natAdd (Base a)
def port (i:Fin (T a)) : Fin (tapes a):=old a (live a i)
def powerSlots (i:Fin (Power a)) : Fin (tapes a):=
  if i=DimensionPolynomial.rawSlot (SourceEnvelope.degree a) then port a (drv a) else extra a i

theorem power_injective : Function.Injective (powerSlots a):=by
  intro i j h
  have hv:=congrArg (fun x:Fin (tapes a)=>x.val) h
  have bound:=(live a (drv a)).isLt
  simp only [powerSlots] at hv
  split_ifs at hv <;> simp only [port,old,extra,Fin.val_castAdd,Fin.val_natAdd,Base] at hv
  all_goals apply Fin.ext;omega

theorem power_old_other (i:Fin (Base a)) (hi:i≠live a (drv a)):
    ∀j,powerSlots a j≠old a i:=by
  intro j h
  have hv:=congrArg (fun x:Fin (tapes a)=>x.val) h
  have bound:=i.isLt
  simp only [powerSlots] at hv
  split_ifs at hv <;> simp only [port,old,extra,Fin.val_castAdd,Fin.val_natAdd] at hv
  · apply hi;exact (Fin.ext hv).symm
  · omega

def eraseSlots (j:Fin (SB a+4)) : Fin (tapes a):=
  if h:j.val<SB a then port a (bk a ⟨j.val,h⟩)
  else if j.val=SB a then port a (fcp a)
  else if j.val=SB a+1 then old a (Prelude.logSlot a)
  else if j.val=SB a+2 then port a (drv a) else port a (wsp a)

theorem erase_value (j:Fin (SB a+4)):(eraseSlots a j).val=
    if j.val<SB a then j.val else if j.val=SB a then SB a+7
    else if j.val=SB a+1 then T a else if j.val=SB a+2 then SB a+8 else SB a+9:=by
  simp only [eraseSlots]
  split_ifs <;> rfl

theorem erase_injective : Function.Injective (eraseSlots a):=by
  intro i j h
  have hv:=congrArg (fun x:Fin (tapes a)=>x.val) h
  rw [erase_value,erase_value] at hv
  have hi:=i.isLt;have hj:=j.isLt
  apply Fin.ext
  dsimp only [T] at hv
  split_ifs at hv <;> omega

noncomputable def powerMachine:=RecoveryFocus.machine (powerSlots a)
  (DimensionPolynomial.machine (SourceEnvelope.degree a) (SourceEnvelope.coefficient a))
noncomputable def eraseMachine:=RecoveryFocus.machine (eraseSlots a)
  (RecoveryScratchErase.resetMachine (SB a+2))
noncomputable def allocationMachine:=Composition.machine (powerMachine a) (eraseMachine a)

end NearCubicWires.ExtDecompositionBatch.Cold

/-! Manufacture the source-specific capacity from the actual retained parser
bound, preserving the native source and its original domain template. -/
namespace NearCubicWires.ExtDecompositionBatch.Cold
open LocalBitMultitape RepairOrdinary RepairRepresentation ExecutableInterfaces
open RepairOrdinary.DecompositionSource RepairOrdinary.RecoveryRootRound
open RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
variable (a : DecompositionAlgorithm)

def heads (pos:ℕ) (i:Fin (tapes a)):=
  if i.val=SB a then pos else if i.val=SB a+10 then 1 else 0
def data (P q:ℕ) (source:List Bool) (i:Fin (tapes a)) : List Bool:=
  if i.val=SB a then source else if i.val=SB a+10 then UnaryTemplate.tape q
  else if i.val=Base a then List.replicate P true else []

theorem raw_positive:0<(DimensionPolynomial.rawSlot (SourceEnvelope.degree a)).val:=by
  simp [DimensionPolynomial.rawSlot,DimensionPolynomial.binarySlots]

theorem power_heads (pos:ℕ) (j:Fin (Power a)):heads a pos (powerSlots a j)=0:=by
  unfold powerSlots
  split_ifs
  · simp [heads,port,old,live,drv,ex]
  · have hj:=j.isLt
    have base:Base a=SB a+14:=by rfl
    simp (disch:=omega) [heads,extra,base]
    split_ifs <;> omega

theorem power_data (P q:ℕ) (source:List Bool) (j:Fin (Power a)):
    data a P q source (powerSlots a j)=DimensionPolynomial.input (SourceEnvelope.degree a) P j:=by
  unfold powerSlots
  split_ifs with hj
  · subst j
    have raw:=raw_positive a
    simp (disch:=omega) [data,port,old,live,drv,ex,DimensionPolynomial.input,Base,CT,T]
    omega
  · have base:Base a=SB a+14:=by rfl
    simp (disch:=omega) [data,extra,base,DimensionPolynomial.input]
    split_ifs <;> first | rfl | omega

theorem power_run (P q pos:ℕ) (source:List Bool):∃A,
    Step (powerMachine a) (DimensionPolynomial.budget (SourceEnvelope.degree a) (SourceEnvelope.coefficient a) P)
      (heads a pos) (data a P q source) (heads a pos) A ∧
    ∀i:Fin (Base a),A (old a i)=
      if i=live a (drv a) then List.replicate (SourceEnvelope.capacity a P) true
      else data a P q source (old a i):=by
  obtain ⟨O,ready,raw⟩:=SourceEnvelope.capacity_produced a P
  obtain ⟨r,hr,ht,hh,hs⟩:=ready
  have step:Step (DimensionPolynomial.machine (SourceEnvelope.degree a) (SourceEnvelope.coefficient a))
      (DimensionPolynomial.budget (SourceEnvelope.degree a) (SourceEnvelope.coefficient a) P)
      (fun _=>0) (DimensionPolynomial.input (SourceEnvelope.degree a) P) (fun _=>0) O:=
    ⟨r,hr,by funext i;exact hh i,ht,hs⟩
  have run:=step.dock (powerSlots a) (power_injective a) (heads a pos) (data a P q source)
    (power_heads a pos) (power_data a P q source)
  have hheads:=dockH_existing (powerSlots a) (heads a pos) (fun _=>0) (power_heads a pos)
  refine ⟨install (powerSlots a) (data a P q source) O,run.congr hheads rfl,?_⟩
  intro i
  by_cases hi:i=live a (drv a)
  · subst i
    rw [if_pos rfl]
    have eq:old a (live a (drv a))=powerSlots a (DimensionPolynomial.rawSlot (SourceEnvelope.degree a)):=by
      simp [powerSlots,port]
    rw [eq,install_slot (powerSlots a) (power_injective a)]
    exact raw
  · rw [if_neg hi,install_other (powerSlots a) _ _ _ (power_old_other a i hi)]

end NearCubicWires.ExtDecompositionBatch.Cold

/-! The manufactured capacity pays for the original batch bank, its mask log,
and its reusable rewind log. The native source and domain stay live. -/
namespace NearCubicWires.ExtDecompositionBatch.Cold
open LocalBitMultitape RepairOrdinary RepairRepresentation ExecutableInterfaces
open RepairOrdinary.DecompositionSource RepairOrdinary.RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
variable (a : DecompositionAlgorithm)

def eraseInput (C:ℕ) (j:Fin (SB a+4)) : List Bool:=
  if j.val=SB a+2 then List.replicate C true else []
def eraseOutput (C:ℕ) (j:Fin (SB a+4)) : List Bool:=
  if j.val<SB a+2 then List.replicate C false
  else if j.val=SB a+2 then List.replicate C true else List.replicate (C+1) false

theorem erase_step (C:ℕ):Step (RecoveryScratchErase.resetMachine (SB a+2)) (2*C+4)
    (fun _=>0) (eraseInput a C) (fun _=>0) (eraseOutput a C):=by
  have h:=Step.of_ready (RecoveryScratchErase.erase_ready C 0 (fun _:Fin (SB a+2)=>[])
    (by intro i;simp))
  apply h.congr_in rfl ?_ |>.congr rfl ?_
  all_goals
    funext i
    refine Fin.addCases (m:=SB a+2+1) (n:=1) (fun j=>?_) (fun j=>?_) i
    · refine Fin.addCases (m:=SB a+2) (n:=1) (fun k=>?_) (fun k=>?_) j
      · have hk:=k.isLt
        simp (disch:=omega) [eraseInput,eraseOutput] <;> omega
      · have hk:=Fin.eq_zero k
        subst k
        simp [eraseInput,eraseOutput]
    · have hj:=Fin.eq_zero j
      subst j
      simp [eraseInput,eraseOutput]

theorem input_value (C q:ℕ) (source:List Bool) (i:Fin (Base a)):
    Prelude.inputTapes a C q source i=
      if i.val<SB a then List.replicate C false
      else if i.val=SB a then source
      else if i.val=SB a+7 then List.replicate C false
      else if i.val=SB a+8 then List.replicate C true
      else if i.val=SB a+9 then List.replicate (C+1) false
      else if i.val=SB a+10 then UnaryTemplate.tape q
      else if i.val=T a then List.replicate C false else []:=by
  refine Fin.addCases (m:=CT a) (n:=1) (fun j=>?_) (fun j=>?_) i
  · refine Fin.addCases (m:=T a) (n:=1) (fun k=>?_) (fun k=>?_) j
    · refine Fin.addCases (m:=SB a) (n:=12) (fun l=>?_) (fun l=>?_) k
      · have hl:=l.isLt
        simp (disch:=omega) [Prelude.inputTapes,loopInA,loggedTapes,loopTapes]
      · fin_cases l <;> simp [Prelude.inputTapes,loopInA,loggedTapes,loopTapes,T]
    · have hk:=Fin.eq_zero k
      subst k
      simp [Prelude.inputTapes,loopInA,loggedTapes,T]
  · have hj:=Fin.eq_zero j
    subst j
    simp [Prelude.inputTapes,CT,T]
    have hsb:SB a=Call.tapes a+11:=by rfl
    split_ifs <;> first | rfl | omega

theorem erase_heads (pos:ℕ) (j:Fin (SB a+4)):heads a pos (eraseSlots a j)=0:=by
  rw [heads,erase_value]
  have hj:=j.isLt
  dsimp only [T]
  split_ifs <;> omega

theorem erase_source (P q:ℕ) (source:List Bool) (A:Fin (tapes a)→List Bool)
    (ha:∀i:Fin (Base a),A (old a i)=
      if i=live a (drv a) then List.replicate (SourceEnvelope.capacity a P) true
      else data a P q source (old a i)) (j:Fin (SB a+4)):
    A (eraseSlots a j)=eraseInput a (SourceEnvelope.capacity a P) j:=by
  have hj:=j.isLt
  unfold eraseSlots
  split_ifs with h0 h1 h2 h3
  all_goals change A (old a _) = _
  all_goals rw [ha]
  all_goals simp (disch:=omega) [eraseInput,data,old,live,drv,fcp,wsp,bk,ex,Base,CT,T,
    Prelude.logSlot,Fin.ext_iff]
  all_goals first | omega | (split_ifs <;> first | rfl | omega)

theorem erase_run (P q pos:ℕ) (source:List Bool) (A:Fin (tapes a)→List Bool)
    (ha:∀i:Fin (Base a),A (old a i)=
      if i=live a (drv a) then List.replicate (SourceEnvelope.capacity a P) true
      else data a P q source (old a i)):
    ∃O,Step (eraseMachine a) (2*SourceEnvelope.capacity a P+4)
      (heads a pos) A (heads a pos) O ∧
      ∀i:Fin (Base a),O (old a i)=Prelude.inputTapes a (SourceEnvelope.capacity a P) q source i:=by
  let C:=SourceEnvelope.capacity a P
  have run:=(erase_step a C).dock (eraseSlots a) (erase_injective a) (heads a pos) A
    (erase_heads a pos) (erase_source a P q source A ha)
  refine ⟨install (eraseSlots a) A (eraseOutput a C),
    run.congr (dockH_existing _ _ _ (erase_heads a pos)) rfl,?_⟩
  intro i
  rw [input_value]
  cases hp:RecoveryFocus.pick (eraseSlots a) (old a i) with
  | some j=>
    have he:=RecoveryFocus.slot_of_pick (eraseSlots a) hp
    have hv:=congrArg (fun x:Fin (tapes a)=>x.val) he
    rw [erase_value] at hv
    simp only [old,Fin.val_castAdd] at hv
    rw [←he,install_slot _ (erase_injective a)]
    have hj:=j.isLt
    simp only [eraseOutput]
    dsimp only [T] at *
    split_ifs at hv ⊢ <;> first | rfl | omega
  | none=>
    have hout:∀j,eraseSlots a j≠old a i:=by
      intro j he
      have h:=RecoveryFocus.pick_slot (eraseSlots a) (erase_injective a) j
      rw [he,hp] at h
      contradiction
    rw [install_other _ _ _ _ hout,ha]
    have hi:=i.isLt
    have notbank:¬i.val<SB a:=by
      intro h
      apply hout ⟨i.val,by omega⟩
      apply Fin.ext
      rw [erase_value]
      simp [h,old]
    have fcp':i.val≠SB a+7:=by
      intro h;apply hout ⟨SB a,by omega⟩;apply Fin.ext
      simp [erase_value,old,h]
    have log':i.val≠T a:=by
      intro h;apply hout ⟨SB a+1,by omega⟩;apply Fin.ext
      simp [erase_value,old,h]
    have drv':i.val≠SB a+8:=by
      intro h;apply hout ⟨SB a+2,by omega⟩;apply Fin.ext
      simp [erase_value,old,h]
    have wsp':i.val≠SB a+9:=by
      intro h;apply hout ⟨SB a+3,by omega⟩;apply Fin.ext
      simp [erase_value,old,h]
    have ne:i≠live a (drv a):=by
      intro h;apply drv';exact congrArg Fin.val h
    simp only [if_neg ne,if_neg notbank,if_neg fcp',if_neg drv',if_neg wsp',if_neg log']
    simp [data,old,show i.val≠Base a by omega]

end NearCubicWires.ExtDecompositionBatch.Cold

/-! Paid cold allocation and native cursor return provide exactly the existing
batch entry. Only source bytes, the actual parser bound and domain enter live. -/
namespace NearCubicWires.ExtDecompositionBatch.Cold
open LocalBitMultitape RepairOrdinary RepairRepresentation ExecutableInterfaces
open RepairOrdinary.DecompositionSource RepairOrdinary.RecoveryRootRound
open RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
variable (a : DecompositionAlgorithm)

def rewindSlots:Fin 3→Fin (tapes a):=![port a (str a),port a (drv a),port a (wsp a)]
noncomputable def rewindMachine:=RecoveryFocus.machine (rewindSlots a) CompetitorRecordRewind.machine
noncomputable def entryMachine:=Composition.machine (allocationMachine a) (rewindMachine a)
def entryBudget (P:ℕ):=DimensionPolynomial.budget (SourceEnvelope.degree a)
  (SourceEnvelope.coefficient a) P+1+(2*SourceEnvelope.capacity a P+4)+1+
  (2*SourceEnvelope.capacity a P+2)

theorem rewind_injective:Function.Injective (rewindSlots a):=by
  intro i j h
  have hv:=congrArg (fun k:Fin (tapes a)=>k.val) h
  fin_cases i <;> fin_cases j <;> first | rfl |
    (simp [rewindSlots,port,old,live,str,drv,wsp,ex] at hv)

theorem rewind_heads (pos:ℕ):dockH (rewindSlots a) (heads a pos) ![0,0,0]=heads a 0:=by
  funext i
  cases hp:RecoveryFocus.pick (rewindSlots a) i with
  | some j=>
    have he:=RecoveryFocus.slot_of_pick (rewindSlots a) hp
    rw [←he,dockH_slot _ (rewind_injective a)]
    fin_cases j <;> simp [rewindSlots,heads,port,old,live,str,drv,wsp,ex]
  | none=>
    have hout:∀j,rewindSlots a j≠i:=by
      intro j he
      have h:=RecoveryFocus.pick_slot (rewindSlots a) (rewind_injective a) j
      rw [he,hp] at h
      contradiction
    rw [dockH_other _ _ _ _ hout]
    have hn:i.val≠SB a:=by
      intro h;apply hout 0;apply Fin.ext
      exact h.symm
    simp [heads,hn]

theorem entry_heads (i:Fin (Base a)):heads a 0 (old a i)=Prelude.inputHeads a i:=by
  refine Fin.addCases (m:=CT a) (n:=1) (fun j=>?_) (fun j=>?_) i
  · refine Fin.addCases (m:=T a) (n:=1) (fun k=>?_) (fun k=>?_) j
    · refine Fin.addCases (m:=SB a) (n:=12) (fun l=>?_) (fun l=>?_) k
      · have hl:=l.isLt
        simp [heads,old,Prelude.inputHeads,OccurrenceTemplate.heads,loopInH,loopHeads]
        omega
      · fin_cases l <;> simp [heads,old,Prelude.inputHeads,OccurrenceTemplate.heads,loopInH,loopHeads]
    · have hk:=Fin.eq_zero k
      subst k
      simp [heads,old,Prelude.inputHeads,OccurrenceTemplate.heads,loopInH,T]
  · have hj:=Fin.eq_zero j
    subst j
    simp [heads,old,Prelude.inputHeads,OccurrenceTemplate.heads,CT,T]

theorem entry_run (P q pos:ℕ) (source:List Bool) (hp:pos≤SourceEnvelope.capacity a P):
    ∃O,Step (entryMachine a) (entryBudget a P)
      (heads a pos) (data a P q source) (heads a 0) O ∧
      ∀i:Fin (Base a),O (old a i)=Prelude.inputTapes a (SourceEnvelope.capacity a P) q source i:=by
  obtain ⟨A,power,pa⟩:=power_run a P q pos source
  obtain ⟨O,erase,oa⟩:=erase_run a P q pos source A pa
  have rewind:=CacheRewind.rewind_dock (rewindSlots a) (rewind_injective a)
    (heads a pos) O (SourceEnvelope.capacity a P)
    (by simpa [rewindSlots,heads,port,old,live,str,ex] using hp)
    (by simp [rewindSlots,heads,port,old,live,drv,ex])
    (by simp [rewindSlots,heads,port,old,live,wsp,ex])
    (by change O (old a (live a (drv a)))=_
        rw [oa,input_value]
        simp [live,drv,ex])
    (by change O (old a (live a (wsp a)))=_
        rw [oa,input_value]
        simp [live,wsp,ex])
  exact ⟨O,((power.seq erase).seq rewind).congr (rewind_heads a pos) rfl,oa⟩

end NearCubicWires.ExtDecompositionBatch.Cold

/-! Both actual append cursors fit the same upstream source capacity. -/
namespace NearCubicWires.ExtDecompositionBatch.SourceEnvelope
open RepairOrdinary RepairRepresentation ExecutableInterfaces SupplierPipeline
open RepairOrdinary.DecompositionSource RepairOrdinary.CloseoutRowsCircuitBottom
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem source_position (a:DecompositionAlgorithm) {q:ℕ}
    (occ:List (SupportedNormalizedGate q)) (top:List Bool) (P:ℕ)
    (hi:(segment occ top).length≤1000*(P+2)^2):
    (segment occ top).length≤capacity a P:=by
  have hscale:=Nat.pow_le_pow_left (show P+2≤2*(P+1) by omega) 2
  have size:(segment occ top).length≤ inputBound P:=by
    unfold inputBound
    nlinarith only [hi,hscale]
  have large:=input_le a P
  have cap:=capacity_covers a P
  nlinarith

theorem counts_length (a:DecompositionAlgorithm) {q:ℕ} (occ:List (SupportedNormalizedGate q)):
    (countWord a occ).length≤2*B a occ+3*occ.length:=by
  induction occ with
  | nil=>simp [countWord,counts,B,GS]
  | cons g occ ih=>
    have bits:=CapacityBounds.bit_length (children a g).length
    simp only [countWord,counts_cons,List.flatMap_cons,List.length_append,natWord_length,
      B_cons,List.length_cons]
    change 2*natBitLength (children a g).length+1+(countWord a occ).length≤_
    omega

theorem count_position (a:DecompositionAlgorithm) {q:ℕ}
    (occ:List (SupportedNormalizedGate q)) (top:List Bool) (P:ℕ)
    (hq:q≤P) (hi:(segment occ top).length≤1000*(P+2)^2):
    (countWord a occ).length≤capacity a P:=by
  obtain ⟨_,n,b,_,_⟩:=actual_bounds a occ top P hq hi
  have count:=counts_length a occ
  have cap:=capacity_covers a P
  nlinarith

end NearCubicWires.ExtDecompositionBatch.SourceEnvelope

/-! The whole actual parent: manufacture C, allocate and rewind, then execute
the unchanged ordered batch. No child/cache/count data is supplied as input. -/
namespace NearCubicWires.ExtDecompositionBatch.Cold
open LocalBitMultitape RepairOrdinary RepairRepresentation ExecutableInterfaces
open RepairOrdinary.DecompositionSource RepairOrdinary.RecoveryRootRound SupplierPipeline
open RepairOrdinary.CloseoutRowsCircuitBottom
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
variable (a:DecompositionAlgorithm)

theorem old_injective:Function.Injective (old a):=by
  intro i j h
  exact Fin.ext (congrArg (fun k:Fin (tapes a)=>k.val) h)
noncomputable def batch:=RecoveryFocus.machine (old a) (batchMachine a)
noncomputable def machine:=Composition.machine (entryMachine a) (batch a)
def budget {q:ℕ} (P:ℕ) (occ:List (SupportedNormalizedGate q)) (top:List Bool):=
  entryBudget a P+1+batchBudget a (SourceEnvelope.capacity a P) occ top

theorem cold_run {q:ℕ} (P:ℕ) (occ:List (SupportedNormalizedGate q)) (top:List Bool)
    (hq:q≤P) (hi:(segment occ top).length≤1000*(P+2)^2):
    ∃H O,Step (machine a) (budget a P occ top)
      (heads a (segment occ top).length) (data a P q (segment occ top)) H O ∧
      O (port a (cch a))=exactListWord (GS a occ) ∧ H (port a (cch a))=0 ∧
      O (port a (cnt a))=countWord a occ ∧ H (port a (cnt a))=(countWord a occ).length ∧
      O (port a (str a))=segment occ top ∧ H (port a (str a))=(segment occ top).length ∧
      O (port a (tot a))=UnaryTemplate.tape (B a occ) ∧ H (port a (tot a))=1 ∧
      O (port a (dom a))=UnaryTemplate.tape q ∧ H (port a (dom a))=1 ∧
      O (port a (scr a))=List.replicate (B a occ) false ∧ H (port a (scr a))=0 ∧
      O (port a (drv a))=List.replicate (SourceEnvelope.capacity a P) true ∧ H (port a (drv a))=0 ∧
      O (port a (wsp a))=List.replicate (SourceEnvelope.capacity a P+1) false ∧ H (port a (wsp a))=0:=by
  obtain ⟨A,entry,ea⟩:=entry_run a P q (segment occ top).length (segment occ top)
    (SourceEnvelope.source_position a occ top P hi)
  obtain ⟨body,hn,hh,hb,hc,header⟩:=SourceEnvelope.actual_capacity a occ top P hq hi
  obtain ⟨H,O,run,post⟩:=batch_run a (SourceEnvelope.capacity a P) occ top header body hn hh hb hc
  have worker:=run.dock (old a) (old_injective a) (heads a 0) A (entry_heads a) ea
  refine ⟨_,_,entry.seq worker,?_⟩
  simpa only [port,install_slot _ (old_injective a),dockH_slot _ (old_injective a)] using post

end NearCubicWires.ExtDecompositionBatch.Cold
