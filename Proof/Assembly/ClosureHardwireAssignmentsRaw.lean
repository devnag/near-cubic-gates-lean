import Proof.Assembly.ClosureHardwireCacheLoop
import Proof.Assembly.ClosureBinaryEnumeratorMask

/-! One real assignment callback before global restoration. Decode the
framed assignment, scatter its frozen mask, reload the child workspace,
skip the cache's native count header, and execute the complete child loop.
The ordinary machine is fixed; assignments and dimensions are runtime data.
-/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.HardwireAssignmentsRaw
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch RecoveryRootRound
open RepairRepresentation RepairSource CloseoutFinal SupplierPipeline SupplierEstimator
open VerifierDecoding CanonicalRecoveryLanguage SignedSortKey
open scoped BigOperators

def old (i : Fin 98) : Fin 112 := ((i.castAdd 5).castAdd 1).castAdd 8
def loopSlots (i : Fin 104) : Fin 112 := i.castAdd 8
def decodeSlots : Fin 3 → Fin 112 := ![104,106,107]
def maskSlots : Fin 5 → Fin 112 := ![92,106,86,108,109]
def headerSlots : Fin 3 → Fin 112 := ![98,110,111]
theorem old_injective : Function.Injective old := by
  intro i j h;exact Fin.ext (congrArg (fun x : Fin 112=>x.val) h)
theorem loopSlots_injective : Function.Injective loopSlots := by
  intro i j h;exact Fin.ext (congrArg (fun x : Fin 112=>x.val) h)
theorem decodeSlots_injective : Function.Injective decodeSlots := by decide
theorem maskSlots_injective : Function.Injective maskSlots := by decide
theorem headerSlots_injective : Function.Injective headerSlots := by decide

def heads (out : List Bool) (up : Bool) (i : Fin 112) : Nat :=
  if i=34 then out.length else if up ∧ (i=100 ∨ i=103 ∨ i=108) then 1 else 0
def directions (i : Fin 112) : HeadMove := if i=100 ∨ i=103 ∨ i=108 then .right else .stay
def advance := DecompositionCountPosition.move directions
noncomputable def decode := RecoveryFocus.machine decodeSlots Streaming.machine
noncomputable def scatter := RecoveryFocus.machine maskSlots FrozenMask.readyMachine
noncomputable def reload := RecoveryFocus.machine old HardwireReusable.restore
noncomputable def counters := RecoveryFocus.machine old (HardwireReusable.move true)
noncomputable def header := RecoveryFocus.machine headerSlots (PCPPQueryField.machine false)
noncomputable def scan := RecoveryFocus.machine loopSlots HardwireCacheLoop.machine
noncomputable def first := Composition.machine (Composition.machine advance decode) scatter
noncomputable def prepared := Composition.machine (Composition.machine first reload) counters
noncomputable def machine := Composition.machine (Composition.machine prepared header) scan

variable {q : Nat} (live : Finset (Fin q)) (gs : List (ExactThresholdGate q)) (B w cap : Nat)

noncomputable def baseline (framed out : List Bool) : Fin 112 → List Bool :=
  Fin.addCases (motive:=fun _=>List Bool)
    (RepeatMachine.cfg 0 (HardwireCacheLoop.entry live (fun _=>false) gs B w 0 out) gs.length 1).tapes
    (![framed,List.replicate cap false,List.replicate live.card false,List.replicate live.card false,
      CompareMachine.word q,List.replicate (4*q+3) false,[],[]] : Fin 8 → List Bool)
noncomputable def decoded (j : Nat) (out : List Bool) := install decodeSlots
  (baseline live gs B w cap (RepairOrdinary.frame (binary live.card j)) out)
  ![RepairOrdinary.frame (binary live.card j),List.ofFn (bitInputOfCode live.card j),List.replicate live.card false]
noncomputable def scattered (j : Nat) (out : List Bool) := install maskSlots
  (decoded live gs B w cap j out)
  ![CloseoutRowsGateSupport.gateMembers live,List.ofFn (bitInputOfCode live.card j),
    List.ofFn (C10NaturalHardwireScore.frozenMask live (bitInputOfCode live.card j)),
    CompareMachine.word q,List.replicate (4*q+3) false]

theorem frozen_zero : List.ofFn (C10NaturalHardwireScore.frozenMask live (fun _=>false))=
    List.replicate q false := by
  have hz : C10NaturalHardwireScore.frozenMask live (fun _=>false)=(fun _=>false) := by
    funext i
    obtain ⟨s,rfl⟩ := (normalizedLiveExternalCoordinateEquiv live).surjective i
    cases s <;> exact C10SupplierRowInput.joinInput_coord live (fun _=>false) (fun _=>false) _
  rw [hz]
  exact List.ofFn_const q false

theorem masters_other (y z : BitInput live.card) (j : Fin 47) (hj : j≠38) :
    HardwireCacheBody.masters live y [] w (HardwireBudget.C w) (HardwireBudget.D q w)
      (HardwireBudget.E B q) [] j =
    HardwireCacheBody.masters live z [] w (HardwireBudget.C w) (HardwireBudget.D q w)
      (HardwireBudget.E B q) [] j := by
  fin_cases j <;> first | rfl | exact False.elim (hj rfl)

theorem masters_fit (y : BitInput live.card) :
    ∀ j,(HardwireCacheBody.masters live y [] w (HardwireBudget.C w) (HardwireBudget.D q w)
      (HardwireBudget.E B q) [] j).length≤HardwireBudget.R B q w := by
  have square : B+q+w+1≤(B+q+w+1)^2 := Nat.le_self_pow (by decide) _
  have hc : HardwireBudget.C w+1≤HardwireBudget.R B q w := by unfold HardwireBudget.C HardwireBudget.R;omega
  have hd : HardwireBudget.D q w≤HardwireBudget.R B q w := by unfold HardwireBudget.D HardwireBudget.C HardwireBudget.R;nlinarith
  have he : HardwireBudget.E B q≤HardwireBudget.R B q w := by unfold HardwireBudget.E HardwireBudget.R;omega
  have hq : q+1≤HardwireBudget.R B q w := by unfold HardwireBudget.R;omega
  have hw : 2*w+1≤HardwireBudget.R B q w := by unfold HardwireBudget.R;omega
  intro j
  fin_cases j <;>
    simp [HardwireCacheBody.masters,HardwireCacheBody.native,HardwireReusable.work,HardwireChild.extra,
      C10NaturalHardwireScoreInputs.data,C10NaturalHardwireScoreInputs.extra,
      C10NaturalHardwireTarget.input,C10NaturalHardwireTarget.pairInput,C10NaturalHardwireTarget.pairExtra,
      C10NaturalHardwireTarget.extra,CloseoutRowsPoolMagnitude.input,CloseoutRowsGateSupport.gateMembers,
      Fin.addCases,MatrixScoreWeight.scalar,ZeroPadding.pad_length,
      frame_length,binary_length,List.length_replicate,List.length_ofFn,CompareMachine.word,List.length_cons] <;> omega

theorem baseline_old (framed out : List Bool) (i : Fin 98) :
    baseline live gs B w cap framed out (old i)=
      HardwireCacheBody.localState live (fun _=>false) [] w (HardwireBudget.C w)
        (HardwireBudget.D q w) (HardwireBudget.E B q) [] [] out (HardwireBudget.R B q w) i := by
  simp only [baseline,old,HardwireCacheLoop.entry,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,
    HardwireCacheLoop.state,HardwireCacheBody.state,Fin.addCases_left,HardwireCacheLoop.heldSource]
  rfl

theorem decoded_old (j : Nat) (out : List Bool) (i : Fin 98) :
    decoded live gs B w cap j out (old i)=baseline live gs B w cap (RepairOrdinary.frame (binary live.card j)) out (old i) := by
  apply install_other
  intro k
  have ho : (old i).val<98 := i.isLt
  have hk : 104≤(decodeSlots k).val := by fin_cases k <;> decide
  intro h
  have := congrArg Fin.val h
  omega

theorem advance_run (out : List Bool) (A : Fin 112 → List Bool) :
    Step advance 1 (heads out false) A (heads out true) A := by
  obtain ⟨r,hr,hf,_⟩ := DecompositionCountPosition.move_run directions (heads out false) A
  apply Step.of_run hr
  · rw [hf]
    funext i
    by_cases h34 : i=34
    · subst i;rfl
    · by_cases h : i=100 ∨ i=103 ∨ i=108 <;> simp [heads,directions,h34,h,HeadMove.apply]
  · rw [hf]

theorem decode_run (j : Nat) (out : List Bool) :
    Step decode (4*live.card+2) (heads out true)
      (baseline live gs B w cap (RepairOrdinary.frame (binary live.card j)) out)
      (heads out true) (decoded live gs B w cap j out) := by
  have actual := (BinaryEnumerator.assignment_run live.card j).focus decodeSlots decodeSlots_injective
    (heads out true) (baseline live gs B w cap (RepairOrdinary.frame (binary live.card j)) out)
  have hh : ∀ i,heads out true (decodeSlots i)=0 := by intro i;fin_cases i <;> rfl
  have ht : ∀ i,baseline live gs B w cap (RepairOrdinary.frame (binary live.card j)) out (decodeSlots i)=
      (![RepairOrdinary.frame (binary live.card j),List.replicate live.card false,List.replicate live.card false] : Fin 3→List Bool) i := by
    intro i;fin_cases i <;> rfl
  exact (actual.congr_in (dockH_existing _ _ _ hh) (install_existing _ _ _ ht)).congr
    (dockH_existing _ _ _ hh) rfl

theorem scatter_input (j : Nat) (out : List Bool) (i : Fin 5) :
    decoded live gs B w cap j out (maskSlots i)=
      (![CloseoutRowsGateSupport.gateMembers live,List.ofFn (bitInputOfCode live.card j),
        List.replicate q false,CompareMachine.word q,List.replicate (4*q+3) false] : Fin 5→List Bool) i := by
  fin_cases i
  · change decoded live gs B w cap j out 92=CloseoutRowsGateSupport.gateMembers live
    rw [decoded,install_other decodeSlots _ _ 92 (by decide)]
    rfl
  · exact install_slot decodeSlots decodeSlots_injective _ _ 1
  · change decoded live gs B w cap j out 86=List.replicate q false
    rw [decoded,install_other decodeSlots _ _ 86 (by decide)]
    exact frozen_zero live
  · change decoded live gs B w cap j out 108=CompareMachine.word q
    rw [decoded,install_other decodeSlots _ _ 108 (by decide)]
    rfl
  · change decoded live gs B w cap j out 109=List.replicate (4*q+3) false
    rw [decoded,install_other decodeSlots _ _ 109 (by decide)]
    rfl

theorem scatter_run (j : Nat) (out : List Bool) :
    Step scatter (8*q+8) (heads out true) (decoded live gs B w cap j out)
      (heads out true) (scattered live gs B w cap j out) := by
  have hh : ∀ i,heads out true (maskSlots i)=(![0,0,0,1,0] : Fin 5→Nat) i := by
    intro i;fin_cases i <;> rfl
  have actual := (BinaryEnumerator.frozen_mask_run live (bitInputOfCode live.card j) (4*q+3) le_rfl).focus
    maskSlots maskSlots_injective (heads out true) (decoded live gs B w cap j out)
  exact (actual.congr_in (dockH_existing _ _ _ hh)
    (install_existing _ _ _ (scatter_input live gs B w cap j out))).congr (dockH_existing _ _ _ hh) rfl

noncomputable def core (y : BitInput live.card) (out : List Bool) :=
  HardwireCacheBody.localState live y [] w (HardwireBudget.C w) (HardwireBudget.D q w)
    (HardwireBudget.E B q) [] [] out (HardwireBudget.R B q w)
noncomputable def mixed (y : BitInput live.card) (out : List Bool) :=
  HardwireReusable.state
    (HardwireCacheBody.padded live (fun _=>false) [] w (HardwireBudget.C w) (HardwireBudget.D q w)
      (HardwireBudget.E B q) [] out (HardwireBudget.R B q w))
    (HardwireCacheBody.masters live y [] w (HardwireBudget.C w) (HardwireBudget.D q w)
      (HardwireBudget.E B q) []) (HardwireBudget.R B q w)
noncomputable def reloaded (j : Nat) (out : List Bool) :=
  install old (scattered live gs B w cap j out) (core live B w (bitInputOfCode live.card j) out)

theorem mixed_other (y : BitInput live.card) (out : List Bool) (i : Fin 98) (hi : i≠86) :
    mixed live B w y out i=core live B w (fun _=>false) out i := by
  revert hi
  refine Fin.addCases (m:=48) (n:=50) (fun i=>?_) (fun i=>?_) i
  · intro _
    simp only [mixed,core,HardwireCacheBody.localState,HardwireReusable.state,Fin.addCases_left]
  · refine Fin.addCases (m:=47) (n:=3) (fun i=>?_) (fun i=>?_) i
    · intro hi
      simp only [mixed,core,HardwireCacheBody.localState,HardwireReusable.state,
        Fin.addCases_right,Fin.addCases_left]
      exact masters_other live B w y (fun _=>false) i (by intro h;subst i;exact hi rfl)
    · intro _
      simp only [mixed,core,HardwireCacheBody.localState,HardwireReusable.state,
        Fin.addCases_right]

theorem scattered_old (j : Nat) (out : List Bool) (i : Fin 98) :
    scattered live gs B w cap j out (old i)=mixed live B w (bitInputOfCode live.card j) out i := by
  by_cases h86 : i=86
  · subst i
    exact install_slot maskSlots maskSlots_injective _ _ 2
  by_cases h92 : i=92
  · subst i
    exact install_slot maskSlots maskSlots_injective _ _ 0
  · have outside : ∀ i : Fin 98,i≠86 → i≠92 → ∀ k,maskSlots k≠old i := by decide
    rw [scattered,install_other _ _ _ _ (outside i h86 h92),decoded_old,baseline_old]
    exact (mixed_other live B w (bitInputOfCode live.card j) out i h86).symm

theorem heads_old (out : List Bool) (i : Fin 98) :
    heads out true (old i)=HardwireReusable.heads out 0 i := by
  have outside : ∀ i : Fin 98,old i≠100 ∧ old i≠103 ∧ old i≠108 := by decide
  have he : old i=34 ↔ i=34 := by
    constructor
    · intro h;exact Fin.ext (congrArg (fun x : Fin 112=>x.val) h)
    · intro h;subst i;rfl
  simp [heads,HardwireReusable.heads,he,(outside i).1,(outside i).2.1,(outside i).2.2]

theorem reload_run (j : Nat) (out : List Bool) :
    Step reload (4*HardwireBudget.R B q w+9) (heads out true) (scattered live gs B w cap j out)
      (heads out true) (reloaded live gs B w cap j out) := by
  have hd : ∀ k,(HardwireCacheBody.padded live (fun _=>false) [] w (HardwireBudget.C w)
      (HardwireBudget.D q w) (HardwireBudget.E B q) [] out (HardwireBudget.R B q w)
      (HardwireReusable.work k)).length≤HardwireBudget.R B q w := by
    intro k
    rw [HardwireCacheBody.padded_work,ZeroPadding.pad_length]
    exact max_le le_rfl (masters_fit live B w (fun _=>false) k)
  have actual := (HardwireReusable.restore_run _ _ _ out (HardwireBudget.R B q w)
    (masters_fit live B w (bitInputOfCode live.card j)) hd
    (HardwireCacheBody.padded_work live (bitInputOfCode live.card j) [] w (HardwireBudget.C w)
      (HardwireBudget.D q w) (HardwireBudget.E B q) [] out (HardwireBudget.R B q w)) rfl).focus
    old old_injective (heads out true) (scattered live gs B w cap j out)
  exact (actual.congr_in (dockH_existing _ _ _ (heads_old out))
    (install_existing _ _ _ (scattered_old live gs B w cap j out))).congr
    (dockH_existing _ _ _ (heads_old out)) rfl

noncomputable def countHeads (out : List Bool) := dockH old (heads out true) (HardwireReusable.heads out 1)
noncomputable def parsedHeads (out : List Bool) := dockH headerSlots (countHeads out)
  (![ (natWord gs.length).length,0,0] : Fin 3 → Nat)
noncomputable def parsed (j : Nat) (out : List Bool) := install headerSlots (reloaded live gs B w cap j out)
  (![exactListWord gs,PCPPQueryField.saved gs.length [],[]] : Fin 3 → List Bool)
noncomputable def loopEntry (y : BitInput live.card) (out : List Bool) :=
  RepeatMachine.cfg 0 (HardwireCacheLoop.entry live y gs B w 0 out) gs.length 1

theorem counters_run (j : Nat) (out : List Bool) :
    Step counters 1 (heads out true) (reloaded live gs B w cap j out)
      (countHeads out) (reloaded live gs B w cap j out) := by
  have actual := (HardwireReusable.move_run true out (core live B w (bitInputOfCode live.card j) out)).focus
    old old_injective (heads out true) (reloaded live gs B w cap j out)
  have ht : ∀ i,reloaded live gs B w cap j out (old i)=core live B w (bitInputOfCode live.card j) out i :=
    install_slot old old_injective _ _
  exact (actual.congr_in (dockH_existing _ _ _ (heads_old out))
    (install_existing _ _ _ ht)).congr rfl (install_existing _ _ _ ht)

theorem reloaded_outside (j : Nat) (out : List Bool) (i : Fin 112)
    (hi : (98 : Nat) ≤ (i : Nat)) (h106 : i≠106) (h107 : i≠107) (h108 : i≠108) (h109 : i≠109) :
    reloaded live gs B w cap j out i=baseline live gs B w cap (RepairOrdinary.frame (binary live.card j)) out i := by
  have ho : ∀ k,old k≠i := by intro k h;have hval:=congrArg Fin.val h;have hk:=k.isLt;change k.val=i.val at hval;omega
  have hm : ∀ k,maskSlots k≠i := by
    intro k h
    have cases : ∀ k,maskSlots k=92 ∨ maskSlots k=106 ∨ maskSlots k=86 ∨ maskSlots k=108 ∨ maskSlots k=109 := by decide
    rcases cases k with hk|hk|hk|hk|hk
    · rw [hk] at h;have hv:=congrArg Fin.val h;change 92=i.val at hv;omega
    · exact h106 (h.symm.trans hk)
    · rw [hk] at h;have hv:=congrArg Fin.val h;change 86=i.val at hv;omega
    · exact h108 (h.symm.trans hk)
    · exact h109 (h.symm.trans hk)
  rw [reloaded,install_other _ _ _ _ ho,scattered,install_other _ _ _ _ hm]
  by_cases h104 : i=104
  · subst i
    exact install_slot decodeSlots decodeSlots_injective _ _ 0
  · apply install_other
    intro k
    fin_cases k <;> intro h <;> first | exact h104 h.symm | exact h106 h.symm | exact h107 h.symm

theorem reloaded_loop (j : Nat) (out : List Bool) (i : Fin 104) :
    reloaded live gs B w cap j out (loopSlots i)= (loopEntry live gs B w (bitInputOfCode live.card j) out).tapes i := by
  refine Fin.addCases (m:=98) (n:=6) (fun i=>?_) (fun i=>?_) i
  · change reloaded live gs B w cap j out (old i)=
      (loopEntry live gs B w (bitInputOfCode live.card j) out).tapes ((i.castAdd 5).castAdd 1)
    simp only [loopEntry,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,HardwireCacheLoop.entry,
      HardwireCacheLoop.state,HardwireCacheBody.state,Fin.addCases_left,HardwireCacheLoop.heldSource]
    exact install_slot old old_injective _ _ i
  · have ho : 98≤(loopSlots (i.natAdd 98)).val := by change 98≤98+i.val;omega
    have hn : loopSlots (i.natAdd 98)≠106 ∧ loopSlots (i.natAdd 98)≠107 ∧
        loopSlots (i.natAdd 98)≠108 ∧ loopSlots (i.natAdd 98)≠109 := by fin_cases i <;> decide
    rw [reloaded_outside live gs B w cap j out _ ho hn.1 hn.2.1 hn.2.2.1 hn.2.2.2]
    simp only [baseline,loopSlots,Fin.addCases_left]
    refine Fin.addCases (m:=5) (n:=1) (fun i=>?_) (fun i=>?_) i
    · change (RepeatMachine.cfg 0 (HardwireCacheLoop.entry live (fun _=>false) gs B w 0 out) gs.length 1).tapes
        ((i.natAdd 98).castAdd 1)=
        (loopEntry live gs B w (bitInputOfCode live.card j) out).tapes ((i.natAdd 98).castAdd 1)
      simp only [loopEntry,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,HardwireCacheLoop.entry,
        HardwireCacheLoop.state,HardwireCacheBody.state,Fin.addCases_left,Fin.addCases_right]
    · fin_cases i
      rfl

theorem header_input (j : Nat) (out : List Bool) (i : Fin 3) :
    reloaded live gs B w cap j out (headerSlots i)=(![exactListWord gs,[],[]] : Fin 3→List Bool) i := by
  fin_cases i
  · exact reloaded_loop live gs B w cap j out 98
  · exact reloaded_outside live gs B w cap j out 110 (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact reloaded_outside live gs B w cap j out 111 (by decide) (by decide) (by decide) (by decide) (by decide)

theorem header_heads (out : List Bool) (i : Fin 3) : countHeads out (headerSlots i)=0 := by
  have hh : ∀ i : Fin 3,∀ k,old k≠headerSlots i := by decide
  rw [countHeads,dockH_other _ _ _ _ (hh i)]
  fin_cases i <;> rfl

theorem header_run (j : Nat) (out : List Bool) :
    Step header (2*natBitLength gs.length+3) (countHeads out) (reloaded live gs B w cap j out)
      (parsedHeads gs out) (parsed live gs B w cap j out) := by
  obtain ⟨r,hr,hf,_⟩ := PCPPQueryField.nat_run false [] (gs.flatMap exactWord) [] [] gs.length
  have skip : Step (PCPPQueryField.machine false) (2*natBitLength gs.length+3)
      (![0,0,0] : Fin 3→Nat) (![exactListWord gs,[],[]] : Fin 3→List Bool)
      (![ (natWord gs.length).length,0,0] : Fin 3→Nat)
      (![exactListWord gs,PCPPQueryField.saved gs.length [],[]] : Fin 3→List Bool) := by
    apply Step.of_run hr
    · rw [hf]
      funext i
      fin_cases i <;> simp [PCPPQueryField.payload,PCPPQueryField.cfg,PCPPQueryField.selected,
        DecompositionSource.natWord_length]
    · rw [hf];rfl
  have actual := skip.focus headerSlots headerSlots_injective (countHeads out) (reloaded live gs B w cap j out)
  exact actual.congr_in (dockH_existing _ _ _ (by intro i;rw [header_heads];fin_cases i <;> rfl))
    (install_existing _ _ _ (header_input live gs B w cap j out))

theorem parsed_loop (j : Nat) (out : List Bool) (i : Fin 104) :
    parsed live gs B w cap j out (loopSlots i)=(loopEntry live gs B w (bitInputOfCode live.card j) out).tapes i := by
  by_cases h98 : i=98
  · subst i
    exact install_slot headerSlots headerSlots_injective _ _ 0
  · have hi : ∀ k,headerSlots k≠loopSlots i := by
      intro k
      fin_cases k <;> intro h
      · apply h98;exact Fin.ext (congrArg (fun x : Fin 112=>x.val) h.symm)
      · have hv:=congrArg Fin.val h;change 110=i.val at hv;have:=i.isLt;omega
      · have hv:=congrArg Fin.val h;change 111=i.val at hv;have:=i.isLt;omega
    rw [parsed,install_other _ _ _ _ hi,reloaded_loop]

theorem countHeads_loop (out : List Bool) (i : Fin 104) :
    countHeads out (loopSlots i)=
      Fin.addCases (HardwireReusable.heads out 1) (![0,0,1,0,0,1] : Fin 6→Nat) i := by
  refine Fin.addCases (m:=98) (n:=6) (fun i=>?_) (fun i=>?_) i
  · simp only [Fin.addCases_left]
    exact dockH_slot old old_injective _ _ i
  · have hi : ∀ k,old k≠loopSlots (i.natAdd 98) := by
      intro k h
      have hv:=congrArg Fin.val h
      change k.val=98+i.val at hv
      have:=k.isLt;omega
    rw [countHeads,dockH_other _ _ _ _ hi]
    fin_cases i <;> rfl

theorem parsed_heads (y : BitInput live.card) (out : List Bool) (i : Fin 104) :
    parsedHeads gs out (loopSlots i)=(loopEntry live gs B w y out).heads i := by
  by_cases h98 : i=98
  · subst i
    have h:=dockH_slot headerSlots headerSlots_injective (countHeads out)
      (![ (natWord gs.length).length,0,0] : Fin 3→Nat) 0
    change parsedHeads gs out (loopSlots 98)=(HardwireCacheLoop.sourcePrefix gs 0).length
    simp only [HardwireCacheLoop.sourcePrefix,List.take_zero,List.flatMap_nil,List.append_nil]
    exact h
  · have hi : ∀ k,headerSlots k≠loopSlots i := by
      intro k
      fin_cases k <;> intro h
      · apply h98;exact Fin.ext (congrArg (fun x : Fin 112=>x.val) h.symm)
      · have hv:=congrArg Fin.val h;change 110=i.val at hv;have:=i.isLt;omega
      · have hv:=congrArg Fin.val h;change 111=i.val at hv;have:=i.isLt;omega
    rw [parsedHeads,dockH_other _ _ _ _ hi,countHeads_loop]
    revert h98
    refine Fin.addCases (m:=98) (n:=6) (fun i=>?_) (fun i=>?_) i
    · intro _
      change Fin.addCases (HardwireReusable.heads out 1) (![0,0,1,0,0,1] : Fin 6→Nat) (i.castAdd 6)=
        (loopEntry live gs B w y out).heads ((i.castAdd 5).castAdd 1)
      simp only [loopEntry,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,HardwireCacheLoop.entry,
        HardwireCacheBody.heads,Fin.addCases_left]
    · intro h98
      fin_cases i <;> first | rfl | exact False.elim (h98 rfl)

noncomputable def emitted (j : Nat) :=
  gs.flatMap (fun g=>exactWord (C10SupplierRowInput.hardwire live g (bitInputOfCode live.card j)))
noncomputable def finished (j : Nat) (out : List Bool) :=
  RepeatMachine.cfg 3 (HardwireCacheLoop.entry live (bitInputOfCode live.card j) gs B w gs.length
    (out++emitted live gs j)) gs.length 1
noncomputable def finalHeads (j : Nat) (out : List Bool) :=
  dockH loopSlots (parsedHeads gs out) (finished live gs B w j out).heads
noncomputable def finalTapes (j : Nat) (out : List Bool) :=
  install loopSlots (parsed live gs B w cap j out) (finished live gs B w j out).tapes
def budget := HardwireCacheLoop.budget gs B w+4*HardwireBudget.R B q w+4*live.card+
  8*q+2*natBitLength gs.length+30

theorem scan_run (hbytes : ∀ g∈gs,(exactWord g).length+2≤B) (hw : 0<w)
    (hm : ∀ g∈gs,g.target.natAbs+(∑ i,(g.weight i).natAbs)<2^w) (j : Nat) (out : List Bool) :
    Step scan (HardwireCacheLoop.budget gs B w) (parsedHeads gs out) (parsed live gs B w cap j out)
      (finalHeads live gs B w j out) (finalTapes live gs B w cap j out) := by
  obtain ⟨r,hr,hf,_⟩ := HardwireCacheLoop.run live (bitInputOfCode live.card j) gs B w hbytes hw hm out
  have actual := (Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)).focus
    loopSlots loopSlots_injective (parsedHeads gs out) (parsed live gs B w cap j out)
  exact actual.congr_in (dockH_existing _ _ _ (parsed_heads live gs B w (bitInputOfCode live.card j) out))
    (install_existing _ _ _ (parsed_loop live gs B w cap j out))

theorem run (hbytes : ∀ g∈gs,(exactWord g).length+2≤B) (hw : 0<w)
    (hm : ∀ g∈gs,g.target.natAbs+(∑ i,(g.weight i).natAbs)<2^w) (j : Nat) (out : List Bool) :
    Step machine (budget live gs B w) (heads out false)
      (baseline live gs B w cap (RepairOrdinary.frame (binary live.card j)) out)
      (finalHeads live gs B w j out) (finalTapes live gs B w cap j out) := by
  have actual := ((((((advance_run out _).seq (decode_run live gs B w cap j out)).seq
    (scatter_run live gs B w cap j out)).seq (reload_run live gs B w cap j out)).seq
    (counters_run live gs B w cap j out)).seq (header_run live gs B w cap j out)).seq
    (scan_run live gs B w cap hbytes hw hm j out)
  convert actual using 1 <;> first | rfl | unfold budget;omega

theorem final_output_head (j : Nat) (out : List Bool) :
    finalHeads live gs B w j out 34=(out++emitted live gs j).length := by
  exact dockH_slot loopSlots loopSlots_injective _ _ 34

theorem final_output (j : Nat) (out : List Bool) :
    finalTapes live gs B w cap j out 34=out++emitted live gs j := by
  rw [finalTapes,show (34 : Fin 112)=loopSlots 34 from rfl,install_slot _ loopSlots_injective]
  exact ZeroPadding.pad_zero _

theorem final_kept (j : Nat) (out : List Bool) (i : Fin 112) (hi : i=98 ∨ i=104 ∨ i=105) :
    finalTapes live gs B w cap j out i=
      baseline live gs B w cap (RepairOrdinary.frame (binary live.card j)) out i := by
  rcases hi with rfl|rfl|rfl
  · have h := install_slot loopSlots loopSlots_injective (parsed live gs B w cap j out)
      (finished live gs B w j out).tapes 98
    apply h.trans
    change (finished live gs B w j out).tapes (((0 : Fin 5).natAdd 98).castAdd 1)=
      baseline live gs B w cap (RepairOrdinary.frame (binary live.card j)) out
        ((((0 : Fin 5).natAdd 98).castAdd 1).castAdd 8)
    simp only [finished,baseline,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,HardwireCacheLoop.entry,
      HardwireCacheLoop.state,HardwireCacheBody.state,Fin.addCases_left,Fin.addCases_right]
    rfl
  · exact (install_other loopSlots (parsed live gs B w cap j out) (finished live gs B w j out).tapes
      104 (by decide)).trans ((install_other headerSlots _ _ 104 (by decide)).trans
      (reloaded_outside live gs B w cap j out 104 (by decide) (by decide) (by decide) (by decide) (by decide)))
  · exact (install_other loopSlots (parsed live gs B w cap j out) (finished live gs B w j out).tapes
      105 (by decide)).trans ((install_other headerSlots _ _ 105 (by decide)).trans
      (reloaded_outside live gs B w cap j out 105 (by decide) (by decide) (by decide) (by decide) (by decide)))

end NearCubicWires.P1Closure.HardwireAssignmentsRaw
