import Proof.MachineModel.Layout
import Proof.CaseAnalysis.FinalAppendWorkspaceInit
import Proof.CaseAnalysis.FinalCacheAtAdmission
import Proof.CaseAnalysis.FinalGateInput
import Proof.CaseAnalysis.FinalOriginalFrame
import Proof.CaseAnalysis.FinalSeedEngine
import Proof.CaseAnalysis.FinalSupplierCall
import Proof.CaseAnalysis.FinalTailCompose
import Proof.CaseAnalysis.RowsOriginalCount
import Proof.CaseAnalysis.WitnessBoundedFamilySupportLayout
import Proof.CaseAnalysis.WitnessLegalCacheFields
import Proof.Circuits.DecompositionCountPosition

/-! The actual admitted cold/prologue/count/append entry on the selected tape layout.
All local frames are supplied by the same physical executions; the counter stays
parked at head 1. The caller still pays its control branches and loop/suffix. -/

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10AdmittedEntry

open NearCubicWires LocalBitMultitape SourceInterfaces RepairSource RepairRepresentation
open ProjectionNormalization CloseoutWitness CloseoutFinal ExtDecompositionBatch CanonicalWitnessCodec

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

private theorem prologue_input
    (e : Nat)
    (c : Nat)
    (W : Nat)
    (input : List Bool)
    (witness : List Bool)
    (ambient : Fin (c+2+(301+e+96+W)) → List Bool)
    (coldData : Fin (c+2) → List Bool)
    (source : coldData 0=frame input)
    (bits : coldData 1=frame witness)
    (parked : ∀ i : Fin (c+2+(301+e+96+W)),i.val≠0 → i.val≠1 → ambient i=if i.val=216 then [true] else []) :
    let P := 301+e
    let total := (c+2+(301+e+96+W))
    let B := total-1
    let coldSlots : Fin (c+2) → Fin total := fun i =>
      ⟨if i.val<2 then i.val else P+i.val-2,by have := i.isLt; dsimp [total,P]; split_ifs <;> omega⟩
    let preSlots : Fin (218+(60+(e+23))+1) → Fin total := fun i =>
      ⟨if i.val<P then i.val else B,by have := i.isLt; dsimp [total,P,B]; split_ifs <;> omega⟩
    ∀ i, (RecoveryRootRound.install coldSlots ambient coldData) (preSlots i)=C10SupplierCall.bank [] [] [] input witness (fun _ => []) i :=
  open RecoveryRootRound in
  by
    dsimp only
    let P := 301+e
    let total := (c+2+(301+e+96+W))
    let B := total-1
    let coldSlots : Fin (c+2) → Fin total := fun i =>
      ⟨if i.val<2 then i.val else P+i.val-2,by have := i.isLt; dsimp [total,P]; split_ifs <;> omega⟩
    let preSlots : Fin (218+(60+(e+23))+1) → Fin total := fun i =>
      ⟨if i.val<P then i.val else B,by have := i.isLt; dsimp [total,P,B]; split_ifs <;> omega⟩
    have hi : Function.Injective coldSlots := by
      intro i j he
      have hv := congrArg Fin.val he
      have hival := i.isLt
      have hjval := j.isLt
      apply Fin.ext
      dsimp only [coldSlots] at hv
      split_ifs at hv <;> dsimp [P] at * <;> omega
    change ∀ i,install coldSlots ambient coldData (preSlots i)=C10SupplierCall.bank [] [] [] input witness (fun _ => []) i
    intro i
    by_cases h0 : i.val=0
    · have he : i=0 := Fin.ext h0
      subst i
      have map0 : preSlots 0=coldSlots 0 := by
        apply Fin.ext
        dsimp [preSlots,coldSlots,P]
        split_ifs <;> omega
      rw [map0,install_slot coldSlots hi]
      exact source
    by_cases h1 : i.val=1
    · have he : i=1 := Fin.ext h1
      subst i
      have map1 : preSlots 1=coldSlots 1 := by
        apply Fin.ext
        dsimp [preSlots,coldSlots,P]
        simp only [Nat.mod_eq_of_lt (show 1<(218+(60+(e+23))+1) by omega),
          Nat.mod_eq_of_lt (show 1<c+2 by omega)]
        split_ifs <;> omega
      rw [map1,install_slot coldSlots hi]
      exact bits
    have hp0 : (preSlots i).val≠0 := by
      have hv := i.isLt
      dsimp only [preSlots]
      split_ifs <;> dsimp [P,B,total] at * <;> omega
    have hp1 : (preSlots i).val≠1 := by
      have hv := i.isLt
      dsimp only [preSlots]
      split_ifs <;> dsimp [P,B,total] at * <;> omega
    rw [install_other coldSlots ambient coldData (preSlots i) (by
      intro j he
      have hv := congrArg Fin.val he
      have hj := j.isLt
      have hip := i.isLt
      dsimp only [coldSlots,preSlots] at hv
      split_ifs at hv <;> dsimp [P,B,total] at * <;> omega)]
    rw [parked (preSlots i) hp0 hp1]
    have h216 : (preSlots i).val=216 ↔ i.val=216 := by
      have hv := i.isLt
      dsimp only [preSlots]
      split_ifs <;> dsimp [P,B,total] at * <;> omega
    simp only [h216,C10SupplierCall.bank,C10SupplierCall.bankAt,h0,h1,if_false]
    by_cases he : i.val=216
    · simp [he]
    · simp [he]

private theorem prologue_post
    (c : Nat)
    (e : Nat)
    (W : Nat)
    (input : List Bool)
    (bits : List Bool)
    (coldData : Fin (c+2) → List Bool)
    (w : Nat → List Bool)
    (b : Nat)
    (N : Nat) :
    let P := 301+e
    let total := (c+2+(301+e+96+W))
    let B := total-1
    let L := P+c
    let coldSlots : Fin (c+2) → Fin total := fun i =>
      ⟨if i.val<2 then i.val else P+i.val-2,by have := i.isLt; dsimp [total,P]; split_ifs <;> omega⟩
    let preSlots : Fin ((218+(60+(e+23)))+1) → Fin total := fun i =>
      ⟨if i.val<P then i.val else B,by have := i.isLt; dsimp [total,P,B]; split_ifs <;> omega⟩
    let flag : Fin total := ⟨216,by dsimp [total];omega⟩
    let ambient := C10TailCompose.entryOf flag input bits
    let coldExit := RecoveryRootRound.install coldSlots ambient coldData
    let prologueData : Fin ((218+(60+(e+23)))+1) → List Bool := Fin.addCases
      (C10SupplierCall.bank [] (VerifierDecoding.CompareMachine.word 0) (List.replicate b true) input bits w : Fin (218+(60+(e+23))) → List Bool)
      (fun _ : Fin 1 => VerifierDecoding.CompareMachine.word N)
    let post := RecoveryRootRound.install preSlots coldExit prologueData
    let postHeads := dockH preSlots (fun _ => 0)
      (Fin.addCases (fun _ : Fin (218+(60+(e+23))) => 0) (fun _ : Fin 1 => 1))
    (∀ j : Fin (c+2),2≤j.val → post (coldSlots j)=coldData j) ∧
    (∀ v,L≤v.val → v.val<B → post v=[]) ∧
    (∀ i : Fin 278,post ⟨i.val,by have := i.isLt;dsimp [total];omega⟩=
      C10SupplierCall.bank [] (VerifierDecoding.CompareMachine.word 0) (List.replicate b true) input bits w i) ∧
    (∀ v,postHeads v=if v.val=B then 1 else 0) :=
  open RecoveryRootRound ExtDecompositionBatch in
  by
    dsimp only
    let P := 301+e
    let total := (c+2+(301+e+96+W))
    let B := total-1
    let L := P+c
    let coldSlots : Fin (c+2) → Fin total := fun i =>
      ⟨if i.val<2 then i.val else P+i.val-2,by have := i.isLt; dsimp [total,P]; split_ifs <;> omega⟩
    let preSlots : Fin ((218+(60+(e+23)))+1) → Fin total := fun i =>
      ⟨if i.val<P then i.val else B,by have := i.isLt; dsimp [total,P,B]; split_ifs <;> omega⟩
    let flag : Fin total := ⟨216,by dsimp [total];omega⟩
    let ambient := C10TailCompose.entryOf flag input bits
    let coldExit := RecoveryRootRound.install coldSlots ambient coldData
    let prologueData : Fin ((218+(60+(e+23)))+1) → List Bool := Fin.addCases
      (C10SupplierCall.bank [] (VerifierDecoding.CompareMachine.word 0) (List.replicate b true) input bits w : Fin (218+(60+(e+23))) → List Bool)
      (fun _ : Fin 1 => VerifierDecoding.CompareMachine.word N)
    let post := RecoveryRootRound.install preSlots coldExit prologueData
    let postHeads := dockH preSlots (fun _ => 0)
      (Fin.addCases (fun _ : Fin (218+(60+(e+23))) => 0) (fun _ : Fin 1 => 1))
    change (∀ j : Fin (c+2),2≤j.val → post (coldSlots j)=coldData j) ∧
  (∀ v,L≤v.val → v.val<B → post v=[]) ∧
  (∀ i : Fin 278,post ⟨i.val,by have := i.isLt;dsimp [total];omega⟩=
    C10SupplierCall.bank [] (VerifierDecoding.CompareMachine.word 0) (List.replicate b true) input bits w i) ∧
  (∀ v,postHeads v=if v.val=B then 1 else 0)
    have coldInj : Function.Injective coldSlots := by
      intro i j he
      have hv := congrArg Fin.val he
      have hi := i.isLt
      have hj := j.isLt
      apply Fin.ext
      dsimp only [coldSlots] at hv
      split_ifs at hv <;> (try dsimp [P] at *) <;> omega
    have preInj : Function.Injective preSlots := by
      intro i j he
      have hv := congrArg Fin.val he
      have hi := i.isLt
      have hj := j.isLt
      apply Fin.ext
      dsimp only [preSlots] at hv
      split_ifs at hv <;> (try dsimp [P,B,total] at *) <;> omega
    have preAway (v : Fin total) (hv : P≤v.val) (hB : v.val<B) : ∀ i,preSlots i≠v := by
      intro i he
      have eqv := congrArg Fin.val he
      dsimp only [preSlots] at eqv
      split_ifs at eqv <;> omega
    refine ⟨?_,?_,?_,?_⟩
    · intro j lo
      have hi := j.isLt
      have cv : (coldSlots j).val=P+j.val-2 := by
        dsimp only [coldSlots]
        rw [if_neg (by omega)]
      rw [show post (coldSlots j)=coldExit (coldSlots j) from
        install_other preSlots coldExit prologueData _ (preAway _ (by rw [cv];omega) (by rw [cv];dsimp [B,total,P];omega))]
      exact install_slot coldSlots coldInj ambient coldData j
    · intro v hlo hhi
      have hp : P≤v.val := by dsimp [L] at hlo;omega
      rw [show post v=coldExit v from install_other preSlots coldExit prologueData v (preAway v hp hhi)]
      rw [show coldExit v=ambient v from install_other coldSlots ambient coldData v (by
        intro j he
        have hv := congrArg Fin.val he
        have hj := j.isLt
        dsimp only [coldSlots] at hv
        split_ifs at hv <;> (try dsimp [L,P] at *) <;> omega)]
      have nf : v≠flag := by intro he;have hv := congrArg Fin.val he;dsimp [flag,L,P] at *;omega
      have n0 : v.val≠0 := by dsimp [L,P] at hlo;omega
      have n1 : v.val≠1 := by dsimp [L,P] at hlo;omega
      simp only [ambient,C10TailCompose.entryOf,nf,n0,n1,if_false]
    · intro i
      let loc : Fin (218+(60+(e+23))) := ⟨i.val,by have := i.isLt;omega⟩
      have eqslot : (⟨i.val,by have := i.isLt;dsimp [total];omega⟩ : Fin total)=preSlots (loc.castAdd 1) := by
        apply Fin.ext
        dsimp only [preSlots,Fin.val_castAdd,loc]
        rw [if_pos (by have := i.isLt;dsimp [P];omega)]
      rw [eqslot,show post (preSlots (loc.castAdd 1))=prologueData (loc.castAdd 1) from
        install_slot preSlots preInj coldExit prologueData (loc.castAdd 1)]
      dsimp only [prologueData]
      rw [Fin.addCases_left]
      rfl
    · intro v
      by_cases hv : v.val=B
      · let top : Fin ((218+(60+(e+23)))+1) := (0 : Fin 1).natAdd (218+(60+(e+23)))
        have eqslot : v=preSlots top := by
          apply Fin.ext
          dsimp [preSlots,top,P]
          split_ifs <;> omega
        rw [eqslot,show postHeads (preSlots top)=1 from (dockH_slot preSlots preInj (fun _ => 0) _ top).trans (by simp only [top,Fin.addCases_right])]
        have ht : (preSlots top).val=B := by dsimp [preSlots,top,P];split_ifs <;> omega
        rw [if_pos ht]
      by_cases hp : v.val<P
      · let loc : Fin (218+(60+(e+23))) := ⟨v.val,by dsimp [P] at hp;omega⟩
        have eqslot : v=preSlots (loc.castAdd 1) := by
          apply Fin.ext
          dsimp only [preSlots,Fin.val_castAdd,loc]
          rw [if_pos hp]
        have zero : postHeads v=0 := by
          rw [eqslot]
          exact (dockH_slot preSlots preInj (fun _ => 0) _ (loc.castAdd 1)).trans (by rw [Fin.addCases_left])
        rw [zero,if_neg hv]
      · have outside : ∀ i,preSlots i≠v := by
          intro i he
          have hval := congrArg Fin.val he
          dsimp only [preSlots] at hval
          split_ifs at hval <;> omega
        rw [show postHeads v=0 from dockH_other preSlots (fun _ => 0) _ v outside,if_neg hv]

private theorem count_append
    (B : Nat)
    (cache : Fin 19 → Fin B)
    (countSlots : Fin 74 → Fin B)
    (appendSlots : Fin 42 → Fin B)
    (cacheData : Fin 19 → List Bool)
    (clauseCount : Nat)
    (sys : Nat)
    (b : Nat)
    (countFuel : Nat)
    (actualBank : Fin B → List Bool)
    (hc : Function.Injective countSlots)
    (hfirst : ∀ j : Fin 19,countSlots (j.castAdd 55)=cache j)
    (ha : Function.Injective appendSlots)
    (hdis : ∀ i j,countSlots i≠appendSlots j)
    (hcount : ∃ out, Step CloseoutRowsOriginalCount.machine countFuel (CloseoutRowsOriginalCount.heads PCPPQueryClauseReuse.heads) (CloseoutRowsOriginalCount.input cacheData) (CloseoutRowsOriginalCount.heads PCPPQueryClauseReuse.heads) out ∧ (∀ j : Fin 19,out (j.castAdd 55)=cacheData j) ∧ out 70=UnaryTemplate.tape clauseCount ∧ out 72=List.replicate clauseCount true ∧ out 28=UnaryTemplate.tape sys)
    (hcache : ∀ j,actualBank (cache j)=cacheData j)
    (hfresh : ∀ j : Fin 55,actualBank (countSlots (Fin.natAdd 19 j))=[])
    (happend : ∀ j,actualBank (appendSlots j)=CloseoutFinalC10AppendWorkspaceInit.input b j) :
    ∃ finalBank, Step (Composition.machine (DecompositionCountPosition.move (fun i : Fin B => if i=cache 13 ∨ i=cache 14 then .right else .stay)) (Composition.machine (RecoveryFocus.machine countSlots CloseoutRowsOriginalCount.machine) (Composition.machine (DecompositionCountPosition.move (fun i : Fin B => if i=cache 13 ∨ i=cache 14 then .left else .stay)) (RecoveryFocus.machine appendSlots CloseoutFinalC10AppendWorkspaceInit.machine)))) (countFuel+CloseoutFinalC10AppendWorkspaceInit.budget b+5) (fun _ => 0) actualBank (fun _ => 0) finalBank ∧ (∀ j,finalBank (cache j)=cacheData j) ∧ finalBank (countSlots 28)=UnaryTemplate.tape sys ∧ finalBank (countSlots 70)=UnaryTemplate.tape clauseCount ∧ finalBank (countSlots 72)=List.replicate clauseCount true ∧ finalBank (appendSlots 0)=List.replicate b true ∧ finalBank (appendSlots 20)=UnaryTemplate.tape (20*b+22) ∧ finalBank (appendSlots 39)=List.replicate (CloseoutFinalC10AppendWorkspaceInit.capacity b) false ∧ finalBank (appendSlots 40)=List.replicate (CloseoutFinalC10AppendWorkspaceInit.capacity b) false ∧ (∀ v,(∀ i,countSlots i≠v) → (∀ i,appendSlots i≠v) → finalBank v=actualBank v) :=
  open RepairOrdinary LocalBitMultitape ExtDecompositionBatch RecoveryRootRound in
  by
    let HR : Fin B → Nat := (fun i : Fin B => if i=cache 13 ∨ i=cache 14 then 1 else 0)
    let rightDirs : Fin B → HeadMove := fun i => if i=cache 13 ∨ i=cache 14 then .right else .stay
    let leftDirs : Fin B → HeadMove := fun i => if i=cache 13 ∨ i=cache 14 then .left else .stay
    obtain ⟨mr,hmr,mrf,_ms⟩ := DecompositionCountPosition.move_run rightDirs (fun _ => 0) actualBank
    have hmrH : mr.final.heads=HR := by
      rw [mrf]
      funext i
      dsimp [HR,rightDirs]
      split_ifs <;> rfl
    have moveRight := Step.of_run hmr hmrH (congrArg Configuration.tapes mrf)
    obtain ⟨C,hC,keepC,Mt,Mr,S⟩ := hcount
    have hHC : ∀ i,HR (countSlots i)=CloseoutRowsOriginalCount.heads PCPPQueryClauseReuse.heads i := by
      intro i
      have eq13 : countSlots i=cache 13 ↔ i=(13 : Fin 19).castAdd 55 := by
        rw [←hfirst 13]
        exact hc.eq_iff
      have eq14 : countSlots i=cache 14 ↔ i=(14 : Fin 19).castAdd 55 := by
        rw [←hfirst 14]
        exact hc.eq_iff
      dsimp only [HR]
      simp only [eq13,eq14]
      refine Fin.addCases (m:=19) (n:=55) (fun j => ?_) (fun j => ?_) i
      · change (if j.castAdd 55=(13 : Fin 19).castAdd 55 ∨ j.castAdd 55=(14 : Fin 19).castAdd 55 then 1 else 0)=_
        simp only [Fin.castAdd_inj]
        rw [show j.castAdd 55=(j.castAdd 37).castAdd 18 from Fin.ext rfl,
          CloseoutRowsOriginalCount.heads,Fin.addCases_left,CloseoutCaseTwo.Metadata.heads,Fin.addCases_left]
        rfl
      · have n13 : Fin.natAdd 19 j≠(13 : Fin 19).castAdd 55 := by intro he;have hv:=congrArg Fin.val he;dsimp at hv;omega
        have n14 : Fin.natAdd 19 j≠(14 : Fin 19).castAdd 55 := by intro he;have hv:=congrArg Fin.val he;dsimp at hv;omega
        rw [if_neg (by simp only [n13,n14,or_self,not_false_eq_true])]
        simp [CloseoutRowsOriginalCount.heads, CloseoutCaseTwo.Metadata.heads,Fin.addCases]
    have hAC : ∀ i,actualBank (countSlots i)=CloseoutRowsOriginalCount.input cacheData i := by
      intro i
      refine Fin.addCases (m:=19) (n:=55) (fun j => ?_) (fun j => ?_) i
      · rw [hfirst]
        rw [show j.castAdd 55=(j.castAdd 37).castAdd 18 from Fin.ext rfl,
          CloseoutRowsOriginalCount.input,Fin.addCases_left,CloseoutCaseTwo.Metadata.input,Fin.addCases_left]
        exact hcache j
      · rw [hfresh]
        simp [CloseoutRowsOriginalCount.input, CloseoutCaseTwo.Metadata.input,Fin.addCases]
    let AC := install countSlots actualBank C
    have countRun := (hC.dock countSlots hc HR actualBank hHC hAC).congr (dockH_existing countSlots HR _ hHC) rfl
    obtain ⟨ml,hml,mlf,_mts⟩ := DecompositionCountPosition.move_run leftDirs HR AC
    have hmlH : ml.final.heads=(fun _ => 0) := by
      rw [mlf]
      funext i
      dsimp [HR,leftDirs]
      split_ifs <;> rfl
    have moveLeft := Step.of_run hml hmlH (congrArg Configuration.tapes mlf)
    obtain ⟨A,hA,bkeep,width,copylog,resetlog⟩ := CloseoutFinalC10AppendWorkspaceInit.initialize_run b
    have hAA : ∀ i,AC (appendSlots i)=CloseoutFinalC10AppendWorkspaceInit.input b i := by
      intro i
      exact (install_other countSlots actualBank C _ (fun j => hdis j i)).trans (happend i)
    have appendRun := (hA.dock appendSlots ha (fun _ => 0) AC (by intro i;rfl) hAA).congr
      (dockH_existing appendSlots (fun _ => 0) _ (by intro i;rfl)) rfl
    have all := moveRight.seq (countRun.seq (moveLeft.seq appendRun))
    have ht : 1+1+(countFuel+1+(1+1+CloseoutFinalC10AppendWorkspaceInit.budget b))=countFuel+CloseoutFinalC10AppendWorkspaceInit.budget b+5 := by omega
    rw [ht] at all
    refine ⟨_,all,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · intro j
      rw [←hfirst j,install_other appendSlots AC A _ (fun i he => hdis (j.castAdd 55) i he.symm)]
      exact (install_slot countSlots hc actualBank C _).trans (keepC j)
    · rw [install_other appendSlots AC A _ (fun i he => hdis 28 i he.symm)]
      exact (install_slot countSlots hc actualBank C 28).trans S
    · rw [install_other appendSlots AC A _ (fun i he => hdis 70 i he.symm)]
      exact (install_slot countSlots hc actualBank C 70).trans Mt
    · rw [install_other appendSlots AC A _ (fun i he => hdis 72 i he.symm)]
      exact (install_slot countSlots hc actualBank C 72).trans Mr
    · exact (install_slot appendSlots ha AC A 0).trans bkeep
    · exact (install_slot appendSlots ha AC A 20).trans width
    · exact (install_slot appendSlots ha AC A 39).trans copylog
    · exact (install_slot appendSlots ha AC A 40).trans resetlog
    · intro v hvC hvA
      exact (install_other appendSlots AC A v hvA).trans (install_other countSlots actualBank C v hvC)

private theorem actual_init
    (B : Nat)
    (L : Nat)
    (hL : 278≤L)
    (space : L+96<B)
    (cache : Fin 19 → Fin B)
    (a : PointwisePCPPAlgorithm)
    (rq : PCPPRequest a.minimumArity)
    (b : Nat)
    (actualBank : Fin B → List Bool)
    (cacheInj : Function.Injective cache)
    (cacheLow : ∀ j,278≤(cache j).val)
    (cacheHigh : ∀ j,(cache j).val<L)
    (cacheBytes : ∀ j,actualBank (cache j)=(PCPPQueryIndexPadding.clauseData (pcppOutput rq (a.output rq)) rq.arity 0 (PCPPQueryCachedBounds.capacity a (rq.circuit.size+rq.arity)) []) j)
    (width : actualBank ⟨218,by omega⟩=List.replicate b true)
    (fresh : ∀ v : Fin B,L≤v.val → actualBank v=[]) :
    let cacheData := PCPPQueryIndexPadding.clauseData (pcppOutput rq (a.output rq)) rq.arity 0 (PCPPQueryCachedBounds.capacity a (rq.circuit.size+rq.arity)) []
    let clauseCount := 2^(a.output rq).clauseBits
    let sys := (a.output rq).systematicBits
    let countFuel := CloseoutRowsOriginalCount.budget rq (a.output rq)
    let countSlots : Fin 74 → Fin B := fun i =>
      if hi : i.val<19 then cache ⟨i.val,hi⟩ else ⟨L+i.val-19,by have := i.isLt;omega⟩
    let appendSlots : Fin 42 → Fin B := fun i =>
      ⟨if i.val=0 then 218 else L+54+i.val,by have := i.isLt;split_ifs <;> omega⟩
    ∃ finalBank, Step (Composition.machine (DecompositionCountPosition.move (fun i : Fin B => if i=cache 13 ∨ i=cache 14 then .right else .stay)) (Composition.machine (RecoveryFocus.machine countSlots CloseoutRowsOriginalCount.machine) (Composition.machine (DecompositionCountPosition.move (fun i : Fin B => if i=cache 13 ∨ i=cache 14 then .left else .stay)) (RecoveryFocus.machine appendSlots CloseoutFinalC10AppendWorkspaceInit.machine)))) (countFuel+CloseoutFinalC10AppendWorkspaceInit.budget b+5) (fun _ => 0) actualBank (fun _ => 0) finalBank ∧ (∀ j,finalBank (cache j)=cacheData j) ∧ finalBank (countSlots 28)=UnaryTemplate.tape sys ∧ finalBank (countSlots 70)=UnaryTemplate.tape clauseCount ∧ finalBank (countSlots 72)=List.replicate clauseCount true ∧ finalBank (appendSlots 0)=List.replicate b true ∧ finalBank (appendSlots 20)=UnaryTemplate.tape (20*b+22) ∧ finalBank (appendSlots 39)=List.replicate (CloseoutFinalC10AppendWorkspaceInit.capacity b) false ∧ finalBank (appendSlots 40)=List.replicate (CloseoutFinalC10AppendWorkspaceInit.capacity b) false ∧ (∀ v,(∀ i,countSlots i≠v) → (∀ i,appendSlots i≠v) → finalBank v=actualBank v) :=
  open RepairOrdinary ExtDecompositionBatch in
  by
    dsimp only
    let cacheData := PCPPQueryIndexPadding.clauseData (pcppOutput rq (a.output rq)) rq.arity 0 (PCPPQueryCachedBounds.capacity a (rq.circuit.size+rq.arity)) []
    let clauseCount := 2^(a.output rq).clauseBits
    let sys := (a.output rq).systematicBits
    let countFuel := CloseoutRowsOriginalCount.budget rq (a.output rq)
    let countSlots : Fin 74 → Fin B := fun i =>
      if hi : i.val<19 then cache ⟨i.val,hi⟩ else ⟨L+i.val-19,by have := i.isLt;omega⟩
    let appendSlots : Fin 42 → Fin B := fun i =>
      ⟨if i.val=0 then 218 else L+54+i.val,by have := i.isLt;split_ifs <;> omega⟩
    have countBound (i : Fin 74) : 278≤(countSlots i).val ∧ (countSlots i).val<L+55 := by
      have hi := i.isLt
      dsimp only [countSlots]
      split_ifs with h
      · exact ⟨cacheLow _,Nat.lt_trans (cacheHigh _) (by omega)⟩
      · dsimp only
        omega
    have hc : Function.Injective countSlots := by
      intro i j he
      have hi74 := i.isLt
      have hj74 := j.isLt
      by_cases hi : i.val<19
      · by_cases hj : j.val<19
        · simp only [countSlots,dif_pos hi,dif_pos hj] at he
          exact Fin.ext (congrArg (fun v : Fin 19 => v.val) (cacheInj he))
        · simp only [countSlots,dif_pos hi,dif_neg hj] at he
          have bound := cacheHigh ⟨i.val,hi⟩
          have hv := congrArg Fin.val he
          dsimp only at hv
          omega
      · by_cases hj : j.val<19
        · simp only [countSlots,dif_neg hi,dif_pos hj] at he
          have bound := cacheHigh ⟨j.val,hj⟩
          have hv := congrArg Fin.val he
          dsimp only at hv
          omega
        · simp only [countSlots,dif_neg hi,dif_neg hj] at he
          apply Fin.ext
          have hv := congrArg Fin.val he
          dsimp only at hv
          omega
    have hfirst : ∀ j : Fin 19,countSlots (j.castAdd 55)=cache j := by
      intro j
      dsimp only [countSlots,Fin.val_castAdd]
      rw [dif_pos j.isLt]
    have ha : Function.Injective appendSlots := by
      intro i j he
      have hv := congrArg Fin.val he
      dsimp only [appendSlots] at hv
      apply Fin.ext
      split_ifs at hv <;> omega
    have hdis : ∀ i j,countSlots i≠appendSlots j := by
      intro i j he
      have hb := countBound i
      have hv := congrArg Fin.val he
      dsimp only [appendSlots] at hv
      split_ifs at hv <;> omega
    have hfresh : ∀ j : Fin 55,actualBank (countSlots (Fin.natAdd 19 j))=[] := by
      intro j
      apply fresh
      dsimp only [countSlots,Fin.val_natAdd]
      rw [dif_neg (by omega)]
      dsimp only
      omega
    have happend : ∀ j,actualBank (appendSlots j)=CloseoutFinalC10AppendWorkspaceInit.input b j := by
      intro j
      by_cases h : j.val=0
      · have hj : j=0 := Fin.ext h
        subst j
        exact width
      · rw [CloseoutFinalC10AppendWorkspaceInit.input,if_neg h]
        apply fresh
        dsimp only [appendSlots]
        rw [if_neg h]
        omega
    have counted := CloseoutRowsOriginalCount.run_with_systematic rq (a.output rq) PCPPQueryClauseReuse.heads cacheData rfl rfl rfl rfl
    exact count_append B cache countSlots appendSlots cacheData clauseCount sys b countFuel actualBank
      hc hfirst ha hdis counted cacheBytes hfresh happend

private theorem cold_entry
    (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
    (a : PointwisePCPPAlgorithm)
    (k : Nat)
    (CH : Nat)
    (Cpad : Nat)
    (cutoff : Nat)
    (D : Nat)
    (G : Nat)
    (copies : Nat)
    (delta : Rat)
    (code : List Bool)
    (n : Nat)
    (x : BitInput n)
    (hpad : k+3 ≤ Cpad)
    (hD : 1 ≤ D)
    (E : Nat)
    (K : Nat)
    (bits : List Bool)
    (hK : 0<K)
    (hcut : 2^a.minimumArity ≤ cutoff)
    (hd : 0<delta)
    (hh : delta<1/2)
    (hc : 1≤copies)
    (hbudget : ∀ N, FamilyResources.capacity (ColdFamily.scale source a G D copies delta N) ≤ K*(N+1)^E)
    (symDen : Nat)
    (thrDen : Nat)
    (hsym : 0<symDen)
    (hthr : 0<thrDen)
    (e : Nat)
    (Wsite : Nat)
    (admitted : BoundedFamily.passed source a k CH Cpad cutoff D G copies symDen thrDen delta code x bits hpad=true) :
    let c := HeaderDock.tapes (BoundedFamily.workspace source a k D G E)
    let old := Classical.choose (CloseoutFinalC10ColdCacheAtAdmission.bounded_cache source a k CH Cpad cutoff D G copies E K symDen thrDen delta code x bits hpad hD hsym hthr hK hcut hd hh hc hbudget)
    let coldData := Fin.addCases (m:=HeaderDock.tapes (BoundedFamily.workspace source a k D G E)+1) (n:=1) (motive:=fun _ => List Bool) old.final.tapes (fun _ : Fin 1 => List.replicate old.steps false)
    let P := 301+e
    let total := c+2+(301+e+96+Wsite)
    let B := total-1
    let coldSlots : Fin ((HeaderDock.tapes (BoundedFamily.workspace source a k D G E)+1)+1) → Fin total := fun i =>
      ⟨if i.val<2 then i.val else P+i.val-2,by have := i.isLt;dsimp [total,P,c];split_ifs <;> omega⟩
    let preSlots : Fin (218+(60+(e+23))+1) → Fin total := fun i =>
      ⟨if i.val<P then i.val else B,by have := i.isLt;dsimp [total,P,B];split_ifs <;> omega⟩
    let flag : Fin total := ⟨216,by dsimp [total];omega⟩
    let ambient := C10TailCompose.entryOf flag (List.ofFn x) bits
    let exit := RecoveryRootRound.install coldSlots ambient coldData
    Step (RecoveryFocus.machine coldSlots (CloseoutFinalC10ColdCacheRewind.machine (BoundedFamilySupport.actualMachine source a k CH Cpad cutoff D G copies E K symDen thrDen (CloseoutMassThreshold.literalWidth delta copies) delta (CloseoutSampledWitness.massCap delta copies) code)))
      (4*(BoundedFamily.budget source a k CH Cpad cutoff D G copies E K symDen thrDen delta code x bits hpad)+2) (fun _ => 0) ambient (fun _ => 0) exit ∧
    (∀ i,exit (preSlots i)=C10SupplierCall.bank [] [] [] (List.ofFn x) bits (fun _ => []) i) ∧
    readTapeBit (exit (coldSlots ((BoundedFamilySupport.flag source a k D G E).castAdd 1))) 0=true ∧
    exit (coldSlots ((((HeaderDock.old (BoundedFamily.workspace source a k D G E) 142).castAdd 1)).castAdd 1))=[BoundedFields.symmetric bits] ∧
    CloseoutFinalC10ColdCacheAtAdmission.Cached source a k CH Cpad D G E code x bits hpad old.final.heads old.final.tapes :=
  open CloseoutWitness in
  by
    classical
    dsimp only
    let c := HeaderDock.tapes (BoundedFamily.workspace source a k D G E)
    let old := Classical.choose (CloseoutFinalC10ColdCacheAtAdmission.bounded_cache source a k CH Cpad cutoff D G copies E K symDen thrDen delta code x bits hpad hD hsym hthr hK hcut hd hh hc hbudget)
    let coldData := Fin.addCases (m:=HeaderDock.tapes (BoundedFamily.workspace source a k D G E)+1) (n:=1) (motive:=fun _ => List Bool) old.final.tapes (fun _ : Fin 1 => List.replicate old.steps false)
    let P := 301+e
    let total := c+2+(301+e+96+Wsite)
    let B := total-1
    let coldSlots : Fin ((HeaderDock.tapes (BoundedFamily.workspace source a k D G E)+1)+1) → Fin total := fun i =>
      ⟨if i.val<2 then i.val else P+i.val-2,by have := i.isLt;dsimp [total,P,c];split_ifs <;> omega⟩
    let preSlots : Fin (218+(60+(e+23))+1) → Fin total := fun i =>
      ⟨if i.val<P then i.val else B,by have := i.isLt;dsimp [total,P,B];split_ifs <;> omega⟩
    let flag : Fin total := ⟨216,by dsimp [total];omega⟩
    let ambient := C10TailCompose.entryOf flag (List.ofFn x) bits
    let exit := RecoveryRootRound.install coldSlots ambient coldData
    change Step (RecoveryFocus.machine coldSlots (CloseoutFinalC10ColdCacheRewind.machine (BoundedFamilySupport.actualMachine source a k CH Cpad cutoff D G copies E K symDen thrDen (CloseoutMassThreshold.literalWidth delta copies) delta (CloseoutSampledWitness.massCap delta copies) code)))   (4*(BoundedFamily.budget source a k CH Cpad cutoff D G copies E K symDen thrDen delta code x bits hpad)+2) (fun _ => 0) ambient (fun _ => 0) exit ∧ (∀ i,exit (preSlots i)=C10SupplierCall.bank [] [] [] (List.ofFn x) bits (fun _ => []) i) ∧ readTapeBit (exit (coldSlots ((BoundedFamilySupport.flag source a k D G E).castAdd 1))) 0=true ∧ exit (coldSlots ((((HeaderDock.old (BoundedFamily.workspace source a k D G E) 142).castAdd 1)).castAdd 1))=[BoundedFields.symmetric bits] ∧ CloseoutFinalC10ColdCacheAtAdmission.Cached source a k CH Cpad D G E code x bits hpad old.final.heads old.final.tapes
    have hi : Function.Injective coldSlots := by
      intro i j he
      have hv := congrArg Fin.val he
      have hival := i.isLt
      have hjval := j.isLt
      apply Fin.ext
      dsimp only [coldSlots] at hv
      split_ifs at hv <;> (try dsimp [P] at *) <;> omega
    have entry : ∀ j,ambient (coldSlots j)=Fin.addCases (BoundedFamilySupport.input source a k D G E (List.ofFn x) bits) (fun _ : Fin 1 => []) j :=
      CloseoutFinalC10ColdGateInput.input (BoundedFamily.workspace source a k D G E) e Wsite (List.ofFn x) bits
    have frameFacts := CloseoutFinalC10ColdOriginalFrame.focused_frame (source:=source) (a:=a) (k:=k) (CH:=CH) (Cpad:=Cpad) (cutoff:=cutoff) (D:=D) (G:=G) (copies:=copies) (delta:=delta) (code:=code) (n:=n) (x:=x) (hpad:=hpad) (hD:=hD) (E:=E) (K:=K) (bits:=bits) (hK:=hK) (hcut:=hcut) (hd:=hd) (hh:=hh) (hc:=hc) (hbudget:=hbudget) (symDen:=symDen) (thrDen:=thrDen) (hsym:=hsym) (hthr:=hthr) (u:=total) (slots:=coldSlots) (injective:=hi) (ambient:=ambient) (entry:=entry)
    have existence := CloseoutFinalC10ColdCacheAtAdmission.bounded_cache source a k CH Cpad cutoff D G copies E K symDen thrDen delta code x bits hpad hD hsym hthr hK hcut hd hh hc hbudget
    have oldRun := (Classical.choose_spec existence).1
    have originals := CloseoutFinalC10ColdOriginalFrame.bounded_originals (source:=source) (a:=a) (k:=k) (CH:=CH) (Cpad:=Cpad) (cutoff:=cutoff) (D:=D) (G:=G) (copies:=copies) (delta:=delta) (code:=code) (n:=n) (x:=x) (hpad:=hpad) (hD:=hD) (E:=E) (K:=K) (bits:=bits) (hK:=hK) (hcut:=hcut) (hd:=hd) (hh:=hh) (hc:=hc) (hbudget:=hbudget) (symDen:=symDen) (thrDen:=thrDen) (hsym:=hsym) (hthr:=hthr) (actual:=old) (hrun:=oldRun) (admitted:=admitted)
    have data0 : coldData 0=frame (List.ofFn x) := by
      have slot0 : (0 : Fin (c+2))=((HeaderDock.old (BoundedFamily.workspace source a k D G E) 0).castAdd 1).castAdd 1 := Fin.ext rfl
      rw [slot0]
      exact (Fin.addCases_left _).trans originals.1
    have data1 : coldData 1=frame bits := by
      have slot1 : (1 : Fin (c+2))=((HeaderDock.old (BoundedFamily.workspace source a k D G E) 1).castAdd 1).castAdd 1 := by
        apply Fin.ext
        simp only [Fin.val_castAdd,HeaderDock.old]
        exact Nat.mod_eq_of_lt (by dsimp [c,HeaderDock.tapes];omega)
      rw [slot1]
      exact (Fin.addCases_left _).trans originals.2.1
    have parked : ∀ i : Fin total,i.val≠0 → i.val≠1 → ambient i=if i.val=216 then [true] else [] := by
      intro i h0 h1
      have eqflag : i=flag ↔ i.val=216 := by
        constructor
        · intro he;subst i;rfl
        · intro he;apply Fin.ext;exact he
      simp only [ambient,C10TailCompose.entryOf,eqflag,h0,h1,if_false]
    have projection := prologue_input e c Wsite (List.ofFn x) bits ambient coldData data0 data1 parked
    refine ⟨frameFacts.1,projection,frameFacts.2.2.2.2.2.1.trans admitted,?_,frameFacts.2.2.2.2.2.2 admitted⟩
    exact (frameFacts.2.2.1 (((HeaderDock.old (BoundedFamily.workspace source a k D G E) 142).castAdd 1))).trans originals.2.2

private theorem cache_injective
    (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
    (a : PointwisePCPPAlgorithm)
    (k : Nat)
    (D : Nat)
    (G : Nat)
    (E : Nat)
    (mode : Bool) :
    Function.Injective (CloseoutFinalC10ColdCacheAtAdmission.cacheSlot source a k D G E mode) :=
  open CloseoutWitness in
  by
    intro i j he
    have one := BoundedFamilySupport.slots_injective source a k D G E mode he
    have two := (Fin.castAdd_injective _ _) one
    have three := (Fin.castAdd_injective _ _) two
    have threeB := (Fin.castAdd_injective _ _) three
    have threeC := (Fin.castAdd_injective _ _) threeB
    have four := (Fin.castAdd_injective _ _) threeC
    have five := NativePipeline.Dock.slots_injective a D G (ColdNative.fields source k)
      (ColdNative.fields_injective source k) four
    have six := NativePolicy.Call.slots_injective a D (NativePipeline.counter G)
      (NativeScreen.slots_injective G) five
    exact ColdLegal.native_cache_injective a ((Fin.castAdd_injective _ _) six)

private theorem cache_lower
    (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
    (a : PointwisePCPPAlgorithm)
    (k : Nat)
    (D : Nat)
    (G : Nat)
    (E : Nat)
    (mode : Bool) :
    ∀ j : Fin 19,2≤(CloseoutFinalC10ColdCacheAtAdmission.cacheSlot source a k D G E mode j).val :=
  open CloseoutWitness in
  by
    intro j
    let idx : Fin (BoundedFamily.localTapes source a k D G E mode) :=
      ColdFamily.cache source a k D G (BoundedFamily.exponent mode) E j
    have outside := ColdNative.slots_ne_originalTape source a k D G
      (NativePipeline.cacheSlots a D G (PCPPSourceCache.cacheSlots a j))
    have ne2 : idx.val ≠ 2 := by
      intro he
      simp only [idx,ColdFamily.cache,ColdFamilyLift.old,FamilyCold.Call.old,FamilyCapacity.Call.old,
        ColdLegal.cache,ColdLegal.old,LegalTemplate.Call.old,Fin.val_castAdd] at he
      apply outside
      apply Fin.ext
      exact he
    change 2≤(SupportDock.slots (BoundedFamily.slots source a k D G E mode)
      (idx.castAdd 1)).val
    rw [SupportDock.slots_old,Fin.val_castAdd]
    unfold BoundedFamily.slots HeaderDock.slots
    split_ifs <;> (try simp only [HeaderDock.old,HeaderDock.flag,Fin.val_castAdd,Fin.val_natAdd,Fin.val_zero]) <;> omega

private theorem gate_run
    (T : Nat)
    (s : Nat)
    (worker : Machine T s)
    (ht : 2≤T)
    (input : Fin T)
    (flag : Fin T)
    (result : Fin T)
    (onset : Nat)
    (n : Nat)
    (x : BitInput n)
    (bits : List Bool)
    (hinput : input.val=0)
    (hflag : flag.val=216)
    (hn : onset≤n) :
    Step (C10LengthGate.counter onset input flag) (4*onset+1) (fun _ => 0) ((UAcceptanceCarrier.verifier worker ht result).inputTapes (List.ofFn x) bits) (fun _ => 0) (C10TailCompose.entryOf flag (List.ofFn x) bits) ∧ (∀ i : Fin T,i.val≠0 → i.val≠1 → (C10TailCompose.entryOf flag (List.ofFn x) bits) i=if i.val=216 then [true] else []) :=
  by
    have read : ∀ j,j<2*onset → j%2=0 → readTapeBit (((UAcceptanceCarrier.verifier worker ht result).inputTapes (List.ofFn x) bits) input) ((fun _ : Fin T => 0) input+j)=true := by
      intro j hj he
      rw [UAcceptanceCarrier.inputTapes_eq]
      simp only [hinput,Nat.zero_add]
      exact C10LengthGate.frame_short (List.ofFn x) j (by rw [List.length_ofFn];omega) he
    have step := C10LengthGate.counter_pass_clean onset input flag (fun _ => 0) ((UAcceptanceCarrier.verifier worker ht result).inputTapes (List.ofFn x) bits) read
    refine ⟨step.congr rfl (C10TailCompose.entry_eq worker ht result flag (by omega) (by omega) (List.ofFn x) bits),?_⟩
    intro i hi0 hi1
    have eqflag : i=flag ↔ i.val=216 := by
      constructor
      · intro he;subst i;exact hflag
      · intro he;apply Fin.ext;omega
    simp only [C10TailCompose.entryOf,eqflag,hi0,hi1,if_false]

private theorem focused_prologue
    (src : EightSources)
    (k : Nat)
    (r : Nat)
    (D : Nat)
    (T : Nat)
    (preSlots : Fin (218+(60+(CloseoutFinalC10SeedEngine.tapesOf (ProjectionNormalization.HierarchyPrefix.tapes k (CloseoutFinalC10SeedEngine.rp src) (CloseoutFinalC10SeedEngine.rq src)) r D+23))+1) → Fin T)
    (n : Nat)
    (x : BitInput n)
    (bits : List Bool)
    (actualColdExit : Fin T → List Bool)
    (hD : 1≤D)
    (hmap : Function.Injective preSlots)
    (hentry : ∀ i,actualColdExit (preSlots i)=(C10SupplierCall.bank [] [] [] (List.ofFn x) bits (fun _ => []) : Fin (218+(60+(CloseoutFinalC10SeedEngine.tapesOf (ProjectionNormalization.HierarchyPrefix.tapes k (CloseoutFinalC10SeedEngine.rp src) (CloseoutFinalC10SeedEngine.rq src)) r D+23))+1) → List Bool) i) :
    ∃ w : Nat → List Bool, Step (RecoveryFocus.machine preSlots (C10PrologueUniform.prologueMachine (CloseoutFinalC10SeedEngine.tapesOf (ProjectionNormalization.HierarchyPrefix.tapes k (CloseoutFinalC10SeedEngine.rp src) (CloseoutFinalC10SeedEngine.rq src)) r D) (RecoveryFocus.machine (CloseoutFinalC10SeedEngine.bankSlots (ProjectionNormalization.HierarchyPrefix.tapes k (CloseoutFinalC10SeedEngine.rp src) (CloseoutFinalC10SeedEngine.rq src)) r D (CloseoutFinalC10SeedEngine.readerIn src k)) (CloseoutFinalC10SeedEngine.engineMachine r D (CloseoutFinalC10SeedEngine.widthReader src k) (CloseoutFinalC10SeedEngine.readerQ src k) (C10PartsSchedule.thresholdFloor src))))) (C10PrologueUniform.prologueFuel D (C10PartsSchedule.widthAt src k) (CloseoutFinalC10SeedEngine.engineFuel r D (CloseoutFinalC10SeedEngine.readerFuel src k) (C10PartsSchedule.thresholdFloor src) (C10PartsSchedule.widthAt src k)) n) (fun _ => 0) actualColdExit (dockH preSlots (fun _ => 0) (Fin.addCases (motive:=fun _ => Nat) (fun _ : Fin (218+(60+(CloseoutFinalC10SeedEngine.tapesOf (ProjectionNormalization.HierarchyPrefix.tapes k (CloseoutFinalC10SeedEngine.rp src) (CloseoutFinalC10SeedEngine.rq src)) r D+23))) => 0) (fun _ : Fin 1 => 1))) (RecoveryRootRound.install preSlots actualColdExit (Fin.addCases (motive:=fun _ => List Bool) (C10SupplierCall.bank [] (VerifierDecoding.CompareMachine.word 0) (List.replicate (C10PartsSchedule.entryWidthSchedule src k r n) true) (List.ofFn x) bits w : Fin (218+(60+(CloseoutFinalC10SeedEngine.tapesOf (ProjectionNormalization.HierarchyPrefix.tapes k (CloseoutFinalC10SeedEngine.rp src) (CloseoutFinalC10SeedEngine.rq src)) r D+23))) → List Bool) (fun _ : Fin 1 => VerifierDecoding.CompareMachine.word (2^(CloseoutLanguage.clauseWidth D (C10PartsSchedule.widthAt src k n)))))) ∧ (∀ v,(∀ i,preSlots i≠v) → (RecoveryRootRound.install preSlots actualColdExit (Fin.addCases (motive:=fun _ => List Bool) (C10SupplierCall.bank [] (VerifierDecoding.CompareMachine.word 0) (List.replicate (C10PartsSchedule.entryWidthSchedule src k r n) true) (List.ofFn x) bits w : Fin (218+(60+(CloseoutFinalC10SeedEngine.tapesOf (ProjectionNormalization.HierarchyPrefix.tapes k (CloseoutFinalC10SeedEngine.rp src) (CloseoutFinalC10SeedEngine.rq src)) r D+23))) → List Bool) (fun _ : Fin 1 => VerifierDecoding.CompareMachine.word (2^(CloseoutLanguage.clauseWidth D (C10PartsSchedule.widthAt src k n)))))) v=actualColdExit v) :=
  by
    have hpro := CloseoutFinalC10SeedEngine.prologue_at_schedule src k r D hD (CloseoutFinalC10SeedEngine.widthReader src k)
      (CloseoutFinalC10SeedEngine.readerIn src k) (CloseoutFinalC10SeedEngine.readerQ src k) (CloseoutFinalC10SeedEngine.readerIn_ne src k)
      (CloseoutFinalC10SeedEngine.readerFuel src k) (CloseoutFinalC10SeedEngine.width_reader src k)
    obtain ⟨w,hw⟩ := hpro n x bits
    refine ⟨w,hw.dock preSlots hmap (fun _ => 0) actualColdExit (by intro i;rfl) hentry,?_⟩
    intro v hv
    exact RecoveryRootRound.install_other preSlots actualColdExit _ v hv
private theorem cache_fits (c e Wsite v : Nat) (hi : v<c+1) :
    301+e+v-2 < (c+2+(301+e+96+Wsite))-1 := by omega

attribute [local irreducible] BoundedFamily.workspace CloseoutFinalC10SeedEngine.tapesOf
  CloseoutFinalC10ColdCacheAtAdmission.cacheSlot

/-- Physical admitted entry. Each component is the selected machine's actual
run; the enclosing worker pays the intervening branches. The existential PCPP
request comes from the same cold cache, and count/append use those exact bytes. -/
theorem run
    (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
    (a : PointwisePCPPAlgorithm)
    (k : Nat)
    (CH : Nat)
    (Cpad : Nat)
    (cutoff : Nat)
    (D : Nat)
    (G : Nat)
    (copies : Nat)
    (delta : Rat)
    (code : List Bool)
    (n : Nat)
    (x : BitInput n)
    (hpad : k+3 ≤ Cpad)
    (hD : 1 ≤ D)
    (E : Nat)
    (K : Nat)
    (bits : List Bool)
    (hK : 0<K)
    (hcut : 2^a.minimumArity ≤ cutoff)
    (hd : 0<delta)
    (hh : delta<1/2)
    (hc : 1≤copies)
    (hbudget : ∀ N, FamilyResources.capacity (ColdFamily.scale source a G D copies delta N) ≤ K*(N+1)^E)
    (symDen : Nat)
    (thrDen : Nat)
    (hsym : 0<symDen)
    (hthr : 0<thrDen)
    (src : EightSources)
    (r : Nat)
    (Wsite : Nat)
    (onset : Nat)
    (admitted : BoundedFamily.passed source a k CH Cpad cutoff D G copies symDen thrDen delta code x bits hpad=true)
    (honset : onset≤n) :
    let e := CloseoutFinalC10SeedEngine.tapesOf (HierarchyPrefix.tapes k (CloseoutFinalC10SeedEngine.rp src) (CloseoutFinalC10SeedEngine.rq src)) r D
    let c := HeaderDock.tapes (BoundedFamily.workspace source a k D G E)
    let old := Classical.choose (CloseoutFinalC10ColdCacheAtAdmission.bounded_cache source a k CH Cpad cutoff D G copies E K symDen thrDen delta code x bits hpad hD hsym hthr hK hcut hd hh hc hbudget)
    let coldData := Fin.addCases (m:=HeaderDock.tapes (BoundedFamily.workspace source a k D G E)+1) (n:=1) (motive:=fun _ => List Bool) old.final.tapes (fun _ : Fin 1 => List.replicate old.steps false)
    let P := 301+e
    let total := c+2+(301+e+96+Wsite)
    let B := total-1
    let coldSlots : Fin ((HeaderDock.tapes (BoundedFamily.workspace source a k D G E)+1)+1) → Fin total := fun i =>
      ⟨if i.val<2 then i.val else P+i.val-2,by have := i.isLt;dsimp only [total,P,c];split_ifs <;> omega⟩
    let preSlots : Fin (218+(60+(e+23))+1) → Fin total := fun i =>
      ⟨if i.val<P then i.val else B,by have := i.isLt;dsimp only [total,P,B];split_ifs <;> omega⟩
    let flag : Fin total := ⟨216,by dsimp only [total];omega⟩
    let ambient := C10TailCompose.entryOf flag (List.ofFn x) bits
    let exit := RecoveryRootRound.install coldSlots ambient coldData
    let L := P+c
    let bodySlots : Fin B → Fin total := fun v => ⟨v.val,by have := v.isLt;dsimp only [B] at *;omega⟩
    let cache : Fin 19 → Fin B := fun j =>
      ⟨P+(CloseoutFinalC10ColdCacheAtAdmission.cacheSlot source a k D G E (BoundedFields.symmetric bits) j).val-2,
        cache_fits c e Wsite _ (CloseoutFinalC10ColdCacheAtAdmission.cacheSlot source a k D G E (BoundedFields.symmetric bits) j).isLt⟩
    let b := C10PartsSchedule.entryWidthSchedule src k r n
    let N := 2^(CloseoutLanguage.clauseWidth D (C10PartsSchedule.widthAt src k n))
    ∃ oracle,
    decodeBooleanCircuit (SelectedOracle.width source k CH Cpad code (List.ofFn x))
        (RadixSemantics.value (BoundedFields.oracle bits))=some oracle ∧
    oracle.size≤RecoveryScheduleEnvelope.oracleSizeBound G
        (SelectedOracle.width source k CH Cpad code (List.ofFn x)) ∧
    let rq := ColdNative.request source a k CH Cpad code x hpad oracle
    ∃ w : Nat → List Bool,
    let prologueData : Fin (218+(60+(e+23))+1) → List Bool := Fin.addCases
      (C10SupplierCall.bank [] (VerifierDecoding.CompareMachine.word 0) (List.replicate b true) (List.ofFn x) bits w : Fin (218+(60+(e+23))) → List Bool)
      (fun _ : Fin 1 => VerifierDecoding.CompareMachine.word N)
    let post := RecoveryRootRound.install preSlots exit prologueData
    let H := dockH preSlots (fun _ => 0) (Fin.addCases (fun _ : Fin (218+(60+(e+23))) => 0) (fun _ : Fin 1 => 1))
    let actualBank := fun v : Fin B => post (bodySlots v)
    let hL : 278≤L := by dsimp only [L,P];omega
    let space : L+96<B := by dsimp only [B,total,L,P];omega
    let cacheData := PCPPQueryIndexPadding.clauseData (pcppOutput rq (a.output rq)) rq.arity 0 (PCPPQueryCachedBounds.capacity a (rq.circuit.size+rq.arity)) []
    let clauseCount := 2^(a.output rq).clauseBits
    let sys := (a.output rq).systematicBits
    let countFuel := CloseoutRowsOriginalCount.budget rq (a.output rq)
    let countSlots : Fin 74 → Fin B := fun i =>
      if hi : i.val<19 then cache ⟨i.val,hi⟩ else ⟨L+i.val-19,by have := i.isLt;omega⟩
    let appendSlots : Fin 42 → Fin B := fun i =>
      ⟨if i.val=0 then 218 else L+54+i.val,by have := i.isLt;split_ifs <;> omega⟩
    ∃ finalBank,
    Step (C10LengthGate.counter onset (⟨0,by dsimp only [total];omega⟩ : Fin total) flag) (4*onset+1) (fun _ => 0) (fun i : Fin total => if i.val=0 then frame (List.ofFn x) else if i.val=1 then frame bits else []) (fun _ => 0) ambient ∧
    Step (RecoveryFocus.machine coldSlots (CloseoutFinalC10ColdCacheRewind.machine (BoundedFamilySupport.actualMachine source a k CH Cpad cutoff D G copies E K symDen thrDen (CloseoutMassThreshold.literalWidth delta copies) delta (CloseoutSampledWitness.massCap delta copies) code)))
      (4*(BoundedFamily.budget source a k CH Cpad cutoff D G copies E K symDen thrDen delta code x bits hpad)+2) (fun _ => 0) ambient (fun _ => 0) exit ∧
    readTapeBit (exit (coldSlots ((BoundedFamilySupport.flag source a k D G E).castAdd 1))) 0=true ∧
    exit (coldSlots ((((HeaderDock.old (BoundedFamily.workspace source a k D G E) 142).castAdd 1)).castAdd 1))=[BoundedFields.symmetric bits] ∧
    Step (RecoveryFocus.machine preSlots (C10PrologueUniform.prologueMachine e (RecoveryFocus.machine (CloseoutFinalC10SeedEngine.bankSlots (HierarchyPrefix.tapes k (CloseoutFinalC10SeedEngine.rp src) (CloseoutFinalC10SeedEngine.rq src)) r D (CloseoutFinalC10SeedEngine.readerIn src k)) (CloseoutFinalC10SeedEngine.engineMachine r D (CloseoutFinalC10SeedEngine.widthReader src k) (CloseoutFinalC10SeedEngine.readerQ src k) (C10PartsSchedule.thresholdFloor src))))) (C10PrologueUniform.prologueFuel D (C10PartsSchedule.widthAt src k) (CloseoutFinalC10SeedEngine.engineFuel r D (CloseoutFinalC10SeedEngine.readerFuel src k) (C10PartsSchedule.thresholdFloor src) (C10PartsSchedule.widthAt src k)) n) (fun _ => 0) exit H post ∧
    Step (RecoveryFocus.machine bodySlots (Composition.machine (DecompositionCountPosition.move (fun i : Fin B => if i=cache 13 ∨ i=cache 14 then .right else .stay)) (Composition.machine (RecoveryFocus.machine countSlots CloseoutRowsOriginalCount.machine) (Composition.machine (DecompositionCountPosition.move (fun i : Fin B => if i=cache 13 ∨ i=cache 14 then .left else .stay)) (RecoveryFocus.machine appendSlots CloseoutFinalC10AppendWorkspaceInit.machine))))) (countFuel+CloseoutFinalC10AppendWorkspaceInit.budget b+5) H post H
      (RecoveryRootRound.install bodySlots post finalBank) ∧
    ((∀ j,finalBank (cache j)=cacheData j) ∧ finalBank (countSlots 28)=UnaryTemplate.tape sys ∧ finalBank (countSlots 70)=UnaryTemplate.tape clauseCount ∧ finalBank (countSlots 72)=List.replicate clauseCount true ∧ finalBank (appendSlots 0)=List.replicate b true ∧ finalBank (appendSlots 20)=UnaryTemplate.tape (20*b+22) ∧ finalBank (appendSlots 39)=List.replicate (CloseoutFinalC10AppendWorkspaceInit.capacity b) false ∧ finalBank (appendSlots 40)=List.replicate (CloseoutFinalC10AppendWorkspaceInit.capacity b) false ∧ (∀ v,(∀ i,countSlots i≠v) → (∀ i,appendSlots i≠v) → finalBank v=actualBank v)) ∧
    (∀ j : Fin ((HeaderDock.tapes (BoundedFamily.workspace source a k D G E)+1)+1),2≤j.val → post (coldSlots j)=coldData j) ∧
    (∀ i : Fin 278,post ⟨i.val,by have := i.isLt;dsimp only [total];omega⟩=
      C10SupplierCall.bank [] (VerifierDecoding.CompareMachine.word 0) (List.replicate b true) (List.ofFn x) bits w i) ∧
    (∀ v : Fin B,v.val<L → v.val≠218 → finalBank v=actualBank v) ∧
    (∀ v : Fin B,L+96≤v.val → finalBank v=[]) ∧
    (∀ v,H v=if v.val=B then 1 else 0) ∧
    (RecoveryRootRound.install bodySlots post finalBank) ⟨B,by dsimp only [B,total];omega⟩=VerifierDecoding.CompareMachine.word N
     :=
  by
    classical
    intro e c old coldData P total B coldSlots preSlots flag ambient exit L bodySlots cache b N
    have cold := cold_entry source a k CH Cpad cutoff D G copies delta code n x hpad hD E K bits hK hcut hd hh hc hbudget symDen thrDen hsym hthr e Wsite admitted
    obtain ⟨coldRun,preInput,passFlag,modeByte,oracle,hdecode,hsize,cacheOld⟩ := cold
    let rq := ColdNative.request source a k CH Cpad code x hpad oracle
    have preInj : Function.Injective preSlots := by
      intro i j he
      have hv := congrArg Fin.val he
      have hi := i.isLt
      have hj := j.isLt
      apply Fin.ext
      dsimp only [preSlots] at hv
      clear * - hv hi hj
      split_ifs at hv <;> (try dsimp only [P,B,total] at *) <;> omega
    have focus0 := focused_prologue src k r D total
    have focus1 := focus0 preSlots
    have focus2 := focus1 n x bits exit
    have focus3 := focus2 hD preInj
    have focus4 := focus3 preInput
    obtain ⟨w,prologue,_offpre⟩ := focus4
    let prologueData : Fin (218+(60+(e+23))+1) → List Bool := Fin.addCases
      (C10SupplierCall.bank [] (VerifierDecoding.CompareMachine.word 0) (List.replicate b true) (List.ofFn x) bits w : Fin (218+(60+(e+23))) → List Bool)
      (fun _ : Fin 1 => VerifierDecoding.CompareMachine.word N)
    let post := RecoveryRootRound.install preSlots exit prologueData
    let H := dockH preSlots (fun _ => 0) (Fin.addCases (fun _ : Fin (218+(60+(e+23))) => 0) (fun _ : Fin 1 => 1))
    let actualBank := fun v : Fin B => post (bodySlots v)
    have fields := prologue_post c e Wsite (List.ofFn x) bits coldData w b N
    have localLow := cache_lower source a k D G E (BoundedFields.symmetric bits)
    have localInj := cache_injective source a k D G E (BoundedFields.symmetric bits)
    have cacheValue (j : Fin 19) : (cache j).val=P+(CloseoutFinalC10ColdCacheAtAdmission.cacheSlot source a k D G E (BoundedFields.symmetric bits) j).val-2 := rfl
    have cacheInj : Function.Injective cache := by
      intro i j he
      have hv := congrArg Fin.val he
      rw [cacheValue i,cacheValue j] at hv
      apply localInj
      apply Fin.ext
      dsimp only [P] at hv
      clear * - hv
      omega
    have cacheLow : ∀ j,278≤(cache j).val := by
      intro j
      rw [cacheValue]
      have lo := localLow j
      dsimp only [P]
      clear * - lo
      omega
    have cacheHigh : ∀ j,(cache j).val<L := by
      intro j
      rw [cacheValue]
      have hj := (CloseoutFinalC10ColdCacheAtAdmission.cacheSlot source a k D G E (BoundedFields.symmetric bits) j).isLt
      change _<c+1 at hj
      dsimp only [L,P]
      clear * - hj
      omega
    have cacheBytes : ∀ j,actualBank (cache j)=PCPPQueryIndexPadding.clauseData (pcppOutput rq (a.output rq)) rq.arity 0 (PCPPQueryCachedBounds.capacity a (rq.circuit.size+rq.arity)) [] j := by
      intro j
      let key := CloseoutFinalC10ColdCacheAtAdmission.cacheSlot source a k D G E (BoundedFields.symmetric bits) j
      have lowj := localLow j
      have retained := fields.1
      have frame0 := retained (key.castAdd 1)
      have frame := frame0 lowj
      have location : bodySlots (cache j)=coldSlots (key.castAdd 1) := by
        apply Fin.ext
        dsimp only [bodySlots,cache,coldSlots,Fin.val_castAdd,key]
        rw [if_neg (Nat.not_lt.mpr lowj)]
      have oldBytes := (cacheOld j).1
      have lifted := Fin.addCases_left (n:=1) (motive:=fun _ => List Bool) (left:=old.final.tapes) (right:=fun _ : Fin 1 => List.replicate old.steps false) key
      have liftedBytes := lifted.trans oldBytes
      have afterPre := frame.trans liftedBytes
      have placed := congrArg post location
      exact placed.trans afterPre
    have width : actualBank ⟨218,by clear * -;dsimp only [B,total];omega⟩=List.replicate b true := fields.2.2.1 218
    have fresh : ∀ v : Fin B,L≤v.val → actualBank v=[] := by
      intro v hv
      exact fields.2.1 (bodySlots v) hv v.isLt
    have hL : 278≤L := by clear * -;dsimp only [L,P];omega
    have space : L+96<B := by clear * -;dsimp only [B,total,L,P];omega
    let cacheData := PCPPQueryIndexPadding.clauseData (pcppOutput rq (a.output rq)) rq.arity 0 (PCPPQueryCachedBounds.capacity a (rq.circuit.size+rq.arity)) []
    let clauseCount := 2^(a.output rq).clauseBits
    let sys := (a.output rq).systematicBits
    let countFuel := CloseoutRowsOriginalCount.budget rq (a.output rq)
    let countSlots : Fin 74 → Fin B := fun i =>
      if hi : i.val<19 then cache ⟨i.val,hi⟩ else ⟨L+i.val-19,by have := i.isLt;omega⟩
    let appendSlots : Fin 42 → Fin B := fun i =>
      ⟨if i.val=0 then 218 else L+54+i.val,by have := i.isLt;split_ifs <;> omega⟩
    have init0 := actual_init B L hL space cache
    have init1 := init0 a rq b actualBank
    have init2 := init1 cacheInj cacheLow cacheHigh
    have init3 := init2 cacheBytes width fresh
    obtain ⟨finalBank,initRun,keepCache,S,Mt,Mr,keepb,template,copylog,resetlog,off⟩ := init3
    have bodyInj : Function.Injective bodySlots := by
      intro i j he
      exact Fin.ext (congrArg (fun v : Fin total => v.val) he)
    have hH : ∀ v,H (bodySlots v)=0 := by
      intro v
      have head := fields.2.2.2 (bodySlots v)
      exact head.trans (if_neg (show (bodySlots v).val≠B from Nat.ne_of_lt v.isLt))
    have initialized := (initRun.dock bodySlots bodyInj H post hH (fun _ => rfl)).congr
      (dockH_existing bodySlots H _ hH) rfl
    have countHigh (i : Fin 74) : (countSlots i).val<L+55 := by
      have hi := i.isLt
      dsimp only [countSlots]
      split_ifs with h
      · exact Nat.lt_trans (cacheHigh _) (by omega)
      · dsimp only
        omega
    have keepLow (v : Fin B) (hv : v.val<L) (h218 : v.val≠218) : finalBank v=actualBank v := by
      by_cases hc : ∃ j,cache j=v
      · obtain ⟨j,rfl⟩ := hc
        exact (keepCache j).trans (cacheBytes j).symm
      · apply off
        · intro i he
          have hi := i.isLt
          dsimp only [countSlots] at he
          split_ifs at he with h
          · exact hc ⟨_,he⟩
          · have hval := congrArg Fin.val he
            dsimp only at hval
            omega
        · intro i he
          have hval := congrArg Fin.val he
          dsimp only [appendSlots] at hval
          split_ifs at hval <;> omega
    have future (v : Fin B) (hv : L+96≤v.val) : finalBank v=[] := by
      rw [off v (by
        intro i he
        have bound := countHigh i
        change countSlots i=v at he
        rw [he] at bound
        clear * - bound hv
        omega) (by
        intro i he
        have hi := i.isLt
        have hval := congrArg Fin.val he
        dsimp only [appendSlots] at hval
        split_ifs at hval <;> omega)]
      exact fresh v (by omega)
    have gate := (gate_run total _ (C10LengthGate.counter onset (⟨0,by dsimp only [total];omega⟩ : Fin total) flag)
      (by dsimp only [total];omega) ⟨0,by dsimp only [total];omega⟩ flag flag onset n x bits rfl rfl honset).1
    refine ⟨oracle,hdecode,hsize,w,finalBank,gate,coldRun,passFlag,modeByte,prologue,initialized,
      ⟨keepCache,S,Mt,Mr,keepb,template,copylog,resetlog,off⟩,fields.1,fields.2.2.1,keepLow,future,fields.2.2.2,?_⟩
    rw [RecoveryRootRound.install_other bodySlots post finalBank _ (by
      intro v he
      have hi := v.isLt
      have hv := congrArg Fin.val he
      dsimp only [bodySlots] at hv
      omega)]
    let top : Fin (218+(60+(e+23))+1) := (0 : Fin 1).natAdd (218+(60+(e+23)))
    have topSlot : (⟨B,by dsimp only [B,total];omega⟩ : Fin total)=preSlots top := by
      apply Fin.ext
      simp only [preSlots,top,P,Fin.val_natAdd,Fin.val_zero]
      split_ifs <;> omega
    rw [topSlot]
    exact (RecoveryRootRound.install_slot preSlots preInj exit prologueData top).trans (Fin.addCases_right _)

end
end NearCubicWires.RepairOrdinary.CloseoutFinalC10AdmittedEntry
