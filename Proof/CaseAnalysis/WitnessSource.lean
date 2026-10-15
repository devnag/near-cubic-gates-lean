import Proof.CaseAnalysis.WitnessGuardedOracle
import Proof.CaseAnalysis.WitnessSelectedOracle

/-! The original framed input is counted once and screened against the
machine-owned finite cutoff. Only the passing branch runs the hierarchy
and the one selected PCP source; its original-N counter remains available. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.ColdSource
open LocalBitMultitape RecoveryRootRound RecoveryExecution RadixSemantics
open RepairSource ProjectionNormalization SourceInterfaces ExecutableInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
abbrev base (k : ℕ):=HierarchySelectedSource.tapes source k
def tapes (k : ℕ):=base source k+8
def old (k : ℕ) (i : Fin (base source k)) : Fin (tapes source k):=i.castAdd 8
def extra (k : ℕ) (i : Fin 8) : Fin (tapes source k):=i.natAdd (base source k)
def slots (k : ℕ) (i : Fin 8):=
  if i.val=0 then old source k (SelectedOracle.fields source k 0) else extra source k i
def input (k : ℕ) (x : List Bool) : Fin (tapes source k) → List Bool:=
  Fin.addCases (m:=base source k) (n:=8) (motive:=fun _=>List Bool)
    (HierarchySelectedSource.input source k x) (fun _=>[])
def first (k cutoff : ℕ):=RecoveryFocus.machine (slots source k) (InputGuard.machine (max 2 cutoff))
def second (k CH Cpad : ℕ) (code : List Bool):=
  RecoveryFocus.machine (old source k) (HierarchySelectedSource.machine source k CH Cpad code)
def machine (k CH Cpad cutoff : ℕ) (code : List Bool):=
  CloseoutRowsGateColdPair.machine (first source k cutoff) (second source k CH Cpad code)
    (fun scanned=>scanned (extra source k 6))
def budget (k CH Cpad cutoff : ℕ) (code x : List Bool):=
  InputGuard.budget (max 2 cutoff) x+1+
    (if max 2 cutoff ≤ x.length then HierarchySelectedSource.budget source k CH Cpad code x else 0)+1

theorem old_injective (k : ℕ) : Function.Injective (old source k):=by
  intro i j h;exact Fin.ext (congrArg (fun z : Fin (tapes source k)=>z.val) h)
theorem outside (k : ℕ) (j : Fin 8) : ∀ i,old source k i≠extra source k j:=by
  intro i h
  have hv:=congrArg (fun z : Fin (tapes source k)=>z.val) h
  change i.val=base source k+j.val at hv
  omega
theorem slots_injective (k : ℕ) : Function.Injective (slots source k):=by
  intro i j h
  have hv:=congrArg (fun z : Fin (tapes source k)=>z.val) h
  have bound:(SelectedOracle.fields source k 0).val < base source k:=(SelectedOracle.fields source k 0).isLt
  dsimp only [slots,old,extra] at hv
  split_ifs at hv <;> dsimp at hv <;> apply Fin.ext <;> omega

theorem source_run (k CH Cpad cutoff : ℕ) (code x : List Bool) (hpad : k+3 ≤ Cpad) :
    ∃ out,ClockJoin.ReadyRun (machine source k CH Cpad cutoff code)
      (budget source k CH Cpad cutoff code x) (input source k x) out ∧
      out (extra source k 2)=List.replicate x.length true ∧
      out (extra source k 6)=[decide (max 2 cutoff ≤ x.length)] ∧
      (max 2 cutoff ≤ x.length →
        HierarchySelectedSource.Fields source k CH Cpad code x
          (out ∘ old source k ∘ HierarchySelectedSource.old source k) ∧
        out (old source k (HierarchySelectedSource.outputTape source k))=
          (source.output (HierarchySelectedSource.request (HierarchyPadding.rawInput k CH Cpad code x))).word):=by
  have original:HierarchySelectedSource.input source k x (SelectedOracle.fields source k 0)=frame x:=by
    change HierarchySelectedSource.input source k x (HierarchySelectedSource.old source k
      (HierarchyPrefix.old k (HierarchySelectedSource.p source) (HierarchySelectedSource.q source)
        (HierarchyFramedInput.old k (HierarchyReduction.xTape k))))=frame x
    simp only [HierarchySelectedSource.input,HierarchySelectedSource.old,Fin.addCases_left]
    rfl
  obtain ⟨guard,hguard,hx,_count,rawN,flag⟩:=InputGuard.guard_run (max 2 cutoff) x
  have firstRun:=hguard.focus (slots source k) (slots_injective source k) (input source k x) (by
    intro j
    fin_cases j
    · change input source k x (old source k (SelectedOracle.fields source k 0))=frame x
      rw [input,old,Fin.addCases_left];exact original
    all_goals change input source k x (extra source k _)=[];rw [input,extra,Fin.addCases_right])
  let middle:=install (slots source k) (input source k x) guard
  have keep (i : Fin (base source k)) : middle (old source k i)=HierarchySelectedSource.input source k x i:=by
    by_cases hi:i=SelectedOracle.fields source k 0
    · subst i
      change install (slots source k) _ _ (slots source k 0)=_
      rw [install_slot _ (slots_injective source k)]
      exact hx.trans original.symm
    · dsimp only [middle]
      rw [install_other _ _ _ _ (by
        intro j hj
        by_cases hz:j.val=0
        · rw [slots,if_pos hz] at hj
          exact hi ((old_injective source k) hj.symm)
        · rw [slots,if_neg hz] at hj
          exact outside source k j i hj.symm),input,old,Fin.addCases_left]
  have midN:middle (extra source k 2)=List.replicate x.length true:=by
    change install (slots source k) _ _ (slots source k 2)=_
    rw [install_slot _ (slots_injective source k)];exact rawN
  have midFlag:middle (extra source k 6)=[decide (max 2 cutoff ≤ x.length)]:=by
    change install (slots source k) _ _ (slots source k 6)=_
    rw [install_slot _ (slots_injective source k)];exact flag
  by_cases live:max 2 cutoff ≤ x.length
  · obtain ⟨prior,hprior,hfields,word⟩:=HierarchySelectedSource.selected_run source k CH Cpad code x hpad
    have secondRun:=hprior.focus (old source k) (old_injective source k) middle keep
    have joined:=CloseoutRowsGateColdPair.joined (first source k cutoff) (second source k CH Cpad code)
      (fun scanned=>scanned (extra source k 6)) _ _ _ _ _ firstRun secondRun
      (by change readTapeBit (middle (extra source k 6)) 0=true;rw [midFlag];simp [live,readTapeBit])
    refine ⟨install (old source k) middle prior,?_,?_,?_,?_⟩
    · simpa only [machine,budget,if_pos live] using joined
    · rw [install_other _ _ _ _ (outside source k 2)];exact midN
    · rw [install_other _ _ _ _ (outside source k 6)];exact midFlag
    · intro _
      have ret:install (old source k) middle prior ∘ old source k=prior:=by
        funext i;exact install_slot _ (old_injective source k) _ _ i
      constructor
      · change HierarchySelectedSource.Fields source k CH Cpad code x
          ((install (old source k) middle prior ∘ old source k) ∘ HierarchySelectedSource.old source k)
        rw [ret];exact hfields
      · rw [install_slot _ (old_injective source k)];exact word
  · have rejected:=CloseoutRowsGateColdPair.rejected (first source k cutoff) (second source k CH Cpad code)
      (fun scanned=>scanned (extra source k 6)) _ _ _ firstRun
      (by change readTapeBit (middle (extra source k 6)) 0=false;rw [midFlag];simp [live,readTapeBit])
    refine ⟨middle,ClockJoin.enlarge (machine source k CH Cpad cutoff code) _ _ _ _ rejected
      (by unfold budget;rw [if_neg live];omega),midN,midFlag,fun h=>False.elim (live h)⟩

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.ColdSource
