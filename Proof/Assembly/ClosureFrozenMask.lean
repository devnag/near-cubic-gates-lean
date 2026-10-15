import Proof.Assembly.ClosureFrozenMaskSemantics
import Proof.CaseAnalysis.RowsDegreeLoop
import Proof.Assembly.FinalPoolMaskDock

/-! A fixed ordinary scatter pass. Membership controls whether the next
compressed assignment bit is read; the output has one bit per original
coordinate. Runtime source words and the repetition counter are retained. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.FrozenMask
open LocalBitMultitape RepairOrdinary RecoveryExecution ExtDecompositionBatch
open RepairSource.VerifierDecoding RepairSource.CloseoutFinal

def body : Machine 3 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => decide (q = 1)
  rule := fun q scan => if q = 0 then
    some ⟨1, ![none, none, some (scan 0 && scan 1)],
      ![.right, if scan 0 then .right else .stay, .right]⟩ else none
def heads (mp yp : Nat) (out : List Bool) : Fin 3 → Nat := ![mp, yp, out.length]
def data (membership assignment out : List Bool) : Fin 3 → List Bool :=
  ![membership, assignment, out]
def source {s : Nat} (c : Fin s) (mp yp : Nat) (membership assignment out : List Bool) :
    Configuration 3 s := ⟨c, heads mp yp out, data membership assignment out⟩

theorem body_run (x : Bool × Bool) (mpre mtail ypre ytail out : List Bool) :
    Step body 1 (heads mpre.length ypre.length out)
      (data (mpre ++ x.1 :: mtail) (ypre ++ selected [x] ++ ytail) out)
      (heads (mpre.length + 1) (ypre.length + (selected [x]).length) (out ++ values [x]))
      (data (mpre ++ x.1 :: mtail) (ypre ++ selected [x] ++ ytail) (out ++ values [x])) := by
  have hs : step body (source 0 mpre.length ypre.length
      (mpre ++ x.1 :: mtail) (ypre ++ selected [x] ++ ytail) out) =
      some (source 1 (mpre.length + 1) (ypre.length + (selected [x]).length)
        (mpre ++ x.1 :: mtail) (ypre ++ selected [x] ++ ytail) (out ++ values [x])) := by
    rcases x with ⟨a,b⟩
    cases a <;> simp [step, body, source, heads, data, Configuration.scanned, selected, values]
    all_goals apply configuration_ext
    all_goals first | rfl | (funext i; fin_cases i <;> simp [applyAction, HeadMove.apply,
      Streaming.read_append, Streaming.write_append])
  obtain ⟨r,hr,hf,_⟩ := (Timed.single (by rfl) hs).run (by rfl)
  exact Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)

noncomputable def machine := RepeatMachine.machine body (fun _ _ => true)
noncomputable def cfg (phase : Fin 5) (mp yp : Nat) (membership assignment out : List Bool)
    (total driver : Nat) := RepeatMachine.cfg phase
      (source body.start mp yp membership assignment out) total driver

theorem remaining (xs : List (Bool × Bool)) (mpre mtail ypre ytail out : List Bool)
    (total pos : Nat) (hn : pos + xs.length = total) :
    ∃ time ≤ 3*xs.length + total + 3, Timed machine time
      (cfg 0 mpre.length ypre.length (mpre ++ xs.map Prod.fst ++ mtail)
        (ypre ++ selected xs ++ ytail) out total (pos+1))
      (cfg 3 (mpre.length + xs.length) (ypre.length + (selected xs).length)
        (mpre ++ xs.map Prod.fst ++ mtail) (ypre ++ selected xs ++ ytail)
        (out ++ values xs) total 1) := by
  induction xs generalizing mpre ypre out pos with
  | nil =>
    have hp : pos = total := by simpa using hn
    subst pos
    refine ⟨total+3, by simp, ?_⟩
    simpa [machine, cfg, selected, values] using RepeatMachine.exhaust body (fun _ _ => true)
      (source body.start mpre.length ypre.length (mpre ++ mtail) (ypre ++ ytail) out) total
  | cons x xs ih =>
    obtain ⟨r,hr,rh,rt,rs⟩ := body_run x mpre (xs.map Prod.fst ++ mtail)
      ypre (selected xs ++ ytail) out
    have one := RepeatMachine.iteration body (fun _ _ => true)
      (source body.start mpre.length ypre.length (mpre ++ x.1 :: (xs.map Prod.fst ++ mtail))
        (ypre ++ selected [x] ++ (selected xs ++ ytail)) out)
      total pos r rfl (by simp only [List.length_cons] at hn; omega) hr
    simp only [if_true] at one
    rw [RowOccurrenceLoop.cfg_eq 0 r.final
      (source body.start (mpre.length+1) (ypre.length+(selected [x]).length)
        (mpre ++ x.1 :: (xs.map Prod.fst ++ mtail))
        (ypre ++ selected [x] ++ (selected xs ++ ytail)) (out ++ values [x]))
      total (pos+2) rh rt] at one
    obtain ⟨t,ht,rest⟩ := ih (mpre ++ [x.1]) (ypre ++ selected [x])
      (out ++ values [x]) (pos+1) (by simp only [List.length_cons] at hn; omega)
    have sel : selected (x::xs) = selected [x] ++ selected xs := by
      simp only [selected, List.filterMap_cons, List.filterMap_nil]
      cases x.1 <;> rfl
    have val : values (x::xs) = values [x] ++ values xs := rfl
    simp only [List.length_append, List.length_singleton, List.append_assoc,
      List.singleton_append, show pos+1+1=pos+2 by omega] at rest
    simp only [List.append_assoc,List.cons_append] at one rest
    have all := one.trans rest
    refine ⟨r.steps+2+t, by simp only [List.length_cons] at ⊢; omega, ?_⟩
    simpa only [machine, cfg, sel, val, List.length_cons, List.map_cons,
      List.cons_append, List.append_assoc, List.length_append, Nat.add_assoc,
      Nat.add_comm 1 xs.length] using all

theorem scatter_run (xs : List (Bool × Bool)) (out : List Bool) :
    Step machine (4*xs.length+3)
      (Fin.addCases (heads 0 0 out) (fun _ : Fin 1 => 1))
      (Fin.addCases (data (xs.map Prod.fst) (selected xs) out)
        (fun _ : Fin 1 => CompareMachine.word xs.length))
      (Fin.addCases (heads xs.length (selected xs).length (out ++ values xs)) (fun _ : Fin 1 => 1))
      (Fin.addCases (data (xs.map Prod.fst) (selected xs) (out ++ values xs))
        (fun _ : Fin 1 => CompareMachine.word xs.length)) := by
  obtain ⟨time,ht,trace⟩ := remaining xs [] [] [] [] out xs.length 0 (by omega)
  obtain ⟨r,hr,hf,_⟩ := trace.run (by simp [machine,cfg,RepeatMachine.machine,RepeatMachine.cfg,
    controlConfig,RepeatMachine.phaseCode])
  have actual := Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)
  have bound : time ≤ 4*xs.length+3 := by omega
  simpa only [cfg,source,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,
    List.nil_append,List.append_nil,List.length_nil,Nat.zero_add] using actual.enlarge bound

theorem mask_run {q : Nat} (live : Finset (Fin q)) (y : BitInput live.card) (out : List Bool) :
    let word := List.ofFn (C10NaturalHardwireScore.frozenMask live y)
    Step machine (4*q+3) (![0,0,out.length,1] : Fin 4 → Nat)
      ![CloseoutRowsGateSupport.gateMembers live,List.ofFn y,out,CompareMachine.word q]
      (![q,live.card,(out ++ word).length,1] : Fin 4 → Nat)
      ![CloseoutRowsGateSupport.gateMembers live,List.ofFn y,out ++ word,CompareMachine.word q] := by
  have h := scatter_run (pairs live y) out
  have len : (pairs live y).length = q := List.length_ofFn
  rw [membership_pairs, selected_pairs, values_pairs, len, List.length_ofFn] at h
  refine (h.congr_in ?_ ?_).congr ?_ ?_
  all_goals funext i;fin_cases i <;> rfl

def resetSelected (i : Fin 4) : Bool := decide (i.val < 3)
noncomputable def readyMachine := MaskedReset.machine machine resetSelected

theorem ready_run {q : Nat} (live : Finset (Fin q)) (y : BitInput live.card) (D : Nat)
    (hD : 4*q+3 ≤ D) :
    Step readyMachine (8*q+8) (![0,0,0,1,0] : Fin 5 → Nat)
      ![CloseoutRowsGateSupport.gateMembers live,List.ofFn y,[],CompareMachine.word q,
        List.replicate D false]
      (![0,0,0,1,0] : Fin 5 → Nat)
      ![CloseoutRowsGateSupport.gateMembers live,List.ofFn y,
        List.ofFn (C10NaturalHardwireScore.frozenMask live y),CompareMachine.word q,
        List.replicate D false] := by
  have h := (mask_run live y []).mask resetSelected (by
    intro i hi
    fin_cases i <;> first | rfl | contradiction) hD
  have cost : 2*(4*q+3)+2=8*q+8 := by omega
  rw [cost] at h
  refine (h.congr_in ?_ ?_).congr ?_ ?_
  all_goals funext i;fin_cases i <;> rfl

end NearCubicWires.P1Closure.FrozenMask
