import Proof.SourceAssembly.SourceCacheBound

/- Exact counted native-field copy. Stops after the actual number of fields,
retaining the exact logical endpoint needed by the outer ordinary framer. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
namespace SourceAssemblyNativeList
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryExecution RepairOrdinary.RecoveryRootRound RepairRepresentation
open RepairSource.VerifierDecoding
open PCPPQueryField (saved store nat_run payload selected)
noncomputable section

def stream (xs : List Nat) := xs.flatMap natWord
def savedFields (xs : List Nat) (backing : List Bool) := xs.foldl (fun old n=>saved n old) backing
def machine := RepeatMachine.machine (PCPPQueryField.machine true) (fun _ _=>true)
def cfg (phase : Fin 5) (source : List Bool) (pos : Nat) (backing out : List Bool)
    (total driver : Nat) := RepeatMachine.cfg phase
      (store (s:=4) 0 source pos backing out) total driver

theorem remaining (pre : List Bool) (xs : List Nat) (tail backing out : List Bool)
    (total pos : Nat) (hn : pos+xs.length=total) :
    Timed machine ((stream xs).length+4*xs.length+total+3)
      (cfg 0 (pre++stream xs++tail) pre.length backing out total (pos+1))
      (cfg 3 (pre++stream xs++tail) (pre.length+(stream xs).length)
        (savedFields xs backing) (out++stream xs) total 1) := by
  induction xs generalizing pre backing out pos with
  | nil =>
    have hp : pos=total := by simpa using hn
    subst pos
    simpa only [machine,cfg,stream,savedFields,List.flatMap_nil,List.foldl_nil,
      List.append_nil,List.length_nil,Nat.mul_zero,Nat.zero_add,Nat.add_zero]
      using RepeatMachine.exhaust (PCPPQueryField.machine true) (fun _ _=>true)
        (store (s:=4) 0 (pre++tail) pre.length backing out) total
  | cons x xs ih =>
    obtain ⟨r,hr,hf,hs⟩ := nat_run true pre (stream xs++tail) backing out x
    have hfinal : r.final=store (s:=4) 3 (pre++natWord x++(stream xs++tail))
        (pre.length+(natWord x).length) (saved x backing) (out++natWord x) := by
      rw [hf]
      simp only [payload,store,PCPPQueryField.cfg,saved,selected,↓reduceIte,
        DecompositionSource.natWord_length,Nat.add_assoc]
    have hstep := RepeatMachine.iteration (PCPPQueryField.machine true) (fun _ _=>true)
      (store (s:=4) 0 (pre++natWord x++(stream xs++tail)) pre.length backing out)
      total pos r (by rfl) (by simp only [List.length_cons] at hn;omega) hr
    rw [hfinal,hs] at hstep
    have htail := ih (pre++natWord x) (saved x backing) (out++natWord x) (pos+1)
      (by simp only [List.length_cons] at hn;omega)
    have hsource : (pre++natWord x)++stream xs++tail=pre++natWord x++(stream xs++tail) := by
      simp only [List.append_assoc]
    have hmid : cfg 0 (pre++natWord x++(stream xs++tail))
        (pre.length+(natWord x).length) (saved x backing) (out++natWord x) total (pos+2)=
      cfg 0 ((pre++natWord x)++stream xs++tail) (pre++natWord x).length
        (saved x backing) (out++natWord x) total ((pos+1)+1) := by
      rw [hsource,List.length_append]
    change Timed machine (2*natBitLength x+3+2)
      (cfg 0 (pre++natWord x++(stream xs++tail)) pre.length backing out total (pos+1))
      (cfg 0 (pre++natWord x++(stream xs++tail))
        (pre.length+(natWord x).length) (saved x backing) (out++natWord x) total (pos+2)) at hstep
    rw [hmid] at hstep
    have hall := hstep.trans htail
    have htime : 2*natBitLength x+3+2+((stream xs).length+4*xs.length+total+3)=
        (stream (x::xs)).length+4*(x::xs).length+total+3 := by
      simp only [stream,List.flatMap_cons,List.length_append,List.length_cons,
        DecompositionSource.natWord_length]
      omega
    rw [htime] at hall
    simpa only [stream,List.flatMap_cons,List.append_assoc,List.length_append,
      savedFields,List.foldl_cons,Nat.add_assoc] using hall

theorem copy_run (pre : List Bool) (xs : List Nat) (tail backing out : List Bool) :
    ∃ r,runFrom machine ((stream xs).length+5*xs.length+3)
      (cfg 0 (pre++stream xs++tail) pre.length backing out xs.length 1)=some r ∧
      r.final=cfg 3 (pre++stream xs++tail) (pre.length+(stream xs).length)
        (savedFields xs backing) (out++stream xs) xs.length 1 ∧
      r.steps=(stream xs).length+5*xs.length+3 := by
  have h := remaining pre xs tail backing out xs.length 0 (by omega)
  have ht : (stream xs).length+4*xs.length+xs.length+3=(stream xs).length+5*xs.length+3 := by omega
  rw [ht] at h
  exact h.run (by simp [machine,cfg,RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])

end
end SourceAssemblyNativeList
