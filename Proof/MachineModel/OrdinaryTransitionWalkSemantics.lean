import Proof.MachineModel.OrdinaryTransitionWalkReject

/-! Literal vectors parsed from the retained witness have exactly the
existing claimed-trace semantics. Only the requested n*t-bit prefix matters;
truncation, continuation through halt, and missing rules return none. -/
namespace NearCubicWires.RepairOrdinary.TransitionWalk
open LocalBitMultitape RecoveryExecution SignedSortKey MemoryLog
open RepairSource VerifierEncoding VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def vector (t : ℕ) (bits : List Bool) : Fin t→Bool := fun i=>bits.getD i.val false

theorem vector_word (t : ℕ) (bits : List Bool) (h : t≤bits.length) :
    List.ofFn (vector t bits)=bits.take t := by
  apply List.ext_getElem
  · simp [min_eq_left h]
  · intro i hi hj
    simp only [List.getElem_ofFn,List.getElem_take,vector]
    exact List.getD_eq_getElem bits false (by simp only [List.length_ofFn] at hi; omega)

theorem vector_prefix {t : ℕ} (reads : Fin t→Bool) (tail : List Bool) :
    vector t (List.ofFn reads++tail)=reads := by
  apply List.ofFn_injective
  rw [vector_word t _ (by simp)]
  simpa only [List.length_ofFn] using (List.take_left (l₁:=List.ofFn reads) (l₂:=tail))

def traceBits {t : ℕ} (claims : List (Fin t→Bool)) : List Bool := (claims.map List.ofFn).flatten

def evaluate (v : OrdinaryVerifier) : ClaimedTrace.View v.tapeCount v.stateCount→ℕ→List Bool→
    Option (ClaimedTrace.View v.tapeCount v.stateCount×List Event)
  | view,0,_=>some (view,[])
  | view,n+1,bits=>
    if v.tapeCount≤bits.length then
      if v.machine.halted view.control then none else
        match v.machine.rule view.control (vector v.tapeCount bits) with
        | none=>none
        | some a=>(evaluate v (ClaimedTrace.advance view a) n (bits.drop v.tapeCount)).map (fun result=>
            (result.1,MemoryTransition.batch view.heads (vector v.tapeCount bits)
              (fun i=>(a.write i).getD (vector v.tapeCount bits i))++result.2))
    else none

def accepted (v : OrdinaryVerifier) (view : ClaimedTrace.View v.tapeCount v.stateCount) (n : ℕ) (bits : List Bool) : Bool :=
  match evaluate v view n bits with
  | none=>false
  | some result=>v.machine.halted result.1.control && v.accepting result.1.control

theorem evaluate_trace (v : OrdinaryVerifier) (view : ClaimedTrace.View v.tapeCount v.stateCount)
    (claims : List (Fin v.tapeCount→Bool)) (tail : List Bool) :
    evaluate v view claims.length (traceBits claims++tail)=ClaimedTrace.check v.machine view claims := by
  induction claims generalizing view with
  | nil=>rfl
  | cons reads rest ih=>
    have hbits : traceBits (reads::rest)++tail=List.ofFn reads++(traceBits rest++tail) := by
      simp only [traceBits,List.map_cons,List.flatten_cons,List.append_assoc]
    have hlength : v.tapeCount≤(List.ofFn reads++(traceBits rest++tail)).length := by simp
    have hdrop : (List.ofFn reads++(traceBits rest++tail)).drop v.tapeCount=traceBits rest++tail := by
      simpa only [List.length_ofFn] using List.drop_left (l₁:=List.ofFn reads) (l₂:=traceBits rest++tail)
    rw [hbits,List.length_cons,evaluate,if_pos hlength,vector_prefix,hdrop]
    cases hh:v.machine.halted view.control with
    | true=>simp only [hh,↓reduceIte,ClaimedTrace.check]
    | false=>
      simp only [hh,Bool.false_eq_true,↓reduceIte,ClaimedTrace.check]
      cases ha:v.machine.rule view.control reads with
      | none=>rfl
      | some a=>
        dsimp only
        rw [ih]

theorem accepted_trace (v : OrdinaryVerifier) (view : ClaimedTrace.View v.tapeCount v.stateCount)
    (claims : List (Fin v.tapeCount→Bool)) (tail : List Bool) :
    accepted v view claims.length (traceBits claims++tail)=true ↔
      ∃ finalView events,ClaimedTrace.check v.machine view claims=some (finalView,events) ∧
        v.machine.halted finalView.control=true ∧ v.accepting finalView.control=true := by
  unfold accepted
  rw [evaluate_trace]
  cases he:ClaimedTrace.check v.machine view claims with
  | none=>simp
  | some result=>
    obtain ⟨finalView,events⟩ := result
    simp

end NearCubicWires.RepairOrdinary.TransitionWalk
