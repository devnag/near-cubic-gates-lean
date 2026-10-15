import Proof.MachineModel.OrdinaryTransitionWalkCertificate

/-! A successful literal-prefix evaluation extracts exactly n claimed
vectors for the existing soundness theorem. This covers arbitrary witnesses,
not only witnesses initially supplied in a vector-list representation. -/
namespace NearCubicWires.RepairOrdinary.TransitionWalk
open LocalBitMultitape RecoveryExecution SignedSortKey MemoryLog
open RepairSource VerifierEncoding VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem evaluate_implies_trace (v : OrdinaryVerifier) (n : ℕ)
    (view : ClaimedTrace.View v.tapeCount v.stateCount) (bits : List Bool)
    (finalView : ClaimedTrace.View v.tapeCount v.stateCount) (events : List Event)
    (he : evaluate v view n bits=some (finalView,events)) :
    ∃ claims padding,claims.length=n ∧ bits=traceBits claims++padding ∧
      ClaimedTrace.check v.machine view claims=some (finalView,events) := by
  induction n generalizing view bits finalView events with
  | zero=>
    refine ⟨[],bits,rfl,?_,he⟩
    rfl
  | succ n ih=>
    by_cases hfit:v.tapeCount≤bits.length
    · cases hhalt:v.machine.halted view.control with
      | true=>simp only [evaluate,if_pos hfit,hhalt,↓reduceIte] at he; cases he
      | false=>
        cases ha:v.machine.rule view.control (vector v.tapeCount bits) with
        | none=>simp only [evaluate,if_pos hfit,hhalt,Bool.false_eq_true,↓reduceIte,ha] at he; cases he
        | some a=>
          rw [evaluate_step v view n bits a hfit hhalt ha] at he
          cases htail:evaluate v (ClaimedTrace.advance view a) n (bits.drop v.tapeCount) with
          | none=>simp only [htail,Option.map_none] at he; cases he
          | some result=>
            obtain ⟨lastView,lastEvents⟩ := result
            have heq : (lastView,MemoryTransition.batch view.heads (vector v.tapeCount bits)
                (fun i=>(a.write i).getD (vector v.tapeCount bits i))++lastEvents)=(finalView,events) := by
              simpa only [htail,Option.map_some,Option.some.injEq] using he
            obtain ⟨rfl,rfl⟩ := Prod.mk.inj heq
            obtain ⟨claims,padding,hlen,hbits,hcheck⟩ := ih (ClaimedTrace.advance view a) (bits.drop v.tapeCount) lastView lastEvents htail
            refine ⟨vector v.tapeCount bits::claims,padding,by simp only [List.length_cons,hlen],?_,?_⟩
            · change bits=(List.ofFn (vector v.tapeCount bits)++traceBits claims)++padding
              rw [vector_word _ _ hfit,List.append_assoc,←hbits,List.take_append_drop]
            · simp only [ClaimedTrace.check,hhalt,Bool.false_eq_true,↓reduceIte,ha,hcheck,Option.map_some]
    · simp only [evaluate,if_neg hfit] at he
      cases he

theorem evaluate_iff_trace (v : OrdinaryVerifier) (n : ℕ)
    (view : ClaimedTrace.View v.tapeCount v.stateCount) (bits : List Bool)
    (finalView : ClaimedTrace.View v.tapeCount v.stateCount) (events : List Event) :
    evaluate v view n bits=some (finalView,events) ↔
      ∃ claims padding,claims.length=n ∧ bits=traceBits claims++padding ∧
        ClaimedTrace.check v.machine view claims=some (finalView,events) := by
  constructor
  · exact evaluate_implies_trace v n view bits finalView events
  · rintro ⟨claims,padding,hlen,rfl,hcheck⟩
    rw [←hlen,evaluate_trace]
    exact hcheck

theorem accepted_iff (v : OrdinaryVerifier) (view : ClaimedTrace.View v.tapeCount v.stateCount)
    (n : ℕ) (bits : List Bool) :
    accepted v view n bits=true ↔ ∃ finalView events,
      evaluate v view n bits=some (finalView,events) ∧
      v.machine.halted finalView.control=true ∧ v.accepting finalView.control=true := by
  unfold accepted
  cases he:evaluate v view n bits with
  | none=>simp
  | some result=>obtain ⟨finalView,events⟩ := result; simp

end NearCubicWires.RepairOrdinary.TransitionWalk
