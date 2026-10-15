import Proof.MachineModel.UEmissionLanguage
import Proof.MachineModel.UAggregateClock

/-! An actual bounded accepting run supplies a literal certificate, with
the same choice word and a count followed by its actual scanned vectors.
Unused suffix bits can pad that certificate to the fixed U clock exactly. -/
namespace NearCubicWires.RepairOrdinary.UEmission
open LocalBitMultitape SignedSortKey RepairSource VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem traceBits_length {t : ℕ} (claims : List (Fin t → Bool)) :
    (TransitionWalk.traceBits claims).length=t*claims.length := by
  induction claims with
  | nil => simp [TransitionWalk.traceBits]
  | cons reads rest ih =>
    simp only [TransitionWalk.traceBits,List.map_cons,List.flatten_cons,List.length_append,
      List.length_ofFn,List.length_cons] at ih ⊢
    rw [ih,Nat.mul_add,Nat.mul_one]
    omega

theorem complete_prefix (raw word input bound padding choices : List Bool) (v : OrdinaryVerifier)
    (hsource : raw=VerifierInputFields.source word input bound padding)
    (hguards : UInputScalars.Guards raw input bound)
    (hdecoded : decode raw.length word=some v) (hcode : word.length ≤ Nat.log 2 raw.length)
    (hchoices : choices.length=RadixSemantics.value bound)
    (ha : v.acceptsAt choices.length input choices) :
    ∃ (count : ℕ) (claims : List (Fin v.tapeCount → Bool)), count ≤ choices.length ∧ claims.length=count ∧
      ∀ tail,Accepted raw (binary (ClockDyadicLedger.width raw.length) count ++ choices ++
        (TransitionWalk.traceBits claims ++ tail)) := by
  obtain ⟨r,hr,haccept⟩ := ha
  have hsteps := runFrom_steps_le v.machine choices.length _ r hr
  obtain ⟨claims,events,hlen,_,_,_,hcomplete,hmemory⟩ :=
    MemoryChecker.evaluation_complete v input choices choices.length r hr haccept
  refine ⟨r.steps,claims,hsteps,hlen,?_⟩
  intro tail
  let d : TraceData := ⟨v,word,input,bound,padding,choices,r.steps,TransitionWalk.traceBits claims ++ tail⟩
  have hf : Fields raw (binary (ClockDyadicLedger.width raw.length) r.steps ++ choices ++
      (TransitionWalk.traceBits claims ++ tail)) d :=
    ⟨hsource,hguards,hdecoded,hcode,rfl,by rw [hchoices]; exact hguards.2.1,
      by rw [hchoices]; exact hguards.2.2,hsteps,hchoices⟩
  obtain ⟨heval,hdecision⟩ := hcomplete tail
  have hflags : v.machine.halted r.final.control=true ∧ v.accepting r.final.control=true := by
    unfold TransitionWalk.accepted at hdecision
    rw [heval] at hdecision
    simpa only [Bool.and_eq_true,ClaimedTrace.view] using hdecision
  have hready := hf.evaluation_ready (ClaimedTrace.view r.final) events heval
  have hm := hmemory (2*ClockDyadicLedger.width raw.length) (ClockDyadicLedger.width raw.length) hready
  rw [MemoryChecker.list_result] at hm
  exact ⟨d,hf,ClaimedTrace.view r.final,events,heval,hflags.1,hflags.2,hm⟩

theorem complete_bounded (raw word input bound padding choices : List Bool) (v : OrdinaryVerifier)
    (hsource : raw=VerifierInputFields.source word input bound padding)
    (hguards : UInputScalars.Guards raw input bound)
    (hdecoded : decode raw.length word=some v) (hcode : word.length ≤ Nat.log 2 raw.length)
    (hchoices : choices.length=RadixSemantics.value bound)
    (ha : v.acceptsAt choices.length input choices) :
    ∃ witness,witness.length=UAggregateClock.time raw.length ∧ Accepted raw witness := by
  obtain ⟨count,claims,hcount,hlen,hall⟩ :=
    complete_prefix raw word input bound padding choices v hsource hguards hdecoded hcode hchoices ha
  let certificatePrefix := binary (ClockDyadicLedger.width raw.length) count ++ choices ++ TransitionWalk.traceBits claims
  have hprefix : certificatePrefix.length=ClockDyadicLedger.width raw.length+choices.length+v.tapeCount*count := by
    simp only [certificatePrefix,List.length_append,binary_length,traceBits_length,hlen]
  have hN : 2 ≤ raw.length := by
    rw [hsource]
    simp only [VerifierInputFields.source,List.length_append,frame_length]
    omega
  have htapes : v.tapeCount ≤ word.length := by
    rw [←(decode_code_length hdecoded).2]
    exact VerifierEncoding.tapes_le_code_length v
  have hb := ClockDyadicLedger.guarded_bounds raw.length input.length choices.length count
    v.tapeCount word.length hN (by rw [hchoices]; exact hguards.2.1)
    (by rw [hchoices]; exact hguards.2.2) hcount htapes hcode
  have hfit : certificatePrefix.length ≤ UAggregateClock.time raw.length :=
    UAggregateClock.witness_le_time raw.length certificatePrefix.length (by rw [hprefix]; exact hb.2.2.2)
  let tail := List.replicate (UAggregateClock.time raw.length-certificatePrefix.length) false
  refine ⟨certificatePrefix ++ tail,?_,?_⟩
  · simp only [List.length_append,tail,List.length_replicate,Nat.add_sub_of_le hfit]
  · simpa only [certificatePrefix,List.append_assoc] using hall tail

/-- The bounded universal source language: the input carries its verifier
and bound, and the same length-B choice word has an accepting B-step run. -/
def SourceAccepted (raw : List Bool) : Prop :=
  ∃ v : OrdinaryVerifier, ∃ word input bound padding choices,
    raw=VerifierInputFields.source word input bound padding ∧ UInputScalars.Guards raw input bound ∧
    decode raw.length word=some v ∧ word.length ≤ Nat.log 2 raw.length ∧
    choices.length=RadixSemantics.value bound ∧ v.acceptsAt choices.length input choices

theorem Accepted.source {raw witness : List Bool} (h : Accepted raw witness) : SourceAccepted raw := by
  obtain ⟨d,hf,haccept⟩ := h.sound
  obtain ⟨r,hr,ha⟩ := haccept
  have hm := run_moreFuel d.verifier.machine d.count (d.choices.length-d.count)
    (d.verifier.inputTapes d.input d.choices) r hr
  rw [Nat.add_sub_of_le hf.count_bound] at hm
  exact ⟨d.verifier,d.word,d.input,d.bound,d.padding,d.choices,hf.source,hf.guards,hf.decoded,
    hf.code_bound,hf.choices_length,r,hm,ha⟩

theorem bounded_language_iff (raw : List Bool) :
    (∃ witness,witness.length=UAggregateClock.time raw.length ∧ Accepted raw witness) ↔ SourceAccepted raw := by
  constructor
  · rintro ⟨_,_,ha⟩
    exact ha.source
  · rintro ⟨v,word,input,bound,padding,choices,hs,hg,hd,hc,hB,ha⟩
    exact complete_bounded raw word input bound padding choices v hs hg hd hc hB ha

theorem bitInput_language_iff (raw : List Bool) :
    (∃ witness : BitInput (UAggregateClock.time raw.length),
      Accepted raw (List.ofFn witness)) ↔ SourceAccepted raw := by
  constructor
  · rintro ⟨_,ha⟩
    exact ha.source
  · intro ha
    obtain ⟨witness,hlen,hw⟩ := (bounded_language_iff raw).2 ha
    rw [←hlen]
    exact ⟨witness.get,by simpa only [List.ofFn_get] using hw⟩

end NearCubicWires.RepairOrdinary.UEmission
