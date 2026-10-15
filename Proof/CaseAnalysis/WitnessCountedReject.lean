import Proof.Amplification.RecoveryRepeatRejectedTape

/-! The existing rejecting repeater needs a body receipt only at the
actual guarded indices. No body runs at the exhausted end of the stream. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.CountedReject
open LocalBitMultitape RecoveryExecution RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
open private successful_cfg_eq from Proof.PCP.VerifierDecodingRejectingRepeat

def advance {α : Type} (next : ℕ → α → Bool×α) (x : ℕ×α) : Bool×(ℕ×α) :=
  ((next x.1 x.2).1,(x.1+1,(next x.1 x.2).2))

theorem driver_run {α : Type} {t s : ℕ} (body : Machine t s)
    (accepted : Fin s → (Fin t → Bool) → Bool) (source : ℕ → α → Configuration t s)
    (next : ℕ → α → Bool×α) (Inv : ℕ → α → Prop) (cost total : ℕ) (bit : Fin t)
    (hstart : ∀ j<total,∀ x,Inv j x → (source j x).control=body.start)
    (supplier : ∀ j<total,∀ x,Inv j x → ∃ r,runFrom body cost (source j x)=some r ∧ r.steps ≤ cost ∧
      accepted r.final.control r.final.scanned=(next j x).1 ∧
      ((next j x).1=true → r.final.heads=(source (j+1) (next j x).2).heads ∧
        r.final.tapes=(source (j+1) (next j x).2).tapes ∧ Inv (j+1) (next j x).2) ∧
      ((next j x).1=false → r.final.heads bit=0 ∧ r.final.tapes bit=[false]))
    (n pos : ℕ) (x : α) (hx : Inv pos x) (hn : pos+n=total) :
    ∃ r,runFrom (RepeatMachine.machine body accepted) (n*(cost+2)+total+3)
        (RepeatMachine.cfg 0 (source pos x) total (pos+1))=some r ∧
      r.steps ≤ n*(cost+2)+total+3 ∧
      RepeatMachine.Result (fun y=>source y.1 y.2) total
        (RepeatMachine.iterate (advance next) n (pos,x)) r.final ∧
      ((RepeatMachine.iterate (advance next) n (pos,x)).1=false →
        r.final.heads (bit.castAdd 1)=0 ∧ r.final.tapes (bit.castAdd 1)=[false]) := by
  induction n generalizing pos x with
  | zero =>
    have hp : pos=total := by omega
    subst pos
    obtain ⟨r,hr,hf,hs⟩ := (RepeatMachine.exhaust body accepted (source total x) total).run
      (by simp [RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])
    exact ⟨r,by simpa using hr,by simpa using hs.le,
      by simpa [RepeatMachine.Result,RepeatMachine.iterate] using hf,
      by simp only [RepeatMachine.iterate,Bool.true_eq_false,IsEmpty.forall_iff]⟩
  | succ n ih =>
    have hp : pos<total := by omega
    obtain ⟨r,hr,hrt,hra,hgood,hbad⟩ := supplier pos hp x hx
    have run := RepeatMachine.iteration body accepted (source pos x) total pos r (hstart pos hp x hx) hp hr
    rw [hra] at run
    cases hb : (next pos x).1 with
    | false =>
      obtain ⟨hh,ht⟩ := hbad hb
      simp only [hb,Bool.false_eq_true,↓reduceIte] at run
      obtain ⟨result,hresult,hfinal,hsteps⟩ := run.run
        (by simp [RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])
      have bound : r.steps+2 ≤ (n+1)*(cost+2)+total+3 := by nlinarith
      have more := runFrom_moreFuel (RepeatMachine.machine body accepted) (r.steps+2)
        ((n+1)*(cost+2)+total+3-(r.steps+2)) _ result hresult
      rw [Nat.add_sub_of_le bound] at more
      refine ⟨result,more,by omega,?_,?_⟩
      · simp [RepeatMachine.Result,RepeatMachine.iterate,advance,hb,hfinal,RepeatMachine.cfg,controlConfig]
      · intro _
        simpa only [hfinal,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,Fin.addCases_left] using And.intro hh ht
    | true =>
      obtain ⟨rh,rt,hi⟩ := hgood hb
      simp only [hb,↓reduceIte] at run
      have he := successful_cfg_eq r.final (source (pos+1) (next pos x).2) total (pos+2) rh rt
      rw [he] at run
      obtain ⟨tail,htail,htt,htf,htbad⟩ := ih (pos+1) (next pos x).2 hi (by omega)
      rcases run with ⟨space,run⟩
      obtain ⟨result,hresult,hfinal,hsteps,_⟩ := run.followedBy tail htail
      have bound : (r.steps+2)+(n*(cost+2)+total+3) ≤ (n+1)*(cost+2)+total+3 := by nlinarith
      have more := runFrom_moreFuel (RepeatMachine.machine body accepted) _
        ((n+1)*(cost+2)+total+3-((r.steps+2)+(n*(cost+2)+total+3))) _ result hresult
      rw [Nat.add_sub_of_le bound] at more
      refine ⟨result,more,?_,?_,?_⟩
      · rw [hsteps];nlinarith
      · simpa only [RepeatMachine.Result,RepeatMachine.iterate,advance,hb,↓reduceIte,hfinal] using htf
      · simpa only [RepeatMachine.iterate,advance,hb,↓reduceIte,hfinal] using htbad

theorem counted_run {α : Type} {t s : ℕ} (body : Machine t s)
    (accepted : Fin s → (Fin t → Bool) → Bool) (source : ℕ → α → Configuration t s)
    (next : ℕ → α → Bool×α) (Inv : ℕ → α → Prop) (cost total : ℕ) (bit : Fin t)
    (hstart : ∀ j<total,∀ x,Inv j x → (source j x).control=body.start)
    (supplier : ∀ j<total,∀ x,Inv j x → ∃ r,runFrom body cost (source j x)=some r ∧ r.steps ≤ cost ∧
      accepted r.final.control r.final.scanned=(next j x).1 ∧
      ((next j x).1=true → r.final.heads=(source (j+1) (next j x).2).heads ∧
        r.final.tapes=(source (j+1) (next j x).2).tapes ∧ Inv (j+1) (next j x).2) ∧
      ((next j x).1=false → r.final.heads bit=0 ∧ r.final.tapes bit=[false]))
    (x : α) (hx : Inv 0 x) :
    ∃ r,runFrom (RepeatMachine.machine body accepted) (total*(cost+3)+3)
        (RepeatMachine.cfg 0 (source 0 x) total 1)=some r ∧
      r.steps ≤ total*(cost+3)+3 ∧
      RepeatMachine.Result (fun y=>source y.1 y.2) total
        (RepeatMachine.iterate (advance next) total (0,x)) r.final ∧
      ((RepeatMachine.iterate (advance next) total (0,x)).1=false →
        r.final.heads (bit.castAdd 1)=0 ∧ r.final.tapes (bit.castAdd 1)=[false]) := by
  have h := driver_run body accepted source next Inv cost total bit hstart supplier total 0 x hx (by omega)
  have he : total*(cost+2)+total+3=total*(cost+3)+3 := by ring
  simpa only [he,Nat.zero_add] using h

end NearCubicWires.RepairOrdinary.CloseoutWitness.CountedReject
