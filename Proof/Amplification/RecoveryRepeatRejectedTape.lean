import Proof.Amplification.RecoveryValuationCountTapes

/-! A physical result-bit consequence for the existing rejecting repeat
machine. Failed bodies retain their real zero-head false result cell. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.RepeatMachine
open LocalBitMultitape RepairOrdinary RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
open private successful_cfg_eq from Proof.PCP.VerifierDecodingRejectingRepeat

theorem rejecting_driver_tape {α : Type} {t s : Nat} (body : Machine t s)
    (accepted : Fin s → (Fin t → Bool) → Bool) (source : α → Configuration t s)
    (next : α → Bool×α) (Inv : α → Prop) (cost : Nat) (bit : Fin t)
    (hstart : ∀ x,Inv x → (source x).control=body.start)
    (supplier : ∀ x,Inv x → ∃ r,runFrom body cost (source x)=some r ∧ r.steps≤cost ∧
      accepted r.final.control r.final.scanned=(next x).1 ∧
      ((next x).1=true  → r.final.heads=(source (next x).2).heads ∧
        r.final.tapes=(source (next x).2).tapes ∧ Inv (next x).2) ∧
      ((next x).1=false  → r.final.heads bit=0 ∧ r.final.tapes bit=[false]))
    (n total pos : Nat) (x : α) (hx : Inv x) (hn : pos+n=total) :
    ∃ r,runFrom (machine body accepted) (n*(cost+2)+total+3)
        (cfg 0 (source x) total (pos+1))=some r ∧
      r.steps≤n*(cost+2)+total+3 ∧ Result source total (iterate next n x) r.final ∧
      ((iterate next n x).1=false  → r.final.heads (bit.castAdd 1)=0 ∧ r.final.tapes (bit.castAdd 1)=[false]) := by
  induction n generalizing pos x with
  | zero =>
    have hpos : pos=total := by omega
    subst pos
    obtain ⟨r,hr,hf,hs⟩ := (exhaust body accepted (source x) total).run
      (by simp [machine,cfg,controlConfig,phaseCode])
    exact ⟨r,by simpa using hr,by simpa using hs.le,by simpa [Result,iterate] using hf,
      by simp only [iterate,Bool.true_eq_false,IsEmpty.forall_iff]⟩
  | succ n ih =>
    obtain ⟨r,hr,hrt,hra,hgood,hbad⟩ := supplier x hx
    have hp := iteration body accepted (source x) total pos r (hstart x hx) (by omega) hr
    rw [hra] at hp
    cases hb : (next x).1 with
    | false =>
      obtain ⟨hh,ht⟩ := hbad hb
      simp only [hb,Bool.false_eq_true,↓reduceIte] at hp
      obtain ⟨result,hresult,hfinal,hsteps⟩ := hp.run
        (by simp [machine,cfg,controlConfig,phaseCode])
      have htime : r.steps+2≤(n+1)*(cost+2)+total+3 := by nlinarith
      have hm := runFrom_moreFuel (machine body accepted) (r.steps+2)
        ((n+1)*(cost+2)+total+3-(r.steps+2)) _ result hresult
      rw [Nat.add_sub_of_le htime] at hm
      refine ⟨result,hm,by omega,?_,?_⟩
      · simp [Result,iterate,hb,hfinal,cfg,controlConfig]
      · intro _
        simpa only [hfinal,cfg,controlConfig,TapeEmbedding.config,Fin.addCases_left] using And.intro hh ht
    | true =>
      obtain ⟨hrh,hrp,hinv⟩ := hgood hb
      simp only [hb,↓reduceIte] at hp
      have he := successful_cfg_eq r.final (source (next x).2) total (pos+2) hrh hrp
      rw [he] at hp
      obtain ⟨tail,htail,htt,htf,htbad⟩ := ih (pos+1) (next x).2 hinv (by omega)
      rcases hp with ⟨space,hp⟩
      obtain ⟨result,hresult,hfinal,hsteps,_⟩ := hp.followedBy tail htail
      have htime : (r.steps+2)+(n*(cost+2)+total+3)≤(n+1)*(cost+2)+total+3 := by nlinarith
      have hm := runFrom_moreFuel (machine body accepted) _
        ((n+1)*(cost+2)+total+3-((r.steps+2)+(n*(cost+2)+total+3))) _ result hresult
      rw [Nat.add_sub_of_le htime] at hm
      refine ⟨result,hm,?_,?_,?_⟩
      · rw [hsteps]; nlinarith
      · simpa only [Result,iterate,hb,↓reduceIte,hfinal] using htf
      · simpa only [iterate,hb,↓reduceIte,hfinal] using htbad

theorem rejecting_repeat_tape {α : Type} {t s : Nat} (body : Machine t s)
    (accepted : Fin s → (Fin t → Bool) → Bool) (source : α → Configuration t s)
    (next : α → Bool×α) (Inv : α → Prop) (cost : Nat) (bit : Fin t)
    (hstart : ∀ x,Inv x → (source x).control=body.start)
    (supplier : ∀ x,Inv x → ∃ r,runFrom body cost (source x)=some r ∧ r.steps≤cost ∧
      accepted r.final.control r.final.scanned=(next x).1 ∧
      ((next x).1=true  → r.final.heads=(source (next x).2).heads ∧
        r.final.tapes=(source (next x).2).tapes ∧ Inv (next x).2) ∧
      ((next x).1=false  → r.final.heads bit=0 ∧ r.final.tapes bit=[false]))
    (total : Nat) (x : α) (hx : Inv x) :
    ∃ r,runFrom (machine body accepted) (total*(cost+3)+3) (cfg 0 (source x) total 1)=some r ∧
      r.steps≤total*(cost+3)+3 ∧ Result source total (iterate next total x) r.final ∧
      ((iterate next total x).1=false  → r.final.heads (bit.castAdd 1)=0 ∧ r.final.tapes (bit.castAdd 1)=[false]) := by
  have h := rejecting_driver_tape body accepted source next Inv cost bit hstart supplier total total 0 x hx (by omega)
  have he : total*(cost+2)+total+3=total*(cost+3)+3 := by ring
  simpa only [he,Nat.zero_add] using h

end NearCubicWires.RepairSource.VerifierDecoding.RepeatMachine
