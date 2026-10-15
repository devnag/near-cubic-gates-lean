import Proof.PCP.VerifierDecodingGuardedTail

/-! Total header-to-result run of the guarded entry program. A missing unary
terminator returns immediately; only a successful header enters the sentinel
and dimension programs. All returns and successful endpoint data are retained. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.GuardedPreparation
open LocalBitMultitape RepairOrdinary RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def headerValid (word : List Bool) : Bool :=
  match HeaderMachine.parts word with
  | none => false
  | some (t,s,_) => dimensions t s

def HeaderOutcome (word : List Bool) (limit : ℕ)
    (final : Configuration 6 (Fintype.card (RecoveryCalls.Control sizes))) : Prop :=
  final.scanned 5=headerValid word ∧
    ∀ t s fields, HeaderMachine.parts word=some (t,s,fields) →
      2≤t ∧ 0<s → final=endpoint word limit t s

theorem parts_lengths {word fields : List Bool} {t s : ℕ}
    (hp : HeaderMachine.parts word=some (t,s,fields)) :
    t+s+2+fields.length=word.length := by
  unfold HeaderMachine.parts at hp
  cases hfirst : unary word with
  | none => simp [hfirst] at hp
  | some first =>
    rcases first with ⟨a,tail⟩
    cases hsecond : unary tail with
    | none => simp [hfirst,hsecond] at hp
    | some second =>
      rcases second with ⟨b,rest⟩
      simp only [hfirst,Option.bind_some,hsecond,Option.map_some,
        Option.some.injEq,Prod.mk.injEq] at hp
      rcases hp with ⟨rfl,rfl,rfl⟩
      have h1 := unary_bounded hfirst
      have h2 := unary_bounded hsecond
      omega

theorem header_tail (word : List Bool) (limit : ℕ) :
    ∃ n final, n≤6*word.length+19 ∧
      Timed machine n
        (controlConfig (RecoveryCalls.code sizes 2) (extend limit (Preparation.headerInput word))) final ∧
      machine.halted final.control=true ∧ HeaderOutcome word limit final := by
  obtain ⟨r,hr,hs,hresult,_,_⟩ := Preparation.header_total_layout word
  have he := TapeEmbedding.run_embed Preparation.headerProgram ![1,0]
    ![CompareMachine.word limit,[]] _ _ r hr
  let result := TapeEmbedding.receipt ![1,0] ![CompareMachine.word limit,[]] r
  have hsteps : result.steps≤2*word.length+5 := hs
  cases hp : HeaderMachine.parts word with
  | none =>
    have hc : r.final.control=7 := by simpa [Preparation.HeaderResult,hp] using hresult
    have hn : next 2 result.final.control result.final.scanned=none := by
      simp [next,result,TapeEmbedding.receipt,TapeEmbedding.config,hc]
    have ht := stop_prefix 2 (2*word.length+5) _ result he hn
    refine ⟨_,_,by omega,ht,?_,?_,?_⟩
    · simp [machine,RecoveryCalls.machine,RecoveryCalls.stopped]
    · simp [headerValid,hp,Configuration.scanned,RecoveryCalls.stopped,result,
        TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases,readTapeBit]
    · intro t s fields h
      simp [hp] at h
  | some value =>
    rcases value with ⟨t,s,fields⟩
    have hf : r.final=⟨6,(Preparation.tInput word t s).heads,(Preparation.tInput word t s).tapes⟩ := by
      simpa [Preparation.HeaderResult,hp] using hresult
    have hfinal : result.final=⟨6,(extend limit (Preparation.tInput word t s)).heads,
        (extend limit (Preparation.tInput word t s)).tapes⟩ := by
      change extend limit r.final=_
      rw [hf]; rfl
    have hn : next 2 result.final.control result.final.scanned=some 3 := by
      simp [next,hfinal]
    have ht := call_prefix 2 3 (2*word.length+5) _ result he hn
    rw [hfinal] at ht
    have hlen := parts_lengths hp
    obtain ⟨n,final,hn,hsentinel,hh,hbit,hgood⟩ := sentinel_tail word limit t s (by omega) (by omega)
    have hall := ht.trans hsentinel
    refine ⟨_,final,by omega,hall,hh,?_,?_⟩
    · simpa [headerValid,hp] using hbit
    · intro t' s' fields' hparts hdim
      rw [hp] at hparts
      have heq := Option.some.inj hparts
      cases heq
      exact hgood hdim

end NearCubicWires.RepairSource.VerifierDecoding.GuardedPreparation
