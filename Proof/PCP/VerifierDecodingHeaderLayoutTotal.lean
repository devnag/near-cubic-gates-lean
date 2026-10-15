import Proof.PCP.VerifierDecodingHeaderTotal
import Proof.PCP.VerifierDecodingDimensionGuard

/-! Total execution of the existing header program on its paid length-counter
layout. Rejection preserves the independent code-length counter. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.Preparation
open LocalBitMultitape RepairOrdinary RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def HeaderResult (word : List Bool) (final : Configuration 4 8) : Prop :=
  match HeaderMachine.parts word with
  | none => final.control=7
  | some (t,s,_) => final=⟨6,(tInput word t s).heads,(tInput word t s).tapes⟩

theorem header_total_layout (word : List Bool) :
    ∃ r, runFrom headerProgram (2*word.length+5) (headerInput word)=some r ∧
      r.steps≤2*word.length+5 ∧ HeaderResult word r.final ∧
      r.final.heads 3=1 ∧ r.final.tapes 3=cap word := by
  obtain ⟨r,hr,hs,hresult⟩ := HeaderMachine.total_run word
  obtain ⟨p,hrp,hfp,hsp,_⟩ := ZeroPadding.run_config HeaderMachine.machine
    ![0,word.length+2,word.length+2] _ _ r hr
  let eh : Fin 1 → ℕ := fun _ => 1
  let et : Fin 1 → List Bool := fun _ => cap word
  have he := TapeEmbedding.run_embed HeaderMachine.machine eh et _ _ p hrp
  let result := TapeEmbedding.receipt eh et p
  have hi : TapeEmbedding.config eh et (ZeroPadding.config ![0,word.length+2,word.length+2]
      (initialConfiguration HeaderMachine.machine ![frame word,[],[]])) = headerInput word := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> simp [TapeEmbedding.config,ZeroPadding.config,
        initialConfiguration,headerInput,eh,et,zeros,Fin.addCases]
  rw [hi] at he
  refine ⟨result,he,by change p.steps≤_; omega,?_,rfl,rfl⟩
  cases hp : HeaderMachine.parts word with
  | none =>
    have hc : r.final.control=7 := by simpa [HeaderMachine.Result,hp] using hresult
    change HeaderResult word (TapeEmbedding.config eh et p.final)
    simp [HeaderResult,hp,TapeEmbedding.config,hfp,ZeroPadding.config,hc]
  | some value =>
    rcases value with ⟨t,s,fields⟩
    have hf : r.final=HeaderMachine.finished t s fields := by
      simpa [HeaderMachine.Result,hp] using hresult
    have hb : word=HeaderMachine.word t s fields := by
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
          rw [UnaryMachine.unary_decomposition hfirst,UnaryMachine.unary_decomposition hsecond]
          rfl
    simp only [HeaderResult,hp]
    apply configuration_ext
    · change p.final.control=6
      simp [hfp,hf,ZeroPadding.config,HeaderMachine.finished]
    · funext i; fin_cases i <;> simp [result,TapeEmbedding.receipt,TapeEmbedding.config,
        hfp,hf,ZeroPadding.config,HeaderMachine.finished,tInput,eh,Fin.addCases]
    · funext i; fin_cases i <;> simp [result,TapeEmbedding.receipt,TapeEmbedding.config,
        hfp,hf,ZeroPadding.config,HeaderMachine.finished,tInput,et,Fin.addCases,
        SentinelMachine.raw,hb]

end NearCubicWires.RepairSource.VerifierDecoding.Preparation
