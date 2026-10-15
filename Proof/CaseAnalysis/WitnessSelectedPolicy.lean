import Proof.CaseAnalysis.WitnessSourcePolicyCall

/-! Original input and the same raw oracle reach the faithful PCPP source
and its one-time family policy. The entire source cache survives unchanged;
no source word, metadata counter or coefficient template is supplied free. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.SelectedPolicy
open LocalBitMultitape RecoveryRootRound RecoveryExecution RadixSemantics
open RepairRepresentation RepairSource ProjectionNormalization SourceInterfaces ExecutableInterfaces
open VerifierDecoding CanonicalWitnessCodec
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem fields_joined (D copies : ℕ) (delta : ℚ) {t n0 s z : ℕ} (fields : Fin 2→Fin t)
    (r : PCPPRequest n0) (p : PointwisePCPP r.circuit)
    (first : ExecutionReceipt (t+SourcePolicy.Call.extra D) s)
    (last : ExecutionReceipt (t+SourcePolicy.Call.extra D) z)
    (h : SourcePolicy.Call.Fields D copies delta fields r p last.final) :
    SourcePolicy.Call.Fields D copies delta fields r p (Composition.joinedReceipt first last).final:=
  ⟨h.count,h.clause,h.q0,h.cap,h.cursor⟩

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
abbrev base (a : PointwisePCPPAlgorithm) (k G : ℕ):=
  PCPPNativeSource.tapes a (PCPPNativeClauseDescriptorConsumer.tapes (SelectedNodes.tapes source k G))
def fields (a : PointwisePCPPAlgorithm) (k G : ℕ) : Fin 2→Fin (base source a k G):=
  ![SelectedSource.cacheSlots source a k G (PCPPSourceCache.cacheSlots a 0),
    SelectedSource.cacheSlots source a k G (PCPPSourceCache.cacheSlots a 13)]
def cacheSlots (a : PointwisePCPPAlgorithm) (k G D : ℕ) (j : Fin (PCPPSourceCache.tapes a)):=
  SourcePolicy.Call.old D (SelectedSource.cacheSlots source a k G j)
def policySlots (a : PointwisePCPPAlgorithm) (k G D : ℕ):=
  SourcePolicy.Call.slots D (fields source a k G)
def first (a : PointwisePCPPAlgorithm) (k CH Cpad G D : ℕ) (code : List Bool):=
  TapeEmbedding.machine (SourcePolicy.Call.extra D) (SelectedSource.machine source a k CH Cpad G code)
def second (a : PointwisePCPPAlgorithm) (k G D copies : ℕ) (delta : ℚ):=
  SourcePolicy.Call.machine D copies delta (fields source a k G)
def machine (a : PointwisePCPPAlgorithm) (k CH Cpad G D copies : ℕ) (delta : ℚ) (code : List Bool):=
  Composition.machine (first source a k CH Cpad G D code) (second source a k G D copies delta)
def input (a : PointwisePCPPAlgorithm) (k G D : ℕ) (x raw : List Bool):=
  SourcePolicy.Call.input D (SelectedSource.input source a k G x raw)
def budget (a : PointwisePCPPAlgorithm) (k CH Cpad G D copies : ℕ) (delta : ℚ) (code : List Bool) {n : ℕ}
    (x : BitInput n) (raw : List Bool) (hpad : k+3 ≤ Cpad)
    (oracle : BooleanCircuit (SelectedOracle.width source k CH Cpad code (List.ofFn x))):=
  let r:=SelectedSource.request source a k CH Cpad code x hpad oracle
  SelectedSource.budget source a k CH Cpad G code x raw hpad oracle+1+
    SourcePolicy.budget D copies r.arity (a.output r).systematicBits (a.output r).auxiliaryBits
      (a.output r).clauseBits delta

theorem policy_run (a : PointwisePCPPAlgorithm) (k CH Cpad G D copies : ℕ) (delta : ℚ) (code : List Bool)
    {n : ℕ} (x : BitInput n) (raw : List Bool) (hpad : k+3 ≤ Cpad) (hD : 1 ≤ D) (hN : 2 ≤ n)
    (hcap : 16*raw.length ≤ n)
    (hwidth : (SelectedOracle.width source k CH Cpad code (List.ofFn x)).bits.length ≤ n+1)
    (oracle : BooleanCircuit (SelectedOracle.width source k CH Cpad code (List.ofFn x)))
    (hd : decodeBooleanCircuit (SelectedOracle.width source k CH Cpad code (List.ofFn x)) (value raw)=some oracle) :
    let r:=SelectedSource.request source a k CH Cpad code x hpad oracle
    ∃ actual,run (machine source a k CH Cpad G D copies delta code)
      (budget source a k CH Cpad G D copies delta code x raw hpad oracle)
      (input source a k G D (List.ofFn x) raw)=some actual ∧
      actual.steps ≤ budget source a k CH Cpad G D copies delta code x raw hpad oracle ∧
      (∀ j : Fin 19,actual.final.tapes (cacheSlots source a k G D (PCPPSourceCache.cacheSlots a j))=
        PCPPQueryIndexPadding.clauseData (pcppOutput r (a.output r)) r.arity 0
          (PCPPQueryCachedBounds.capacity a (r.circuit.size+r.arity)) [] j) ∧
      (∀ j : Fin 19,actual.final.heads (cacheSlots source a k G D (PCPPSourceCache.cacheSlots a j))=
        PCPPQueryClauseReuse.heads j) ∧
      actual.final.tapes (cacheSlots source a k G D (PCPPSourceCache.sizeSlot a))=
        List.replicate r.circuit.size true ∧
      actual.final.heads (cacheSlots source a k G D (PCPPSourceCache.sizeSlot a))=0 ∧
      SourcePolicy.Call.Fields D copies delta (fields source a k G) r (a.output r) actual.final:=by
  intro r
  obtain ⟨s,hs,ss,st,sh,sz,szh⟩:=SelectedSource.source_run source a k CH Cpad G code x raw hpad hN hcap hwidth oracle hd
  have sh0:s.final.heads (fields source a k G 0)=0:=sh 0
  have sh1:s.final.heads (fields source a k G 1)=1:=sh 13
  have ht0:s.final.tapes (fields source a k G 0)=pcppOutput r (a.output r):=st 0
  have ht1:s.final.tapes (fields source a k G 1)=UnaryTemplate.tape r.arity:=st 13
  have distinct:fields source a k G 0≠fields source a k G 1:=by
    intro he
    rw [he,sh1] at sh0
    omega
  have hf:Function.Injective (fields source a k G):=by
    intro i j he
    fin_cases i <;> fin_cases j
    · rfl
    · exact False.elim (distinct he)
    · exact False.elim (distinct he.symm)
    · rfl
  let lifted:=TapeEmbedding.receipt (fun _ : Fin (SourcePolicy.Call.extra D)=>0) (fun _=>[]) s
  have hfirst:=TapeEmbedding.run_embed (SelectedSource.machine source a k CH Cpad G code)
    (fun _ : Fin (SourcePolicy.Call.extra D)=>0) (fun _=>[]) _ _ s hs
  obtain ⟨last,hl,ls,keep,lf⟩:=SourcePolicy.Call.call_run D copies delta (fields source a k G) hf
    s.final.tapes s.final.heads r (a.output r) hD sh0 sh1 ht0 ht1
  have he:=MatrixPacketBranch.restart_fields (second source a k G D copies delta) lifted.final
    (SourcePolicy.Call.heads D s.final.heads) (SourcePolicy.Call.input D s.final.tapes) rfl rfl
  dsimp only [second,RecoveryCalls.restarted] at he
  rw [he] at hl
  have hall:=Composition.run_join (first source a k CH Cpad G D code) (second source a k G D copies delta)
    _ _ _ lifted last hfirst hl
  rw [MatrixWilliamsProduct.initial_join (SelectedSource.machine source a k CH Cpad G code)
    (second source a k G D copies delta) (SelectedSource.input source a k G (List.ofFn x) raw)] at hall
  refine ⟨Composition.joinedReceipt lifted last,hall,?_,?_,?_,?_,?_,
    fields_joined D copies delta _ r _ lifted last lf⟩
  · change s.steps+1+last.steps ≤ budget source a k CH Cpad G D copies delta code x raw hpad oracle
    exact Nat.add_le_add (Nat.add_le_add_right ss 1) ls
  · intro j
    rw [PCPTripleGlobal.joined_tapes]
    exact (keep _).2.trans (st j)
  · intro j
    rw [PCPTripleGlobal.joined_heads]
    exact (keep _).1.trans (sh j)
  · rw [PCPTripleGlobal.joined_tapes]
    exact (keep _).2.trans sz
  · rw [PCPTripleGlobal.joined_heads]
    exact (keep _).1.trans szh

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.SelectedPolicy
