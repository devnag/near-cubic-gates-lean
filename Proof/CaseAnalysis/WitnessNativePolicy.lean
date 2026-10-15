import Proof.CaseAnalysis.WitnessNativeCache
import Proof.CaseAnalysis.WitnessSelectedPolicy

/-! The original guarded native continuation produces the cache and its
one-time actual V, clause count, q0 and coefficient-width policy together. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.NativePolicy
open LocalBitMultitape RecoveryRootRound RecoveryExecution
open RepairRepresentation RepairSource ProjectionNormalization SourceInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

abbrev base (a : PointwisePCPPAlgorithm):=
  PCPPNativeSource.tapes a (PCPPNativeClauseDescriptorConsumer.tapes 364)
def fields (a : PointwisePCPPAlgorithm) : Fin 2→Fin (base a):=
  ![NativeCache.cacheSlots a (PCPPSourceCache.cacheSlots a 0),
    NativeCache.cacheSlots a (PCPPSourceCache.cacheSlots a 13)]
def cacheSlots (a : PointwisePCPPAlgorithm) (D : ℕ) (j : Fin (PCPPSourceCache.tapes a)):=
  SourcePolicy.Call.old D (NativeCache.cacheSlots a j)
def policySlots (a : PointwisePCPPAlgorithm) (D : ℕ):=SourcePolicy.Call.slots D (fields a)
def first (a : PointwisePCPPAlgorithm) (D : ℕ):=
  TapeEmbedding.machine (SourcePolicy.Call.extra D) (NativeCache.machine a)
def second (a : PointwisePCPPAlgorithm) (D copies : ℕ) (delta : ℚ):=
  SourcePolicy.Call.machine D copies delta (fields a)
def machine (a : PointwisePCPPAlgorithm) (D copies : ℕ) (delta : ℚ):=
  Composition.machine (first a D) (second a D copies delta)
def input (a : PointwisePCPPAlgorithm) (D : ℕ) {R : ℕ}
    (oracle : BooleanCircuit R) (p : RawProjectionPCP) (Q : ℕ):=
  SourcePolicy.Call.input D (NativeCache.input a oracle p Q)
def budget (a : PointwisePCPPAlgorithm) (D copies : ℕ) (delta : ℚ)
    (p : RawProjectionPCP) (R Q : ℕ) (hR : p.width≤R) (hQ : p.queries≤Q)
    {n : ℕ} (x : BitInput n) (oracle : BooleanCircuit R):=
  let r:=NativeCache.request a p R Q hR hQ x oracle
  NativeCache.budget a p R Q hR hQ x oracle+1+
    SourcePolicy.budget D copies r.arity (a.output r).systematicBits (a.output r).auxiliaryBits
      (a.output r).clauseBits delta

theorem policy_run (a : PointwisePCPPAlgorithm) (D copies : ℕ) (delta : ℚ)
    (p : RawProjectionPCP) (R Q : ℕ) (hR : p.width≤R) (hQ : p.queries≤Q)
    {n : ℕ} (x : BitInput n) (oracle : BooleanCircuit R) (hD : 1≤D) :
    let r:=NativeCache.request a p R Q hR hQ x oracle
    ∃ actual,run (machine a D copies delta) (budget a D copies delta p R Q hR hQ x oracle)
      (input a D oracle p Q)=some actual ∧
      actual.steps≤budget a D copies delta p R Q hR hQ x oracle ∧
      (∀ j : Fin 19,actual.final.tapes (cacheSlots a D (PCPPSourceCache.cacheSlots a j))=
        PCPPQueryIndexPadding.clauseData (pcppOutput r (a.output r)) r.arity 0
          (PCPPQueryCachedBounds.capacity a (r.circuit.size+r.arity)) [] j) ∧
      (∀ j : Fin 19,actual.final.heads (cacheSlots a D (PCPPSourceCache.cacheSlots a j))=
        PCPPQueryClauseReuse.heads j) ∧
      SourcePolicy.Call.Fields D copies delta (fields a) r (a.output r) actual.final:=by
  intro r
  obtain ⟨s,hs,ss,st,sh,_,_⟩:=NativeCache.cache_run a p R Q hR hQ x oracle
  have sh0:s.final.heads (fields a 0)=0:=sh 0
  have sh1:s.final.heads (fields a 1)=1:=sh 13
  have ht0:s.final.tapes (fields a 0)=pcppOutput r (a.output r):=st 0
  have ht1:s.final.tapes (fields a 1)=UnaryTemplate.tape r.arity:=st 13
  have distinct:fields a 0≠fields a 1:=by
    intro he
    rw [he,sh1] at sh0
    omega
  have hf:Function.Injective (fields a):=by
    intro i j he
    fin_cases i <;> fin_cases j
    · rfl
    · exact False.elim (distinct he)
    · exact False.elim (distinct he.symm)
    · rfl
  let lifted:=TapeEmbedding.receipt (fun _ : Fin (SourcePolicy.Call.extra D)=>0) (fun _=>[]) s
  have hfirst:=TapeEmbedding.run_embed (NativeCache.machine a)
    (fun _ : Fin (SourcePolicy.Call.extra D)=>0) (fun _=>[]) _ _ s hs
  rw [StreamPrepare.embed_initial] at hfirst
  obtain ⟨last,hl,ls,keep,lf⟩:=SourcePolicy.Call.call_run D copies delta (fields a) hf
    s.final.tapes s.final.heads r (a.output r) hD sh0 sh1 ht0 ht1
  have he:=MatrixPacketBranch.restart_fields (second a D copies delta) lifted.final
    (SourcePolicy.Call.heads D s.final.heads) (SourcePolicy.Call.input D s.final.tapes) rfl rfl
  dsimp only [second,RecoveryCalls.restarted] at he
  rw [he] at hl
  have hall:=Composition.run_join (first a D) (second a D copies delta) _ _ _ lifted last hfirst hl
  refine ⟨Composition.joinedReceipt lifted last,hall,?_,?_,?_,
    SelectedPolicy.fields_joined D copies delta _ r _ lifted last lf⟩
  · exact Nat.add_le_add (Nat.add_le_add_right ss 1) ls
  · intro j
    rw [PCPTripleGlobal.joined_tapes]
    exact (keep _).2.trans (st j)
  · intro j
    rw [PCPTripleGlobal.joined_heads]
    exact (keep _).1.trans (sh j)

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.NativePolicy
