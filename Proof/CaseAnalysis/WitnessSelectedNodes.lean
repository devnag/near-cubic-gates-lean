import Proof.CaseAnalysis.WitnessSelectedCap
import Proof.CaseAnalysis.WitnessNativeNodeCall
import Proof.PCP.PCPPNativeHierarchyNodesCircuit

/-! Original input and the same decoded oracle emit the actual compact
substituted DAG after the paid exact cap test. No native descriptor or metadata
is supplied, and neither source selection nor counter production is repeated. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.SelectedNodes
open LocalBitMultitape RecoveryRootRound RecoveryExecution RadixSemantics
open RepairSource ProjectionNormalization SourceInterfaces ExecutableInterfaces VerifierDecoding CanonicalWitnessCodec
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
abbrev base (k G : ℕ):=SelectedCap.tapes source k G
abbrev tapes (k G : ℕ):=base source k G+363
def counter (k G : ℕ):=SelectedCap.slots source k G
theorem counter_injective (k G : ℕ) : Function.Injective (counter source k G):=by
  intro a b h
  have hv:=congrArg Fin.val h
  exact SelectedCounters.slots_injective source k (Fin.ext hv)
def slots (k G : ℕ):=NativeNodeCall.slots (counter source k G)
def widthSlot (k G : ℕ):=NativeNodeCall.old (counter source k G 72)
def first (k CH Cpad G : ℕ) (code : List Bool):=
  TapeEmbedding.machine 363 (SelectedCap.machine source k CH Cpad G code)
def second (k G : ℕ):=NativeNodeCall.machine (counter source k G)
def machine (k CH Cpad G : ℕ) (code : List Bool):=
  Composition.machine (first source k CH Cpad G code) (second source k G)
def input (k G : ℕ) (x raw : List Bool):=NativeNodeCall.input (SelectedCap.input source k G x raw)
def circuit (k CH Cpad : ℕ) (code : List Bool) {n : ℕ} (x : BitInput n) (hpad : k+3  ≤  Cpad)
    (oracle : BooleanCircuit (SelectedOracle.width source k CH Cpad code (List.ofFn x))):=
  PCPPNativeHierarchyNodes.circuit source k CH Cpad code x hpad oracle
def budget (k CH Cpad G : ℕ) (code : List Bool) {n : ℕ} (x : BitInput n) (raw : List Bool)
    (oracle : BooleanCircuit (SelectedOracle.width source k CH Cpad code (List.ofFn x))):=
  SelectedCap.budget source k CH Cpad G code (List.ofFn x) raw oracle+1+
    PCPPNativeClauseOracle.budget oracle (SelectedStreams.queries source k CH Cpad code (List.ofFn x))
      (Codec.clauses (SelectedStreams.pcp source k CH Cpad code (List.ofFn x))).length
      (PCPPNativeMetadataMass.queryBytes (SelectedStreams.pcp source k CH Cpad code (List.ofFn x))
        (SelectedOracle.width source k CH Cpad code (List.ofFn x))
        (SelectedStreams.queries source k CH Cpad code (List.ofFn x))).length
      (DedupBytes.fields (SelectedStreams.pcp source k CH Cpad code (List.ofFn x))).length

theorem output_slot (k G : ℕ) : slots source k G 102=(102 : Fin 363).natAdd (base source k G):=by
  change NativeNodeCall.bank (counter source k G) ((102 : Fin 363).natAdd 75)=_
  simp only [NativeNodeCall.bank,Fin.addCases_right]
theorem forward (k CH Cpad G : ℕ) (code : List Bool) :
    CursorRestore.NoLeft (machine source k CH Cpad G code) (slots source k G 102):=by
  apply CursorRestore.composition_forward
  · rw [output_slot]
    exact EquationRowRaw.embedded_extra_forward (SelectedCap.machine source k CH Cpad G code) (102 : Fin 363)
  · exact NativeNodeCall.forward (counter source k G) (counter_injective source k G)
theorem scalar_distinct (k G : ℕ) : widthSlot source k G≠slots source k G 16 ∧
    widthSlot source k G≠slots source k G 14 ∧ slots source k G 16≠slots source k G 14:=by
  have hi:=NativeNodeCall.slots_injective (counter source k G) (counter_injective source k G)
  exact ⟨(NativeNodeCall.raw_arity_outside (counter source k G) (counter_injective source k G) 16).symm,
    (NativeNodeCall.raw_arity_outside (counter source k G) (counter_injective source k G) 14).symm,
    fun h=>(by decide : (16 : Fin 363)≠14) (hi h)⟩

theorem nodes_run (k CH Cpad G : ℕ) (code : List Bool) {n : ℕ} (x : BitInput n) (raw : List Bool)
    (hpad : k+3  ≤  Cpad) (hN : 2  ≤  n) (hcap : 16*raw.length  ≤  n)
    (hwidth : (SelectedOracle.width source k CH Cpad code (List.ofFn x)).bits.length  ≤  n+1)
    (oracle : BooleanCircuit (SelectedOracle.width source k CH Cpad code (List.ofFn x)))
    (hd : decodeBooleanCircuit (SelectedOracle.width source k CH Cpad code (List.ofFn x)) (value raw)=some oracle) :
    let c:=circuit source k CH Cpad code x hpad oracle
    ∃ actual,run (machine source k CH Cpad G code) (budget source k CH Cpad G code x raw oracle)
      (input source k G (List.ofFn x) raw)=some actual ∧
      actual.steps  ≤  budget source k CH Cpad G code x raw oracle ∧
      actual.final.tapes (slots source k G 102)=c.nodes.flatMap PCPPRequestNodeSchema.native ∧
      actual.final.heads (slots source k G 102)=(c.nodes.flatMap PCPPRequestNodeSchema.native).length ∧
      actual.final.heads (slots source k G 14)=0 ∧
      actual.final.tapes (slots source k G 14)=List.replicate c.output.val true ∧
      actual.final.heads (slots source k G 16)=0 ∧
      actual.final.tapes (slots source k G 16)=List.replicate c.size true ∧
      actual.final.heads (widthSlot source k G)=0 ∧
      actual.final.tapes (widthSlot source k G)=
        List.replicate (SelectedOracle.width source k CH Cpad code (List.ofFn x)) true:=by
  intro c
  obtain ⟨a,ha,as,af,ah72,at72,_,_⟩:=SelectedCap.cap_run source k CH Cpad G code (List.ofFn x) raw hpad
    (by simpa only [List.length_ofFn] using hN) (by simpa only [List.length_ofFn] using hcap)
    (by simpa only [List.length_ofFn] using hwidth) oracle hd
  let lifted:=TapeEmbedding.receipt (fun _ : Fin 363=>0) (fun _=>[]) a
  have hfirst:=TapeEmbedding.run_embed (SelectedCap.machine source k CH Cpad G code)
    (fun _ : Fin 363=>0) (fun _=>[]) _ _ a ha
  let p:=SelectedStreams.pcp source k CH Cpad code (List.ofFn x)
  let R:=SelectedOracle.width source k CH Cpad code (List.ofFn x)
  let Q:=SelectedStreams.queries source k CH Cpad code (List.ofFn x)
  have hR:p.width  ≤  R:=PCPPNativeHierarchyNodes.width_fits source k CH Cpad code x hpad
  have hQ:p.queries  ≤  Q:=PCPPNativeHierarchyNodes.queries_fit source k CH Cpad code x hpad
  obtain ⟨b,hb,bt,bh,b14h,b14t,b16h,b16t,bs⟩:=PCPPNativeClauseOracle.original_run p R Q hR hQ x oracle []
    (PCPPNativeCompactNodes.clauses p R Q hR hQ x)
  simp only [List.append_nil,PCPPNativeCompactNodes.count,PCPPNativeCompactNodes.fields] at hb b14t b16t bs
  rw [PCPPNativeCounterNodes.node_input] at hb
  have hdata:=NativeNodeCall.input_fields (counter source k G) a.final.tapes a.final.heads oracle p Q af
  obtain ⟨last,hl,_,ls,lh,lt,away⟩:=RecoveryFocus.dock (slots source k G)
    (NativeNodeCall.slots_injective (counter source k G) (counter_injective source k G))
    PCPPNativeClauseOracle.machine _ lifted.final.heads lifted.final.tapes
    (initialConfiguration PCPPNativeClauseOracle.machine
      (PCPPNativeCounterNodes.nodeInput (PCPPNative.descriptor oracle) (PCPPNativeMetadataMass.queryBytes p R Q)
        (DedupBytes.fields p) R Q oracle.size (Codec.clauses p).length
        (PCPPNativeMetadataMass.queryBytes p R Q).length (DedupBytes.fields p).length))
    (fun i=>(hdata i).1) (fun i=>(hdata i).2) b hb
  have hall:=Composition.run_join (first source k CH Cpad G code) (second source k G) _ _ _ lifted last hfirst hl
  rw [MatrixWilliamsProduct.initial_join (SelectedCap.machine source k CH Cpad G code)
    (second source k G) (SelectedCap.input source k G (List.ofFn x) raw)] at hall
  have cn:c.nodes=PCPPNativeCompactNodes.nodes p R Q hR hQ x oracle:=PCPPNativeCompactNodes.circuit_nodes _ _ _ _ _ _ _
  have csize:c.size=PCPPNativeCount.nativeSize Q oracle.size (Codec.clauses p).length:=
    PCPPNativeCompactNodes.circuit_size _ _ _ _ _ _ _
  have cout:c.output.val=PCPPNativeCount.outputIndex Q oracle.size (Codec.clauses p).length:=
    PCPPNativeCompactNodes.circuit_output _ _ _ _ _ _ _
  have keep:=away (widthSlot source k G)
    (NativeNodeCall.raw_arity_outside (counter source k G) (counter_injective source k G))
  refine ⟨Composition.joinedReceipt lifted last,hall,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · change a.steps+1+last.steps  ≤  budget source k CH Cpad G code x raw oracle
    rw [ls]
    exact Nat.add_le_add (Nat.add_le_add_right as 1) bs
  · rw [PCPTripleGlobal.joined_tapes,cn]
    exact (lt 102).trans bt
  · rw [PCPTripleGlobal.joined_heads,cn]
    exact (lh 102).trans bh
  · rw [PCPTripleGlobal.joined_heads]
    exact (lh 14).trans b14h
  · rw [PCPTripleGlobal.joined_tapes,cout]
    exact (lt 14).trans b14t
  · rw [PCPTripleGlobal.joined_heads]
    exact (lh 16).trans b16h
  · rw [PCPTripleGlobal.joined_tapes,csize]
    exact (lt 16).trans b16t
  · rw [PCPTripleGlobal.joined_heads]
    exact keep.1.trans ((TapeEmbedding.receipt_heads_old (fun _ : Fin 363=>0) (fun _=>[]) a _).trans ah72)
  · rw [PCPTripleGlobal.joined_tapes]
    exact keep.2.trans ((TapeEmbedding.receipt_tapes_old (fun _ : Fin 363=>0) (fun _=>[]) a _).trans at72)

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.SelectedNodes
