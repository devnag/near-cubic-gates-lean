import Proof.MachineModel.ClosureBinaryPreparedWriterLayout

/-! One fixed program constructs the actual raw family into the initially
empty native port, pays to rewind it, computes native metadata, then writes
the literal binary request header. All private preparation state survives
outside the native bank and every tape/head is specified at the endpoint.
The encoded hardwired cache and runtime dimensions remain real inputs. -/
namespace NearCubicWires.P1Closure.BinaryPreparedWriter
open LocalBitMultitape RepairOrdinary ExtIncidence ExtDecompositionBatch RecoveryRootRound
open RepairRepresentation SupplierPipeline SupplierEstimator ThresholdCompiler CanonicalFourfoldRowProgram
open RepairSource CloseoutFinal C10SupplierRowInput
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem prepare_run {n : ℕ} (gs : List (ExactThresholdGate n)) [P1Radix gs] (Q w : ℕ)
    (N Y S F : ℕ) (P : List (List ℕ)) (tail out : List Bool)
    (hS : (stream P).length ≤ S) (hF : RawRelabelFamily.budget N Y S ≤ F) :
    Step prepare (2*RawRelabelFamily.budget N Y S+2) (heads out)
      (state gs Q w N Y S 0 F [] (stream P++tail) out)
      (heads out) (state gs Q w N Y S Y F
        ((List.range Y).flatMap (RawRelabelFamily.emit N P)) (stream P++tail) out) := by
  have familyRun:=RawRelabelFamily.run N Y S P tail [] hS
  simp only [List.nil_append] at familyRun
  have reset:=familyRun.mask (fun i=>decide (i=4))
    (by intro i hi;have e:i=4:=of_decide_eq_true hi;subst i;rfl) hF
  have h:=reset.dock slots slots_injective (heads out)
    (state gs Q w N Y S 0 F [] (stream P++tail) out)
    (head_slots out) (input_slots gs Q w N Y S F P tail out)
  exact h.congr (exit_heads out _) (exit_tapes gs Q w N Y S F P tail out _)

attribute [local irreducible] pool BinaryPool.pool bank childList CompactBounds.radix
  CloseoutRowsUniversal.pool ExtDecompositionBatch.GS

variable {q : ℕ} (a : DecompositionAlgorithm) (live : Finset (Fin q))
  (occ : List (SupportedNormalizedGate q)) (s : ℕ) (harity : (s+1)/2+s/2=liveᶜ.card)
  (P : StructuralGF2Polynomial) (w degree S : ℕ) (tail out : List Bool)

noncomputable def entry : Fin 448→List Bool:=
  letI:=BinaryRequest.radix a live occ s harity degree
  let N:=(childList a live occ).length
  let Y:=2^live.card
  state (BinaryPool.pool a live occ s harity) (live.card+1) w N Y S 0
    (RawRelabelFamily.budget N Y S) [] (stream (CloseoutRowsUniversal.lower a live occ P)++tail) out

noncomputable def finalHeads : Fin 448→ℕ:=
  letI:=BinaryRequest.radix a live occ s harity degree
  Fin.addCases (m:=440) (n:=8) (motive:=fun _=>ℕ)
    (CompactColdFamily.finalHeads (BinaryPool.pool a live occ s harity) (live.card+1) w
      (BinaryWriter.packets a live occ s harity P) out [] []) (fun _=>0)

noncomputable def finalTapes : Fin 448→List Bool:=
  letI:=BinaryRequest.radix a live occ s harity degree
  let N:=(childList a live occ).length
  let Y:=2^live.card
  frame (CompactColdFamily.finalTapes (BinaryPool.pool a live occ s harity) (live.card+1) w
    (BinaryWriter.packets a live occ s harity P) out [] [])
    (privateData N Y S Y (RawRelabelFamily.budget N Y S) (stream (CloseoutRowsUniversal.lower a live occ P)++tail))

noncomputable def budget : ℕ:=
  letI:=BinaryRequest.radix a live occ s harity degree
  2*RawRelabelFamily.budget (childList a live occ).length (2^live.card) S+3+
    CompactColdFamily.budget (BinaryPool.pool a live occ s harity) (live.card+1) w
      (BinaryWriter.packets a live occ s harity P)

theorem run (hs : 67 ≤ s) (hmon : (CloseoutRowsUniversal.lower a live occ P).length < 2^w)
    (hpos : 1 ≤ w) (hload : 200*(live.card+w*(live.card+2)) ≤ s)
    (hdegree : CloseoutRawRows.RawMonomialDegreeAtMost degree P)
    (hS : (stream (CloseoutRowsUniversal.lower a live occ P)).length ≤ S) :
    Step machine (budget a live occ s harity P w degree S) (heads out)
      (entry a live occ s harity P w degree S tail out)
      (finalHeads a live occ s harity P w degree out)
      (finalTapes a live occ s harity P w degree S tail out) ∧
    finalTapes a live occ s harity P w degree S tail out 180=
      out++CloseoutRowsEstimator.Header.stream
        (BinaryRequest.input a live occ s harity P w degree hs hmon hpos hload hdegree) := by
  letI:=BinaryRequest.radix a live occ s harity degree
  let N:=(childList a live occ).length
  let Y:=2^live.card
  let F:=RawRelabelFamily.budget N Y S
  let lower:=CloseoutRowsUniversal.lower a live occ P
  have first:=prepare_run (BinaryPool.pool a live occ s harity) (live.card+1) w
    N Y S F lower tail out hS (Nat.le_refl _)
  have length:(ps a live occ s harity P).length=Y:=by
    simp only [Y,ps,List.length_ofFn,liveList_length]
  have raw:(List.range Y).flatMap (RawRelabelFamily.emit N lower)=
      (ps a live occ s harity P).flatMap P1CompactNativeFamily.rawWord:=
    RawRelabelFamily.actual_word a live occ s harity P
  rw [raw] at first
  obtain ⟨written,word⟩:=BinaryWriter.run a live occ s harity P w degree hs hmon hpos hload hdegree out [] []
  simp only [List.nil_append,List.append_nil,length] at written
  have last:=written.embed (fun _ : Fin 8=>0)
    (privateData N Y S Y F (stream lower++tail))
  have joined:=first.seq last
  constructor
  · simpa only [machine,writer,budget,N,Y,F,lower,entry,finalHeads,finalTapes,state,frame,
      show 2*RawRelabelFamily.budget N Y S+2+1=2*RawRelabelFamily.budget N Y S+3 by omega] using joined
  · exact word

end
end NearCubicWires.P1Closure.BinaryPreparedWriter
