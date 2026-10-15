import Proof.Hierarchy.CompetitorSameBucketCandidatePair

/-! Whole reusable candidate: paid scalar erase, actual streamed right-record
load, then the actual conditional emitter. No decoded record is supplied for
free, and the next call receives the resulting physical scratch invariant. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketCandidate
open LocalBitMultitape RecoveryExecution RecoveryRootRound MatrixBatchBucketEndpoints
open MatrixScoreBatch (Request)
open CompetitorSameBucketPackets (word width)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure State (r : Request) (cap : ℕ) (coefficient : ℤ) (left : Option KeyLoop.Record)
    (source out : List Bool) (ambient : Fin 41 → List Bool) : Prop where
  store : Store cap ambient
  fields : Fields cap r.M r.U r.p coefficient (word r left) out ambient
  width : ambient 38=UnaryTemplate.tape (CompetitorSameBucketPackets.width r)
  source : ambient 39=source

noncomputable def body := Composition.machine prepare native
def budget (r : Request) (cap : ℕ) := 2*cap+4*width r+16+CompetitorSameBucketPairEmit.budget r.S r.M r.p

theorem body_run (r : Request) (cap : ℕ) (coefficient : ℤ) (left right : Option KeyLoop.Record)
    (pre suffix out : List Bool) (ambient : Fin 41 → List Bool)
    (hc : 30*(H r+1)≤cap) (hp : 2*(r.p+1)+1≤cap) (hl : Fits r left) (hr : Fits r right)
    (hstate : State r cap coefficient left (pre++word r right++suffix) out ambient) :
    ∃ b,runFrom body (budget r cap) (cfg body.start pre.length out.length ambient)=some b ∧
      b.steps≤budget r cap ∧
      b.final.heads=heads (pre.length+width r) (pairOutput r coefficient left right out).length ∧
      State r cap coefficient left (pre++word r right++suffix) (pairOutput r coefficient left right out) b.final.tapes := by
  have hw : 2*(word r right).length+4≤cap := by rw [CompetitorSameBucketPackets.word_length]; unfold width at *; omega
  obtain ⟨prep,hprep,ph,pt,ps⟩ := prepare_run cap out.length pre (word r right) suffix ambient hstate.store
    (by rw [CompetitorSameBucketPackets.word_length]; exact hstate.width) hstate.source hw
  obtain ⟨small,hsmall,sh,ss,sf,sb⟩ := pair_local_run r cap coefficient left right out hc hp hl hr
  obtain ⟨actual,ha,ah,atapes,ab⟩ := native_run (CompetitorSameBucketPairEmit.budget r.S r.M r.p)
    (pre.length+(word r right).length) out (pairOutput r coefficient left right out) (loaded cap (word r right) ambient)
    (part cap r.M r.U r.p coefficient (word r left) (word r right) out).tapes small.final.tapes
    (loaded_input cap r.M r.U r.p coefficient (word r left) (word r right) out ambient hstate.fields)
    ⟨small,hsmall,sh,rfl,sb⟩
  have hi : Composition.restart prep.final native.start=
      cfg native.start (pre.length+(word r right).length) out.length (loaded cap (word r right) ambient) :=
    configuration_ext rfl ph pt
  rw [←hi] at ha
  have hall := Composition.run_join prepare native _ _ _ prep actual hprep ha
  have he : (2*cap+4*(word r right).length+15)+1+CompetitorSameBucketPairEmit.budget r.S r.M r.p=budget r cap := by
    rw [CompetitorSameBucketPackets.word_length]
    unfold budget
    omega
  rw [he] at hall
  refine ⟨Composition.joinedReceipt prep actual,hall,?_,?_,?_⟩
  · change prep.steps+1+actual.steps≤budget r cap
    rw [←he]
    omega
  · change actual.final.heads=_
    simpa only [CompetitorSameBucketPackets.word_length] using ah
  · change State r cap coefficient left _ _ actual.final.tapes
    rw [atapes]
    constructor
    · exact (hstate.store.loaded (word r right) (by omega)).replace small.final.tapes ss
    · exact Fields.replace small.final.tapes sf
    · change replace (loaded cap (word r right) ambient) small.final.tapes (Fin.natAdd 36 (2 : Fin 5))=_
      rw [replace_high]
      change Function.update (clean cap ambient) 13 (ZeroPadding.pad cap (word r right)) 38=_
      rw [Function.update_of_ne (by decide : (38 : Fin 41)≠13)]
      exact (clean_other cap ambient 38 (by decide)).trans hstate.width
    · change replace (loaded cap (word r right) ambient) small.final.tapes (Fin.natAdd 36 (3 : Fin 5))=_
      rw [replace_high]
      change Function.update (clean cap ambient) 13 (ZeroPadding.pad cap (word r right)) 39=_
      rw [Function.update_of_ne (by decide : (39 : Fin 41)≠13)]
      exact (clean_other cap ambient 39 (by decide)).trans hstate.source

end NearCubicWires.RepairOrdinary.CompetitorSameBucketCandidate
