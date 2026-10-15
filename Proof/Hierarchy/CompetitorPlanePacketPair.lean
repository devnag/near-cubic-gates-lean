import Proof.Hierarchy.CompetitorPlanePacketBanks

/-! A complete positive/negative plane pair from the serialized source.
The second fixed tape routing reads the bank physically written by the
first pass and returns the final P/N stream on the original bank19. -/
namespace NearCubicWires.RepairOrdinary.CompetitorPlanePacketPair
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open CompetitorPlaneStream CompetitorPlanePacketPass CompetitorPlanePacketBanks
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine := Composition.machine CompetitorPlanePacketPass.machine CompetitorPlanePacketBanks.machine
def word (b : ℕ) (bits : List Bool) (xs ys : List Cell) :=
  CompetitorPlanePacketLoad.packet false bits (countWords b xs)++
    CompetitorPlanePacketLoad.packet true bits (countWords b ys)
def budget (b w : ℕ) (bits : List Bool) (xs ys : List Cell) :=
  CompetitorPlanePacketPass.budget b w bits xs+1+CompetitorPlanePacketPass.budget b w bits ys

theorem pair_run (pre suffix bits : List Bool) (b w : ℕ) (xs ys : List Cell)
    (ambient : Fin 34 → List Bool) (h : Context b w xs ambient)
    (hsource : ambient 32=pre++word b bits xs ys++suffix)
    (hlen : ys.length=xs.length) (hnext : oldWords w ys=newWords false w bits xs)
    (hb : b≤w) (hbits : bits.length≤w)
    (hx : ∀ a∈xs,a.Valid false b w bits) (hy : ∀ a∈ys,a.Valid true b w bits) :
    ∃ r,runFrom machine (budget b w bits xs ys)
      (CompetitorPlanePacketDock.cfg machine.start pre.length ambient)=some r ∧
      r.final.heads=CompetitorPlanePacketDock.heads (pre.length+(word b bits xs ys).length) ∧
      r.final.tapes 19=ZeroPadding.pad (capacity w xs.length) (newWords true w bits ys) ∧
      r.final.tapes 32=ambient 32 ∧ Context b w (nextCells true bits ys) r.final.tapes ∧
      r.steps≤budget b w bits xs ys := by
  let firstWord := CompetitorPlanePacketLoad.packet false bits (countWords b xs)
  let secondWord := CompetitorPlanePacketLoad.packet true bits (countWords b ys)
  obtain ⟨first,hfirst,hfh,h17,h32,hcontext,hfs⟩ := CompetitorPlanePacketPass.packet_pass_run pre
    (secondWord++suffix) bits false b w xs ambient h
    (by simpa only [word,List.append_assoc] using hsource) hb hbits hx
  have hcontext' : Context b w ys (exchanged first.final.tapes) :=
    context_exchange b w xs ys first.final.tapes hcontext hlen (by rw [hnext]; exact h17)
  obtain ⟨second,hsecond,hsh,h19,hs32,hscontext,hss⟩ := reversed_pass_run (pre++firstWord) suffix bits true b w ys
    first.final.tapes hcontext' (by rw [h32,hsource]; simp only [word,firstWord,List.append_assoc]) hb hbits hy
  have hmid : Composition.restart first.final CompetitorPlanePacketBanks.machine.start=
      CompetitorPlanePacketDock.cfg CompetitorPlanePacketBanks.machine.start (pre++firstWord).length first.final.tapes := by
    apply configuration_ext
    · rfl
    · simpa only [Composition.restart,CompetitorPlanePacketDock.cfg,firstWord,List.length_append] using hfh
    · rfl
  have hsecond' : runFrom CompetitorPlanePacketBanks.machine (CompetitorPlanePacketPass.budget b w bits ys)
      (Composition.restart first.final CompetitorPlanePacketBanks.machine.start)=some second := by rw [hmid]; exact hsecond
  have joined := Composition.run_join CompetitorPlanePacketPass.machine CompetitorPlanePacketBanks.machine _ _ _ first second hfirst hsecond'
  refine ⟨Composition.joinedReceipt first second,joined,?_,?_,hs32.trans h32,hscontext,?_⟩
  · change second.final.heads=_
    rw [hsh]
    apply congrArg CompetitorPlanePacketDock.heads
    simp only [word,firstWord,List.length_append,Nat.add_assoc]
  · change second.final.tapes 19=_
    simpa only [hlen] using h19
  · change first.steps+1+second.steps≤budget b w bits xs ys
    unfold budget
    omega

end NearCubicWires.RepairOrdinary.CompetitorPlanePacketPair
