import Proof.CaseAnalysis.WitnessTermJoin
import Proof.CaseAnalysis.RowsIntegerLoad

/-! One actual term field is loaded from the canonical sum stream and
decoded in the reusable bank. The stream cursor, policy width and global
aggregate survive; the same coefficient and circuit fields remain live. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.TermRead
open LocalBitMultitape RecoveryRootRound RadixSemantics CanonicalWitnessCodec
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def core (i : Fin 720) : Fin 725:=i.castAdd 5
def extra (P : ℕ) (source : List Bool) (flag : Bool) : Fin 5→List Bool:=
  ![List.replicate P true,List.replicate (P+1) false,source,List.replicate P false,[flag]]
def extraHeads (pos : ℕ) : Fin 5→ℕ:=![0,0,pos,0,0]
def heads (pos : ℕ) : Fin 725→ℕ:=
  Fin.addCases (m:=720) (n:=5) (motive:=fun _=>ℕ) (fun _ : Fin 720=>0) (extraHeads pos)
def data (P b : ℕ) (bits source : List Bool) (flag : Bool) : Fin 725→List Bool:=
  Fin.addCases (m:=720) (n:=5) (motive:=fun _=>List Bool)
    (TermPadded.input P b bits) (extra P source flag)
def cfg {s : ℕ} (q : Fin s) (P b pos : ℕ) (bits source : List Bool) (flag : Bool) :
    Configuration 725 s:=⟨q,heads pos,data P b bits source flag⟩
def loadSlots : Fin 3→Fin 725:=![722,1,723]
noncomputable def loader:=RecoveryFocus.machine loadSlots FrameLoad.machine
noncomputable def parser:=TapeEmbedding.machine 5 TermCoefficient.machine
noncomputable def machine:=Composition.machine loader parser
def budget (C : ℕ) (bits : List Bool):=4*bits.length+3+1+TermCoefficient.budget C bits

theorem data_other (P b : ℕ) (bits next source : List Bool) (flag : Bool)
    (i : Fin 725) (hi : i≠1) : data P b bits source flag i=data P b next source flag i:=by
  revert hi
  refine Fin.addCases (m:=720) (n:=5) ?_ ?_ i
  · intro j hj
    have hn:j.val≠1:=by intro h;exact hj (Fin.ext h)
    simp only [data,Fin.addCases_left,TermPadded.input,TermCoefficient.input,if_neg hn]
  · intro j _
    simp only [data,Fin.addCases_right]
theorem heads_other (pos next : ℕ) (i : Fin 725) (hi : i≠722) : heads pos i=heads next i:=by
  revert hi
  refine Fin.addCases (m:=720) (n:=5) ?_ ?_ i
  · intro j _;simp only [heads,Fin.addCases_left]
  · intro j hj
    have hn:j≠2:=by intro h;subst j;exact hj rfl
    fin_cases j <;> first | rfl | exact (hn rfl).elim

theorem load_run (P b : ℕ) (bits pre tail : List Bool) (flag : Bool)
    (hcap : 2*bits.length+1≤P) : ∃ result,
    runFrom loader (4*bits.length+3)
      (cfg loader.start P b pre.length [] (pre++frame bits++tail) flag)=some result ∧
      result.steps=4*bits.length+3 ∧
      result.final.heads=heads (pre.length+2*bits.length+1) ∧
      result.final.tapes=data P b bits (pre++frame bits++tail) flag:=by
  let source:=pre++frame bits++tail
  obtain ⟨base,hb,bs,bh,bt⟩:=CloseoutRowsIntegerRound.padded_load_run P bits pre tail hcap
  obtain ⟨r,hr,_rf,rs,rh,rt,keep⟩:=RecoveryFocus.dock loadSlots (by decide) FrameLoad.machine _
    (heads pre.length) (data P b [] source flag) _
    (by intro i;fin_cases i <;> rfl)
    (by
      intro i;fin_cases i
      · exact (ZeroPadding.pad_zero source).symm
      · change ZeroPadding.pad P (frame [])=ZeroPadding.pad P []
        rw [CloseoutRowsIntegerReady.pad_empty_frame P (by omega)]
        simp [ZeroPadding.pad]
      · change List.replicate P false=ZeroPadding.pad P []
        simp [ZeroPadding.pad]) base hb
  refine ⟨r,hr,rs.trans bs,?_,?_⟩
  · funext i
    by_cases h0:i=722
    · subst i;exact (rh 0).trans (bh 0)
    by_cases h1:i=1
    · subst i;exact (rh 1).trans (bh 1)
    by_cases h2:i=723
    · subst i;exact (rh 2).trans (bh 2)
    exact ((keep i (by intro j;fin_cases j <;>
      first | exact Ne.symm h0 | exact Ne.symm h1 | exact Ne.symm h2)).1).trans
      (heads_other _ _ i h0)
  · funext i
    by_cases h0:i=722
    · subst i;exact (rt 0).trans (bt 0)
    by_cases h1:i=1
    · subst i;exact (rt 1).trans (bt 1)
    by_cases h2:i=723
    · subst i;exact (rt 2).trans (bt 2)
    exact ((keep i (by intro j;fin_cases j <;>
      first | exact Ne.symm h0 | exact Ne.symm h1 | exact Ne.symm h2)).2).trans
      (data_other P b [] bits source flag i h1)

theorem read_run (P C : ℕ) (bits pre tail : List Bool) (flag : Bool) (hC : 0<C)
    (hbudget : TermCoefficient.budget C bits+1≤P)
    (hraw : 2*bits.length+1≤P) (hb : natBitLength C≤P) : ∃ out : Fin 720→List Bool, ∃ result,
    runFrom machine (budget C bits)
      (cfg machine.start P (natBitLength C) pre.length [] (pre++frame bits++tail) flag)=some result ∧
      result.steps≤budget C bits ∧
      result.final.heads=heads (pre.length+2*bits.length+1) ∧
      result.final.tapes=Fin.addCases (m:=720) (n:=5) (motive:=fun _=>List Bool)
        out (extra P (pre++frame bits++tail) flag) ∧
      (∀ i,(out i).length≤P) ∧ out 149=ZeroPadding.pad P (List.replicate (natBitLength C) true) ∧
      out 78=ZeroPadding.pad P (frame (TermCoefficient.circuitCode bits)) ∧
      (readTapeBit (out 719) 0=true ↔ PairHeader.valid bits ∧
        ∃ q,decodeCanonicalRational (value (TermCoefficient.coefficientCode bits))=some q ∧
          natBitLength q.num.natAbs≤natBitLength C ∧ natBitLength q.den≤natBitLength C) ∧
      (readTapeBit (out 719) 0=true→
        out 690=ZeroPadding.pad P (frame (SignedSortKey.binary (natBitLength C)
          (value (RationalCold.numerator (TermCoefficient.coefficientCode bits))))) ∧
        out 693=ZeroPadding.pad P (frame (SignedSortKey.binary (natBitLength C)
          (value (RationalCold.denominator (TermCoefficient.coefficientCode bits)))))) ∧
      out 316=ZeroPadding.pad P (frame
        (RecoveryFixedUnpair.leftWord (RationalCold.numeratorWord (TermCoefficient.coefficientCode bits)))):=by
  let source:=pre++frame bits++tail
  let pos:=pre.length+2*bits.length+1
  obtain ⟨l,hl,ls,lh,lt⟩:=load_run P (natBitLength C) bits pre tail flag hraw
  obtain ⟨out,hreader,hcir,hflag,hcoef,hsign,hbound⟩:=TermPadded.fields_run P C bits hC hbudget hraw hb
  have hwidth:=TermWidth.retained P C bits out hreader
  obtain ⟨p,hp,pt,ph,ps⟩:=hreader
  have he:=TapeEmbedding.run_embed TermCoefficient.machine (extraHeads pos) (extra P source flag) _ _ p hp
  let ep:=TapeEmbedding.receipt (extraHeads pos) (extra P source flag) p
  have hrestart:Composition.restart l.final parser.start=
      TapeEmbedding.config (extraHeads pos) (extra P source flag)
        (initialConfiguration TermCoefficient.machine (TermPadded.input P (natBitLength C) bits)):=
    TermJoin.restart_embedded TermCoefficient.machine l.final
      (TermPadded.input P (natBitLength C) bits) (extraHeads pos) (extra P source flag) lh lt
  have hparse:runFrom parser (TermCoefficient.budget C bits)
      (Composition.restart l.final parser.start)=some ep:=by rw [hrestart];exact he
  have hall:=Composition.run_join loader parser _ _ _ l ep hl hparse
  refine ⟨out,Composition.joinedReceipt l ep,hall,?_,?_,?_,hbound,hwidth,hcir,hflag,hcoef,hsign⟩
  · change l.steps+1+p.steps≤budget C bits
    rw [ls]
    unfold budget
    omega
  · change Fin.addCases (m:=720) (n:=5) (motive:=fun _=>ℕ) p.final.heads (extraHeads pos)=heads pos
    rw [funext ph]
    rfl
  · change Fin.addCases (m:=720) (n:=5) (motive:=fun _=>List Bool) p.final.tapes (extra P source flag)=_
    rw [pt]

end NearCubicWires.RepairOrdinary.CloseoutWitness.TermRead
