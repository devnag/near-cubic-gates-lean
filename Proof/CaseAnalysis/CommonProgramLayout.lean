import Proof.CaseAnalysis.RecoverySharedInput
import Proof.CaseAnalysis.CommonPrefixSelected
import Proof.CaseAnalysis.CaseOneHeaderLive
import Proof.CaseAnalysis.CaseTwoDirectInputRun
import Proof.CaseAnalysis.CommonQueryBudget
import Proof.Hierarchy.HierarchyFixedWord

/-! Static layout of the one common oracle program. Its five worker banks
are fresh except for the listed retained inputs and the ONE query/output.
All parameters are fixed before running on the final ordinary input. -/
namespace NearCubicWires.RepairSource.CloseoutCommonProgram
open LocalBitMultitape RepairOrdinary SourceInterfaces SelectedRecoveryIntegration
open OrdinaryOracleCompose CloseoutLanguage
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

structure Parameters where
  sources : EightSources
  k : ℕ
  degree : ℕ
  D : ℕ
  copies : ℕ
  As : ℕ
  Bs : ℕ
  onset : ℕ
  Aw : ℕ
  Bw : ℕ
  Aq : ℕ
  Bq : ℕ
  clock : OrdinaryClock (fun n=>n^(k+2))
  refuter : OrdinaryOracleProgram

def source (p : Parameters):=fixedProjection p.sources
def hierarchy (p : Parameters):=(p.sources.hierarchy (fun n=>n^(p.k+2)) p.clock).hierarchy
def pad (p : Parameters):=padding p.sources p.k p.clock
def code (p : Parameters):=VerifierEncoding.code (hierarchy p).verifier
def amp (p : Parameters):=(selectedAmplifier p.sources.amplification p.degree).constructor.program
def work (p : Parameters):=CloseoutSchedule.Step.workTapes p.sources p.k p.D
def prefixProgram (p : Parameters):=CloseoutCommonPrefix.program p.sources p.k p.D p.copies
  p.As p.Bs p.onset p.Aw p.Bw p.clock p.refuter
def recovery (p : Parameters):=RecoveryBoundedCold.program (source p) p.k p.degree
  (hierarchy p).coefficient (pad p) (code p)
def one (p : Parameters):=RecoveryCaseOnePaddedBit.program (source p) (amp p) p.k
  (hierarchy p).coefficient (pad p) (code p)
def two (p : Parameters):=CloseoutCaseTwo.SelectedOutput.machine (source p) (selectedPCPP p.sources)
  p.k p.D p.copies (hierarchy p).coefficient (pad p) (code p)
def rn (p : Parameters):=RecoveryBoundedCold.tapes (source p) p.k p.degree
def on (p : Parameters):=(one p).base.tapeCount
def tn (p : Parameters):=CloseoutCaseTwo.DirectInput.tapes (source p) (selectedPCPP p.sources) p.k p.D p.copies
def n0 (p : Parameters):=(prefixProgram p).base.tapeCount+1
def n1 (p : Parameters):=n0 p+rn p
def n2 (p : Parameters):=n1 p+28
def n3 (p : Parameters):=n2 p+on p
def n4 (p : Parameters):=n3 p+tn p
def tapes (p : Parameters):=n4 p+2

def word0 (p : Parameters) : Fin (n0 p):=
  (CloseoutCommonPrefix.prepareSlots (work p) p.refuter p.k (CloseoutCommonPrepare.hierarchySlot p.k)).castAdd 1
def capacity0 (p : Parameters) : Fin (n0 p):=
  (CloseoutCommonPrefix.prepareSlots (work p) p.refuter p.k (CloseoutCommonPrepare.capacitySlot p.k)).castAdd 1
def query0 (p : Parameters) : Fin (n0 p):=(prefixProgram p).queryTape.castAdd 1
def output0 (p : Parameters) : Fin (n0 p):=(0 : Fin 1).natAdd (prefixProgram p).base.tapeCount
def address0 (p : Parameters) : Fin (n0 p):=⟨0,by unfold n0;omega⟩
def lift0 (p : Parameters) (i : Fin (n0 p)) : Fin (tapes p):=
  ((((i.castAdd (rn p)).castAdd 28).castAdd (on p)).castAdd (tn p)).castAdd 2
def lift1 (p : Parameters) (i : Fin (n1 p)) : Fin (tapes p):=
  (((i.castAdd 28).castAdd (on p)).castAdd (tn p)).castAdd 2
def lift2 (p : Parameters) (i : Fin (n2 p)) : Fin (tapes p):=
  ((i.castAdd (on p)).castAdd (tn p)).castAdd 2
def lift3 (p : Parameters) (i : Fin (n3 p)) : Fin (tapes p):=(i.castAdd (tn p)).castAdd 2
def prefixSlot (p : Parameters) (i : Fin (prefixProgram p).base.tapeCount):=lift0 p (i.castAdd 1)

def recoveryShared (p : Parameters) : Fin 3→Fin (n0 p):=![word0 p,capacity0 p,query0 p]
def recoveryBank (p : Parameters):=CloseoutCommonPortBank.slot
  (RecoveryBoundedCold.sharedLocal (source p) p.k p.degree) (recoveryShared p)
def recoverySlot (p : Parameters) (i : Fin (rn p)):=lift1 p (recoveryBank p i)
def scalarBank (p : Parameters) (j : Fin 5) : Fin (n1 p):=recoveryBank p
  ((RecoveryBoundedColdSourceGraph.graphSlots (source p) p.k p.degree (j.natAdd 1659)).castAdd 790)
def descriptionBank (p : Parameters) : Fin (n1 p):=recoveryBank p
  ((787 : Fin 790).natAdd (RecoveryBoundedCold.oldTapes (source p) p.k p.degree))
def flagBank (p : Parameters) : Fin (n1 p):=recoveryBank p
  ((369 : Fin 790).natAdd (RecoveryBoundedCold.oldTapes (source p) p.k p.degree))

def clearLocal : Fin 2→Fin 28:=![0,26]
def clearShared (p : Parameters) : Fin 2→Fin (n1 p):=
  ![(address0 p).castAdd (rn p),(query0 p).castAdd (rn p)]
def clearBank (p : Parameters):=CloseoutCommonPortBank.slot clearLocal (clearShared p)
def clearSlot (p : Parameters) (i : Fin 28):=lift2 p (clearBank p i)

def oneLocal (p : Parameters) : Fin 4→Fin (on p):=
  ![⟨0,(one p).base.twoTapes.trans_lt' (by decide)⟩,
    ⟨RecoveryCaseOnePaddedBit.base (source p) (amp p) p.k+16,by
      change _<RecoveryCaseOnePaddedBit.base (source p) (amp p) p.k+45;omega⟩,
    (one p).queryTape,(one p).base.outputTape]
def oneShared (p : Parameters) : Fin 4→Fin (n2 p):=
  ![((word0 p).castAdd (rn p)).castAdd 28,((address0 p).castAdd (rn p)).castAdd 28,
    ((query0 p).castAdd (rn p)).castAdd 28,((output0 p).castAdd (rn p)).castAdd 28]
def oneBank (p : Parameters):=CloseoutCommonPortBank.slot (oneLocal p) (oneShared p)
def oneSlot (p : Parameters) (i : Fin (on p)):=lift3 p (oneBank p i)

def twoLocal (p : Parameters) : Fin 6→Fin (tn p):=
  Fin.addCases (m:=5) (n:=1) (CloseoutCaseTwo.DirectInput.ports (source p) (selectedPCPP p.sources) p.k p.D p.copies)
    (fun _=>CloseoutCaseTwo.DirectInput.outputPort (source p) (selectedPCPP p.sources) p.k p.D p.copies)
def twoShared (p : Parameters) : Fin 6→Fin (n3 p):=
  ![(((word0 p).castAdd (rn p)).castAdd 28).castAdd (on p),
    ((descriptionBank p).castAdd 28).castAdd (on p),
    (((address0 p).castAdd (rn p)).castAdd 28).castAdd (on p),
    ((scalarBank p 0).castAdd 28).castAdd (on p),
    ((scalarBank p 2).castAdd 28).castAdd (on p),
    (((output0 p).castAdd (rn p)).castAdd 28).castAdd (on p)]
def twoBank (p : Parameters):=CloseoutCommonPortBank.slot (twoLocal p) (twoShared p)
def twoSlot (p : Parameters) (i : Fin (tn p)):=(twoBank p i).castAdd 2
def falseLocal : Fin 1→Fin 2:=fun _=>0
def falseShared (p : Parameters) : Fin 1→Fin (n4 p):=
  fun _=>((((output0 p).castAdd (rn p)).castAdd 28).castAdd (on p)).castAdd (tn p)
def falseSlot (p : Parameters):=CloseoutCommonPortBank.slot falseLocal (falseShared p)

def ports (p : Parameters) : Ports (tapes p) where
  twoTapes:=by unfold tapes;omega
  outputTape:=lift0 p (output0 p)
  outputFresh:=by
    have h:=(prefixProgram p).base.twoTapes
    change (prefixProgram p).base.tapeCount+0≠0
    omega
  queryTape:=lift0 p (query0 p)
  queryFresh:=(prefixProgram p).queryFresh

end
end NearCubicWires.RepairSource.CloseoutCommonProgram
