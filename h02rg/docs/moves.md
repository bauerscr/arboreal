# File moves, phase 3 (2026-10-16)

Module paths changed in the phase-3 reorganisation (see `Log.md`). Declaration names did not change.
"merged" means the file was appended, inside `section … end`, at the top of the target file; the target is the
final path. Every other file of the four big libraries moved into a subdirectory with its basename unchanged.

## FRD

| old | new | |
|---|---|---|
| `FRD/PtConstruction.lean` | `FRD/GreenBd.lean` | merged |

## Grassmann

| old | new | |
|---|---|---|
| `Grassmann/Basic.lean` | `Grassmann/Coeff.lean` | merged |

## Loc

| old | new | |
|---|---|---|
| `Loc/Aut.lean` | `Loc/Equivariance.lean` | merged |
| `Loc/LocalPoly.lean` | `Loc/Stencil.lean` | merged |

## Suscept

| old | new | |
|---|---|---|
| `Suscept/Continuity.lean` | `Suscept/Main.lean` | merged |

## Ward

| old | new | |
|---|---|---|
| `Ward/FinVolMain.lean` | `Ward/MainAll.lean` | merged |
| `Ward/MacroAnalysis.lean` | `Ward/Macro.lean` | merged |
| `Ward/ModelFacts.lean` | `Ward/Model.lean` | merged |

## Step2

| old | new | |
|---|---|---|
| `Step2/Block.lean` | `Step2/Map/Block.lean` |  |
| `Step2/Bubble.lean` | `Step2/Coup/Bubble.lean` |  |
| `Step2/BubbleX.lean` | `Step2/Coup/BubbleX.lean` |  |
| `Step2/Cauchy.lean` | `Step2/Map/Cauchy.lean` |  |
| `Step2/CdrHol.lean` | `Step2/Lip/CdrHol.lean` |  |
| `Step2/CdrLip.lean` | `Step2/Lip/CdrLip.lean` |  |
| `Step2/Conj2.lean` | `Step2/Map/Conj2.lean` |  |
| `Step2/Coord.lean` | `Step2/Map/Coord.lean` |  |
| `Step2/CoupBound.lean` | `Step2/Coup/CoupBound.lean` |  |
| `Step2/CoupClass.lean` | `Step2/Coup/CoupClass.lean` |  |
| `Step2/CoupFlow.lean` | `Step2/Coup/CoupFlow.lean` |  |
| `Step2/CoupG.lean` | `Step2/Coup/CoupG.lean` |  |
| `Step2/CoupPast.lean` | `Step2/Coup/CoupPast.lean` |  |
| `Step2/CoupPast6.lean` | `Step2/Coup/CoupPast6.lean` |  |
| `Step2/CoupQuad.lean` | `Step2/Coup/CoupQuad.lean` |  |
| `Step2/CoupQuad2.lean` | `Step2/Coup/CoupQuad2.lean` |  |
| `Step2/CoupStep.lean` | `Step2/Coup/CoupStep.lean` |  |
| `Step2/Coupling.lean` | `Step2/Coup/Coupling.lean` |  |
| `Step2/Crude.lean` | `Step2/Map/Crude.lean` |  |
| `Step2/D2Bub1.lean` | `Step2/D2/D2Bub1.lean` |  |
| `Step2/D2Bub2.lean` | `Step2/D2/D2Bub2.lean` |  |
| `Step2/D2Bub3.lean` | `Step2/D2/D2Bub3.lean` |  |
| `Step2/D2Bub4.lean` | `Step2/D2/D2Bub4.lean` |  |
| `Step2/D2Bub5.lean` | `Step2/D2/D2Bub5.lean` |  |
| `Step2/D2Bv1.lean` | `Step2/D2/D2Bv1.lean` |  |
| `Step2/D2Bv2.lean` | `Step2/D2/D2Bv2.lean` |  |
| `Step2/D2Bv3.lean` | `Step2/D2/D2Bv3.lean` |  |
| `Step2/D2Bv4.lean` | `Step2/D2/D2Bv4.lean` |  |
| `Step2/D2Bv5.lean` | `Step2/D2/D2Bv5.lean` |  |
| `Step2/D2Bv6.lean` | `Step2/D2/D2Bv6.lean` |  |
| `Step2/D2Bv7.lean` | `Step2/D2/D2Bv7.lean` |  |
| `Step2/D2Bv8.lean` | `Step2/D2/D2Bv8.lean` |  |
| `Step2/D2Bv9.lean` | `Step2/D2/D2Bv9.lean` |  |
| `Step2/D2Bx1.lean` | `Step2/D2/D2Bx1.lean` |  |
| `Step2/D2Bx2.lean` | `Step2/D2/D2Bx2.lean` |  |
| `Step2/D2Bx3.lean` | `Step2/D2/D2Bx3.lean` |  |
| `Step2/D2Continuum.lean` | `Step2/D2/D2Continuum.lean` |  |
| `Step2/D2Cov.lean` | `Step2/D2/D2Cov.lean` |  |
| `Step2/D2Dress.lean` | `Step2/D2/D2Dress.lean` |  |
| `Step2/D2Ehat.lean` | `Step2/D2/D2Ehat.lean` |  |
| `Step2/D2Frullani.lean` | `Step2/D2/D2Frullani.lean` |  |
| `Step2/D2HD.lean` | `Step2/D2/D2HD.lean` |  |
| `Step2/D2HV1.lean` | `Step2/D2/D2HV1.lean` |  |
| `Step2/D2HV10.lean` | `Step2/D2/D2HV10.lean` |  |
| `Step2/D2HV11.lean` | `Step2/D2/D2HV11.lean` |  |
| `Step2/D2HV12.lean` | `Step2/D2/D2HV12.lean` |  |
| `Step2/D2HV2.lean` | `Step2/D2/D2HV2.lean` |  |
| `Step2/D2HV3.lean` | `Step2/D2/D2HV3.lean` |  |
| `Step2/D2HV4.lean` | `Step2/D2/D2HV4.lean` |  |
| `Step2/D2HV5.lean` | `Step2/D2/D2HV5.lean` |  |
| `Step2/D2HV6.lean` | `Step2/D2/D2HV6.lean` |  |
| `Step2/D2HV7.lean` | `Step2/D2/D2HV7.lean` |  |
| `Step2/D2HV8.lean` | `Step2/D2/D2HV8.lean` |  |
| `Step2/D2HV9.lean` | `Step2/D2/D2HV9.lean` |  |
| `Step2/D2LDress.lean` | `Step2/D2/D2LDress.lean` |  |
| `Step2/D2Lattice.lean` | `Step2/D2/D2Lattice.lean` |  |
| `Step2/D2Lfun.lean` | `Step2/D2/D2Lfun.lean` |  |
| `Step2/D2Line3.lean` | `Step2/D2/D2HV5.lean` | merged |
| `Step2/D2Lval.lean` | `Step2/D2/D2Lval.lean` |  |
| `Step2/D2Past.lean` | `Step2/D2/D2Past.lean` |  |
| `Step2/D2Profile.lean` | `Step2/D2/D2Profile.lean` |  |
| `Step2/D2Prop.lean` | `Step2/D2/D2Prop.lean` |  |
| `Step2/D2S01.lean` | `Step2/D2/D2S01.lean` |  |
| `Step2/D2Sh1.lean` | `Step2/D2/D2Sh1.lean` |  |
| `Step2/D2Sh10.lean` | `Step2/D2/D2Sh10.lean` |  |
| `Step2/D2Sh11.lean` | `Step2/D2/D2Sh11.lean` |  |
| `Step2/D2Sh12.lean` | `Step2/D2/D2Sh12.lean` |  |
| `Step2/D2Sh13.lean` | `Step2/D2/D2Sh13.lean` |  |
| `Step2/D2Sh2.lean` | `Step2/D2/D2Sh2.lean` |  |
| `Step2/D2Sh3.lean` | `Step2/D2/D2Sh3.lean` |  |
| `Step2/D2Sh4.lean` | `Step2/D2/D2Sh4.lean` |  |
| `Step2/D2Sh5.lean` | `Step2/D2/D2Sh5.lean` |  |
| `Step2/D2Sh6.lean` | `Step2/D2/D2Sh6.lean` |  |
| `Step2/D2Sh7.lean` | `Step2/D2/D2Sh7.lean` |  |
| `Step2/D2Sh8.lean` | `Step2/D2/D2Sh8.lean` |  |
| `Step2/D2Sh9.lean` | `Step2/D2/D2Sh9.lean` |  |
| `Step2/D2Tad.lean` | `Step2/D2/D2Tad.lean` |  |
| `Step2/D2Torus.lean` | `Step2/D2/D2Torus.lean` |  |
| `Step2/DCov.lean` | `Step2/Map/DCov.lean` |  |
| `Step2/Defs.lean` | `Step2/Map/Defs.lean` |  |
| `Step2/Degree.lean` | `Step2/Coup/Degree.lean` |  |
| `Step2/Est4.lean` | `Step2/Coup/Est4.lean` |  |
| `Step2/Exp.lean` | `Step2/Map/Exp.lean` |  |
| `Step2/F2SharpGlue.lean` | `Step2/Last/F2SharpGlue.lean` |  |
| `Step2/Fact.lean` | `Step2/Map/Fact.lean` |  |
| `Step2/FieldScale.lean` | `Step2/Map/FieldScale.lean` |  |
| `Step2/FieldScaleC.lean` | `Step2/Map/FieldScaleC.lean` |  |
| `Step2/FlowBounds.lean` | `Step2/Flow/FlowBounds.lean` |  |
| `Step2/FlowComplete.lean` | `Step2/Flow/FlowComplete.lean` |  |
| `Step2/FlowComplete2.lean` | `Step2/Flow/FlowComplete2.lean` |  |
| `Step2/FlowComplete2Hyp.lean` | `Step2/Flow/FlowComplete2Hyp.lean` |  |
| `Step2/FlowComplete2X.lean` | `Step2/Flow/FlowComplete2X.lean` |  |
| `Step2/FlowCompleteBand.lean` | `Step2/Flow/FlowCompleteBand.lean` |  |
| `Step2/FlowCompleteBandHyp.lean` | `Step2/Flow/FlowCompleteBandHyp.lean` |  |
| `Step2/FlowCompleteHyp.lean` | `Step2/Flow/FlowCompleteHyp.lean` |  |
| `Step2/FlowCont.lean` | `Step2/FlowCont/FlowCont.lean` |  |
| `Step2/FlowCont1.lean` | `Step2/FlowCont/FlowCont1.lean` |  |
| `Step2/FlowCont2.lean` | `Step2/FlowCont/FlowCont2.lean` |  |
| `Step2/FlowCont3.lean` | `Step2/FlowCont/FlowCont3.lean` |  |
| `Step2/FlowDiffBasic.lean` | `Step2/FlowCont/FlowDiffBasic.lean` |  |
| `Step2/FlowDiffClamp.lean` | `Step2/FlowCont/FlowDiffClamp.lean` |  |
| `Step2/FlowDiffHist.lean` | `Step2/FlowCont/FlowDiffHist.lean` |  |
| `Step2/FlowDiffStep.lean` | `Step2/FlowCont/FlowDiffStep.lean` |  |
| `Step2/FlowF1.lean` | `Step2/Flow/FlowF1.lean` |  |
| `Step2/FlowF1Alg.lean` | `Step2/Flow/FlowF1Alg.lean` |  |
| `Step2/FlowF1S1.lean` | `Step2/Flow/FlowF1S1.lean` |  |
| `Step2/FlowF1S2.lean` | `Step2/Flow/FlowF1S2.lean` |  |
| `Step2/FlowF1S3.lean` | `Step2/Flow/FlowF1S3.lean` |  |
| `Step2/FlowF1b.lean` | `Step2/Flow/FlowF1b.lean` |  |
| `Step2/FlowF1c.lean` | `Step2/Flow/FlowF1c.lean` |  |
| `Step2/FlowF1d.lean` | `Step2/Flow/FlowF1d.lean` |  |
| `Step2/FlowFadeHist.lean` | `Step2/Lip/FlowFadeHist.lean` |  |
| `Step2/FlowFadePair.lean` | `Step2/Lip/FlowZetaPair.lean` | merged |
| `Step2/FlowFadeRun.lean` | `Step2/Lip/FlowFadeRun.lean` |  |
| `Step2/FlowFinalZ.lean` | `Step2/Flow/FlowFinalZ.lean` |  |
| `Step2/FlowFinalZAux.lean` | `Step2/Flow/FlowFinalZAux.lean` |  |
| `Step2/FlowFinalZHyp.lean` | `Step2/Flow/FlowFinalZHyp.lean` |  |
| `Step2/FlowFixedRMsq.lean` | `Step2/FlowCont/FlowFixedRMsq.lean` |  |
| `Step2/FlowGlueG.lean` | `Step2/Last/FlowGlueG.lean` |  |
| `Step2/FlowGlueHist.lean` | `Step2/Last/FlowGlueHist.lean` |  |
| `Step2/FlowGlueLast.lean` | `Step2/Last/FlowGlueLast.lean` |  |
| `Step2/FlowGlueStep.lean` | `Step2/Last/FlowGlueStep.lean` |  |
| `Step2/FlowHV.lean` | `Step2/Flow/FlowHV.lean` |  |
| `Step2/FlowHist.lean` | `Step2/Flow/FlowHist.lean` |  |
| `Step2/FlowHor2Aux.lean` | `Step2/Flow/FlowHor2Aux.lean` |  |
| `Step2/FlowHor2Thm.lean` | `Step2/Flow/FlowHor2Thm.lean` |  |
| `Step2/FlowHorizon.lean` | `Step2/Flow/FlowHorizon.lean` |  |
| `Step2/FlowLastBand.lean` | `Step2/Last/FlowLastBand.lean` |  |
| `Step2/FlowLastBand2.lean` | `Step2/Last/FlowLastBand2.lean` |  |
| `Step2/FlowLastCont.lean` | `Step2/Last/FlowLastCont.lean` |  |
| `Step2/FlowLastCont2a.lean` | `Step2/Last/FlowLastCont2a.lean` |  |
| `Step2/FlowLastCont2b.lean` | `Step2/Last/FlowLastCont2b.lean` |  |
| `Step2/FlowLastF1a.lean` | `Step2/Last/FlowLastF1a.lean` |  |
| `Step2/FlowLastF1b.lean` | `Step2/Last/FlowLastF1b.lean` |  |
| `Step2/FlowLastLip1.lean` | `Step2/Last/FlowLastLip1.lean` |  |
| `Step2/FlowLastLip2.lean` | `Step2/Last/FlowLastLip2.lean` |  |
| `Step2/FlowLastLip3.lean` | `Step2/Last/FlowLastLip3.lean` |  |
| `Step2/FlowLastLip4.lean` | `Step2/Last/FlowLastLip4.lean` |  |
| `Step2/FlowLastLip5.lean` | `Step2/Last/FlowLastLip5.lean` |  |
| `Step2/FlowLastLip6.lean` | `Step2/Last/FlowLastLip6.lean` |  |
| `Step2/FlowLipCmp.lean` | `Step2/Lip/FlowLipCmp.lean` |  |
| `Step2/FlowLipCmp2.lean` | `Step2/Lip/FlowLipCmp2.lean` |  |
| `Step2/FlowLipCoup.lean` | `Step2/Lip/FlowLipCoup.lean` |  |
| `Step2/FlowLipCov.lean` | `Step2/Lip/FlowLipCov.lean` |  |
| `Step2/FlowLipCovH.lean` | `Step2/Lip/FlowLipCovH.lean` |  |
| `Step2/FlowLipCx.lean` | `Step2/Lip/FlowLipCx.lean` |  |
| `Step2/FlowLipDom.lean` | `Step2/Lip/FlowLipDom.lean` |  |
| `Step2/FlowLipErr.lean` | `Step2/Lip/FlowLipErr.lean` |  |
| `Step2/FlowLipFin.lean` | `Step2/Lip/FlowLipFin.lean` |  |
| `Step2/FlowLipFinal.lean` | `Step2/Lip/FlowLipFinal.lean` |  |
| `Step2/FlowLipG.lean` | `Step2/Lip/FlowLipG.lean` |  |
| `Step2/FlowLipGA.lean` | `Step2/Lip/FlowLipGA.lean` |  |
| `Step2/FlowLipGH.lean` | `Step2/Lip/FlowLipGH.lean` |  |
| `Step2/FlowLipGH2.lean` | `Step2/Lip/FlowLipGH2.lean` |  |
| `Step2/FlowLipGH3.lean` | `Step2/Lip/FlowLipGH3.lean` |  |
| `Step2/FlowLipHist.lean` | `Step2/Lip/FlowLipHist.lean` |  |
| `Step2/FlowLipHist2.lean` | `Step2/Lip/FlowLipHist2.lean` |  |
| `Step2/FlowLipIn.lean` | `Step2/Lip/FlowLipIn.lean` |  |
| `Step2/FlowLipInd.lean` | `Step2/Lip/FlowLipInd.lean` |  |
| `Step2/FlowLipK.lean` | `Step2/Lip/FlowLipK.lean` |  |
| `Step2/FlowLipMain.lean` | `Step2/Lip/FlowLipMain.lean` |  |
| `Step2/FlowLipNorm.lean` | `Step2/Lip/FlowLipNorm.lean` |  |
| `Step2/FlowLipPair.lean` | `Step2/Lip/FlowLipPair.lean` |  |
| `Step2/FlowLipRec.lean` | `Step2/Lip/FlowLipRec.lean` |  |
| `Step2/FlowLipRun.lean` | `Step2/Lip/FlowLipRun.lean` |  |
| `Step2/FlowLipRunH.lean` | `Step2/Lip/FlowLipRunH.lean` |  |
| `Step2/FlowLipScale.lean` | `Step2/Lip/FlowLipScale.lean` |  |
| `Step2/FlowLipShv.lean` | `Step2/Lip/FlowLipShv.lean` |  |
| `Step2/FlowLipSig.lean` | `Step2/Lip/FlowLipSig.lean` |  |
| `Step2/FlowLipSize.lean` | `Step2/Lip/FlowLipSize.lean` |  |
| `Step2/FlowLipStep.lean` | `Step2/Lip/FlowLipStep.lean` |  |
| `Step2/FlowLipStep2.lean` | `Step2/Lip/FlowLipStep2.lean` |  |
| `Step2/FlowLipT.lean` | `Step2/Lip/FlowLipT.lean` |  |
| `Step2/FlowLipW.lean` | `Step2/Lip/FlowLipW.lean` |  |
| `Step2/FlowMain.lean` | `Step2/Flow/FlowMain.lean` |  |
| `Step2/FlowMasterHypL.lean` | `Step2/Flow/FlowMasterHypL.lean` |  |
| `Step2/FlowMasterHypLZ.lean` | `Step2/Flow/FlowMasterHypLZ.lean` |  |
| `Step2/FlowMsqCov.lean` | `Step2/FlowCont/FlowMsqCov.lean` |  |
| `Step2/FlowMsqStep.lean` | `Step2/FlowCont/FlowMsqStep.lean` |  |
| `Step2/FlowRG.lean` | `Step2/Flow/FlowRG.lean` |  |
| `Step2/FlowRGIn.lean` | `Step2/Flow/FlowRGIn.lean` |  |
| `Step2/FlowRange.lean` | `Step2/Flow/FlowRange.lean` |  |
| `Step2/FlowRangeHyp.lean` | `Step2/Flow/FlowRangeHyp.lean` |  |
| `Step2/FlowSharp1.lean` | `Step2/Flow/FlowSharp1.lean` |  |
| `Step2/FlowSharp2.lean` | `Step2/Flow/FlowSharp2.lean` |  |
| `Step2/FlowSharp3.lean` | `Step2/Flow/FlowSharp3.lean` |  |
| `Step2/FlowStep.lean` | `Step2/Flow/FlowStep.lean` |  |
| `Step2/FlowThm.lean` | `Step2/Flow/FlowThm.lean` |  |
| `Step2/FlowValid.lean` | `Step2/Flow/FlowValid.lean` |  |
| `Step2/FlowWin1.lean` | `Step2/Flow/FlowWin1.lean` |  |
| `Step2/FlowWin2.lean` | `Step2/Flow/FlowWin2.lean` |  |
| `Step2/FlowZetaApriori.lean` | `Step2/Lip/FlowZetaApriori.lean` |  |
| `Step2/FlowZetaCov.lean` | `Step2/Lip/FlowZetaCov.lean` |  |
| `Step2/FlowZetaHist.lean` | `Step2/Lip/FlowZetaHist.lean` |  |
| `Step2/FlowZetaMain.lean` | `Step2/Lip/FlowZetaMain.lean` |  |
| `Step2/FlowZetaPair.lean` | `Step2/Lip/FlowZetaPair.lean` |  |
| `Step2/FlowZetaStep.lean` | `Step2/Lip/FlowZetaStep.lean` |  |
| `Step2/FullStep.lean` | `Step2/Map/FullStep.lean` |  |
| `Step2/Gen.lean` | `Step2/Map/Gen.lean` |  |
| `Step2/Geom.lean` | `Step2/Map/Geom.lean` |  |
| `Step2/Hol.lean` | `Step2/Map/Hol.lean` |  |
| `Step2/HolC.lean` | `Step2/Map/HolC.lean` |  |
| `Step2/JInv.lean` | `Step2/Coup/JInv.lean` |  |
| `Step2/JSym.lean` | `Step2/Coup/JSym.lean` |  |
| `Step2/KCov.lean` | `Step2/Map/KCov.lean` |  |
| `Step2/Lambda.lean` | `Step2/Map/Lambda.lean` |  |
| `Step2/LastCoup.lean` | `Step2/Last/LastCoup.lean` |  |
| `Step2/LastGeo.lean` | `Step2/Last/LastGeo.lean` |  |
| `Step2/LastKCov.lean` | `Step2/Last/LastKCov.lean` |  |
| `Step2/LastNBlock.lean` | `Step2/Last/LastNBlock.lean` |  |
| `Step2/LastNDefs.lean` | `Step2/Last/LastNDefs.lean` |  |
| `Step2/LastNMain.lean` | `Step2/Last/LastNMain.lean` |  |
| `Step2/LastNRG.lean` | `Step2/Last/LastNRG.lean` |  |
| `Step2/LastNSecond.lean` | `Step2/Last/LastNSecond.lean` |  |
| `Step2/LastNStep.lean` | `Step2/Last/LastNStep.lean` |  |
| `Step2/LastRaw.lean` | `Step2/Last/LastRaw.lean` |  |
| `Step2/LastStep.lean` | `Step2/Last/LastStep.lean` |  |
| `Step2/LastSym.lean` | `Step2/Last/LastSym.lean` |  |
| `Step2/LastValid.lean` | `Step2/Last/FlowLastBand.lean` | merged |
| `Step2/Lin.lean` | `Step2/Map/Lin.lean` |  |
| `Step2/LinB.lean` | `Step2/Map/LinB.lean` |  |
| `Step2/LinBound.lean` | `Step2/Map/LinBound.lean` |  |
| `Step2/Lip.lean` | `Step2/Lip/Lip.lean` |  |
| `Step2/LipW.lean` | `Step2/Lip/LipW.lean` |  |
| `Step2/LocAut.lean` | `Step2/Map/LocAut.lean` |  |
| `Step2/LocTr.lean` | `Step2/Map/LocTr.lean` |  |
| `Step2/Main.lean` | `Step2/Map/Main.lean` |  |
| `Step2/Mem.lean` | `Step2/Map/Mem.lean` |  |
| `Step2/MsqCont.lean` | `Step2/FlowCont/MsqCont.lean` |  |
| `Step2/Norm.lean` | `Step2/Map/Norm.lean` |  |
| `Step2/Ord.lean` | `Step2/Map/Ord.lean` |  |
| `Step2/RGMap.lean` | `Step2/Map/RGMap.lean` |  |
| `Step2/Raw.lean` | `Step2/Map/Raw.lean` |  |
| `Step2/RawMap.lean` | `Step2/Map/RawMap.lean` |  |
| `Step2/Reapp.lean` | `Step2/Map/Reapp.lean` |  |
| `Step2/Reblock.lean` | `Step2/Map/Reblock.lean` |  |
| `Step2/ReblockBound.lean` | `Step2/Map/ReblockBound.lean` |  |
| `Step2/Rescale.lean` | `Step2/Map/FullStep.lean` | merged |
| `Step2/Second.lean` | `Step2/Map/Second.lean` |  |
| `Step2/Spaces2.lean` | `Step2/Map/Spaces2.lean` |  |
| `Step2/Split.lean` | `Step2/Map/Split.lean` |  |
| `Step2/SplitSmall.lean` | `Step2/Map/SplitSmall.lean` |  |
| `Step2/StepFinal.lean` | `Step2/Map/StepFinal.lean` |  |
| `Step2/SymCov.lean` | `Step2/Map/SymCov.lean` |  |
| `Step2/TNorm2.lean` | `Step2/Map/TNorm2.lean` |  |
| `Step2/ThetaScale.lean` | `Step2/Map/ThetaScale.lean` |  |
| `Step2/TwoScale.lean` | `Step2/Map/TwoScale.lean` |  |
| `Step2/V0Sym.lean` | `Step2/Coup/V0Sym.lean` |  |
| `Step2/VNorm.lean` | `Step2/Coup/VNorm.lean` |  |
| `Step2/WContract.lean` | `Step2/Map/WContract.lean` |  |
| `Step2/WCov.lean` | `Step2/Map/WCov.lean` |  |
| `Step2/Wick.lean` | `Step2/Coup/Wick.lean` |  |
| `Step2/Wick2.lean` | `Step2/Coup/Wick2.lean` |  |
| `Step2/WickAsm.lean` | `Step2/Coup/WickAsm.lean` |  |
| `Step2/WickSum.lean` | `Step2/Coup/WickSum.lean` |  |
| `Step2/XStep.lean` | `Step2/Map/XStep.lean` |  |
| `Step2/ZeroMode.lean` | `Step2/Last/ZeroMode.lean` |  |
| `Step2/ZeroTOk.lean` | `Step2/Last/ZeroTOk.lean` |  |
| `Step2/ZetaFact.lean` | `Step2/Map/ZetaFact.lean` |  |
| `Step2/ZetaSharp0.lean` | `Step2/Flow/ZetaSharp0.lean` |  |
| `Step2/ZetaSharp1.lean` | `Step2/Flow/ZetaSharp1.lean` |  |
| `Step2/ZetaSharp2.lean` | `Step2/Flow/ZetaSharp2.lean` |  |
| `Step2/ZetaSharp3.lean` | `Step2/Flow/ZetaSharp3.lean` |  |
| `Step2/ZetaSharp4.lean` | `Step2/Flow/ZetaSharp4.lean` |  |
| `Step2/ZetaSharp5.lean` | `Step2/Flow/ZetaSharp5.lean` |  |
| `Step2/ZetaSharp6.lean` | `Step2/Flow/ZetaSharp6.lean` |  |
| `Step2/ZetaSharpHypX.lean` | `Step2/Flow/ZetaSharpHypX.lean` |  |
| `Step2/ZetaSharpThm.lean` | `Step2/Flow/ZetaSharpThm.lean` |  |

## Obs2

| old | new | |
|---|---|---|
| `Obs2/AnchAB.lean` | `Obs2/Pair/AnchAB.lean` |  |
| `Obs2/BlockFlow.lean` | `Obs2/Flow/BlockFlow.lean` |  |
| `Obs2/BlockFlow2.lean` | `Obs2/Flow/BlockFlow2.lean` |  |
| `Obs2/BlockFlow3.lean` | `Obs2/Flow/BlockFlow3.lean` |  |
| `Obs2/BlockFlowE.lean` | `Obs2/Flow/BlockFlowE.lean` |  |
| `Obs2/BlockMass.lean` | `Obs2/Flow/BlockMass.lean` |  |
| `Obs2/BlockO1.lean` | `Obs2/Est/BlockO1.lean` |  |
| `Obs2/BlockO2.lean` | `Obs2/Est/BlockO2.lean` |  |
| `Obs2/BlockO3.lean` | `Obs2/Est/BlockO3.lean` |  |
| `Obs2/BlockO4.lean` | `Obs2/Est/BlockO4.lean` |  |
| `Obs2/BlockO5.lean` | `Obs2/Est/BlockO5.lean` |  |
| `Obs2/BlockO6.lean` | `Obs2/Est/BlockO6.lean` |  |
| `Obs2/BlockOAB1.lean` | `Obs2/Est/BlockOAB1.lean` |  |
| `Obs2/BlockOAB2.lean` | `Obs2/Est/BlockOAB2.lean` |  |
| `Obs2/BlockOAB3.lean` | `Obs2/Est/BlockOAB3.lean` |  |
| `Obs2/BlockOAB4.lean` | `Obs2/Est/BlockOAB4.lean` |  |
| `Obs2/BlockOAB5.lean` | `Obs2/Est/BlockOAB5.lean` |  |
| `Obs2/BlockOAB6.lean` | `Obs2/Est/BlockOAB6.lean` |  |
| `Obs2/BlockOU2.lean` | `Obs2/Est/BlockOU2.lean` |  |
| `Obs2/BlockOU3.lean` | `Obs2/Est/BlockOU3.lean` |  |
| `Obs2/BlockOU4.lean` | `Obs2/Est/BlockOU4.lean` |  |
| `Obs2/BlockOU6.lean` | `Obs2/Est/BlockOU6.lean` |  |
| `Obs2/CauchyW.lean` | `Obs2/Map/CauchyW.lean` |  |
| `Obs2/Coal.lean` | `Obs2/Pair/Coal.lean` |  |
| `Obs2/CoalHist.lean` | `Obs2/Pair/CoalHist.lean` |  |
| `Obs2/CoalHistL.lean` | `Obs2/Pair/CoalHistL.lean` |  |
| `Obs2/CoalHistR.lean` | `Obs2/Pair/CoalHistR.lean` |  |
| `Obs2/CoalR.lean` | `Obs2/Pair/CoalR.lean` |  |
| `Obs2/ConstSplit.lean` | `Obs2/Map/ConstSplit.lean` |  |
| `Obs2/Coupling.lean` | `Obs2/Map/Coupling.lean` |  |
| `Obs2/CrudeG.lean` | `Obs2/Est/CrudeG.lean` |  |
| `Obs2/ErrAB.lean` | `Obs2/Est/ErrAB.lean` |  |
| `Obs2/ErrABX.lean` | `Obs2/Est/ErrABX.lean` |  |
| `Obs2/EstAB.lean` | `Obs2/Est/EstAB.lean` |  |
| `Obs2/EstBlock.lean` | `Obs2/Est/EstBlock.lean` |  |
| `Obs2/EstBlockAB.lean` | `Obs2/Est/EstBlockAB.lean` |  |
| `Obs2/EstBlockU.lean` | `Obs2/Est/EstBlockU.lean` |  |
| `Obs2/EstLoc.lean` | `Obs2/Est/EstLoc.lean` |  |
| `Obs2/EstLocU.lean` | `Obs2/Est/EstLocU.lean` |  |
| `Obs2/EstMu.lean` | `Obs2/Flow/EstMu.lean` |  |
| `Obs2/EstNorm.lean` | `Obs2/Est/EstNorm.lean` |  |
| `Obs2/EstNormAB.lean` | `Obs2/Est/EstNormAB.lean` |  |
| `Obs2/ExactStep.lean` | `Obs2/Map/ExactStep.lean` |  |
| `Obs2/FlowMu.lean` | `Obs2/Flow/FlowMu.lean` |  |
| `Obs2/GamBulk.lean` | `Obs2/Flow/GamBulk.lean` |  |
| `Obs2/GamChain2.lean` | `Obs2/Flow/GamChain2.lean` |  |
| `Obs2/GamRem.lean` | `Obs2/Flow/GamRem.lean` |  |
| `Obs2/GamTop.lean` | `Obs2/Flow/GamTop.lean` |  |
| `Obs2/Gamma1.lean` | `Obs2/Flow/Gamma1.lean` |  |
| `Obs2/Gamma2.lean` | `Obs2/Flow/Gamma2.lean` |  |
| `Obs2/GradAB1.lean` | `Obs2/Flow/GradAB1.lean` |  |
| `Obs2/GradAB2.lean` | `Obs2/Flow/GradAB2.lean` |  |
| `Obs2/GradAB3.lean` | `Obs2/Flow/GradAB3.lean` |  |
| `Obs2/GradAB4.lean` | `Obs2/Flow/GradAB4.lean` |  |
| `Obs2/GramDiff.lean` | `Obs2/Map/GramDiff.lean` |  |
| `Obs2/Hist.lean` | `Obs2/Flow/Hist.lean` |  |
| `Obs2/HolO.lean` | `Obs2/Map/HolO.lean` |  |
| `Obs2/HolW.lean` | `Obs2/Map/HolW.lean` |  |
| `Obs2/KFlatO.lean` | `Obs2/Est/KFlatO.lean` |  |
| `Obs2/KObs1.lean` | `Obs2/Est/KObs1.lean` |  |
| `Obs2/KObs2.lean` | `Obs2/Est/KObs2.lean` |  |
| `Obs2/KObs3.lean` | `Obs2/Est/KObs3.lean` |  |
| `Obs2/KObs4W.lean` | `Obs2/Est/KObs4W.lean` |  |
| `Obs2/KObsAB.lean` | `Obs2/Est/KObsAB.lean` |  |
| `Obs2/KObsInd.lean` | `Obs2/Est/KObsInd.lean` |  |
| `Obs2/KObsU.lean` | `Obs2/Est/KObsU.lean` |  |
| `Obs2/LastKO1.lean` | `Obs2/Est/LastKO1.lean` |  |
| `Obs2/LastKO2.lean` | `Obs2/Est/LastKO2.lean` |  |
| `Obs2/LinBO.lean` | `Obs2/Est/LinBO.lean` |  |
| `Obs2/LinBoundAB.lean` | `Obs2/Est/LinBoundAB.lean` |  |
| `Obs2/LinBoundO.lean` | `Obs2/Est/LinBoundO.lean` |  |
| `Obs2/LinBoundOL.lean` | `Obs2/Est/LinBoundOL.lean` |  |
| `Obs2/LinBoundU.lean` | `Obs2/Est/LinBoundU.lean` |  |
| `Obs2/LinComp.lean` | `Obs2/Est/LinComp.lean` |  |
| `Obs2/LinCompL.lean` | `Obs2/Est/LinCompL.lean` |  |
| `Obs2/LinIter.lean` | `Obs2/Flow/LinIter.lean` |  |
| `Obs2/LinO.lean` | `Obs2/Est/LinO.lean` |  |
| `Obs2/LinearMrg.lean` | `Obs2/Map/LinearMrg.lean` |  |
| `Obs2/LinearStep.lean` | `Obs2/Map/LinearStep.lean` |  |
| `Obs2/Loc.lean` | `Obs2/Loc/Loc.lean` |  |
| `Obs2/LocABRepro.lean` | `Obs2/Loc/LocABRepro.lean` |  |
| `Obs2/LocABt.lean` | `Obs2/Loc/LocABt.lean` |  |
| `Obs2/LocContract.lean` | `Obs2/Loc/LocContract.lean` |  |
| `Obs2/LocContractLarge.lean` | `Obs2/Loc/LocContractLarge.lean` |  |
| `Obs2/LocFlow.lean` | `Obs2/Loc/LocFlow.lean` |  |
| `Obs2/LocGram.lean` | `Obs2/Loc/LocGram.lean` |  |
| `Obs2/LocRepro.lean` | `Obs2/Loc/LocRepro.lean` |  |
| `Obs2/LocT.lean` | `Obs2/Loc/LocT.lean` |  |
| `Obs2/LocWeight.lean` | `Obs2/Loc/LocWeight.lean` |  |
| `Obs2/Map.lean` | `Obs2/Map/Map.lean` |  |
| `Obs2/MemGronwall.lean` | `Obs2/Flow/MemGronwall.lean` |  |
| `Obs2/MemGronwall2.lean` | `Obs2/Flow/MemGronwall2.lean` |  |
| `Obs2/MuChain2.lean` | `Obs2/Flow/MuChain2.lean` |  |
| `Obs2/MuChainAB.lean` | `Obs2/Flow/MuChainAB.lean` |  |
| `Obs2/MuChainAB2.lean` | `Obs2/Flow/MuChainAB2.lean` |  |
| `Obs2/MuHist.lean` | `Obs2/Flow/MuHist.lean` |  |
| `Obs2/MuHist2.lean` | `Obs2/Flow/MuHist2.lean` |  |
| `Obs2/MuK.lean` | `Obs2/Flow/MuK.lean` |  |
| `Obs2/MuTad0.lean` | `Obs2/Flow/MuTad0.lean` |  |
| `Obs2/MuTad1.lean` | `Obs2/Flow/MuTad1.lean` |  |
| `Obs2/MuTad2.lean` | `Obs2/Flow/MuTad2.lean` |  |
| `Obs2/MuTad3.lean` | `Obs2/Flow/MuTad3.lean` |  |
| `Obs2/MuTau.lean` | `Obs2/Flow/MuTau.lean` |  |
| `Obs2/OSNorm.lean` | `Obs2/Map/OSNorm.lean` |  |
| `Obs2/Ops.lean` | `Obs2/Map/Ops.lean` |  |
| `Obs2/OrdW.lean` | `Obs2/Map/OrdW.lean` |  |
| `Obs2/PairChain.lean` | `Obs2/Pair/PairChain.lean` |  |
| `Obs2/PairLin1.lean` | `Obs2/Pair/PairLin1.lean` |  |
| `Obs2/PairRed.lean` | `Obs2/Pair/PairRed.lean` |  |
| `Obs2/PairSect.lean` | `Obs2/Pair/PairSect.lean` |  |
| `Obs2/PauliLip.lean` | `Obs2/Loc/PauliLip.lean` |  |
| `Obs2/PauliMass.lean` | `Obs2/Loc/PauliMass.lean` |  |
| `Obs2/ProdObs.lean` | `Obs2/Flow/ProdObs.lean` |  |
| `Obs2/ReblockO.lean` | `Obs2/Est/ReblockO.lean` |  |
| `Obs2/RelRec.lean` | `Obs2/Flow/RelRec.lean` |  |
| `Obs2/RelRecTop.lean` | `Obs2/Flow/RelRecTop.lean` |  |
| `Obs2/Reloc.lean` | `Obs2/Loc/Reloc.lean` |  |
| `Obs2/RestartChain.lean` | `Obs2/Flow/RestartChain.lean` |  |
| `Obs2/RestartFlow.lean` | `Obs2/Flow/RestartFlow.lean` |  |
| `Obs2/RestartRec.lean` | `Obs2/Flow/RestartRec.lean` |  |
| `Obs2/RestartRec2.lean` | `Obs2/Flow/RestartRec2.lean` |  |
| `Obs2/RestartRec2Flow.lean` | `Obs2/Flow/RestartRec2Flow.lean` |  |
| `Obs2/SFirst1.lean` | `Obs2/Pair/SFirst1.lean` |  |
| `Obs2/Second.lean` | `Obs2/Map/Second.lean` |  |
| `Obs2/SecondO.lean` | `Obs2/Est/SecondO.lean` |  |
| `Obs2/SeedAB.lean` | `Obs2/Pair/SeedAB.lean` |  |
| `Obs2/ShareAB1.lean` | `Obs2/Pair/ShareAB1.lean` |  |
| `Obs2/SigmaScale.lean` | `Obs2/Map/SigmaScale.lean` |  |
| `Obs2/SplitO.lean` | `Obs2/Est/SplitO.lean` |  |
| `Obs2/Step2O.lean` | `Obs2/Est/Step2O.lean` |  |
| `Obs2/Step2OAB.lean` | `Obs2/Est/Step2OAB.lean` |  |
| `Obs2/Step2OL.lean` | `Obs2/Est/Step2OL.lean` |  |
| `Obs2/Step2OLAB.lean` | `Obs2/Est/Step2OLAB.lean` |  |
| `Obs2/Step2OLU.lean` | `Obs2/Est/Step2OLU.lean` |  |
| `Obs2/Step3O.lean` | `Obs2/Est/Step3O.lean` |  |
| `Obs2/Step3OAB.lean` | `Obs2/Est/Step3OAB.lean` |  |
| `Obs2/Step3OL.lean` | `Obs2/Est/Step3OL.lean` |  |
| `Obs2/Step3OLAB.lean` | `Obs2/Est/Step3OLAB.lean` |  |
| `Obs2/Step3OLU.lean` | `Obs2/Est/Step3OLU.lean` |  |
| `Obs2/Step3OU.lean` | `Obs2/Est/Step3OU.lean` |  |
| `Obs2/StepKO.lean` | `Obs2/Est/StepKO.lean` |  |
| `Obs2/StepKOW.lean` | `Obs2/Est/StepKOW.lean` |  |
| `Obs2/StepKOWAB.lean` | `Obs2/Est/StepKOWAB.lean` |  |
| `Obs2/StepKOWU.lean` | `Obs2/Est/StepKOWU.lean` |  |
| `Obs2/Supp.lean` | `Obs2/Map/Supp.lean` |  |
| `Obs2/SwapHist.lean` | `Obs2/Map/SwapHist.lean` |  |
| `Obs2/SwapO.lean` | `Obs2/Map/SwapO.lean` |  |
| `Obs2/SymO.lean` | `Obs2/Map/SymO.lean` |  |
| `Obs2/Tau2.lean` | `Obs2/Flow/Tau2.lean` |  |
| `Obs2/Tau2Bd.lean` | `Obs2/Flow/Tau2Bd.lean` |  |
| `Obs2/Tau2Hist.lean` | `Obs2/Flow/Tau2Hist.lean` |  |
| `Obs2/TotalMu.lean` | `Obs2/Flow/TotalMu.lean` |  |
| `Obs2/VObs1.lean` | `Obs2/Flow/VObs1.lean` |  |
| `Obs2/VObs2.lean` | `Obs2/Flow/VObs2.lean` |  |
| `Obs2/VObsAB1.lean` | `Obs2/Flow/VObsAB1.lean` |  |
| `Obs2/VObsAB2.lean` | `Obs2/Flow/VObsAB2.lean` |  |
| `Obs2/VObsAB3.lean` | `Obs2/Flow/VObsAB3.lean` |  |
| `Obs2/VObsAB4.lean` | `Obs2/Flow/VObsAB4.lean` |  |
| `Obs2/VObsAB4X.lean` | `Obs2/Flow/VObsAB4X.lean` |  |
| `Obs2/WObs1.lean` | `Obs2/Est/WObs1.lean` |  |
| `Obs2/WObs2.lean` | `Obs2/Est/WObs2.lean` |  |
| `Obs2/WObs3.lean` | `Obs2/Est/WObs3.lean` |  |
| `Obs2/WObsAB.lean` | `Obs2/Est/WObsAB.lean` |  |
| `Obs2/WObsAB2.lean` | `Obs2/Est/WObsAB2.lean` |  |
| `Obs2/WObsU.lean` | `Obs2/Est/WObsU.lean` |  |
| `Obs2/Wick1.lean` | `Obs2/Flow/Wick1.lean` |  |
| `Obs2/Wick2.lean` | `Obs2/Flow/Wick2.lean` |  |
| `Obs2/WickPair.lean` | `Obs2/Flow/WickPair.lean` |  |
| `Obs2/WickTotal.lean` | `Obs2/Flow/WickTotal.lean` |  |
| `Obs2/WickV.lean` | `Obs2/Flow/WickV.lean` |  |
| `Obs2/WickVcoup.lean` | `Obs2/Flow/WickVcoup.lean` |  |

## PtCorr2

| old | new | |
|---|---|---|
| `PtCorr2/Bounds.lean` | `PtCorr2/Zero/Bounds.lean` |  |
| `PtCorr2/Chain.lean` | `PtCorr2/Zero/Chain.lean` |  |
| `PtCorr2/ChainFlow.lean` | `PtCorr2/Zero/ChainFlow.lean` |  |
| `PtCorr2/ChainHist.lean` | `PtCorr2/Zero/ChainHist.lean` |  |
| `PtCorr2/CoalRestartR.lean` | `PtCorr2/Restart/CoalRestartR.lean` |  |
| `PtCorr2/ConstSplitHist.lean` | `PtCorr2/Obs/ConstSplitHist.lean` |  |
| `PtCorr2/ContFx1.lean` | `PtCorr2/Cont/ContFx1.lean` |  |
| `PtCorr2/ContK2a.lean` | `PtCorr2/Cont/ContK2a.lean` |  |
| `PtCorr2/ContNa1.lean` | `PtCorr2/Cont/ContNa1.lean` |  |
| `PtCorr2/ContTop1.lean` | `PtCorr2/Cont/ContTop1.lean` |  |
| `PtCorr2/ContTop2.lean` | `PtCorr2/Cont/ContTop2.lean` |  |
| `PtCorr2/ContTop3.lean` | `PtCorr2/Cont/ContTop3.lean` |  |
| `PtCorr2/ContWire1.lean` | `PtCorr2/Cont/ContWire1.lean` |  |
| `PtCorr2/ContZab1.lean` | `PtCorr2/Cont/ContZab1.lean` |  |
| `PtCorr2/Coupling.lean` | `PtCorr2/Zero/Coupling.lean` |  |
| `PtCorr2/Dressing.lean` | `PtCorr2/Zero/Dressing.lean` |  |
| `PtCorr2/EpsFlow.lean` | `PtCorr2/Zero/EpsFlow.lean` |  |
| `PtCorr2/ExactHist.lean` | `PtCorr2/Zero/ExactHist.lean` |  |
| `PtCorr2/ExactStep.lean` | `PtCorr2/Zero/ExactStep.lean` |  |
| `PtCorr2/Final.lean` | `PtCorr2/Zero/Final.lean` |  |
| `PtCorr2/Flow.lean` | `PtCorr2/Zero/Flow.lean` |  |
| `PtCorr2/ForestNear.lean` | `PtCorr2/Zero/ForestNear.lean` |  |
| `PtCorr2/GamWKBd.lean` | `PtCorr2/Obs/GamWKBd.lean` |  |
| `PtCorr2/Glue.lean` | `PtCorr2/Zero/Glue.lean` |  |
| `PtCorr2/GradABHist1.lean` | `PtCorr2/Pair/GradABHist1.lean` |  |
| `PtCorr2/GradABHist2.lean` | `PtCorr2/Pair/GradABHist2.lean` |  |
| `PtCorr2/GradABHist3.lean` | `PtCorr2/Pair/GradABHist3.lean` |  |
| `PtCorr2/HistLink.lean` | `PtCorr2/Restart/HistLink.lean` |  |
| `PtCorr2/KObsEK.lean` | `PtCorr2/Obs/KObsEK.lean` |  |
| `PtCorr2/KObsHist.lean` | `PtCorr2/Obs/KObsHist.lean` |  |
| `PtCorr2/KObsHistAB.lean` | `PtCorr2/Pair/KObsHistAB.lean` |  |
| `PtCorr2/KObsStep.lean` | `PtCorr2/Obs/KObsStep.lean` |  |
| `PtCorr2/KObsStepAB.lean` | `PtCorr2/Pair/KObsStepAB.lean` |  |
| `PtCorr2/KObsStepU.lean` | `PtCorr2/Obs/KObsStepU.lean` |  |
| `PtCorr2/LastAB1.lean` | `PtCorr2/Last/LastAB1.lean` |  |
| `PtCorr2/LastAB2.lean` | `PtCorr2/Last/LastAB2.lean` |  |
| `PtCorr2/LastAB3.lean` | `PtCorr2/Last/LastAB3.lean` |  |
| `PtCorr2/LastAB4.lean` | `PtCorr2/Last/LastAB4.lean` |  |
| `PtCorr2/LastL1.lean` | `PtCorr2/Last/LastL1.lean` |  |
| `PtCorr2/LastObsA.lean` | `PtCorr2/Last/LastObsA.lean` |  |
| `PtCorr2/LastObsK1.lean` | `PtCorr2/Last/LastObsK1.lean` |  |
| `PtCorr2/LastObsK2.lean` | `PtCorr2/Last/LastObsK2.lean` |  |
| `PtCorr2/LastObsK3.lean` | `PtCorr2/Last/LastObsK3.lean` |  |
| `PtCorr2/LastObsK4.lean` | `PtCorr2/Last/LastObsK4.lean` |  |
| `PtCorr2/LastObsK5.lean` | `PtCorr2/Last/LastObsK5.lean` |  |
| `PtCorr2/LastObsK6.lean` | `PtCorr2/Last/LastObsK6.lean` |  |
| `PtCorr2/LastObsK7.lean` | `PtCorr2/Last/LastObsK7.lean` |  |
| `PtCorr2/LastOneTI.lean` | `PtCorr2/Last/LastOneTI.lean` |  |
| `PtCorr2/LinearHist.lean` | `PtCorr2/Obs/LinearHist.lean` |  |
| `PtCorr2/MemAB1.lean` | `PtCorr2/Pair/MemAB1.lean` |  |
| `PtCorr2/MemAB2.lean` | `PtCorr2/Pair/MemAB2.lean` |  |
| `PtCorr2/MuKHist.lean` | `PtCorr2/Obs/KObsEK.lean` | merged |
| `PtCorr2/ObsChain.lean` | `PtCorr2/Obs/ObsChain.lean` |  |
| `PtCorr2/ObsFlow.lean` | `PtCorr2/Obs/ObsFlow.lean` |  |
| `PtCorr2/ObsHist.lean` | `PtCorr2/Obs/ObsHist.lean` |  |
| `PtCorr2/ObsHist2.lean` | `PtCorr2/Obs/ObsHist2.lean` |  |
| `PtCorr2/ObsHistAnch.lean` | `PtCorr2/Pair/ObsHistAnch.lean` |  |
| `PtCorr2/ObsHistFrom.lean` | `PtCorr2/Obs/ObsHistFrom.lean` |  |
| `PtCorr2/ObsHistLast.lean` | `PtCorr2/Obs/ObsHistLast.lean` |  |
| `PtCorr2/ObsHistRel.lean` | `PtCorr2/Obs/ObsHistRel.lean` |  |
| `PtCorr2/ObsHistRelE.lean` | `PtCorr2/Obs/ObsHistRelE.lean` |  |
| `PtCorr2/ObsHistRelE2.lean` | `PtCorr2/Obs/ObsHistRelE2.lean` |  |
| `PtCorr2/ObsHistRelW.lean` | `PtCorr2/Obs/ObsHistRelW.lean` |  |
| `PtCorr2/ObsHistTop.lean` | `PtCorr2/Obs/ObsHistTop.lean` |  |
| `PtCorr2/ObsHistU.lean` | `PtCorr2/Obs/ObsHistU.lean` |  |
| `PtCorr2/ObsInit.lean` | `PtCorr2/Obs/ObsInit.lean` |  |
| `PtCorr2/ObsLoc.lean` | `PtCorr2/Obs/ObsLoc.lean` |  |
| `PtCorr2/ObsStep.lean` | `PtCorr2/Obs/ObsStep.lean` |  |
| `PtCorr2/ObsSym.lean` | `PtCorr2/Obs/ObsSym.lean` |  |
| `PtCorr2/ObsSymFrom.lean` | `PtCorr2/Obs/ObsSymFrom.lean` |  |
| `PtCorr2/ObsZero.lean` | `PtCorr2/Obs/ObsZero.lean` |  |
| `PtCorr2/OnePt.lean` | `PtCorr2/Zero/OnePt.lean` |  |
| `PtCorr2/OnePtFlow.lean` | `PtCorr2/Zero/OnePtFlow.lean` |  |
| `PtCorr2/OnePtWin.lean` | `PtCorr2/Zero/OnePtWin.lean` |  |
| `PtCorr2/PairAbove.lean` | `PtCorr2/Pair/PairAbove.lean` |  |
| `PtCorr2/PairChainAB.lean` | `PtCorr2/Pair/PairChainAB.lean` |  |
| `PtCorr2/PairDGeom.lean` | `PtCorr2/Pair/PairDGeom.lean` |  |
| `PtCorr2/PairDGeom2.lean` | `PtCorr2/Pair/PairDGeom2.lean` |  |
| `PtCorr2/PairDef5S.lean` | `PtCorr2/Pair/PairDef5S.lean` |  |
| `PtCorr2/PairEStep1.lean` | `PtCorr2/Pair/PairEStep1.lean` |  |
| `PtCorr2/PairEStep2.lean` | `PtCorr2/Pair/PairEStep2.lean` |  |
| `PtCorr2/PairESz1.lean` | `PtCorr2/Pair/PairESz1.lean` |  |
| `PtCorr2/PairESz2.lean` | `PtCorr2/Pair/PairESz2.lean` |  |
| `PtCorr2/PairInitAB.lean` | `PtCorr2/Pair/PairInitAB.lean` |  |
| `PtCorr2/PairInitAB2.lean` | `PtCorr2/Pair/PairInitAB2.lean` |  |
| `PtCorr2/PairInitU.lean` | `PtCorr2/Pair/PairInitU.lean` |  |
| `PtCorr2/PairLin1.lean` | `PtCorr2/Pair/PairLin1.lean` |  |
| `PtCorr2/PairLin2.lean` | `PtCorr2/Pair/PairLin2.lean` |  |
| `PtCorr2/PairRecAB.lean` | `PtCorr2/Pair/PairRecAB.lean` |  |
| `PtCorr2/PairReduce.lean` | `PtCorr2/Pair/PairReduce.lean` |  |
| `PtCorr2/PairReduceChain.lean` | `PtCorr2/Pair/PairReduceChain.lean` |  |
| `PtCorr2/PairSectHist.lean` | `PtCorr2/Pair/PairSectHist.lean` |  |
| `PtCorr2/PairSizesAB.lean` | `PtCorr2/Pair/PairSizesAB.lean` |  |
| `PtCorr2/PairVStep1.lean` | `PtCorr2/Pair/PairVStep1.lean` |  |
| `PtCorr2/PairVStep2.lean` | `PtCorr2/Pair/PairVStep2.lean` |  |
| `PtCorr2/PairVStep3.lean` | `PtCorr2/Pair/PairVStep3.lean` |  |
| `PtCorr2/PairVStep4.lean` | `PtCorr2/Pair/PairVStep4.lean` |  |
| `PtCorr2/PairZero.lean` | `PtCorr2/Pair/PairZero.lean` |  |
| `PtCorr2/ProdBd2Hist.lean` | `PtCorr2/Obs/ProdBd2Hist.lean` |  |
| `PtCorr2/ProdBd2Top.lean` | `PtCorr2/Obs/ProdBd2Top.lean` |  |
| `PtCorr2/ProdBdHist.lean` | `PtCorr2/Obs/ProdBdHist.lean` |  |
| `PtCorr2/ProdStep.lean` | `PtCorr2/Obs/ProdStep.lean` |  |
| `PtCorr2/RealStep.lean` | `PtCorr2/Zero/RealStep.lean` |  |
| `PtCorr2/RerepK.lean` | `PtCorr2/Restart/RerepK.lean` |  |
| `PtCorr2/RerepState.lean` | `PtCorr2/Restart/RerepState.lean` |  |
| `PtCorr2/RerepSym.lean` | `PtCorr2/Restart/RerepSym.lean` |  |
| `PtCorr2/RerepZ.lean` | `PtCorr2/Restart/RerepZ.lean` |  |
| `PtCorr2/Restart2D.lean` | `PtCorr2/Restart/Restart2D.lean` |  |
| `PtCorr2/Restart2Hist.lean` | `PtCorr2/Restart/Restart2Hist.lean` |  |
| `PtCorr2/Restart2Step.lean` | `PtCorr2/Restart/Restart2Step.lean` |  |
| `PtCorr2/Restart2Thm.lean` | `PtCorr2/Restart/Restart2Thm.lean` |  |
| `PtCorr2/Restart3a.lean` | `PtCorr2/Restart/Restart3a.lean` |  |
| `PtCorr2/Restart3b.lean` | `PtCorr2/Restart/Restart3b.lean` |  |
| `PtCorr2/RestartBulk.lean` | `PtCorr2/Restart/RestartBulk.lean` |  |
| `PtCorr2/RestartHist.lean` | `PtCorr2/Restart/RestartHist.lean` |  |
| `PtCorr2/RestartLoc.lean` | `PtCorr2/Restart/RestartLoc.lean` |  |
| `PtCorr2/RestartPairAB.lean` | `PtCorr2/Restart/RestartPairAB.lean` |  |
| `PtCorr2/RestartPairB.lean` | `PtCorr2/Restart/RestartPairB.lean` |  |
| `PtCorr2/RestartPairChain1.lean` | `PtCorr2/Restart/RestartPairChain1.lean` |  |
| `PtCorr2/RestartPairChain3.lean` | `PtCorr2/Restart/RestartPairChain3.lean` |  |
| `PtCorr2/RestartPairGam.lean` | `PtCorr2/Restart/RestartPairGam.lean` |  |
| `PtCorr2/RestartPairGamB.lean` | `PtCorr2/Restart/RestartPairGamB.lean` |  |
| `PtCorr2/RestartPairTop.lean` | `PtCorr2/Restart/RestartPairTop.lean` |  |
| `PtCorr2/RestartPairTopF1.lean` | `PtCorr2/Restart/RestartPairTopF1.lean` |  |
| `PtCorr2/RestartProd.lean` | `PtCorr2/Restart/RestartProd.lean` |  |
| `PtCorr2/RestartStep.lean` | `PtCorr2/Restart/RestartStep.lean` |  |
| `PtCorr2/RestartThm.lean` | `PtCorr2/Restart/RestartThm.lean` |  |
| `PtCorr2/Restrict.lean` | `PtCorr2/Zero/Restrict.lean` |  |
| `PtCorr2/SFirst1.lean` | `PtCorr2/Pair/SFirst1.lean` |  |
| `PtCorr2/SXOStepAB.lean` | `PtCorr2/Pair/SXOStepAB.lean` |  |
| `PtCorr2/SeedSplit.lean` | `PtCorr2/Pair/SeedSplit.lean` |  |
| `PtCorr2/SeedSplit2.lean` | `PtCorr2/Pair/SeedSplit2.lean` |  |
| `PtCorr2/ShareABHist1.lean` | `PtCorr2/Pair/ShareABHist1.lean` |  |
| `PtCorr2/ShareABHist2.lean` | `PtCorr2/Pair/ShareABHist2.lean` |  |
| `PtCorr2/Suscept2.lean` | `PtCorr2/Zero/Suscept2.lean` |  |
| `PtCorr2/TopCoal1.lean` | `PtCorr2/Last/TopCoal1.lean` |  |
| `PtCorr2/TopCoal2.lean` | `PtCorr2/Last/TopCoal2.lean` |  |
| `PtCorr2/TopCoal3.lean` | `PtCorr2/Last/TopCoal3.lean` |  |
| `PtCorr2/TwoPtGhost.lean` | `PtCorr2/Zero/TwoPtGhost.lean` |  |
| `PtCorr2/TwoPtRep.lean` | `PtCorr2/Zero/TwoPtRep.lean` |  |
| `PtCorr2/TwoPtZZ.lean` | `PtCorr2/Pair/TwoPtZZ.lean` |  |
| `PtCorr2/VObsStep.lean` | `PtCorr2/Obs/VObsStep.lean` |  |
| `PtCorr2/VObsStepAB1.lean` | `PtCorr2/Pair/VObsStepAB1.lean` |  |
| `PtCorr2/VObsStepAB2.lean` | `PtCorr2/Pair/VObsStepAB2.lean` |  |
| `PtCorr2/WObsStep.lean` | `PtCorr2/Obs/WObsStep.lean` |  |
| `PtCorr2/WObsStepAB.lean` | `PtCorr2/Pair/WObsStepAB.lean` |  |
| `PtCorr2/WObsStepAB2.lean` | `PtCorr2/Pair/KObsHistAB.lean` | merged |
| `PtCorr2/WObsStepU.lean` | `PtCorr2/Obs/WObsStepU.lean` |  |
| `PtCorr2/Ward2.lean` | `PtCorr2/Zero/Ward2.lean` |  |
| `PtCorr2/WardNeg1.lean` | `PtCorr2/Zero/WardNeg1.lean` |  |
| `PtCorr2/WardNeg2.lean` | `PtCorr2/Zero/WardNeg2.lean` |  |
| `PtCorr2/ZeroInit.lean` | `PtCorr2/Zero/ZeroInit.lean` |  |
| `PtCorr2/ZeroShift.lean` | `PtCorr2/Zero/ZeroShift.lean` |  |
| `PtCorr2/ZeroShiftDeriv.lean` | `PtCorr2/Zero/ZeroShiftDeriv.lean` |  |
| `PtCorr2/ZeroShiftHist.lean` | `PtCorr2/Zero/ZeroShiftHist.lean` |  |
| `PtCorr2/ZeroT.lean` | `PtCorr2/Zero/ZeroT.lean` |  |

## Spin2

| old | new | |
|---|---|---|
| `Spin2/AbwReq.lean` | `Spin2/Master/AbwReq.lean` |  |
| `Spin2/BetaLog.lean` | `Spin2/Multiscale/BetaLog.lean` |  |
| `Spin2/BetaThm.lean` | `Spin2/Multiscale/BetaThm.lean` |  |
| `Spin2/Case2.lean` | `Spin2/Case2/Case2.lean` |  |
| `Spin2/Case2Bd.lean` | `Spin2/Case2/Case2Bd.lean` |  |
| `Spin2/Case2Loop.lean` | `Spin2/Case2/Case2Loop.lean` |  |
| `Spin2/Case2Nu.lean` | `Spin2/Case2/Case2Nu.lean` |  |
| `Spin2/Case2Rel.lean` | `Spin2/Case2/Case2Rel.lean` |  |
| `Spin2/Case2RelPair.lean` | `Spin2/Case2/Case2RelPairThm.lean` | merged |
| `Spin2/Case2RelPairL.lean` | `Spin2/Case2/Case2RelPairL.lean` |  |
| `Spin2/Case2RelPairLI.lean` | `Spin2/Case2/Case2RelPairLI.lean` |  |
| `Spin2/Case2RelPairLT.lean` | `Spin2/Case2/Case2RelPairLT.lean` |  |
| `Spin2/Case2RelPairThm.lean` | `Spin2/Case2/Case2RelPairThm.lean` |  |
| `Spin2/Case2Thm.lean` | `Spin2/Case2/Case2Thm.lean` |  |
| `Spin2/Case2Top.lean` | `Spin2/Case2/Case2Top.lean` |  |
| `Spin2/Case2TopMaster.lean` | `Spin2/Case2/Case2TopMaster.lean` |  |
| `Spin2/Conn.lean` | `Spin2/Multiscale/Conn.lean` |  |
| `Spin2/ConnSym.lean` | `Spin2/Multiscale/ConnSym.lean` |  |
| `Spin2/ContArt1.lean` | `Spin2/Cont/ContArt1.lean` |  |
| `Spin2/ContArt2.lean` | `Spin2/Cont/ContArt2.lean` |  |
| `Spin2/ContArt3.lean` | `Spin2/Cont/ContArt3.lean` |  |
| `Spin2/ContArt4.lean` | `Spin2/Cont/ContArt4.lean` |  |
| `Spin2/ContBound.lean` | `Spin2/Cont/ContLimit1.lean` | merged |
| `Spin2/ContDiff.lean` | `Spin2/Cont/ContDiff.lean` |  |
| `Spin2/ContDiff2.lean` | `Spin2/Cont/ContDiff2.lean` |  |
| `Spin2/ContDiff3.lean` | `Spin2/Cont/ContDiff3.lean` |  |
| `Spin2/ContDiff4a.lean` | `Spin2/Cont/ContDiff4a.lean` |  |
| `Spin2/ContDiff4b.lean` | `Spin2/Cont/ContDiff4b.lean` |  |
| `Spin2/ContDiff4c.lean` | `Spin2/Cont/ContDiff4c.lean` |  |
| `Spin2/ContDiffD1.lean` | `Spin2/Cont/ContDiffD1.lean` |  |
| `Spin2/ContDiffD2.lean` | `Spin2/Cont/ContDiffD2.lean` |  |
| `Spin2/ContDiffD3.lean` | `Spin2/Cont/ContDiffD3.lean` |  |
| `Spin2/ContEq1.lean` | `Spin2/Cont/ContEq1.lean` |  |
| `Spin2/ContEq2.lean` | `Spin2/Cont/ContEq2.lean` |  |
| `Spin2/ContEq3.lean` | `Spin2/Cont/ContEq3.lean` |  |
| `Spin2/ContEqC1.lean` | `Spin2/Cont/ContEqC1.lean` |  |
| `Spin2/ContEqC2.lean` | `Spin2/Cont/ContEqC2.lean` |  |
| `Spin2/ContEqC3.lean` | `Spin2/Cont/ContEqC3.lean` |  |
| `Spin2/ContEqC4.lean` | `Spin2/Cont/ContEqC4.lean` |  |
| `Spin2/ContEqC5.lean` | `Spin2/Cont/ContEqC5.lean` |  |
| `Spin2/ContEqC6.lean` | `Spin2/Cont/ContEqC6.lean` |  |
| `Spin2/ContEqF1.lean` | `Spin2/Cont/ContEqF1.lean` |  |
| `Spin2/ContEqF2.lean` | `Spin2/Cont/ContEqF2.lean` |  |
| `Spin2/ContEqF3.lean` | `Spin2/Cont/ContEqF3.lean` |  |
| `Spin2/ContEqF4.lean` | `Spin2/Cont/ContEqF4.lean` |  |
| `Spin2/ContEqF5.lean` | `Spin2/Cont/ContEqF5.lean` |  |
| `Spin2/ContEqS0.lean` | `Spin2/Cont/ContEqS0.lean` |  |
| `Spin2/ContEqS1.lean` | `Spin2/Cont/ContEqS1.lean` |  |
| `Spin2/ContEqS2.lean` | `Spin2/Cont/ContEqS2.lean` |  |
| `Spin2/ContEqS3.lean` | `Spin2/Cont/ContEqS3.lean` |  |
| `Spin2/ContEqS4.lean` | `Spin2/Cont/ContEqS4.lean` |  |
| `Spin2/ContEqS5.lean` | `Spin2/Cont/ContEqS5.lean` |  |
| `Spin2/ContEqS6.lean` | `Spin2/Cont/ContEqS6.lean` |  |
| `Spin2/ContEqS7.lean` | `Spin2/Cont/ContEqS7.lean` |  |
| `Spin2/ContEqS8.lean` | `Spin2/Cont/ContEqS8.lean` |  |
| `Spin2/ContFin1.lean` | `Spin2/Cont/ContFin1.lean` |  |
| `Spin2/ContFin2.lean` | `Spin2/Cont/ContFin2.lean` |  |
| `Spin2/ContFx1.lean` | `Spin2/Cont/ContFx1.lean` |  |
| `Spin2/ContFx2a.lean` | `Spin2/Cont/ContFx2a.lean` |  |
| `Spin2/ContFx2b.lean` | `Spin2/Cont/ContFx2b.lean` |  |
| `Spin2/ContFx2c.lean` | `Spin2/Cont/ContFx2c.lean` |  |
| `Spin2/ContFx2d.lean` | `Spin2/Cont/ContFx2d.lean` |  |
| `Spin2/ContFx2e.lean` | `Spin2/Cont/ContFx2e.lean` |  |
| `Spin2/ContFx2f.lean` | `Spin2/Cont/ContFx2f.lean` |  |
| `Spin2/ContFx3a.lean` | `Spin2/Cont/ContFx3a.lean` |  |
| `Spin2/ContFx3b.lean` | `Spin2/Cont/ContFx3b.lean` |  |
| `Spin2/ContFx4a.lean` | `Spin2/Cont/ContFx4a.lean` |  |
| `Spin2/ContFx4b.lean` | `Spin2/Cont/ContFx4b.lean` |  |
| `Spin2/ContFx5a.lean` | `Spin2/Cont/ContFx5a.lean` |  |
| `Spin2/ContFx5b.lean` | `Spin2/Cont/ContFx5b.lean` |  |
| `Spin2/ContK2a.lean` | `Spin2/Cont/ContK2a.lean` |  |
| `Spin2/ContK2b.lean` | `Spin2/Cont/ContK2b.lean` |  |
| `Spin2/ContK2c.lean` | `Spin2/Cont/ContK2c.lean` |  |
| `Spin2/ContK2d.lean` | `Spin2/Cont/ContK2d.lean` |  |
| `Spin2/ContK2e.lean` | `Spin2/Cont/ContK2e.lean` |  |
| `Spin2/ContLimit.lean` | `Spin2/Cont/ContLimit.lean` |  |
| `Spin2/ContLimit1.lean` | `Spin2/Cont/ContLimit1.lean` |  |
| `Spin2/ContNa1.lean` | `Spin2/Cont/ContNa1.lean` |  |
| `Spin2/ContNa2.lean` | `Spin2/Cont/ContNa2.lean` |  |
| `Spin2/ContNa3.lean` | `Spin2/Cont/ContNa3.lean` |  |
| `Spin2/ContNa4.lean` | `Spin2/Cont/ContNa4.lean` |  |
| `Spin2/ContNa5.lean` | `Spin2/Cont/ContNa5.lean` |  |
| `Spin2/ContNa6.lean` | `Spin2/Cont/ContNa6.lean` |  |
| `Spin2/ContNa7.lean` | `Spin2/Cont/ContNa7.lean` |  |
| `Spin2/ContNb1.lean` | `Spin2/Cont/ContNb1.lean` |  |
| `Spin2/ContNb2.lean` | `Spin2/Cont/ContNb2.lean` |  |
| `Spin2/ContNb3.lean` | `Spin2/Cont/ContNb3.lean` |  |
| `Spin2/ContNb4.lean` | `Spin2/Cont/ContNb4.lean` |  |
| `Spin2/ContNb5.lean` | `Spin2/Cont/ContNb5.lean` |  |
| `Spin2/ContNb6.lean` | `Spin2/Cont/ContNb6.lean` |  |
| `Spin2/ContNb7.lean` | `Spin2/Cont/ContNb7.lean` |  |
| `Spin2/ContNb8.lean` | `Spin2/Cont/ContNb8.lean` |  |
| `Spin2/ContNb9.lean` | `Spin2/Cont/ContNb9.lean` |  |
| `Spin2/ContScaleM.lean` | `Spin2/Cont/ContScaleM.lean` |  |
| `Spin2/ContShift.lean` | `Spin2/Cont/ContShift.lean` |  |
| `Spin2/ContShort.lean` | `Spin2/Cont/ContShort.lean` |  |
| `Spin2/ContShortX.lean` | `Spin2/Cont/ContShortX.lean` |  |
| `Spin2/ContTheta.lean` | `Spin2/Cont/ContTheta.lean` |  |
| `Spin2/ContTop1.lean` | `Spin2/Cont/ContTop1.lean` |  |
| `Spin2/ContTop2.lean` | `Spin2/Cont/ContTop2.lean` |  |
| `Spin2/ContTop3.lean` | `Spin2/Cont/ContTop3.lean` |  |
| `Spin2/ContTop4.lean` | `Spin2/Cont/ContTop4.lean` |  |
| `Spin2/ContTop5.lean` | `Spin2/Cont/ContTop5.lean` |  |
| `Spin2/ContTop6.lean` | `Spin2/Cont/ContTop6.lean` |  |
| `Spin2/ContTop7.lean` | `Spin2/Cont/ContTop7.lean` |  |
| `Spin2/ContTop8.lean` | `Spin2/Cont/ContTop8.lean` |  |
| `Spin2/ContWindow.lean` | `Spin2/Cont/ContWindow.lean` |  |
| `Spin2/ContWindowPure.lean` | `Spin2/Cont/ContWindowPure.lean` |  |
| `Spin2/ContWindowX.lean` | `Spin2/Cont/ContWindowX.lean` |  |
| `Spin2/ContWire1.lean` | `Spin2/Cont/ContWire1.lean` |  |
| `Spin2/ContWire2.lean` | `Spin2/Cont/ContWire2.lean` |  |
| `Spin2/ContWire3.lean` | `Spin2/Cont/ContWire3.lean` |  |
| `Spin2/ContWire4.lean` | `Spin2/Cont/ContWire4.lean` |  |
| `Spin2/ContWire5.lean` | `Spin2/Cont/ContWire5.lean` |  |
| `Spin2/ContWire6.lean` | `Spin2/Cont/ContWire6.lean` |  |
| `Spin2/ContWire7.lean` | `Spin2/Cont/ContWire7.lean` |  |
| `Spin2/ContWire8.lean` | `Spin2/Cont/ContWire8.lean` |  |
| `Spin2/ContWire9.lean` | `Spin2/Cont/ContWire9.lean` |  |
| `Spin2/ContZab1.lean` | `Spin2/Cont/ContZab1.lean` |  |
| `Spin2/ContZab2.lean` | `Spin2/Cont/ContZab2.lean` |  |
| `Spin2/ContZab3.lean` | `Spin2/Cont/ContZab3.lean` |  |
| `Spin2/ContZab4.lean` | `Spin2/Cont/ContZab4.lean` |  |
| `Spin2/ContZab5.lean` | `Spin2/Cont/ContZab5.lean` |  |
| `Spin2/FinalAll.lean` | `Spin2/Final/FinalAll.lean` |  |
| `Spin2/FinalAllX.lean` | `Spin2/Final/FinalAllX.lean` |  |
| `Spin2/FinalBeta.lean` | `Spin2/Final/FinalBeta.lean` |  |
| `Spin2/FinalMultiscale.lean` | `Spin2/Final/FinalMultiscale.lean` |  |
| `Spin2/FinalNF.lean` | `Spin2/Final/FinalNF.lean` |  |
| `Spin2/FinalTheorem.lean` | `Spin2/Final/FinalTheorem.lean` |  |
| `Spin2/FinalTop.lean` | `Spin2/Final/FinalTop.lean` |  |
| `Spin2/FinalTop1.lean` | `Spin2/Final/FinalTop1.lean` |  |
| `Spin2/FinalWire.lean` | `Spin2/Final/FinalWire.lean` |  |
| `Spin2/Flow.lean` | `Spin2/Multiscale/Flow.lean` |  |
| `Spin2/GamBulk.lean` | `Spin2/Gam/GamBulk.lean` |  |
| `Spin2/GamBulk2.lean` | `Spin2/Gam/GamBulk2.lean` |  |
| `Spin2/GamFormB.lean` | `Spin2/Gam/GamFormB.lean` |  |
| `Spin2/GamLast.lean` | `Spin2/Gam/GamLast.lean` |  |
| `Spin2/GamLastBd.lean` | `Spin2/Gam/GamLastBd.lean` |  |
| `Spin2/GamRem.lean` | `Spin2/Gam/GamRem.lean` |  |
| `Spin2/GamRemLast.lean` | `Spin2/Gam/GamRemLast.lean` |  |
| `Spin2/GamTop.lean` | `Spin2/Gam/GamTop.lean` |  |
| `Spin2/GamTopB.lean` | `Spin2/Gam/GamTopB.lean` |  |
| `Spin2/GamTopFull.lean` | `Spin2/Gam/GamTopFull.lean` |  |
| `Spin2/GamTopFullL.lean` | `Spin2/Gam/GamTopFullL.lean` |  |
| `Spin2/Gamma.lean` | `Spin2/Multiscale/Gamma.lean` |  |
| `Spin2/H0Factors.lean` | `Spin2/H0/H0Factors.lean` |  |
| `Spin2/H0MassFlow.lean` | `Spin2/H0/H0MassFlow.lean` |  |
| `Spin2/H0OnePt.lean` | `Spin2/H0/H0OnePt.lean` |  |
| `Spin2/H0OnePtM.lean` | `Spin2/H0/H0OnePtM.lean` |  |
| `Spin2/H0OnePtW.lean` | `Spin2/H0/H0OnePtW.lean` |  |
| `Spin2/H0SlackBd.lean` | `Spin2/H0/H0SlackBd.lean` |  |
| `Spin2/H0SlackReq.lean` | `Spin2/H0/H0SlackReq.lean` |  |
| `Spin2/H0WinConcl.lean` | `Spin2/H0/H0WinConcl.lean` |  |
| `Spin2/H0Window.lean` | `Spin2/H0/H0Window.lean` |  |
| `Spin2/LamFlow.lean` | `Spin2/Multiscale/LamFlow.lean` |  |
| `Spin2/LastKRem1.lean` | `Spin2/Gam/LastKRem1.lean` |  |
| `Spin2/LastKRemM.lean` | `Spin2/Gam/LastL1M.lean` | merged |
| `Spin2/LastL1M.lean` | `Spin2/Gam/LastL1M.lean` |  |
| `Spin2/LastOneM.lean` | `Spin2/Gam/LastOneM.lean` |  |
| `Spin2/LastOneRem.lean` | `Spin2/Gam/LastOneRem.lean` |  |
| `Spin2/MacroA.lean` | `Spin2/Macro/MacroA.lean` |  |
| `Spin2/MacroB.lean` | `Spin2/Macro/MacroB.lean` |  |
| `Spin2/Master.lean` | `Spin2/Master/Master.lean` |  |
| `Spin2/MasterAllAbw.lean` | `Spin2/Master/MasterAllAbw.lean` |  |
| `Spin2/MasterAllBase.lean` | `Spin2/Master/MasterAllBase.lean` |  |
| `Spin2/MasterAllConst.lean` | `Spin2/Master/MasterAllConst.lean` |  |
| `Spin2/MasterAllCore.lean` | `Spin2/Master/MasterAllCore.lean` |  |
| `Spin2/MasterAllFacts.lean` | `Spin2/Master/MasterAllFacts.lean` |  |
| `Spin2/MasterAllFactsD.lean` | `Spin2/Master/MasterAllFactsD.lean` |  |
| `Spin2/MasterAllGB.lean` | `Spin2/Master/MasterAllGB.lean` |  |
| `Spin2/MasterAllLastK.lean` | `Spin2/Master/MasterAllLastK.lean` |  |
| `Spin2/MasterAllLastL1.lean` | `Spin2/Master/MasterAllLastL1.lean` |  |
| `Spin2/MasterAllLastO.lean` | `Spin2/Master/MasterAllLastO.lean` |  |
| `Spin2/MasterAllLastW.lean` | `Spin2/Master/MasterAllLastW.lean` |  |
| `Spin2/MasterAllLoop.lean` | `Spin2/Master/MasterAllLoop.lean` |  |
| `Spin2/MasterAllPairU.lean` | `Spin2/Master/MasterAllPairU.lean` |  |
| `Spin2/MasterAllPairW.lean` | `Spin2/Master/MasterAllPairW.lean` |  |
| `Spin2/MasterAllRel.lean` | `Spin2/Master/MasterAllRel.lean` |  |
| `Spin2/MasterAllTop.lean` | `Spin2/Master/MasterAllTop.lean` |  |
| `Spin2/MasterAllVStep.lean` | `Spin2/Master/MasterAllVStep.lean` |  |
| `Spin2/MasterAllWK.lean` | `Spin2/Master/MasterAllWK.lean` |  |
| `Spin2/MasterH0.lean` | `Spin2/H0/MasterH0.lean` |  |
| `Spin2/MasterH0Ends.lean` | `Spin2/H0/MasterH0Ends.lean` |  |
| `Spin2/MasterH0Multi.lean` | `Spin2/H0/MasterH0Multi.lean` |  |
| `Spin2/MasterH0OnePt.lean` | `Spin2/H0/MasterH0OnePt.lean` |  |
| `Spin2/MasterH0Pair.lean` | `Spin2/H0/MasterH0Pair.lean` |  |
| `Spin2/MasterH0Shoot.lean` | `Spin2/H0/MasterH0Shoot.lean` |  |
| `Spin2/MasterH0Slack.lean` | `Spin2/H0/MasterH0Slack.lean` |  |
| `Spin2/MasterL.lean` | `Spin2/Master/MasterL.lean` |  |
| `Spin2/MasterVHist.lean` | `Spin2/Master/MasterVHist.lean` |  |
| `Spin2/Multiscale.lean` | `Spin2/Multiscale/Multiscale.lean` |  |
| `Spin2/ObsRel.lean` | `Spin2/Multiscale/ObsRel.lean` |  |
| `Spin2/PairAbove.lean` | `Spin2/Pair/PairAbove.lean` |  |
| `Spin2/PairCst.lean` | `Spin2/Pair/PairCst.lean` |  |
| `Spin2/PairDef5D.lean` | `Spin2/Pair/PairDef5D.lean` |  |
| `Spin2/PairDef5a.lean` | `Spin2/Pair/PairDef5a.lean` |  |
| `Spin2/PairDef5b.lean` | `Spin2/Pair/PairDef5b.lean` |  |
| `Spin2/PairDef5c.lean` | `Spin2/Pair/PairDef5c.lean` |  |
| `Spin2/PairDef5d.lean` | `Spin2/Pair/PairDef5d.lean` |  |
| `Spin2/PairDef5e.lean` | `Spin2/Pair/PairDef5e.lean` |  |
| `Spin2/PairDef5eD.lean` | `Spin2/Pair/PairDef5eD.lean` |  |
| `Spin2/PairDef6a.lean` | `Spin2/Pair/PairDef6a.lean` |  |
| `Spin2/PairDef6b.lean` | `Spin2/Pair/PairDef6b.lean` |  |
| `Spin2/PairDef6bD.lean` | `Spin2/Pair/PairDef6bD.lean` |  |
| `Spin2/PairDefAB.lean` | `Spin2/Pair/PairDefAB.lean` |  |
| `Spin2/PairDefAB2.lean` | `Spin2/Pair/PairDefAB2.lean` |  |
| `Spin2/PairDefAB4.lean` | `Spin2/Pair/PairDefAB4.lean` |  |
| `Spin2/PairDefSeed.lean` | `Spin2/Pair/PairDefSeed.lean` |  |
| `Spin2/PairEReq.lean` | `Spin2/Pair/PairEReq.lean` |  |
| `Spin2/PairEStep1.lean` | `Spin2/Pair/PairEStep1.lean` |  |
| `Spin2/PairEStep2.lean` | `Spin2/Pair/PairEStep2.lean` |  |
| `Spin2/PairEStep3.lean` | `Spin2/Pair/PairEStep3.lean` |  |
| `Spin2/PairEStep4.lean` | `Spin2/Pair/PairEStep4.lean` |  |
| `Spin2/PairESz2.lean` | `Spin2/Pair/PairESz2.lean` |  |
| `Spin2/PairESz3.lean` | `Spin2/Pair/PairESz3.lean` |  |
| `Spin2/PairESz4.lean` | `Spin2/Pair/PairESz4.lean` |  |
| `Spin2/PairESz5.lean` | `Spin2/Pair/PairESz5.lean` |  |
| `Spin2/PairESz6.lean` | `Spin2/Pair/PairESz6.lean` |  |
| `Spin2/PairESz7.lean` | `Spin2/Pair/PairESz7.lean` |  |
| `Spin2/PairESz8.lean` | `Spin2/Pair/PairESz8.lean` |  |
| `Spin2/PairErrAB.lean` | `Spin2/Pair/PairErrAB.lean` |  |
| `Spin2/PairErrAB3.lean` | `Spin2/Pair/PairErrAB3.lean` |  |
| `Spin2/PairFinal.lean` | `Spin2/Pair/PairFinal.lean` |  |
| `Spin2/PairFinal4.lean` | `Spin2/Pair/PairFinal4.lean` |  |
| `Spin2/PairFinal5.lean` | `Spin2/Pair/PairFinal5.lean` |  |
| `Spin2/PairFinal6.lean` | `Spin2/Pair/PairFinal6.lean` |  |
| `Spin2/PairInitReq.lean` | `Spin2/Pair/PairInitReq.lean` |  |
| `Spin2/PairInitSizes.lean` | `Spin2/Pair/PairInitSizes.lean` |  |
| `Spin2/PairInitW.lean` | `Spin2/Pair/PairInitW.lean` |  |
| `Spin2/PairJoint2.lean` | `Spin2/Pair/PairJoint2.lean` |  |
| `Spin2/PairJoint3.lean` | `Spin2/Pair/PairJoint3.lean` |  |
| `Spin2/PairJoint4.lean` | `Spin2/Pair/PairJoint4.lean` |  |
| `Spin2/PairJoint6Def.lean` | `Spin2/Pair/PairJoint6Def.lean` |  |
| `Spin2/PairLin1.lean` | `Spin2/Pair/PairLin1.lean` |  |
| `Spin2/PairLin2.lean` | `Spin2/Pair/PairLin2.lean` |  |
| `Spin2/PairLin3.lean` | `Spin2/Pair/PairLin3.lean` |  |
| `Spin2/PairLin4.lean` | `Spin2/Pair/PairLin4.lean` |  |
| `Spin2/PairLin5.lean` | `Spin2/Pair/PairLin5.lean` |  |
| `Spin2/PairLin5b.lean` | `Spin2/Pair/PairLin5b.lean` |  |
| `Spin2/PairLoop.lean` | `Spin2/Pair/PairLoop.lean` |  |
| `Spin2/PairLoop2.lean` | `Spin2/Pair/PairLoop2.lean` |  |
| `Spin2/PairLoop3.lean` | `Spin2/Pair/PairLoop3.lean` |  |
| `Spin2/PairLoop4.lean` | `Spin2/Pair/PairLoop4.lean` |  |
| `Spin2/PairLoop5.lean` | `Spin2/Pair/PairLoop5.lean` |  |
| `Spin2/PairLoop6D.lean` | `Spin2/Pair/PairLoop6D.lean` |  |
| `Spin2/PairLoop6a.lean` | `Spin2/Pair/PairLoop6a.lean` |  |
| `Spin2/PairLoop6b.lean` | `Spin2/Pair/PairLoop6b.lean` |  |
| `Spin2/PairLoop6c.lean` | `Spin2/Pair/PairLoop6c.lean` |  |
| `Spin2/PairLoop6d.lean` | `Spin2/Pair/PairLoop6d.lean` |  |
| `Spin2/PairLoop6e.lean` | `Spin2/Pair/PairLoop6e.lean` |  |
| `Spin2/PairLoop6f.lean` | `Spin2/Pair/PairLoop6f.lean` |  |
| `Spin2/PairLoop6g.lean` | `Spin2/Pair/PairLoop6g.lean` |  |
| `Spin2/PairPR5.lean` | `Spin2/Pair/PairPR5.lean` |  |
| `Spin2/PairPR5b.lean` | `Spin2/Pair/PairPR5b.lean` |  |
| `Spin2/PairPR5d.lean` | `Spin2/Pair/PairPR5d.lean` |  |
| `Spin2/PairPR6.lean` | `Spin2/Pair/PairPR6.lean` |  |
| `Spin2/PairRed.lean` | `Spin2/Pair/PairRed.lean` |  |
| `Spin2/PairRed2.lean` | `Spin2/Pair/PairRed2.lean` |  |
| `Spin2/PairRed3.lean` | `Spin2/Pair/PairRed3.lean` |  |
| `Spin2/PairSect.lean` | `Spin2/Pair/PairSect.lean` |  |
| `Spin2/PairSeedW.lean` | `Spin2/Pair/PairSeedW.lean` |  |
| `Spin2/PairShareAB1.lean` | `Spin2/Pair/PairShareAB1.lean` |  |
| `Spin2/PairTop1.lean` | `Spin2/Pair/PairTop1.lean` |  |
| `Spin2/PairTop2.lean` | `Spin2/Pair/PairTop2.lean` |  |
| `Spin2/PairTop3.lean` | `Spin2/Pair/PairTop3.lean` |  |
| `Spin2/PairTop4.lean` | `Spin2/Pair/PairTop4.lean` |  |
| `Spin2/PairTop5.lean` | `Spin2/Pair/PairTop5.lean` |  |
| `Spin2/PairTop6.lean` | `Spin2/Pair/PairTop6.lean` |  |
| `Spin2/PairTopSeed1.lean` | `Spin2/Pair/PairTopSeed1.lean` |  |
| `Spin2/PairTopSeed2.lean` | `Spin2/Pair/PairTopSeed2.lean` |  |
| `Spin2/PairTopSeed3.lean` | `Spin2/Pair/PairTopSeed3.lean` |  |
| `Spin2/PairUnit.lean` | `Spin2/Pair/PairUnit.lean` |  |
| `Spin2/PairVReq.lean` | `Spin2/Pair/PairVReq.lean` |  |
| `Spin2/PairVStep1.lean` | `Spin2/Pair/PairVStep1.lean` |  |
| `Spin2/PairZeroAB1.lean` | `Spin2/Pair/PairZeroAB1.lean` |  |
| `Spin2/PairZeroAB2.lean` | `Spin2/Pair/PairZeroAB2.lean` |  |
| `Spin2/PairZeroAB3.lean` | `Spin2/Pair/PairZeroAB3.lean` |  |
| `Spin2/PairZeroAB4.lean` | `Spin2/Pair/PairZeroAB4.lean` |  |
| `Spin2/RGInH.lean` | `Spin2/Multiscale/RGInH.lean` |  |
| `Spin2/Restart2DMaster.lean` | `Spin2/Restart/Restart2DMaster.lean` |  |
| `Spin2/Restart2Lin.lean` | `Spin2/Restart/Restart2Lin.lean` |  |
| `Spin2/Restart2Master.lean` | `Spin2/Restart/Restart2Master.lean` |  |
| `Spin2/RestartMaster.lean` | `Spin2/Restart/RestartMaster.lean` |  |
| `Spin2/RestartPairChain1.lean` | `Spin2/Restart/RestartPairChain1.lean` |  |
| `Spin2/RestartPairChain10.lean` | `Spin2/Restart/RestartPairChain10.lean` |  |
| `Spin2/RestartPairChain11.lean` | `Spin2/Restart/RestartPairChain11.lean` |  |
| `Spin2/RestartPairChain12.lean` | `Spin2/Restart/RestartPairChain12.lean` |  |
| `Spin2/RestartPairChain2.lean` | `Spin2/Restart/RestartPairChain2.lean` |  |
| `Spin2/RestartPairChain3.lean` | `Spin2/Restart/RestartPairChain3.lean` |  |
| `Spin2/RestartPairChain4.lean` | `Spin2/Restart/RestartPairChain4.lean` |  |
| `Spin2/RestartPairChain5.lean` | `Spin2/Restart/RestartPairChain5.lean` |  |
| `Spin2/RestartPairChain6.lean` | `Spin2/Restart/RestartPairChain6.lean` |  |
| `Spin2/RestartPairChain7.lean` | `Spin2/Restart/RestartPairChain7.lean` |  |
| `Spin2/RestartPairChain8.lean` | `Spin2/Restart/RestartPairChain8.lean` |  |
| `Spin2/RestartPairChain9.lean` | `Spin2/Restart/RestartPairChain9.lean` |  |
| `Spin2/RestartPairGamC.lean` | `Spin2/Restart/RestartPairTopF1.lean` | merged |
| `Spin2/RestartPairSeed.lean` | `Spin2/Restart/RestartPairSeed.lean` |  |
| `Spin2/RestartPairTop1.lean` | `Spin2/Restart/RestartPairTop1.lean` |  |
| `Spin2/RestartPairTop2.lean` | `Spin2/Restart/RestartPairTop2.lean` |  |
| `Spin2/RestartPairTopF1.lean` | `Spin2/Restart/RestartPairTopF1.lean` |  |
| `Spin2/RestartPairTopF2.lean` | `Spin2/Restart/RestartPairTopF2.lean` |  |
| `Spin2/Sum.lean` | `Spin2/Multiscale/Sum.lean` |  |
| `Spin2/Thm.lean` | `Spin2/Multiscale/Thm.lean` |  |
| `Spin2/TwoPtNear.lean` | `Spin2/Multiscale/TwoPtNear.lean` |  |
| `Spin2/TwoPtSq.lean` | `Spin2/Multiscale/TwoPtSq.lean` |  |
| `Spin2/ZBelow.lean` | `Spin2/Multiscale/ZBelow.lean` |  |
| `Spin2/ZBelow2.lean` | `Spin2/Multiscale/ZBelow2.lean` |  |
| `Spin2/ZBelow3.lean` | `Spin2/Multiscale/ZBelow3.lean` |  |
| `Spin2/ZeroNorm.lean` | `Spin2/Pair/ZeroNorm.lean` |  |
| `Spin2/ZeroNormA.lean` | `Spin2/Pair/ZeroNormA.lean` |  |

# File moves, grouping into `H02RG/` and `H02UV/` (2026-10-26)

The `d ≥ 3` and `d = 2` libraries were moved into two group directories. Library names, module
names and declaration names did not change: the moved libraries have `srcDir = "H02RG"` resp.
`srcDir = "H02UV"` in their `[[lean_lib]]` entry of `lakefile.toml`, so for example
`import Step2.Flow.FlowThm` is the file `H02UV/Step2/Flow/FlowThm.lean`. The paths in the tables
above are relative to the library's source directory; prefix them as below to get the current file.

| old | new |
|---|---|
| `Step.lean`, `Step/` | `H02RG/Step.lean`, `H02RG/Step/` |
| `Flow.lean`, `Flow/` | `H02RG/Flow.lean`, `H02RG/Flow/` |
| `Suscept.lean`, `Suscept/` | `H02RG/Suscept.lean`, `H02RG/Suscept/` |
| `Obs.lean`, `Obs/` | `H02RG/Obs.lean`, `H02RG/Obs/` |
| `PtCorr.lean`, `PtCorr/` | `H02RG/PtCorr.lean`, `H02RG/PtCorr/` |
| `Psi4.lean`, `Psi4/` | `H02RG/Psi4.lean`, `H02RG/Psi4/` |
| `Ward.lean`, `Ward/` | `H02RG/Ward.lean`, `H02RG/Ward/` |
| `Step2.lean`, `Step2/` | `H02UV/Step2.lean`, `H02UV/Step2/` |
| `Flow2.lean`, `Flow2/` | `H02UV/Flow2.lean`, `H02UV/Flow2/` |
| `Obs2.lean`, `Obs2/` | `H02UV/Obs2.lean`, `H02UV/Obs2/` |
| `PtCorr2.lean`, `PtCorr2/` | `H02UV/PtCorr2.lean`, `H02UV/PtCorr2/` |
| `Spin2.lean`, `Spin2/` | `H02UV/Spin2.lean`, `H02UV/Spin2/` |
| `Cont.lean`, `Cont/` | `Cont.lean`, `Cont/` |

Unchanged (top level): `H02`, `Grassmann`, `Loc`, `FRD`, `DressedFRD`, `Audit/`.

# Declaration moves, `flow_master` (2026-10-26)

Two new files in `H02UV/Step2/Flow/`: `FlowBase.lean` (elementary helpers) and `FlowMaster.lean`
(the master theorem `flow_master` of the flow-theorem chain). Declarations moved there, with names
and statements unchanged (module `Step2.Flow.X` = file `H02UV/Step2/Flow/X.lean`):

| declaration | old module | new module |
|---|---|---|
| `ev_small`, `ev_lin`, `cZ_congr`, `cV_congr`, `cW_congr`, `cR_congr`, `cE_congr`, `cB_congr`, `cF2_congr`, `kap1_le_half`, `kap1_nonneg`, `betaL` | `Step2.Flow.FlowThm` | `Step2.Flow.FlowBase` |
| `msq_horizon`, `exists_lost_scales`, `mass_of_horizon` | `Step2.Flow.FlowHorizon` | `Step2.Flow.FlowBase` |
| `msq_j2`, `msq_j4`, `heA1_of` | `Step2.Flow.FlowHor2Thm` | `Step2.Flow.FlowBase` |
| `G_eq_kern`, `XG_value_hist` | `Step2.Flow.ZetaSharpHypX` | `Step2.Flow.FlowMaster` |
| `pTwo`, `bMu`, `bZe`, `bWz`, `kFin`, `BandF1` | `Step2.Flow.FlowComplete2Hyp` | `Step2.Flow.FlowMaster` |
| `inDh_rg_of_D` | `Step2.Flow.FlowMasterHypLZ` | `Step2.Flow.FlowMaster` |

All `Step2.*` names are `Step2.<name>`. Import changes: `Step2.Last.FlowGlueLast` and
`Step2.Flow.ZetaSharp5` import `FlowBase` instead of `FlowThm`; `Step2.Last.FlowGlueHist` and
`Step2.Flow.FlowHor2Aux` import `FlowBase` and `FlowSharp1` instead of `FlowHorizon`;
`Step2.Last.FlowLastBand` imports `FlowHor2Aux` instead of `FlowHor2Thm`; `FlowMasterHypL` imports
`FlowMasterHypLZ` (and no longer `FlowComplete2Hyp`), `FlowComplete2Hyp` imports `FlowMasterHypL`.

# Main theorems collected in `H02RG/Main/`, `H02UV/Main/` (2026-10-26)

Two new libraries in `lakefile.toml` (both in `defaultTargets`), with the default `srcDir = "."`,
so the module names contain the group directory:

| library | globs | file | module |
|---|---|---|---|
| `H02RGMain` | `H02RG.Main.+` | `H02RG/Main/Theorems.lean` | `H02RG.Main.Theorems` |
| `H02UVMain` | `H02UV.Main.+` | `H02UV/Main/Theorems.lean` | `H02UV.Main.Theorems` |

Declarations moved (names, namespaces, statements, docstrings and proofs unchanged):

| declaration | old file (module) | new file (module) |
|---|---|---|
| `Ward.thm_forest_macro` | `H02RG/Ward/ForestMacro.lean` (`Ward.ForestMacro`) | `H02RG/Main/Theorems.lean` (`H02RG.Main.Theorems`) |
| `Ward.thm_h02` | `H02RG/Ward/Main.lean` (`Ward.Main`) | `H02RG/Main/Theorems.lean` (`H02RG.Main.Theorems`) |
| `Ward.thm_forests0` | `H02RG/Ward/Main.lean` (`Ward.Main`) | `H02RG/Main/Theorems.lean` (`H02RG.Main.Theorems`) |
| `Ward.thm_forests` | `H02RG/Ward/Main.lean` (`Ward.Main`) | `H02RG/Main/Theorems.lean` (`H02RG.Main.Theorems`) |
| `Ward.thm_all` | `H02RG/Ward/MainAll.lean` (`Ward.MainAll`) | `H02RG/Main/Theorems.lean` (`H02RG.Main.Theorems`) |
| `Spin2.thm_arboreal_multiscale` | `H02UV/Spin2/Final/Arboreal.lean` (`Spin2.Final.Arboreal`) | `H02UV/Main/Theorems.lean` (`H02UV.Main.Theorems`) |
| `Spin2.thm_arboreal_limit_fixed` | `H02UV/Spin2/Final/Arboreal.lean` (`Spin2.Final.Arboreal`) | `H02UV/Main/Theorems.lean` (`H02UV.Main.Theorems`) |

Not moved: the statement predicates (`FMBody`, `H02Body`, `F0Body`, `FBody`, `AllBody`,
`ArbScale`, `ArbShort`, `arbF`), the per-coupling versions (`thm_forest_macro_of`, `thm_h02_of`,
`thm_all_of`), `Pg`/`Pg_eq` (used by `forests0_of_body` in `Ward.MainAll`), and the mass-shift
identities `Spin2.avg0_mass_indep`, `Spin2.avg0_eq_Pconn` (a lemma, `lem:massshift`, not a theorem).
No file became empty. The audit scripts import `H02RG.Main.Theorems` resp. `H02UV.Main.Theorems`
(`Audit/H02RG.lean`, `Audit/H02UV.lean`, `H02RG/Ward/Audit.lean`).


## Per-library audit scripts (2026-10-26)

The per-library audits moved from `Audit/` into the library directories; `Audit/H02RG.lean` and
`Audit/H02UV.lean` stay. They are not modules of any library (no umbrella imports them).

| old | new |
|---|---|
| `Audit/FRD.lean` | `FRD/Audit.lean` |
| `Audit/Grassmann.lean` | `Grassmann/Audit.lean` |
| `Audit/Loc.lean` | `Loc/Audit.lean` |
| `Audit/DressedFRD.lean` | `DressedFRD/Audit.lean` |
| `Audit/H02Forest.lean` | `H02/Audit.lean` |
| `Audit/Flow.lean` | `H02RG/Flow/Audit.lean` |
| `Audit/Obs.lean` | `H02RG/Obs/Audit.lean` |
| `Audit/PtCorr.lean` | `H02RG/PtCorr/Audit.lean` |
| `Audit/Psi4.lean` | `H02RG/Psi4/Audit.lean` |
| `Audit/Step.lean` | `H02RG/Step/Audit.lean` |
| `Audit/Suscept.lean` | `H02RG/Suscept/Audit.lean` |
| `Audit/Ward.lean` | `H02RG/Ward/Audit.lean` |
| `Audit/Cont.lean` | `Cont/Audit.lean` |
| `Audit/Flow2.lean` | `H02UV/Flow2/Audit.lean` |
| `Audit/Obs2.lean` | `H02UV/Obs2/Audit.lean` |
| `Audit/PtCorr2.lean` | `H02UV/PtCorr2/Audit.lean` |
| `Audit/Spin2.lean` | `H02UV/Spin2/Audit.lean` |
| `Audit/Step2.lean` | `H02UV/Step2/Audit.lean` |
| `Audit/H02RG.lean` | `H02RG/Audit.lean` (new `Audit/H02RG.lean`: only `h02rg-lean.tex`) |
| `Audit/H02UV.lean` | `H02UV/Audit.lean` (new `Audit/H02UV.lean`: only `h02uv-lean.tex`) |

## `Cont` to the top level (2026-10-26)

`H02UV/Cont/` → `Cont/`, `H02UV/Cont.lean` → `Cont.lean`, `H02UV/Cont/Audit.lean` →
`Cont/Audit.lean`; `srcDir = "H02UV"` removed from the `Cont` lib. Module and declaration names
unchanged. (Paths in the earlier sections of this file were updated to the new location.)

## Main theorems renamed into the `H02RG` / `H02UV` namespaces (2026-10-26)

The declarations in `H02RG/Main/Theorems.lean` and `H02UV/Main/Theorems.lean` now live in the
namespace matching their directory. Statements unchanged (the `#check` output is identical up to
the name).

| old name | new name |
|---|---|
| `Ward.thm_forest_macro` | `H02RG.thm_forest_macro` |
| `Ward.thm_h02` | `H02RG.thm_h02` |
| `Ward.thm_forests0` | `H02RG.thm_forests0` |
| `Ward.thm_forests` | `H02RG.thm_forests` |
| `Ward.thm_all` | `H02RG.thm_all` |
| `Spin2.thm_arboreal_multiscale` | `H02UV.thm_arboreal_multiscale` |
| `Spin2.thm_arboreal_limit_fixed` | `H02UV.thm_arboreal_limit_fixed` |
