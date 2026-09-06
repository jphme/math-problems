import PeaceableQueens.UpperBound.RecoveredFiniteCutSupport.CountBridge
import PeaceableQueens.UpperBound.RecoveredFiniteCutSupport.Cuts_00_03
import PeaceableQueens.UpperBound.RecoveredFiniteCutSupport.Cuts_04_07
import PeaceableQueens.UpperBound.RecoveredFiniteCutSupport.Cuts_08_11
import PeaceableQueens.UpperBound.RecoveredFiniteCutSupport.Cuts_12_15
import PeaceableQueens.UpperBound.RecoveredFiniteCutSupport.Cuts_16_19
import PeaceableQueens.UpperBound.RecoveredFiniteCutSupport.Cuts_20_23
import PeaceableQueens.UpperBound.RecoveredFiniteCutSupport.Cuts_24_27
import PeaceableQueens.UpperBound.RecoveredFiniteCutSupport.Cuts_28_31
import PeaceableQueens.UpperBound.RecoveredFiniteCutSupport.Cuts_32_35
import PeaceableQueens.UpperBound.RecoveredFiniteCutSupport.Cuts_36_39
import PeaceableQueens.UpperBound.RecoveredFiniteCutSupport.Cuts_40_43
import PeaceableQueens.UpperBound.RecoveredFiniteCutSupport.Cuts_44_47
import PeaceableQueens.UpperBound.RecoveredFiniteCutSupport.Cuts_48_51
import PeaceableQueens.UpperBound.RecoveredFiniteCutSupport.Cuts_52_55
import PeaceableQueens.UpperBound.RecoveredFiniteCutSupport.Cuts_56_59
import PeaceableQueens.UpperBound.RecoveredFiniteCutSupport.Cuts_60_63
import PeaceableQueens.UpperBound.RecoveredFiniteCutSupport.Cuts_64_67
import PeaceableQueens.UpperBound.RecoveredFiniteCutSupport.Cuts_68_71
import PeaceableQueens.UpperBound.RecoveredFiniteCutSupport.Cuts_72_75

namespace PeaceableQueens.UpperBound.RecoveredFiniteCutSupport

open MomentModel ConfigurationMoments ConfigurationBridge LPModel ModelCompatibility
open FiniteCertificateConsequences
open PeaceableQueens.UpperBound.FiniteCertificates

theorem cut_0_count_sound (cfg : Configuration q) [NeZero (2 * q)] (hq : 0 < q) :
    ((12 * min cfg.blackCells.card cfg.whiteCells.card : ℕ) : Int) ≤
      (FiniteCertificates.cuts 0).eval q (countPoint cfg) := by
  exact generated_cut_count_consequence (c := 0) cfg hq (cut_0_normalized_sound cfg hq)

theorem cut_1_count_sound (cfg : Configuration q) [NeZero (2 * q)] (hq : 0 < q) :
    ((12 * min cfg.blackCells.card cfg.whiteCells.card : ℕ) : Int) ≤
      (FiniteCertificates.cuts 1).eval q (countPoint cfg) := by
  exact generated_cut_count_consequence (c := 1) cfg hq (cut_1_normalized_sound cfg hq)

theorem cut_2_count_sound (cfg : Configuration q) [NeZero (2 * q)] (hq : 0 < q) :
    ((12 * min cfg.blackCells.card cfg.whiteCells.card : ℕ) : Int) ≤
      (FiniteCertificates.cuts 2).eval q (countPoint cfg) := by
  exact generated_cut_count_consequence (c := 2) cfg hq (cut_2_normalized_sound cfg hq)

theorem cut_3_count_sound (cfg : Configuration q) [NeZero (2 * q)] (hq : 0 < q) :
    ((12 * min cfg.blackCells.card cfg.whiteCells.card : ℕ) : Int) ≤
      (FiniteCertificates.cuts 3).eval q (countPoint cfg) := by
  exact generated_cut_count_consequence (c := 3) cfg hq (cut_3_normalized_sound cfg hq)

theorem cut_4_count_sound (cfg : Configuration q) [NeZero (2 * q)] (hq : 0 < q) :
    ((12 * min cfg.blackCells.card cfg.whiteCells.card : ℕ) : Int) ≤
      (FiniteCertificates.cuts 4).eval q (countPoint cfg) := by
  exact generated_cut_count_consequence (c := 4) cfg hq (cut_4_normalized_sound cfg hq)

theorem cut_5_count_sound (cfg : Configuration q) [NeZero (2 * q)] (hq : 0 < q) :
    ((12 * min cfg.blackCells.card cfg.whiteCells.card : ℕ) : Int) ≤
      (FiniteCertificates.cuts 5).eval q (countPoint cfg) := by
  exact generated_cut_count_consequence (c := 5) cfg hq (cut_5_normalized_sound cfg hq)

theorem cut_6_count_sound (cfg : Configuration q) [NeZero (2 * q)] (hq : 0 < q) :
    ((12 * min cfg.blackCells.card cfg.whiteCells.card : ℕ) : Int) ≤
      (FiniteCertificates.cuts 6).eval q (countPoint cfg) := by
  exact generated_cut_count_consequence (c := 6) cfg hq (cut_6_normalized_sound cfg hq)

theorem cut_7_count_sound (cfg : Configuration q) [NeZero (2 * q)] (hq : 0 < q) :
    ((12 * min cfg.blackCells.card cfg.whiteCells.card : ℕ) : Int) ≤
      (FiniteCertificates.cuts 7).eval q (countPoint cfg) := by
  exact generated_cut_count_consequence (c := 7) cfg hq (cut_7_normalized_sound cfg hq)

theorem cut_8_count_sound (cfg : Configuration q) [NeZero (2 * q)] (hq : 0 < q) :
    ((12 * min cfg.blackCells.card cfg.whiteCells.card : ℕ) : Int) ≤
      (FiniteCertificates.cuts 8).eval q (countPoint cfg) := by
  exact generated_cut_count_consequence (c := 8) cfg hq (cut_8_normalized_sound cfg hq)

theorem cut_9_count_sound (cfg : Configuration q) [NeZero (2 * q)] (hq : 0 < q) :
    ((12 * min cfg.blackCells.card cfg.whiteCells.card : ℕ) : Int) ≤
      (FiniteCertificates.cuts 9).eval q (countPoint cfg) := by
  exact generated_cut_count_consequence (c := 9) cfg hq (cut_9_normalized_sound cfg hq)

theorem cut_10_count_sound (cfg : Configuration q) [NeZero (2 * q)] (hq : 0 < q) :
    ((12 * min cfg.blackCells.card cfg.whiteCells.card : ℕ) : Int) ≤
      (FiniteCertificates.cuts 10).eval q (countPoint cfg) := by
  exact generated_cut_count_consequence (c := 10) cfg hq (cut_10_normalized_sound cfg hq)

theorem cut_11_count_sound (cfg : Configuration q) [NeZero (2 * q)] (hq : 0 < q) :
    ((12 * min cfg.blackCells.card cfg.whiteCells.card : ℕ) : Int) ≤
      (FiniteCertificates.cuts 11).eval q (countPoint cfg) := by
  exact generated_cut_count_consequence (c := 11) cfg hq (cut_11_normalized_sound cfg hq)

theorem cut_12_count_sound (cfg : Configuration q) [NeZero (2 * q)] (hq : 0 < q) :
    ((12 * min cfg.blackCells.card cfg.whiteCells.card : ℕ) : Int) ≤
      (FiniteCertificates.cuts 12).eval q (countPoint cfg) := by
  exact generated_cut_count_consequence (c := 12) cfg hq (cut_12_normalized_sound cfg hq)

theorem cut_13_count_sound (cfg : Configuration q) [NeZero (2 * q)] (hq : 0 < q) :
    ((12 * min cfg.blackCells.card cfg.whiteCells.card : ℕ) : Int) ≤
      (FiniteCertificates.cuts 13).eval q (countPoint cfg) := by
  exact generated_cut_count_consequence (c := 13) cfg hq (cut_13_normalized_sound cfg hq)

theorem cut_14_count_sound (cfg : Configuration q) [NeZero (2 * q)] (hq : 0 < q) :
    ((12 * min cfg.blackCells.card cfg.whiteCells.card : ℕ) : Int) ≤
      (FiniteCertificates.cuts 14).eval q (countPoint cfg) := by
  exact generated_cut_count_consequence (c := 14) cfg hq (cut_14_normalized_sound cfg hq)

theorem cut_15_count_sound (cfg : Configuration q) [NeZero (2 * q)] (hq : 0 < q) :
    ((12 * min cfg.blackCells.card cfg.whiteCells.card : ℕ) : Int) ≤
      (FiniteCertificates.cuts 15).eval q (countPoint cfg) := by
  exact generated_cut_count_consequence (c := 15) cfg hq (cut_15_normalized_sound cfg hq)

theorem cut_16_count_sound (cfg : Configuration q) [NeZero (2 * q)] (hq : 0 < q) :
    ((12 * min cfg.blackCells.card cfg.whiteCells.card : ℕ) : Int) ≤
      (FiniteCertificates.cuts 16).eval q (countPoint cfg) := by
  exact generated_cut_count_consequence (c := 16) cfg hq (cut_16_normalized_sound cfg hq)

theorem cut_17_count_sound (cfg : Configuration q) [NeZero (2 * q)] (hq : 0 < q) :
    ((12 * min cfg.blackCells.card cfg.whiteCells.card : ℕ) : Int) ≤
      (FiniteCertificates.cuts 17).eval q (countPoint cfg) := by
  exact generated_cut_count_consequence (c := 17) cfg hq (cut_17_normalized_sound cfg hq)

theorem cut_18_count_sound (cfg : Configuration q) [NeZero (2 * q)] (hq : 0 < q) :
    ((12 * min cfg.blackCells.card cfg.whiteCells.card : ℕ) : Int) ≤
      (FiniteCertificates.cuts 18).eval q (countPoint cfg) := by
  exact generated_cut_count_consequence (c := 18) cfg hq (cut_18_normalized_sound cfg hq)

theorem cut_19_count_sound (cfg : Configuration q) [NeZero (2 * q)] (hq : 0 < q) :
    ((12 * min cfg.blackCells.card cfg.whiteCells.card : ℕ) : Int) ≤
      (FiniteCertificates.cuts 19).eval q (countPoint cfg) := by
  exact generated_cut_count_consequence (c := 19) cfg hq (cut_19_normalized_sound cfg hq)

theorem cut_20_count_sound (cfg : Configuration q) [NeZero (2 * q)] (hq : 0 < q) :
    ((12 * min cfg.blackCells.card cfg.whiteCells.card : ℕ) : Int) ≤
      (FiniteCertificates.cuts 20).eval q (countPoint cfg) := by
  exact generated_cut_count_consequence (c := 20) cfg hq (cut_20_normalized_sound cfg hq)

theorem cut_21_count_sound (cfg : Configuration q) [NeZero (2 * q)] (hq : 0 < q) :
    ((12 * min cfg.blackCells.card cfg.whiteCells.card : ℕ) : Int) ≤
      (FiniteCertificates.cuts 21).eval q (countPoint cfg) := by
  exact generated_cut_count_consequence (c := 21) cfg hq (cut_21_normalized_sound cfg hq)

theorem cut_22_count_sound (cfg : Configuration q) [NeZero (2 * q)] (hq : 0 < q) :
    ((12 * min cfg.blackCells.card cfg.whiteCells.card : ℕ) : Int) ≤
      (FiniteCertificates.cuts 22).eval q (countPoint cfg) := by
  exact generated_cut_count_consequence (c := 22) cfg hq (cut_22_normalized_sound cfg hq)

theorem cut_23_count_sound (cfg : Configuration q) [NeZero (2 * q)] (hq : 0 < q) :
    ((12 * min cfg.blackCells.card cfg.whiteCells.card : ℕ) : Int) ≤
      (FiniteCertificates.cuts 23).eval q (countPoint cfg) := by
  exact generated_cut_count_consequence (c := 23) cfg hq (cut_23_normalized_sound cfg hq)

theorem cut_24_count_sound (cfg : Configuration q) [NeZero (2 * q)] (hq : 0 < q) :
    ((12 * min cfg.blackCells.card cfg.whiteCells.card : ℕ) : Int) ≤
      (FiniteCertificates.cuts 24).eval q (countPoint cfg) := by
  exact generated_cut_count_consequence (c := 24) cfg hq (cut_24_normalized_sound cfg hq)

theorem cut_25_count_sound (cfg : Configuration q) [NeZero (2 * q)] (hq : 0 < q) :
    ((12 * min cfg.blackCells.card cfg.whiteCells.card : ℕ) : Int) ≤
      (FiniteCertificates.cuts 25).eval q (countPoint cfg) := by
  exact generated_cut_count_consequence (c := 25) cfg hq (cut_25_normalized_sound cfg hq)

theorem cut_26_count_sound (cfg : Configuration q) [NeZero (2 * q)] (hq : 0 < q) :
    ((12 * min cfg.blackCells.card cfg.whiteCells.card : ℕ) : Int) ≤
      (FiniteCertificates.cuts 26).eval q (countPoint cfg) := by
  exact generated_cut_count_consequence (c := 26) cfg hq (cut_26_normalized_sound cfg hq)

theorem cut_27_count_sound (cfg : Configuration q) [NeZero (2 * q)] (hq : 0 < q) :
    ((12 * min cfg.blackCells.card cfg.whiteCells.card : ℕ) : Int) ≤
      (FiniteCertificates.cuts 27).eval q (countPoint cfg) := by
  exact generated_cut_count_consequence (c := 27) cfg hq (cut_27_normalized_sound cfg hq)

theorem cut_28_count_sound (cfg : Configuration q) [NeZero (2 * q)] (hq : 0 < q) :
    ((12 * min cfg.blackCells.card cfg.whiteCells.card : ℕ) : Int) ≤
      (FiniteCertificates.cuts 28).eval q (countPoint cfg) := by
  exact generated_cut_count_consequence (c := 28) cfg hq (cut_28_normalized_sound cfg hq)

theorem cut_29_count_sound (cfg : Configuration q) [NeZero (2 * q)] (hq : 0 < q) :
    ((12 * min cfg.blackCells.card cfg.whiteCells.card : ℕ) : Int) ≤
      (FiniteCertificates.cuts 29).eval q (countPoint cfg) := by
  exact generated_cut_count_consequence (c := 29) cfg hq (cut_29_normalized_sound cfg hq)

theorem cut_30_count_sound (cfg : Configuration q) [NeZero (2 * q)] (hq : 0 < q) :
    ((12 * min cfg.blackCells.card cfg.whiteCells.card : ℕ) : Int) ≤
      (FiniteCertificates.cuts 30).eval q (countPoint cfg) := by
  exact generated_cut_count_consequence (c := 30) cfg hq (cut_30_normalized_sound cfg hq)

theorem cut_31_count_sound (cfg : Configuration q) [NeZero (2 * q)] (hq : 0 < q) :
    ((12 * min cfg.blackCells.card cfg.whiteCells.card : ℕ) : Int) ≤
      (FiniteCertificates.cuts 31).eval q (countPoint cfg) := by
  exact generated_cut_count_consequence (c := 31) cfg hq (cut_31_normalized_sound cfg hq)

theorem cut_32_count_sound (cfg : Configuration q) [NeZero (2 * q)] (hq : 0 < q) :
    ((12 * min cfg.blackCells.card cfg.whiteCells.card : ℕ) : Int) ≤
      (FiniteCertificates.cuts 32).eval q (countPoint cfg) := by
  exact generated_cut_count_consequence (c := 32) cfg hq (cut_32_normalized_sound cfg hq)

theorem cut_33_count_sound (cfg : Configuration q) [NeZero (2 * q)] (hq : 0 < q) :
    ((12 * min cfg.blackCells.card cfg.whiteCells.card : ℕ) : Int) ≤
      (FiniteCertificates.cuts 33).eval q (countPoint cfg) := by
  exact generated_cut_count_consequence (c := 33) cfg hq (cut_33_normalized_sound cfg hq)

theorem cut_34_count_sound (cfg : Configuration q) [NeZero (2 * q)] (hq : 0 < q) :
    ((12 * min cfg.blackCells.card cfg.whiteCells.card : ℕ) : Int) ≤
      (FiniteCertificates.cuts 34).eval q (countPoint cfg) := by
  exact generated_cut_count_consequence (c := 34) cfg hq (cut_34_normalized_sound cfg hq)

theorem cut_35_count_sound (cfg : Configuration q) [NeZero (2 * q)] (hq : 0 < q) :
    ((12 * min cfg.blackCells.card cfg.whiteCells.card : ℕ) : Int) ≤
      (FiniteCertificates.cuts 35).eval q (countPoint cfg) := by
  exact generated_cut_count_consequence (c := 35) cfg hq (cut_35_normalized_sound cfg hq)

theorem cut_36_count_sound (cfg : Configuration q) [NeZero (2 * q)] (hq : 0 < q) :
    ((12 * min cfg.blackCells.card cfg.whiteCells.card : ℕ) : Int) ≤
      (FiniteCertificates.cuts 36).eval q (countPoint cfg) := by
  exact generated_cut_count_consequence (c := 36) cfg hq (cut_36_normalized_sound cfg hq)

theorem cut_37_count_sound (cfg : Configuration q) [NeZero (2 * q)] (hq : 0 < q) :
    ((12 * min cfg.blackCells.card cfg.whiteCells.card : ℕ) : Int) ≤
      (FiniteCertificates.cuts 37).eval q (countPoint cfg) := by
  exact generated_cut_count_consequence (c := 37) cfg hq (cut_37_normalized_sound cfg hq)

theorem cut_38_count_sound (cfg : Configuration q) [NeZero (2 * q)] (hq : 0 < q) :
    ((12 * min cfg.blackCells.card cfg.whiteCells.card : ℕ) : Int) ≤
      (FiniteCertificates.cuts 38).eval q (countPoint cfg) := by
  exact generated_cut_count_consequence (c := 38) cfg hq (cut_38_normalized_sound cfg hq)

theorem cut_39_count_sound (cfg : Configuration q) [NeZero (2 * q)] (hq : 0 < q) :
    ((12 * min cfg.blackCells.card cfg.whiteCells.card : ℕ) : Int) ≤
      (FiniteCertificates.cuts 39).eval q (countPoint cfg) := by
  exact generated_cut_count_consequence (c := 39) cfg hq (cut_39_normalized_sound cfg hq)

theorem cut_40_count_sound (cfg : Configuration q) [NeZero (2 * q)] (hq : 0 < q) :
    ((12 * min cfg.blackCells.card cfg.whiteCells.card : ℕ) : Int) ≤
      (FiniteCertificates.cuts 40).eval q (countPoint cfg) := by
  exact generated_cut_count_consequence (c := 40) cfg hq (cut_40_normalized_sound cfg hq)

theorem cut_41_count_sound (cfg : Configuration q) [NeZero (2 * q)] (hq : 0 < q) :
    ((12 * min cfg.blackCells.card cfg.whiteCells.card : ℕ) : Int) ≤
      (FiniteCertificates.cuts 41).eval q (countPoint cfg) := by
  exact generated_cut_count_consequence (c := 41) cfg hq (cut_41_normalized_sound cfg hq)

theorem cut_42_count_sound (cfg : Configuration q) [NeZero (2 * q)] (hq : 0 < q) :
    ((12 * min cfg.blackCells.card cfg.whiteCells.card : ℕ) : Int) ≤
      (FiniteCertificates.cuts 42).eval q (countPoint cfg) := by
  exact generated_cut_count_consequence (c := 42) cfg hq (cut_42_normalized_sound cfg hq)

theorem cut_43_count_sound (cfg : Configuration q) [NeZero (2 * q)] (hq : 0 < q) :
    ((12 * min cfg.blackCells.card cfg.whiteCells.card : ℕ) : Int) ≤
      (FiniteCertificates.cuts 43).eval q (countPoint cfg) := by
  exact generated_cut_count_consequence (c := 43) cfg hq (cut_43_normalized_sound cfg hq)

theorem cut_44_count_sound (cfg : Configuration q) [NeZero (2 * q)] (hq : 0 < q) :
    ((12 * min cfg.blackCells.card cfg.whiteCells.card : ℕ) : Int) ≤
      (FiniteCertificates.cuts 44).eval q (countPoint cfg) := by
  exact generated_cut_count_consequence (c := 44) cfg hq (cut_44_normalized_sound cfg hq)

theorem cut_45_count_sound (cfg : Configuration q) [NeZero (2 * q)] (hq : 0 < q) :
    ((12 * min cfg.blackCells.card cfg.whiteCells.card : ℕ) : Int) ≤
      (FiniteCertificates.cuts 45).eval q (countPoint cfg) := by
  exact generated_cut_count_consequence (c := 45) cfg hq (cut_45_normalized_sound cfg hq)

theorem cut_46_count_sound (cfg : Configuration q) [NeZero (2 * q)] (hq : 0 < q) :
    ((12 * min cfg.blackCells.card cfg.whiteCells.card : ℕ) : Int) ≤
      (FiniteCertificates.cuts 46).eval q (countPoint cfg) := by
  exact generated_cut_count_consequence (c := 46) cfg hq (cut_46_normalized_sound cfg hq)

theorem cut_47_count_sound (cfg : Configuration q) [NeZero (2 * q)] (hq : 0 < q) :
    ((12 * min cfg.blackCells.card cfg.whiteCells.card : ℕ) : Int) ≤
      (FiniteCertificates.cuts 47).eval q (countPoint cfg) := by
  exact generated_cut_count_consequence (c := 47) cfg hq (cut_47_normalized_sound cfg hq)

theorem cut_48_count_sound (cfg : Configuration q) [NeZero (2 * q)] (hq : 0 < q) :
    ((12 * min cfg.blackCells.card cfg.whiteCells.card : ℕ) : Int) ≤
      (FiniteCertificates.cuts 48).eval q (countPoint cfg) := by
  exact generated_cut_count_consequence (c := 48) cfg hq (cut_48_normalized_sound cfg hq)

theorem cut_49_count_sound (cfg : Configuration q) [NeZero (2 * q)] (hq : 0 < q) :
    ((12 * min cfg.blackCells.card cfg.whiteCells.card : ℕ) : Int) ≤
      (FiniteCertificates.cuts 49).eval q (countPoint cfg) := by
  exact generated_cut_count_consequence (c := 49) cfg hq (cut_49_normalized_sound cfg hq)

theorem cut_50_count_sound (cfg : Configuration q) [NeZero (2 * q)] (hq : 0 < q) :
    ((12 * min cfg.blackCells.card cfg.whiteCells.card : ℕ) : Int) ≤
      (FiniteCertificates.cuts 50).eval q (countPoint cfg) := by
  exact generated_cut_count_consequence (c := 50) cfg hq (cut_50_normalized_sound cfg hq)

theorem cut_51_count_sound (cfg : Configuration q) [NeZero (2 * q)] (hq : 0 < q) :
    ((12 * min cfg.blackCells.card cfg.whiteCells.card : ℕ) : Int) ≤
      (FiniteCertificates.cuts 51).eval q (countPoint cfg) := by
  exact generated_cut_count_consequence (c := 51) cfg hq (cut_51_normalized_sound cfg hq)

theorem cut_52_count_sound (cfg : Configuration q) [NeZero (2 * q)] (hq : 0 < q) :
    ((12 * min cfg.blackCells.card cfg.whiteCells.card : ℕ) : Int) ≤
      (FiniteCertificates.cuts 52).eval q (countPoint cfg) := by
  exact generated_cut_count_consequence (c := 52) cfg hq (cut_52_normalized_sound cfg hq)

theorem cut_53_count_sound (cfg : Configuration q) [NeZero (2 * q)] (hq : 0 < q) :
    ((12 * min cfg.blackCells.card cfg.whiteCells.card : ℕ) : Int) ≤
      (FiniteCertificates.cuts 53).eval q (countPoint cfg) := by
  exact generated_cut_count_consequence (c := 53) cfg hq (cut_53_normalized_sound cfg hq)

theorem cut_54_count_sound (cfg : Configuration q) [NeZero (2 * q)] (hq : 0 < q) :
    ((12 * min cfg.blackCells.card cfg.whiteCells.card : ℕ) : Int) ≤
      (FiniteCertificates.cuts 54).eval q (countPoint cfg) := by
  exact generated_cut_count_consequence (c := 54) cfg hq (cut_54_normalized_sound cfg hq)

theorem cut_55_count_sound (cfg : Configuration q) [NeZero (2 * q)] (hq : 0 < q) :
    ((12 * min cfg.blackCells.card cfg.whiteCells.card : ℕ) : Int) ≤
      (FiniteCertificates.cuts 55).eval q (countPoint cfg) := by
  exact generated_cut_count_consequence (c := 55) cfg hq (cut_55_normalized_sound cfg hq)

theorem cut_56_count_sound (cfg : Configuration q) [NeZero (2 * q)] (hq : 0 < q) :
    ((12 * min cfg.blackCells.card cfg.whiteCells.card : ℕ) : Int) ≤
      (FiniteCertificates.cuts 56).eval q (countPoint cfg) := by
  exact generated_cut_count_consequence (c := 56) cfg hq (cut_56_normalized_sound cfg hq)

theorem cut_57_count_sound (cfg : Configuration q) [NeZero (2 * q)] (hq : 0 < q) :
    ((12 * min cfg.blackCells.card cfg.whiteCells.card : ℕ) : Int) ≤
      (FiniteCertificates.cuts 57).eval q (countPoint cfg) := by
  exact generated_cut_count_consequence (c := 57) cfg hq (cut_57_normalized_sound cfg hq)

theorem cut_58_count_sound (cfg : Configuration q) [NeZero (2 * q)] (hq : 0 < q) :
    ((12 * min cfg.blackCells.card cfg.whiteCells.card : ℕ) : Int) ≤
      (FiniteCertificates.cuts 58).eval q (countPoint cfg) := by
  exact generated_cut_count_consequence (c := 58) cfg hq (cut_58_normalized_sound cfg hq)

theorem cut_59_count_sound (cfg : Configuration q) [NeZero (2 * q)] (hq : 0 < q) :
    ((12 * min cfg.blackCells.card cfg.whiteCells.card : ℕ) : Int) ≤
      (FiniteCertificates.cuts 59).eval q (countPoint cfg) := by
  exact generated_cut_count_consequence (c := 59) cfg hq (cut_59_normalized_sound cfg hq)

theorem cut_60_count_sound (cfg : Configuration q) [NeZero (2 * q)] (hq : 0 < q) :
    ((12 * min cfg.blackCells.card cfg.whiteCells.card : ℕ) : Int) ≤
      (FiniteCertificates.cuts 60).eval q (countPoint cfg) := by
  exact generated_cut_count_consequence (c := 60) cfg hq (cut_60_normalized_sound cfg hq)

theorem cut_61_count_sound (cfg : Configuration q) [NeZero (2 * q)] (hq : 0 < q) :
    ((12 * min cfg.blackCells.card cfg.whiteCells.card : ℕ) : Int) ≤
      (FiniteCertificates.cuts 61).eval q (countPoint cfg) := by
  exact generated_cut_count_consequence (c := 61) cfg hq (cut_61_normalized_sound cfg hq)

theorem cut_62_count_sound (cfg : Configuration q) [NeZero (2 * q)] (hq : 0 < q) :
    ((12 * min cfg.blackCells.card cfg.whiteCells.card : ℕ) : Int) ≤
      (FiniteCertificates.cuts 62).eval q (countPoint cfg) := by
  exact generated_cut_count_consequence (c := 62) cfg hq (cut_62_normalized_sound cfg hq)

theorem cut_63_count_sound (cfg : Configuration q) [NeZero (2 * q)] (hq : 0 < q) :
    ((12 * min cfg.blackCells.card cfg.whiteCells.card : ℕ) : Int) ≤
      (FiniteCertificates.cuts 63).eval q (countPoint cfg) := by
  exact generated_cut_count_consequence (c := 63) cfg hq (cut_63_normalized_sound cfg hq)

theorem cut_64_count_sound (cfg : Configuration q) [NeZero (2 * q)] (hq : 0 < q) :
    ((12 * min cfg.blackCells.card cfg.whiteCells.card : ℕ) : Int) ≤
      (FiniteCertificates.cuts 64).eval q (countPoint cfg) := by
  exact generated_cut_count_consequence (c := 64) cfg hq (cut_64_normalized_sound cfg hq)

theorem cut_65_count_sound (cfg : Configuration q) [NeZero (2 * q)] (hq : 0 < q) :
    ((12 * min cfg.blackCells.card cfg.whiteCells.card : ℕ) : Int) ≤
      (FiniteCertificates.cuts 65).eval q (countPoint cfg) := by
  exact generated_cut_count_consequence (c := 65) cfg hq (cut_65_normalized_sound cfg hq)

theorem cut_66_count_sound (cfg : Configuration q) [NeZero (2 * q)] (hq : 0 < q) :
    ((12 * min cfg.blackCells.card cfg.whiteCells.card : ℕ) : Int) ≤
      (FiniteCertificates.cuts 66).eval q (countPoint cfg) := by
  exact generated_cut_count_consequence (c := 66) cfg hq (cut_66_normalized_sound cfg hq)

theorem cut_67_count_sound (cfg : Configuration q) [NeZero (2 * q)] (hq : 0 < q) :
    ((12 * min cfg.blackCells.card cfg.whiteCells.card : ℕ) : Int) ≤
      (FiniteCertificates.cuts 67).eval q (countPoint cfg) := by
  exact generated_cut_count_consequence (c := 67) cfg hq (cut_67_normalized_sound cfg hq)

theorem cut_68_count_sound (cfg : Configuration q) [NeZero (2 * q)] (hq : 0 < q) :
    ((12 * min cfg.blackCells.card cfg.whiteCells.card : ℕ) : Int) ≤
      (FiniteCertificates.cuts 68).eval q (countPoint cfg) := by
  exact generated_cut_count_consequence (c := 68) cfg hq (cut_68_normalized_sound cfg hq)

theorem cut_69_count_sound (cfg : Configuration q) [NeZero (2 * q)] (hq : 0 < q) :
    ((12 * min cfg.blackCells.card cfg.whiteCells.card : ℕ) : Int) ≤
      (FiniteCertificates.cuts 69).eval q (countPoint cfg) := by
  exact generated_cut_count_consequence (c := 69) cfg hq (cut_69_normalized_sound cfg hq)

theorem cut_70_count_sound (cfg : Configuration q) [NeZero (2 * q)] (hq : 0 < q) :
    ((12 * min cfg.blackCells.card cfg.whiteCells.card : ℕ) : Int) ≤
      (FiniteCertificates.cuts 70).eval q (countPoint cfg) := by
  exact generated_cut_count_consequence (c := 70) cfg hq (cut_70_normalized_sound cfg hq)

theorem cut_71_count_sound (cfg : Configuration q) [NeZero (2 * q)] (hq : 0 < q) :
    ((12 * min cfg.blackCells.card cfg.whiteCells.card : ℕ) : Int) ≤
      (FiniteCertificates.cuts 71).eval q (countPoint cfg) := by
  exact generated_cut_count_consequence (c := 71) cfg hq (cut_71_normalized_sound cfg hq)

theorem cut_72_count_sound (cfg : Configuration q) [NeZero (2 * q)] (hq : 0 < q) :
    ((12 * min cfg.blackCells.card cfg.whiteCells.card : ℕ) : Int) ≤
      (FiniteCertificates.cuts 72).eval q (countPoint cfg) := by
  exact generated_cut_count_consequence (c := 72) cfg hq (cut_72_normalized_sound cfg hq)

theorem cut_73_count_sound (cfg : Configuration q) [NeZero (2 * q)] (hq : 0 < q) :
    ((12 * min cfg.blackCells.card cfg.whiteCells.card : ℕ) : Int) ≤
      (FiniteCertificates.cuts 73).eval q (countPoint cfg) := by
  exact generated_cut_count_consequence (c := 73) cfg hq (cut_73_normalized_sound cfg hq)

theorem cut_74_count_sound (cfg : Configuration q) [NeZero (2 * q)] (hq : 0 < q) :
    ((12 * min cfg.blackCells.card cfg.whiteCells.card : ℕ) : Int) ≤
      (FiniteCertificates.cuts 74).eval q (countPoint cfg) := by
  exact generated_cut_count_consequence (c := 74) cfg hq (cut_74_normalized_sound cfg hq)

theorem cut_75_count_sound (cfg : Configuration q) [NeZero (2 * q)] (hq : 0 < q) :
    ((12 * min cfg.blackCells.card cfg.whiteCells.card : ℕ) : Int) ≤
      (FiniteCertificates.cuts 75).eval q (countPoint cfg) := by
  exact generated_cut_count_consequence (c := 75) cfg hq (cut_75_normalized_sound cfg hq)

/-- The uniform support fact consumed by `finite_order_bound_of_tree`. -/
theorem cutSound (q : ℕ) [NeZero (2 * q)] (hq : 0 < q) :
    ∀ (c : Fin 76) (cfg : Configuration q), ((12 * min cfg.blackCells.card cfg.whiteCells.card : ℕ) : Int) ≤
      (FiniteCertificates.cuts c).eval q (countPoint cfg) := by
  intro c cfg
  fin_cases c
  · exact cut_0_count_sound cfg hq
  · exact cut_1_count_sound cfg hq
  · exact cut_2_count_sound cfg hq
  · exact cut_3_count_sound cfg hq
  · exact cut_4_count_sound cfg hq
  · exact cut_5_count_sound cfg hq
  · exact cut_6_count_sound cfg hq
  · exact cut_7_count_sound cfg hq
  · exact cut_8_count_sound cfg hq
  · exact cut_9_count_sound cfg hq
  · exact cut_10_count_sound cfg hq
  · exact cut_11_count_sound cfg hq
  · exact cut_12_count_sound cfg hq
  · exact cut_13_count_sound cfg hq
  · exact cut_14_count_sound cfg hq
  · exact cut_15_count_sound cfg hq
  · exact cut_16_count_sound cfg hq
  · exact cut_17_count_sound cfg hq
  · exact cut_18_count_sound cfg hq
  · exact cut_19_count_sound cfg hq
  · exact cut_20_count_sound cfg hq
  · exact cut_21_count_sound cfg hq
  · exact cut_22_count_sound cfg hq
  · exact cut_23_count_sound cfg hq
  · exact cut_24_count_sound cfg hq
  · exact cut_25_count_sound cfg hq
  · exact cut_26_count_sound cfg hq
  · exact cut_27_count_sound cfg hq
  · exact cut_28_count_sound cfg hq
  · exact cut_29_count_sound cfg hq
  · exact cut_30_count_sound cfg hq
  · exact cut_31_count_sound cfg hq
  · exact cut_32_count_sound cfg hq
  · exact cut_33_count_sound cfg hq
  · exact cut_34_count_sound cfg hq
  · exact cut_35_count_sound cfg hq
  · exact cut_36_count_sound cfg hq
  · exact cut_37_count_sound cfg hq
  · exact cut_38_count_sound cfg hq
  · exact cut_39_count_sound cfg hq
  · exact cut_40_count_sound cfg hq
  · exact cut_41_count_sound cfg hq
  · exact cut_42_count_sound cfg hq
  · exact cut_43_count_sound cfg hq
  · exact cut_44_count_sound cfg hq
  · exact cut_45_count_sound cfg hq
  · exact cut_46_count_sound cfg hq
  · exact cut_47_count_sound cfg hq
  · exact cut_48_count_sound cfg hq
  · exact cut_49_count_sound cfg hq
  · exact cut_50_count_sound cfg hq
  · exact cut_51_count_sound cfg hq
  · exact cut_52_count_sound cfg hq
  · exact cut_53_count_sound cfg hq
  · exact cut_54_count_sound cfg hq
  · exact cut_55_count_sound cfg hq
  · exact cut_56_count_sound cfg hq
  · exact cut_57_count_sound cfg hq
  · exact cut_58_count_sound cfg hq
  · exact cut_59_count_sound cfg hq
  · exact cut_60_count_sound cfg hq
  · exact cut_61_count_sound cfg hq
  · exact cut_62_count_sound cfg hq
  · exact cut_63_count_sound cfg hq
  · exact cut_64_count_sound cfg hq
  · exact cut_65_count_sound cfg hq
  · exact cut_66_count_sound cfg hq
  · exact cut_67_count_sound cfg hq
  · exact cut_68_count_sound cfg hq
  · exact cut_69_count_sound cfg hq
  · exact cut_70_count_sound cfg hq
  · exact cut_71_count_sound cfg hq
  · exact cut_72_count_sound cfg hq
  · exact cut_73_count_sound cfg hq
  · exact cut_74_count_sound cfg hq
  · exact cut_75_count_sound cfg hq

#print axioms cut_0_count_sound
#print axioms cut_75_count_sound

#print axioms cutSound

end PeaceableQueens.UpperBound.RecoveredFiniteCutSupport
