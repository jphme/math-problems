import PeaceableQueens.UpperBound.Generated.Even.CoreTopology
import PeaceableQueens.UpperBound.Generated.Even.CoreLeafRange01
import PeaceableQueens.UpperBound.Generated.Even.CoreScaled00Check

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.BranchCertificate

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def node_box_0 : ProfileBox := { lower := ![(0 : ℚ) / 1, (3 : ℚ) / 5, (0 : ℚ) / 1, (3 : ℚ) / 5, (19 : ℚ) / 20, (0 : ℚ) / 1, (19 : ℚ) / 20, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 10, (7 : ℚ) / 8, (1 : ℚ) / 10, (7 : ℚ) / 8, (1 : ℚ) / 1, (1 : ℚ) / 10, (1 : ℚ) / 1, (1 : ℚ) / 10] }
def node_box_1 : ProfileBox := { lower := ![(0 : ℚ) / 1, (3 : ℚ) / 5, (0 : ℚ) / 1, (3 : ℚ) / 5, (19 : ℚ) / 20, (0 : ℚ) / 1, (19 : ℚ) / 20, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 10, (59 : ℚ) / 80, (1 : ℚ) / 10, (7 : ℚ) / 8, (1 : ℚ) / 1, (1 : ℚ) / 10, (1 : ℚ) / 1, (1 : ℚ) / 10] }
def node_box_2 : ProfileBox := { lower := ![(0 : ℚ) / 1, (59 : ℚ) / 80, (0 : ℚ) / 1, (3 : ℚ) / 5, (19 : ℚ) / 20, (0 : ℚ) / 1, (19 : ℚ) / 20, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 10, (7 : ℚ) / 8, (1 : ℚ) / 10, (7 : ℚ) / 8, (1 : ℚ) / 1, (1 : ℚ) / 10, (1 : ℚ) / 1, (1 : ℚ) / 10] }
def node_box_3 : ProfileBox := { lower := ![(0 : ℚ) / 1, (3 : ℚ) / 5, (0 : ℚ) / 1, (3 : ℚ) / 5, (19 : ℚ) / 20, (0 : ℚ) / 1, (19 : ℚ) / 20, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 10, (59 : ℚ) / 80, (1 : ℚ) / 10, (59 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 10, (1 : ℚ) / 1, (1 : ℚ) / 10] }
def node_box_4 : ProfileBox := { lower := ![(0 : ℚ) / 1, (3 : ℚ) / 5, (0 : ℚ) / 1, (59 : ℚ) / 80, (19 : ℚ) / 20, (0 : ℚ) / 1, (19 : ℚ) / 20, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 10, (59 : ℚ) / 80, (1 : ℚ) / 10, (7 : ℚ) / 8, (1 : ℚ) / 1, (1 : ℚ) / 10, (1 : ℚ) / 1, (1 : ℚ) / 10] }
def node_box_5 : ProfileBox := branch_box_5
def node_box_6 : ProfileBox := { lower := ![(0 : ℚ) / 1, (107 : ℚ) / 160, (0 : ℚ) / 1, (3 : ℚ) / 5, (19 : ℚ) / 20, (0 : ℚ) / 1, (19 : ℚ) / 20, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 10, (59 : ℚ) / 80, (1 : ℚ) / 10, (59 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 10, (1 : ℚ) / 1, (1 : ℚ) / 10] }
def node_box_7 : ProfileBox := branch_box_7
def node_box_8 : ProfileBox := { lower := ![(0 : ℚ) / 1, (107 : ℚ) / 160, (0 : ℚ) / 1, (107 : ℚ) / 160, (19 : ℚ) / 20, (0 : ℚ) / 1, (19 : ℚ) / 20, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 10, (59 : ℚ) / 80, (1 : ℚ) / 10, (59 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 10, (1 : ℚ) / 1, (1 : ℚ) / 10] }
def node_box_9 : ProfileBox := { lower := ![(0 : ℚ) / 1, (107 : ℚ) / 160, (0 : ℚ) / 1, (107 : ℚ) / 160, (19 : ℚ) / 20, (0 : ℚ) / 1, (19 : ℚ) / 20, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 20, (59 : ℚ) / 80, (1 : ℚ) / 10, (59 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 10, (1 : ℚ) / 1, (1 : ℚ) / 10] }
def node_box_10 : ProfileBox := { lower := ![(1 : ℚ) / 20, (107 : ℚ) / 160, (0 : ℚ) / 1, (107 : ℚ) / 160, (19 : ℚ) / 20, (0 : ℚ) / 1, (19 : ℚ) / 20, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 10, (59 : ℚ) / 80, (1 : ℚ) / 10, (59 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 10, (1 : ℚ) / 1, (1 : ℚ) / 10] }
def node_box_11 : ProfileBox := { lower := ![(0 : ℚ) / 1, (107 : ℚ) / 160, (0 : ℚ) / 1, (107 : ℚ) / 160, (19 : ℚ) / 20, (0 : ℚ) / 1, (19 : ℚ) / 20, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 20, (59 : ℚ) / 80, (1 : ℚ) / 20, (59 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 10, (1 : ℚ) / 1, (1 : ℚ) / 10] }
def node_box_12 : ProfileBox := { lower := ![(0 : ℚ) / 1, (107 : ℚ) / 160, (1 : ℚ) / 20, (107 : ℚ) / 160, (19 : ℚ) / 20, (0 : ℚ) / 1, (19 : ℚ) / 20, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 20, (59 : ℚ) / 80, (1 : ℚ) / 10, (59 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 10, (1 : ℚ) / 1, (1 : ℚ) / 10] }
def node_box_13 : ProfileBox := { lower := ![(0 : ℚ) / 1, (107 : ℚ) / 160, (0 : ℚ) / 1, (107 : ℚ) / 160, (19 : ℚ) / 20, (0 : ℚ) / 1, (19 : ℚ) / 20, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 20, (59 : ℚ) / 80, (1 : ℚ) / 20, (59 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 20, (1 : ℚ) / 1, (1 : ℚ) / 10] }
def node_box_14 : ProfileBox := branch_box_14
def node_box_15 : ProfileBox := { lower := ![(0 : ℚ) / 1, (107 : ℚ) / 160, (0 : ℚ) / 1, (107 : ℚ) / 160, (19 : ℚ) / 20, (0 : ℚ) / 1, (19 : ℚ) / 20, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 20, (59 : ℚ) / 80, (1 : ℚ) / 20, (59 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 20, (1 : ℚ) / 1, (1 : ℚ) / 20] }
def node_box_16 : ProfileBox := branch_box_16
def node_box_17 : ProfileBox := branch_box_17
def node_box_18 : ProfileBox := { lower := ![(0 : ℚ) / 1, (45 : ℚ) / 64, (0 : ℚ) / 1, (107 : ℚ) / 160, (19 : ℚ) / 20, (0 : ℚ) / 1, (19 : ℚ) / 20, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 20, (59 : ℚ) / 80, (1 : ℚ) / 20, (59 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 20, (1 : ℚ) / 1, (1 : ℚ) / 20] }
def node_box_19 : ProfileBox := branch_box_19
def node_box_20 : ProfileBox := { lower := ![(0 : ℚ) / 1, (45 : ℚ) / 64, (0 : ℚ) / 1, (45 : ℚ) / 64, (19 : ℚ) / 20, (0 : ℚ) / 1, (19 : ℚ) / 20, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 20, (59 : ℚ) / 80, (1 : ℚ) / 20, (59 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 20, (1 : ℚ) / 1, (1 : ℚ) / 20] }
def node_box_21 : ProfileBox := { lower := ![(0 : ℚ) / 1, (45 : ℚ) / 64, (0 : ℚ) / 1, (45 : ℚ) / 64, (19 : ℚ) / 20, (0 : ℚ) / 1, (19 : ℚ) / 20, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 40, (59 : ℚ) / 80, (1 : ℚ) / 20, (59 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 20, (1 : ℚ) / 1, (1 : ℚ) / 20] }
def node_box_22 : ProfileBox := { lower := ![(1 : ℚ) / 40, (45 : ℚ) / 64, (0 : ℚ) / 1, (45 : ℚ) / 64, (19 : ℚ) / 20, (0 : ℚ) / 1, (19 : ℚ) / 20, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 20, (59 : ℚ) / 80, (1 : ℚ) / 20, (59 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 20, (1 : ℚ) / 1, (1 : ℚ) / 20] }
def node_box_23 : ProfileBox := { lower := ![(0 : ℚ) / 1, (45 : ℚ) / 64, (0 : ℚ) / 1, (45 : ℚ) / 64, (19 : ℚ) / 20, (0 : ℚ) / 1, (19 : ℚ) / 20, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 40, (59 : ℚ) / 80, (1 : ℚ) / 20, (59 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40, (1 : ℚ) / 1, (1 : ℚ) / 20] }
def node_box_24 : ProfileBox := branch_box_24
def node_box_25 : ProfileBox := { lower := ![(0 : ℚ) / 1, (45 : ℚ) / 64, (0 : ℚ) / 1, (45 : ℚ) / 64, (19 : ℚ) / 20, (0 : ℚ) / 1, (19 : ℚ) / 20, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 40, (59 : ℚ) / 80, (1 : ℚ) / 20, (59 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_26 : ProfileBox := { lower := ![(0 : ℚ) / 1, (45 : ℚ) / 64, (0 : ℚ) / 1, (45 : ℚ) / 64, (19 : ℚ) / 20, (0 : ℚ) / 1, (19 : ℚ) / 20, (1 : ℚ) / 40], upper := ![(1 : ℚ) / 40, (59 : ℚ) / 80, (1 : ℚ) / 20, (59 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40, (1 : ℚ) / 1, (1 : ℚ) / 20] }
def node_box_27 : ProfileBox := { lower := ![(0 : ℚ) / 1, (45 : ℚ) / 64, (0 : ℚ) / 1, (45 : ℚ) / 64, (19 : ℚ) / 20, (0 : ℚ) / 1, (19 : ℚ) / 20, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 40, (59 : ℚ) / 80, (1 : ℚ) / 20, (59 : ℚ) / 80, (39 : ℚ) / 40, (1 : ℚ) / 40, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_28 : ProfileBox := { lower := ![(0 : ℚ) / 1, (45 : ℚ) / 64, (0 : ℚ) / 1, (45 : ℚ) / 64, (39 : ℚ) / 40, (0 : ℚ) / 1, (19 : ℚ) / 20, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 40, (59 : ℚ) / 80, (1 : ℚ) / 20, (59 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_29 : ProfileBox := branch_box_29
def node_box_30 : ProfileBox := { lower := ![(0 : ℚ) / 1, (45 : ℚ) / 64, (0 : ℚ) / 1, (45 : ℚ) / 64, (19 : ℚ) / 20, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 40, (59 : ℚ) / 80, (1 : ℚ) / 20, (59 : ℚ) / 80, (39 : ℚ) / 40, (1 : ℚ) / 40, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_31 : ProfileBox := branch_box_31
def node_box_32 : ProfileBox := { lower := ![(0 : ℚ) / 1, (461 : ℚ) / 640, (0 : ℚ) / 1, (45 : ℚ) / 64, (19 : ℚ) / 20, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 40, (59 : ℚ) / 80, (1 : ℚ) / 20, (59 : ℚ) / 80, (39 : ℚ) / 40, (1 : ℚ) / 40, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_33 : ProfileBox := branch_box_33
def node_box_34 : ProfileBox := { lower := ![(0 : ℚ) / 1, (461 : ℚ) / 640, (0 : ℚ) / 1, (461 : ℚ) / 640, (19 : ℚ) / 20, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 40, (59 : ℚ) / 80, (1 : ℚ) / 20, (59 : ℚ) / 80, (39 : ℚ) / 40, (1 : ℚ) / 40, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_35 : ProfileBox := { lower := ![(0 : ℚ) / 1, (461 : ℚ) / 640, (0 : ℚ) / 1, (461 : ℚ) / 640, (19 : ℚ) / 20, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 40, (59 : ℚ) / 80, (1 : ℚ) / 20, (59 : ℚ) / 80, (39 : ℚ) / 40, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_36 : ProfileBox := branch_box_36
def node_box_37 : ProfileBox := branch_box_37
def node_box_38 : ProfileBox := { lower := ![(0 : ℚ) / 1, (461 : ℚ) / 640, (0 : ℚ) / 1, (461 : ℚ) / 640, (77 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 40, (59 : ℚ) / 80, (1 : ℚ) / 20, (59 : ℚ) / 80, (39 : ℚ) / 40, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_39 : ProfileBox := branch_box_39
def node_box_40 : ProfileBox := { lower := ![(0 : ℚ) / 1, (461 : ℚ) / 640, (0 : ℚ) / 1, (461 : ℚ) / 640, (77 : ℚ) / 80, (0 : ℚ) / 1, (79 : ℚ) / 80, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 40, (59 : ℚ) / 80, (1 : ℚ) / 20, (59 : ℚ) / 80, (39 : ℚ) / 40, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_41 : ProfileBox := { lower := ![(0 : ℚ) / 1, (461 : ℚ) / 640, (0 : ℚ) / 1, (461 : ℚ) / 640, (77 : ℚ) / 80, (0 : ℚ) / 1, (79 : ℚ) / 80, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 40, (59 : ℚ) / 80, (1 : ℚ) / 20, (59 : ℚ) / 80, (31 : ℚ) / 32, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_42 : ProfileBox := { lower := ![(0 : ℚ) / 1, (461 : ℚ) / 640, (0 : ℚ) / 1, (461 : ℚ) / 640, (31 : ℚ) / 32, (0 : ℚ) / 1, (79 : ℚ) / 80, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 40, (59 : ℚ) / 80, (1 : ℚ) / 20, (59 : ℚ) / 80, (39 : ℚ) / 40, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_43 : ProfileBox := branch_box_43
def node_box_44 : ProfileBox := { lower := ![(0 : ℚ) / 1, (461 : ℚ) / 640, (0 : ℚ) / 1, (461 : ℚ) / 640, (77 : ℚ) / 80, (0 : ℚ) / 1, (159 : ℚ) / 160, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 40, (59 : ℚ) / 80, (1 : ℚ) / 20, (59 : ℚ) / 80, (31 : ℚ) / 32, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_45 : ProfileBox := branch_box_45
def node_box_46 : ProfileBox := { lower := ![(0 : ℚ) / 1, (461 : ℚ) / 640, (0 : ℚ) / 1, (461 : ℚ) / 640, (309 : ℚ) / 320, (0 : ℚ) / 1, (159 : ℚ) / 160, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 40, (59 : ℚ) / 80, (1 : ℚ) / 20, (59 : ℚ) / 80, (31 : ℚ) / 32, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_47 : ProfileBox := branch_box_47
def node_box_48 : ProfileBox := { lower := ![(0 : ℚ) / 1, (461 : ℚ) / 640, (0 : ℚ) / 1, (461 : ℚ) / 640, (309 : ℚ) / 320, (0 : ℚ) / 1, (319 : ℚ) / 320, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 40, (59 : ℚ) / 80, (1 : ℚ) / 20, (59 : ℚ) / 80, (31 : ℚ) / 32, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_49 : ProfileBox := { lower := ![(0 : ℚ) / 1, (461 : ℚ) / 640, (0 : ℚ) / 1, (461 : ℚ) / 640, (31 : ℚ) / 32, (0 : ℚ) / 1, (79 : ℚ) / 80, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 40, (59 : ℚ) / 80, (1 : ℚ) / 20, (59 : ℚ) / 80, (39 : ℚ) / 40, (1 : ℚ) / 80, (159 : ℚ) / 160, (1 : ℚ) / 40] }

def split_0_accepted : Bool := splitNodeOK node_box_0 node_box_1 node_box_2 ⟨1, by omega⟩ ((59 : ℚ) / 80)
def split_1_accepted : Bool := splitNodeOK node_box_1 node_box_3 node_box_4 ⟨3, by omega⟩ ((59 : ℚ) / 80)
def split_2_accepted : Bool := splitNodeOK node_box_2 node_box_3887 node_box_3888 ⟨3, by omega⟩ ((59 : ℚ) / 80)
def split_3_accepted : Bool := splitNodeOK node_box_3 node_box_5 node_box_6 ⟨1, by omega⟩ ((107 : ℚ) / 160)
def split_4_accepted : Bool := splitNodeOK node_box_4 node_box_853 node_box_854 ⟨1, by omega⟩ ((107 : ℚ) / 160)
def split_6_accepted : Bool := splitNodeOK node_box_6 node_box_7 node_box_8 ⟨3, by omega⟩ ((107 : ℚ) / 160)
def split_8_accepted : Bool := splitNodeOK node_box_8 node_box_9 node_box_10 ⟨0, by omega⟩ ((1 : ℚ) / 20)
def split_9_accepted : Bool := splitNodeOK node_box_9 node_box_11 node_box_12 ⟨2, by omega⟩ ((1 : ℚ) / 20)
def split_10_accepted : Bool := splitNodeOK node_box_10 node_box_801 node_box_802 ⟨2, by omega⟩ ((1 : ℚ) / 20)
def split_11_accepted : Bool := splitNodeOK node_box_11 node_box_13 node_box_14 ⟨5, by omega⟩ ((1 : ℚ) / 20)
def split_12_accepted : Bool := splitNodeOK node_box_12 node_box_475 node_box_476 ⟨5, by omega⟩ ((1 : ℚ) / 20)
def split_13_accepted : Bool := splitNodeOK node_box_13 node_box_15 node_box_16 ⟨7, by omega⟩ ((1 : ℚ) / 20)
def split_15_accepted : Bool := splitNodeOK node_box_15 node_box_17 node_box_18 ⟨1, by omega⟩ ((45 : ℚ) / 64)
def split_18_accepted : Bool := splitNodeOK node_box_18 node_box_19 node_box_20 ⟨3, by omega⟩ ((45 : ℚ) / 64)
def split_20_accepted : Bool := splitNodeOK node_box_20 node_box_21 node_box_22 ⟨0, by omega⟩ ((1 : ℚ) / 40)
def split_21_accepted : Bool := splitNodeOK node_box_21 node_box_23 node_box_24 ⟨5, by omega⟩ ((1 : ℚ) / 40)
def split_22_accepted : Bool := splitNodeOK node_box_22 node_box_261 node_box_262 ⟨2, by omega⟩ ((1 : ℚ) / 40)
def split_23_accepted : Bool := splitNodeOK node_box_23 node_box_25 node_box_26 ⟨7, by omega⟩ ((1 : ℚ) / 40)
def split_25_accepted : Bool := splitNodeOK node_box_25 node_box_27 node_box_28 ⟨4, by omega⟩ ((39 : ℚ) / 40)
def split_26_accepted : Bool := splitNodeOK node_box_26 node_box_153 node_box_154 ⟨4, by omega⟩ ((39 : ℚ) / 40)
def split_27_accepted : Bool := splitNodeOK node_box_27 node_box_29 node_box_30 ⟨6, by omega⟩ ((39 : ℚ) / 40)
def split_28_accepted : Bool := splitNodeOK node_box_28 node_box_55 node_box_56 ⟨6, by omega⟩ ((39 : ℚ) / 40)
def split_30_accepted : Bool := splitNodeOK node_box_30 node_box_31 node_box_32 ⟨1, by omega⟩ ((461 : ℚ) / 640)
def split_32_accepted : Bool := splitNodeOK node_box_32 node_box_33 node_box_34 ⟨3, by omega⟩ ((461 : ℚ) / 640)
def split_34_accepted : Bool := splitNodeOK node_box_34 node_box_35 node_box_36 ⟨5, by omega⟩ ((1 : ℚ) / 80)
def split_35_accepted : Bool := splitNodeOK node_box_35 node_box_37 node_box_38 ⟨4, by omega⟩ ((77 : ℚ) / 80)
def split_38_accepted : Bool := splitNodeOK node_box_38 node_box_39 node_box_40 ⟨6, by omega⟩ ((79 : ℚ) / 80)
def split_40_accepted : Bool := splitNodeOK node_box_40 node_box_41 node_box_42 ⟨4, by omega⟩ ((31 : ℚ) / 32)
def split_41_accepted : Bool := splitNodeOK node_box_41 node_box_43 node_box_44 ⟨6, by omega⟩ ((159 : ℚ) / 160)
def split_42_accepted : Bool := splitNodeOK node_box_42 node_box_49 node_box_50 ⟨6, by omega⟩ ((159 : ℚ) / 160)
def split_44_accepted : Bool := splitNodeOK node_box_44 node_box_45 node_box_46 ⟨4, by omega⟩ ((309 : ℚ) / 320)
def split_46_accepted : Bool := splitNodeOK node_box_46 node_box_47 node_box_48 ⟨6, by omega⟩ ((319 : ℚ) / 320)
def split_49_accepted : Bool := splitNodeOK node_box_49 node_box_51 node_box_52 ⟨4, by omega⟩ ((311 : ℚ) / 320)
def split_batch_00_values : List Bool := [split_0_accepted, split_1_accepted, split_2_accepted, split_3_accepted, split_4_accepted, split_6_accepted, split_8_accepted, split_9_accepted, split_10_accepted, split_11_accepted, split_12_accepted, split_13_accepted, split_15_accepted, split_18_accepted, split_20_accepted, split_21_accepted, split_22_accepted, split_23_accepted, split_25_accepted, split_26_accepted, split_27_accepted, split_28_accepted, split_30_accepted, split_32_accepted, split_34_accepted, split_35_accepted, split_38_accepted, split_40_accepted, split_41_accepted, split_42_accepted, split_44_accepted, split_46_accepted, split_49_accepted]
theorem split_batch_00_ok : split_batch_00_values.all id = true := by
  native_decide

def terminal_48_accepted : Bool := LeafChecks.checkCore node_box_48
def terminal_batch_00_values : List Bool := [terminal_48_accepted]
theorem terminal_batch_00_ok : terminal_batch_00_values.all id = true := by
  native_decide

theorem split_49_ok : split_49_accepted = true := by
  have h := List.all_eq_true.mp split_batch_00_ok split_49_accepted
    (by simp [split_batch_00_values])
  exact h
theorem tree_49 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_49) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_49 node_box_51 node_box_52 ⟨4, by omega⟩ ((311 : ℚ) / 320)
    (by simpa [split_49_accepted] using split_49_ok) tree_51 tree_52

theorem terminal_48_ok : terminal_48_accepted = true := by
  have h := List.all_eq_true.mp terminal_batch_00_ok terminal_48_accepted
    (by simp [terminal_batch_00_values])
  exact h
theorem tree_48 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_48) := by
  refine ⟨CoverTree.leaf (Or.inr ?_)⟩
  apply LeafChecks.checkCore_sound node_box_48
  simpa [terminal_48_accepted] using terminal_48_ok

theorem tree_47 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_47) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_47] using leaf_47_BranchSafe))⟩

theorem split_46_ok : split_46_accepted = true := by
  have h := List.all_eq_true.mp split_batch_00_ok split_46_accepted
    (by simp [split_batch_00_values])
  exact h
theorem tree_46 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_46) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_46 node_box_47 node_box_48 ⟨6, by omega⟩ ((319 : ℚ) / 320)
    (by simpa [split_46_accepted] using split_46_ok) tree_47 tree_48

theorem tree_45 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_45) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_45] using leaf_45_BranchSafe))⟩

theorem split_44_ok : split_44_accepted = true := by
  have h := List.all_eq_true.mp split_batch_00_ok split_44_accepted
    (by simp [split_batch_00_values])
  exact h
theorem tree_44 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_44) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_44 node_box_45 node_box_46 ⟨4, by omega⟩ ((309 : ℚ) / 320)
    (by simpa [split_44_accepted] using split_44_ok) tree_45 tree_46

theorem tree_43 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_43) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_43] using leaf_43_BranchSafe))⟩

theorem split_42_ok : split_42_accepted = true := by
  have h := List.all_eq_true.mp split_batch_00_ok split_42_accepted
    (by simp [split_batch_00_values])
  exact h
theorem tree_42 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_42) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_42 node_box_49 node_box_50 ⟨6, by omega⟩ ((159 : ℚ) / 160)
    (by simpa [split_42_accepted] using split_42_ok) tree_49 tree_50

theorem split_41_ok : split_41_accepted = true := by
  have h := List.all_eq_true.mp split_batch_00_ok split_41_accepted
    (by simp [split_batch_00_values])
  exact h
theorem tree_41 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_41) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_41 node_box_43 node_box_44 ⟨6, by omega⟩ ((159 : ℚ) / 160)
    (by simpa [split_41_accepted] using split_41_ok) tree_43 tree_44

theorem split_40_ok : split_40_accepted = true := by
  have h := List.all_eq_true.mp split_batch_00_ok split_40_accepted
    (by simp [split_batch_00_values])
  exact h
theorem tree_40 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_40) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_40 node_box_41 node_box_42 ⟨4, by omega⟩ ((31 : ℚ) / 32)
    (by simpa [split_40_accepted] using split_40_ok) tree_41 tree_42

theorem tree_39 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_39) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_39] using leaf_39_BranchSafe))⟩

theorem split_38_ok : split_38_accepted = true := by
  have h := List.all_eq_true.mp split_batch_00_ok split_38_accepted
    (by simp [split_batch_00_values])
  exact h
theorem tree_38 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_38) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_38 node_box_39 node_box_40 ⟨6, by omega⟩ ((79 : ℚ) / 80)
    (by simpa [split_38_accepted] using split_38_ok) tree_39 tree_40

theorem tree_37 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_37) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_37] using leaf_37_BranchSafe))⟩

theorem tree_36 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_36) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_36] using leaf_36_BranchSafe))⟩

theorem split_35_ok : split_35_accepted = true := by
  have h := List.all_eq_true.mp split_batch_00_ok split_35_accepted
    (by simp [split_batch_00_values])
  exact h
theorem tree_35 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_35) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_35 node_box_37 node_box_38 ⟨4, by omega⟩ ((77 : ℚ) / 80)
    (by simpa [split_35_accepted] using split_35_ok) tree_37 tree_38

theorem split_34_ok : split_34_accepted = true := by
  have h := List.all_eq_true.mp split_batch_00_ok split_34_accepted
    (by simp [split_batch_00_values])
  exact h
theorem tree_34 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_34) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_34 node_box_35 node_box_36 ⟨5, by omega⟩ ((1 : ℚ) / 80)
    (by simpa [split_34_accepted] using split_34_ok) tree_35 tree_36

theorem tree_33 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_33) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_33] using leaf_33_BranchSafe))⟩

theorem split_32_ok : split_32_accepted = true := by
  have h := List.all_eq_true.mp split_batch_00_ok split_32_accepted
    (by simp [split_batch_00_values])
  exact h
theorem tree_32 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_32) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_32 node_box_33 node_box_34 ⟨3, by omega⟩ ((461 : ℚ) / 640)
    (by simpa [split_32_accepted] using split_32_ok) tree_33 tree_34

theorem tree_31 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_31) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_31] using leaf_31_BranchSafe))⟩

theorem split_30_ok : split_30_accepted = true := by
  have h := List.all_eq_true.mp split_batch_00_ok split_30_accepted
    (by simp [split_batch_00_values])
  exact h
theorem tree_30 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_30) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_30 node_box_31 node_box_32 ⟨1, by omega⟩ ((461 : ℚ) / 640)
    (by simpa [split_30_accepted] using split_30_ok) tree_31 tree_32

theorem tree_29 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_29) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_29] using leaf_29_BranchSafe))⟩

theorem split_28_ok : split_28_accepted = true := by
  have h := List.all_eq_true.mp split_batch_00_ok split_28_accepted
    (by simp [split_batch_00_values])
  exact h
theorem tree_28 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_28) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_28 node_box_55 node_box_56 ⟨6, by omega⟩ ((39 : ℚ) / 40)
    (by simpa [split_28_accepted] using split_28_ok) tree_55 tree_56

theorem split_27_ok : split_27_accepted = true := by
  have h := List.all_eq_true.mp split_batch_00_ok split_27_accepted
    (by simp [split_batch_00_values])
  exact h
theorem tree_27 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_27) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_27 node_box_29 node_box_30 ⟨6, by omega⟩ ((39 : ℚ) / 40)
    (by simpa [split_27_accepted] using split_27_ok) tree_29 tree_30

theorem split_26_ok : split_26_accepted = true := by
  have h := List.all_eq_true.mp split_batch_00_ok split_26_accepted
    (by simp [split_batch_00_values])
  exact h
theorem tree_26 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_26) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_26 node_box_153 node_box_154 ⟨4, by omega⟩ ((39 : ℚ) / 40)
    (by simpa [split_26_accepted] using split_26_ok) tree_153 tree_154

theorem split_25_ok : split_25_accepted = true := by
  have h := List.all_eq_true.mp split_batch_00_ok split_25_accepted
    (by simp [split_batch_00_values])
  exact h
theorem tree_25 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_25) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_25 node_box_27 node_box_28 ⟨4, by omega⟩ ((39 : ℚ) / 40)
    (by simpa [split_25_accepted] using split_25_ok) tree_27 tree_28

theorem tree_24 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_24) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_24] using leaf_24_BranchSafe))⟩

theorem split_23_ok : split_23_accepted = true := by
  have h := List.all_eq_true.mp split_batch_00_ok split_23_accepted
    (by simp [split_batch_00_values])
  exact h
theorem tree_23 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_23) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_23 node_box_25 node_box_26 ⟨7, by omega⟩ ((1 : ℚ) / 40)
    (by simpa [split_23_accepted] using split_23_ok) tree_25 tree_26

theorem split_22_ok : split_22_accepted = true := by
  have h := List.all_eq_true.mp split_batch_00_ok split_22_accepted
    (by simp [split_batch_00_values])
  exact h
theorem tree_22 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_22) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_22 node_box_261 node_box_262 ⟨2, by omega⟩ ((1 : ℚ) / 40)
    (by simpa [split_22_accepted] using split_22_ok) tree_261 tree_262

theorem split_21_ok : split_21_accepted = true := by
  have h := List.all_eq_true.mp split_batch_00_ok split_21_accepted
    (by simp [split_batch_00_values])
  exact h
theorem tree_21 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_21) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_21 node_box_23 node_box_24 ⟨5, by omega⟩ ((1 : ℚ) / 40)
    (by simpa [split_21_accepted] using split_21_ok) tree_23 tree_24

theorem split_20_ok : split_20_accepted = true := by
  have h := List.all_eq_true.mp split_batch_00_ok split_20_accepted
    (by simp [split_batch_00_values])
  exact h
theorem tree_20 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_20) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_20 node_box_21 node_box_22 ⟨0, by omega⟩ ((1 : ℚ) / 40)
    (by simpa [split_20_accepted] using split_20_ok) tree_21 tree_22

theorem tree_19 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_19) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_19] using leaf_19_BranchSafe))⟩

theorem split_18_ok : split_18_accepted = true := by
  have h := List.all_eq_true.mp split_batch_00_ok split_18_accepted
    (by simp [split_batch_00_values])
  exact h
theorem tree_18 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_18) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_18 node_box_19 node_box_20 ⟨3, by omega⟩ ((45 : ℚ) / 64)
    (by simpa [split_18_accepted] using split_18_ok) tree_19 tree_20

theorem tree_17 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_17) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_17] using leaf_17_BranchSafe))⟩

theorem tree_16 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_16) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_16] using leaf_16_BranchSafe))⟩

theorem split_15_ok : split_15_accepted = true := by
  have h := List.all_eq_true.mp split_batch_00_ok split_15_accepted
    (by simp [split_batch_00_values])
  exact h
theorem tree_15 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_15) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_15 node_box_17 node_box_18 ⟨1, by omega⟩ ((45 : ℚ) / 64)
    (by simpa [split_15_accepted] using split_15_ok) tree_17 tree_18

theorem tree_14 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_14) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_14] using leaf_14_BranchSafe))⟩

theorem split_13_ok : split_13_accepted = true := by
  have h := List.all_eq_true.mp split_batch_00_ok split_13_accepted
    (by simp [split_batch_00_values])
  exact h
theorem tree_13 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_13) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_13 node_box_15 node_box_16 ⟨7, by omega⟩ ((1 : ℚ) / 20)
    (by simpa [split_13_accepted] using split_13_ok) tree_15 tree_16

theorem split_12_ok : split_12_accepted = true := by
  have h := List.all_eq_true.mp split_batch_00_ok split_12_accepted
    (by simp [split_batch_00_values])
  exact h
theorem tree_12 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_12) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_12 node_box_475 node_box_476 ⟨5, by omega⟩ ((1 : ℚ) / 20)
    (by simpa [split_12_accepted] using split_12_ok) tree_475 tree_476

theorem split_11_ok : split_11_accepted = true := by
  have h := List.all_eq_true.mp split_batch_00_ok split_11_accepted
    (by simp [split_batch_00_values])
  exact h
theorem tree_11 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_11) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_11 node_box_13 node_box_14 ⟨5, by omega⟩ ((1 : ℚ) / 20)
    (by simpa [split_11_accepted] using split_11_ok) tree_13 tree_14

theorem split_10_ok : split_10_accepted = true := by
  have h := List.all_eq_true.mp split_batch_00_ok split_10_accepted
    (by simp [split_batch_00_values])
  exact h
theorem tree_10 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_10) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_10 node_box_801 node_box_802 ⟨2, by omega⟩ ((1 : ℚ) / 20)
    (by simpa [split_10_accepted] using split_10_ok) tree_801 tree_802

theorem split_9_ok : split_9_accepted = true := by
  have h := List.all_eq_true.mp split_batch_00_ok split_9_accepted
    (by simp [split_batch_00_values])
  exact h
theorem tree_9 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_9) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_9 node_box_11 node_box_12 ⟨2, by omega⟩ ((1 : ℚ) / 20)
    (by simpa [split_9_accepted] using split_9_ok) tree_11 tree_12

theorem split_8_ok : split_8_accepted = true := by
  have h := List.all_eq_true.mp split_batch_00_ok split_8_accepted
    (by simp [split_batch_00_values])
  exact h
theorem tree_8 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_8) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_8 node_box_9 node_box_10 ⟨0, by omega⟩ ((1 : ℚ) / 20)
    (by simpa [split_8_accepted] using split_8_ok) tree_9 tree_10

theorem tree_7 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_7) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_7] using leaf_7_BranchSafe))⟩

theorem split_6_ok : split_6_accepted = true := by
  have h := List.all_eq_true.mp split_batch_00_ok split_6_accepted
    (by simp [split_batch_00_values])
  exact h
theorem tree_6 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_6) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_6 node_box_7 node_box_8 ⟨3, by omega⟩ ((107 : ℚ) / 160)
    (by simpa [split_6_accepted] using split_6_ok) tree_7 tree_8

theorem tree_5 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_5) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_5] using leaf_5_BranchSafe))⟩

theorem split_4_ok : split_4_accepted = true := by
  have h := List.all_eq_true.mp split_batch_00_ok split_4_accepted
    (by simp [split_batch_00_values])
  exact h
theorem tree_4 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_4) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_4 node_box_853 node_box_854 ⟨1, by omega⟩ ((107 : ℚ) / 160)
    (by simpa [split_4_accepted] using split_4_ok) tree_853 tree_854

theorem split_3_ok : split_3_accepted = true := by
  have h := List.all_eq_true.mp split_batch_00_ok split_3_accepted
    (by simp [split_batch_00_values])
  exact h
theorem tree_3 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_3) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_3 node_box_5 node_box_6 ⟨1, by omega⟩ ((107 : ℚ) / 160)
    (by simpa [split_3_accepted] using split_3_ok) tree_5 tree_6

theorem split_2_ok : split_2_accepted = true := by
  have h := List.all_eq_true.mp split_batch_00_ok split_2_accepted
    (by simp [split_batch_00_values])
  exact h
theorem tree_2 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_2) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_2 node_box_3887 node_box_3888 ⟨3, by omega⟩ ((59 : ℚ) / 80)
    (by simpa [split_2_accepted] using split_2_ok) tree_3887 tree_3888

theorem split_1_ok : split_1_accepted = true := by
  have h := List.all_eq_true.mp split_batch_00_ok split_1_accepted
    (by simp [split_batch_00_values])
  exact h
theorem tree_1 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_1) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_1 node_box_3 node_box_4 ⟨3, by omega⟩ ((59 : ℚ) / 80)
    (by simpa [split_1_accepted] using split_1_ok) tree_3 tree_4

theorem split_0_ok : split_0_accepted = true := by
  have h := List.all_eq_true.mp split_batch_00_ok split_0_accepted
    (by simp [split_batch_00_values])
  exact h
theorem tree_0 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_0) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_0 node_box_1 node_box_2 ⟨1, by omega⟩ ((59 : ℚ) / 80)
    (by simpa [split_0_accepted] using split_0_ok) tree_1 tree_2

#print axioms tree_0
end PeaceableQueens.UpperBound.Generated.Even.Core
