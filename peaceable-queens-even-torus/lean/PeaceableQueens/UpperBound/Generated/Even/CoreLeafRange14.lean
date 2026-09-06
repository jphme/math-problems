import PeaceableQueens.UpperBound.Generated.Even.CoreTopology
import PeaceableQueens.UpperBound.Generated.Even.CoreLeafRange15
import PeaceableQueens.UpperBound.Generated.Even.CoreScaled14Check

namespace PeaceableQueens.UpperBound.Generated.Even.Core
open PeaceableQueens.UpperBound
open PeaceableQueens.UpperBound.BranchCertificate

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def node_box_700 : ProfileBox := branch_box_700
def node_box_701 : ProfileBox := branch_box_701
def node_box_702 : ProfileBox := { lower := ![(1 : ℚ) / 40, (45 : ℚ) / 64, (1 : ℚ) / 20, (461 : ℚ) / 640, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(3 : ℚ) / 80, (461 : ℚ) / 640, (1 : ℚ) / 16, (59 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_703 : ProfileBox := branch_box_703
def node_box_704 : ProfileBox := { lower := ![(1 : ℚ) / 40, (911 : ℚ) / 1280, (1 : ℚ) / 20, (461 : ℚ) / 640, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(3 : ℚ) / 80, (461 : ℚ) / 640, (1 : ℚ) / 16, (59 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_705 : ProfileBox := branch_box_705
def node_box_706 : ProfileBox := { lower := ![(1 : ℚ) / 40, (911 : ℚ) / 1280, (1 : ℚ) / 20, (933 : ℚ) / 1280, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(3 : ℚ) / 80, (461 : ℚ) / 640, (1 : ℚ) / 16, (59 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_707 : ProfileBox := { lower := ![(1 : ℚ) / 40, (911 : ℚ) / 1280, (1 : ℚ) / 20, (933 : ℚ) / 1280, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 32, (461 : ℚ) / 640, (1 : ℚ) / 16, (59 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_708 : ProfileBox := { lower := ![(1 : ℚ) / 32, (911 : ℚ) / 1280, (1 : ℚ) / 20, (933 : ℚ) / 1280, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(3 : ℚ) / 80, (461 : ℚ) / 640, (1 : ℚ) / 16, (59 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_709 : ProfileBox := { lower := ![(1 : ℚ) / 40, (911 : ℚ) / 1280, (1 : ℚ) / 20, (933 : ℚ) / 1280, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 32, (461 : ℚ) / 640, (9 : ℚ) / 160, (59 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_710 : ProfileBox := { lower := ![(1 : ℚ) / 40, (911 : ℚ) / 1280, (9 : ℚ) / 160, (933 : ℚ) / 1280, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 32, (461 : ℚ) / 640, (1 : ℚ) / 16, (59 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_711 : ProfileBox := { lower := ![(1 : ℚ) / 40, (911 : ℚ) / 1280, (9 : ℚ) / 160, (933 : ℚ) / 1280, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(9 : ℚ) / 320, (461 : ℚ) / 640, (1 : ℚ) / 16, (59 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_712 : ProfileBox := branch_box_712
def node_box_713 : ProfileBox := { lower := ![(1 : ℚ) / 40, (911 : ℚ) / 1280, (9 : ℚ) / 160, (933 : ℚ) / 1280, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(9 : ℚ) / 320, (461 : ℚ) / 640, (19 : ℚ) / 320, (59 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_714 : ProfileBox := branch_box_714
def node_box_715 : ProfileBox := { lower := ![(1 : ℚ) / 32, (911 : ℚ) / 1280, (1 : ℚ) / 20, (933 : ℚ) / 1280, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(3 : ℚ) / 80, (461 : ℚ) / 640, (9 : ℚ) / 160, (59 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_716 : ProfileBox := branch_box_716
def node_box_717 : ProfileBox := { lower := ![(1 : ℚ) / 32, (911 : ℚ) / 1280, (1 : ℚ) / 20, (933 : ℚ) / 1280, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(11 : ℚ) / 320, (461 : ℚ) / 640, (9 : ℚ) / 160, (59 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_718 : ProfileBox := { lower := ![(11 : ℚ) / 320, (911 : ℚ) / 1280, (1 : ℚ) / 20, (933 : ℚ) / 1280, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(3 : ℚ) / 80, (461 : ℚ) / 640, (9 : ℚ) / 160, (59 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_719 : ProfileBox := { lower := ![(1 : ℚ) / 32, (911 : ℚ) / 1280, (1 : ℚ) / 20, (933 : ℚ) / 1280, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(11 : ℚ) / 320, (461 : ℚ) / 640, (17 : ℚ) / 320, (59 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_720 : ProfileBox := { lower := ![(1 : ℚ) / 32, (911 : ℚ) / 1280, (17 : ℚ) / 320, (933 : ℚ) / 1280, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(11 : ℚ) / 320, (461 : ℚ) / 640, (9 : ℚ) / 160, (59 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_721 : ProfileBox := { lower := ![(1 : ℚ) / 32, (911 : ℚ) / 1280, (17 : ℚ) / 320, (933 : ℚ) / 1280, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(21 : ℚ) / 640, (461 : ℚ) / 640, (9 : ℚ) / 160, (59 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_722 : ProfileBox := branch_box_722
def node_box_723 : ProfileBox := { lower := ![(11 : ℚ) / 320, (911 : ℚ) / 1280, (1 : ℚ) / 20, (933 : ℚ) / 1280, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(3 : ℚ) / 80, (461 : ℚ) / 640, (17 : ℚ) / 320, (59 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_724 : ProfileBox := branch_box_724
def node_box_725 : ProfileBox := { lower := ![(11 : ℚ) / 320, (911 : ℚ) / 1280, (1 : ℚ) / 20, (933 : ℚ) / 1280, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(23 : ℚ) / 640, (461 : ℚ) / 640, (17 : ℚ) / 320, (59 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_726 : ProfileBox := branch_box_726
def node_box_727 : ProfileBox := { lower := ![(1 : ℚ) / 40, (461 : ℚ) / 640, (1 : ℚ) / 20, (45 : ℚ) / 64, (39 : ℚ) / 40, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 20, (59 : ℚ) / 80, (3 : ℚ) / 40, (461 : ℚ) / 640, (1 : ℚ) / 1, (1 : ℚ) / 40, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_728 : ProfileBox := { lower := ![(1 : ℚ) / 40, (461 : ℚ) / 640, (1 : ℚ) / 20, (461 : ℚ) / 640, (39 : ℚ) / 40, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 20, (59 : ℚ) / 80, (3 : ℚ) / 40, (59 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_729 : ProfileBox := { lower := ![(1 : ℚ) / 40, (461 : ℚ) / 640, (1 : ℚ) / 20, (45 : ℚ) / 64, (39 : ℚ) / 40, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(3 : ℚ) / 80, (59 : ℚ) / 80, (3 : ℚ) / 40, (461 : ℚ) / 640, (1 : ℚ) / 1, (1 : ℚ) / 40, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_730 : ProfileBox := branch_box_730
def node_box_731 : ProfileBox := { lower := ![(1 : ℚ) / 40, (461 : ℚ) / 640, (1 : ℚ) / 20, (45 : ℚ) / 64, (39 : ℚ) / 40, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(3 : ℚ) / 80, (59 : ℚ) / 80, (1 : ℚ) / 16, (461 : ℚ) / 640, (1 : ℚ) / 1, (1 : ℚ) / 40, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_732 : ProfileBox := branch_box_732
def node_box_733 : ProfileBox := { lower := ![(1 : ℚ) / 40, (461 : ℚ) / 640, (1 : ℚ) / 20, (45 : ℚ) / 64, (39 : ℚ) / 40, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(3 : ℚ) / 80, (59 : ℚ) / 80, (1 : ℚ) / 16, (461 : ℚ) / 640, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_734 : ProfileBox := branch_box_734
def node_box_735 : ProfileBox := branch_box_735
def node_box_736 : ProfileBox := { lower := ![(1 : ℚ) / 40, (461 : ℚ) / 640, (1 : ℚ) / 20, (45 : ℚ) / 64, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(3 : ℚ) / 80, (59 : ℚ) / 80, (1 : ℚ) / 16, (461 : ℚ) / 640, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_737 : ProfileBox := branch_box_737
def node_box_738 : ProfileBox := { lower := ![(1 : ℚ) / 40, (933 : ℚ) / 1280, (1 : ℚ) / 20, (45 : ℚ) / 64, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(3 : ℚ) / 80, (59 : ℚ) / 80, (1 : ℚ) / 16, (461 : ℚ) / 640, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_739 : ProfileBox := branch_box_739
def node_box_740 : ProfileBox := { lower := ![(1 : ℚ) / 40, (933 : ℚ) / 1280, (1 : ℚ) / 20, (911 : ℚ) / 1280, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(3 : ℚ) / 80, (59 : ℚ) / 80, (1 : ℚ) / 16, (461 : ℚ) / 640, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_741 : ProfileBox := { lower := ![(1 : ℚ) / 40, (933 : ℚ) / 1280, (1 : ℚ) / 20, (911 : ℚ) / 1280, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 32, (59 : ℚ) / 80, (1 : ℚ) / 16, (461 : ℚ) / 640, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_742 : ProfileBox := { lower := ![(1 : ℚ) / 32, (933 : ℚ) / 1280, (1 : ℚ) / 20, (911 : ℚ) / 1280, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(3 : ℚ) / 80, (59 : ℚ) / 80, (1 : ℚ) / 16, (461 : ℚ) / 640, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_743 : ProfileBox := { lower := ![(1 : ℚ) / 40, (933 : ℚ) / 1280, (1 : ℚ) / 20, (911 : ℚ) / 1280, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 32, (59 : ℚ) / 80, (9 : ℚ) / 160, (461 : ℚ) / 640, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_744 : ProfileBox := { lower := ![(1 : ℚ) / 40, (933 : ℚ) / 1280, (9 : ℚ) / 160, (911 : ℚ) / 1280, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 32, (59 : ℚ) / 80, (1 : ℚ) / 16, (461 : ℚ) / 640, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_745 : ProfileBox := { lower := ![(1 : ℚ) / 40, (933 : ℚ) / 1280, (9 : ℚ) / 160, (911 : ℚ) / 1280, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(9 : ℚ) / 320, (59 : ℚ) / 80, (1 : ℚ) / 16, (461 : ℚ) / 640, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_746 : ProfileBox := { lower := ![(9 : ℚ) / 320, (933 : ℚ) / 1280, (9 : ℚ) / 160, (911 : ℚ) / 1280, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(1 : ℚ) / 32, (59 : ℚ) / 80, (1 : ℚ) / 16, (461 : ℚ) / 640, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_747 : ProfileBox := { lower := ![(1 : ℚ) / 40, (933 : ℚ) / 1280, (9 : ℚ) / 160, (911 : ℚ) / 1280, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(9 : ℚ) / 320, (59 : ℚ) / 80, (19 : ℚ) / 320, (461 : ℚ) / 640, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_748 : ProfileBox := { lower := ![(1 : ℚ) / 40, (933 : ℚ) / 1280, (19 : ℚ) / 320, (911 : ℚ) / 1280, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(9 : ℚ) / 320, (59 : ℚ) / 80, (1 : ℚ) / 16, (461 : ℚ) / 640, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }
def node_box_749 : ProfileBox := { lower := ![(1 : ℚ) / 40, (933 : ℚ) / 1280, (19 : ℚ) / 320, (911 : ℚ) / 1280, (79 : ℚ) / 80, (0 : ℚ) / 1, (39 : ℚ) / 40, (0 : ℚ) / 1], upper := ![(17 : ℚ) / 640, (59 : ℚ) / 80, (1 : ℚ) / 16, (461 : ℚ) / 640, (1 : ℚ) / 1, (1 : ℚ) / 80, (1 : ℚ) / 1, (1 : ℚ) / 40] }

def split_702_accepted : Bool := splitNodeOK node_box_702 node_box_703 node_box_704 ⟨1, by omega⟩ ((911 : ℚ) / 1280)
def split_704_accepted : Bool := splitNodeOK node_box_704 node_box_705 node_box_706 ⟨3, by omega⟩ ((933 : ℚ) / 1280)
def split_706_accepted : Bool := splitNodeOK node_box_706 node_box_707 node_box_708 ⟨0, by omega⟩ ((1 : ℚ) / 32)
def split_707_accepted : Bool := splitNodeOK node_box_707 node_box_709 node_box_710 ⟨2, by omega⟩ ((9 : ℚ) / 160)
def split_708_accepted : Bool := splitNodeOK node_box_708 node_box_715 node_box_716 ⟨2, by omega⟩ ((9 : ℚ) / 160)
def split_710_accepted : Bool := splitNodeOK node_box_710 node_box_711 node_box_712 ⟨0, by omega⟩ ((9 : ℚ) / 320)
def split_711_accepted : Bool := splitNodeOK node_box_711 node_box_713 node_box_714 ⟨2, by omega⟩ ((19 : ℚ) / 320)
def split_715_accepted : Bool := splitNodeOK node_box_715 node_box_717 node_box_718 ⟨0, by omega⟩ ((11 : ℚ) / 320)
def split_717_accepted : Bool := splitNodeOK node_box_717 node_box_719 node_box_720 ⟨2, by omega⟩ ((17 : ℚ) / 320)
def split_718_accepted : Bool := splitNodeOK node_box_718 node_box_723 node_box_724 ⟨2, by omega⟩ ((17 : ℚ) / 320)
def split_720_accepted : Bool := splitNodeOK node_box_720 node_box_721 node_box_722 ⟨0, by omega⟩ ((21 : ℚ) / 640)
def split_723_accepted : Bool := splitNodeOK node_box_723 node_box_725 node_box_726 ⟨0, by omega⟩ ((23 : ℚ) / 640)
def split_727_accepted : Bool := splitNodeOK node_box_727 node_box_729 node_box_730 ⟨0, by omega⟩ ((3 : ℚ) / 80)
def split_728_accepted : Bool := splitNodeOK node_box_728 node_box_767 node_box_768 ⟨0, by omega⟩ ((3 : ℚ) / 80)
def split_729_accepted : Bool := splitNodeOK node_box_729 node_box_731 node_box_732 ⟨2, by omega⟩ ((1 : ℚ) / 16)
def split_731_accepted : Bool := splitNodeOK node_box_731 node_box_733 node_box_734 ⟨5, by omega⟩ ((1 : ℚ) / 80)
def split_733_accepted : Bool := splitNodeOK node_box_733 node_box_735 node_box_736 ⟨4, by omega⟩ ((79 : ℚ) / 80)
def split_736_accepted : Bool := splitNodeOK node_box_736 node_box_737 node_box_738 ⟨1, by omega⟩ ((933 : ℚ) / 1280)
def split_738_accepted : Bool := splitNodeOK node_box_738 node_box_739 node_box_740 ⟨3, by omega⟩ ((911 : ℚ) / 1280)
def split_740_accepted : Bool := splitNodeOK node_box_740 node_box_741 node_box_742 ⟨0, by omega⟩ ((1 : ℚ) / 32)
def split_741_accepted : Bool := splitNodeOK node_box_741 node_box_743 node_box_744 ⟨2, by omega⟩ ((9 : ℚ) / 160)
def split_742_accepted : Bool := splitNodeOK node_box_742 node_box_755 node_box_756 ⟨2, by omega⟩ ((9 : ℚ) / 160)
def split_744_accepted : Bool := splitNodeOK node_box_744 node_box_745 node_box_746 ⟨0, by omega⟩ ((9 : ℚ) / 320)
def split_745_accepted : Bool := splitNodeOK node_box_745 node_box_747 node_box_748 ⟨2, by omega⟩ ((19 : ℚ) / 320)
def split_746_accepted : Bool := splitNodeOK node_box_746 node_box_751 node_box_752 ⟨2, by omega⟩ ((19 : ℚ) / 320)
def split_748_accepted : Bool := splitNodeOK node_box_748 node_box_749 node_box_750 ⟨0, by omega⟩ ((17 : ℚ) / 640)
def split_batch_14_values : List Bool := [split_702_accepted, split_704_accepted, split_706_accepted, split_707_accepted, split_708_accepted, split_710_accepted, split_711_accepted, split_715_accepted, split_717_accepted, split_718_accepted, split_720_accepted, split_723_accepted, split_727_accepted, split_728_accepted, split_729_accepted, split_731_accepted, split_733_accepted, split_736_accepted, split_738_accepted, split_740_accepted, split_741_accepted, split_742_accepted, split_744_accepted, split_745_accepted, split_746_accepted, split_748_accepted]
theorem split_batch_14_ok : split_batch_14_values.all id = true := by
  native_decide

def terminal_709_accepted : Bool := LeafChecks.checkCore node_box_709
def terminal_713_accepted : Bool := LeafChecks.checkCore node_box_713
def terminal_719_accepted : Bool := LeafChecks.checkCore node_box_719
def terminal_721_accepted : Bool := LeafChecks.checkCore node_box_721
def terminal_725_accepted : Bool := LeafChecks.checkCore node_box_725
def terminal_743_accepted : Bool := LeafChecks.checkCore node_box_743
def terminal_747_accepted : Bool := LeafChecks.checkCore node_box_747
def terminal_749_accepted : Bool := LeafChecks.checkCore node_box_749
def terminal_batch_14_values : List Bool := [terminal_709_accepted, terminal_713_accepted, terminal_719_accepted, terminal_721_accepted, terminal_725_accepted, terminal_743_accepted, terminal_747_accepted, terminal_749_accepted]
theorem terminal_batch_14_ok : terminal_batch_14_values.all id = true := by
  native_decide

theorem terminal_749_ok : terminal_749_accepted = true := by
  have h := List.all_eq_true.mp terminal_batch_14_ok terminal_749_accepted
    (by simp [terminal_batch_14_values])
  exact h
theorem tree_749 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_749) := by
  refine ⟨CoverTree.leaf (Or.inr ?_)⟩
  apply LeafChecks.checkCore_sound node_box_749
  simpa [terminal_749_accepted] using terminal_749_ok

theorem split_748_ok : split_748_accepted = true := by
  have h := List.all_eq_true.mp split_batch_14_ok split_748_accepted
    (by simp [split_batch_14_values])
  exact h
theorem tree_748 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_748) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_748 node_box_749 node_box_750 ⟨0, by omega⟩ ((17 : ℚ) / 640)
    (by simpa [split_748_accepted] using split_748_ok) tree_749 tree_750

theorem terminal_747_ok : terminal_747_accepted = true := by
  have h := List.all_eq_true.mp terminal_batch_14_ok terminal_747_accepted
    (by simp [terminal_batch_14_values])
  exact h
theorem tree_747 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_747) := by
  refine ⟨CoverTree.leaf (Or.inr ?_)⟩
  apply LeafChecks.checkCore_sound node_box_747
  simpa [terminal_747_accepted] using terminal_747_ok

theorem split_746_ok : split_746_accepted = true := by
  have h := List.all_eq_true.mp split_batch_14_ok split_746_accepted
    (by simp [split_batch_14_values])
  exact h
theorem tree_746 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_746) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_746 node_box_751 node_box_752 ⟨2, by omega⟩ ((19 : ℚ) / 320)
    (by simpa [split_746_accepted] using split_746_ok) tree_751 tree_752

theorem split_745_ok : split_745_accepted = true := by
  have h := List.all_eq_true.mp split_batch_14_ok split_745_accepted
    (by simp [split_batch_14_values])
  exact h
theorem tree_745 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_745) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_745 node_box_747 node_box_748 ⟨2, by omega⟩ ((19 : ℚ) / 320)
    (by simpa [split_745_accepted] using split_745_ok) tree_747 tree_748

theorem split_744_ok : split_744_accepted = true := by
  have h := List.all_eq_true.mp split_batch_14_ok split_744_accepted
    (by simp [split_batch_14_values])
  exact h
theorem tree_744 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_744) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_744 node_box_745 node_box_746 ⟨0, by omega⟩ ((9 : ℚ) / 320)
    (by simpa [split_744_accepted] using split_744_ok) tree_745 tree_746

theorem terminal_743_ok : terminal_743_accepted = true := by
  have h := List.all_eq_true.mp terminal_batch_14_ok terminal_743_accepted
    (by simp [terminal_batch_14_values])
  exact h
theorem tree_743 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_743) := by
  refine ⟨CoverTree.leaf (Or.inr ?_)⟩
  apply LeafChecks.checkCore_sound node_box_743
  simpa [terminal_743_accepted] using terminal_743_ok

theorem split_742_ok : split_742_accepted = true := by
  have h := List.all_eq_true.mp split_batch_14_ok split_742_accepted
    (by simp [split_batch_14_values])
  exact h
theorem tree_742 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_742) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_742 node_box_755 node_box_756 ⟨2, by omega⟩ ((9 : ℚ) / 160)
    (by simpa [split_742_accepted] using split_742_ok) tree_755 tree_756

theorem split_741_ok : split_741_accepted = true := by
  have h := List.all_eq_true.mp split_batch_14_ok split_741_accepted
    (by simp [split_batch_14_values])
  exact h
theorem tree_741 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_741) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_741 node_box_743 node_box_744 ⟨2, by omega⟩ ((9 : ℚ) / 160)
    (by simpa [split_741_accepted] using split_741_ok) tree_743 tree_744

theorem split_740_ok : split_740_accepted = true := by
  have h := List.all_eq_true.mp split_batch_14_ok split_740_accepted
    (by simp [split_batch_14_values])
  exact h
theorem tree_740 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_740) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_740 node_box_741 node_box_742 ⟨0, by omega⟩ ((1 : ℚ) / 32)
    (by simpa [split_740_accepted] using split_740_ok) tree_741 tree_742

theorem tree_739 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_739) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_739] using leaf_739_BranchSafe))⟩

theorem split_738_ok : split_738_accepted = true := by
  have h := List.all_eq_true.mp split_batch_14_ok split_738_accepted
    (by simp [split_batch_14_values])
  exact h
theorem tree_738 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_738) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_738 node_box_739 node_box_740 ⟨3, by omega⟩ ((911 : ℚ) / 1280)
    (by simpa [split_738_accepted] using split_738_ok) tree_739 tree_740

theorem tree_737 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_737) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_737] using leaf_737_BranchSafe))⟩

theorem split_736_ok : split_736_accepted = true := by
  have h := List.all_eq_true.mp split_batch_14_ok split_736_accepted
    (by simp [split_batch_14_values])
  exact h
theorem tree_736 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_736) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_736 node_box_737 node_box_738 ⟨1, by omega⟩ ((933 : ℚ) / 1280)
    (by simpa [split_736_accepted] using split_736_ok) tree_737 tree_738

theorem tree_735 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_735) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_735] using leaf_735_BranchSafe))⟩

theorem tree_734 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_734) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_734] using leaf_734_BranchSafe))⟩

theorem split_733_ok : split_733_accepted = true := by
  have h := List.all_eq_true.mp split_batch_14_ok split_733_accepted
    (by simp [split_batch_14_values])
  exact h
theorem tree_733 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_733) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_733 node_box_735 node_box_736 ⟨4, by omega⟩ ((79 : ℚ) / 80)
    (by simpa [split_733_accepted] using split_733_ok) tree_735 tree_736

theorem tree_732 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_732) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_732] using leaf_732_BranchSafe))⟩

theorem split_731_ok : split_731_accepted = true := by
  have h := List.all_eq_true.mp split_batch_14_ok split_731_accepted
    (by simp [split_batch_14_values])
  exact h
theorem tree_731 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_731) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_731 node_box_733 node_box_734 ⟨5, by omega⟩ ((1 : ℚ) / 80)
    (by simpa [split_731_accepted] using split_731_ok) tree_733 tree_734

theorem tree_730 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_730) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_730] using leaf_730_BranchSafe))⟩

theorem split_729_ok : split_729_accepted = true := by
  have h := List.all_eq_true.mp split_batch_14_ok split_729_accepted
    (by simp [split_batch_14_values])
  exact h
theorem tree_729 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_729) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_729 node_box_731 node_box_732 ⟨2, by omega⟩ ((1 : ℚ) / 16)
    (by simpa [split_729_accepted] using split_729_ok) tree_731 tree_732

theorem split_728_ok : split_728_accepted = true := by
  have h := List.all_eq_true.mp split_batch_14_ok split_728_accepted
    (by simp [split_batch_14_values])
  exact h
theorem tree_728 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_728) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_728 node_box_767 node_box_768 ⟨0, by omega⟩ ((3 : ℚ) / 80)
    (by simpa [split_728_accepted] using split_728_ok) tree_767 tree_768

theorem split_727_ok : split_727_accepted = true := by
  have h := List.all_eq_true.mp split_batch_14_ok split_727_accepted
    (by simp [split_batch_14_values])
  exact h
theorem tree_727 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_727) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_727 node_box_729 node_box_730 ⟨0, by omega⟩ ((3 : ℚ) / 80)
    (by simpa [split_727_accepted] using split_727_ok) tree_729 tree_730

theorem tree_726 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_726) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_726] using leaf_726_BranchSafe))⟩

theorem terminal_725_ok : terminal_725_accepted = true := by
  have h := List.all_eq_true.mp terminal_batch_14_ok terminal_725_accepted
    (by simp [terminal_batch_14_values])
  exact h
theorem tree_725 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_725) := by
  refine ⟨CoverTree.leaf (Or.inr ?_)⟩
  apply LeafChecks.checkCore_sound node_box_725
  simpa [terminal_725_accepted] using terminal_725_ok

theorem tree_724 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_724) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_724] using leaf_724_BranchSafe))⟩

theorem split_723_ok : split_723_accepted = true := by
  have h := List.all_eq_true.mp split_batch_14_ok split_723_accepted
    (by simp [split_batch_14_values])
  exact h
theorem tree_723 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_723) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_723 node_box_725 node_box_726 ⟨0, by omega⟩ ((23 : ℚ) / 640)
    (by simpa [split_723_accepted] using split_723_ok) tree_725 tree_726

theorem tree_722 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_722) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_722] using leaf_722_BranchSafe))⟩

theorem terminal_721_ok : terminal_721_accepted = true := by
  have h := List.all_eq_true.mp terminal_batch_14_ok terminal_721_accepted
    (by simp [terminal_batch_14_values])
  exact h
theorem tree_721 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_721) := by
  refine ⟨CoverTree.leaf (Or.inr ?_)⟩
  apply LeafChecks.checkCore_sound node_box_721
  simpa [terminal_721_accepted] using terminal_721_ok

theorem split_720_ok : split_720_accepted = true := by
  have h := List.all_eq_true.mp split_batch_14_ok split_720_accepted
    (by simp [split_batch_14_values])
  exact h
theorem tree_720 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_720) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_720 node_box_721 node_box_722 ⟨0, by omega⟩ ((21 : ℚ) / 640)
    (by simpa [split_720_accepted] using split_720_ok) tree_721 tree_722

theorem terminal_719_ok : terminal_719_accepted = true := by
  have h := List.all_eq_true.mp terminal_batch_14_ok terminal_719_accepted
    (by simp [terminal_batch_14_values])
  exact h
theorem tree_719 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_719) := by
  refine ⟨CoverTree.leaf (Or.inr ?_)⟩
  apply LeafChecks.checkCore_sound node_box_719
  simpa [terminal_719_accepted] using terminal_719_ok

theorem split_718_ok : split_718_accepted = true := by
  have h := List.all_eq_true.mp split_batch_14_ok split_718_accepted
    (by simp [split_batch_14_values])
  exact h
theorem tree_718 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_718) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_718 node_box_723 node_box_724 ⟨2, by omega⟩ ((17 : ℚ) / 320)
    (by simpa [split_718_accepted] using split_718_ok) tree_723 tree_724

theorem split_717_ok : split_717_accepted = true := by
  have h := List.all_eq_true.mp split_batch_14_ok split_717_accepted
    (by simp [split_batch_14_values])
  exact h
theorem tree_717 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_717) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_717 node_box_719 node_box_720 ⟨2, by omega⟩ ((17 : ℚ) / 320)
    (by simpa [split_717_accepted] using split_717_ok) tree_719 tree_720

theorem tree_716 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_716) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_716] using leaf_716_BranchSafe))⟩

theorem split_715_ok : split_715_accepted = true := by
  have h := List.all_eq_true.mp split_batch_14_ok split_715_accepted
    (by simp [split_batch_14_values])
  exact h
theorem tree_715 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_715) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_715 node_box_717 node_box_718 ⟨0, by omega⟩ ((11 : ℚ) / 320)
    (by simpa [split_715_accepted] using split_715_ok) tree_717 tree_718

theorem tree_714 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_714) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_714] using leaf_714_BranchSafe))⟩

theorem terminal_713_ok : terminal_713_accepted = true := by
  have h := List.all_eq_true.mp terminal_batch_14_ok terminal_713_accepted
    (by simp [terminal_batch_14_values])
  exact h
theorem tree_713 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_713) := by
  refine ⟨CoverTree.leaf (Or.inr ?_)⟩
  apply LeafChecks.checkCore_sound node_box_713
  simpa [terminal_713_accepted] using terminal_713_ok

theorem tree_712 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_712) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_712] using leaf_712_BranchSafe))⟩

theorem split_711_ok : split_711_accepted = true := by
  have h := List.all_eq_true.mp split_batch_14_ok split_711_accepted
    (by simp [split_batch_14_values])
  exact h
theorem tree_711 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_711) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_711 node_box_713 node_box_714 ⟨2, by omega⟩ ((19 : ℚ) / 320)
    (by simpa [split_711_accepted] using split_711_ok) tree_713 tree_714

theorem split_710_ok : split_710_accepted = true := by
  have h := List.all_eq_true.mp split_batch_14_ok split_710_accepted
    (by simp [split_batch_14_values])
  exact h
theorem tree_710 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_710) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_710 node_box_711 node_box_712 ⟨0, by omega⟩ ((9 : ℚ) / 320)
    (by simpa [split_710_accepted] using split_710_ok) tree_711 tree_712

theorem terminal_709_ok : terminal_709_accepted = true := by
  have h := List.all_eq_true.mp terminal_batch_14_ok terminal_709_accepted
    (by simp [terminal_batch_14_values])
  exact h
theorem tree_709 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_709) := by
  refine ⟨CoverTree.leaf (Or.inr ?_)⟩
  apply LeafChecks.checkCore_sound node_box_709
  simpa [terminal_709_accepted] using terminal_709_ok

theorem split_708_ok : split_708_accepted = true := by
  have h := List.all_eq_true.mp split_batch_14_ok split_708_accepted
    (by simp [split_batch_14_values])
  exact h
theorem tree_708 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_708) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_708 node_box_715 node_box_716 ⟨2, by omega⟩ ((9 : ℚ) / 160)
    (by simpa [split_708_accepted] using split_708_ok) tree_715 tree_716

theorem split_707_ok : split_707_accepted = true := by
  have h := List.all_eq_true.mp split_batch_14_ok split_707_accepted
    (by simp [split_batch_14_values])
  exact h
theorem tree_707 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_707) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_707 node_box_709 node_box_710 ⟨2, by omega⟩ ((9 : ℚ) / 160)
    (by simpa [split_707_accepted] using split_707_ok) tree_709 tree_710

theorem split_706_ok : split_706_accepted = true := by
  have h := List.all_eq_true.mp split_batch_14_ok split_706_accepted
    (by simp [split_batch_14_values])
  exact h
theorem tree_706 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_706) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_706 node_box_707 node_box_708 ⟨0, by omega⟩ ((1 : ℚ) / 32)
    (by simpa [split_706_accepted] using split_706_ok) tree_707 tree_708

theorem tree_705 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_705) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_705] using leaf_705_BranchSafe))⟩

theorem split_704_ok : split_704_accepted = true := by
  have h := List.all_eq_true.mp split_batch_14_ok split_704_accepted
    (by simp [split_batch_14_values])
  exact h
theorem tree_704 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_704) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_704 node_box_705 node_box_706 ⟨3, by omega⟩ ((933 : ℚ) / 1280)
    (by simpa [split_704_accepted] using split_704_ok) tree_705 tree_706

theorem tree_703 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_703) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_703] using leaf_703_BranchSafe))⟩

theorem split_702_ok : split_702_accepted = true := by
  have h := List.all_eq_true.mp split_batch_14_ok split_702_accepted
    (by simp [split_batch_14_values])
  exact h
theorem tree_702 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_702) :=
  splitNodeOK_coverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional
    node_box_702 node_box_703 node_box_704 ⟨1, by omega⟩ ((911 : ℚ) / 1280)
    (by simpa [split_702_accepted] using split_702_ok) tree_703 tree_704

theorem tree_701 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_701) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_701] using leaf_701_BranchSafe))⟩

theorem tree_700 :
    Nonempty (CoverTree CertificateConsequences.BranchSafe CertificateConsequences.CoreExceptional node_box_700) := by
  exact ⟨CoverTree.leaf (Or.inl (by simpa [node_box_700] using leaf_700_BranchSafe))⟩

#print axioms tree_700
end PeaceableQueens.UpperBound.Generated.Even.Core
